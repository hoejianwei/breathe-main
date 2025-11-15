// MIDI Input Monitor (C++17 + RtMidi)
// - Opens ALL available MIDI input ports
// - Prints human-readable events + raw hex
// Build instructions below.

#include "RtMidi.h"
#include <chrono>
#include <cstdint>
#include <iomanip>
#include <iostream>
#include <memory>
#include <sstream>
#include <string>
#include <vector>
#include <thread>


using Clock = std::chrono::steady_clock;

struct PortCtx {
  std::string name;
  Clock::time_point start;
  bool ignoreRealtime{true}; // filter MIDI Clock/ActiveSensing by default
};

static std::string hexDump(const std::vector<unsigned char>& m) {
  std::ostringstream oss;
  oss << std::hex << std::setfill('0');
  for (size_t i = 0; i < m.size(); ++i) {
    oss << "0x" << std::setw(2) << int(m[i]);
    if (i + 1 < m.size()) oss << " ";
  }
  return oss.str();
}

static void decodeChannelMessage(
    const std::vector<unsigned char>& msg,
    std::ostream& out) {
  if (msg.empty()) return;
  uint8_t status = msg[0];
  if (status < 0x80 || status > 0xEF) return; // not a channel voice msg

  uint8_t type = status & 0xF0;   // high nibble
  uint8_t ch   = (status & 0x0F); // 0..15 -> show 1..16
  auto safe = [&](size_t i)->int { return (i < msg.size()) ? int(msg[i]) : -1; };

  switch (type) {
    case 0x80: { // Note Off
      int note = safe(1), vel = safe(2);
      if (note >= 0 && vel >= 0)
        out << "NoteOff  ch=" << (ch+1) << " note=" << note << " vel=" << vel;
      break;
    }
    case 0x90: { // Note On (vel 0 == Note Off)
      int note = safe(1), vel = safe(2);
      if (note >= 0 && vel >= 0) {
        if (vel == 0)
          out << "NoteOff  ch=" << (ch+1) << " note=" << note << " vel=0";
        else
          out << "NoteOn   ch=" << (ch+1) << " note=" << note << " vel=" << vel;
      }
      break;
    }
    case 0xA0: { // Poly Aftertouch
      int note = safe(1), pressure = safe(2);
      if (note >= 0 && pressure >= 0)
        out << "PolyAT   ch=" << (ch+1) << " note=" << note << " pressure=" << pressure;
      break;
    }
    case 0xB0: { // Control Change
      int cc = safe(1), val = safe(2);
      if (cc >= 0 && val >= 0)
        out << "CC       ch=" << (ch+1) << " cc=" << cc << " val=" << val;
      break;
    }
    case 0xC0: { // Program Change
      int prog = safe(1);
      if (prog >= 0)
        out << "Program  ch=" << (ch+1) << " program=" << prog;
      break;
    }
    case 0xD0: { // Channel Aftertouch (mono pressure)
      int pressure = safe(1);
      if (pressure >= 0)
        out << "ChanAT   ch=" << (ch+1) << " pressure=" << pressure;
      break;
    }
    case 0xE0: { // Pitch Bend (14-bit, center=8192)
      int lsb = safe(1), msb = safe(2);
      if (lsb >= 0 && msb >= 0) {
        int value14 = (msb << 7) | lsb; // 0..16383
        int centered = value14 - 8192;  // -8192..+8191
        out << "PitchBd  ch=" << (ch+1) << " value=" << centered
            << " (raw=" << value14 << ")";
      }
      break;
    }
    default:
      out << "UnknownChannelMsg type=0x" << std::hex << int(type) << std::dec;
  }
}

static bool isRealtime(uint8_t b) {
  // MIDI real-time messages (0xF8..0xFF, but 0xF9,0xFD undefined)
  // Common noisy ones: 0xF8 Clock, 0xFA Start, 0xFB Continue, 0xFC Stop, 0xFE ActiveSensing, 0xFF Reset
  return b >= 0xF8;
}

static void midiCallback(double /*ts*/, std::vector<unsigned char>* message, void* userData) {
  auto* ctx = static_cast<PortCtx*>(userData);
  if (!message || message->empty()) return;

  // Filter real-time if desired (but still show Start/Stop if you want—toggle here).
  if (ctx->ignoreRealtime && isRealtime((*message)[0])) return;

  auto now = Clock::now();
  double ms = std::chrono::duration<double, std::milli>(now - ctx->start).count();

  std::ostringstream line;
  line << std::fixed << std::setprecision(1);
  line << "[" << std::setw(9) << ms << " ms] "
       << "[" << ctx->name << "]  ";

  uint8_t status = (*message)[0];

  if (status >= 0x80 && status <= 0xEF) {
    decodeChannelMessage(*message, line);
  } else {
    // System Common / System Real-Time
    switch (status) {
      case 0xF0: line << "SysEx (start)"; break;
      case 0xF1: line << "MTC Quarter Frame"; break;
      case 0xF2: line << "Song Position"; break;
      case 0xF3: line << "Song Select"; break;
      case 0xF6: line << "Tune Request"; break;
      case 0xF7: line << "SysEx (end)"; break;
      case 0xF8: line << "Timing Clock"; break;
      case 0xFA: line << "Start"; break;
      case 0xFB: line << "Continue"; break;
      case 0xFC: line << "Stop"; break;
      case 0xFE: line << "Active Sensing"; break;
      case 0xFF: line << "System Reset"; break;
      default:   line << "System 0x" << std::hex << int(status) << std::dec; break;
    }
  }

  line << "   | raw: " << hexDump(*message);
  std::cout << line.str() << std::endl;
}

int main() {
  try {
    auto midiIn = std::make_unique<RtMidiIn>(RtMidi::UNSPECIFIED, "midimon");
    unsigned int portCount = midiIn->getPortCount();

    // If one instance opens a port, we need separate instances to open the others.
    std::vector<std::unique_ptr<RtMidiIn>> inputs;
    std::vector<std::unique_ptr<PortCtx>> contexts;

    if (portCount == 0) {
      std::cout << "No MIDI input ports found.\n";
      return 0;
    }

    std::cout << "Found " << portCount << " MIDI input port(s):\n";
    for (unsigned int i = 0; i < portCount; ++i) {
      std::string name = midiIn->getPortName(i);
      std::cout << "  [" << i << "] " << name << "\n";
    }
    std::cout << "Opening all inputs… (Ctrl+C to quit)\n";

    for (unsigned int i = 0; i < portCount; ++i) {
      auto in = std::make_unique<RtMidiIn>(RtMidi::UNSPECIFIED, "midimon");
      auto ctx = std::make_unique<PortCtx>();
      ctx->name = in->getPortName(i);
      ctx->start = Clock::now();

      in->openPort(i);
      in->ignoreTypes(false, false, false); // don't ignore anything here; we filter in callback
      in->setCallback(&midiCallback, ctx.get());

      inputs.emplace_back(std::move(in));
      contexts.emplace_back(std::move(ctx));
    }

    // Idle loop
    while (true) {
      std::this_thread::sleep_for(std::chrono::milliseconds(200));
    }
  } catch (RtMidiError& e) {
    std::cerr << "RtMidiError: " << e.getMessage() << std::endl;
    return 1;
  } catch (const std::exception& e) {
    std::cerr << "Error: " << e.what() << std::endl;
    return 1;
  }
}
