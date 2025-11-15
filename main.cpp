// main.cpp
#define MINIAUDIO_IMPLEMENTATION
#include "miniaudio.h"
#include "RtMidi.h"

#include <atomic>
#include <chrono>
#include <cmath>
#include <cstdint>
#include <iostream>
#include <thread>
#include <unordered_map>
#include <vector>
#include <string>
#include <array>
#include <memory>
#include <random>
#include <algorithm>





using namespace std::chrono;

// ---------------- Constants ----------------
static constexpr double PI = 3.14159265358979323846;

// ---------------- Synth (two triangles + two binaural layers) ----------------
static double phaseA = 0.0, phaseB = 0.0, phaseC = 0.0, phaseD = 0.0; // A=bass, B=high, C/D=binaural

static const double baseFreqC2 = 65.406;   // C2
static const double baseFreqC4 = 261.626;  // C4

static std::atomic<double> freqA(baseFreqC2);  // bass
static std::atomic<double> freqB(baseFreqC4);  // high
static std::atomic<float>  gainA(0.2f);        // CH1 CC7 (bass)
static std::atomic<float>  gainB(0.2f);        // CH2 CC7 (high)
static std::atomic<float>  binauralOffsetA_Hz(0.0f); // CH1 CC16 → 0..40 Hz (for A->C)
static std::atomic<float>  binauralOffsetB_Hz(0.0f); // CH1 CC17 → 0..40 Hz (for B->D)
static constexpr bool FORCE_MONO = true;


// Delay spacing/intensity (0..1) — CH1 CC23
static std::atomic<float> delayIntensity{0.5f}; // 0=tight (1/16), 1=very spaced (1 bar)

// ---- Drum KIT layer (direct-to-master one-shots; loopable via CH7 NOTE 52) ----
static std::atomic<float> kitLayerGain{0.8f};   // CH5 CC7 (kit volume)
static std::vector<uint8_t> gIsKit;             // parallel to gSamples: 1 = kit sample

// ==== MIC LOOPER (record → loop) ====
static std::atomic<bool>  micRecStartReq{false};  // set by MIDI: start recording
static std::atomic<bool>  micRecStopReq{false};   // set by MIDI: stop rec → arm loop
static std::atomic<bool>  micLoopStopReq{false};  // set by MIDI: stop loop only

static bool   micLooperInit = false;
static bool   micRecOn      = false;             // audio-thread state
static bool   micLoopActive = false;             // audio-thread state

static std::vector<float> micLoopBuf;            // interleaved stereo
static size_t micLoopMaxFrames = 0;              // capacity
static size_t micRecFrames     = 0;              // how many frames captured
static size_t micLoopLenFrames = 0;              // final loop length (frames)
static size_t micLoopPosFrame  = 0;              // playback cursor



ma_device device;

// ---- APC40 maps (your custom mapping) ----
static const std::unordered_map<int,int> mapA_noteToSemis = {
  {0,0},{9,1},{1,2},{10,3},{2,4},{3,5},{12,6},{4,7},{13,8},{5,9},{14,10},{6,11},{7,12}
};
static const std::unordered_map<int,int> mapB_noteToSemis = {
  {16,0},{25,1},{17,2},{26,3},{18,4},{19,5},{28,6},{20,7},{29,8},{21,9},{30,10},{22,11},{23,12}
};

// === FX mixes (0..1) — CH1 CC21/CC22 ===
static std::atomic<float> reverbMix{0.0f}; // CC21
static std::atomic<float> delayMix{0.0f};  // CC22

// === Simple reverb state: 3 parallel damped feedback delays per channel ===
static bool fxInit = false;
static std::vector<float> rvBufL1, rvBufL2, rvBufL3;
static std::vector<float> rvBufR1, rvBufR2, rvBufR3;
static int rvPos1 = 0, rvPos2 = 0, rvPos3 = 0;
static float rvLP_L1 = 0.f, rvLP_L2 = 0.f, rvLP_L3 = 0.f;
static float rvLP_R1 = 0.f, rvLP_R2 = 0.f, rvLP_R3 = 0.f;

// === Stereo ping-pong delay state (tempo-aware length) ===
static std::vector<float> dlBufL, dlBufR;
static int dlPos = 0;
static int dlLen = 1; // current active length (samples)

// ==== MIC INPUT ====
static std::atomic<float> micGain{1.0f};        // CH6 CC7
static std::atomic<bool>  micOctDown{true};     // ALWAYS ON by default (no MIDI needed)
   // toggle: CH6 NOTE 8

// Granular octave-down (-12 semitones) state
static bool micInit = false;
static std::vector<float> micRingL, micRingR, micWin; // 2s ring + Hann window
static size_t micRingSize = 0, micWritePos = 0;
static double micReadA = 0.0, micReadB = 0.0;
static int micGrainLen = 0, micGrainHop = 0, micBaseDelay = 0; // ~40ms grains, 50% overlap
static int micPhaseA = 0, micPhaseB = 0;

// --- Simple formant EQ (optional) ---
struct Biquad {
  float b0=1, b1=0, b2=0, a1=0, a2=0;
  float z1L=0, z2L=0, z1R=0, z2R=0;
  inline float procL(float x){ float y=b0*x + z1L; z1L=b1*x - a1*y + z2L; z2L=b2*x - a2*y; return y; }
  inline float procR(float x){ float y=b0*x + z1R; z1R=b1*x - a1*y + z2R; z2R=b2*x - a2*y; return y; }
};
inline void setPeaking(Biquad& q, double sr, double f0, double Q, double dB){
  double w0=2.0*PI*f0/sr, cosw=std::cos(w0), sinw=std::sin(w0);
  double A=std::pow(10.0, dB/40.0), alpha=sinw/(2.0*Q);
  double b0=1+alpha*A, b1=-2*cosw, b2=1-alpha*A;
  double a0=1+alpha/A, a1=-2*cosw, a2=1-alpha/A;
  q.b0=(float)(b0/a0); q.b1=(float)(b1/a0); q.b2=(float)(b2/a0);
  q.a1=(float)(a1/a0); q.a2=(float)(a2/a0);
}
static std::atomic<float> micFormant{2.5f}; // default formant darken (always on)

static Biquad micEQLo, micEQHi;




// Triangle helper (phase in [0,1) -> [-1,1])
inline float tri(double t) {
  if (t < 0.25) return float(t * 4.0);
  if (t < 0.75) return float(2.0 - t * 4.0);
  return float(-4.0 + t * 4.0);
}

// ---------------- Sample Layer ----------------
struct Sample { std::vector<float> pcm; uint64_t frames = 0; };

// MOVEABLE SampleTrim so it can live in std::vector
struct SampleTrim {
  std::atomic<uint64_t> in;
  std::atomic<uint64_t> len;
  SampleTrim() : in(0), len(0) {}
  SampleTrim(const SampleTrim&)            = delete;
  SampleTrim& operator=(const SampleTrim&) = delete;
  SampleTrim(SampleTrim&& other) noexcept {
    in.store(other.in.load(std::memory_order_relaxed),  std::memory_order_relaxed);
    len.store(other.len.load(std::memory_order_relaxed), std::memory_order_relaxed);
  }
  SampleTrim& operator=(SampleTrim&& other) noexcept {
    if (this != &other) {
      in.store(other.in.load(std::memory_order_relaxed),  std::memory_order_relaxed);
      len.store(other.len.load(std::memory_order_relaxed), std::memory_order_relaxed);
    }
    return *this;
  }
};

struct Voice {
  int sampleId = -1;
  uint64_t pos = 0;   // current frame
  uint64_t end = 0;   // exclusive end frame (in + len) — used for one-shots
  bool active = false;
  bool looping = false; // NEW: if true, wrap [in,end) continuously and respond live to trim edits
  bool isDrum = false;  // NEW: drum layer routing
};

static std::vector<Sample>       gSamples;
static std::vector<SampleTrim>   gSampleTrim;     // parallel to gSamples
static std::vector<std::string>  gSampleNames;    // for logs

static constexpr int kMaxVoices = 32;
static std::array<Voice, kMaxVoices> gVoices;

// Selection tracking
static std::atomic<int> gSelectedSample{-1};
static std::array<int,16> gLastSampleByCh; // init to -1 in main()
static std::atomic<int> gLastAnySample{-1}; // global fallback

// --- Loop modifier (hold to create a loop on sample trigger) ---
static std::atomic<bool> gLoopShiftHeld{false};   // CH7 NOTE 52 held?
// --- Loop clear request (CH1 NOTE 8) ---
static std::atomic<bool> gClearLoops{false};


// Simple lock-free trigger queue (MIDI->audio)
struct Trigger { int sampleId = -1; bool loop = false; };   // NEW: loop flag
static constexpr int kTrigQ = 128;
static std::array<Trigger, kTrigQ> gTrigQ;
static std::atomic<int> trigHead{0}, trigTail{0};

inline void pushTrigger(int sid, bool loop) {
  int h = trigHead.load(std::memory_order_relaxed);
  int n = (h + 1) % kTrigQ;
  if (n == trigTail.load(std::memory_order_acquire)) return; // drop if full
  gTrigQ[h].sampleId = sid;
  gTrigQ[h].loop     = loop;
  trigHead.store(n, std::memory_order_release);
}
inline bool popTrigger(int& sid, bool& loop) {
  int t = trigTail.load(std::memory_order_relaxed);
  if (t == trigHead.load(std::memory_order_acquire)) return false;
  sid  = gTrigQ[t].sampleId;
  loop = gTrigQ[t].loop;
  trigTail.store((t + 1) % kTrigQ, std::memory_order_release);
  return true;
}

// Sample layer gain (CH3 CC7)
static std::atomic<float> sampleLayerGain{0.5f}; // scaled 0..0.7 in mixer

// ==== DJ FILTER (CC50) ====
static std::atomic<float> djFilterParam{0.5f};
static float lpfYL = 0.0f, lpfYR = 0.0f;          // LPF state
static float hpfYL = 0.0f, hpfYR = 0.0f;          // HPF state
static float hpfXL = 0.0f, hpfXR = 0.0f;          // HPF previous inputs

// === SENTENCE MODE (where fair share when we send death) ===
static std::array<int,7> gSentenceIds{};  // filled in main by filename lookup
static std::atomic<bool> gSentenceLoopOn{false}; // toggled by CH3/N50
// runtime (audio thread only)
static bool   sSentenceActive   = false;
static int    sSentenceWordIdx  = 0;   // 0..6
static int    sSentenceOddCount = 0;   // 0..8 (8th odd beat is silence)



// Separate volume for LOOP layer
static std::atomic<float> loopLayerGain{0.5f};   // CH7 CC7

// Separate DJ-style filter for LOOP layer (0..1; 0=LPF, 0.5=dry, 1=HPF)
static std::atomic<float> loopFilterParam{0.5f}; // CH1 CC54

// Master volume (all layers including synth)
static std::atomic<float> masterGain{1.0f};      // CH1 CC14

// LOOP-layer filter states
static float lpfYL_loop = 0.0f, lpfYR_loop = 0.0f;
static float hpfYL_loop = 0.0f, hpfYR_loop = 0.0f;
static float hpfXL_loop = 0.0f, hpfXR_loop = 0.0f;

// === DRUM LOOP LAYER ===
// Controls
static std::atomic<float> drumLayerGain{0.8f};   // CH4 CC7 (drum volume)
static std::atomic<float> drumFilterParam{0.5f}; // CH1 CC51 (DJ-style LPF/HPF)
static std::atomic<float> drumBPM{120.0f};       // CH1 CC20 (50..180 BPM)

// Filter states (drum layer)
static float lpfYL_drum = 0.0f, lpfYR_drum = 0.0f;
static float hpfYL_drum = 0.0f, hpfYR_drum = 0.0f;
static float hpfXL_drum = 0.0f, hpfXR_drum = 0.0f;

// Sequencer: 16-step pattern
struct DrumStep { int sampleId = -1; uint64_t in = 0; uint64_t len = 0; bool active = false; };
static std::array<DrumStep, 16> gDrumSteps;
static std::atomic<bool> gDrumRegenRequest{true}; // start with a pattern

// Sequencer runtime
static uint64_t gDrumSampleCounter = 0; // running sample clock
static uint64_t gDrumNextStep      = 0; // sample time of next step
static int      gDrumStepIndex     = 0; // 0..15

// RNG
static std::mt19937 gRng((uint32_t)std::chrono::high_resolution_clock::now().time_since_epoch().count());



inline double expoLerp(double f1, double f2, double t) {
  f1 = std::max(1.0, f1);
  f2 = std::max(1.0, f2);
  return f1 * std::pow(f2 / f1, t);
}

static void makeRandomDrumPattern(uint32_t sampleRate) {
  // Build a pool of allowed (non-KIT) samples
  std::vector<int> allowed;
  allowed.reserve(gSamples.size());
  for (int i = 0; i < (int)gSamples.size(); ++i) {
    if (gSamples[i].frames == 0) continue;
    // exclude KIT samples
    if (i < (int)gIsKit.size() && gIsKit[i]) continue;
    allowed.push_back(i);
  }

  if (allowed.empty()) {
    // nothing eligible → clear pattern
    for (auto& st : gDrumSteps) st = DrumStep{};
    gDrumStepIndex = 0;
    return;
  }

  std::uniform_int_distribution<int> pick(0, (int)allowed.size() - 1);
  std::uniform_real_distribution<float> activeDist(0.0f, 1.0f);

  // Slice durations ~10..180 ms
  const int minLen = (int)std::lround(sampleRate * 0.010);
  const int maxLen = (int)std::lround(sampleRate * 0.180);
  std::uniform_int_distribution<int> lenDist(minLen, maxLen);

  for (int i = 0; i < 16; ++i) {
    DrumStep step;
    step.sampleId = allowed[pick(gRng)];

    const auto& s = gSamples[step.sampleId];
    int len = std::min<int>(lenDist(gRng), (int)s.frames);
    uint64_t maxIn = (s.frames > (uint64_t)len) ? (s.frames - (uint64_t)len) : 0ull;
    std::uniform_int_distribution<uint64_t> inDist(0ull, maxIn);

    step.len    = (uint64_t)len;
    step.in     = inDist(gRng);
    step.active = (activeDist(gRng) < 0.6f); // ~60% fill

    gDrumSteps[i] = step;
  }

  gDrumStepIndex = 0;
}



// WAV loader (to f32 stereo @ deviceRate)
static bool loadSampleFile(const std::string& path, uint32_t deviceRate, Sample& out) {
  ma_decoder_config cfg = ma_decoder_config_init(ma_format_f32, 2, deviceRate);
  ma_decoder dec;
  if (ma_decoder_init_file(path.c_str(), &cfg, &dec) != MA_SUCCESS) {
    std::cerr << "Failed to load " << path << "\n";
    return false;
  }
  std::vector<float> pcm;
  constexpr ma_uint64 CHUNK_FRAMES = 4096;
  std::vector<float> chunk(CHUNK_FRAMES * 2); // interleaved stereo
  for (;;) {
    ma_uint64 framesRead = 0;
    ma_result r = ma_decoder_read_pcm_frames(&dec, chunk.data(), CHUNK_FRAMES, &framesRead);
    if (r != MA_SUCCESS && r != MA_AT_END) { std::cerr << "Decode error " << path << "\n"; break; }
    if (framesRead == 0) break;
    pcm.insert(pcm.end(), chunk.begin(), chunk.begin() + (size_t)(framesRead * 2));
    if (r == MA_AT_END) break;
  }
  ma_decoder_uninit(&dec);
  out.frames = pcm.size() / 2;
  out.pcm = std::move(pcm);
  std::cout << "Loaded " << path << " (" << out.frames << " frames)\n";
  return out.frames > 0;
}

// channel+note key
inline int keyCN(int ch, int note) { return ((ch & 0xF) << 8) | (note & 0x7F); }
static std::unordered_map<int,int> sampleKeyToId;

// ---------------- Audio callback (synth + samples + DJ filter) ----------------
static void dataCallback(ma_device* d, void* out, const void* in, ma_uint32 frames) {
  float* buffer = (float*)out;
  const float* inbuf = (const float*)in;   // <-- mic/capture
  const double sr = (double)d->sampleRate;


// --- FX one-time init (sizes depend on sample rate) ---
if (!fxInit) {
  // Reverb: 3 delay lengths (seconds) — roughly Freeverb comb region, scaled for 48k
  const double d1 = 0.0297, d2 = 0.0371, d3 = 0.0411;
  size_t n1 = (size_t)std::max(2.0, std::round(sr * d1));
  size_t n2 = (size_t)std::max(2.0, std::round(sr * d2));
  size_t n3 = (size_t)std::max(2.0, std::round(sr * d3));
  rvBufL1.assign(n1, 0.0f); rvBufR1.assign(n1 + 23, 0.0f); // small stereo offset
  rvBufL2.assign(n2, 0.0f); rvBufR2.assign(n2 + 37, 0.0f);
  rvBufL3.assign(n3, 0.0f); rvBufR3.assign(n3 + 53, 0.0f);

// Delay: allocate up to 6s; actual length set per-block from BPM + intensity
const size_t maxDelay = (size_t)std::round(sr * 6.0);
dlBufL.assign(maxDelay, 0.0f);
dlBufR.assign(maxDelay, 0.0f);
dlLen = std::max(1, (int)std::min<size_t>(maxDelay, (size_t)std::round(sr * 0.4))); // default ~400ms


  fxInit = true;
}

  // --- one-time init for MIC shifter ---
  if (!micInit) {
    micRingSize = (size_t)std::round(sr * 2.0);               // ~2s ring
    micRingL.assign(micRingSize, 0.0f);
    micRingR.assign(micRingSize, 0.0f);

// was ~40ms
micGrainLen  = std::clamp((int)std::round(sr * 0.080), 512, 16384); // ~80ms
micGrainHop  = micGrainLen / 2;                                     // 50% overlap
micBaseDelay = micGrainLen * 4;                                     // ~320ms lookback


    micWin.resize(micGrainLen);
    for (int n = 0; n < micGrainLen; ++n)
      micWin[n] = 0.5f * (1.0f - std::cos(2.0 * PI * (double)n / (double)(micGrainLen - 1)));

    micPhaseA = 0;
    micPhaseB = micGrainHop;
    micWritePos = 0;

    // seed read heads behind write pointer
    size_t base = (micRingSize + micWritePos - (size_t)micBaseDelay) % micRingSize;
    micReadA = (double)base;
    micReadB = (double)((base + (size_t)micGrainHop) % micRingSize);

    micInit = true;
  }

// --- one-time init for MIC LOOPER ring/buffer ---
if (!micLooperInit) {
  // e.g., up to 30 seconds max @ current sample rate
  micLoopMaxFrames = (size_t)std::llround(sr * 30.0);
  micLoopBuf.assign(micLoopMaxFrames * 2, 0.0f);
  micRecFrames = 0;
  micLooperInit = true;
}

  // tiny helper for ring linear interpolation
  auto interp = [&](const std::vector<float>& ring, double pos)->float {
    // wrap into [0, micRingSize)
    if (pos >= (double)micRingSize) pos -= std::floor(pos / (double)micRingSize) * (double)micRingSize;
    size_t i0 = (size_t)pos;
    size_t i1 = (i0 + 1 < micRingSize) ? (i0 + 1) : 0;
    float  frac = (float)(pos - (double)i0);
    return ring[i0] + (ring[i1] - ring[i0]) * frac;
  };

// If a clear-loops request is pending, kill all looping voices (done in audio thread)
if (gClearLoops.exchange(false, std::memory_order_acq_rel)) {
  for (auto& v : gVoices) {
    if (v.looping) v.active = false;
  }
}

// Refresh drum pattern on request (safe in audio thread)
if (gDrumRegenRequest.exchange(false, std::memory_order_acq_rel)) {
  makeRandomDrumPattern((uint32_t)sr);
  // fire next step immediately
  gDrumNextStep = gDrumSampleCounter;
}

// Sentence mode: follow the toggled loop state from MIDI
{
  bool want = gSentenceLoopOn.load(std::memory_order_acquire);
  if (want && !sSentenceActive) {
    sSentenceActive   = true;
    sSentenceWordIdx  = 0;
    sSentenceOddCount = 0; // first word fires at next eligible odd step
  } else if (!want && sSentenceActive) {
    sSentenceActive   = false;
  }
}







  // Pull pending triggers and start voices
  int sid; bool loop;
  while (popTrigger(sid, loop)) {
    for (auto& v : gVoices) {
      if (!v.active) {
        v.sampleId = sid;
        v.looping  = loop;
v.isDrum   = false;   // make sure queued one-shots/loopers are NOT treated as drum hits

        const auto& s  = gSamples[sid];
        const auto& st = gSampleTrim[sid];
        uint64_t in  = st.in.load(std::memory_order_relaxed);
        uint64_t len = st.len.load(std::memory_order_relaxed);
        if (len == 0 || in >= s.frames) { in = 0; len = s.frames; }
        uint64_t end = in + len;
        if (end > s.frames) end = s.frames;
        v.pos = in;
        v.end = end;                 // used by one-shots; loopers will update live
        v.active = (v.pos < end);
        break;
      }
    }
  }

  // Snapshot synth params
  const double fA = std::max(0.0, freqA.load());
  const double fB = std::max(0.0, freqB.load());
  const float  gA = gainA.load();
  const float  gB = gainB.load();
  const double fC = std::max(0.0, fA + (double)binauralOffsetA_Hz.load());
  const double fD = std::max(0.0, fB + (double)binauralOffsetB_Hz.load());
  const double incA = fA / sr, incB = fB / sr, incC = fC / sr, incD = fD / sr;

const float shotGain  = sampleLayerGain.load() * 0.7f; // non-loop sample layer
const float loopGain  = loopLayerGain.load()   * 0.7f; // loop layer
const float master    = masterGain.load();             // master volume

const float drumGain  = drumLayerGain.load() * 0.7f; // drum layer


  // DJ filter params once per block
  const float knob = djFilterParam.load();   // 0..1
  const bool leftLPF  = (knob < 0.5f - 1e-6f);
  const bool rightHPF = (knob > 0.5f + 1e-6f);
  const double mixLPF = leftLPF  ? (0.5 - knob) / 0.5 : 0.0;   // 0..1
  const double mixHPF = rightHPF ? (knob - 0.5) / 0.5 : 0.0;   // 0..1

  // Map knob to cutoffs (expo)
  const double fcLPF = leftLPF  ? expoLerp(18000.0, 200.0,  mixLPF) : 18000.0;
  const double fcHPF = rightHPF ? expoLerp(30.0,    8000.0, mixHPF) : 30.0;

  // One-pole coefficients
  const double aLPF = std::exp(-2.0 * PI * fcLPF / sr); // y = (1-a)*x + a*y
  const double bLPF = 1.0 - aLPF;
  const double aHPF = std::exp(-2.0 * PI * fcHPF / sr); // y = a*(y + x - xPrev)

// Drum sequencer timing
const double bpm = std::clamp((double)drumBPM.load(), 50.0, 180.0);
const uint64_t stepSamples = (uint64_t)std::llround(sr * 60.0 / (bpm * 4.0)); // 16th notes

// DRUM-layer DJ filter params
const float drumKnob = drumFilterParam.load();
const bool drumLeftLPF  = (drumKnob < 0.5f - 1e-6f);
const bool drumRightHPF = (drumKnob > 0.5f + 1e-6f);
const double drumMixLPF = drumLeftLPF  ? (0.5 - drumKnob) / 0.5 : 0.0;
const double drumMixHPF = drumRightHPF ? (drumKnob - 0.5) / 0.5 : 0.0;

const double drumFcLPF = drumLeftLPF  ? expoLerp(18000.0, 200.0,  drumMixLPF) : 18000.0;
const double drumFcHPF = drumRightHPF ? expoLerp(30.0,    8000.0, drumMixHPF) : 30.0;

const double aLPF_drum = std::exp(-2.0 * PI * drumFcLPF / sr);
const double bLPF_drum = 1.0 - aLPF_drum;
const double aHPF_drum = std::exp(-2.0 * PI * drumFcHPF / sr);

// LOOP-layer DJ filter params (same mapping, independent knob)
const float loopKnob = loopFilterParam.load();
const bool loopLeftLPF  = (loopKnob < 0.5f - 1e-6f);
const bool loopRightHPF = (loopKnob > 0.5f + 1e-6f);
const double loopMixLPF = loopLeftLPF  ? (0.5 - loopKnob) / 0.5 : 0.0;
const double loopMixHPF = loopRightHPF ? (loopKnob - 0.5) / 0.5 : 0.0;

const double loopFcLPF = loopLeftLPF  ? expoLerp(18000.0, 200.0,  loopMixLPF) : 18000.0;
const double loopFcHPF = loopRightHPF ? expoLerp(30.0,    8000.0, loopMixHPF) : 30.0;

// One-pole coefficients (loop layer)
const double aLPF_loop = std::exp(-2.0 * PI * loopFcLPF / sr);
const double bLPF_loop = 1.0 - aLPF_loop;
const double aHPF_loop = std::exp(-2.0 * PI * loopFcHPF / sr);

// --- Mic formant EQ design for this block (always on) ---
{
  const float formAmt = std::clamp(micFormant.load(std::memory_order_relaxed), 0.0f, 1.0f);
  setPeaking(micEQLo, sr,  300.0, 0.8,  +6.0 * formAmt);   // warm chest
  setPeaking(micEQHi, sr, 2500.0, 1.2, -12.0 * formAmt);   // reduce brightness
}

// --- Mic looper state updates from MIDI (once per block) ---
if (micRecStartReq.exchange(false, std::memory_order_acq_rel)) {
  micRecOn = true;
  micLoopActive = false;        // stop any current loop while recording a new one
  micRecFrames = 0;             // start fresh
}

if (micRecStopReq.exchange(false, std::memory_order_acq_rel)) {
  micRecOn = false;
  micLoopLenFrames = micRecFrames;     // freeze length
  micLoopPosFrame  = 0;
  micLoopActive = (micLoopLenFrames > 0);
}

if (micLoopStopReq.exchange(false, std::memory_order_acq_rel)) {
  micLoopActive = false;
}



  for (ma_uint32 i = 0; i < frames; ++i) {

// --- Drum step scheduler ---
if (gDrumSampleCounter >= gDrumNextStep) {
  const DrumStep st = gDrumSteps[gDrumStepIndex];
  if (st.active && st.sampleId >= 0 && st.sampleId < (int)gSamples.size()
      && !(st.sampleId < (int)gIsKit.size() && gIsKit[st.sampleId])) {

    // start a DRUM voice directly (no queue)
    for (auto& v : gVoices) {
      if (!v.active) {
        v.sampleId = st.sampleId;
        v.looping  = false;
        v.isDrum   = true;
        v.pos      = st.in;
        uint64_t end = st.in + st.len;
        const uint64_t total = gSamples[v.sampleId].frames;
        if (end > total) end = total;
        v.end    = end;
        v.active = (v.pos < v.end);
break;



      }
    }
  }

  // --- Sentence scheduler: fire on beats 1,3,5,7,9,11,13; beat 15 is silence
  if (sSentenceActive) {
    if ((gDrumStepIndex & 1) == 0) { // 0,2,4,... => 1,3,5,...
      if (sSentenceOddCount < 7) {
        int sid = (sSentenceWordIdx >= 0 && sSentenceWordIdx < (int)gSentenceIds.size())
                    ? gSentenceIds[sSentenceWordIdx] : -1;
        if (sid >= 0 && sid < (int)gSamples.size()) {
          // normal one-shot, full length, through sample layer (CH3 CC7 + CC50)
          for (auto& v : gVoices) {
            if (!v.active) {
              v.sampleId = sid;
              v.looping  = false;
              v.isDrum   = false;
              v.pos      = 0;
              v.end      = gSamples[sid].frames;
              v.active   = (v.pos < v.end);
              break;
            }
          }
        }
        sSentenceWordIdx++;
      }
    sSentenceOddCount++;
    if (sSentenceOddCount >= 8) {  // 7 words + 1 silent odd beat
      if (gSentenceLoopOn.load(std::memory_order_relaxed)) {
        // loop back to the start of the sentence
        sSentenceWordIdx  = 0;
        sSentenceOddCount = 0;
      } else {
        sSentenceActive = false;
      }
    }

    }
  }

  gDrumStepIndex = (gDrumStepIndex + 1) & 15;
  gDrumNextStep += stepSamples;
}

    // --- Synth ---
    const float sA = tri(phaseA) * gA;
    const float sB = tri(phaseB) * gB;
    const float sC = tri(phaseC) * gA; // same volume as A
    const float sD = tri(phaseD) * gB; // same volume as B

    float L = sA + sB + sD;
    float R = sA + sB + sC;

    // advance synth phases
    phaseA += incA; if (phaseA >= 1.0) phaseA -= 1.0;
    phaseB += incB; if (phaseB >= 1.0) phaseB -= 1.0;
    phaseC += incC; if (phaseC >= 1.0) phaseC -= 1.0;
    phaseD += incD; if (phaseD >= 1.0) phaseD -= 1.0;

// --- Samples: three buses: ONE-SHOTS, LOOPERS, DRUM ---
float shotL = 0.0f, shotR = 0.0f;
float loopL = 0.0f, loopR = 0.0f;
float drumL = 0.0f, drumR = 0.0f;
float kitL  = 0.0f, kitR  = 0.0f;

for (auto& v : gVoices) {
  if (!v.active) continue;

  const Sample& s = gSamples[v.sampleId];

  if (v.looping) {
    // Live-read trim every sample for loopers
    const auto& st = gSampleTrim[v.sampleId];
    uint64_t in  = st.in.load(std::memory_order_relaxed);
    uint64_t len = st.len.load(std::memory_order_relaxed);
    if (len == 0 || in >= s.frames) { in = 0; len = s.frames; }
    uint64_t end = in + len;
    if (end > s.frames) end = s.frames;

    // keep position inside the current window
    if (v.pos < in || v.pos >= end) v.pos = in;

    const size_t idx = (size_t)v.pos * 2;
    loopL += s.pcm[idx + 0] * loopGain;
    loopR += s.pcm[idx + 1] * loopGain;

    // advance and wrap next sample if needed
    ++v.pos;
    if (v.pos >= end) v.pos = in;

} else {
  // One-shot (fixed in/end) — may be DRUM, KIT, or normal SHOT
  if (v.pos >= v.end) { v.active = false; continue; }
  const size_t idx = (size_t)v.pos * 2;

  if (v.isDrum) {
    // sequencer hits
    drumL += s.pcm[idx + 0] * drumGain;
    drumR += s.pcm[idx + 1] * drumGain;
  } else if (!gIsKit.empty() && gIsKit[v.sampleId]) {
    // KIT one-shots: direct to master (no LP/HP, no send to reverb/delay)
    const float g = kitLayerGain.load(std::memory_order_relaxed);
    kitL += s.pcm[idx + 0] * g;
    kitR += s.pcm[idx + 1] * g;
  } else {
    // regular one-shots (spoken/etc.), go through sample bus + its DJ filter
    shotL += s.pcm[idx + 0] * shotGain;
    shotR += s.pcm[idx + 1] * shotGain;
  }

  ++v.pos;
  if (v.pos >= v.end) v.active = false;
}


}

// --- DJ filter: apply to ONE-SHOTS (sample layer) ---
float lpfL = lpfYL = float(bLPF * shotL + aLPF * lpfYL);
float lpfR = lpfYR = float(bLPF * shotR + aLPF * lpfYR);

float hpfL = hpfYL = float(aHPF * (hpfYL + shotL - hpfXL));
float hpfR = hpfYR = float(aHPF * (hpfYR + shotR - hpfXR));
hpfXL = shotL; hpfXR = shotR;

// crossfade so center is truly dry
float shotOutL = shotL;
float shotOutR = shotR;
if (leftLPF) {
  shotOutL = float((1.0 - mixLPF) * shotL + mixLPF * lpfL);
  shotOutR = float((1.0 - mixLPF) * shotR + mixLPF * lpfR);
} else if (rightHPF) {
  shotOutL = float((1.0 - mixHPF) * shotL + mixHPF * hpfL);
  shotOutR = float((1.0 - mixHPF) * shotR + mixHPF * hpfR);
}

// --- DJ filter: apply to DRUM layer (independent knob/states) ---
float lpfL_drummed = lpfYL_drum = float(bLPF_drum * drumL + aLPF_drum * lpfYL_drum);
float lpfR_drummed = lpfYR_drum = float(bLPF_drum * drumR + aLPF_drum * lpfYR_drum);

float hpfL_drummed = hpfYL_drum = float(aHPF_drum * (hpfYL_drum + drumL - hpfXL_drum));
float hpfR_drummed = hpfYR_drum = float(aHPF_drum * (hpfYR_drum + drumR - hpfXR_drum));
hpfXL_drum = drumL; hpfXR_drum = drumR;

// crossfade so center is truly dry
float drumOutL = drumL;
float drumOutR = drumR;
if (drumLeftLPF) {
  drumOutL = float((1.0 - drumMixLPF) * drumL + drumMixLPF * lpfL_drummed);
  drumOutR = float((1.0 - drumMixLPF) * drumR + drumMixLPF * lpfR_drummed);
} else if (drumRightHPF) {
  drumOutL = float((1.0 - drumMixHPF) * drumL + drumMixHPF * hpfL_drummed);
  drumOutR = float((1.0 - drumMixHPF) * drumR + drumMixHPF * hpfR_drummed);
}


// --- DJ filter: apply to LOOP layer (independent knob/states) ---
float lpfL_looped = lpfYL_loop = float(bLPF_loop * loopL + aLPF_loop * lpfYL_loop);
float lpfR_looped = lpfYR_loop = float(bLPF_loop * loopR + aLPF_loop * lpfYR_loop);

float hpfL_looped = hpfYL_loop = float(aHPF_loop * (hpfYL_loop + loopL - hpfXL_loop));
float hpfR_looped = hpfYR_loop = float(aHPF_loop * (hpfYR_loop + loopR - hpfXR_loop));
hpfXL_loop = loopL; hpfXR_loop = loopR;

// crossfade so center is truly dry
float loopOutL = loopL;
float loopOutR = loopR;
if (loopLeftLPF) {
  loopOutL = float((1.0 - loopMixLPF) * loopL + loopMixLPF * lpfL_looped);
  loopOutR = float((1.0 - loopMixLPF) * loopR + loopMixLPF * lpfR_looped);
} else if (loopRightHPF) {
  loopOutL = float((1.0 - loopMixHPF) * loopL + loopMixHPF * hpfL_looped);
  loopOutR = float((1.0 - loopMixHPF) * loopR + loopMixHPF * hpfR_looped);
}

// --- Build DRUM+LOOP bus input to FX (post each layer’s DJ filter) ---
float fxInL = loopOutL + drumOutL;
float fxInR = loopOutR + drumOutR;

// --- Reverb (3 parallel damped feedback delays per channel) ---
const float rvFb   = 0.72f;   // feedback
const float rvDamp = 0.20f;   // 1-pole LP in feedback path
float rvWetL = 0.0f, rvWetR = 0.0f;

// line 1
{
  float yL = rvBufL1[rvPos1];
  float yR = rvBufR1[rvPos1 % (int)rvBufR1.size()];
  rvLP_L1 += rvDamp * (yL - rvLP_L1);
  rvLP_R1 += rvDamp * (yR - rvLP_R1);
  rvBufL1[rvPos1] = fxInL + rvFb * rvLP_L1;
  rvBufR1[rvPos1 % (int)rvBufR1.size()] = fxInR + rvFb * rvLP_R1;
  rvWetL += yL; rvWetR += yR;
}

// line 2
{
  float yL = rvBufL2[rvPos2];
  float yR = rvBufR2[rvPos2 % (int)rvBufR2.size()];
  rvLP_L2 += rvDamp * (yL - rvLP_L2);
  rvLP_R2 += rvDamp * (yR - rvLP_R2);
  rvBufL2[rvPos2] = fxInL + rvFb * rvLP_L2;
  rvBufR2[rvPos2 % (int)rvBufR2.size()] = fxInR + rvFb * rvLP_R2;
  rvWetL += yL; rvWetR += yR;
}

// line 3
{
  float yL = rvBufL3[rvPos3];
  float yR = rvBufR3[rvPos3 % (int)rvBufR3.size()];
  rvLP_L3 += rvDamp * (yL - rvLP_L3);
  rvLP_R3 += rvDamp * (yR - rvLP_R3);
  rvBufL3[rvPos3] = fxInL + rvFb * rvLP_L3;
  rvBufR3[rvPos3 % (int)rvBufR3.size()] = fxInR + rvFb * rvLP_R3;
  rvWetL += yL; rvWetR += yR;
}

// advance reverb indices
rvPos1 = (rvPos1 + 1) % (int)rvBufL1.size();
rvPos2 = (rvPos2 + 1) % (int)rvBufL2.size();
rvPos3 = (rvPos3 + 1) % (int)rvBufL3.size();

// subtle crossfeed for width + average
rvWetL = (rvWetL + 0.15f * rvWetR) / 3.0f;
rvWetR = (rvWetR + 0.15f * rvWetL) / 3.0f;

// Reverb insert crossfade
const float rvMix = std::clamp(reverbMix.load(std::memory_order_relaxed), 0.0f, 1.0f);
float postRvL = (1.0f - rvMix) * fxInL + rvMix * rvWetL;
float postRvR = (1.0f - rvMix) * fxInR + rvMix * rvWetR;

// --- Tempo-aware ping-pong delay (insert) ---
const double bpmDelay = std::clamp((double)drumBPM.load(std::memory_order_relaxed), 50.0, 180.0);
const double qNoteSamples = sr * 60.0 / bpmDelay;   // quarter note

// Map CC23 0..1 -> musical multiplier 1/16 .. 1 bar (0.25 .. 4.0 quarters)
const double tInt   = std::clamp((double)delayIntensity.load(std::memory_order_relaxed), 0.0, 3.0);
// exponential curve feels more musical (small moves at short times, bigger jumps later)
const double mult   = expoLerp(0.25, 4.0, tInt);  // 1/16 → 1 bar
int targetLen       = (int)std::llround(qNoteSamples * mult);

// clamp to buffer
targetLen = std::clamp(targetLen, 1, (int)dlBufL.size() - 1);

// apply if changed
if (targetLen != dlLen) {
  dlLen = targetLen;
  if (dlPos >= dlLen) dlPos = dlPos % dlLen;
}


// read
float dlyOutL = dlBufL[dlPos];
float dlyOutR = dlBufR[dlPos];

// write with cross-feedback for ping-pong
const float dlyFb = 0.35f;
dlBufL[dlPos] = postRvL + dlyFb * dlyOutR;
dlBufR[dlPos] = postRvR + dlyFb * dlyOutL;

// advance
dlPos++; if (dlPos >= dlLen) dlPos = 0;

// Delay insert crossfade
const float dlMix = std::clamp(delayMix.load(std::memory_order_relaxed), 0.0f, 1.0f);
float fxOutL = (1.0f - dlMix) * postRvL + dlMix * dlyOutL;
float fxOutR = (1.0f - dlMix) * postRvR + dlMix * dlyOutR;

// === MIC + MIC LOOPER (both on CH6 CC7) ===
float inL = 0.0f, inR = 0.0f;
if (in) {
  // use the inbuf declared at the top of dataCallback
  inL = inbuf[2*i + 0];
  inR = inbuf[2*i + 1];
}

// write capture into ring
micRingL[micWritePos] = inL;
micRingR[micWritePos] = inR;
micWritePos++; if (micWritePos >= micRingSize) micWritePos = 0;

// produce mic (oct-down or dry)
float micOutL = 0.0f, micOutR = 0.0f;
if (micOctDown.load(std::memory_order_relaxed)) {
  const float wA = micWin[micPhaseA];
  const float wB = micWin[micPhaseB];

  float aL = interp(micRingL, micReadA);
  float aR = interp(micRingR, micReadA);
  float bL = interp(micRingL, micReadB);
  float bR = interp(micRingR, micReadB);

  micOutL = aL * wA + bL * wB;
  micOutR = aR * wA + bR * wB;

  const double ratio = 0.6; // -36 st (semitone as in your code)
  micReadA += ratio; micReadB += ratio;

  // advance window phases and re-seed at hop boundaries
  micPhaseA++;
  if (micPhaseA >= micGrainLen) {
    micPhaseA = 0;
    size_t base = (micRingSize + micWritePos - (size_t)micBaseDelay) % micRingSize;
    micReadA = (double)base;
  }
  micPhaseB++;
  if (micPhaseB >= micGrainLen) {
    micPhaseB = 0;
    size_t base = (micRingSize + micWritePos - (size_t)micBaseDelay) % micRingSize;
    size_t b2   = base + (size_t)micGrainHop; if (b2 >= micRingSize) b2 -= micRingSize;
    micReadB = (double)b2;
  }
} else {
  micOutL = inL;
  micOutR = inR;
}

// Always-on formant EQ
micOutL = micEQHi.procL(micEQLo.procL(micOutL));
micOutR = micEQHi.procR(micEQLo.procR(micOutR));

// --- MIC LOOPER: playback first, then capture ---
float micLoopL = 0.0f, micLoopR = 0.0f;
if (micLoopActive && micLoopLenFrames > 0) {
  size_t rd = (micLoopPosFrame % micLoopLenFrames) * 2;
  micLoopL = micLoopBuf[rd + 0];
  micLoopR = micLoopBuf[rd + 1];
  micLoopPosFrame++;
}

if (micRecOn && micRecFrames < micLoopMaxFrames) {
  size_t wr = micRecFrames * 2;
  micLoopBuf[wr + 0] = micOutL;   // record what you hear (post-shift/EQ)
  micLoopBuf[wr + 1] = micOutR;
  micRecFrames++;
}

// Mix mic + mic loop at the SAME fader (CH6 CC7)
const float micg = micGain.load(std::memory_order_relaxed);
L += (micOutL + micLoopL) * micg;
R += (micOutR + micLoopR) * micg;

// <-- ADD: sum SAMPLE buses into the synth+mic mix
L += shotOutL + fxOutL + kitL;
R += shotOutR + fxOutR + kitR;


// advance drum clock
gDrumSampleCounter++;




float outL = L * master;
float outR = R * master;

if (FORCE_MONO) {
  // collapse to mono (identical on L/R)
  float mono = 0.5f * (outL + outR);
  outL = outR = mono;
}

buffer[2*i + 0] = outL;
buffer[2*i + 1] = outR;

  }
}

// -------- Port-aware logging helpers --------
struct MidiPortCtx {
  unsigned index;
  std::string name;
};
static std::vector<std::unique_ptr<RtMidiIn>> gMidiIns;
static std::vector<std::unique_ptr<MidiPortCtx>> gMidiCtxs;
static steady_clock::time_point gT0 = steady_clock::now();

// Ignore one "startup zero" on CC7 for the first couple seconds
static inline bool ignoreStartupZeroCC7(long msSinceBoot, int ch, int cc, int val) {
  if (cc != 7) return false;
  if (val != 0) return false;
  // Only protect layers that frequently get muted at boot
  if (!(ch == 3 || ch == 5)) return false; // ch3=sample bus, ch5=kit bus
  return (msSinceBoot < 2000); // first 2 seconds after program start
}


static void printRaw(const MidiPortCtx* ctx, const std::vector<unsigned char>& m) {
  auto ms = duration_cast<milliseconds>(steady_clock::now() - gT0).count();
  std::cout << "[" << ms << " ms] [" << (ctx ? ctx->name : std::string("MIDI"))
            << "] raw:";
  for (auto b : m) std::cout << " 0x" << std::hex << (int)b << std::dec;
  std::cout << "\n";
}

void midiCallback(double, std::vector<unsigned char>* msg, void* userData) {
  if (!msg || msg->size() < 3) return;
  auto* ctx = static_cast<MidiPortCtx*>(userData);
  const unsigned char st = (*msg)[0], d1 = (*msg)[1], d2 = (*msg)[2];
  printRaw(ctx, *msg); // always print raw first

  const unsigned char type = st & 0xF0;
  const unsigned char ch0  = (st & 0x0F);     // 0..15
  const unsigned char ch   = ch0 + 1;         // 1..16

  // Pretty log
  if (type == 0xB0) {
    std::cout << "[CC]  port=" << (ctx ? ctx->name : std::string("?"))
              << " ch=" << (int)ch << " cc=" << (int)d1 << " val=" << (int)d2 << "\n";
  } else if (type == 0x90) {
    std::cout << "[NOTE ON] ch=" << (int)ch << " note=" << (int)d1 << " vel=" << (int)d2 << "\n";
  } else if (type == 0x80) {
    std::cout << "[NOTE OFF] ch=" << (int)ch << " note=" << (int)d1 << " vel=" << (int)d2 << "\n";
  }



  // ---- Loop modifier: CH7 NOTE 52 ----
  if ((type == 0x90 || type == 0x80) && ch == 7 && d1 == 52) {
    bool held = (type == 0x90 && d2 > 0);
    gLoopShiftHeld.store(held, std::memory_order_relaxed);
    std::cout << (held ? "[LOOP SHIFT] DOWN" : "[LOOP SHIFT] UP") << "\n";
  }



  // Also catch NoteOn ch7 note52 with vel=0 (running status devices)
  if (type == 0x90 && ch == 7 && d1 == 52 && d2 == 0) {
    gLoopShiftHeld.store(false, std::memory_order_relaxed);
    std::cout << "[LOOP SHIFT] UP\n";
  }

// ---- Clear loop layer: CH6 NOTE 52 (press) ----
if (type == 0x90 && ch == 6 && d1 == 52 && d2 > 0) {
  gClearLoops.store(true, std::memory_order_release);
  std::cout << "[LOOP] Clear looping voices (ch6 note52)\n";
}


// ---- DRUM: re-randomize pattern on CH4 NOTE 8 (press) ----
if (type == 0x90 && ch == 4 && d1 == 8 && d2 > 0) {
  gDrumRegenRequest.store(true, std::memory_order_release);
  std::cout << "[DRUM] Randomize pattern (ch4 note8)\n";
}


  // ---- Retune synth (NoteOn ch=1 vel=127) using both maps ----
  if (type == 0x90 && ch == 1 && d2 == 127) {
    if (auto it = mapA_noteToSemis.find((int)d1); it != mapA_noteToSemis.end()) {
      int semis = it->second;
      double f = baseFreqC2 * std::pow(2.0, semis / 12.0);
      freqA.store(f);
      std::cout << "A: NoteOn n=" << (int)d1 << " → " << f << " Hz\n";
    }
    if (auto it = mapB_noteToSemis.find((int)d1); it != mapB_noteToSemis.end()) {
      int semis = it->second;
      double f = baseFreqC4 * std::pow(2.0, semis / 12.0);
      freqB.store(f);
      std::cout << "B: NoteOn n=" << (int)d1 << " → " << f << " Hz\n";
    }
  }

// === MIC LOOPER MIDI ===
// Record button: ch=1, note=93  (0x90 0x5D 0x7F shown in your log)
//  - NOTE ON  => begin recording mic (clears previous take)
//  - NOTE OFF (or NoteOn vel=0) => stop rec AND start looping the take
if (ch == 1 && d1 == 93) {
  if (type == 0x90 && d2 > 0) {            // NOTE ON
    micRecStartReq.store(true, std::memory_order_release);
    std::cout << "[MIC LOOPER] REC START (ch1 n93)\n";
  }
  if ((type == 0x80) || (type == 0x90 && d2 == 0)) { // NOTE OFF
    micRecStopReq.store(true, std::memory_order_release);
    std::cout << "[MIC LOOPER] REC STOP → LOOP (ch1 n93)\n";
  }
}

// Stop *that* loop only: ch=1, note=15 (your 0x80 0x0F 0x00 example)
if (ch == 1 && d1 == 15 && ((type == 0x80) || (type == 0x90 && d2 == 0))) {
  micLoopStopReq.store(true, std::memory_order_release);
  std::cout << "[MIC LOOPER] LOOP STOP (ch1 n15)\n";
}

// Tie loop+mic volume to CH6 CC7 (same knob you already use for the mic)
if (type == 0xB0 && ch == 6 && d1 == 7) {
  float g = (float)d2 / 127.0f;
  micGain.store(g, std::memory_order_release);
  std::cout << "[MIC/LOOPER] Vol CC7 (ch6) = " << (int)d2 << " gain=" << g << "\n";
}

  // ==== CH3 NOTE 50 ====
  // press = start looping the selected/last sample
  // release = stop all loops
// ==== CH3 NOTE 50: toggle the SENTENCE loop ====
if (ch == 3 && d1 == 50 && type == 0x90 && d2 > 0) {
  bool newState = !gSentenceLoopOn.load(std::memory_order_relaxed);
  gSentenceLoopOn.store(newState, std::memory_order_release);
  if (newState) {
    std::cout << "[SENTENCE] LOOP ON\n";
  } else {
    std::cout << "[SENTENCE] LOOP OFF\n";
  }
}


  // ---- DRUM: re-randomize 16-step pattern on CH1 NOTE 16 (NoteOff OR NoteOn with vel=0) ----
  if ((type == 0x80 && ch == 1 && d1 == 8) || (type == 0x90 && ch == 1 && d1 == 8 && d2 == 0)) {
    gDrumRegenRequest.store(true, std::memory_order_release);
    std::cout << "[DRUM] Randomize pattern (NOTE 16)\n";
  }

  // ---- Sample pad triggers: trigger on NoteOn with ANY velocity > 0 ----
  if (type == 0x90 && d2 > 0) {
    int key = keyCN(ch, d1);
    auto it = sampleKeyToId.find(key);
    if (it != sampleKeyToId.end()) {
      int sid = it->second;
      bool makeLoop = gLoopShiftHeld.load(std::memory_order_relaxed);
      pushTrigger(sid, makeLoop);
      gSelectedSample.store(sid, std::memory_order_relaxed);
      gLastSampleByCh[ch0] = sid;
      gLastAnySample.store(sid, std::memory_order_relaxed);
      std::cout << (makeLoop ? "[SELECT+LOOP] " : "[SELECT] ")
                << "target=" << sid << " (" << gSampleNames[sid] << ")\n";
    }
  }

// Delay spacing (CH1 CC23) — controls delay time from 1/16 → 1 bar
if (type == 0xB0 && ch == 8 && d1 == 23) {
  float m = (float)d2 / 127.0f;
  delayIntensity.store(m, std::memory_order_release);
  std::cout << "[FX] Delay spacing CC23=" << (int)d2
            << " -> " << m << " (1/16 ↔ 1 bar)\n";
}

  // ---- Volumes ----
  if (type == 0xB0 && ch == 1 && d1 == 7) {
    float g = (float)d2 / 127.0f; gainA.store(g * 0.5f);
    std::cout << "A: CC7=" << (int)d2 << " gain=" << (g * 0.5f) << "\n";
  }
  if (type == 0xB0 && ch == 2 && d1 == 7) {
    float g = (float)d2 / 127.0f; gainB.store(g * 0.5f);
    std::cout << "B: CC7=" << (int)d2 << " gain=" << (g * 0.5f) << "\n";
  }// measure ms since boot for the guard
auto msSinceBoot = (long)std::chrono::duration_cast<std::chrono::milliseconds>(
                     std::chrono::steady_clock::now() - gT0).count();

// Samples layer volume: CH3 CC7
if (type == 0xB0 && ch == 3 && d1 == 7) {
  if (ignoreStartupZeroCC7(msSinceBoot, (int)ch, (int)d1, (int)d2)) {
    std::cout << "[BOOT-GUARD] Ignoring startup zero on CH3 CC7\n";
  } else {
    float g = (float)d2 / 127.0f;
    sampleLayerGain.store(g);
    std::cout << "[SAMPLES] Vol CC7 (ch3) = " << (int)d2 << " gain=" << g << "\n";
  }
}

// KIT layer volume: CH5 CC7 (direct-to-master)
if (type == 0xB0 && ch == 5 && d1 == 7) {
  if (ignoreStartupZeroCC7(msSinceBoot, (int)ch, (int)d1, (int)d2)) {
    std::cout << "[BOOT-GUARD] Ignoring startup zero on CH5 CC7\n";
  } else {
    float g = (float)d2 / 127.0f;
    kitLayerGain.store(g);
    std::cout << "[KIT] Vol CC7 (ch5) = " << (int)d2 << " gain=" << g << "\n";
  }
}



  // LOOP layer volume: CH7 CC7
  if (type == 0xB0 && ch == 7 && d1 == 7) {
    float g = (float)d2 / 127.0f;
    loopLayerGain.store(g);
    std::cout << "Loop layer: CC7=" << (int)d2 << " layerGain=" << g << "\n";
  }

  // DRUM layer volume: CH4 CC7
  if (type == 0xB0 && ch == 4 && d1 == 7) {
    float g = (float)d2 / 127.0f;
    drumLayerGain.store(g);
    std::cout << "[DRUM] Vol CC7 (ch4) = " << (int)d2 << " gain=" << g << "\n";
  }

  // Master volume (all layers): CH1 CC14
  if (type == 0xB0 && ch == 1 && d1 == 14) {
    float g = (float)d2 / 127.0f;
    masterGain.store(g);
    std::cout << "[MASTER] CC14=" << (int)d2 << " gain=" << g << "\n";
  }

  // DRUM BPM: CH1 CC20 -> 50..180 BPM
  if (type == 0xB0 && ch == 8 && d1 == 20) {
    float t = (float)d2 / 127.0f;
    float bpm = 30.0f + t * (180.0f - 30.0f);
    drumBPM.store(bpm);
    std::cout << "[DRUM] BPM set to " << bpm << " (CC20=" << (int)d2 << ")\n";
  }




  // ==== DJ FILTER control (CC50 — any channel) ====
  if (type == 0xB0 && d1 == 50) {
    djFilterParam.store((float)d2 / 127.0f);
    std::cout << "[FILTER] CC50=" << (int)d2 << " -> " << djFilterParam.load()
              << " (LPF←•→HPF)\n";
  }

  // LOOP layer DJ filter: CH1 CC54
  if (type == 0xB0 && ch == 1 && d1 == 54) {
    loopFilterParam.store((float)d2 / 127.0f);
    std::cout << "[LOOP FILTER] CC54=" << (int)d2 << " -> " << loopFilterParam.load()
              << " (LPF←•→HPF)\n";
  }

  // DRUM layer DJ filter: CH1 CC51
  if (type == 0xB0 && ch == 1 && d1 == 51) {
    drumFilterParam.store((float)d2 / 127.0f);
    std::cout << "[DRUM FILTER] CC51=" << (int)d2 << " -> " << drumFilterParam.load()
              << " (LPF←•→HPF)\n";
  }

  // Binaural offsets (absolute 0..40 Hz)
  if (type == 0xB0 && ch == 8 && d1 == 16) {
    float hz = (float)d2 * (40.0f / 127.0f);
    binauralOffsetA_Hz.store(hz);
    std::cout << "C(binaural A) offset=" << hz << " Hz\n";
  }
  if (type == 0xB0 && ch == 8 && d1 == 17) {
    float hz = (float)d2 * (40.0f / 127.0f);
    binauralOffsetB_Hz.store(hz);
    std::cout << "D(binaural B) offset=" << hz << " Hz\n";
  }

  // ---- Which sample to edit with CC48/49?
  auto getEditableSid = [&](int ch0Idx)->int {
    int sid = gSelectedSample.load(std::memory_order_relaxed);
    if (sid >= 0 && sid < (int)gSamples.size()) return sid;
    int byCh = gLastSampleByCh[ch0Idx];
    if (byCh >= 0 && byCh < (int)gSamples.size()) return byCh;
    int any = gLastAnySample.load(std::memory_order_relaxed);
    if (any >= 0 && any < (int)gSamples.size()) return any;
    return -1;
  };

  // ==== Trim controls on selected sample (CC48/49 — any channel) ====
  if (type == 0xB0 && (d1 == 48 || d1 == 49)) {
    int sid = getEditableSid(ch0);
    if (sid >= 0) {
      const uint64_t total = gSamples[sid].frames;
      if (total > 0) {
        if (d1 == 48) { // IN
          double norm = (double)d2 / 127.0; if (norm > 0.999999) norm = 1.0;
          uint64_t in  = (uint64_t)std::llround(norm * (double)(total - 1));
          uint64_t len = gSampleTrim[sid].len.load();
          if (len == 0 || len > total) len = total;
          if (in + len > total) len = total - in;
          gSampleTrim[sid].in.store(in);
          gSampleTrim[sid].len.store(len);
          std::cout << "[TRIM] " << gSampleNames[sid] << "  IN=" << in
                    << " (" << (100.0 * (double)in / (double)total) << "%)\n";
        } else {        // LEN
          double norm = (double)d2 / 127.0;
          uint64_t in  = gSampleTrim[sid].in.load();
          uint64_t len = (uint64_t)std::llround(norm * (double)total);
          if (len < 1) len = 1;
          if (in >= total) in = 0;
          if (in + len > total) len = total - in;
          gSampleTrim[sid].in.store(in);
          gSampleTrim[sid].len.store(len);
          std::cout << "[TRIM] " << gSampleNames[sid] << "  LEN=" << len
                    << " (" << (100.0 * (double)len / (double)total) << "%)\n";
        }
      }
    } else {
      std::cout << "[TRIM] CC" << (int)d1
                << " moved but no sample has been triggered yet. Fire any pad once.\n";
    }
  }

  // Reset trims: press (select) a sample, then CH8 note 52 -> reset in/len
  if (type == 0x90 && ch == 8 && d1 == 52 && d2 > 0) {
    int sid = gSelectedSample.load(std::memory_order_relaxed);
    if (sid >= 0 && sid < (int)gSamples.size()) {
      gSampleTrim[sid].in.store(0);
      gSampleTrim[sid].len.store(gSamples[sid].frames);
      std::cout << "Reset trims for [" << gSampleNames[sid] << "]\n";
    } else {
      std::cout << "Reset pressed but no sample is selected yet.\n";
    }
  }

// Reverb mix (CH1 CC21) — 0..1
if (type == 0xB0 && ch == 8 && d1 == 21) {
  float m = (float)d2 / 127.0f;
  reverbMix.store(m, std::memory_order_release);
  std::cout << "[FX] Reverb mix CC21=" << (int)d2 << " -> " << m << " (dry↔wet)\n";
}

// Delay mix (CH1 CC22) — 0..1
if (type == 0xB0 && ch == 8 && d1 == 22) {
  float m = (float)d2 / 127.0f;
  delayMix.store(m, std::memory_order_release);
  std::cout << "[FX] Delay mix CC22=" << (int)d2 << " -> " << m << " (dry↔wet)\n";
}


  // Global reset of ALL sample trims: CH1 NOTE 81 (press)
  if (type == 0x90 && ch == 1 && d1 == 81 && d2 > 0) {
    for (size_t i = 0; i < gSamples.size(); ++i) {
      gSampleTrim[i].in.store(0);
      gSampleTrim[i].len.store(gSamples[i].frames);
    }
    std::cout << "[GLOBAL] Reset ALL sample IN/LEN (CH1 NOTE 81)\n";
  }
}

// --------- Open ALL MIDI input ports and keep them alive ----------
static bool openAllMidiInputs() {
  try {
    RtMidiIn probe;
    unsigned n = probe.getPortCount();
    if (n == 0) {
      std::cerr << "No MIDI input ports.\n";
      return false;
    }
    std::cout << "MIDI inputs:\n";
    for (unsigned i = 0; i < n; ++i) {
      std::cout << "  [" << i << "] " << probe.getPortName(i) << "\n";
    }
    for (unsigned i = 0; i < n; ++i) {
      auto in = std::make_unique<RtMidiIn>();
      in->ignoreTypes(false, false, false);      // don't ignore anything
      in->openPort(i);
      auto ctx = std::make_unique<MidiPortCtx>();
      ctx->index = i;
      ctx->name  = in->getPortName(i);
      std::cout << "Opened MIDI port " << i << ": " << ctx->name << "\n";
      in->setCallback(&midiCallback, ctx.get()); // pass port context
      gMidiCtxs.push_back(std::move(ctx));       // keep ctx alive
      gMidiIns.push_back(std::move(in));         // keep instance alive
    }
    return true;
  } catch (const RtMidiError& e) {
    std::cerr << "RtMidi error while opening ports: " << e.getMessage() << "\n";
    return false;
  }
}

// -------------------- Main --------------------
int main() {
  // init last-by-channel to -1
  gLastSampleByCh.fill(-1);

// audio init
ma_device_config cfg = ma_device_config_init(ma_device_type_duplex);
cfg.playback.format   = ma_format_f32;
cfg.playback.channels = 2;
cfg.capture.format    = ma_format_f32;
cfg.capture.channels  = 2;
cfg.sampleRate        = 48000;
cfg.dataCallback      = dataCallback;

if (ma_device_init(NULL, &cfg, &device) != MA_SUCCESS) {
  std::cerr << "Failed to init audio\n"; return 1;
}


  // load samples (convert to device format @ cfg.sampleRate)
  const std::string base = "/Users/jianwei/Downloads/breathe-v1-main/spoken/";
const std::string baseDrumKit = "/Users/jianwei/Downloads/breathe-v1-main/drum/";
auto addSample = [&](const std::string& filename, int ch, int note, bool isKit = false) {
  const std::string& dir = isKit ? baseDrumKit : base;    // choose folder by isKit

  Sample s;
  if (loadSampleFile(dir + filename, cfg.sampleRate, s)) {
    int id = (int)gSamples.size();
    gSamples.push_back(std::move(s));
    sampleKeyToId[keyCN(ch, note)] = id;

    SampleTrim st;
    st.in.store(0);
    st.len.store(gSamples[id].frames);
    gSampleTrim.push_back(std::move(st));
    gSampleNames.push_back(filename);

    // mark whether this sample is part of the KIT
    gIsKit.push_back(isKit ? 1u : 0u);

    std::cout << "Mapped " << filename << " to ch=" << ch
              << " note=" << note << " (id " << id
              << ", kit=" << (isKit ? "yes" : "no") << ")\n";
  }
};


  // your mappings
  addSample("breathe in.wav",  1, 52);
  addSample("breathe out.wav", 2, 52);
  addSample("breath.wav",      3, 52);

  addSample("where.wav", 1, 32);
  addSample("fair.wav",  1, 33);
  addSample("share.wav", 1, 34);
  addSample("when.wav",  1, 35);
  addSample("we.wav",    1, 36);
  addSample("send.wav",  1, 37);
  addSample("death.wav", 1, 38);


addSample("1.wav", 1, 82, true); // CH1 note 82
addSample("2.wav", 1, 83, true); // CH1 note 83
addSample("3.wav", 1, 84, true); // CH1 note 84
addSample("4.wav", 1, 85, true); // CH1 note 85
addSample("5.wav", 1, 86, true); // CH1 note 86


// Map the 7 words to sample IDs by filename
auto findByName = [&](const std::string& name)->int {
  for (int i = 0; i < (int)gSampleNames.size(); ++i)
    if (gSampleNames[i] == name) return i;
  return -1;
};
gSentenceIds[0] = findByName("where.wav");
gSentenceIds[1] = findByName("fair.wav");
gSentenceIds[2] = findByName("share.wav");
gSentenceIds[3] = findByName("when.wav");
gSentenceIds[4] = findByName("we.wav");
gSentenceIds[5] = findByName("send.wav");
gSentenceIds[6] = findByName("death.wav");
for (int i = 0; i < 7; ++i) {
  if (gSentenceIds[i] < 0)
    std::cout << "[SENTENCE] Missing sample id for index " << i << "\n";
  else
    std::cout << "[SENTENCE] word " << i << " -> id " << gSentenceIds[i]
              << " (" << gSampleNames[gSentenceIds[i]] << ")\n";
}


  if (gSamples.empty()) {
    std::cerr << "No samples loaded—check file paths.\n";
  }

  // start audio
  if (ma_device_start(&device) != MA_SUCCESS) {
    std::cerr << "Failed to start audio\n"; return 1;
  }

  // open ALL midi inputs (port-aware, with contexts)
  if (!openAllMidiInputs()) return 1;

  std::cout << "Triangles + binaural + sample layer + DJ filter + per-sample trim + LOOP SHIFT ready.\n"
               "Hold CH7 NOTE 52, tap a sample pad → that sample loops; edit IN (CC48) / LEN (CC49) live.\n"
               "CH3 CC7 = sample vol | CC50 = DJ filter | Reset trims: select sample then CH8 NOTE 52.\n";

  // park
  while (true) std::this_thread::sleep_for(std::chrono::seconds(1));
}
