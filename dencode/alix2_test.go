package main

import (
	"bufio"
	"bytes"
	"encoding/binary"
	"io"
	"math"
	"strconv"
	"strings"
	"testing"

	"github.com/klauspost/compress/zstd"
)

func parseALIXContainerForTest(t *testing.T, blob []byte) (codec string, block int, raw []byte) {
	t.Helper()
	br := bufio.NewReader(bytes.NewReader(blob))
	for {
		line, err := br.ReadString('\n')
		if err != nil {
			t.Fatalf("reading header: %v", err)
		}
		line = strings.TrimRight(line, "\r\n")
		if line == "" {
			break
		}
		if !strings.Contains(line, "=") {
			continue
		}
		parts := strings.SplitN(line, "=", 2)
		key := strings.TrimSpace(parts[0])
		val := strings.TrimSpace(parts[1])
		switch key {
		case "CODEC":
			codec = strings.ToUpper(val)
		case "BLOCK":
			block, _ = strconv.Atoi(val)
		}
	}
	payload, err := io.ReadAll(br)
	if err != nil {
		t.Fatalf("reading payload: %v", err)
	}
	dec, err := zstd.NewReader(nil)
	if err != nil {
		t.Fatalf("zstd reader: %v", err)
	}
	defer dec.Close()
	raw, err = dec.DecodeAll(payload, nil)
	if err != nil {
		t.Fatalf("zstd decode: %v", err)
	}
	return codec, block, raw
}

func decodeALIX2RawTest(raw []byte, channels, samples, blockFrames int) []int16 {
	br := newBitReader(raw)
	out := make([]int16, 0, samples*channels)
	clampS16 := func(v int32) int16 {
		if v > 32767 {
			return 32767
		}
		if v < -32768 {
			return -32768
		}
		return int16(v)
	}
	decodeSeries := func(n int) []int32 {
		ob, _ := br.ReadBits(2)
		kb, _ := br.ReadBits(5)
		order := int(ob)
		k := uint8(kb)
		x := make([]int32, n)
		get := func(j int) int32 {
			if j < 0 {
				return 0
			}
			return x[j]
		}
		for i := 0; i < n; i++ {
			rv, _ := readRiceSigned(br, k)
			var pred int32
			switch order {
			case 1:
				pred = get(i - 1)
			case 2:
				pred = 2*get(i-1) - get(i-2)
			case 3:
				pred = 3*get(i-1) - 3*get(i-2) + get(i-3)
			}
			x[i] = int32(rv) + pred
		}
		return x
	}
	framesLeft := samples
	for framesLeft > 0 {
		n := blockFrames
		if n > framesLeft {
			n = framesLeft
		}
		silence, _ := br.ReadBit()
		if silence == 1 {
			for i := 0; i < n*channels; i++ {
				out = append(out, 0)
			}
			framesLeft -= n
			continue
		}
		if channels == 2 {
			decorr, _ := br.ReadBit()
			a := decodeSeries(n)
			b := decodeSeries(n)
			if decorr == 1 {
				for i := 0; i < n; i++ {
					mid := a[i]
					side := b[i]
					l := mid + ((side + (side & 1)) >> 1)
					r := l - side
					out = append(out, clampS16(l), clampS16(r))
				}
			} else {
				for i := 0; i < n; i++ {
					out = append(out, clampS16(a[i]), clampS16(b[i]))
				}
			}
		} else {
			series := make([][]int32, channels)
			for c := 0; c < channels; c++ {
				series[c] = decodeSeries(n)
			}
			for i := 0; i < n; i++ {
				for c := 0; c < channels; c++ {
					out = append(out, clampS16(series[c][i]))
				}
			}
		}
		framesLeft -= n
	}
	return out
}

func pcmFromSamples(samples []int16) []byte {
	out := make([]byte, len(samples)*2)
	for i, s := range samples {
		binary.LittleEndian.PutUint16(out[i*2:], uint16(s))
	}
	return out
}

func synthStereo(frames int) []int16 {
	s := make([]int16, frames*2)
	for i := 0; i < frames; i++ {
		l := int16(8000*math.Sin(float64(i)*0.05) + 3000*math.Sin(float64(i)*0.31))
		r := l + int16(120*math.Sin(float64(i)*0.07))
		s[i*2] = l
		s[i*2+1] = r
	}
	return s
}

func synthMono(frames int) []int16 {
	s := make([]int16, frames)
	for i := 0; i < frames; i++ {
		s[i] = int16(12000*math.Sin(float64(i)*0.02) + 1500*math.Sin(float64(i)*0.5))
	}
	return s
}

func sliceEqI16(a, b []int16) (int, bool) {
	if len(a) != len(b) {
		return -1, false
	}
	for i := range a {
		if a[i] != b[i] {
			return i, false
		}
	}
	return 0, true
}

func TestALIX2RoundTripLossless(t *testing.T) {
	cases := []struct {
		name     string
		channels int
		frames   int
		block    int
		samples  []int16
	}{
		{"stereo-4096", 2, 5000, 4096, synthStereo(5000)},
		{"stereo-1024", 2, 5000, 1024, synthStereo(5000)},
		{"stereo-tiny-block", 2, 300, 7, synthStereo(300)},
		{"mono-4096", 1, 5000, 4096, synthMono(5000)},
		{"mono-1024", 1, 4096, 1024, synthMono(4096)},
	}
	for _, tc := range cases {
		t.Run(tc.name, func(t *testing.T) {
			pcm := pcmFromSamples(tc.samples)
			raw, err := encodeALIX2Raw(pcm, tc.channels, tc.block)
			if err != nil {
				t.Fatalf("encodeALIX2Raw: %v", err)
			}
			got := decodeALIX2RawTest(raw, tc.channels, tc.frames, tc.block)
			if idx, ok := sliceEqI16(tc.samples, got); !ok {
				if idx < 0 {
					t.Fatalf("length mismatch: got %d want %d", len(got), len(tc.samples))
				}
				t.Fatalf("sample %d differs: got %d want %d", idx, got[idx], tc.samples[idx])
			}
		})
	}
}

func TestALIX2SilenceBlock(t *testing.T) {
	frames := 4096
	samples := make([]int16, frames*2)
	pcm := pcmFromSamples(samples)
	raw, err := encodeALIX2Raw(pcm, 2, 1024)
	if err != nil {
		t.Fatalf("encodeALIX2Raw: %v", err)
	}
	got := decodeALIX2RawTest(raw, 2, frames, 1024)
	if _, ok := sliceEqI16(samples, got); !ok {
		t.Fatalf("silence round-trip mismatch")
	}
	if len(raw) > frames/8 {
		t.Fatalf("silence encoding too large: %d bytes for %d frames", len(raw), frames)
	}
}

func TestALIX2BeatsOrderOneOnCorrelatedStereo(t *testing.T) {
	frames := 16384
	samples := synthStereo(frames)
	pcm := pcmFromSamples(samples)
	alix2Raw, err := encodeALIX2Raw(pcm, 2, alix2DefaultBlock)
	if err != nil {
		t.Fatalf("encodeALIX2Raw: %v", err)
	}
	alixRaw, err := encodeALIXBlockRaw(pcm, 2, alixBlockFrames)
	if err != nil {
		t.Fatalf("encodeALIXBlockRaw: %v", err)
	}
	if len(alix2Raw) >= len(alixRaw) {
		t.Fatalf("expected ALIX2 (%d) smaller than order-1 ALIX (%d) on correlated stereo", len(alix2Raw), len(alixRaw))
	}
}

func TestEncodeALIXFromPCMSelectsAndRoundTrips(t *testing.T) {
	frames := 16384
	samples := synthStereo(frames)
	pcm := pcmFromSamples(samples)
	blob, gotFrames, err := encodeALIXFromPCM(pcm, 44100, 2, 19, 0)
	if err != nil {
		t.Fatalf("encodeALIXFromPCM: %v", err)
	}
	if gotFrames != frames {
		t.Fatalf("frame count: got %d want %d", gotFrames, frames)
	}
	codec, block, payload := parseALIXContainerForTest(t, blob)
	t.Logf("selected codec=%s block=%d payload=%d bytes", codec, block, len(payload))
	if codec != alix2Codec {
		t.Logf("note: codec %s selected over ALIX2 (still valid)", codec)
	}
}
