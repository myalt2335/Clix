package main

import (
	"os"
	"path/filepath"
	"testing"
)

func TestALIX2GoldenDecode(t *testing.T) {
	dir := filepath.Join("testdata")
	blob, err := os.ReadFile(filepath.Join(dir, "alix2_stereo.alix"))
	if err != nil {
		t.Skipf("golden not present: %v", err)
	}
	ref, err := os.ReadFile(filepath.Join(dir, "alix2_stereo_ref.pcm"))
	if err != nil {
		t.Fatalf("reading reference pcm: %v", err)
	}
	pcm, sampleRate, channels, err := decodeALIXBinary(blob)
	if err != nil {
		t.Fatalf("decodeALIXBinary: %v", err)
	}
	if sampleRate != 44100 {
		t.Fatalf("sample rate: got %d want 44100", sampleRate)
	}
	if channels != 2 {
		t.Fatalf("channels: got %d want 2", channels)
	}
	if len(pcm) != len(ref) {
		t.Fatalf("pcm length: got %d want %d", len(pcm), len(ref))
	}
	for i := range ref {
		if pcm[i] != ref[i] {
			t.Fatalf("pcm byte %d differs: got %d want %d", i, pcm[i], ref[i])
		}
	}
}
