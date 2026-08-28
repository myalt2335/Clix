package main

import "testing"

func TestDecodeALIXToPCMRoundTrip(t *testing.T) {
	cases := []struct {
		name     string
		channels int
		samples  []int16
	}{
		{"stereo", 2, synthStereo(5000)},
		{"mono", 1, synthMono(4096)},
	}
	for _, tc := range cases {
		t.Run(tc.name, func(t *testing.T) {
			pcm := pcmFromSamples(tc.samples)
			blob, _, err := encodeALIXFromPCM(pcm, 44100, tc.channels, 19, 0)
			if err != nil {
				t.Fatalf("encodeALIXFromPCM: %v", err)
			}
			for _, variant := range []struct {
				name string
				data []byte
			}{
				{"binary", blob},
				{"text", encodeALIXTextFromBinary(blob)},
			} {
				t.Run(variant.name, func(t *testing.T) {
					got, sr, ch, err := decodeALIXToPCM(variant.data)
					if err != nil {
						t.Fatalf("decodeALIXToPCM: %v", err)
					}
					if sr != 44100 || ch != tc.channels {
						t.Fatalf("header sr=%d ch=%d, want 44100/%d", sr, ch, tc.channels)
					}
					if len(got) != len(pcm) {
						t.Fatalf("pcm length %d != %d", len(got), len(pcm))
					}
					for i := range pcm {
						if got[i] != pcm[i] {
							t.Fatalf("pcm byte %d: %d != %d", i, got[i], pcm[i])
						}
					}
				})
			}
		})
	}
}
