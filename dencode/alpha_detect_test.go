package main

import (
	"image"
	"image/color"
	"path/filepath"
	"testing"
)

func writeFrame(t *testing.T, path string, a uint8) {
	t.Helper()
	img := image.NewNRGBA(image.Rect(0, 0, 8, 8))
	for y := 0; y < 8; y++ {
		for x := 0; x < 8; x++ {
			img.SetNRGBA(x, y, color.NRGBA{R: uint8(x * 8), G: uint8(y * 8), B: 64, A: a})
		}
	}
	writeTestPNG(t, path, img)
}

func TestDetectFramesAlpha(t *testing.T) {
	dir := t.TempDir()
	st := losslessSettings(t)

	// All-opaque frames -> ALPHA=0.
	var opaque []string
	for i := 0; i < 3; i++ {
		p := filepath.Join(dir, "op"+string(rune('0'+i))+".png")
		writeFrame(t, p, 255)
		opaque = append(opaque, p)
	}
	has, err := detectFramesAlpha(opaque, st, "")
	if err != nil {
		t.Fatalf("detectFramesAlpha(opaque): %v", err)
	}
	if has {
		t.Fatal("opaque frames reported as having alpha")
	}

	mixed := append([]string{}, opaque...)
	transp := filepath.Join(dir, "tr.png")
	writeFrame(t, transp, 128)
	mixed = append(mixed, transp)
	has, err = detectFramesAlpha(mixed, st, "")
	if err != nil {
		t.Fatalf("detectFramesAlpha(mixed): %v", err)
	}
	if !has {
		t.Fatal("frame with alpha not detected")
	}
}
