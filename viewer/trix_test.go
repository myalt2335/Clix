package main

import (
	"image"
	"os"
	"path/filepath"
	"testing"
)

func TestTrixGoldenDecode(t *testing.T) {
	dir := filepath.Join("testdata")
	ref, err := os.ReadFile(filepath.Join(dir, "trix_blocks_ref.rgba"))
	if err != nil {
		t.Skipf("golden not present: %v", err)
	}
	img, _, _, err := decodeTrixToImage(filepath.Join(dir, "trix_blocks.trix"))
	if err != nil {
		t.Fatalf("decodeTrixToImage: %v", err)
	}
	rgba, ok := img.(*image.RGBA)
	if !ok {
		t.Fatalf("expected *image.RGBA, got %T", img)
	}
	b := rgba.Bounds()
	if got := b.Dx() * b.Dy() * 4; got != len(ref) {
		t.Fatalf("decoded plane size %d != reference %d", got, len(ref))
	}
	w := b.Dx()
	for y := 0; y < b.Dy(); y++ {
		ro := rgba.PixOffset(b.Min.X, b.Min.Y+y)
		refRow := y * w * 4
		for i := 0; i < w*4; i++ {
			if rgba.Pix[ro+i] != ref[refRow+i] {
				t.Fatalf("row %d byte %d differs: %d != %d", y, i, rgba.Pix[ro+i], ref[refRow+i])
			}
		}
	}
}
