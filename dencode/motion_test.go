package main

import (
	"math"
	"math/rand"
	"testing"
)

func smoothPlane(w, h int) []float64 {
	p := make([]float64, w*h)
	for y := 0; y < h; y++ {
		for x := 0; x < w; x++ {
			fx, fy := float64(x), float64(y)
			v := 128 + 60*math.Sin(fx*0.20) + 50*math.Cos(fy*0.16) + 20*math.Sin((fx+fy)*0.08)
			if v < 0 {
				v = 0
			} else if v > 255 {
				v = 255
			}
			p[y*w+x] = v
		}
	}
	return p
}

func floatSADRef(cur, ref []float64, frameW, curX, curY, srcX, srcY, blockW, blockH int) int {
	sad := 0
	for y := 0; y < blockH; y++ {
		for x := 0; x < blockW; x++ {
			c := int(cur[(curY+y)*frameW+(curX+x)] + 0.5)
			r := int(ref[(srcY+y)*frameW+(srcX+x)] + 0.5)
			d := c - r
			if d < 0 {
				d = -d
			}
			sad += d
		}
	}
	return sad
}

func randPlane(rng *rand.Rand, n int) []float64 {
	p := make([]float64, n)
	for i := range p {
		p[i] = float64(rng.Intn(256)) + rng.Float64()*0.9 - 0.45
		if p[i] < 0 {
			p[i] = 0
		}
	}
	return p
}

func TestI16SADMatchesFloat(t *testing.T) {
	rng := rand.New(rand.NewSource(1))
	const W, H = 48, 40
	cur := randPlane(rng, W*H)
	ref := randPlane(rng, W*H)
	curI := planeToMatchI16(cur)
	refI := planeToMatchI16(ref)

	for trial := 0; trial < 2000; trial++ {
		bw := 4 + rng.Intn(13)
		bh := 4 + rng.Intn(13)
		cx := rng.Intn(W - bw + 1)
		cy := rng.Intn(H - bh + 1)
		sx := rng.Intn(W - bw + 1)
		sy := rng.Intn(H - bh + 1)
		want := floatSADRef(cur, ref, W, cx, cy, sx, sy, bw, bh)
		got, ok := blockMatchScoreI16(curI, refI, W, H, cx, cy, sx, sy, bw, bh, 1<<20)
		if !ok {
			t.Fatalf("trial %d: unexpected out-of-bounds", trial)
		}
		if got != want {
			t.Fatalf("trial %d: i16 SAD=%d, float SAD=%d", trial, got, want)
		}
	}
}

// shiftPlane builds ref such that ref[Y][X] = base[Y-dy][X-dx], i.e. content
func shiftPlane(base []float64, w, h, dx, dy int) []float64 {
	ref := make([]float64, w*h)
	for Y := 0; Y < h; Y++ {
		for X := 0; X < w; X++ {
			sx := X - dx
			sy := Y - dy
			if sx < 0 || sy < 0 || sx >= w || sy >= h {
				ref[Y*w+X] = 0
				continue
			}
			ref[Y*w+X] = base[sy*w+sx]
		}
	}
	return ref
}

func TestDiamondFindsTranslation(t *testing.T) {
	const W, H = 64, 64
	base := smoothPlane(W, H)
	curI := planeToMatchI16(base)

	shifts := [][2]int{{3, 2}, {-4, 1}, {0, -5}, {6, -3}}
	for _, s := range shifts {
		dx, dy := s[0], s[1]
		refI := planeToMatchI16(shiftPlane(base, W, H, dx, dy))
		bx, by, bw, bh := 24, 24, 16, 16
		gotDx, gotDy, sad, ok := diamondMotionI16(curI, refI, W, H, bx, by, bw, bh, 12, 16)
		if !ok {
			t.Fatalf("shift %v: no MV found", s)
		}
		if gotDx != dx || gotDy != dy || sad != 0 {
			t.Fatalf("shift %v: got (%d,%d) sad=%d, want (%d,%d) sad=0", s, gotDx, gotDy, sad, dx, dy)
		}
	}
}

func TestComputeVLIX2BlockMVsGlobalShift(t *testing.T) {
	const W, H = 64, 48
	const blockDim = 16
	base := smoothPlane(W, H)
	dx, dy := 4, -3
	prev := shiftPlane(base, W, H, dx, dy)

	mvs := computeVLIX2BlockMVs(vlxFrameDelta, base, prev, nil, W, H, blockDim, 8, 16, true)
	bwBlocks := (W + blockDim - 1) / blockDim
	bhBlocks := (H + blockDim - 1) / blockDim
	checked := 0
	for by := 0; by < bhBlocks; by++ {
		for bx := 0; bx < bwBlocks; bx++ {
			ox, oy := bx*blockDim, by*blockDim
			if ox+dx < 0 || oy+dy < 0 || ox+blockDim+dx > W || oy+blockDim+dy > H {
				continue
			}
			mv := mvs[by*bwBlocks+bx]
			if mv.mode != 1 || mv.dx1 != dx || mv.dy1 != dy {
				t.Fatalf("block (%d,%d): mode=%d mv=(%d,%d), want mode=1 mv=(%d,%d)", bx, by, mv.mode, mv.dx1, mv.dy1, dx, dy)
			}
			checked++
		}
	}
	if checked == 0 {
		t.Fatal("no interior blocks were validated")
	}
}
