//go:build cuda && cgo

package main

/*
#include "vlx_accel.h"
*/
import "C"

import (
	"fmt"
	"os"
	"strconv"
	"sync"
	"unsafe"
)

type cudaComputeBackend struct {
	mu             sync.Mutex
	warnDCTOnce    sync.Once
	warnIDCTOnce   sync.Once
	warnMotionOnce sync.Once
	chunkBlocks    int
}

func (b *cudaComputeBackend) Name() string { return "cuda" }

func vlxF64ToF32(dst []float32, src []float64) {
	for i := range src {
		dst[i] = float32(src[i])
	}
}

func vlxF32ToF64(dst []float64, src []float32) {
	for i := range src {
		dst[i] = float64(src[i])
	}
}

func (b *cudaComputeBackend) DCT8x8EncodeMany(blocksIn []float64, coeffOut []float64) {
	if len(blocksIn) == 0 {
		return
	}
	blocks := len(blocksIn) / 64
	if blocks == 0 {
		return
	}
	chunkBlocks := b.chunkBlocks
	if chunkBlocks <= 0 {
		chunkBlocks = blocks
	}
	maxElems := chunkBlocks * 64
	if maxElems <= 0 || maxElems > len(blocksIn) {
		maxElems = len(blocksIn)
	}
	inF32 := make([]float32, maxElems)
	outF32 := make([]float32, maxElems)
	for off := 0; off < blocks; off += chunkBlocks {
		n := blocks - off
		if n > chunkBlocks {
			n = chunkBlocks
		}
		inChunk := blocksIn[off*64 : (off+n)*64]
		outChunk := coeffOut[off*64 : (off+n)*64]
		elems := len(inChunk)
		inBuf := inF32[:elems]
		outBuf := outF32[:elems]
		vlxF64ToF32(inBuf, inChunk)
		b.mu.Lock()
		err := C.vlx_cuda_dct_many_f32(
			(*C.float)(unsafe.Pointer(&inBuf[0])),
			C.int(n),
			(*C.float)(unsafe.Pointer(&outBuf[0])),
		)
		b.mu.Unlock()
		if err != nil {
			msg := C.GoString(err)
			b.warnDCTOnce.Do(func() {
				fmt.Fprintf(os.Stderr, "[!] CUDA DCT path failed once (%s); falling back to CPU for failed chunks\n", msg)
			})
			cpuComputeBackend{}.DCT8x8EncodeMany(inChunk, outChunk)
			continue
		}
		vlxF32ToF64(outChunk, outBuf)
	}
}

func (b *cudaComputeBackend) IDCT8x8DecodeMany(coeffBlocks []float64, outBlocks []float64) {
	if len(coeffBlocks) == 0 {
		return
	}
	blocks := len(coeffBlocks) / 64
	if blocks == 0 {
		return
	}
	chunkBlocks := b.chunkBlocks
	if chunkBlocks <= 0 {
		chunkBlocks = blocks
	}
	maxElems := chunkBlocks * 64
	if maxElems <= 0 || maxElems > len(coeffBlocks) {
		maxElems = len(coeffBlocks)
	}
	inF32 := make([]float32, maxElems)
	outF32 := make([]float32, maxElems)
	for off := 0; off < blocks; off += chunkBlocks {
		n := blocks - off
		if n > chunkBlocks {
			n = chunkBlocks
		}
		inChunk := coeffBlocks[off*64 : (off+n)*64]
		outChunk := outBlocks[off*64 : (off+n)*64]
		elems := len(inChunk)
		inBuf := inF32[:elems]
		outBuf := outF32[:elems]
		vlxF64ToF32(inBuf, inChunk)
		b.mu.Lock()
		err := C.vlx_cuda_idct_many_f32(
			(*C.float)(unsafe.Pointer(&inBuf[0])),
			C.int(n),
			(*C.float)(unsafe.Pointer(&outBuf[0])),
		)
		b.mu.Unlock()
		if err != nil {
			msg := C.GoString(err)
			b.warnIDCTOnce.Do(func() {
				fmt.Fprintf(os.Stderr, "[!] CUDA IDCT path failed once (%s); falling back to CPU for failed chunks\n", msg)
			})
			cpuComputeBackend{}.IDCT8x8DecodeMany(inChunk, outChunk)
			continue
		}
		vlxF32ToF64(outChunk, outBuf)
	}
}

func (b *cudaComputeBackend) ComputeVLIX2BlockMVs(
	planType byte,
	curY []float64,
	prevY []float64,
	nextY []float64,
	width, height int,
	blockDim int,
	searchRadius int,
	motionThreshold int,
	motionEnabled bool,
) ([]vlix2BlockMV, bool) {
	bwBlocks := (width + blockDim - 1) / blockDim
	bhBlocks := (height + blockDim - 1) / blockDim
	total := bwBlocks * bhBlocks
	mvs := make([]vlix2BlockMV, total)
	if total == 0 {
		return mvs, true
	}
	if !motionEnabled {
		return mvs, true
	}
	if planType != vlxFrameDelta && planType != vlxFrameB {
		return nil, false
	}
	expected := width * height
	if len(curY) < expected || expected <= 0 {
		return nil, false
	}

	hasPrev := len(prevY) >= expected
	hasNext := len(nextY) >= expected
	if planType == vlxFrameDelta && !hasPrev {
		return mvs, true
	}
	if planType == vlxFrameB && !hasPrev && !hasNext {
		return mvs, true
	}

	out := make([]C.vlx_motion_mv, total)
	curF32 := make([]float32, expected)
	vlxF64ToF32(curF32, curY[:expected])
	var prevF32 []float32
	var nextF32 []float32
	var prevPtr *C.float
	var nextPtr *C.float
	if hasPrev {
		prevF32 = make([]float32, expected)
		vlxF64ToF32(prevF32, prevY[:expected])
		prevPtr = (*C.float)(unsafe.Pointer(&prevF32[0]))
	}
	if hasNext {
		nextF32 = make([]float32, expected)
		vlxF64ToF32(nextF32, nextY[:expected])
		nextPtr = (*C.float)(unsafe.Pointer(&nextF32[0]))
	}
	b.mu.Lock()
	err := C.vlx_cuda_motion_search_f32(
		(*C.float)(unsafe.Pointer(&curF32[0])),
		prevPtr,
		nextPtr,
		C.int(width),
		C.int(height),
		C.int(blockDim),
		C.int(searchRadius),
		C.int(motionThreshold),
		C.int(planType),
		C.int(total),
		(*C.vlx_motion_mv)(unsafe.Pointer(&out[0])),
	)
	b.mu.Unlock()
	if err != nil {
		msg := C.GoString(err)
		b.warnMotionOnce.Do(func() {
			fmt.Fprintf(os.Stderr, "[!] CUDA motion-search path failed once (%s); falling back to CPU motion search\n", msg)
		})
		return nil, false
	}

	for i := 0; i < total; i++ {
		mvs[i].mode = uint8(out[i].mode)
		mvs[i].dx1 = int(out[i].dx1)
		mvs[i].dy1 = int(out[i].dy1)
		mvs[i].dx2 = int(out[i].dx2)
		mvs[i].dy2 = int(out[i].dy2)
	}
	return mvs, true
}

func buildCUDAComputeBackend() (computeBackend, error) {
	var t32 [64]float32
	for r := 0; r < 8; r++ {
		for c := 0; c < 8; c++ {
			v := 0.5 * dctScale[r] * dctCos[r][c]
			t32[r*8+c] = float32(v)
		}
	}
	cerr := C.vlx_cuda_init_f32((*C.float)(unsafe.Pointer(&t32[0])))
	if cerr != nil {
		return nil, fmt.Errorf("CUDA init failed: %s", C.GoString(cerr))
	}
	chunkBlocks := 16384
	if s := os.Getenv("DENCODER_CUDA_CHUNK_BLOCKS"); s != "" {
		if v, err := strconv.Atoi(s); err == nil && v > 0 {
			chunkBlocks = v
		}
	}
	return &cudaComputeBackend{chunkBlocks: chunkBlocks}, nil
}

func buildVulkanComputeBackend() (computeBackend, error) {
	return nil, fmt.Errorf("Vulkan backend not implemented yet")
}
