package main

import "C"

import (
	"fmt"
	"os"
	"strconv"
	"sync"
	"unsafe"
)

type cudaComputeBackend struct {
	mu           sync.Mutex
	warnDCTOnce  sync.Once
	warnIDCTOnce sync.Once
	chunkBlocks  int
}

func (b *cudaComputeBackend) Name() string { return "cuda" }

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
	for off := 0; off < blocks; off += chunkBlocks {
		n := blocks - off
		if n > chunkBlocks {
			n = chunkBlocks
		}
		inChunk := blocksIn[off*64 : (off+n)*64]
		outChunk := coeffOut[off*64 : (off+n)*64]
		b.mu.Lock()
		err := C.vlx_cuda_dct_many(
			(*C.double)(unsafe.Pointer(&inChunk[0])),
			C.int(n),
			(*C.double)(unsafe.Pointer(&outChunk[0])),
		)
		b.mu.Unlock()
		if err != nil {
			msg := C.GoString(err)
			b.warnDCTOnce.Do(func() {
				fmt.Fprintf(os.Stderr, "[!] Viewer CUDA DCT path failed once (%s); falling back to CPU for failed chunks\n", msg)
			})
			cpuComputeBackend{}.DCT8x8EncodeMany(inChunk, outChunk)
		}
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
	for off := 0; off < blocks; off += chunkBlocks {
		n := blocks - off
		if n > chunkBlocks {
			n = chunkBlocks
		}
		inChunk := coeffBlocks[off*64 : (off+n)*64]
		outChunk := outBlocks[off*64 : (off+n)*64]
		b.mu.Lock()
		err := C.vlx_cuda_idct_many(
			(*C.double)(unsafe.Pointer(&inChunk[0])),
			C.int(n),
			(*C.double)(unsafe.Pointer(&outChunk[0])),
		)
		b.mu.Unlock()
		if err != nil {
			msg := C.GoString(err)
			b.warnIDCTOnce.Do(func() {
				fmt.Fprintf(os.Stderr, "[!] Viewer CUDA IDCT path failed once (%s); falling back to CPU for failed chunks\n", msg)
			})
			cpuComputeBackend{}.IDCT8x8DecodeMany(inChunk, outChunk)
		}
	}
}

func buildCUDAComputeBackend() (computeBackend, error) {
	var t [64]float64
	for r := 0; r < 8; r++ {
		for c := 0; c < 8; c++ {
			t[r*8+c] = 0.5 * dctScale[r] * dctCos[r][c]
		}
	}
	cerr := C.vlx_cuda_init((*C.double)(unsafe.Pointer(&t[0])))
	if cerr != nil {
		return nil, fmt.Errorf("CUDA init failed: %s", C.GoString(cerr))
	}
	chunkBlocks := 16384
	if s := os.Getenv("VIEWER_CUDA_CHUNK_BLOCKS"); s != "" {
		if v, err := strconv.Atoi(s); err == nil && v > 0 {
			chunkBlocks = v
		}
	}
	if s := os.Getenv("CLIX_CUDA_CHUNK_BLOCKS"); s != "" {
		if v, err := strconv.Atoi(s); err == nil && v > 0 {
			chunkBlocks = v
		}
	}
	return &cudaComputeBackend{chunkBlocks: chunkBlocks}, nil
}

func buildVulkanComputeBackend() (computeBackend, error) {
	return nil, fmt.Errorf("Vulkan backend not implemented yet")
}
