package main

import (
	"fmt"
	"strings"
)

type computeBackend interface {
	Name() string
	DCT8x8EncodeMany(blocksIn []float64, coeffOut []float64)
	IDCT8x8DecodeMany(coeffBlocks []float64, outBlocks []float64)
}

type cpuComputeBackend struct{}

func (cpuComputeBackend) Name() string { return "cpu" }

func (cpuComputeBackend) DCT8x8EncodeMany(blocksIn []float64, coeffOut []float64) {
	dct8x8EncodeMany(blocksIn, coeffOut)
}

func (cpuComputeBackend) IDCT8x8DecodeMany(coeffBlocks []float64, outBlocks []float64) {
	idct8x8DecodeMany(coeffBlocks, outBlocks)
}

type unavailableComputeBackend struct {
	name   string
	reason string
}

func (b unavailableComputeBackend) Name() string { return b.name }

func (b unavailableComputeBackend) DCT8x8EncodeMany(blocksIn []float64, coeffOut []float64) {
	cpuComputeBackend{}.DCT8x8EncodeMany(blocksIn, coeffOut)
}

func (b unavailableComputeBackend) IDCT8x8DecodeMany(coeffBlocks []float64, outBlocks []float64) {
	cpuComputeBackend{}.IDCT8x8DecodeMany(coeffBlocks, outBlocks)
}

func (b unavailableComputeBackend) unavailableReason() string { return b.reason }

var (
	activeComputeBackend computeBackend = cpuComputeBackend{}
)

func setComputeBackend(spec string) error {
	s := strings.ToLower(strings.TrimSpace(spec))
	if s == "" || s == "auto" {
		if b, err := buildCUDAComputeBackend(); err == nil {
			activeComputeBackend = b
			return nil
		}
		activeComputeBackend = cpuComputeBackend{}
		return nil
	}
	switch s {
	case "cpu":
		activeComputeBackend = cpuComputeBackend{}
		return nil
	case "cuda":
		b, err := buildCUDAComputeBackend()
		if err != nil {
			activeComputeBackend = unavailableComputeBackend{name: "cuda", reason: err.Error()}
			return nil
		}
		activeComputeBackend = b
		return nil
	case "vulkan":
		b, err := buildVulkanComputeBackend()
		if err != nil {
			activeComputeBackend = unavailableComputeBackend{name: "vulkan", reason: err.Error()}
			return nil
		}
		activeComputeBackend = b
		return nil
	default:
		return fmt.Errorf("invalid compute backend: %q (expected auto|cpu|cuda|vulkan)", spec)
	}
}

func computeBackendName() string {
	if activeComputeBackend == nil {
		return "cpu"
	}
	return activeComputeBackend.Name()
}

func computeBackendNote() string {
	if b, ok := activeComputeBackend.(interface{ unavailableReason() string }); ok {
		return b.unavailableReason()
	}
	return ""
}

func dct8x8EncodeMany(blocksIn []float64, coeffOut []float64) {
	if len(blocksIn) == 0 {
		return
	}
	blocks := len(blocksIn) / 64
	for i := 0; i < blocks; i++ {
		off := i * 64
		var block [64]float64
		copy(block[:], blocksIn[off:off+64])
		coeff := dct8x8(block)
		copy(coeffOut[off:off+64], coeff[:])
	}
}

func dctEncodeMany(blocksIn []float64, coeffOut []float64) {
	activeComputeBackend.DCT8x8EncodeMany(blocksIn, coeffOut)
}

func idctDecodeMany(coeffBlocks []float64, outBlocks []float64) {
	activeComputeBackend.IDCT8x8DecodeMany(coeffBlocks, outBlocks)
}
