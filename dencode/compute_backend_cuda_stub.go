//go:build !cuda || !cgo

package main

import "fmt"

func buildCUDAComputeBackend() (computeBackend, error) {
	return nil, fmt.Errorf("CUDA backend not built (rebuild with -tags cuda and cgo enabled)")
}

func buildVulkanComputeBackend() (computeBackend, error) {
	return nil, fmt.Errorf("Vulkan backend not implemented yet")
}
