#include "vlx_accel.h"

#include <windows.h>
#include <stdarg.h>
#include <stddef.h>
#include <stdio.h>
#include <stdlib.h>

int vlix_idct_backend_id(void) { return 0; }

void vlix_idct8x8(const double *coeff, const double *C, const double *S, double *out) {
	double tmp[64];
	for (int v = 0; v < 8; v++)
		for (int x = 0; x < 8; x++) {
			double sum = 0.0;
			for (int u = 0; u < 8; u++) sum += S[u] * coeff[v * 8 + u] * C[u * 8 + x];
			tmp[v * 8 + x] = sum;
		}
	for (int y = 0; y < 8; y++)
		for (int x = 0; x < 8; x++) {
			double sum = 0.0;
			for (int v = 0; v < 8; v++) sum += S[v] * tmp[v * 8 + x] * C[v * 8 + y];
			out[y * 8 + x] = 0.25 * sum;
		}
}

void vlix_idct8x8_many(const double *coeff, int blocks, const double *C, const double *S, double *out) {
	for (int b = 0; b < blocks; b++) vlix_idct8x8(coeff + b * 64, C, S, out + b * 64);
}

#ifndef VLX_ACCEL_NO_GPU

#include "vlx_ptx.h" /* static const char *VLX_PTX */

typedef int CUresult;
typedef int CUdevice;
typedef unsigned long long CUdeviceptr;
typedef struct CUctx_st *CUcontext;
typedef struct CUmod_st *CUmodule;
typedef struct CUfunc_st *CUfunction;

#define CU_SUCCESS 0

typedef CUresult(*pfn_cuInit)(unsigned int);
typedef CUresult(*pfn_cuDeviceGet)(CUdevice *, int);
typedef CUresult(*pfn_cuDevicePrimaryCtxRetain)(CUcontext *, CUdevice);
typedef CUresult(*pfn_cuCtxSetCurrent)(CUcontext);
typedef CUresult(*pfn_cuModuleLoadDataEx)(CUmodule *, const void *, unsigned int, int *, void **);
typedef CUresult(*pfn_cuModuleGetFunction)(CUfunction *, CUmodule, const char *);
typedef CUresult(*pfn_cuMemAlloc)(CUdeviceptr *, size_t);
typedef CUresult(*pfn_cuMemFree)(CUdeviceptr);
typedef CUresult(*pfn_cuMemcpyHtoD)(CUdeviceptr, const void *, size_t);
typedef CUresult(*pfn_cuMemcpyDtoH)(void *, CUdeviceptr, size_t);
typedef CUresult(*pfn_cuLaunchKernel)(CUfunction, unsigned int, unsigned int, unsigned int,
	unsigned int, unsigned int, unsigned int, unsigned int, void *, void **, void **);
typedef CUresult(*pfn_cuCtxSynchronize)(void);
typedef CUresult(*pfn_cuGetErrorName)(CUresult, const char **);

static pfn_cuInit p_cuInit;
static pfn_cuDeviceGet p_cuDeviceGet;
static pfn_cuDevicePrimaryCtxRetain p_cuDevicePrimaryCtxRetain;
static pfn_cuCtxSetCurrent p_cuCtxSetCurrent;
static pfn_cuModuleLoadDataEx p_cuModuleLoadDataEx;
static pfn_cuModuleGetFunction p_cuModuleGetFunction;
static pfn_cuMemAlloc p_cuMemAlloc;
static pfn_cuMemFree p_cuMemFree;
static pfn_cuMemcpyHtoD p_cuMemcpyHtoD;
static pfn_cuMemcpyDtoH p_cuMemcpyDtoH;
static pfn_cuLaunchKernel p_cuLaunchKernel;
static pfn_cuCtxSynchronize p_cuCtxSynchronize;
static pfn_cuGetErrorName p_cuGetErrorName;

static int g_ready = 0;
static CUcontext g_ctx;
static CUmodule g_mod;
static CUfunction g_dct, g_idct;
static CUdeviceptr g_dT;
static char g_err[1024];

static const char *vlx_errf(const char *fmt, ...) {
	va_list ap;
	va_start(ap, fmt);
	vsnprintf(g_err, sizeof(g_err), fmt, ap);
	va_end(ap);
	return g_err;
}

static const char *cu_errf(const char *where, CUresult r) {
	const char *name = NULL;
	if (p_cuGetErrorName) p_cuGetErrorName(r, &name);
	return vlx_errf("%s failed: %s (%d)", where, name ? name : "?", r);
}

static int resolve_driver(void) {
	HMODULE drv = LoadLibraryA("nvcuda.dll");
	if (!drv) return 0;
	p_cuInit = (pfn_cuInit)GetProcAddress(drv, "cuInit");
	p_cuDeviceGet = (pfn_cuDeviceGet)GetProcAddress(drv, "cuDeviceGet");
	p_cuDevicePrimaryCtxRetain = (pfn_cuDevicePrimaryCtxRetain)GetProcAddress(drv, "cuDevicePrimaryCtxRetain");
	p_cuCtxSetCurrent = (pfn_cuCtxSetCurrent)GetProcAddress(drv, "cuCtxSetCurrent");
	p_cuModuleLoadDataEx = (pfn_cuModuleLoadDataEx)GetProcAddress(drv, "cuModuleLoadDataEx");
	p_cuModuleGetFunction = (pfn_cuModuleGetFunction)GetProcAddress(drv, "cuModuleGetFunction");
	p_cuMemAlloc = (pfn_cuMemAlloc)GetProcAddress(drv, "cuMemAlloc_v2");
	p_cuMemFree = (pfn_cuMemFree)GetProcAddress(drv, "cuMemFree_v2");
	p_cuMemcpyHtoD = (pfn_cuMemcpyHtoD)GetProcAddress(drv, "cuMemcpyHtoD_v2");
	p_cuMemcpyDtoH = (pfn_cuMemcpyDtoH)GetProcAddress(drv, "cuMemcpyDtoH_v2");
	p_cuLaunchKernel = (pfn_cuLaunchKernel)GetProcAddress(drv, "cuLaunchKernel");
	p_cuCtxSynchronize = (pfn_cuCtxSynchronize)GetProcAddress(drv, "cuCtxSynchronize");
	p_cuGetErrorName = (pfn_cuGetErrorName)GetProcAddress(drv, "cuGetErrorName");
	return p_cuInit && p_cuDeviceGet && p_cuDevicePrimaryCtxRetain && p_cuCtxSetCurrent &&
		p_cuModuleLoadDataEx && p_cuModuleGetFunction && p_cuMemAlloc && p_cuMemFree &&
		p_cuMemcpyHtoD && p_cuMemcpyDtoH && p_cuLaunchKernel && p_cuCtxSynchronize;
}

const char *vlx_cuda_init(const double *table64) {
	CUresult r;
	CUdevice dev;

	if (g_ready) return NULL;
	if (!resolve_driver()) return vlx_errf("could not load nvcuda.dll driver entry points");

	if ((r = p_cuInit(0)) != CU_SUCCESS) return cu_errf("cuInit", r);
	if ((r = p_cuDeviceGet(&dev, 0)) != CU_SUCCESS) return cu_errf("cuDeviceGet", r);
	if ((r = p_cuDevicePrimaryCtxRetain(&g_ctx, dev)) != CU_SUCCESS) return cu_errf("cuDevicePrimaryCtxRetain", r);
	if ((r = p_cuCtxSetCurrent(g_ctx)) != CU_SUCCESS) return cu_errf("cuCtxSetCurrent", r);

	r = p_cuModuleLoadDataEx(&g_mod, VLX_PTX, 0, NULL, NULL);
	if (r != CU_SUCCESS) return cu_errf("cuModuleLoadDataEx", r);
	if ((r = p_cuModuleGetFunction(&g_dct, g_mod, "dct_many")) != CU_SUCCESS) return cu_errf("cuModuleGetFunction(dct_many)", r);
	if ((r = p_cuModuleGetFunction(&g_idct, g_mod, "idct_many")) != CU_SUCCESS) return cu_errf("cuModuleGetFunction(idct_many)", r);

	if ((r = p_cuMemAlloc(&g_dT, 64 * sizeof(double))) != CU_SUCCESS) return cu_errf("cuMemAlloc(table)", r);
	if ((r = p_cuMemcpyHtoD(g_dT, table64, 64 * sizeof(double))) != CU_SUCCESS) return cu_errf("cuMemcpyHtoD(table)", r);

	g_ready = 1;
	return NULL;
}

static const char *run_transform(CUfunction fn, const double *in, int n, double *out) {
	CUresult r;
	CUdeviceptr d_in = 0, d_out = 0;
	void *args[4];
	size_t bytes;

	if (!g_ready) return vlx_errf("cuda backend not initialized");
	if (n <= 0) return NULL;
	bytes = (size_t)n * 64 * sizeof(double);
	p_cuCtxSetCurrent(g_ctx);
	if ((r = p_cuMemAlloc(&d_in, bytes)) != CU_SUCCESS) return cu_errf("cuMemAlloc(in)", r);
	if ((r = p_cuMemAlloc(&d_out, bytes)) != CU_SUCCESS) {
		p_cuMemFree(d_in);
		return cu_errf("cuMemAlloc(out)", r);
	}
	if ((r = p_cuMemcpyHtoD(d_in, in, bytes)) != CU_SUCCESS) goto done;
	args[0] = &d_in;
	args[1] = &n;
	args[2] = &g_dT;
	args[3] = &d_out;
	if ((r = p_cuLaunchKernel(fn, (unsigned)n, 1, 1, 64, 1, 1, 0, NULL, args, NULL)) != CU_SUCCESS) goto done;
	if ((r = p_cuCtxSynchronize()) != CU_SUCCESS) goto done;
	r = p_cuMemcpyDtoH(out, d_out, bytes);
done:
	p_cuMemFree(d_in);
	p_cuMemFree(d_out);
	return (r != CU_SUCCESS) ? cu_errf("transform launch", r) : NULL;
}

const char *vlx_cuda_dct_many(const double *in, int n, double *out) {
	return run_transform(g_dct, in, n, out);
}

const char *vlx_cuda_idct_many(const double *in, int n, double *out) {
	return run_transform(g_idct, in, n, out);
}

#endif
