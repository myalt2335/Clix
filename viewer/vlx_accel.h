#ifndef VLX_ACCEL_H
#define VLX_ACCEL_H

#ifdef __cplusplus
extern "C" {
#endif

int  vlix_idct_backend_id(void);
void vlix_idct8x8(const double *coeff, const double *dctCos, const double *dctScale, double *out);
void vlix_idct8x8_many(const double *coeff, int blocks, const double *dctCos, const double *dctScale, double *out);

const char *vlx_cuda_init(const double *table64);
const char *vlx_cuda_dct_many(const double *in, int n, double *out);
const char *vlx_cuda_idct_many(const double *in, int n, double *out);

#ifdef __cplusplus
}
#endif

#endif
