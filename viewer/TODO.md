# TODO

- [x] Critical memory issue (VLIX2 streaming path): replaced unbounded full-frame retention with bounded streaming cache + eviction/backpressure so RAM no longer grows linearly with frame count during playback.
- [ ] Extend bounded caching to legacy full-decode paths (`decodeVlix` / VLIX1 and non-stream paths) so those modes also avoid whole-video frame retention.
- [x] Investigated high-RAM behavior in `dencode2.11` VLIX2 workflows and fixed unbounded reference-frame retention in both VLIX2 encode/decode paths via reference eviction.
- [x] Fixed VLIX2 inter-frame reference drift bug in `dencode2.11` (closed-loop encoder references now use reconstructed quantized frames instead of original source planes).
- [ ] `dencode2.11`: reduce peak RAM in long audio/video jobs by replacing whole-PCM-in-memory paths (`extractAudioPCM` / `encodeALIXFromPCM`) with streaming/chunked audio processing.
- [ ] VLIX2 decode in viewer is too slow. Profile and optimize hot paths (threading and SIMD opportunities in decode/motion + color plane reconstruction).
- [ ] Add optional GPU decode backend for viewer VLIX2 path (CUDA first, backend abstraction designed for future Vulkan support).
- [x] Add CLIX shape syntax support used by `dencode` (`@x,y,w,h=TOKEN`, `@C,x,y,w,h=TOKEN`, `@T,x,y,w,h,o=TOKEN`) in viewer CLIX decoder.
