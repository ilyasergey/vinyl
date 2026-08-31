/* AFL++ injects -DFUZZING_BUILD_MODE_UNSAFE_FOR_PRODUCTION=1, which switches OFF
 * five decoder validity checks in libFLAC stream_decoder.c and switches ON its
 * allocation-failure injection. Neither is wanted here: the AFL build must
 * behave exactly like the libFuzzer build or the differential oracle would
 * compare two different libFLACs. -U on the command line loses (AFL appends its
 * -D after user flags), but an -include header is processed after all -D/-U. */
#undef FUZZING_BUILD_MODE_UNSAFE_FOR_PRODUCTION
