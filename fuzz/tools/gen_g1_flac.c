/* gen_g1_flac (B2) -- materialize the G1 hostile-chooser space as committed FLAC
 * seeds. G1 (common/vinyl_gen.c) drives Vinyl's own proven writer
 * (Stream.Unchecked.encode) from a RAW parameter block, so it emits
 * correct-by-construction FLAC across the whole legal option space -- arbitrary
 * bit depth, channel count, and the hostile EncoderCfg choosers (LPC 9-32,
 * mid/side, partition orders, RICE2 large-k, and the B3 parameterized
 * order-7 / partition-{4,5,6,8} / RICE2-k{18,24,28,30} (the OOM-safe encode-side
 * sets, all k>17 -- the general readRiceSeqScan path) / stereo-mode / invalid
 * arms). Running G1 as a live campaign burns executions re-deriving these; this
 * tool bakes the interesting cells into a static corpus the decode targets share.
 *
 * Each cell builds the 9-byte RAW block that gen_build (vinyl_gen.c) decodes to
 * the wanted parameters, runs vinyl_gen_encode, and writes the resulting FLAC to
 * <dir>/g1_<name>.flac. Small block size (16) and nsamples keep every file well
 * under 16 KiB so libFuzzer/AFL can still evolve them.
 *
 *   gen_g1_flac <output-dir>
 *
 * RAW block layout consumed by gen_build (see vinyl_gen.c):
 *   data[0] : bps-1        (bps = 1 + data[0]%32)
 *   data[1] : ch-1         (ch  = 1 + data[1]%8)
 *   data[2] : bit0 adversarial | bits1-2 advkind | bits3-4 population
 *   data[3] : bits0-2 block-size index (k_bs) | bits3-5 chooser_kind
 *   data[4],[5] : nsamples low / seed  (ns = 16 + (LE16 % (2048-16)))
 *   data[6] : sample-rate index (k_sr, bits0-2)
 *   data[7] : seed byte
 *   data[8] : captured-argument byte for chooser_kind 5/6/7 (B3)
 */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/stat.h>

#include "vinyl_api.h" /* vinyl_init */
#include "vinyl_gen.h" /* vinyl_gen_encode, GenParams */

/* bps -> data[0] value (data[0]%32 == bps-1 for bps in 1..32). */
static uint8_t bps_byte(int bps) { return (uint8_t)(bps - 1); }

/* One chooser cell: kind selects the EncoderCfg chooser slot, arg feeds the B3
 * captured-argument byte (data[8]); only meaningful for kinds 5-7. */
typedef struct {
  int kind;
  unsigned arg;
  const char *name;
} Chooser;

/* The hostile set: fixed choosers 1-4, plus the B3 parameterized arms in slots
 * 5-7. Names describe the ACTUAL emitted structure: gen_build maps the captured
 * arg through the OOM-safe sets po_set[arg&3]={4,5,6,8} (slot 6) and
 * k_set[arg&3]={18,24,28,30} (slot 7 RICE2), and 1+arg%32 (slot 5 LPC). Args are
 * chosen so arg&3 = 0,1,2,3 hits every distinct value. RICE2 k are all >17 (the
 * general readRiceSeqScan path); very high PO / small-k RICE2 are OOM-bounded away
 * on the encode side by design (see vinyl_gen.c slots 6/7). NOTE: gen_build now
 * raises the RICE2 k to max(base, bps-3) for OOM-safety, so a "rice2_k18" cell at
 * bps>=22 actually emits a larger k (still >17, same decode path) -- the cell name
 * is the requested BASE k, the emitted k scales with the cell's bps to stay bounded. */
static const Chooser k_choosers[] = {
    {1, 0, "lpc32"},        {2, 0, "stereo"},       {3, 0, "partition16"},
    {4, 0, "fixed_rice28"},
    {5, 6, "lpcN_ord7"},    {5, 11, "lpcN_ord12"},  {5, 31, "lpcN_ord32"},
    {6, 0, "part_po4"},     {6, 1, "part_po5"},     {6, 2, "part_po6"},   {6, 3, "part_po8"},
    {7, 0, "rice2_k18"},    {7, 1, "rice2_k24"},    {7, 2, "rice2_k28"},  {7, 3, "rice2_k30"},
    {7, 64, "stereomode0"}, {7, 65, "stereomode1"},
    {7, 66, "stereomode2"}, {7, 67, "stereomode3"}, {7, 128, "invalid"},
};

/* bps span from CONTRACT/plan; sample-rate index 4 = 44100 (k_sr in vinyl_gen.c). */
static const int k_bps[] = {8, 12, 16, 24, 32};
static const int k_ch[] = {1, 2};

static int write_file(const char *dir, const char *name, const uint8_t *buf, size_t len) {
  char path[1024];
  snprintf(path, sizeof path, "%s/%s", dir, name);
  FILE *f = fopen(path, "wb");
  if (!f) {
    fprintf(stderr, "gen_g1_flac: cannot open %s\n", path);
    return 1;
  }
  if (len && fwrite(buf, 1, len, f) != len) {
    fprintf(stderr, "gen_g1_flac: short write %s\n", path);
    fclose(f);
    return 1;
  }
  fclose(f);
  return 0;
}

int main(int argc, char **argv) {
  if (argc < 2) {
    fprintf(stderr, "usage: %s <output-dir>\n", argv[0]);
    return 2;
  }
  const char *dir = argv[1];
  mkdir(dir, 0755); /* best-effort; existing dir is fine */
  if (vinyl_init())
    return 1;

  unsigned long written = 0, skipped = 0;
  for (size_t bi = 0; bi < sizeof k_bps / sizeof k_bps[0]; bi++)
    for (size_t ci = 0; ci < sizeof k_ch / sizeof k_ch[0]; ci++)
      for (size_t ki = 0; ki < sizeof k_choosers / sizeof k_choosers[0]; ki++) {
        const Chooser *ch = &k_choosers[ki];
        uint8_t data[9];
        data[0] = bps_byte(k_bps[bi]);
        data[1] = (uint8_t)(k_ch[ci] - 1);
        data[2] = (uint8_t)(3u << 3);           /* valid population 3 (sine): real residuals */
        /* Partition-order cells (slot 6) need a REAL block so the forced PO is
         * valid: a 16-sample frame makes any PO>0 degenerate and safeChooser
         * falls back to VERBATIM. bs index 7 = 1024 samples, ns = 1024 (a full
         * frame): 1024 % 2^po == 0 for po<=8 with samples/partition > fixed order.
         * Other cells (LPC/RICE2/fixed) keep the tiny 16-sample block. */
        int big = (ch->kind == 6);
        uint8_t bs_idx = big ? 7u : 0u;         /* 7 -> 1024 samples, 0 -> 16 */
        unsigned ns_x = big ? 1008u : 0u;       /* gen_build: ns = 16 + ns_x%2032 -> 1024 or 16 */
        data[3] = (uint8_t)(bs_idx | (ch->kind << 3)); /* bs index | chooser_kind */
        data[4] = (uint8_t)(ns_x & 0xffu);      /* nsamples low */
        data[5] = (uint8_t)(ns_x >> 8);         /* nsamples high */
        data[6] = 4;                            /* sample-rate index 4 = 44100 */
        data[7] = 0;                            /* seed */
        data[8] = (uint8_t)ch->arg;             /* captured-argument byte (B3) */

        uint8_t *flac = NULL;
        size_t flen = 0;
        GenParams gp;
        if (!vinyl_gen_encode(data, sizeof data, &flac, &flen, &gp) || flen == 0) {
          skipped++;
          continue;
        }
        char name[128];
        snprintf(name, sizeof name, "g1_bps%d_ch%d_%s.flac", k_bps[bi], k_ch[ci], ch->name);
        if (write_file(dir, name, flac, flen))
          return 1;
        written++;
      }

  printf("gen_g1_flac: wrote %lu FLAC seeds to %s (%lu skipped)\n", written, dir, skipped);
  return 0;
}
