#ifndef MFKEY_DEDUP_H
#define MFKEY_DEDUP_H

#include "mfkey.h"
#include "crypto1.h"
#include <stdint.h>
#include <stdbool.h>

/* Fibonacci multiply-shift hash: 20-bit input -> 11-bit output */
#define FIB_HASH_20BIT(x) (((x) * 2654435769u) >> 21)

/*
 * Quick existence test for rounds 1-3. Returns 1 if any path through
 * the filter tree survives, 0 if all eliminated. Does not advance state.
 */

static inline __attribute__((always_inline)) int prefilter_rounds_1_3(
    uint32_t semi_state,
    int oks)
{
    OPT_BARRIER(oks);
    uint32_t nib1 = ((0x0d938 >> ((semi_state >> 15) & 0xF)) & 1);
    uint32_t nib2 = ((0x0d938 >> ((semi_state >> 14) & 0xF)) & 1);
    uint32_t nib3 = ((0x0d938 >> ((semi_state >> 13) & 0xF)) & 1);

    uint32_t v = semi_state << 1;
    int target = BIT(oks, 1);
    uint32_t fp = filter_pair_with_nib(v, nib1);
    int f0 = FILTER_F0(fp);
    int f1 = FILTER_F1(fp);

    int r1_valid = ((f0 == target) << 0) | ((f1 == target) << 1);
    if (!r1_valid) return 0;

    target = BIT(oks, 2);
    int r2_valid = 0;

    if (r1_valid & 1) {
        fp = filter_pair_with_nib(v << 1, nib2);
        f0 = FILTER_F0(fp);
        f1 = FILTER_F1(fp);
        if (f0 == target) r2_valid |= 1;
        if (f1 == target) r2_valid |= 2;
    }
    if (r1_valid & 2) {
        fp = filter_pair_with_nib((v | 1) << 1, nib2);
        f0 = FILTER_F0(fp);
        f1 = FILTER_F1(fp);
        if (f0 == target) r2_valid |= 4;
        if (f1 == target) r2_valid |= 8;
    }

    if (!r2_valid) return 0;

    target = BIT(oks, 3);

    if (r2_valid & 1) {
        fp = filter_pair_with_nib(v << 2, nib3);
        f0 = FILTER_F0(fp);
        f1 = FILTER_F1(fp);
        if (f0 == target || f1 == target) return 1;
    }
    if (r2_valid & 2) {
        fp = filter_pair_with_nib((v << 2) | 2, nib3);
        f0 = FILTER_F0(fp);
        f1 = FILTER_F1(fp);
        if (f0 == target || f1 == target) return 1;
    }
    if (r2_valid & 4) {
        fp = filter_pair_with_nib((v | 1) << 2, nib3);
        f0 = FILTER_F0(fp);
        f1 = FILTER_F1(fp);
        if (f0 == target || f1 == target) return 1;
    }
    if (r2_valid & 8) {
        fp = filter_pair_with_nib(((v | 1) << 2) | 2, nib3);
        f0 = FILTER_F0(fp);
        f1 = FILTER_F1(fp);
        if (f0 == target || f1 == target) return 1;
    }

    return 0;
}

/* Duff's device scan for duplicate in packed 24-bit state array */
static inline __attribute__((always_inline)) bool scan_for_duplicate_8x(
    const uint8_t *states, int count, uint32_t state_masked)
{
    if (count <= 0) return false;

    const uint8_t *p = states;
    int n = (count + 7) / 8;
    switch (count % 8) {
        case 0: do { if ((*(uint32_t*)p & 0x00FFFFFF) == state_masked) return true; p += 3; __attribute__((fallthrough));
        case 7:      if ((*(uint32_t*)p & 0x00FFFFFF) == state_masked) return true; p += 3; __attribute__((fallthrough));
        case 6:      if ((*(uint32_t*)p & 0x00FFFFFF) == state_masked) return true; p += 3; __attribute__((fallthrough));
        case 5:      if ((*(uint32_t*)p & 0x00FFFFFF) == state_masked) return true; p += 3; __attribute__((fallthrough));
        case 4:      if ((*(uint32_t*)p & 0x00FFFFFF) == state_masked) return true; p += 3; __attribute__((fallthrough));
        case 3:      if ((*(uint32_t*)p & 0x00FFFFFF) == state_masked) return true; p += 3; __attribute__((fallthrough));
        case 2:      if ((*(uint32_t*)p & 0x00FFFFFF) == state_masked) return true; p += 3; __attribute__((fallthrough));
        case 1:      if ((*(uint32_t*)p & 0x00FFFFFF) == state_masked) return true; p += 3;
                } while (--n > 0);
    }
    return false;
}

#endif // MFKEY_DEDUP_H
