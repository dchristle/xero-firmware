// MFKey32 Optimized Attack Implementation

#pragma GCC optimize("O3")

#include <stdlib.h>
#include <string.h>
#include <furi.h>
#include "mfkey_attack.h"
#include "crypto1.h"
#include "mfkey_bs_verify.h"

// Global abort flag - checked in hot-path without passing through recursion
static volatile bool g_abort_attack = false;
static ProgramState *g_program_state = NULL;

// Externs from mfkey.c
extern int sync_state(ProgramState *program_state);
extern void flush_key_buffer(ProgramState *program_state);
extern uint8_t MSB_LIMIT;

#define SWAP(a, b) do { unsigned int t = a; a = b; b = t; } while (0)

// Validate candidate LFSR state. Returns 1 if key found, 0 otherwise.

static inline int check_state(struct Crypto1State *t, MfClassicNonce *n) {
    if (!(t->odd | t->even))
        return 0;

    if (n->attack == mfkey32) {
        uint32_t rb = (napi_lfsr_rollback_word(t, 0, 0) ^ n->p64);
        if (rb != n->ar0_enc) {
            return 0;
        }
        rollback_word_noret(t, n->nr0_enc, 1);
        rollback_word_noret(t, n->uid_xor_nt0, 0);
        struct Crypto1State temp = {t->odd, t->even};
        crypt_word_noret(t, n->uid_xor_nt1, 0);
        crypt_word_noret(t, n->nr1_enc, 1);
        if (n->ar1_enc == (crypt_word(t) ^ n->p64b)) {
            crypto1_get_lfsr(&temp, &(n->key));
            return 1;
        }
    } else if (n->attack == static_nested) {
        struct Crypto1State temp = {t->odd, t->even};
        rollback_word_noret(t, n->uid_xor_nt1, 0);
        if (n->ks1_1_enc == crypt_word_ret(t, n->uid_xor_nt0, 0)) {
            rollback_word_noret(&temp, n->uid_xor_nt1, 0);
            crypto1_get_lfsr(&temp, &(n->key));
            return 1;
        }
    } else if (n->attack == static_encrypted) {
        if (n->ks1_1_enc == napi_lfsr_rollback_word(t, n->uid_xor_nt0, 0)) {
            uint8_t local_parity_keystream_bits;
            struct Crypto1State temp = {t->odd, t->even};
            if ((crypt_word_par(&temp, n->uid_xor_nt0, 0, n->nt0, &local_parity_keystream_bits) ==
                 n->ks1_1_enc) &&
                (local_parity_keystream_bits == n->par_1)) {
                crypto1_get_lfsr(t, &(n->key));
                g_program_state->num_candidates++;
                g_program_state->key_buffer[g_program_state->key_buffer_count] = n->key;
                g_program_state->key_idx_buffer[g_program_state->key_buffer_count] = n->key_idx;
                g_program_state->key_buffer_count++;
                if (g_program_state->key_buffer_count >= g_program_state->key_buffer_size) {
                    flush_key_buffer(g_program_state);
                }
            }
        }
    }
    return 0;
}

// LFSR state expansion through 12 rounds
static inline __attribute__((hot)) int state_loop(
    unsigned int *states_buffer,
    int xks,
    int m1,
    int m2,
    unsigned int in,
    int and_val)
{
    int states_tail = 0;
    int xks_bit = 0;
    unsigned int round_in = 0;  // Must be unsigned to avoid UB on << 24

    // Unroll first 4 rounds (no round_in calculations needed)
    // Early exit when all states eliminated (95%+ of calls)
    for (int round = 1; round <= 4; ++round) {
        xks_bit = BIT(xks, round);
        for (int s = 0; s <= states_tail; ++s) {
            unsigned int v = states_buffer[s] << 1;
            states_buffer[s] = v;
            // Compute filter(v) and filter(v|1) with shared lookup work
            uint32_t fp = filter_pair(v);
            int f0 = FILTER_F0(fp);
            int f1 = FILTER_F1(fp);

            if (__builtin_expect((f0 ^ f1) != 0, 0)) {
                states_buffer[s] |= f0 ^ xks_bit;
            } else if (__builtin_expect(f0 == xks_bit, 1)) {
                // Buffer size is 1280; check limit before expanding to prevent corruption
                if (__builtin_expect(states_tail >= 1270, 0)) {
                    break;
                }
                states_buffer[++states_tail] = states_buffer[++s];
                states_buffer[s] = states_buffer[s - 1] | 1;
            } else {
                states_buffer[s--] = states_buffer[states_tail--];
            }
        }
        // Early termination: 95%+ of calls eliminate all states
        if (__builtin_expect(states_tail < 0, 1)) goto done;
    }

    // Round 5 (unrolled)
    {
        xks_bit = BIT(xks, 5);
        unsigned int r5_in = ((in >> 2) & and_val) << 24;  // Must be unsigned
        for (int s = 0; s <= states_tail; ++s) {
            unsigned int v = states_buffer[s] << 1;
            states_buffer[s] = v;
            uint32_t fp = filter_pair(v);
            int f0 = FILTER_F0(fp);
            int f1 = FILTER_F1(fp);
            if (__builtin_expect((f0 ^ f1) != 0, 0)) {
                states_buffer[s] |= f0 ^ xks_bit;
                update_contribution(states_buffer, s, m1, m2);
                states_buffer[s] ^= r5_in;
            } else if (__builtin_expect(f0 == xks_bit, 1)) {
                if (__builtin_expect(states_tail >= 1270, 0)) break;
                states_buffer[++states_tail] = states_buffer[s + 1];
                states_buffer[s + 1] = v | 1;
                update_contribution(states_buffer, s, m1, m2);
                states_buffer[s++] ^= r5_in;
                update_contribution(states_buffer, s, m1, m2);
                states_buffer[s] ^= r5_in;
            } else {
                states_buffer[s--] = states_buffer[states_tail--];
            }
        }
        if (__builtin_expect(states_tail < 0, 0)) goto done;
    }

    // Round 6 (unrolled)
    {
        xks_bit = BIT(xks, 6);
        unsigned int r6_in = ((in >> 4) & and_val) << 24;  // Must be unsigned
        for (int s = 0; s <= states_tail; ++s) {
            unsigned int v = states_buffer[s] << 1;
            states_buffer[s] = v;
            uint32_t fp = filter_pair(v);
            int f0 = FILTER_F0(fp);
            int f1 = FILTER_F1(fp);
            if (__builtin_expect((f0 ^ f1) != 0, 0)) {
                states_buffer[s] |= f0 ^ xks_bit;
                update_contribution(states_buffer, s, m1, m2);
                states_buffer[s] ^= r6_in;
            } else if (__builtin_expect(f0 == xks_bit, 1)) {
                if (__builtin_expect(states_tail >= 1270, 0)) break;
                states_buffer[++states_tail] = states_buffer[s + 1];
                states_buffer[s + 1] = v | 1;
                update_contribution(states_buffer, s, m1, m2);
                states_buffer[s++] ^= r6_in;
                update_contribution(states_buffer, s, m1, m2);
                states_buffer[s] ^= r6_in;
            } else {
                states_buffer[s--] = states_buffer[states_tail--];
            }
        }
        if (__builtin_expect(states_tail < 0, 0)) goto done;
    }

    // Loop rounds 7-12
    for (int round = 7; round <= 12; ++round) {
        xks_bit = BIT(xks, round);
        round_in = ((in >> (2 * (round - 4))) & and_val) << 24;
        for (int s = 0; s <= states_tail; ++s) {
            unsigned int v = states_buffer[s] << 1;
            states_buffer[s] = v;
            uint32_t fp = filter_pair(v);
            int f0 = FILTER_F0(fp);
            int f1 = FILTER_F1(fp);
            if (__builtin_expect((f0 ^ f1) != 0, 0)) {
                states_buffer[s] |= f0 ^ xks_bit;
                update_contribution(states_buffer, s, m1, m2);
                states_buffer[s] ^= round_in;
            } else if (__builtin_expect(f0 == xks_bit, 1)) {
                if (__builtin_expect(states_tail >= 1270, 0)) break;
                states_buffer[++states_tail] = states_buffer[s + 1];
                states_buffer[s + 1] = v | 1;
                update_contribution(states_buffer, s, m1, m2);
                states_buffer[s++] ^= round_in;
                update_contribution(states_buffer, s, m1, m2);
                states_buffer[s] ^= round_in;
            } else {
                states_buffer[s--] = states_buffer[states_tail--];
            }
        }
        if (__builtin_expect(states_tail < 0, 0)) goto done;
    }

done:
    return states_tail;
}

static inline __attribute__((always_inline)) int binsearch(unsigned int data[], int start, int stop) {
    unsigned int msb_val = data[stop] & 0xff000000;

    while (start != stop) {
        int mid = start + ((stop - start) >> 1);
        if (data[mid] >= msb_val) {
            stop = mid;
        } else {
            start = mid + 1;
        }
    }
    return start;
}

// O(n) radix sort - replaces quicksort
#define RADIX_BITS 8
#define RADIX_SIZE (1 << RADIX_BITS)
#define RADIX_MASK (RADIX_SIZE - 1)

// Static buffer for radix sort scratch (shared with expansion phase)
static unsigned int g_radix_temp[1280];

static void radix_sort_32(unsigned int* arr, int low, int high, unsigned int* temp) {
    int count = high - low + 1;
    if (count <= 1) return;

    // Small arrays use insertion sort
    if (count < 32) {
        for (int i = low + 1; i <= high; i++) {
            unsigned int key = arr[i];
            int j = i - 1;
            while (j >= low && arr[j] > key) {
                arr[j + 1] = arr[j];
                j--;
            }
            arr[j + 1] = key;
        }
        return;
    }

    // Ensure we don't overflow temp buffer
    if (count > 1280) {
        count = 1280;
        high = low + count - 1;
    }

    // 256-entry histogram
    unsigned int hist[RADIX_SIZE];
    unsigned int* src = arr + low;
    unsigned int* dst = temp;

    // 4 passes for 32-bit values (LSD: least significant digit first)
    for (int pass = 0; pass < 4; pass++) {
        int shift = pass * RADIX_BITS;

        // Build histogram
        memset(hist, 0, sizeof(hist));
        for (int i = 0; i < count; i++) {
            hist[(src[i] >> shift) & RADIX_MASK]++;
        }

        // Convert histogram to offsets (prefix sum)
        unsigned int total = 0;
        for (int i = 0; i < RADIX_SIZE; i++) {
            unsigned int c = hist[i];
            hist[i] = total;
            total += c;
        }

        // Scatter to destination
        for (int i = 0; i < count; i++) {
            int bucket = (src[i] >> shift) & RADIX_MASK;
            dst[hist[bucket]++] = src[i];
        }

        // Swap src/dst for next pass
        unsigned int* t = src;
        src = dst;
        dst = t;
    }

    // After 4 (even) passes, result is in original position
}

static inline __attribute__((always_inline)) void update_contribution_odd(unsigned int data[], int item) {
    unsigned int val = data[item];
    unsigned int p = val >> 25;  // Use unsigned to avoid UB on left shift
    p = p << 1 | evenparity32(val & CONST_M1_1);
    p = p << 1 | evenparity32(val & CONST_M2_1);
    data[item] = (p << 24) | (val & 0xffffff);
}

static inline __attribute__((always_inline)) void update_contribution_even(unsigned int data[], int item) {
    unsigned int val = data[item];
    unsigned int p = val >> 25;  // Use unsigned to avoid UB on left shift
    p = p << 1 | evenparity32(val & CONST_M1_2);
    p = p << 1 | evenparity32(val & CONST_M2_2);
    data[item] = (p << 24) | (val & 0xffffff);
}

static int __attribute__((hot)) extend_table_odd(unsigned int data[], int tbl, int end, int bit) {
    for (data[tbl] <<= 1; tbl <= end; data[++tbl] <<= 1) {
        int f0 = filter(data[tbl]);
        int f1 = filter(data[tbl] | 1);
        if ((f0 ^ f1) != 0) {
            data[tbl] |= f0 ^ bit;
            update_contribution_odd(data, tbl);
        } else if (f0 == bit) {
            if (__builtin_expect(end >= 1270, 0)) break;
            data[++end] = data[tbl + 1];
            data[tbl + 1] = data[tbl] | 1;
            update_contribution_odd(data, tbl);
            tbl++;
            update_contribution_odd(data, tbl);
        } else {
            data[tbl--] = data[end--];
        }
    }
    return end;
}

static int __attribute__((hot)) extend_table_even(unsigned int data[], int tbl, int end, int bit, unsigned int in) {
    in <<= 24;
    for (data[tbl] <<= 1; tbl <= end; data[++tbl] <<= 1) {
        int f0 = filter(data[tbl]);
        int f1 = filter(data[tbl] | 1);
        if ((f0 ^ f1) != 0) {
            data[tbl] |= f0 ^ bit;
            update_contribution_even(data, tbl);
            data[tbl] ^= in;
        } else if (f0 == bit) {
            if (__builtin_expect(end >= 1270, 0)) break;
            data[++end] = data[tbl + 1];
            data[tbl + 1] = data[tbl] | 1;
            update_contribution_even(data, tbl);
            data[tbl++] ^= in;
            update_contribution_even(data, tbl);
            data[tbl] ^= in;
        } else {
            data[tbl--] = data[end--];
        }
    }
    return end;
}

// Scalar recovery - needed for nested attacks
// Return codes: >0 = states checked, -1 = key found, -2 = aborted
static int old_recover(
    unsigned int odd[],
    int o_head,
    int o_tail,
    int oks,
    unsigned int even[],
    int e_head,
    int e_tail,
    int eks,
    int rem,
    int s,
    MfClassicNonce *n,
    unsigned int in,
    int first_run)
{
    int o, e, i;
    if (rem == -1) {
        int check_counter = 0;
        for (e = e_head; e <= e_tail; ++e) {
            even[e] = (even[e] << 1) ^ evenparity32(even[e] & LF_POLY_EVEN) ^ (!!(in & 4));
            for (o = o_head; o <= o_tail; ++o, ++s) {
                // Check abort flag every 1024 iterations (power-of-2 for single-cycle & op)
                if ((check_counter++ & 1023) == 0) {
                    if (g_abort_attack) return -2;
                }
                struct Crypto1State temp = {0, 0};
                temp.even = odd[o];
                temp.odd = even[e] ^ evenparity32(odd[o] & LF_POLY_ODD);
                if (check_state(&temp, n)) {
                    return -1;
                }
            }
        }
        return s;
    }

    if (first_run == 0) {
        for (i = 0; (i < 4) && (rem-- != 0); i++) {
            oks >>= 1;
            eks >>= 1;
            in >>= 2;
            o_tail = extend_table_odd(odd, o_head, o_tail, oks & 1);
            if (o_head > o_tail)
                return s;
            e_tail = extend_table_even(even, e_head, e_tail, eks & 1, in & 3);
            if (e_head > e_tail)
                return s;
        }
    }

    first_run = 0;
    radix_sort_32(odd, o_head, o_tail, g_radix_temp);
    radix_sort_32(even, e_head, e_tail, g_radix_temp);

    while (o_tail >= o_head && e_tail >= e_head) {
        if (((odd[o_tail] ^ even[e_tail]) >> 24) == 0) {
            o_tail = binsearch(odd, o_head, o = o_tail);
            e_tail = binsearch(even, e_head, e = e_tail);
            s = old_recover(
                odd, o_tail--, o, oks,
                even, e_tail--, e, eks,
                rem, s, n, in, first_run);
            if (s < 0) {  // -1 = found, -2 = aborted
                break;
            }
        } else if ((odd[o_tail] ^ 0x80000000) > (even[e_tail] ^ 0x80000000)) {
            o_tail = binsearch(odd, o_head, o_tail) - 1;
        } else {
            e_tail = binsearch(even, e_head, e_tail) - 1;
        }
    }
    return s;
}

// 32-way parallel verification using bitsliced LFSR
// Return codes: >0 = states checked, -1 = key found, -2 = aborted
static int old_recover_bs(
    unsigned int odd[],
    int o_head,
    int o_tail,
    int oks,
    unsigned int even[],
    int e_head,
    int e_tail,
    int eks,
    int rem,
    int s,
    MfClassicNonce *n,
    unsigned int in,
    int first_run)
{
    int o, e, i;

    // Base case: rem == -1, use batched verification
    if (rem == -1) {
        BsCandidateBatch batch;
        bs_batch_init(&batch);

        for (e = e_head; e <= e_tail; ++e) {
            uint32_t e_val = (even[e] << 1) ^ evenparity32(even[e] & LF_POLY_EVEN) ^ (!!(in & 4));

            for (o = o_head; o <= o_tail; ++o, ++s) {
                uint32_t o_val = odd[o];
                uint32_t final_even = o_val;
                uint32_t final_odd = e_val ^ evenparity32(o_val & LF_POLY_ODD);

                if (bs_batch_add(&batch, final_odd, final_even)) {
                    uint32_t valid = bs_verify_batch_32(&batch, n);
                    if (valid) {
                        int lane = __builtin_ctz(valid);
                        bs_extract_key(&batch, lane, n);
                        return -1;
                    }
                    // Check abort after each batch (32 candidates verified)
                    if (g_abort_attack) return -2;
                    bs_batch_init(&batch);
                }
            }
        }

        // Verify remaining partial batch
        if (batch.count > 0) {
            uint32_t valid = bs_verify_batch_32(&batch, n);
            if (valid) {
                int lane = __builtin_ctz(valid);
                bs_extract_key(&batch, lane, n);
                return -1;
            }
        }

        return s;
    }

    // Recursion: same as scalar old_recover
    if (first_run == 0) {
        for (i = 0; (i < 4) && (rem-- != 0); i++) {
            oks >>= 1;
            eks >>= 1;
            in >>= 2;
            o_tail = extend_table_odd(odd, o_head, o_tail, oks & 1);
            if (o_head > o_tail)
                return s;
            e_tail = extend_table_even(even, e_head, e_tail, eks & 1, in & 3);
            if (e_head > e_tail)
                return s;
        }
    }

    first_run = 0;
    radix_sort_32(odd, o_head, o_tail, g_radix_temp);
    radix_sort_32(even, e_head, e_tail, g_radix_temp);

    while (o_tail >= o_head && e_tail >= e_head) {
        if (((odd[o_tail] ^ even[e_tail]) >> 24) == 0) {
            o_tail = binsearch(odd, o_head, o = o_tail);
            e_tail = binsearch(even, e_head, e = e_tail);
            s = old_recover_bs(
                odd, o_tail--, o, oks,
                even, e_tail--, e, eks,
                rem, s, n, in, first_run);
            if (s < 0) {  // -1 = found, -2 = aborted
                break;
            }
        } else if ((odd[o_tail] ^ 0x80000000) > (even[e_tail] ^ 0x80000000)) {
            o_tail = binsearch(odd, o_head, o_tail) - 1;
        } else {
            e_tail = binsearch(even, e_head, e_tail) - 1;
        }
    }
    return s;
}

// Pre-filter: check rounds 1-3 using register-only bitmask tracking.
// Returns 0 if all paths eliminated, 1 if at least one survives.
static inline __attribute__((always_inline)) int prefilter_rounds_1_3(
    uint32_t semi_state,
    int oks)
{
    // Round 1: 2 potential children -> 2-bit mask
    uint32_t v = semi_state << 1;
    int target = BIT(oks, 1);
    uint32_t fp = filter_pair(v);
    int f0 = FILTER_F0(fp);
    int f1 = FILTER_F1(fp);

    // r1_valid: bit 0 = v survives, bit 1 = v|1 survives
    int r1_valid = ((f0 == target) << 0) | ((f1 == target) << 1);
    if (!r1_valid) return 0;

    // Round 2: up to 4 grandchildren -> 4-bit mask
    // Tracks exactly which grandchildren survive
    target = BIT(oks, 2);
    int r2_valid = 0;

    if (r1_valid & 1) {  // v survived R1
        fp = filter_pair(v << 1);
        f0 = FILTER_F0(fp);
        f1 = FILTER_F1(fp);
        if (f0 == target) r2_valid |= 1;  // v<<1 survives
        if (f1 == target) r2_valid |= 2;  // (v<<1)|1 survives
    }
    if (r1_valid & 2) {  // v|1 survived R1
        fp = filter_pair((v | 1) << 1);
        f0 = FILTER_F0(fp);
        f1 = FILTER_F1(fp);
        if (f0 == target) r2_valid |= 4;  // (v|1)<<1 survives
        if (f1 == target) r2_valid |= 8;  // ((v|1)<<1)|1 survives
    }

    if (!r2_valid) return 0;

    // Round 3: only check children of actual R2 survivors
    target = BIT(oks, 3);

    if (r2_valid & 1) {  // v<<1 survived R2
        fp = filter_pair(v << 2);
        f0 = FILTER_F0(fp);
        f1 = FILTER_F1(fp);
        if (f0 == target || f1 == target) return 1;
    }
    if (r2_valid & 2) {  // (v<<1)|1 survived R2
        fp = filter_pair((v << 2) | 2);
        f0 = FILTER_F0(fp);
        f1 = FILTER_F1(fp);
        if (f0 == target || f1 == target) return 1;
    }
    if (r2_valid & 4) {  // (v|1)<<1 survived R2
        fp = filter_pair((v | 1) << 2);
        f0 = FILTER_F0(fp);
        f1 = FILTER_F1(fp);
        if (f0 == target || f1 == target) return 1;
    }
    if (r2_valid & 8) {  // ((v|1)<<1)|1 survived R2
        fp = filter_pair(((v | 1) << 2) | 2);
        f0 = FILTER_F0(fp);
        f1 = FILTER_F1(fp);
        if (f0 == target || f1 == target) return 1;
    }

    return 0;
}

// 8x unrolled duplicate scan using Duff's Device
static inline __attribute__((always_inline)) bool scan_for_duplicate_8x(
    const uint8_t *states,  // Packed 24-bit state array
    int count,              // Number of entries to scan
    uint32_t state_masked)  // Target state with MSB masked off (& 0x00FFFFFF)
{
    if (count <= 0) return false;

    const uint8_t *p = states;
    int n = (count + 7) / 8;  // Number of 8-iteration chunks (rounded up)

    // Duff's Device: jump into unrolled loop based on remainder
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

// Main attack loop - processes one MSB bucket
int calculate_msb_tables_optimized(
    int oks,
    int eks,
    int msb_round,
    MfClassicNonce *n,
    unsigned int *states_buffer,
    struct Msb *odd_msbs,
    struct Msb *even_msbs,
    unsigned int *temp_states_odd,
    unsigned int *temp_states_even,
    unsigned int in,
    ProgramState *program_state)
{
    // Set global state for hot-path functions (avoids passing through recursion)
    g_program_state = program_state;
    g_abort_attack = false;

    unsigned int msb_head = (MSB_LIMIT * msb_round);
    unsigned int msb_tail = (MSB_LIMIT * (msb_round + 1));
    int states_tail = 0;
    int semi_state = 0;
    unsigned int msb = 0;

    // Preprocessed in value
    in = ((in >> 16 & 0xff) | (in << 16) | (in & 0xff00)) << 1;

    memset(odd_msbs, 0, MSB_LIMIT * sizeof(struct Msb));
    memset(even_msbs, 0, MSB_LIMIT * sizeof(struct Msb));

    // Bloom filter for deduplication (reuse temp_states buffers as scratch)
    uint32_t* odd_msb_filters = (uint32_t*)temp_states_odd;
    uint32_t* even_msb_filters = (uint32_t*)temp_states_even;
    memset(temp_states_odd, 0, 1024 * sizeof(unsigned int));
    memset(temp_states_even, 0, 1024 * sizeof(unsigned int));

    int oks_bit = oks & 1;
    int eks_bit = eks & 1;

    // Check for stop request interval
    int sync_check_interval = 65536;

    // Iterate all 2^20 semi-states and expand via state_loop
    for (semi_state = 1 << 20; semi_state >= 0; semi_state--) {
        if (semi_state % sync_check_interval == 0) {
            if (sync_state(program_state) == 1) {
                return 0;
            }
        }

        int filter_semi_state = filter(semi_state);

        // Check oks condition
        if (filter_semi_state == oks_bit) {
            // Extended pre-filter: check rounds 1-3 using register-only bitmask
            if (!prefilter_rounds_1_3(semi_state, oks)) continue;

            states_buffer[0] = semi_state;
            states_tail = state_loop(states_buffer, oks, CONST_M1_1, CONST_M2_1, 0, 0);

            for (int i = states_tail; i >= 0; i--) {
                msb = states_buffer[i] >> 24;
                if ((msb >= msb_head) && (msb < msb_tail)) {
                    int msb_idx = msb - msb_head;
                    uint32_t state = states_buffer[i];

                    uint32_t fingerprint = (state * 2654435769u) >> 21;
                    uint32_t filter_idx = (msb_idx << 6) | (fingerprint >> 5);
                    uint32_t mask = 1U << (fingerprint & 31);

                    bool already_exists = false;
                    if (odd_msb_filters[filter_idx] & mask) {
                        already_exists = scan_for_duplicate_8x(
                            odd_msbs[msb_idx].states,
                            odd_msbs[msb_idx].tail,
                            state & 0x00FFFFFF);
                    }

                    if (!already_exists && odd_msbs[msb_idx].tail < MSB_BUCKET_CAPACITY) {
                        odd_msb_filters[filter_idx] |= mask;
                        int tail = odd_msbs[msb_idx].tail++;
                        memcpy(&odd_msbs[msb_idx].states[tail * 3], &state, 3);
                    }
                }
            }
        }

        // Check eks condition
        if (filter_semi_state == eks_bit) {
            // Extended pre-filter: check rounds 1-3 using register-only bitmask
            if (!prefilter_rounds_1_3(semi_state, eks)) continue;

            states_buffer[0] = semi_state;
            states_tail = state_loop(states_buffer, eks, CONST_M1_2, CONST_M2_2, in, 3);

            for (int i = 0; i <= states_tail; i++) {
                msb = states_buffer[i] >> 24;
                if ((msb >= msb_head) && (msb < msb_tail)) {
                    int msb_idx = msb - msb_head;
                    uint32_t state = states_buffer[i];

                    uint32_t fingerprint = (state * 2654435769u) >> 21;
                    uint32_t filter_idx = (msb_idx << 6) | (fingerprint >> 5);
                    uint32_t mask = 1U << (fingerprint & 31);

                    bool already_exists = false;
                    if (even_msb_filters[filter_idx] & mask) {
                        already_exists = scan_for_duplicate_8x(
                            even_msbs[msb_idx].states,
                            even_msbs[msb_idx].tail,
                            state & 0x00FFFFFF);
                    }

                    if (!already_exists && even_msbs[msb_idx].tail < MSB_BUCKET_CAPACITY) {
                        even_msb_filters[filter_idx] |= mask;
                        int tail = even_msbs[msb_idx].tail++;
                        memcpy(&even_msbs[msb_idx].states[tail * 3], &state, 3);
                    }
                }
            }
        }
    }

    oks >>= 12;
    eks >>= 12;

    for (int i = 0; i < MSB_LIMIT; i++) {
        // Update abort flag from UI state (sync every 4 iterations)
        if ((i % 4) == 0) {
            if (sync_state(program_state) == 1) {
                g_abort_attack = true;
                return 0;
            }
        }

        if (odd_msbs[i].tail > 0 || even_msbs[i].tail > 0) {
            // Reconstruct full 32-bit states from packed 24-bit storage
            uint32_t current_msb_val = (uint32_t)(msb_head + i) << 24;

            for (int k = 0; k < odd_msbs[i].tail; k++) {
                uint32_t raw = 0;
                memcpy(&raw, &odd_msbs[i].states[k * 3], 3);
                temp_states_odd[k] = raw | current_msb_val;
            }

            for (int k = 0; k < even_msbs[i].tail; k++) {
                uint32_t raw = 0;
                memcpy(&raw, &even_msbs[i].states[k * 3], 3);
                temp_states_even[k] = raw | current_msb_val;
            }

            // Use bitsliced verification for mfkey32 attacks
            // Nested attacks require scalar check_state() for correct verification
            int res;
            if (n->attack == mfkey32) {
                res = old_recover_bs(
                    temp_states_odd, 0, odd_msbs[i].tail - 1, oks,
                    temp_states_even, 0, even_msbs[i].tail - 1, eks,
                    3, 0, n, in >> 16, 1);
            } else {
                res = old_recover(
                    temp_states_odd, 0, odd_msbs[i].tail - 1, oks,
                    temp_states_even, 0, even_msbs[i].tail - 1, eks,
                    3, 0, n, in >> 16, 1);
            }

            if (res == -1) {
                return 1;  // Key found
            } else if (res == -2) {
                return 0;  // User aborted
            }
        }
    }

    return 0;
}
