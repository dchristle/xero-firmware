#pragma GCC optimize("O3")

#include <stdlib.h>
#include <string.h>

#include <furi.h>
#include "mfkey_attack.h"

#include "crypto1.h"
#include "mfkey_bs_verify.h"
#include "mfkey_dedup.h"
#include "mfkey_state_expansion.h"
#include "mfkey_recovery.h"
#include "mfkey_batch_prelude.h"

volatile bool g_abort_attack = false;
ProgramState *g_program_state = NULL;

extern int sync_state(ProgramState *program_state);
extern void flush_key_buffer(ProgramState *program_state);
extern uint8_t MSB_LIMIT;

#define SWAP(a, b) do { unsigned int t = a; a = b; b = t; } while (0)

/*
 * R4 lane elimination masks, indexed by [shared][target_bit].
 * Precomputed from filter() over 16 lanes per half-batch.
 */

static const uint16_t R4_LANE_MASK[8][2] = {
    /* shared=0 */ {0xFFFF, 0x26C7},
    /* shared=1 */ {0xD938, 0x26C7},
    /* shared=2 */ {0xFFFF, 0xFFFF},
    /* shared=3 */ {0x26C7, 0xFFFF},
    /* shared=4 */ {0xFFFF, 0x26C7},
    /* shared=5 */ {0x26C7, 0xD938},
    /* shared=6 */ {0x26C7, 0xFFFF},
    /* shared=7 */ {0x26C7, 0xD938},
};

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
    g_program_state = program_state;
    g_abort_attack = false;

    unsigned int msb_head = (MSB_LIMIT * msb_round);
    unsigned int msb_tail = (MSB_LIMIT * (msb_round + 1));

    int states_tail = 0;
    unsigned int msb = 0;

    in = ((in >> 16 & 0xff) | (in << 16) | (in & 0xff00)) << 1;

    memset(odd_msbs, 0, MSB_LIMIT * sizeof(struct Msb));
    memset(even_msbs, 0, MSB_LIMIT * sizeof(struct Msb));

    /* Bloom-style dedup using idle temp_states buffers as bitmask scratch */
    #define DISABLE_IDENTITY_FILTER 0
    #if !DISABLE_IDENTITY_FILTER
    uint32_t* odd_msb_filters = (uint32_t*)temp_states_odd;
    uint32_t* even_msb_filters = (uint32_t*)temp_states_even;
    memset(temp_states_odd, 0, 1024 * sizeof(unsigned int));
    memset(temp_states_even, 0, 1024 * sizeof(unsigned int));
    #endif

    for (int batch_base = (1 << 20) & ~31; batch_base >= 0; batch_base -= 32) {
        OPT_BARRIER(oks);
        OPT_BARRIER(eks);

        if ((batch_base & 0xFFE0) == 0) {
            if (sync_state(program_state) == 1) {
                return 0;
            }
        }

        /* Precompute R4 lane masks (batch-invariant) */
        uint32_t nib_bit_r4 = (0x0d938 >> ((batch_base >> 12) & 0xF)) & 1;
        uint32_t l2_base_r4 = (batch_base >> 4) & 0xFE;
        uint32_t shared_lo_r4 = lookup2[l2_base_r4] | nib_bit_r4;
        uint32_t shared_hi_r4 = lookup2[l2_base_r4 | 1] | nib_bit_r4;
        uint32_t r4_mask_oks = (uint32_t)R4_LANE_MASK[shared_lo_r4][BIT(oks, 4)] |
                               ((uint32_t)R4_LANE_MASK[shared_hi_r4][BIT(oks, 4)] << 16);
        uint32_t r4_mask_eks = (uint32_t)R4_LANE_MASK[shared_lo_r4][BIT(eks, 4)] |
                               ((uint32_t)R4_LANE_MASK[shared_hi_r4][BIT(eks, 4)] << 16);

        /* OKS */
        uint32_t oks_leaf_masks[8];
        uint32_t valid_oks = batch_prelude_unified(batch_base, oks, r4_mask_oks, oks_leaf_masks);

        if (valid_oks) {
            uint32_t node_base = (batch_base << 3);
            uint32_t active = valid_oks;
            while (active) {
                int lane = __builtin_ctz(active);
                active &= active - 1;

                uint32_t lane_bit = 1u << lane;
                uint32_t base_state = node_base | (lane << 3);
                int count = 0;
                for (int c = 0; c < 8; c++)
                    if (oks_leaf_masks[c] & lane_bit)
                        states_buffer[count++] = base_state | c;

                if (count > 0) {
                    states_tail = state_loop_r4(states_buffer, count, oks, CONST_M1_1, CONST_M2_1, 0, 0);

                    for (int i = states_tail; i >= 0; i--) {
                        msb = states_buffer[i] >> 24;
                        if ((msb >= msb_head) && (msb < msb_tail)) {
                            int msb_idx = msb - msb_head;
                            uint32_t state = states_buffer[i];

                            #if DISABLE_IDENTITY_FILTER
                            if (odd_msbs[msb_idx].tail < MSB_BUCKET_CAPACITY) {
                                int tail = odd_msbs[msb_idx].tail++;
                                memcpy(&odd_msbs[msb_idx].states[tail * 3], &state, 3);
                            }
                            #else
                            uint32_t fingerprint = FIB_HASH_20BIT(state);
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
                            #endif
                        }
                    }
                }
            }
        }

        /* EKS */
        uint32_t eks_leaf_masks[8];
        uint32_t valid_eks = batch_prelude_unified(batch_base, eks, r4_mask_eks, eks_leaf_masks);

        if (valid_eks) {
            uint32_t node_base = (batch_base << 3);
            uint32_t active = valid_eks;
            while (active) {
                int lane = __builtin_ctz(active);
                active &= active - 1;

                uint32_t lane_bit = 1u << lane;
                uint32_t base_state = node_base | (lane << 3);
                int count = 0;
                for (int c = 0; c < 8; c++)
                    if (eks_leaf_masks[c] & lane_bit)
                        states_buffer[count++] = base_state | c;

                if (count > 0) {
                    states_tail = state_loop_r4(states_buffer, count, eks, CONST_M1_2, CONST_M2_2, in, 3);

                    for (int i = 0; i <= states_tail; i++) {
                        msb = states_buffer[i] >> 24;
                        if ((msb >= msb_head) && (msb < msb_tail)) {
                            int msb_idx = msb - msb_head;
                            uint32_t state = states_buffer[i];

                            #if DISABLE_IDENTITY_FILTER
                            if (even_msbs[msb_idx].tail < MSB_BUCKET_CAPACITY) {
                                int tail = even_msbs[msb_idx].tail++;
                                memcpy(&even_msbs[msb_idx].states[tail * 3], &state, 3);
                            }
                            #else
                            uint32_t fingerprint = FIB_HASH_20BIT(state);
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
                            #endif
                        }
                    }
                }
            }
        }
    }

    oks >>= 12;
    eks >>= 12;

    /* Verification: merge odd/even buckets and recover candidates */
    for (int i = 0; i < MSB_LIMIT; i++) {
        if ((i % 4) == 0) {
            if (sync_state(program_state) == 1) {
                g_abort_attack = true;
                return 0;
            }
        }

        if (odd_msbs[i].tail > 0 || even_msbs[i].tail > 0) {
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
