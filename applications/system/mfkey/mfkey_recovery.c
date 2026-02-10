#pragma GCC optimize("O3")

#include "mfkey_recovery.h"
#include "crypto1.h"
#include "mfkey_bs_verify.h"
#include <string.h>

extern int sync_state(ProgramState *program_state);
extern void flush_key_buffer(ProgramState *program_state);
extern uint8_t MSB_LIMIT;
extern volatile bool g_abort_attack;
extern ProgramState *g_program_state;
int check_state(struct Crypto1State *t, MfClassicNonce *n) {
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

#define RADIX_BITS 8
#define RADIX_SIZE (1 << RADIX_BITS)
#define RADIX_MASK (RADIX_SIZE - 1)

unsigned int g_radix_temp[1280];

void radix_sort_32(unsigned int* arr, int low, int high, unsigned int* temp) {
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

    if (count > 1280) {
        count = 1280;
        high = low + count - 1;
    }

    unsigned int hist[RADIX_SIZE];
    unsigned int* src = arr + low;
    unsigned int* dst = temp;

    for (int pass = 0; pass < 4; pass++) {
        int shift = pass * RADIX_BITS;
        memset(hist, 0, sizeof(hist));
        for (int i = 0; i < count; i++) {
            hist[(src[i] >> shift) & RADIX_MASK]++;
        }
        unsigned int total = 0;
        for (int i = 0; i < RADIX_SIZE; i++) {
            unsigned int c = hist[i];
            hist[i] = total;
            total += c;
        }
        for (int i = 0; i < count; i++) {
            int bucket = (src[i] >> shift) & RADIX_MASK;
            dst[hist[bucket]++] = src[i];
        }
        unsigned int* t = src;
        src = dst;
        dst = t;
    }
}

static inline __attribute__((always_inline)) void update_contribution_odd(unsigned int data[], int item) {
    unsigned int val = data[item];
    unsigned int p = val >> 25;
    p = p << 1 | evenparity32(val & CONST_M1_1);
    p = p << 1 | evenparity32(val & CONST_M2_1);
    data[item] = (p << 24) | (val & 0xffffff);
}

static inline __attribute__((always_inline)) void update_contribution_even(unsigned int data[], int item) {
    unsigned int val = data[item];
    unsigned int p = val >> 25;
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

/* Scalar candidate verification */
int old_recover(
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
            if (s < 0) {
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

/* 32-way bitsliced candidate verification */
int old_recover_bs(
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
                    if (g_abort_attack) return -2;
                    bs_batch_init(&batch);
                }
            }
        }

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
            if (s < 0) {
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
