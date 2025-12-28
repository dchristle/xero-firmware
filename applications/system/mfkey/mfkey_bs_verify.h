#ifndef MFKEY_BS_VERIFY_H
#define MFKEY_BS_VERIFY_H

// 32-way parallel LFSR verification using SWAR (SIMD Within A Register)

#include "mfkey.h"
#include <stdint.h>
#include <stdbool.h>

#define BS_BATCH_SIZE 32

typedef struct {
    uint32_t odd[BS_BATCH_SIZE];
    uint32_t even[BS_BATCH_SIZE];
    int count;
} BsCandidateBatch;

typedef struct {
    uint32_t odd[72];   // 24 LFSR bits mirrored 3x for runway
    uint32_t even[72];
    uint32_t odd_head;
    uint32_t even_head;
} Crypto1BitSlice;

static inline void bs_batch_init(BsCandidateBatch* batch) {
    batch->count = 0;
}

static inline bool bs_batch_add(BsCandidateBatch* batch, uint32_t odd, uint32_t even) {
    if (batch->count < BS_BATCH_SIZE) {
        batch->odd[batch->count] = odd;
        batch->even[batch->count] = even;
        batch->count++;
    }
    return batch->count >= BS_BATCH_SIZE;
}

uint32_t bs_verify_batch_32(
    const BsCandidateBatch* batch,
    MfClassicNonce* nonce);

void bs_extract_key(
    const BsCandidateBatch* batch,
    int lane,
    MfClassicNonce* nonce);

#endif // MFKEY_BS_VERIFY_H
