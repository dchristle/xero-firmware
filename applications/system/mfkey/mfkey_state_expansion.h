#ifndef MFKEY_STATE_EXPANSION_H
#define MFKEY_STATE_EXPANSION_H

#include <stdint.h>

// Optimized state expansion for rounds 4-12 starting from precomputed state
// Used after batch prelude completes rounds 0-3
// Returns final state count (states_tail), or -1 if all eliminated
int state_loop_r4(
    unsigned int *states_buffer,
    int count,
    int xks,
    int m1,
    int m2,
    unsigned int in,
    int and_val);

#endif // MFKEY_STATE_EXPANSION_H
