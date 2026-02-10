#ifndef MFKEY_ATTACK_H
#define MFKEY_ATTACK_H

#include "mfkey.h"

/* Run attack for one MSB round. Returns 1 if key found. */
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
    ProgramState *program_state);

#endif // MFKEY_ATTACK_H
