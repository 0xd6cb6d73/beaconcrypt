// SPDX-License-Identifier: 0BSD
#ifndef BEACONCRYPT_ROW_GO_H
#define BEACONCRYPT_ROW_GO_H
#include "beaconcrypt_go.h"

beaconcrypt_RowServerHandle *beaconcrypt_go_row_create(uint64_t kid, const uint8_t *seed, uintptr_t seed_len, const uint8_t *mldsa, uintptr_t mldsa_len, uintptr_t token, const uint8_t *lineage, uint32_t *status);
beaconcrypt_RowServerHandle *beaconcrypt_go_row_open(uintptr_t token, const uint8_t *lineage, uint32_t *status);
void beaconcrypt_go_deliver_row(void *delivery, const uint8_t *bytes, uintptr_t len);

beaconcrypt_Buffer beaconcrypt_go_row_transaction(beaconcrypt_RowServerHandle *server, uintptr_t token);
beaconcrypt_Buffer beaconcrypt_go_row_registration_transaction(beaconcrypt_RowServerHandle *server, uintptr_t token, uint32_t *phase);

#endif
