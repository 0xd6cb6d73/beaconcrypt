// SPDX-License-Identifier: 0BSD

#ifndef BEACONCRYPT_GO_H
#define BEACONCRYPT_GO_H

#include "bindings.h"

typedef beaconcrypt_Buffer beaconcrypt_buffer;
typedef beaconcrypt_RegistrationResponse beaconcrypt_registration_response;
typedef beaconcrypt_EncryptState beaconcrypt_encrypt_state;

// Construct callback structs in C so the integer token is never exposed to Go
// as the void pointer that the native callback ABI uses for its context.
beaconcrypt_Server *beaconcrypt_go_server_create_with_store(uint64_t server_kid, const uint8_t *seed, uintptr_t seed_len, uintptr_t token, uint32_t *status_out);
beaconcrypt_Server *beaconcrypt_go_server_create_with_store_and_lineage(uint64_t server_kid, const uint8_t *seed, uintptr_t seed_len, uintptr_t token, const uint8_t *lineage, uintptr_t lineage_len, uint32_t *status_out);
beaconcrypt_Server *beaconcrypt_go_server_restore_with_store(uintptr_t token, uint32_t *status_out);
void beaconcrypt_go_deliver_snapshot(void *delivery, const uint8_t *bytes, uintptr_t len);

// C.CBytes owns exactly len bytes. Volatile stores preserve the wipe before free.
static inline void beaconcrypt_wipe_free(void *ptr, uintptr_t len) {
	volatile uint8_t *bytes = (volatile uint8_t *)ptr;
	for (uintptr_t i = 0; i < len; i++) bytes[i] = 0;
	free(ptr);
}

#endif
