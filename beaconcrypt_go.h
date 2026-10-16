// SPDX-License-Identifier: 0BSD

#ifndef BEACONCRYPT_GO_H
#define BEACONCRYPT_GO_H

#include "bindings.h"

typedef beaconcrypt_Buffer beaconcrypt_buffer;
typedef beaconcrypt_RegistrationResponse beaconcrypt_registration_response;
typedef beaconcrypt_EncryptState beaconcrypt_encrypt_state;

beaconcrypt_SnapshotStoreCallbacks beaconcrypt_go_store_callbacks(uintptr_t handle);
void beaconcrypt_go_deliver_snapshot(void *delivery, const uint8_t *bytes, uintptr_t len);

// C.CBytes owns exactly len bytes. Volatile stores preserve the wipe before free.
static inline void beaconcrypt_wipe_free(void *ptr, uintptr_t len) {
	volatile uint8_t *bytes = (volatile uint8_t *)ptr;
	for (uintptr_t i = 0; i < len; i++) bytes[i] = 0;
	free(ptr);
}

#endif
