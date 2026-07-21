#ifndef _BEACON_CRYPT_H_
#define _BEACON_CRYPT_H_

/* Generated with cbindgen:0.29.4 */

// Do not modify manually.

#include <stdarg.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdlib.h>

#define beaconcrypt_KEX_KDF_OUT_LEN 32

#define beaconcrypt_KDF_STATE_SIZE 32

/**
 * crypto_aead::chacha20poly1305_ietf::KEYBYTES
 */
#define beaconcrypt_AEAD_KEY_LEN 32

/**
 * crypto_aead::chacha20poly1305_ietf::NPUBBYTES
 */
#define beaconcrypt_AEAD_NONCE_LEN 12

#define beaconcrypt_KDF_RATCHET_OUTPUT_LEN ((beaconcrypt_AEAD_KEY_LEN + beaconcrypt_KDF_STATE_SIZE) + beaconcrypt_AEAD_NONCE_LEN)

/**
 * crypto_scalarmult::BYTES
 */
#define beaconcrypt_DH_OUT_LEN 32

#define beaconcrypt_RATCHET_MAX_GAP 50

#define beaconcrypt_ED25519_SEED_SIZE 32

#define beaconcrypt_COMMITMENT_SIZE 64

typedef struct beaconcrypt_BeaconCryptPqxdh beaconcrypt_BeaconCryptPqxdh;

typedef struct beaconcrypt_Buffer {
  uint8_t *ptr;
  uintptr_t len;
  uintptr_t cap;
} beaconcrypt_Buffer;

typedef struct beaconcrypt_RegistrationResponse {
  struct beaconcrypt_Buffer response;
  struct beaconcrypt_Buffer beacon_pk;
  uint64_t key_id;
} beaconcrypt_RegistrationResponse;

typedef struct beaconcrypt_EncryptState {
  struct beaconcrypt_Buffer data;
  struct beaconcrypt_Buffer key;
  uint64_t key_id;
} beaconcrypt_EncryptState;

#ifdef __cplusplus
extern "C" {
#endif // __cplusplus

void beaconcrypt_free_buffer(struct beaconcrypt_Buffer buffer);

struct beaconcrypt_BeaconCryptPqxdh *beaconcrypt_server_new(uint64_t server_kid);

struct beaconcrypt_BeaconCryptPqxdh *beaconcrypt_server_new_from_seed(uint64_t server_kid,
                                                                      const uint8_t *seed_ptr,
                                                                      uintptr_t seed_len);

struct beaconcrypt_BeaconCryptPqxdh *beaconcrypt_beacon_new(uint64_t server_kid,
                                                            const uint8_t *server_pk_ptr,
                                                            uintptr_t server_pk_len);

void beaconcrypt_free(struct beaconcrypt_BeaconCryptPqxdh *handle);

struct beaconcrypt_Buffer beaconcrypt_identity_pk(const struct beaconcrypt_BeaconCryptPqxdh *handle);

struct beaconcrypt_Buffer beaconcrypt_generate_registration(struct beaconcrypt_BeaconCryptPqxdh *handle);

struct beaconcrypt_RegistrationResponse beaconcrypt_register_beacon(struct beaconcrypt_BeaconCryptPqxdh *handle,
                                                                    const uint8_t *reg_ptr,
                                                                    uintptr_t reg_len,
                                                                    const uint8_t *msg_ptr,
                                                                    uintptr_t msg_len);

struct beaconcrypt_Buffer beaconcrypt_process_initial_message(struct beaconcrypt_BeaconCryptPqxdh *handle,
                                                              const uint8_t *ptr,
                                                              uintptr_t len);

struct beaconcrypt_Buffer beaconcrypt_encrypt_to_beacon(struct beaconcrypt_BeaconCryptPqxdh *handle,
                                                        uint64_t key_id,
                                                        const uint8_t *ptr,
                                                        uintptr_t len);

struct beaconcrypt_Buffer beaconcrypt_encrypt_to_beacon_signed(struct beaconcrypt_BeaconCryptPqxdh *handle,
                                                               uint64_t key_id,
                                                               const uint8_t *ptr,
                                                               uintptr_t len);

struct beaconcrypt_Buffer beaconcrypt_decrypt_beacon_message(struct beaconcrypt_BeaconCryptPqxdh *handle,
                                                             uint64_t key_id,
                                                             const uint8_t *ptr,
                                                             uintptr_t len);

struct beaconcrypt_Buffer beaconcrypt_decrypt_beacon_message_signed(struct beaconcrypt_BeaconCryptPqxdh *handle,
                                                                    const uint8_t *ptr,
                                                                    uintptr_t len);

struct beaconcrypt_EncryptState beaconcrypt_encrypt_and_update(struct beaconcrypt_BeaconCryptPqxdh *handle,
                                                               uint64_t key_id,
                                                               const uint8_t *ptr,
                                                               uintptr_t len);

struct beaconcrypt_EncryptState beaconcrypt_decrypt_and_update(struct beaconcrypt_BeaconCryptPqxdh *handle,
                                                               uint64_t key_id,
                                                               const uint8_t *ptr,
                                                               uintptr_t len);

struct beaconcrypt_Buffer beaconcrypt_encrypt_to_server(struct beaconcrypt_BeaconCryptPqxdh *handle,
                                                        const uint8_t *ptr,
                                                        uintptr_t len);

struct beaconcrypt_Buffer beaconcrypt_encrypt_to_server_signed(struct beaconcrypt_BeaconCryptPqxdh *handle,
                                                               const uint8_t *ptr,
                                                               uintptr_t len);

struct beaconcrypt_Buffer beaconcrypt_decrypt_server_message(struct beaconcrypt_BeaconCryptPqxdh *handle,
                                                             const uint8_t *ptr,
                                                             uintptr_t len);

struct beaconcrypt_Buffer beaconcrypt_decrypt_server_message_signed(struct beaconcrypt_BeaconCryptPqxdh *handle,
                                                                    const uint8_t *ptr,
                                                                    uintptr_t len);

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  /* _BEACON_CRYPT_H_ */
