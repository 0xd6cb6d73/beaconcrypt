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

typedef struct beaconcrypt_BeaconCryptPqxdh beaconcrypt_BeaconCryptPqxdh;

typedef struct beaconcrypt_GoBuffer {
  uint8_t *ptr;
  uintptr_t len;
  uintptr_t cap;
} beaconcrypt_GoBuffer;

typedef struct beaconcrypt_GoRegistrationResponse {
  struct beaconcrypt_GoBuffer response;
  struct beaconcrypt_GoBuffer beacon_pk;
  uint64_t key_id;
} beaconcrypt_GoRegistrationResponse;

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

#ifdef __cplusplus
extern "C" {
#endif // __cplusplus

/**
 * # Safety
 * * `bytes` should NOT be null and should point to a byte buffer of `bytes_len` length, in bytes.
 * * The library will overwrite all the `out` parameters
 * * It is not safe to read the `out` parameters if the function doesn't return `0`
 */
int32_t process_initial_message(const uint8_t *bytes,
                                uintptr_t bytes_len,
                                uint8_t **_out,
                                uintptr_t *out_len,
                                uintptr_t *out_capa);

/**
 * # Safety
 * * `bytes` should NOT be null and should point to a byte buffer of `bytes_len` length, in bytes.
 * * The library will overwrite all the `out` parameters
 * * It is not safe to read the `out` parameters if the function doesn't return `0`
 */
int32_t process_initial_message_signed(const uint8_t *bytes,
                                       uintptr_t bytes_len,
                                       uint8_t **_out,
                                       uintptr_t *out_len,
                                       uintptr_t *out_capa);

/**
 * # Safety
 * * `bytes` should NOT be null and should point to a byte buffer of `bytes_len` length, in bytes.
 * * The library will overwrite all the `out` parameters
 * * It is not safe to read the `out` parameters if the function doesn't return `0`
 *
 * ## Arguments
 * * `bytes` - A serialized `cryptoframe_capnp::crypto_frame`
 * * `bytes_len` - The size of the `bytes` buffer
 * * `out` - A caller-managed pointer that will contain the results in case of success. Call `free_vec` to free it once you're done
 * * `out_len` - The actual size of the `out` buffer
 * * `out_capa` - The size of the underlying allocation for the `out` buffer
 *
 * ## Returns
 * `0` on success, negative values on error
 */
int32_t decrypt_server_message(const uint8_t *bytes,
                               uintptr_t bytes_len,
                               uint8_t **_out,
                               uintptr_t *out_len,
                               uintptr_t *out_capa);

/**
 * # Safety
 * * `bytes` should NOT be null and should point to a byte buffer of `bytes_len` length, in bytes.
 * * The library will overwrite all the `out` parameters
 * * It is not safe to read the `out` parameters if the function doesn't return `0`
 *
 * ## Arguments
 * * `bytes` - A serialized `cryptoframe_capnp::crypto_frame`
 * * `bytes_len` - The size of the `bytes` buffer
 * * `out` - A caller-managed pointer that will contain the results in case of success. Call `free_vec` to free it once you're done
 * * `out_len` - The actual size of the `out` buffer
 * * `out_capa` - The size of the underlying allocation for the `out` buffer
 *
 * ## Returns
 * `0` on success, negative values on error
 */
int32_t decrypt_server_message_signed(const uint8_t *bytes,
                                      uintptr_t bytes_len,
                                      uint8_t **_out,
                                      uintptr_t *out_len,
                                      uintptr_t *out_capa);

/**
 * # Safety
 * * `bytes` should NOT be null and should point to a byte buffer of `bytes_len` length, in bytes.
 * * The library will overwrite all the `out` parameters
 * * It is not safe to read the `out` parameters if the function doesn't return `0`
 *
 * ## Arguments
 * * `bytes` - Whatever you want to be encrypted to the server
 * * `bytes_len` - The size of the `bytes` buffer
 * * `out` - A caller-managed pointer that will contain the results in case of success. Call `free_vec` to free it once you're done
 * * `out_len` - The actual size of the `out` buffer
 * * `out_capa` - The size of the underlying allocation for the `out` buffer
 *
 * ## Returns
 * `0` on success, negative values on error
 */
int32_t encrypt_to_server(const uint8_t *bytes,
                          uintptr_t bytes_len,
                          uint8_t **_out,
                          uintptr_t *out_len,
                          uintptr_t *out_capa);

/**
 * # Safety
 * * `bytes` should NOT be null and should point to a byte buffer of `bytes_len` length, in bytes.
 * * The library will overwrite all the `out` parameters
 * * It is not safe to read the `out` parameters if the function doesn't return `0`
 *
 * ## Arguments
 * * `bytes` - Whatever you want to be encrypted to the server
 * * `bytes_len` - The size of the `bytes` buffer
 * * `out` - A caller-managed pointer that will contain the results in case of success. Call `free_vec` to free it once you're done
 * * `out_len` - The actual size of the `out` buffer
 * * `out_capa` - The size of the underlying allocation for the `out` buffer
 *
 * ## Returns
 * `0` on success, negative values on error
 */
int32_t encrypt_to_server_signed(const uint8_t *bytes,
                                 uintptr_t bytes_len,
                                 uint8_t **_out,
                                 uintptr_t *out_len,
                                 uintptr_t *out_capa);

/**
 * # Safety
 * * The library will overwrite all the `out` parameters
 * * It is not safe to read the `out` parameters if the function doesn't return `0`
 *
 * ## Arguments
 * * `bytes` - Whatever you want to be encrypted to the server
 * * `bytes_len` - The size of the `bytes` buffer
 * * `out` - A caller-managed pointer that will contain the results in case of success. Call `free_vec` to free it once you're done
 * * `out_len` - The actual size of the `out` buffer
 * * `out_capa` - The size of the underlying allocation for the `out` buffer
 *
 * ## Returns
 * `0` on success, negative values on error
 */
int32_t generate_registration(uint8_t **_out,
                              uintptr_t *out_len,
                              uintptr_t *out_capa);

/**
 * This function is safe to call multiple times. It is used to initialize beacons with a hardcoded server public key. You should always use this on beacons
 * ## Arguments
 *
 * * `is_beacon` - Whether the current instance is a beacon
 * * `server_kid` - The ID of the server's identity key for the campaign
 */
void init_for_server(bool is_beacon,
                     uint64_t server_kid,
                     const uint8_t *server_pk,
                     uint64_t server_pk_len);

/**
 * Initialize a server with existing keys from seeds. This MUST only be called by a server
 * # Safety
 * This function is safe to call multiple times.
 * ## Arguments
 *
 * * `server_kid` - The ID of the server's identity key for the campaign
 * * `id_seed` - 32 byte Ed25519 seed for the server's identity key
 */
void init_server_from_seeds(uint64_t server_kid, const uint8_t *id_seed);

/**
 * # Safety
 * * `bytes` should NOT be null and should point to a byte buffer of `bytes_len` length, in bytes.
 * * The library will overwrite all the `out` parameters
 * * It is not safe to read the `out` parameters if the function doesn't return `0`
 *
 * ## Arguments
 *
 * * `bytes` - A serialized `phase1_capnp::init_kex` from the network
 * * `bytes_len` - The size of the `bytes` buffer
 * * `data` - The contents of the initial message to send back to the agent, as bytes
 * * `data_len` - The size of the `data` buffer
 * * `out` - A caller-managed pointer that will contain the results in case of success. Call `free_vec` to free it once you're done
 * * `out_len` - The actual size of the `out` buffer
 * * `out_capa` - The size of the underlying allocation for the `out` buffer
 * ## Returns
 *
 * * i32 - Values other than 0 indicate failure
 *
 */
int32_t register_beacon(const uint8_t *bytes,
                        uintptr_t bytes_len,
                        const uint8_t *data,
                        uintptr_t data_len,
                        uint8_t **_response,
                        uintptr_t *response_len,
                        uintptr_t *response_capa,
                        uint8_t **_pk,
                        uintptr_t *pk_len,
                        uintptr_t *pk_capa,
                        uint64_t *key_id);

/**
 * This function takes a raw `cryptoframe_capnp::crypto_frame`. It needs to know the ID of the beacon that encrypted the message
 * # Safety
 * * `bytes` should NOT be null and should point to a byte buffer of `bytes_len` length, in bytes.
 * * The library will overwrite all the `out` parameters
 * * It is not safe to read the `out` parameters if the function doesn't return `0`
 *
 * ## Arguments
 * * `key_id` - The ID of the beacon to decrypt for
 * * `bytes` - A serialized `cryptoframe_capnp::crypto_frame`
 * * `bytes_len` - The size of the `bytes` buffer
 * * `out` - A caller-managed pointer that will contain the results in case of success. Call `free_vec` to free it once you're done
 * * `out_len` - The actual size of the `out` buffer
 * * `out_capa` - The size of the underlying allocation for the `out` buffer
 *
 * ## Returns
 * `0` on success, negative values on error
 */
int32_t decrypt_beacon_message(uint64_t key_id,
                               const uint8_t *bytes,
                               uintptr_t bytes_len,
                               uint8_t **_out,
                               uintptr_t *out_len,
                               uintptr_t *out_capa);

/**
 * This function takes a raw `protogram_capnp::proto_gram` and returns a plaintext if the signature is valid. It does not need to know the ID of the beacon that created the message
 * # Safety
 * * `bytes` should NOT be null and should point to a byte buffer of `bytes_len` length, in bytes.
 * * The library will overwrite all the `out` parameters
 * * It is not safe to read the `out` parameters if the function doesn't return `0`
 *
 * ## Arguments
 * * `bytes` - A serialized `protogram_capnp::proto_gram`
 * * `bytes_len` - The size of the `bytes` buffer
 * * `out` - A caller-managed pointer that will contain the results in case of success. Call `free_vec` to free it once you're done
 * * `out_len` - The actual size of the `out` buffer
 * * `out_capa` - The size of the underlying allocation for the `out` buffer
 *
 * ## Returns
 * `0` on success, negative values on error
 */
int32_t decrypt_beacon_message_signed(const uint8_t *bytes,
                                      uintptr_t bytes_len,
                                      uint8_t **_out,
                                      uintptr_t *out_len,
                                      uintptr_t *out_capa);

/**
 * Encrypts a plaintext to the beacon identified by `key_id`. The output is intended to be sent directly over the network
 * # Safety
 * * `bytes` should NOT be null and should point to a byte buffer of `bytes_len` length, in bytes.
 * * The library will overwrite all the `out` parameters
 * * It is not safe to read the `out` parameters if the function doesn't return `0`
 *
 * ## Arguments
 * * `key_id` - The ID of the beacon to encypt for
 * * `bytes` - Whatever you want to be encrypted to the server
 * * `bytes_len` - The size of the `bytes` buffer
 * * `out` - A caller-managed pointer that will contain the results in case of success. Call `free_vec` to free it once you're done
 * * `out_len` - The actual size of the `out` buffer
 * * `out_capa` - The size of the underlying allocation for the `out` buffer
 *
 * ## Returns
 * `0` on success, negative values on error
 */
int32_t encrypt_to_beacon(uint64_t key_id,
                          const uint8_t *bytes,
                          uintptr_t bytes_len,
                          uint8_t **_out,
                          uintptr_t *out_len,
                          uintptr_t *out_capa);

/**
 * Encrypts a plaintext to the beacon identified by `key_id`. The output is intended to be sent directly over the network
 * # Safety
 * * `bytes` should NOT be null and should point to a byte buffer of `bytes_len` length, in bytes.
 * * The library will overwrite all the `out` parameters
 * * It is not safe to read the `out` parameters if the function doesn't return `0`
 *
 * ## Arguments
 * * `key_id` - The sequence number for the beacon to encypt to
 * * `bytes` - Whatever you want to be encrypted to the server
 * * `bytes_len` - The size of the `bytes` buffer
 * * `out` - A caller-managed pointer that will contain the results in case of success. Call `free_vec` to free it once you're done
 * * `out_len` - The actual size of the `out` buffer
 * * `out_capa` - The size of the underlying allocation for the `out` buffer
 *
 * ## Returns
 * `0` on success, negative values on error
 */
int32_t encrypt_to_beacon_signed(uint64_t key_id,
                                 const uint8_t *bytes,
                                 uintptr_t bytes_len,
                                 uint8_t **_out,
                                 uintptr_t *out_len,
                                 uintptr_t *out_capa);

/**
 * This function is safe to call multiple times
 * ## Arguments
 *
 * * `is_beacon` - Whether the current instance is a beacon
 * * `server_kid` - The ID of the server's identity key for the campaign
 */
void init(bool is_beacon, uint64_t server_kid);

/**
 * # Safety
 * * `bytes` should NOT be null and should point to a byte buffer of `bytes_len` length, in bytes.
 * * The library will overwrite all the `out` parameters
 * * It is not safe to read the `out` parameters if the function doesn't return `0`
 *
 * ## Arguments
 * * `bytes` - A serialized `protogram_capnp::proto_gram`
 * * `bytes_len` - The size of the `bytes` buffer
 * * `out` - A caller-managed pointer that will contain the results in case of success. Call `free_vec` to free it once you're done
 * * `out_len` - The actual size of the `out` buffer
 * * `out_capa` - The size of the underlying allocation for the `out` buffer
 *
 * ## Returns
 * `0` on success, negative values on error
 */
int32_t verify_signature(const uint8_t *bytes,
                         uintptr_t bytes_len,
                         uint8_t **_out,
                         uintptr_t *out_len,
                         uintptr_t *out_capa,
                         uint64_t *key_id);

/**
 * # Safety
 * * `bytes` should NOT be null and should point to a byte buffer of `bytes_len` length, in bytes.
 * * The library will overwrite all the `out` parameters
 * * It is not safe to read the `out` parameters if the function doesn't return `0`
 *
 * ## Arguments
 * * `bytes` - Buffer to sign, probably should be a `cryptoframe_capnp::crypto_frame`
 * * `bytes_len` - The size of the `bytes` buffer
 * * `out` - A caller-managed pointer that will contain the results in case of success. Call `free_vec` to free it once you're done
 * * `out_len` - The actual size of the `out` buffer
 * * `out_capa` - The size of the underlying allocation for the `out` buffer
 *
 * ## Returns
 * `0` on success, negative values on error
 */
int32_t sign_message(const uint8_t *bytes,
                     uintptr_t bytes_len,
                     uint8_t **_out,
                     uintptr_t *out_len,
                     uintptr_t *out_capa);

void beaconcrypt_go_free_buffer(struct beaconcrypt_GoBuffer buffer);

struct beaconcrypt_BeaconCryptPqxdh *beaconcrypt_go_server_new(uint64_t server_kid);

struct beaconcrypt_BeaconCryptPqxdh *beaconcrypt_go_server_new_from_seed(uint64_t server_kid,
                                                                         const uint8_t *seed_ptr,
                                                                         uintptr_t seed_len);

struct beaconcrypt_BeaconCryptPqxdh *beaconcrypt_go_beacon_new(uint64_t server_kid,
                                                               const uint8_t *server_pk_ptr,
                                                               uintptr_t server_pk_len);

void beaconcrypt_go_free(struct beaconcrypt_BeaconCryptPqxdh *handle);

struct beaconcrypt_GoBuffer beaconcrypt_go_identity_pk(const struct beaconcrypt_BeaconCryptPqxdh *handle);

struct beaconcrypt_GoBuffer beaconcrypt_go_generate_registration(struct beaconcrypt_BeaconCryptPqxdh *handle);

struct beaconcrypt_GoRegistrationResponse beaconcrypt_go_register_beacon(struct beaconcrypt_BeaconCryptPqxdh *handle,
                                                                         const uint8_t *reg_ptr,
                                                                         uintptr_t reg_len,
                                                                         const uint8_t *msg_ptr,
                                                                         uintptr_t msg_len);

struct beaconcrypt_GoBuffer beaconcrypt_go_process_initial_message(struct beaconcrypt_BeaconCryptPqxdh *handle,
                                                                   const uint8_t *ptr,
                                                                   uintptr_t len);

struct beaconcrypt_GoBuffer beaconcrypt_go_encrypt_to_beacon(struct beaconcrypt_BeaconCryptPqxdh *handle,
                                                             uint64_t key_id,
                                                             const uint8_t *ptr,
                                                             uintptr_t len);

struct beaconcrypt_GoBuffer beaconcrypt_go_encrypt_to_beacon_signed(struct beaconcrypt_BeaconCryptPqxdh *handle,
                                                                    uint64_t key_id,
                                                                    const uint8_t *ptr,
                                                                    uintptr_t len);

struct beaconcrypt_GoBuffer beaconcrypt_go_decrypt_beacon_message(struct beaconcrypt_BeaconCryptPqxdh *handle,
                                                                  uint64_t key_id,
                                                                  const uint8_t *ptr,
                                                                  uintptr_t len);

struct beaconcrypt_GoBuffer beaconcrypt_go_decrypt_beacon_message_signed(struct beaconcrypt_BeaconCryptPqxdh *handle,
                                                                         const uint8_t *ptr,
                                                                         uintptr_t len);

struct beaconcrypt_GoBuffer beaconcrypt_go_encrypt_to_server(struct beaconcrypt_BeaconCryptPqxdh *handle,
                                                             const uint8_t *ptr,
                                                             uintptr_t len);

struct beaconcrypt_GoBuffer beaconcrypt_go_encrypt_to_server_signed(struct beaconcrypt_BeaconCryptPqxdh *handle,
                                                                    const uint8_t *ptr,
                                                                    uintptr_t len);

struct beaconcrypt_GoBuffer beaconcrypt_go_decrypt_server_message(struct beaconcrypt_BeaconCryptPqxdh *handle,
                                                                  const uint8_t *ptr,
                                                                  uintptr_t len);

struct beaconcrypt_GoBuffer beaconcrypt_go_decrypt_server_message_signed(struct beaconcrypt_BeaconCryptPqxdh *handle,
                                                                         const uint8_t *ptr,
                                                                         uintptr_t len);

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
