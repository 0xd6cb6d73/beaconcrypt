#ifndef _BEACON_CRYPT_H_
#define _BEACON_CRYPT_H_

/* Generated with cbindgen:0.29.4 */

// Do not modify manually.

#include <stdarg.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdlib.h>



#define beaconcrypt_ML_DSA_SIGN_RANDOM_SIZE 32



#define beaconcrypt_ML_DSA_87_ENC_PUBKEY_SIZE (beaconcrypt_ML_DSA_87_PUBKEY_SIZE + 1)

#define beaconcrypt_ML_KEM_1024_ENCAP_RAN_SIZE beaconcrypt_SHARED_SECRET_SIZE

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

#define beaconcrypt_KEM_SHARED_SECRET_SIZE 32

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
 * * `server_seq` - The ID of the server's identity key for the campaign
 */
void init_for_server(bool is_beacon,
                     uint64_t server_seq,
                     const uint8_t *server_pk,
                     uint64_t server_pk_len);

/**
 * Initialize a server with existing keys from seeds. This MUST only be called by a server
 * # Safety
 * This function is safe to call multiple times.
 * ## Arguments
 *
 * * `server_seq` - The ID of the server's identity key for the campaign
 * * `id_seed` - 32 byte Ed25519 seed for the server's identity key
 */
void init_server_from_seeds(uint64_t server_seq, const uint8_t *id_seed);

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
 * # Safety
 * * `bytes` should NOT be null and should point to a byte buffer of `bytes_len` length, in bytes.
 * * The library will overwrite all the `out` parameters
 * * It is not safe to read the `out` parameters if the function doesn't return `0`
 *
 * ## Arguments
 * * `seq` - The sequence number for the beacon to encypt to
 * * `bytes` - A serialized `cryptoframe_capnp::crypto_frame`
 * * `bytes_len` - The size of the `bytes` buffer
 * * `out` - A caller-managed pointer that will contain the results in case of success. Call `free_vec` to free it once you're done
 * * `out_len` - The actual size of the `out` buffer
 * * `out_capa` - The size of the underlying allocation for the `out` buffer
 *
 * ## Returns
 * `0` on success, negative values on error
 */
int32_t decrypt_beacon_message(uint64_t seq,
                               const uint8_t *bytes,
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
 * * `seq` - The sequence number for the beacon to encypt to
 * * `bytes` - A serialized `cryptoframe_capnp::crypto_frame`
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
 * # Safety
 * * `bytes` should NOT be null and should point to a byte buffer of `bytes_len` length, in bytes.
 * * The library will overwrite all the `out` parameters
 * * It is not safe to read the `out` parameters if the function doesn't return `0`
 *
 * ## Arguments
 * * `seq` - The sequence number for the beacon to encypt to
 * * `bytes` - Whatever you want to be encrypted to the server
 * * `bytes_len` - The size of the `bytes` buffer
 * * `out` - A caller-managed pointer that will contain the results in case of success. Call `free_vec` to free it once you're done
 * * `out_len` - The actual size of the `out` buffer
 * * `out_capa` - The size of the underlying allocation for the `out` buffer
 *
 * ## Returns
 * `0` on success, negative values on error
 */
int32_t encrypt_to_beacon(uint64_t seq,
                          const uint8_t *bytes,
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
 * * `seq` - The sequence number for the beacon to encypt to
 * * `bytes` - Whatever you want to be encrypted to the server
 * * `bytes_len` - The size of the `bytes` buffer
 * * `out` - A caller-managed pointer that will contain the results in case of success. Call `free_vec` to free it once you're done
 * * `out_len` - The actual size of the `out` buffer
 * * `out_capa` - The size of the underlying allocation for the `out` buffer
 *
 * ## Returns
 * `0` on success, negative values on error
 */
int32_t encrypt_to_beacon_signed(uint64_t seq,
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
 * * `server_seq` - The ID of the server's identity key for the campaign
 */
void init(bool is_beacon, uint64_t server_seq);

/**
 * # Safety
 * * This function MUST only be called to clean up byte buffers returned by this library, do NOT use as a general `free`
 * * `ptr` should NOT be null and should point to a byte buffer of `len` length, in bytes.
 */
void free_vec(uint8_t *ptr,
              uintptr_t len,
              uintptr_t capa);

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
                         uint8_t *_out,
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
                     uint8_t *_out,
                     uintptr_t *out_len,
                     uintptr_t *out_capa);

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  /* _BEACON_CRYPT_H_ */
