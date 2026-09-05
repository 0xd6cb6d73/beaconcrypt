#ifndef _BEACON_CRYPT_H_
#define _BEACON_CRYPT_H_

/* Generated with cbindgen:0.29.4 */

// Do not modify manually.

#include <stdarg.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdlib.h>



#define beaconcrypt_KDF_STATE_SIZE 32

/**
 * crypto_aead::chacha20poly1305_ietf::KEYBYTES
 */
#define beaconcrypt_AEAD_KEY_LEN 32

/**
 * crypto_aead::chacha20poly1305_ietf::NPUBBYTES
 */
#define beaconcrypt_AEAD_NONCE_LEN 12

/**
 * crypto_aead::chacha20poly1305_ietf::ABYTES
 */
#define beaconcrypt_AEAD_TAG_LEN 16

#define beaconcrypt_KDF_RATCHET_OUTPUT_LEN ((beaconcrypt_AEAD_KEY_LEN + beaconcrypt_KDF_STATE_SIZE) + beaconcrypt_AEAD_NONCE_LEN)

#define beaconcrypt_RATCHET_MAX_GAP 50

#define beaconcrypt_COMMITMENT_SIZE 64

#define beaconcrypt_MESSAGE_OVERHEAD (beaconcrypt_COMMITMENT_SIZE + beaconcrypt_AEAD_TAG_LEN)

#define beaconcrypt_KEX_KDF_OUT_LEN 32

/**
 * crypto_scalarmult::BYTES
 */
#define beaconcrypt_DH_OUT_LEN 32

#define beaconcrypt_ED25519_SEED_SIZE 32

/**
 * Opaque beacon handle exposed by the C API and owned by its caller.
 */
typedef struct beaconcrypt_Beacon beaconcrypt_Beacon;

/**
 * Opaque server handle owned by the C caller.
 */
typedef struct beaconcrypt_Server beaconcrypt_Server;

/**
 * Heap-allocated byte buffer returned by the C API.
 *
 * A non-empty buffer must be released exactly once with `beaconcrypt_free_buffer`. An empty buffer has a null `ptr` and indicates either empty output or failure, depending on the called function.
 */
typedef struct beaconcrypt_Buffer {
  /**
   * Pointer to the first byte, or null when the buffer is empty.
   */
  uint8_t *ptr;
  /**
   * Number of initialized bytes available through `ptr`.
   */
  uintptr_t len;
  /**
   * Allocation capacity reserved for `beaconcrypt_free_buffer`; callers must not modify it.
   */
  uintptr_t cap;
} beaconcrypt_Buffer;

/**
 * Result returned after a successful server-side beacon registration.
 */
typedef struct beaconcrypt_RegistrationResponse {
  /**
   * Serialized registration response for the beacon.
   */
  struct beaconcrypt_Buffer response;
  /**
   * Key identifier assigned to the registered beacon.
   */
  uint64_t key_id;
} beaconcrypt_RegistrationResponse;

/**
 * Message output accompanied by observational ratchet metadata.
 */
typedef struct beaconcrypt_EncryptState {
  /**
   * Ciphertext for encryption calls or plaintext for decryption calls.
   */
  struct beaconcrypt_Buffer data;
  /**
   * Inert plaintext ratchet JSON for observation only.
   * It is secret-bearing, unauthenticated, and not restorable.
   */
  struct beaconcrypt_Buffer state;
  /**
   * Key identifier used by the ratchet operation.
   */
  uint64_t key_id;
  /**
   * Ratchet sequence number used by the operation.
   */
  uint64_t seq;
} beaconcrypt_EncryptState;



#ifdef __cplusplus
extern "C" {
#endif // __cplusplus

/**
 * Release a byte buffer returned by this API.
 *
 * Passing an empty buffer is allowed. The buffer and its pointer must not be used after this call.
 * The complete allocation is wiped before release. Copies retained by the caller are not erased.
 */
void beaconcrypt_free_buffer(struct beaconcrypt_Buffer buffer);

/**
 * Create a server with a randomly generated identity key.
 *
 * Returns an owned handle, or null on failure. Release a non-null handle with `beaconcrypt_server_free`.
 */
struct beaconcrypt_Server *beaconcrypt_server_new(uint64_t server_kid);

/**
 * Create a server with an optional deterministic identity seed.
 *
 * A null pointer or zero length selects a random identity key. A non-empty seed must contain exactly `beaconcrypt_ED25519_SEED_SIZE` readable bytes.
 *
 * Returns an owned handle, or null when creation fails. Release a non-null handle with `beaconcrypt_server_free`.
 */
struct beaconcrypt_Server *beaconcrypt_server_new_from_seed(uint64_t server_kid,
                                                            const uint8_t *seed_ptr,
                                                            uintptr_t seed_len);

/**
 * Restore a server from trusted checkpoint bytes.
 *
 * The caller must reject stale or untrusted checkpoints. These bytes are plaintext and are not cryptographically authenticated.
 *
 * Restoration advances the generation, so export and save the returned handle immediately before using it. Returns an owned handle, or null for invalid state.
 */
struct beaconcrypt_Server *beaconcrypt_server_new_from_state(const uint8_t *state_ptr,
                                                             uintptr_t state_len);

/**
 * Export the current plaintext checkpoint.
 *
 * Save it immediately after every accepted receive or other state-changing call and before using that call's output.
 * A normal rejected receive leaves the checkpoint unchanged.
 * Returns an empty buffer on failure.
 */
struct beaconcrypt_Buffer beaconcrypt_server_export_state(const struct beaconcrypt_Server *handle);

/**
 * Create a beacon bound to a server identity public key.
 *
 * `server_pk_ptr` must point to an Ed25519 public key of the length implied by the API constants.
 *
 * Returns an owned handle, or null for absent or incorrectly sized input or a reported initialization/key-generation failure. Release a non-null handle with `beaconcrypt_beacon_free`.
 */
struct beaconcrypt_Beacon *beaconcrypt_beacon_new(uint64_t server_kid,
                                                  const uint8_t *server_pk_ptr,
                                                  uintptr_t server_pk_len);

/**
 * Release a server handle created by this API.
 *
 * Passing null is allowed. The handle must not be used after this call.
 */
void beaconcrypt_server_free(struct beaconcrypt_Server *handle);

/**
 * Release a beacon handle created by this API.
 *
 * Passing null is allowed. The handle must not be used after this call.
 */
void beaconcrypt_beacon_free(struct beaconcrypt_Beacon *handle);

/**
 * Copy the server identity public key into a caller-owned buffer.
 *
 * Returns an empty buffer when `handle` is null.
 */
struct beaconcrypt_Buffer beaconcrypt_server_identity_pk(const struct beaconcrypt_Server *handle);

/**
 * Copy the beacon identity public key into a caller-owned buffer.
 *
 * Returns an empty buffer when `handle` is null.
 */
struct beaconcrypt_Buffer beaconcrypt_beacon_identity_pk(const struct beaconcrypt_Beacon *handle);

/**
 * Generate the beacon's serialized registration bundle.
 *
 * Returns an empty buffer when the handle is invalid or the beacon cannot generate a bundle in its current state.
 */
struct beaconcrypt_Buffer beaconcrypt_generate_registration(struct beaconcrypt_Beacon *handle);

/**
 * Register a beacon and build its initial server response.
 *
 * `msg_ptr` may be null when `msg_len` is zero to omit the initial message. On failure, returns an empty response with key identifier zero.
 */
struct beaconcrypt_RegistrationResponse beaconcrypt_register_beacon(struct beaconcrypt_Server *handle,
                                                                    const uint8_t *reg_ptr,
                                                                    uintptr_t reg_len,
                                                                    const uint8_t *msg_ptr,
                                                                    uintptr_t msg_len);

/**
 * Finish beacon registration and return the optional initial plaintext message.
 *
 * Returns an empty buffer when the input is invalid, registration fails, or no initial message was supplied.
 */
struct beaconcrypt_Buffer beaconcrypt_process_initial_message(struct beaconcrypt_Beacon *handle,
                                                              const uint8_t *ptr,
                                                              uintptr_t len);

/**
 * Encrypt a message from the server to the beacon identified by `key_id`.
 *
 * Returns an empty buffer when the handle or input is invalid, the key is unknown, or encryption fails.
 */
struct beaconcrypt_Buffer beaconcrypt_encrypt_to_beacon(struct beaconcrypt_Server *handle,
                                                        uint64_t key_id,
                                                        const uint8_t *ptr,
                                                        uintptr_t len);

/**
 * Decrypt a beacon-to-server message.
 *
 * Returns an empty buffer when the handle or input is invalid, authentication fails, or the ratchet rejects the message.
 */
struct beaconcrypt_Buffer beaconcrypt_decrypt_beacon_message(struct beaconcrypt_Server *handle,
                                                             const uint8_t *ptr,
                                                             uintptr_t len);

/**
 * Encrypt a server-to-beacon message and return observational ratchet metadata.
 *
 * Returns an empty `beaconcrypt_EncryptState` when the operation fails. Persist the server checkpoint before using the returned output.
 */
struct beaconcrypt_EncryptState beaconcrypt_encrypt_and_update(struct beaconcrypt_Server *handle,
                                                               uint64_t key_id,
                                                               const uint8_t *ptr,
                                                               uintptr_t len);

/**
 * Encrypt a server-to-beacon message and return the result and ratchet metadata as JSON.
 *
 * Returns an empty buffer when the operation fails. Persist the server checkpoint before using the returned output.
 */
struct beaconcrypt_Buffer beaconcrypt_encrypt_and_update_json(struct beaconcrypt_Server *handle,
                                                              uint64_t key_id,
                                                              const uint8_t *ptr,
                                                              uintptr_t len);

/**
 * Decrypt a beacon-to-server message and return observational ratchet metadata.
 *
 * Returns an empty `beaconcrypt_EncryptState` when the operation fails. Persist the server checkpoint before using the returned output.
 */
struct beaconcrypt_EncryptState beaconcrypt_decrypt_and_update(struct beaconcrypt_Server *handle,
                                                               const uint8_t *ptr,
                                                               uintptr_t len);

/**
 * Decrypt a beacon-to-server message and return the result and ratchet metadata as JSON.
 *
 * Returns an empty buffer when the operation fails. Persist the server checkpoint before using the returned output.
 */
struct beaconcrypt_Buffer beaconcrypt_decrypt_and_update_json(struct beaconcrypt_Server *handle,
                                                              const uint8_t *ptr,
                                                              uintptr_t len);

/**
 * Encrypt a message from the beacon to its server.
 *
 * Returns an empty buffer when the handle or input is invalid or encryption fails.
 */
struct beaconcrypt_Buffer beaconcrypt_encrypt_to_server(struct beaconcrypt_Beacon *handle,
                                                        const uint8_t *ptr,
                                                        uintptr_t len);

/**
 * Decrypt a server-to-beacon message.
 *
 * Returns an empty buffer when the handle or input is invalid, authentication fails, or the ratchet rejects the message.
 */
struct beaconcrypt_Buffer beaconcrypt_decrypt_server_message(struct beaconcrypt_Beacon *handle,
                                                             const uint8_t *ptr,
                                                             uintptr_t len);

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  /* _BEACON_CRYPT_H_ */
