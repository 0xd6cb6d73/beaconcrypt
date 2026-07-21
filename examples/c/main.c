// SPDX-License-Identifier: 0BSD

#include "bindings.h"

#include <inttypes.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#ifdef _WIN32
#include <windows.h>

#include <bcrypt.h>
#endif

#define SERVER_KID 0
#define TRANSPORT_PATH "transport"

static const uint8_t REGISTRATION_MESSAGE[] = "registration ok";

static void free_buffer(beaconcrypt_Buffer *buffer) {
  if (buffer != NULL && buffer->ptr != NULL) {
    beaconcrypt_free_buffer(*buffer);
    buffer->ptr = NULL;
    buffer->len = 0;
    buffer->cap = 0;
  }
}

static void
free_registration_response(beaconcrypt_RegistrationResponse *response) {
  if (response != NULL) {
    free_buffer(&response->response);
    free_buffer(&response->beacon_pk);
    response->key_id = 0;
  }
}

static void free_encrypt_state(beaconcrypt_EncryptState *state) {
  if (state != NULL) {
    free_buffer(&state->data);
    free_buffer(&state->key);
    state->key_id = 0;
  }
}

static int buffer_is_empty(beaconcrypt_Buffer buffer) {
  return buffer.ptr == NULL;
}

static int fill_random(uint8_t *buffer, size_t len) {
#ifdef _WIN32
  return BCryptGenRandom(NULL, buffer, (ULONG)len,
                         BCRYPT_USE_SYSTEM_PREFERRED_RNG) == 0
             ? 0
             : -1;
#else
  FILE *file = fopen("/dev/urandom", "rb");
  if (file == NULL) {
    return -1;
  }
  size_t read_len = fread(buffer, 1, len, file);
  int close_result = fclose(file);
  return read_len == len && close_result == 0 ? 0 : -1;
#endif
}

static int write_transport(const uint8_t *data, size_t len) {
  FILE *file = fopen(TRANSPORT_PATH, "wb");
  if (file == NULL) {
    return -1;
  }
  size_t written = fwrite(data, 1, len, file);
  int close_result = fclose(file);
  return written == len && close_result == 0 ? 0 : -1;
}

static int read_transport(uint8_t **out, size_t *out_len) {
  *out = NULL;
  *out_len = 0;

  FILE *file = fopen(TRANSPORT_PATH, "rb");
  if (file == NULL) {
    return -1;
  }
  if (fseek(file, 0, SEEK_END) != 0) {
    fclose(file);
    return -1;
  }
  long file_len = ftell(file);
  if (file_len <= 0 || fseek(file, 0, SEEK_SET) != 0) {
    fclose(file);
    return -1;
  }

  uint8_t *buffer = malloc((size_t)file_len);
  if (buffer == NULL) {
    fclose(file);
    return -1;
  }

  size_t read_len = fread(buffer, 1, (size_t)file_len, file);
  int close_result = fclose(file);
  if (read_len != (size_t)file_len || close_result != 0) {
    free(buffer);
    return -1;
  }

  *out = buffer;
  *out_len = (size_t)file_len;
  return 0;
}

static void print_text(const char *label, beaconcrypt_Buffer buffer) {
  printf("%s: %.*s\n", label, (int)buffer.len, (const char *)buffer.ptr);
}

static void print_state(const beaconcrypt_EncryptState *state) {
  printf("Key ID: %" PRIu64 "\n", state->key_id);
  printf("Ratchet state: ");
  for (size_t i = 0; i < state->key.len; i++) {
    printf("%02x", state->key.ptr[i]);
  }
  putchar('\n');
}

static int run(void) {
  int result = 1;
  uint8_t server_seed[32];
  uint8_t *transport = NULL;
  size_t transport_len = 0;

  beaconcrypt_BeaconCryptPqxdh *server = NULL;
  beaconcrypt_BeaconCryptPqxdh *beacon = NULL;
  beaconcrypt_Buffer server_pk = {0};
  beaconcrypt_Buffer b_reg_1 = {0};
  beaconcrypt_RegistrationResponse s_reg_resp = {0};
  beaconcrypt_Buffer first_message = {0};
  beaconcrypt_Buffer b_ping = {0};
  beaconcrypt_EncryptState ping = {0};
  beaconcrypt_EncryptState s_task_0 = {0};
  beaconcrypt_Buffer task_0 = {0};
  beaconcrypt_Buffer b_task_1 = {0};
  beaconcrypt_EncryptState task_1 = {0};

  if (fill_random(server_seed, sizeof(server_seed)) != 0) {
    fprintf(stderr, "error: failed to generate server seed\n");
    goto cleanup;
  }

  server = beaconcrypt_server_new_from_seed(SERVER_KID, server_seed,
                                            sizeof(server_seed));
  if (server == NULL) {
    fprintf(stderr, "error: failed to create server\n");
    goto cleanup;
  }

  /* It is assumed that the server's public key is compiled into beacons. */
  server_pk = beaconcrypt_identity_pk(server);
  if (buffer_is_empty(server_pk)) {
    fprintf(stderr, "error: failed to get server public key\n");
    goto cleanup;
  }
  beacon = beaconcrypt_beacon_new(SERVER_KID, server_pk.ptr, server_pk.len);
  if (beacon == NULL) {
    fprintf(stderr, "error: failed to create beacon\n");
    goto cleanup;
  }
  free_buffer(&server_pk);

  /* The beacon is run and registers. */
  b_reg_1 = beaconcrypt_generate_registration(beacon);
  if (buffer_is_empty(b_reg_1)) {
    fprintf(stderr, "error: failed to generate registration\n");
    goto cleanup;
  }
  /* Ship the registration bytes over whichever transport you like. */
  if (write_transport(b_reg_1.ptr, b_reg_1.len) != 0) {
    fprintf(stderr, "error: failed to write registration transport\n");
    goto cleanup;
  }
  free_buffer(&b_reg_1);

  if (read_transport(&transport, &transport_len) != 0) {
    fprintf(stderr, "error: failed to read registration transport\n");
    goto cleanup;
  }

  /* Now the server has the registration message and can send an initial message
   * if needed. */
  s_reg_resp = beaconcrypt_register_beacon(server, transport, transport_len,
                                           REGISTRATION_MESSAGE,
                                           sizeof(REGISTRATION_MESSAGE) - 1);
  free(transport);
  transport = NULL;
  transport_len = 0;
  if (buffer_is_empty(s_reg_resp.response)) {
    fprintf(stderr, "error: failed to register beacon\n");
    goto cleanup;
  }

  /* Ship the response back over your transport. */
  if (write_transport(s_reg_resp.response.ptr, s_reg_resp.response.len) != 0) {
    fprintf(stderr, "error: failed to write registration response transport\n");
    goto cleanup;
  }
  if (read_transport(&transport, &transport_len) != 0) {
    fprintf(stderr, "error: failed to read registration response transport\n");
    goto cleanup;
  }

  /* Do whatever you like with the initial message. */
  first_message =
      beaconcrypt_process_initial_message(beacon, transport, transport_len);
  free(transport);
  transport = NULL;
  transport_len = 0;
  if (buffer_is_empty(first_message)) {
    fprintf(stderr, "error: failed to process initial message\n");
    goto cleanup;
  }
  print_text("Beacon got initial message", first_message);
  free_buffer(&first_message);

  b_ping =
      beaconcrypt_encrypt_to_server_signed(beacon, (const uint8_t *)"ping", 4);
  if (buffer_is_empty(b_ping) || write_transport(b_ping.ptr, b_ping.len) != 0) {
    fprintf(stderr, "error: failed to send ping\n");
    goto cleanup;
  }
  free_buffer(&b_ping);
  if (read_transport(&transport, &transport_len) != 0) {
    fprintf(stderr, "error: failed to read ping transport\n");
    goto cleanup;
  }

  /* Got the ping, maybe there's a task to send now. */
  ping = beaconcrypt_decrypt_and_update(server, transport, transport_len);
  free(transport);
  transport = NULL;
  transport_len = 0;
  if (buffer_is_empty(ping.data)) {
    fprintf(stderr, "error: failed to decrypt ping\n");
    goto cleanup;
  }
  print_text("Server got ping", ping.data);
  print_state(&ping);
  free_encrypt_state(&ping);

  /* The C2 needs to know what the beacon's ID is so it can encrypt to it. */
  s_task_0 = beaconcrypt_encrypt_and_update(
      server, s_reg_resp.key_id, (const uint8_t *)"task contents", 13);
  if (buffer_is_empty(s_task_0.data)) {
    fprintf(stderr, "error: failed to send first task\n");
    goto cleanup;
  }
  print_state(&s_task_0);
  if (write_transport(s_task_0.data.ptr, s_task_0.data.len) != 0) {
    fprintf(stderr, "error: failed to send first task\n");
    goto cleanup;
  }
  free_encrypt_state(&s_task_0);
  if (read_transport(&transport, &transport_len) != 0) {
    fprintf(stderr, "error: failed to read first task transport\n");
    goto cleanup;
  }

  task_0 = beaconcrypt_decrypt_server_message_signed(beacon, transport,
                                                     transport_len);
  free(transport);
  transport = NULL;
  transport_len = 0;
  if (buffer_is_empty(task_0)) {
    fprintf(stderr, "error: failed to decrypt first task\n");
    goto cleanup;
  }
  print_text("Beacon got first task", task_0);
  free_buffer(&task_0);

  /* Process task and send the response. */
  b_task_1 = beaconcrypt_encrypt_to_server_signed(
      beacon, (const uint8_t *)"task response", 13);
  if (buffer_is_empty(b_task_1) ||
      write_transport(b_task_1.ptr, b_task_1.len) != 0) {
    fprintf(stderr, "error: failed to send task response\n");
    goto cleanup;
  }
  free_buffer(&b_task_1);
  if (read_transport(&transport, &transport_len) != 0) {
    fprintf(stderr, "error: failed to read task response transport\n");
    goto cleanup;
  }

  task_1 = beaconcrypt_decrypt_and_update(server, transport, transport_len);
  free(transport);
  transport = NULL;
  transport_len = 0;
  if (buffer_is_empty(task_1.data)) {
    fprintf(stderr, "error: failed to decrypt task response\n");
    goto cleanup;
  }
  print_text("Server got response to first task", task_1.data);
  print_state(&task_1);

  result = 0;

cleanup:
  free(transport);
  free_buffer(&server_pk);
  free_buffer(&b_reg_1);
  free_registration_response(&s_reg_resp);
  free_buffer(&first_message);
  free_buffer(&b_ping);
  free_encrypt_state(&ping);
  free_encrypt_state(&s_task_0);
  free_buffer(&task_0);
  free_buffer(&b_task_1);
  free_encrypt_state(&task_1);
  if (beacon != NULL) {
    beaconcrypt_free(beacon);
  }
  if (server != NULL) {
    beaconcrypt_free(server);
  }
  remove(TRANSPORT_PATH);
  return result;
}

int main(void) { return run(); }
