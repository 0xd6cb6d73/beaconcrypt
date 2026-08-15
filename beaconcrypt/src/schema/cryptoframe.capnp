# SPDX-License-Identifier: 0BSD

@0xef858976d7f7863b;

struct CryptoFrame {
    # sequence number for the key used to encrypt `cipherText`
    seq @0 :UInt64;
    # identifier for the sender's public key
    keyId @1 :UInt64;
    # libsodium-style buffer with ciphertext || tag || commitment
    cipherText @2 :Data;
}
