# SPDX-License-Identifier: 0BSD

@0xef858976d7f7863b;

struct CryptoFrame {
    seq @0 :UInt64;
    # libsodium-style buffer with ciphertext || tag || commitment
    cipherText @1 :Data;
}
