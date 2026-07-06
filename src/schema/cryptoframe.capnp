# SPDX-License-Identifier: 0BSD

@0xef858976d7f7863b;

struct CryptoFrame {
    seq @0 :UInt64;
    # Whether this message was sent from the server to a beacon
    sToB @1 :Bool;
    # libsodium-style buffer with AD + Tag + ciphertext, our code should not attempt to parse this
    cipherText @2 :Data;
}
