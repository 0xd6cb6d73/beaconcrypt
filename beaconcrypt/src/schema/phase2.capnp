# SPDX-License-Identifier: 0BSD

@0xd7a57844e2843863;

struct KexResponse {
    identityKey @0 :Data;
    ephemeralKey @1 :Data;
    # this is the KEM ciphertext used to protect the PQ shared secret
    kemCipherText @2 :Data;
    # A serialized `CryptoFrame`, this is an application-defined message encrypted under the newly derived key
    appCipherText @3 :Data;
    # The ID assigned to this beacon instance's identity
    keyId @4 :UInt64;
}
