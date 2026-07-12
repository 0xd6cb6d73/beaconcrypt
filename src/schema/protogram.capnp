# SPDX-License-Identifier: 0BSD

@0xec633cc0f84b92e3;

struct ProtoGram {
   # signed buffer in libsodium format
   data @0 :Data;
   # This is the identifier of the key used to sign this message.
   keyId @1 :UInt64;
}
