# SPDX-License-Identifier: 0BSD

@0xd840dedb1017061a;

struct InitKex {
    identityKey @0 :Data;

    # we use libsodium-style buffers: sig || data
    preKey @1 :Data;
    oneTimeKey @2 :Data;
    pqKey @3 :Data;
}
