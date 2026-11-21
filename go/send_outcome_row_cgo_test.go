// SPDX-License-Identifier: 0BSD

//go:build cgo && !beaconcrypt_wazero

package beaconcrypt

import "testing"

func TestRowExplicitSendOutcomes(t *testing.T) {
	for _, cached := range []bool{false, true} {
		var server *RowServer
		if cached {
			owner, _, _ := newCachedRowTestServer(t, 2)
			server = &owner.RowServer
		} else {
			server, _, _ = newRowTestServer(t)
		}
		beacon, kid, _ := registerRowBeacon(t, server)
		result, err := server.EncryptToBeaconOutcome(kid, nil)
		requireSendOutcome(t, result, err, SendRejected)
		result, err = server.EncryptToBeaconOutcome(kid+500, []byte("unknown"))
		requireSendOutcome(t, result, err, SendRejected)
		result, err = server.EncryptToBeaconOutcome(kid, []byte("row outcome"))
		requireSendOutcome(t, result, err, SendSent)
		if result.KeyID != kid || result.Seq == 0 {
			t.Fatal("row outcome metadata missing")
		}
		if plaintext, err := beacon.DecryptServerMessage(result.Data); err != nil || string(plaintext) != "row outcome" {
			t.Fatalf("row outcome ciphertext invalid: %q %v", plaintext, err)
		}
	}
}
