// SPDX-License-Identifier: 0BSD
//go:build cgo && !beaconcrypt_wazero

package beaconcrypt

import (
	"errors"
	"testing"
)

func TestRowServerAndSessionRetirePeer(t *testing.T) {
	server, _, _ := newRowTestServer(t)
	beacon, kid, request := registerRowBeacon(t, server)
	_, other, _ := registerRowBeacon(t, server)
	inbound, err := beacon.EncryptToServer([]byte("after retirement"))
	if err != nil {
		t.Fatal(err)
	}
	if retired, err := server.RetirePeer(kid); err != nil || !retired {
		t.Fatalf("retire: %v %v", retired, err)
	}
	if retired, err := server.RetirePeer(kid); err != nil || retired {
		t.Fatalf("second retire: %v %v", retired, err)
	}
	if _, err := server.DecryptBeaconMessage(inbound); !errors.Is(err, ErrCrypto) {
		t.Fatalf("retired inbound: %v", err)
	}
	if _, err := server.EncryptToBeacon(kid, []byte("tasking")); !errors.Is(err, ErrCrypto) {
		t.Fatalf("retired outbound: %v", err)
	}
	if _, err := server.RegisterBeacon(request, nil); !errors.Is(err, ErrCrypto) {
		t.Fatalf("replayed registration: %v", err)
	}

	output, err := server.Transaction(func(session *RowSession) ([]byte, error) {
		if err := session.Store([]byte("audit"), []byte("retired")); err != nil {
			return nil, err
		}
		retired, err := session.RetirePeer(other)
		if err != nil || !retired {
			t.Errorf("session retire: %v %v", retired, err)
		}
		return []byte("done"), err
	})
	if err != nil || string(output) != "done" {
		t.Fatalf("session transaction: %q %v", output, err)
	}
	if _, err := server.EncryptToBeacon(other, []byte("tasking")); !errors.Is(err, ErrCrypto) {
		t.Fatalf("session-retired outbound: %v", err)
	}
}
