// SPDX-License-Identifier: 0BSD
//go:build !cgo || beaconcrypt_wazero

package beaconcrypt

import (
	"errors"
	"testing"
)

func TestRowPersistenceExplicitlyUnsupportedOnWasm(t *testing.T) {
	if server, err := NewRowServer(0, nil, nil, nil, [32]byte{}); server != nil || !errors.Is(err, ErrPersistenceUnsupported) {
		t.Fatalf("create: %v, %v", server, err)
	}
	if server, err := OpenRowServer(nil, [32]byte{}); server != nil || !errors.Is(err, ErrPersistenceUnsupported) {
		t.Fatalf("open: %v, %v", server, err)
	}
	var server *RowServer
	server.Close()
	if _, err := server.DecryptBeaconMessage(nil); !errors.Is(err, ErrClosed) {
		t.Fatal(err)
	}
}
