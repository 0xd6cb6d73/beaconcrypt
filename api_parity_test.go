// SPDX-License-Identifier: 0BSD

package beaconcrypt

import (
	"bytes"
	"encoding/hex"
	"errors"
	"testing"
)

func serverErrorCalls(server *Server) []struct {
	name string
	call func() error
} {
	return []struct {
		name string
		call func() error
	}{
		{"identity", func() error { _, err := server.IdentityPK(); return err }},
		{"export", func() error { _, err := server.ExportState(); return err }},
		{"head", func() error { _, err := server.Head(); return err }},
		{"register", func() error { _, err := server.RegisterBeacon(nil, nil); return err }},
		{"encrypt", func() error { _, err := server.EncryptToBeacon(1, nil); return err }},
		{"decrypt", func() error { _, err := server.DecryptBeaconMessage(nil); return err }},
		{"encrypt-state", func() error { _, err := server.EncryptAndUpdate(1, nil); return err }},
		{"decrypt-state", func() error { _, err := server.DecryptAndUpdate(nil); return err }},
		{"encrypt-json", func() error { _, err := server.EncryptAndUpdateJSON(1, nil); return err }},
		{"decrypt-json", func() error { _, err := server.DecryptAndUpdateJSON(nil); return err }},
	}
}

func beaconErrorCalls(beacon *Beacon) []struct {
	name string
	call func() error
} {
	return []struct {
		name string
		call func() error
	}{
		{"registration", func() error { _, err := beacon.GenerateRegistration(); return err }},
		{"finish-registration", func() error { _, err := beacon.ProcessInitialMessage(nil); return err }},
		{"encrypt", func() error { _, err := beacon.EncryptToServer(nil); return err }},
		{"decrypt", func() error { _, err := beacon.DecryptServerMessage(nil); return err }},
	}
}

func TestAbsentHandlesTakePrecedenceOverEmptyInputs(t *testing.T) {
	server, err := NewServerFromSeed(19, bytes.Repeat([]byte{9}, 32))
	if err != nil {
		t.Fatal(err)
	}
	publicKey, err := server.IdentityPK()
	if err != nil {
		server.Close()
		t.Fatal(err)
	}
	beacon, err := NewBeacon(19, publicKey)
	if err != nil {
		server.Close()
		t.Fatal(err)
	}
	server.Close()
	beacon.Close()

	for _, state := range []struct {
		name   string
		server *Server
		beacon *Beacon
	}{
		{"nil", nil, nil},
		{"zero", new(Server), new(Beacon)},
		{"closed", server, beacon},
	} {
		t.Run(state.name, func(t *testing.T) {
			for _, operation := range serverErrorCalls(state.server) {
				t.Run("server/"+operation.name, func(t *testing.T) {
					if err := operation.call(); !errors.Is(err, ErrClosed) {
						t.Fatalf("got %v, want ErrClosed", err)
					}
				})
			}
			if !state.server.IsPoisoned() {
				t.Error("absent server must report poisoned")
			}
			for _, operation := range beaconErrorCalls(state.beacon) {
				t.Run("beacon/"+operation.name, func(t *testing.T) {
					if err := operation.call(); !errors.Is(err, ErrClosed) {
						t.Fatalf("got %v, want ErrClosed", err)
					}
				})
			}
			state.server.Close()
			state.beacon.Close()
		})
	}
}

func TestLiveHandlesRejectEmptyOperationInputs(t *testing.T) {
	server := newServer(t)
	publicKey, err := server.IdentityPK()
	if err != nil {
		t.Fatal(err)
	}
	beacon := newBeacon(t, publicKey)
	for _, operation := range serverErrorCalls(server)[3:] {
		t.Run("server/"+operation.name, func(t *testing.T) {
			if err := operation.call(); !errors.Is(err, ErrEmptyData) {
				t.Fatalf("got %v, want ErrEmptyData", err)
			}
		})
	}
	for _, operation := range beaconErrorCalls(beacon)[1:] {
		t.Run("beacon/"+operation.name, func(t *testing.T) {
			if err := operation.call(); !errors.Is(err, ErrEmptyData) {
				t.Fatalf("got %v, want ErrEmptyData", err)
			}
		})
	}
}

func TestConstructorValidationErrors(t *testing.T) {
	for _, size := range []int{0, 1, 31, 33} {
		server, err := NewServerFromSeed(19, make([]byte, size))
		if server != nil || !errors.Is(err, ErrSeedSize) {
			t.Fatalf("seed length %d: server=%v err=%v", size, server, err)
		}
	}
	if server, err := NewServerFromState(nil); server != nil || !errors.Is(err, ErrEmptyData) {
		t.Fatalf("empty checkpoint: server=%v err=%v", server, err)
	}
	if server, err := NewServerFromState([]byte("malformed checkpoint")); server != nil || !errors.Is(err, ErrCrypto) {
		t.Fatalf("malformed checkpoint: server=%v err=%v", server, err)
	}
	for _, create := range []func() (*Server, error){
		func() (*Server, error) { return NewServerWithStore(19, []byte{1}, nil) },
		func() (*Server, error) { return NewServerWithStoreAndLineage(19, []byte{1}, nil, [32]byte{}) },
		func() (*Server, error) { return RestoreServer(nil) },
	} {
		server, err := create()
		if server != nil {
			server.Close()
			t.Fatal("invalid store returned a server")
		}
		requirePersistenceStatus(t, err, StatusInvalidArgument)
	}
	if server, err := NewServerWithStore(19, []byte{1}, &testSnapshotStore{}); server != nil || !errors.Is(err, ErrSeedSize) {
		t.Fatalf("invalid store seed: server=%v err=%v", server, err)
	}
}

func TestCopiedValuesShareHandleLifetime(t *testing.T) {
	server := newServer(t)
	publicKey, err := server.IdentityPK()
	if err != nil {
		t.Fatal(err)
	}
	beacon := newBeacon(t, publicKey)
	serverCopy, beaconCopy := *server, *beacon
	serverCopy.Close()
	beaconCopy.Close()
	if _, err := server.IdentityPK(); !errors.Is(err, ErrClosed) {
		t.Fatalf("original server survived closing its copy: %v", err)
	}
	if _, err := beacon.GenerateRegistration(); !errors.Is(err, ErrClosed) {
		t.Fatalf("original beacon survived closing its copy: %v", err)
	}
	server.Close()
	beacon.Close()
}

func TestServerIdentityMatchesRFC8032SeedVector(t *testing.T) {
	seed, err := hex.DecodeString("9d61b19deffd5a60ba844af492ec2cc44449c5697b326919703bac031cae7f60")
	if err != nil {
		t.Fatal(err)
	}
	expected, err := hex.DecodeString("d75a980182b10ab7d54bfed3c964073a0ee172f3daa62325af021a68f707511a")
	if err != nil {
		t.Fatal(err)
	}
	server, err := NewServerFromSeed(19, seed)
	if err != nil {
		t.Fatal(err)
	}
	defer server.Close()
	publicKey, err := server.IdentityPK()
	if err != nil || !bytes.Equal(publicKey, expected) {
		t.Fatalf("RFC8032publickey=%x,error=%v", publicKey, err)
	}
}
