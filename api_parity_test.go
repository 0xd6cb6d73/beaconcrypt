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
	server, err := NewServerFromSeed(19, bytes.Repeat([]byte{9}, 32), make([]byte, 32))
	if err != nil {
		t.Fatal(err)
	}
	publicKey, err := server.IdentityPK()
	if err != nil {
		server.Close()
		t.Fatal(err)
	}
	beacon, err := NewBeacon(19, publicKey, mustServerMLDSAPublicKey(t, server))
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
	beacon := newBeacon(t, server, publicKey)
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
		server, err := NewServerFromSeed(19, make([]byte, size), make([]byte, 32))
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
		func() (*Server, error) { return NewServerWithStore(19, []byte{1}, nil, nil) },
		func() (*Server, error) { return NewServerWithStoreAndLineage(19, []byte{1}, nil, nil, [32]byte{}) },
		func() (*Server, error) { return RestoreServer(nil) },
	} {
		server, err := create()
		if server != nil {
			server.Close()
			t.Fatal("invalid store returned a server")
		}
		requirePersistenceStatus(t, err, StatusInvalidArgument)
	}
	if server, err := NewServerWithStore(19, []byte{1}, nil, &testSnapshotStore{}); server != nil || !errors.Is(err, ErrSeedSize) {
		t.Fatalf("invalid store seed: server=%v err=%v", server, err)
	}
}

func TestCopiedValuesShareHandleLifetime(t *testing.T) {
	server := newServer(t)
	publicKey, err := server.IdentityPK()
	if err != nil {
		t.Fatal(err)
	}
	beacon := newBeacon(t, server, publicKey)
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
	server, err := NewServerFromSeed(19, seed, make([]byte, 32))
	if err != nil {
		t.Fatal(err)
	}
	defer server.Close()
	publicKey, err := server.IdentityPK()
	if err != nil || !bytes.Equal(publicKey, expected) {
		t.Fatalf("RFC8032publickey=%x,error=%v", publicKey, err)
	}
}

func TestMLDSAConstructorValidationAndPublicKeyLifetime(t *testing.T) {
	server := newServer(t)
	ed, err := server.IdentityPK()
	if err != nil {
		t.Fatal(err)
	}
	for _, length := range []int{0, 1, MLDSA65PublicKeySize - 1, MLDSA65PublicKeySize + 1} {
		if beacon, err := NewBeacon(0, ed, make([]byte, length)); beacon != nil || !errors.Is(err, ErrCrypto) {
			t.Fatalf("ML-DSA pin length %d accepted: %v", length, err)
		}
	}
	for _, length := range []int{0, 1, 31, 33} {
		if created, err := NewServerFromSeed(0, make([]byte, 32), make([]byte, length)); created != nil || !errors.Is(err, ErrSeedSize) {
			t.Fatalf("ML-DSA seed length %d accepted: %v", length, err)
		}
	}
	beacon := newBeacon(t, server, ed)
	key, err := beacon.MLDSAPublicKey()
	if err != nil || len(key) != MLDSA65PublicKeySize {
		t.Fatalf("beacon ML-DSA key: %d, %v", len(key), err)
	}
	server.Close()
	beacon.Close()
	for _, get := range []func() ([]byte, error){server.MLDSAPublicKey, beacon.MLDSAPublicKey, (*Server)(nil).MLDSAPublicKey, (*Beacon)(nil).MLDSAPublicKey} {
		if _, err := get(); !errors.Is(err, ErrClosed) {
			t.Fatalf("absent ML-DSA getter: %v", err)
		}
	}
}

func TestMLDSAServerPinSeparatelyAuthenticatesTheRegistration(t *testing.T) {
	edSeed := bytes.Repeat([]byte{17}, 32)
	first, err := NewServerFromSeed(0, edSeed, bytes.Repeat([]byte{18}, 32))
	if err != nil {
		t.Fatal(err)
	}
	t.Cleanup(first.Close)
	intended, err := NewServerFromSeed(0, edSeed, bytes.Repeat([]byte{19}, 32))
	if err != nil {
		t.Fatal(err)
	}
	t.Cleanup(intended.Close)
	ed, err := first.IdentityPK()
	if err != nil {
		t.Fatal(err)
	}
	beacon := newBeacon(t, intended, ed)
	registration, err := beacon.GenerateRegistration()
	if err != nil {
		t.Fatal(err)
	}
	before, err := first.ExportState()
	if err != nil {
		t.Fatal(err)
	}
	if response, err := first.RegisterBeacon(registration, []byte("wrong ML-DSA identity")); response != nil || err == nil {
		t.Fatal("registration was accepted with a different ML-DSA key and the same Ed25519 key")
	}
	after, err := first.ExportState()
	if err != nil {
		t.Fatal(err)
	}
	// Registration attempts commit a new persistence generation even on rejection;
	// the canonical server payload after the 100-byte envelope must stay identical.
	const snapshotHeaderBytes = 100
	if len(before) < snapshotHeaderBytes || len(after) < snapshotHeaderBytes || !bytes.Equal(before[snapshotHeaderBytes:], after[snapshotHeaderBytes:]) {
		t.Fatal("rejected authentication changed the protocol state")
	}
	response, err := intended.RegisterBeacon(registration, []byte("intended server"))
	if err != nil {
		t.Fatal(err)
	}
	opened, err := beacon.ProcessInitialMessage(response.Serialized)
	if err != nil || !bytes.Equal(opened, []byte("intended server")) {
		t.Fatalf("intended registration: %q, %v", opened, err)
	}
}
