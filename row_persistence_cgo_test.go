// SPDX-License-Identifier: 0BSD
//go:build cgo && !beaconcrypt_wazero

package beaconcrypt

import (
	"bytes"
	"errors"
	"reflect"
	"sync"
	"testing"
)

// Callback contract fixture. The Python integration suite and Rust SQL example
// exercise real SQLite databases; these tests inject binding failures directly.
type rowDatabase struct {
	mu   sync.Mutex
	rows map[string][]byte
}
type rowTestStore struct {
	database        *rowDatabase
	pending         map[string][]byte
	failCommit      bool
	failAfterCommit bool
	panicLoad       bool
	failBegin       bool
}

var errRowCommit = errors.New("row commit failed")

func (s *rowTestStore) Begin() error {
	s.database.mu.Lock()
	s.pending = make(map[string][]byte)
	for key, value := range s.database.rows {
		s.pending[key] = bytes.Clone(value)
	}
	if s.failBegin {
		return errors.New("begin failed after transaction start")
	}
	return nil
}
func (s *rowTestStore) Load(key []byte) ([]byte, error) {
	if s.panicLoad {
		panic("row load panic")
	}
	return bytes.Clone(s.pending[string(key)]), nil
}
func (s *rowTestStore) Store(key, value []byte) error {
	s.pending[string(key)] = bytes.Clone(value)
	return nil
}
func (s *rowTestStore) Commit() error {
	if s.failCommit {
		return errRowCommit
	}
	s.database.rows = s.pending
	s.pending = nil
	s.database.mu.Unlock()
	if s.failAfterCommit {
		return errRowCommit
	}
	return nil
}
func (s *rowTestStore) Rollback() error {
	if s.pending != nil {
		s.pending = nil
		s.database.mu.Unlock()
	}
	return nil
}

func newRowTestServer(t *testing.T) (*RowServer, *rowTestStore, [32]byte) {
	t.Helper()
	store := &rowTestStore{database: &rowDatabase{rows: make(map[string][]byte)}}
	var lineage [32]byte
	lineage[0] = 31
	server, err := NewRowServer(19, bytes.Repeat([]byte{3}, 32), bytes.Repeat([]byte{4}, 32), store, lineage)
	if err != nil {
		t.Fatal(err)
	}
	t.Cleanup(server.Close)
	return server, store, lineage
}

func registerRowBeacon(t *testing.T, server *RowServer) (*Beacon, uint64, []byte) {
	t.Helper()
	pk, err := server.IdentityPK()
	if err != nil {
		t.Fatal(err)
	}
	ml, err := server.MLDSAPublicKey()
	if err != nil {
		t.Fatal(err)
	}
	beacon, err := NewBeacon(19, pk, ml)
	if err != nil {
		t.Fatal(err)
	}
	t.Cleanup(beacon.Close)
	request, err := beacon.GenerateRegistration()
	if err != nil {
		t.Fatal(err)
	}
	response, err := server.RegisterBeacon(request, []byte("registered"))
	if err != nil {
		t.Fatal(err)
	}
	plain, err := beacon.ProcessInitialMessage(response.Serialized)
	if err != nil || string(plain) != "registered" {
		t.Fatalf("registration: %q, %v", plain, err)
	}
	return beacon, response.KeyID, request
}

func TestRowBindingsRestartReplayAndSinglePeerWrite(t *testing.T) {
	server, store, lineage := newRowTestServer(t)
	beacon, kid, request := registerRowBeacon(t, server)
	_, _, _ = registerRowBeacon(t, server)
	before := store.database.rows
	ciphertext, err := server.EncryptToBeacon(kid, []byte("hello"))
	if err != nil {
		t.Fatal(err)
	}
	plain, err := beacon.DecryptServerMessage(ciphertext)
	if err != nil || string(plain) != "hello" {
		t.Fatalf("decrypt: %q %v", plain, err)
	}
	changed := 0
	for key, value := range before {
		if !bytes.Equal(value, store.database.rows[key]) {
			changed++
		}
	}
	if changed != 1 {
		t.Fatalf("changed %d rows", changed)
	}
	server.Close()
	restored, err := OpenRowServer(&rowTestStore{database: store.database}, lineage)
	if err != nil {
		t.Fatal(err)
	}
	defer restored.Close()
	message, err := beacon.EncryptToServer([]byte("inbound"))
	if err != nil {
		t.Fatal(err)
	}
	plain, err = restored.DecryptBeaconMessage(message)
	if err != nil || string(plain) != "inbound" {
		t.Fatalf("receive: %q %v", plain, err)
	}
	if _, err := restored.DecryptBeaconMessage(message); !errors.Is(err, ErrCrypto) {
		t.Fatalf("replay: %v", err)
	}
	if _, err := restored.RegisterBeacon(request, nil); !errors.Is(err, ErrCrypto) {
		t.Fatalf("registration replay: %v", err)
	}
}

func TestRowBindingsAuthenticatedMetadataAndCachedReceive(t *testing.T) {
	server, store, _ := newRowTestServer(t)
	first, firstID, _ := registerRowBeacon(t, server)
	second, secondID, _ := registerRowBeacon(t, server)
	outbound, err := server.EncryptToBeaconWithMetadata(firstID, []byte("outbound"))
	if err != nil {
		t.Fatal(err)
	}
	if outbound.KeyID != firstID || outbound.Seq != 2 {
		t.Fatalf("outbound metadata: %+v", outbound)
	}
	plain, err := first.DecryptServerMessage(outbound.Data)
	if err != nil || string(plain) != "outbound" {
		t.Fatalf("outbound data: %q %v", plain, err)
	}

	makeMessage := func(beacon *Beacon, value string) []byte {
		t.Helper()
		message, err := beacon.EncryptToServer([]byte(value))
		if err != nil {
			t.Fatal(err)
		}
		return message
	}
	older := makeMessage(first, "older")
	newer := makeMessage(first, "newer")
	other := makeMessage(second, "other peer")
	for _, test := range []struct {
		message []byte
		plain   string
		kid     uint64
		seq     uint64
	}{
		{newer, "newer", firstID, 2},
		{other, "other peer", secondID, 1},
		{older, "older", firstID, 1},
	} {
		value, err := server.DecryptBeaconMessageWithMetadata(test.message)
		if err != nil {
			t.Fatal(err)
		}
		if string(value.Data) != test.plain || value.KeyID != test.kid || value.Seq != test.seq {
			t.Fatalf("receive metadata: %+v; want peer %d sequence %d data %q", value, test.kid, test.seq, test.plain)
		}
	}
	if value, err := server.DecryptBeaconMessageWithMetadata(older); value != nil || !errors.Is(err, ErrCrypto) {
		t.Fatalf("replay released metadata: %+v %v", value, err)
	}
	store.failCommit = true
	if value, err := server.EncryptToBeaconWithMetadata(firstID, []byte("uncommitted")); value != nil || !errors.Is(err, errRowCommit) {
		t.Fatalf("failed commit released metadata: %+v %v", value, err)
	}
}

func TestRowBindingsRollbackUncertainCommitAndCallbackPanic(t *testing.T) {
	server, store, _ := newRowTestServer(t)
	beacon, _, _ := registerRowBeacon(t, server)
	message, err := beacon.EncryptToServer([]byte("receive"))
	if err != nil {
		t.Fatal(err)
	}
	before := store.database.rows
	store.failCommit = true
	plain, err := server.DecryptBeaconMessage(message)
	var persistence *PersistenceError
	if plain != nil || !errors.As(err, &persistence) || persistence.Code != StatusStorage || !errors.Is(err, errRowCommit) {
		t.Fatalf("failed commit: %q %v", plain, err)
	}
	if !reflect.DeepEqual(before, store.database.rows) || store.pending != nil {
		t.Fatal("failed commit changed database or left transaction open")
	}
	if _, err := server.DecryptBeaconMessage(nil); !errors.Is(err, ErrEmptyData) {
		t.Fatalf("stale native status replaced empty-input error: %v", err)
	}
	store.failCommit = false
	store.panicLoad = true
	if _, err := server.DecryptBeaconMessage(message); !errors.As(err, &persistence) || persistence.Cause == nil {
		t.Fatalf("panic: %v", err)
	}
	store.panicLoad = false
	store.failAfterCommit = true
	if plain, err := server.DecryptBeaconMessage(message); plain != nil || !errors.Is(err, errRowCommit) {
		t.Fatalf("uncertain commit: %q %v", plain, err)
	}
	store.failAfterCommit = false
	if _, err := server.DecryptBeaconMessage(message); !errors.Is(err, ErrCrypto) {
		t.Fatalf("consumption lost: %v", err)
	}
}

func TestRowBindingsConcurrentOwnersConsumeOnlyOnce(t *testing.T) {
	server, store, lineage := newRowTestServer(t)
	beacon, _, _ := registerRowBeacon(t, server)
	other, err := OpenRowServer(&rowTestStore{database: store.database}, lineage)
	if err != nil {
		t.Fatal(err)
	}
	defer other.Close()
	message, err := beacon.EncryptToServer([]byte("once"))
	if err != nil {
		t.Fatal(err)
	}
	results := make(chan error, 2)
	for _, owner := range []*RowServer{server, other} {
		go func(owner *RowServer) { _, err := owner.DecryptBeaconMessage(message); results <- err }(owner)
	}
	first, second := <-results, <-results
	if !((first == nil && errors.Is(second, ErrCrypto)) || (second == nil && errors.Is(first, ErrCrypto))) {
		t.Fatalf("results: %v, %v", first, second)
	}
}

func TestRowBindingsClosedAndInvalidConstruction(t *testing.T) {
	server, store, lineage := newRowTestServer(t)
	server.Close()
	for _, owner := range []*RowServer{nil, {}, server} {
		if _, err := owner.EncryptToBeacon(20, nil); !errors.Is(err, ErrClosed) {
			t.Fatalf("closed encrypt: %v", err)
		}
		if _, err := owner.RegisterBeacon(nil, nil); !errors.Is(err, ErrClosed) {
			t.Fatalf("closed registration: %v", err)
		}
		owner.Close()
	}
	if _, err := NewRowServer(19, []byte{1}, nil, store, lineage); !errors.Is(err, ErrSeedSize) {
		t.Fatalf("seed: %v", err)
	}
	if _, err := OpenRowServer(nil, lineage); err == nil {
		t.Fatal("nil store accepted")
	}
	if _, err := NewRowServer(19, nil, nil, store, lineage); err == nil {
		t.Fatal("existing namespace overwritten")
	}
}

func TestRowBindingsExplicitEmptyRegistrationResponseBurnsReplayMarker(t *testing.T) {
	server, _, _ := newRowTestServer(t)
	pk, _ := server.IdentityPK()
	ml, _ := server.MLDSAPublicKey()
	beacon, err := NewBeacon(19, pk, ml)
	if err != nil {
		t.Fatal(err)
	}
	defer beacon.Close()
	request, err := beacon.GenerateRegistration()
	if err != nil {
		t.Fatal(err)
	}
	if _, err := server.RegisterBeacon(request, []byte{}); !errors.Is(err, ErrCrypto) {
		t.Fatalf("empty response: %v", err)
	}
	if _, err := server.RegisterBeacon(request, nil); !errors.Is(err, ErrCrypto) {
		t.Fatalf("consumed registration reused: %v", err)
	}
}

func TestRowBindingsFailedBeginRollsBack(t *testing.T) {
	server, store, _ := newRowTestServer(t)
	beacon, kid, _ := registerRowBeacon(t, server)
	before := store.database.rows
	store.failBegin = true
	if _, err := server.EncryptToBeacon(kid, []byte("failed begin")); err == nil {
		t.Fatal("failed begin released output")
	}
	if store.pending != nil || !reflect.DeepEqual(before, store.database.rows) {
		t.Fatal("failed begin retained transaction or mutated state")
	}
	store.failBegin = false
	message, err := server.EncryptToBeacon(kid, []byte("retry"))
	if err != nil {
		t.Fatal(err)
	}
	plain, err := beacon.DecryptServerMessage(message)
	if err != nil || string(plain) != "retry" {
		t.Fatalf("retry: %q %v", plain, err)
	}
}

func TestRowBindingsEmptyStoredValueIsInvalidRatherThanAbsent(t *testing.T) {
	server, store, _ := newRowTestServer(t)
	_, kid, _ := registerRowBeacon(t, server)
	before := store.database.rows
	if _, err := server.EncryptToBeacon(kid, []byte("find peer row")); err != nil {
		t.Fatal(err)
	}
	var peerKey string
	for key, value := range before {
		if !bytes.Equal(value, store.database.rows[key]) {
			peerKey = key
		}
	}
	if peerKey == "" {
		t.Fatal("no changed peer row")
	}
	store.database.rows[peerKey] = []byte{}
	_, err := server.EncryptToBeacon(kid, []byte("corrupt row"))
	var persistence *PersistenceError
	if !errors.As(err, &persistence) || persistence.Code != StatusInvalidSnapshot {
		t.Fatalf("empty stored row: %v", err)
	}
}
