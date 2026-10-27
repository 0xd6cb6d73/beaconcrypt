// SPDX-License-Identifier: 0BSD
//go:build cgo && !beaconcrypt_wazero

package beaconcrypt

import (
	"bytes"
	"errors"
	"testing"
)

type cachedRowTestStore struct {
	*rowTestStore
	loads        int
	expectations int
	expectError  error
}

func (s *cachedRowTestStore) Load(key []byte) ([]byte, error) {
	s.loads++
	return s.rowTestStore.Load(key)
}
func (s *cachedRowTestStore) Expect(key, expected []byte) error {
	s.expectations++
	if s.expectError != nil {
		return s.expectError
	}
	actual := s.pending[string(key)]
	if (actual == nil) != (expected == nil) || !bytes.Equal(actual, expected) {
		return ErrRowConflict
	}
	return nil
}
func (s *cachedRowTestStore) reset() { s.loads = 0; s.expectations = 0 }

func newCachedRowTestServer(t *testing.T, capacity uint) (*CachedRowServer, *cachedRowTestStore, [32]byte) {
	t.Helper()
	store := &cachedRowTestStore{rowTestStore: &rowTestStore{database: &rowDatabase{rows: make(map[string][]byte)}}}
	var lineage [32]byte
	lineage[0] = 71
	server, err := NewCachedRowServer(19, bytes.Repeat([]byte{3}, 32), bytes.Repeat([]byte{4}, 32), store, lineage, capacity)
	if err != nil {
		t.Fatal(err)
	}
	t.Cleanup(server.Close)
	return server, store, lineage
}

func TestCachedRowBindingsWarmExpectationConflictAndUnknownCommit(t *testing.T) {
	server, store, lineage := newCachedRowTestServer(t, 2)
	_, kid, _ := registerRowBeacon(t, &server.RowServer)
	if count, err := server.CachedPeerCount(); err != nil || count != 0 {
		t.Fatalf("registration cache: %d %v", count, err)
	}
	store.reset()
	first, err := server.EncryptToBeaconWithMetadata(kid, []byte("cold"))
	if err != nil || first.Seq != 2 || store.loads != 1 || store.expectations != 0 {
		t.Fatalf("cold read: %+v %v loads=%d expectations=%d", first, err, store.loads, store.expectations)
	}
	store.reset()
	second, err := server.EncryptToBeaconWithMetadata(kid, []byte("warm"))
	if err != nil || second.Seq != 3 || store.loads != 0 || store.expectations != 1 {
		t.Fatalf("warm expectation: %+v %v loads=%d expectations=%d", second, err, store.loads, store.expectations)
	}
	other, err := OpenRowServer(&rowTestStore{database: store.database}, lineage)
	if err != nil {
		t.Fatal(err)
	}
	defer other.Close()
	if _, err := other.EncryptToBeacon(kid, []byte("other worker")); err != nil {
		t.Fatal(err)
	}
	value, err := server.EncryptToBeaconWithMetadata(kid, []byte("stale"))
	var persistence *PersistenceError
	if value != nil || !errors.As(err, &persistence) || persistence.Code != StatusStaleGeneration || !errors.Is(err, ErrRowConflict) {
		t.Fatalf("stale cache: %+v %v", value, err)
	}
	if count, _ := server.CachedPeerCount(); count != 0 {
		t.Fatalf("conflict retained %d peers", count)
	}
	store.reset()
	fresh, err := server.EncryptToBeaconWithMetadata(kid, []byte("fresh"))
	if err != nil || fresh.Seq != 5 || store.loads != 1 {
		t.Fatalf("conflict reload: %+v %v loads=%d", fresh, err, store.loads)
	}
	store.failAfterCommit = true
	if value, err := server.EncryptToBeaconWithMetadata(kid, []byte("unknown")); value != nil || !errors.Is(err, errRowCommit) {
		t.Fatalf("unknown commit: %+v %v", value, err)
	}
	store.failAfterCommit = false
	if count, _ := server.CachedPeerCount(); count != 0 {
		t.Fatalf("unknown commit retained %d peers", count)
	}
	store.reset()
	next, err := server.EncryptToBeaconWithMetadata(kid, []byte("after unknown"))
	if err != nil || next.Seq != 7 || store.loads != 1 {
		t.Fatalf("unknown reload: %+v %v loads=%d", next, err, store.loads)
	}
	store.expectError = errors.New("expectation transport failed")
	if _, err := server.EncryptToBeacon(kid, []byte("failure")); !errors.Is(err, store.expectError) {
		t.Fatalf("expectation cause: %v", err)
	}
}

func TestCachedRowBindingsCompositionCapacityAndFallback(t *testing.T) {
	server, store, lineage := newCachedRowTestServer(t, 1)
	beacon, kid, _ := registerRowBeacon(t, &server.RowServer)
	if capacity, err := server.CacheCapacity(); err != nil || capacity != 1 {
		t.Fatalf("capacity: %d %v", capacity, err)
	}
	if _, err := server.EncryptToBeacon(kid, []byte("warm")); err != nil {
		t.Fatal(err)
	}
	message, err := beacon.EncryptToServer([]byte("receive"))
	if err != nil {
		t.Fatal(err)
	}
	var escaped *RowSession
	store.reset()
	output, err := server.Transaction(func(session *RowSession) ([]byte, error) {
		escaped = session
		transition, err := session.DecryptBeaconMessage(message)
		if err != nil {
			return nil, err
		}
		if transition.Message == nil || transition.Message.KeyID != kid || transition.Message.Seq != 1 {
			return nil, errors.New("cached receive metadata mismatch")
		}
		if err := session.Store([]byte("result"), transition.Message.Data); err != nil {
			return nil, err
		}
		return transition.Message.Data, nil
	})
	if err != nil || string(output) != "receive" || store.loads != 0 || store.expectations != 1 {
		t.Fatalf("cached composition: %q %v loads=%d expectations=%d", output, err, store.loads, store.expectations)
	}
	if _, err := escaped.Load(nil); !errors.Is(err, ErrRowSessionExpired) {
		t.Fatalf("escaped cache session: %v", err)
	}
	if err := server.ClearCache(); err != nil {
		t.Fatal(err)
	}
	if count, _ := server.CachedPeerCount(); count != 0 {
		t.Fatal("clear cache retained peer")
	}
	zero, err := OpenCachedRowServer(store, lineage, 0)
	if err != nil {
		t.Fatal(err)
	}
	defer zero.Close()
	store.reset()
	for range 2 {
		if _, err := zero.EncryptToBeacon(kid, []byte("uncached")); err != nil {
			t.Fatal(err)
		}
	}
	if count, _ := zero.CachedPeerCount(); count != 0 || store.loads != 2 || store.expectations != 0 {
		t.Fatalf("zero capacity: count=%d loads=%d expectations=%d", count, store.loads, store.expectations)
	}
	fallback, err := OpenCachedRowServer(&rowTestStore{database: store.database}, lineage, 1)
	if err != nil {
		t.Fatal(err)
	}
	defer fallback.Close()
	for range 2 {
		if _, err := fallback.EncryptToBeacon(kid, []byte("fallback")); err != nil {
			t.Fatal(err)
		}
	}
	if count, _ := fallback.CachedPeerCount(); count != 1 {
		t.Fatalf("fallback cache population: %d", count)
	}
}
