// SPDX-License-Identifier: 0BSD

package beaconcrypt

import (
	"bytes"
	"errors"
	"fmt"
	"runtime"
	"sync"
	"testing"
)

// This store models one trusted storage domain. Production stores must provide
// the same atomicity and additionally make successful writes crash durable.
type testSnapshotStore struct {
	mu          sync.Mutex
	snapshot    []byte
	head        *SnapshotHead
	casCalls    int
	rejectCAS   bool
	casError    error
	loadError   error
	panicCAS    bool
	panicLoad   bool
	staleLoad   []byte
	loadStarted chan struct{}
	loadRelease chan struct{}
}

func (store *testSnapshotStore) Load() ([]byte, error) {
	store.mu.Lock()
	if store.panicLoad {
		store.mu.Unlock()
		panic("injected load panic")
	}
	snapshot := bytes.Clone(store.snapshot)
	if store.staleLoad != nil {
		snapshot = bytes.Clone(store.staleLoad)
	}
	err, started, release := store.loadError, store.loadStarted, store.loadRelease
	store.mu.Unlock()
	if started != nil {
		started <- struct{}{}
		<-release
	}
	return snapshot, err
}

func (store *testSnapshotStore) CompareAndSwap(expected *SnapshotHead, replacement []byte) (bool, error) {
	store.mu.Lock()
	defer store.mu.Unlock()
	store.casCalls++
	if store.panicCAS {
		panic("injected CAS panic")
	}
	if store.rejectCAS || store.casError != nil {
		return false, store.casError
	}
	if (store.head == nil) != (expected == nil) || (expected != nil && *expected != *store.head) {
		return false, nil
	}
	head, err := ValidateSnapshotSuccessor(replacement, expected)
	if err != nil {
		return false, err
	}
	// Callback inputs are copied to Go memory and may safely be retained.
	store.snapshot = replacement
	store.head = &head
	return true, nil
}

func (store *testSnapshotStore) current() ([]byte, SnapshotHead, int) {
	store.mu.Lock()
	defer store.mu.Unlock()
	var head SnapshotHead
	if store.head != nil {
		head = *store.head
	}
	return bytes.Clone(store.snapshot), head, store.casCalls
}

func newPersistentPair(t *testing.T) (*Server, *Beacon, uint64, *testSnapshotStore) {
	t.Helper()
	store := &testSnapshotStore{}
	server, err := NewServerWithStore(0, bytes.Repeat([]byte{9}, 32), nil, store)
	if err != nil {
		t.Fatal(err)
	}
	t.Cleanup(server.Close)
	pk, err := server.IdentityPK()
	if err != nil {
		t.Fatal(err)
	}
	beacon := newBeacon(t, server, pk)
	response := registerBeacon(t, server, beacon)
	return server, beacon, response.KeyID, store
}

func requirePersistenceStatus(t *testing.T, err error, code PersistenceStatus) *PersistenceError {
	t.Helper()
	var persistenceErr *PersistenceError
	if !errors.As(err, &persistenceErr) || persistenceErr.Code != code {
		t.Fatalf("got error %v, want persistence status %d", err, code)
	}
	return persistenceErr
}

func TestPersistentServerCommitsBeforeReturnAndRestoreClaimsGeneration(t *testing.T) {
	store := &testSnapshotStore{}
	lineage := [32]byte{27}
	server, err := NewServerWithStoreAndLineage(0, bytes.Repeat([]byte{1}, 32), nil, store, lineage)
	if err != nil {
		t.Fatal(err)
	}
	t.Cleanup(server.Close)
	initial, err := server.Head()
	if err != nil {
		t.Fatal(err)
	}
	snapshot, stored, calls := store.current()
	if initial != stored || initial.Generation != 0 || initial.Lineage != lineage || calls != 1 {
		t.Fatalf("initial owner not committed: owner=%v store=%v calls=%d", initial, stored, calls)
	}
	parsed, err := ParseSnapshotHead(snapshot)
	if err != nil || parsed != initial {
		t.Fatalf("snapshot head: %v %v", parsed, err)
	}
	if _, err := ValidateSnapshotSuccessor(snapshot, nil); err != nil {
		t.Fatal(err)
	}
	if _, err := ValidateSnapshotSuccessor(snapshot, &initial); err == nil {
		t.Fatal("snapshot accepted as its own successor")
	}
	pk, err := server.IdentityPK()
	if err != nil {
		t.Fatal(err)
	}
	beacon := newBeacon(t, server, pk)
	registration := registerBeacon(t, server, beacon)
	before, err := server.Head()
	if err != nil || before.Generation <= initial.Generation {
		t.Fatalf("registration did not commit: %v %v", before, err)
	}
	ciphertext, err := server.EncryptToBeacon(registration.KeyID, []byte("committed output"))
	if err != nil {
		t.Fatal(err)
	}
	_, stored, _ = store.current()
	owner, err := server.Head()
	if err != nil || owner != stored || owner.Generation != before.Generation+1 {
		t.Fatalf("send escaped before its commit: %v %v %v", owner, stored, err)
	}
	if plaintext, err := beacon.DecryptServerMessage(ciphertext); err != nil || string(plaintext) != "committed output" {
		t.Fatalf("send output: %q %v", plaintext, err)
	}
	server.Close()
	restored, err := RestoreServer(store)
	if err != nil {
		t.Fatal(err)
	}
	t.Cleanup(restored.Close)
	activated, err := restored.Head()
	if err != nil || activated.Generation != owner.Generation+1 || activated.Lineage != owner.Lineage {
		t.Fatalf("restoration did not claim generation: %v %v", activated, err)
	}
	_, stored, _ = store.current()
	if activated != stored {
		t.Fatal("activation returned before durable publication")
	}
	frame, err := beacon.EncryptToServer([]byte("after restore"))
	if err != nil {
		t.Fatal(err)
	}
	plaintext, err := restored.DecryptBeaconMessage(frame)
	if err != nil || string(plaintext) != "after restore" {
		t.Fatalf("restored receive: %q %v", plaintext, err)
	}
	_, stored, _ = store.current()
	if stored.Generation != activated.Generation+1 {
		t.Fatal("receive output escaped before commit")
	}
}

func TestPersistentServerCASFailureSuppressesEveryOutputAndPoisons(t *testing.T) {
	for _, operation := range []string{"send", "send-state", "send-json", "receive", "receive-state", "receive-json"} {
		t.Run(operation, func(t *testing.T) {
			server, beacon, kid, store := newPersistentPair(t)
			before, err := server.Head()
			if err != nil {
				t.Fatal(err)
			}
			frame, err := beacon.EncryptToServer([]byte("must stay private"))
			if err != nil {
				t.Fatal(err)
			}
			storeError := errors.New("durable storage unavailable")
			store.mu.Lock()
			store.casError = storeError
			store.mu.Unlock()
			switch operation {
			case "send":
				var output []byte
				output, err = server.EncryptToBeacon(kid, []byte("must stay private"))
				if output != nil {
					t.Fatal("ciphertext escaped failed CAS")
				}
			case "send-state":
				var output *EncryptState
				output, err = server.EncryptAndUpdate(kid, []byte("must stay private"))
				if output != nil {
					t.Fatal("send update escaped failed CAS")
				}
			case "send-json":
				var output string
				output, err = server.EncryptAndUpdateJSON(kid, []byte("must stay private"))
				if output != "" {
					t.Fatal("send JSON escaped failed CAS")
				}
			case "receive":
				var output []byte
				output, err = server.DecryptBeaconMessage(frame)
				if output != nil {
					t.Fatal("plaintext escaped failed CAS")
				}
			case "receive-state":
				var output *EncryptState
				output, err = server.DecryptAndUpdate(frame)
				if output != nil {
					t.Fatal("receive update escaped failed CAS")
				}
			case "receive-json":
				var output string
				output, err = server.DecryptAndUpdateJSON(frame)
				if output != "" {
					t.Fatal("receive JSON escaped failed CAS")
				}
			}
			requirePersistenceStatus(t, err, StatusStaleGeneration)
			if !errors.Is(err, storeError) || !server.IsPoisoned() {
				t.Fatalf("store error or poison lost: %v", err)
			}
			after, err := server.Head()
			if err != nil || before != after {
				t.Fatal("failed commit changed committed head")
			}
			output, err := server.EncryptToBeacon(kid, []byte("poisoned"))
			requirePersistenceStatus(t, err, StatusPoisoned)
			if output != nil {
				t.Fatal("poisoned owner released output")
			}
		})
	}
}

func TestPersistentReceiveRejectionDoesNotCallStoreOrAdvanceHead(t *testing.T) {
	server, beacon, _, store := newPersistentPair(t)
	frame, err := beacon.EncryptToServer([]byte("retry me"))
	if err != nil {
		t.Fatal(err)
	}
	corrupt := corruptAEADCiphertext(t, frame)
	beforeBytes, before, calls := store.current()
	for _, receive := range []func([]byte) error{
		func(frame []byte) error { _, err := server.DecryptBeaconMessage(frame); return err },
		func(frame []byte) error { _, err := server.DecryptAndUpdate(frame); return err },
		func(frame []byte) error { _, err := server.DecryptAndUpdateJSON(frame); return err },
	} {
		if err := receive(corrupt); !errors.Is(err, ErrCrypto) {
			t.Fatalf("rejection changed legacy error: %v", err)
		}
	}
	afterBytes, after, afterCalls := store.current()
	if before != after || !bytes.Equal(beforeBytes, afterBytes) || calls != afterCalls || server.IsPoisoned() {
		t.Fatal("ordinary rejection touched durable state")
	}
	if output, err := server.DecryptBeaconMessage(frame); err != nil || string(output) != "retry me" {
		t.Fatalf("rejected receive was not retryable: %q %v", output, err)
	}
}

func TestPersistentServerStaleLoadAndOwnerCannotPublish(t *testing.T) {
	server, _, kid, store := newPersistentPair(t)
	oldSnapshot, _, _ := store.current()
	if _, err := server.EncryptToBeacon(kid, []byte("advance")); err != nil {
		t.Fatal(err)
	}
	store.mu.Lock()
	store.staleLoad = oldSnapshot
	store.mu.Unlock()
	stale, err := RestoreServer(store)
	requirePersistenceStatus(t, err, StatusStaleGeneration)
	if stale != nil {
		t.Fatal("stale load activated")
	}
	if snapshot, err := server.ExportState(); snapshot != nil {
		t.Fatal("owner exported stale store bytes")
	} else {
		requirePersistenceStatus(t, err, StatusStaleGeneration)
	}
	store.mu.Lock()
	store.staleLoad = nil
	store.mu.Unlock()
	newOwner, err := RestoreServer(store)
	if err != nil {
		t.Fatal(err)
	}
	t.Cleanup(newOwner.Close)
	if output, err := server.EncryptToBeacon(kid, []byte("stale owner")); output != nil {
		t.Fatal("stale owner released ciphertext")
	} else {
		requirePersistenceStatus(t, err, StatusStaleGeneration)
	}
	if !server.IsPoisoned() || newOwner.IsPoisoned() {
		t.Fatal("stale-owner fencing affected wrong owner")
	}
}

func TestPersistentRestorersRaceOnOneAuthoritativeHead(t *testing.T) {
	store := &testSnapshotStore{}
	initial, err := NewServerWithStore(0, nil, nil, store)
	if err != nil {
		t.Fatal(err)
	}
	initial.Close()
	store.mu.Lock()
	store.loadStarted = make(chan struct{}, 2)
	store.loadRelease = make(chan struct{})
	started, release := store.loadStarted, store.loadRelease
	store.mu.Unlock()
	type result struct {
		server *Server
		err    error
	}
	results := make(chan result, 2)
	for i := 0; i < 2; i++ {
		go func() {
			server, err := RestoreServer(store)
			results <- result{server, err}
		}()
	}
	<-started
	<-started
	close(release)
	winners := 0
	for i := 0; i < 2; i++ {
		result := <-results
		if result.err == nil {
			winners++
			result.server.Close()
		} else {
			requirePersistenceStatus(t, result.err, StatusStaleGeneration)
		}
	}
	if winners != 1 {
		t.Fatalf("got %d live owners, want one", winners)
	}
}

type stackPressureSnapshotStore struct {
	*testSnapshotStore
}

func (store stackPressureSnapshotStore) Load() ([]byte, error) {
	growSnapshotCallbackStack(64)
	return store.testSnapshotStore.Load()
}

func (store stackPressureSnapshotStore) CompareAndSwap(expected *SnapshotHead, replacement []byte) (bool, error) {
	growSnapshotCallbackStack(64)
	return store.testSnapshotStore.CompareAndSwap(expected, replacement)
}

//go:noinline
func growSnapshotCallbackStack(depth int) byte {
	var padding [4096]byte
	for i := range padding {
		padding[i] = byte(i + depth)
	}
	var child byte
	if depth == 0 {
		runtime.GC()
	} else {
		child = growSnapshotCallbackStack(depth - 1)
	}
	result := padding[depth%len(padding)] ^ child
	runtime.KeepAlive(&padding)
	return result
}

// Constructors must keep callback tokens as integers while Go can scan or copy
// their stacks. Load and CAS may allocate, grow the stack and run a collection.
func TestSnapshotConstructorsAcrossCallbackStackGrowth(t *testing.T) {
	for _, explicitLineage := range []bool{false, true} {
		t.Run(fmt.Sprintf("lineage=%v", explicitLineage), func(t *testing.T) {
			for iteration := 0; iteration < 4; iteration++ {
				store := stackPressureSnapshotStore{&testSnapshotStore{}}
				done := make(chan error, 1)
				go func() {
					var server *Server
					var err error
					if explicitLineage {
						server, err = NewServerWithStoreAndLineage(19, nil, nil, store, [32]byte{1})
					} else {
						server, err = NewServerWithStore(19, nil, nil, store)
					}
					if err != nil {
						done <- err
						return
					}
					server.Close()
					done <- nil
				}()
				if err := <-done; err != nil {
					t.Fatal(err)
				}
				// Restore starts on a fresh small stack as well.
				go func() {
					restored, err := RestoreServer(store)
					if err == nil {
						restored.Close()
					}
					done <- err
				}()
				if err := <-done; err != nil {
					t.Fatal(err)
				}
			}
		})
	}
}

func TestSnapshotHelpersRejectMalformedAndIncorrectParents(t *testing.T) {
	for _, snapshot := range [][]byte{nil, {}, []byte("invalid envelope")} {
		if _, err := ParseSnapshotHead(snapshot); err == nil {
			t.Fatal("malformed envelope accepted")
		}
	}
	store := &testSnapshotStore{}
	server, err := NewServerWithStore(0, nil, nil, store)
	if err != nil {
		t.Fatal(err)
	}
	server.Close()
	previousBytes, previous, _ := store.current()
	restored, err := RestoreServer(store)
	if err != nil {
		t.Fatal(err)
	}
	defer restored.Close()
	currentBytes, current, _ := store.current()
	if head, err := ValidateSnapshotSuccessor(currentBytes, &previous); err != nil || head != current {
		t.Fatalf("valid parent rejected: %v %v", head, err)
	}
	for _, mutate := range []func(*SnapshotHead){
		func(head *SnapshotHead) { head.Lineage[0] ^= 1 },
		func(head *SnapshotHead) { head.Generation++ },
		func(head *SnapshotHead) { head.Digest[0] ^= 1 },
	} {
		wrong := previous
		mutate(&wrong)
		_, err := ValidateSnapshotSuccessor(currentBytes, &wrong)
		requirePersistenceStatus(t, err, StatusStaleGeneration)
	}
	if _, err := ValidateSnapshotSuccessor(previousBytes, &previous); err == nil {
		t.Fatal("self-parent accepted")
	}
}
