// SPDX-License-Identifier: 0BSD

//go:build cgo && !beaconcrypt_wazero

package beaconcrypt

import (
	"errors"
	"runtime"
	"runtime/cgo"
	"strings"
	"testing"
)

func handleIsReleased(handle cgo.Handle) (released bool) {
	defer func() { released = recover() != nil }()
	_ = handle.Value()
	return false
}

func TestSnapshotCallbackLifetimeAndFailedConstructors(t *testing.T) {
	store := &testSnapshotStore{}
	server, err := NewServerWithStore(0, nil, nil, store)
	if err != nil {
		t.Fatal(err)
	}
	context := server.native.store
	runtime.GC()
	if context.handle.Value() != context {
		t.Fatal("live callback context was released")
	}
	server.Close()
	server.Close()
	if !handleIsReleased(context.handle) {
		t.Fatal("Close retained callback context")
	}
	for _, scenario := range []string{"occupied", "invalid-seed", "missing", "load-error", "load-panic", "cas-panic"} {
		t.Run(scenario, func(t *testing.T) {
			failedStore := &testSnapshotStore{}
			var code PersistenceStatus
			switch scenario {
			case "occupied":
				failedStore = store
				code = StatusStaleGeneration
			case "invalid-seed":
				code = StatusInitialization
			case "missing":
				code = StatusMissingSnapshot
			case "load-error":
				failedStore.loadError = errors.New("injected load error")
				code = StatusMissingSnapshot
			case "load-panic":
				failedStore.panicLoad = true
				code = StatusMissingSnapshot
			case "cas-panic":
				failedStore.panicCAS = true
				code = StatusStaleGeneration
			}
			context := newSnapshotStoreContext(failedStore)
			var failed *Server
			var err error
			if strings.HasPrefix(scenario, "load-") || scenario == "missing" {
				failed, err = restoreServerWithStoreContext(context)
			} else {
				var seed []byte
				if scenario == "invalid-seed" {
					seed = []byte{1}
				}
				failed, err = createServerWithStoreContext(0, seed, nil, context, nil)
			}
			requirePersistenceStatus(t, err, code)
			if failed != nil || !handleIsReleased(context.handle) {
				t.Fatal("failed constructor retained handle or callback context")
			}
			if strings.HasSuffix(scenario, "panic") {
				var persistenceErr *PersistenceError
				if !errors.As(err, &persistenceErr) || persistenceErr.Cause == nil || !strings.Contains(err.Error(), "panic") {
					t.Fatalf("callback panic lost its cause: %v", err)
				}
			}
		})
	}
}
