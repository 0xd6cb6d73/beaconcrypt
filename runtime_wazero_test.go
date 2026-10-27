// SPDX-License-Identifier: 0BSD

//go:build !cgo || beaconcrypt_wazero

package beaconcrypt

import (
	"bytes"
	"errors"
	"io"
	"strings"
	"testing"
)

func testWasmEngine(t *testing.T, entropy io.Reader) *wasmEngine {
	t.Helper()
	engine, err := newWasmEngine(wasmModule, entropy)
	if err != nil {
		t.Fatal(err)
	}
	t.Cleanup(func() { _ = engine.runtime.Close(engine.ctx) })
	return engine
}

type failedWasmEntropy struct{}

func (failedWasmEntropy) Read([]byte) (int, error) {
	return 0, errors.New("injected entropy failure")
}

func TestWasmInitializationRejectsInvalidModuleAndEntropy(t *testing.T) {
	if engine, err := newWasmEngine([]byte("invalid Wasm"), bytes.NewReader(nil)); engine != nil || err == nil {
		t.Fatal("invalid Wasm module was accepted")
	}
	if engine, err := newWasmEngine(wasmModule, nil); engine != nil || err == nil {
		t.Fatal("nil entropy source was accepted")
	}
	missingExport := bytes.Replace(wasmModule, []byte("bc_abi_version"), []byte("bc_bad_version"), 1)
	if engine, err := newWasmEngine(missingExport, bytes.NewReader(nil)); engine != nil || err == nil {
		t.Fatal("module missing its ABI version export was accepted")
	}
	engine := testWasmEngine(t, failedWasmEntropy{})
	if instance, err := engine.construct(1, 19, nil, []byte{0}, nil); instance != nil || err == nil {
		t.Fatal("failed entropy returned a live server")
	}
}

func TestWasmTrapsAndCleanupFailuresSuppressOutputAndReleaseCallbacks(t *testing.T) {
	// Replacing a cached function with one of an incompatible signature injects
	// a deterministic wazero call failure without modifying the shipped guest.
	for _, stage := range []string{"allocate", "dispatch", "release"} {
		t.Run(stage, func(t *testing.T) {
			engine, err := sharedWasmEngine()
			if err != nil {
				t.Fatal(err)
			}
			store := &testSnapshotStore{}
			instance, err := engine.construct(12, 19, nil, []byte{1, 0, 0, 0, 0}, store)
			if err != nil {
				t.Fatal(err)
			}
			defer instance.close()
			switch stage {
			case "allocate":
				instance.allocate = instance.dispatch
			case "dispatch":
				instance.dispatch = instance.release
			case "release":
				instance.release = instance.allocate
			}
			// Even a successful guest-side query must not release its result
			// when wiping its temporary allocations fails.
			op, input := uint32(3), []byte(nil)
			if stage == "allocate" {
				op, input = 8, []byte("input")
			}
			result, err := instance.call(op, 0, input, nil)
			if !errors.Is(err, ErrCrypto) || len(result.data) != 0 || len(result.state) != 0 {
				t.Fatalf("failure released output: %+v, %v", result, err)
			}
			if !instance.closed || !instance.module.IsClosed() || instance.state.store != nil || instance.state.loaded != nil {
				t.Fatal("terminal call failure retained an instance or callback state")
			}
			if _, err := instance.call(3, 0, nil, nil); !errors.Is(err, ErrClosed) {
				t.Fatalf("terminal instance reused: %v", err)
			}
		})
	}
}

func TestWasmObservedModuleClosureReleasesCallbacks(t *testing.T) {
	engine, err := sharedWasmEngine()
	if err != nil {
		t.Fatal(err)
	}
	instance, err := engine.construct(12, 19, nil, []byte{1, 0, 0, 0, 0}, &testSnapshotStore{})
	if err != nil {
		t.Fatal(err)
	}
	defer instance.close()
	if err := instance.module.Close(instance.ctx); err != nil {
		t.Fatal(err)
	}
	if _, err := instance.call(3, 0, nil, nil); !errors.Is(err, ErrClosed) {
		t.Fatalf("closed module returned %v", err)
	}
	if instance.state.store != nil || instance.state.loaded != nil || !instance.closed {
		t.Fatal("observed module closure retained callbacks")
	}
}

func TestWasmFailedConstructorsReleaseStoreAndPreserveCause(t *testing.T) {
	engine, err := sharedWasmEngine()
	if err != nil {
		t.Fatal(err)
	}
	for _, scenario := range []string{"missing", "load-error", "load-panic", "cas-error", "cas-panic"} {
		t.Run(scenario, func(t *testing.T) {
			store := &testSnapshotStore{}
			op, arg, extra := uint32(13), uint64(1), []byte(nil)
			status := StatusMissingSnapshot
			sentinel := errors.New("injected store failure")
			switch scenario {
			case "load-error":
				store.loadError = sentinel
			case "load-panic":
				store.panicLoad = true
			case "cas-error", "cas-panic":
				op, arg, extra, status = 12, 19, []byte{1, 0, 0, 0, 0}, StatusStaleGeneration
				store.casError = sentinel
				store.panicCAS = scenario == "cas-panic"
			}
			instance, err := engine.instantiate(store)
			if err != nil {
				t.Fatal(err)
			}
			defer instance.close()
			_, err = instance.call(op, arg, nil, extra)
			failure := requirePersistenceStatus(t, err, status)
			if strings.HasSuffix(scenario, "error") && !errors.Is(failure, sentinel) {
				t.Fatalf("callback error cause lost: %v", failure)
			}
			if strings.HasSuffix(scenario, "panic") && (failure.Cause == nil || !strings.Contains(failure.Error(), "panic")) {
				t.Fatalf("callback panic cause lost: %v", failure)
			}
			if instance.state.store != nil || instance.state.loaded != nil {
				t.Fatal("failed Rust constructor retained host store")
			}
		})
	}
}

func TestWasmSnapshotValidatorRecoversAfterTerminalFailure(t *testing.T) {
	engine := testWasmEngine(t, bytes.NewReader(bytes.Repeat([]byte{0x49}, 4096)))
	server := newServer(t)
	snapshot, err := server.ExportState()
	if err != nil {
		t.Fatal(err)
	}
	expected, err := engine.inspect(snapshot, nil, false)
	if err != nil {
		t.Fatal(err)
	}
	failed := engine.helper
	failed.allocate = failed.dispatch
	if _, err := engine.inspect(snapshot, nil, false); !errors.Is(err, ErrCrypto) {
		t.Fatalf("injected validator failure: %v", err)
	}
	actual, err := engine.inspect(snapshot, nil, false)
	if err != nil || actual != expected || engine.helper == failed {
		t.Fatalf("validator did not recover with a new instance: %v", err)
	}
}
