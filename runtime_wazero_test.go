// SPDX-License-Identifier: 0BSD

//go:build !cgo || beaconcrypt_wazero

package beaconcrypt

import (
	"bytes"
	"context"
	"encoding/binary"
	"errors"
	"fmt"
	"io"
	"strings"
	"testing"

	"github.com/tetratelabs/wazero/api"
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

type statusWasmFunction struct {
	api.Function
	module api.Module
	status uint32
}

func (function statusWasmFunction) Call(ctx context.Context, parameters ...uint64) ([]uint64, error) {
	result, err := function.Function.Call(ctx, parameters...)
	if err != nil {
		return nil, err
	}
	if len(result) != 1 || !function.module.Memory().WriteUint32Le(uint32(result[0]>>32), function.status) {
		return nil, errors.New("cannot inject response status")
	}
	return result, nil
}

func TestWasmResponseStatusRejectsReservedAndUnknownCodes(t *testing.T) {
	engine, err := sharedWasmEngine()
	if err != nil {
		t.Fatal(err)
	}
	for _, status := range []PersistenceStatus{StatusStorage, StatusCommitUnknown, StatusInvalidSession, 16, ^PersistenceStatus(0)} {
		t.Run(fmt.Sprintf("status=%d", status), func(t *testing.T) {
			instance, err := engine.construct(1, 19, nil, []byte{0}, nil)
			if err != nil {
				t.Fatal(err)
			}
			defer instance.close()
			instance.dispatch = statusWasmFunction{instance.dispatch, instance.module, uint32(status)}
			// An unknown operation normally returns a valid, payload-free error reply.
			output, err := instance.call(99, 0, nil, nil)
			if len(output.data) != 0 || len(output.state) != 0 {
				t.Fatal("error response released output")
			}
			if status == StatusStorage || status == StatusCommitUnknown {
				requirePersistenceStatus(t, err, status)
				if instance.closed || instance.module.IsClosed() {
					t.Fatal("known persistence status invalidated guest")
				}
			} else if !errors.Is(err, ErrCrypto) || !instance.closed || !instance.module.IsClosed() {
				t.Fatalf("reserved or unknown status did not invalidate guest: %v", err)
			}
		})
	}
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
				status = StatusStorage
			case "load-panic":
				store.panicLoad = true
				status = StatusStorage
			case "cas-error", "cas-panic":
				op, arg, extra, status = 12, 19, []byte{1, 0, 0, 0, 0}, StatusCommitUnknown
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

// replyWasmFunction injects an owned guest allocation, so malformed ABI bytes
// exercise the actual host parser and its terminal cleanup path.
type replyWasmFunction struct {
	api.Function
	module   api.Module
	allocate api.Function
	reply    []byte
}

func (function replyWasmFunction) Call(ctx context.Context, parameters ...uint64) ([]uint64, error) {
	if len(parameters) == 0 || parameters[0] < 25 || parameters[0] > 27 {
		return function.Function.Call(ctx, parameters...)
	}
	allocated, err := function.allocate.Call(ctx, uint64(len(function.reply)))
	if err != nil || len(allocated) != 1 || allocated[0] == 0 {
		return nil, fmt.Errorf("allocate injected response: %v", err)
	}
	ptr := uint32(allocated[0])
	if !function.module.Memory().Write(ptr, function.reply) {
		return nil, errors.New("cannot inject response bytes")
	}
	return []uint64{uint64(ptr)<<32 | uint64(len(function.reply))}, nil
}

func wasmSendReply(data, state []byte, keyID, sequence uint64) []byte {
	reply := make([]byte, 32+len(data)+len(state))
	binary.LittleEndian.PutUint32(reply[4:], 41)
	binary.LittleEndian.PutUint64(reply[8:], keyID)
	binary.LittleEndian.PutUint64(reply[16:], sequence)
	binary.LittleEndian.PutUint32(reply[24:], uint32(len(data)))
	binary.LittleEndian.PutUint32(reply[28:], uint32(len(state)))
	copy(reply[32:], data)
	copy(reply[32+len(data):], state)
	return reply
}

func TestWasmSendOutcomeParserRejectsMalformedRepliesAndInvalidatesOwner(t *testing.T) {
	cases := []struct {
		name  string
		op    uint32
		reply []byte
	}{
		{"missing-tag", 25, wasmSendReply(nil, nil, 0, 0)},
		{"unknown-tag", 25, wasmSendReply(nil, []byte{3}, 0, 0)},
		{"full-byte-unknown-tag", 25, wasmSendReply(nil, []byte{255}, 0, 0)},
		{"sent-no-payload", 25, wasmSendReply(nil, []byte{1}, 7, 1)},
		{"sent-zero-sequence", 25, wasmSendReply([]byte{9}, []byte{1}, 7, 0)},
		{"raw-extra-state", 25, wasmSendReply([]byte{9}, []byte{1, 9}, 7, 1)},
		{"json-extra-state", 27, wasmSendReply([]byte{9}, []byte{1, 9}, 7, 1)},
		{"update-missing-state", 26, wasmSendReply([]byte{9}, []byte{1}, 7, 1)},
	}
	for _, kind := range []byte{0, 2} {
		for _, invalid := range []struct {
			name  string
			data  []byte
			state []byte
			keyID uint64
			seq   uint64
		}{
			{"payload", []byte{9}, []byte{kind}, 0, 0},
			{"state", nil, []byte{kind, 9}, 0, 0},
			{"key-id", nil, []byte{kind}, 7, 0},
			{"sequence", nil, []byte{kind}, 0, 1},
		} {
			cases = append(cases, struct {
				name  string
				op    uint32
				reply []byte
			}{fmt.Sprintf("kind-%d/%s", kind, invalid.name), 26, wasmSendReply(invalid.data, invalid.state, invalid.keyID, invalid.seq)})
		}
	}
	badLength := wasmSendReply([]byte("private output"), []byte{1}, 7, 1)
	binary.LittleEndian.PutUint32(badLength[24:], ^uint32(0))
	cases = append(cases, struct {
		name  string
		op    uint32
		reply []byte
	}{"overflowing-data-length", 25, badLength})
	for _, scenario := range cases {
		t.Run(scenario.name, func(t *testing.T) {
			engine, err := sharedWasmEngine()
			if err != nil {
				t.Fatal(err)
			}
			instance, err := engine.construct(12, 19, nil, []byte{1, 0, 0, 0, 0}, &testSnapshotStore{})
			if err != nil {
				t.Fatal(err)
			}
			defer instance.close()
			instance.dispatch = replyWasmFunction{instance.dispatch, instance.module, instance.allocate, scenario.reply}
			output, err := instance.call(scenario.op, 0, nil, nil)
			if !errors.Is(err, ErrCrypto) || len(output.data) != 0 || len(output.state) != 0 || output.keyID != 0 || output.seq != 0 || output.handle != 0 {
				t.Fatalf("malformed send outcome released output: %+v, %v", output, err)
			}
			if !instance.closed || !instance.module.IsClosed() || instance.state.store != nil || instance.state.loaded != nil {
				t.Fatal("malformed send outcome retained guest or callback state")
			}
			if _, err := instance.call(25, 0, nil, nil); !errors.Is(err, ErrClosed) {
				t.Fatalf("malformed send outcome owner remained reusable: %v", err)
			}
		})
	}
}

func TestWasmSendOutcomeParserAcceptsCanonicalRepliesAndDetachesState(t *testing.T) {
	for _, scenario := range []struct {
		name  string
		op    uint32
		kind  SendOutcome
		data  []byte
		state []byte
		keyID uint64
		seq   uint64
	}{
		{"rejected", 25, SendRejected, nil, []byte{0}, 0, 0},
		{"consumed", 26, SendConsumedWithoutOutput, nil, []byte{2}, 0, 0},
		{"raw", 25, SendSent, []byte("ciphertext"), []byte{1}, 7, 1},
		{"update", 26, SendSent, []byte("ciphertext"), append([]byte{1}, []byte(`{"send_key":"secret"}`)...), 7, 1},
		{"json", 27, SendSent, []byte(`{"data":[9]}`), []byte{1}, 7, 1},
	} {
		t.Run(scenario.name, func(t *testing.T) {
			engine, err := sharedWasmEngine()
			if err != nil {
				t.Fatal(err)
			}
			instance, err := engine.construct(1, 19, nil, []byte{0}, nil)
			if err != nil {
				t.Fatal(err)
			}
			defer instance.close()
			instance.dispatch = replyWasmFunction{instance.dispatch, instance.module, instance.allocate, wasmSendReply(scenario.data, scenario.state, scenario.keyID, scenario.seq)}
			output, err := instance.call(scenario.op, 0, nil, nil)
			if err != nil {
				t.Fatal(err)
			}
			if instance.closed || instance.module.IsClosed() {
				t.Fatal("canonical send outcome invalidated guest")
			}
			result, err := decodeWasmSendResult(output)
			requireSendOutcome(t, result, err, scenario.kind)
			if !bytes.Equal(result.Data, scenario.data) || result.State != string(scenario.state[1:]) || result.KeyID != scenario.keyID || result.Seq != scenario.seq {
				t.Fatalf("canonical send outcome changed: %+v", result)
			}
			if !bytes.Equal(output.state, make([]byte, len(output.state))) {
				t.Fatal("decoded send result retained temporary outcome and secret state bytes")
			}
		})
	}
}
