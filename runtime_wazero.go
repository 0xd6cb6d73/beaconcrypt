// SPDX-License-Identifier: 0BSD

//go:build !cgo || beaconcrypt_wazero

package beaconcrypt

import (
	"bytes"
	"context"
	"crypto/rand"
	_ "embed"
	"encoding/binary"
	"errors"
	"fmt"
	"io"
	"runtime"
	"slices"
	"sync"

	"github.com/tetratelabs/wazero"
	"github.com/tetratelabs/wazero/api"
	"github.com/tetratelabs/wazero/imports/wasi_snapshot_preview1"
)

// The release bundle supplies this generated file. Build it from source with
// scripts/build-wasm.sh; consumers do not need a Rust or C toolchain.
//
//go:embed internal/wasm/beaconcrypt.wasm
var wasmModule []byte

const wasmABIVersion = 1
const wasmMemoryPages = 4096 // 256 MiB per endpoint, including temporary buffers.

type wasmEngine struct {
	ctx      context.Context
	runtime  wazero.Runtime
	compiled wazero.CompiledModule
	entropy  io.Reader
	helperMu sync.Mutex
	helper   *wasmInstance
}

var defaultWasm struct {
	once   sync.Once
	engine *wasmEngine
	err    error
}

func sharedWasmEngine() (*wasmEngine, error) {
	defaultWasm.once.Do(func() {
		defaultWasm.engine, defaultWasm.err = newWasmEngine(wasmModule, rand.Reader)
	})
	return defaultWasm.engine, defaultWasm.err
}

// Entropy injection is private and used only by failure tests. A production
// instance always receives crypto/rand before any guest constructor can run.
func newWasmEngine(module []byte, entropy io.Reader) (*wasmEngine, error) {
	if entropy == nil {
		return nil, errors.New("beaconcrypt: nil WASM entropy source")
	}
	ctx := context.Background()
	r := wazero.NewRuntimeWithConfig(ctx, wazero.NewRuntimeConfig().WithMemoryLimitPages(wasmMemoryPages))
	e := &wasmEngine{ctx: ctx, runtime: r, entropy: entropy}
	fail := func(err error) (*wasmEngine, error) { _ = r.Close(ctx); return nil, err }
	if _, err := wasi_snapshot_preview1.Instantiate(ctx, r); err != nil {
		return fail(err)
	}
	b := r.NewHostModuleBuilder("beaconcrypt_host")
	b.NewFunctionBuilder().WithFunc(wasmSnapshotLoad).Export("snapshot_load")
	b.NewFunctionBuilder().WithFunc(wasmSnapshotCAS).Export("snapshot_cas")
	b.NewFunctionBuilder().WithFunc(wasmSnapshotDestroy).Export("snapshot_destroy")
	if _, err := b.Instantiate(ctx); err != nil {
		return fail(err)
	}
	compiled, err := r.CompileModule(ctx, module)
	if err != nil {
		return fail(err)
	}
	if err := validateWasmABI(compiled); err != nil {
		return fail(err)
	}
	e.compiled = compiled
	return e, nil
}

func validateWasmABI(module wazero.CompiledModule) error {
	type signature struct{ params, results []api.ValueType }
	i32, i64 := api.ValueTypeI32, api.ValueTypeI64
	required := map[string]signature{
		"bc_abi_version":      {nil, []api.ValueType{i32}},
		"bc_max_message_size": {nil, []api.ValueType{i32}},
		"bc_alloc":            {[]api.ValueType{i32}, []api.ValueType{i32}},
		"bc_free":             {[]api.ValueType{i32, i32}, nil},
		"bc_call":             {[]api.ValueType{i32, i32, i64, i32, i32, i32, i32}, []api.ValueType{i64}},
	}
	exports := module.ExportedFunctions()
	for name, expected := range required {
		actual := exports[name]
		if actual == nil || !slices.Equal(actual.ParamTypes(), expected.params) || !slices.Equal(actual.ResultTypes(), expected.results) {
			return fmt.Errorf("beaconcrypt: incompatible WASM function %s", name)
		}
	}
	if module.ExportedMemories()["memory"] == nil || len(module.ImportedMemories()) != 0 {
		return errors.New("beaconcrypt: incompatible WASM linear memory")
	}
	return nil
}

type wasmBridgeKey struct{}

type wasmCallbackState struct {
	store       SnapshotStore
	err         error
	loaded      []byte
	loadPending bool
}

func (s *wasmCallbackState) clearLoad() {
	clear(s.loaded)
	s.loaded = nil
	s.loadPending = false
}

func (s *wasmCallbackState) setError(err error) {
	if s.err == nil {
		s.err = err
	}
}

type wasmInstance struct {
	mu       sync.Mutex
	ctx      context.Context
	module   api.Module
	allocate api.Function
	dispatch api.Function
	release  api.Function
	state    *wasmCallbackState
	handle   uint32
	closed   bool
}

func (e *wasmEngine) instantiate(store SnapshotStore) (*wasmInstance, error) {
	state := &wasmCallbackState{store: store}
	ctx := context.WithValue(e.ctx, wasmBridgeKey{}, state)
	config := wazero.NewModuleConfig().WithName("").WithRandSource(e.entropy).WithStartFunctions("_initialize")
	module, err := e.runtime.InstantiateModule(ctx, e.compiled, config)
	if err != nil {
		state.store = nil
		return nil, err
	}
	i := &wasmInstance{ctx: ctx, module: module, state: state,
		allocate: module.ExportedFunction("bc_alloc"), dispatch: module.ExportedFunction("bc_call"), release: module.ExportedFunction("bc_free")}
	if i.allocate == nil || i.dispatch == nil || i.release == nil {
		i.invalidate()
		return nil, errors.New("beaconcrypt: missing WASM ABI exports")
	}
	for name, expected := range map[string]uint64{"bc_abi_version": wasmABIVersion, "bc_max_message_size": uint64(MaxMessageSize)} {
		f := module.ExportedFunction(name)
		if f == nil {
			i.invalidate()
			return nil, fmt.Errorf("beaconcrypt: missing WASM export %s", name)
		}
		result, err := f.Call(ctx)
		if err != nil || len(result) != 1 || result[0] != expected {
			i.invalidate()
			return nil, fmt.Errorf("beaconcrypt: incompatible WASM export %s: %v", name, err)
		}
	}
	return i, nil
}

type wasmResponse struct {
	handle uint32
	keyID  uint64
	seq    uint64
	data   []byte
	state  []byte
}

type wasmAllocation struct{ ptr, length uint32 }

// call holds the endpoint lock through callbacks, response copying and wiping.
// All returned slices own Go memory. Cleanup failures suppress successful output.
func (i *wasmInstance) call(op uint32, arg uint64, input, extra []byte) (out wasmResponse, err error) {
	if i == nil {
		return out, ErrClosed
	}
	i.mu.Lock()
	defer i.mu.Unlock()
	defer runtime.KeepAlive(i)
	if i.closed {
		return out, ErrClosed
	}
	if i.module.IsClosed() {
		i.invalidate()
		return out, ErrClosed
	}
	switch op {
	case 5, 6, 7, 8, 20, 21, 22, 23:
		if len(input) == 0 {
			return out, ErrEmptyData
		}
	}
	i.state.err = nil
	var allocations []wasmAllocation
	defer func() {
		i.state.clearLoad()
		for n := len(allocations) - 1; n >= 0; n-- {
			if cleanupErr := i.free(allocations[n]); cleanupErr != nil {
				clear(out.data)
				clear(out.state)
				out = wasmResponse{}
				err = cleanupErr
			}
		}
	}()
	put := func(data []byte) (uint32, error) {
		a, err := i.put(data)
		if err == nil && a.length != 0 {
			allocations = append(allocations, a)
		}
		return a.ptr, err
	}
	inputPtr, err := put(input)
	if err != nil {
		return out, err
	}
	extraPtr, err := put(extra)
	if err != nil {
		return out, err
	}
	result, err := i.dispatch.Call(i.ctx, uint64(op), uint64(i.handle), arg,
		uint64(inputPtr), uint64(len(input)), uint64(extraPtr), uint64(len(extra)))
	if err != nil {
		i.invalidate()
		return out, fmt.Errorf("%w: WASM call: %v", ErrCrypto, err)
	}
	if len(result) != 1 {
		return out, i.invalidABI("invalid result count")
	}
	a := wasmAllocation{uint32(result[0] >> 32), uint32(result[0])}
	if a.ptr == 0 || a.length < 32 {
		return out, i.invalidABI("invalid response descriptor")
	}
	allocations = append(allocations, a)
	view, ok := i.module.Memory().Read(a.ptr, a.length)
	if !ok {
		return out, i.invalidABI("response outside guest memory")
	}
	status := PersistenceStatus(binary.LittleEndian.Uint32(view))
	dataLen, stateLen := binary.LittleEndian.Uint32(view[24:]), binary.LittleEndian.Uint32(view[28:])
	if status > StatusPoisoned || uint64(dataLen)+uint64(stateLen)+32 != uint64(a.length) {
		return out, i.invalidABI("invalid response header")
	}
	if status != StatusOK {
		return out, &PersistenceError{Code: status, Cause: i.state.err}
	}
	if (op == 14 || op == 16 || op == 19) && (dataLen != 72 || stateLen != 0) {
		return out, i.invalidABI("invalid snapshot head response")
	}
	if op == 15 && (dataLen != 1 || stateLen != 0 || view[32] > 1) {
		return out, i.invalidABI("invalid poisoned status response")
	}
	if i.state.err != nil {
		i.invalidate()
		return out, fmt.Errorf("%w: WASM callback: %w", ErrCrypto, i.state.err)
	}
	out = wasmResponse{handle: binary.LittleEndian.Uint32(view[4:]),
		keyID: binary.LittleEndian.Uint64(view[8:]), seq: binary.LittleEndian.Uint64(view[16:]),
		data: bytes.Clone(view[32 : 32+dataLen]), state: bytes.Clone(view[32+dataLen:])}
	return out, nil
}

func (i *wasmInstance) invalidABI(message string) error {
	i.invalidate()
	return fmt.Errorf("%w: WASM ABI: %s", ErrCrypto, message)
}

func (i *wasmInstance) put(data []byte) (wasmAllocation, error) {
	if len(data) == 0 {
		return wasmAllocation{}, nil
	}
	if uint64(len(data)) > uint64(wasmMemoryPages)*65536 {
		return wasmAllocation{}, fmt.Errorf("%w: WASM memory limit exceeded", ErrCrypto)
	}
	result, err := i.allocate.Call(i.ctx, uint64(len(data)))
	if err != nil {
		i.invalidate()
		return wasmAllocation{}, fmt.Errorf("%w: WASM allocation: %v", ErrCrypto, err)
	}
	if len(result) != 1 || result[0] == 0 || result[0] > uint64(^uint32(0)) {
		return wasmAllocation{}, i.invalidABI("allocation failed")
	}
	a := wasmAllocation{uint32(result[0]), uint32(len(data))}
	if !i.module.Memory().Write(a.ptr, data) {
		return wasmAllocation{}, i.invalidABI("allocation outside guest memory")
	}
	return a, nil
}

func (i *wasmInstance) free(a wasmAllocation) error {
	if a.length == 0 || i.closed || i.module.IsClosed() {
		return nil
	}
	if _, err := i.release.Call(i.ctx, uint64(a.ptr), uint64(a.length)); err != nil {
		i.invalidate()
		return fmt.Errorf("%w: WASM buffer cleanup: %v", ErrCrypto, err)
	}
	return nil
}

// Caller holds the instance mutex, or has not published the instance yet.
func (i *wasmInstance) invalidate() {
	i.closed = true
	i.state.store = nil
	i.state.clearLoad()
	if memory := i.module.Memory(); memory != nil {
		if view, ok := memory.Read(0, memory.Size()); ok {
			clear(view)
		}
	}
	_ = i.module.Close(i.ctx)
}

func (i *wasmInstance) close() {
	if i == nil {
		return
	}
	i.mu.Lock()
	defer i.mu.Unlock()
	if i.closed {
		return
	}
	if !i.module.IsClosed() && i.handle != 0 {
		result, err := i.dispatch.Call(i.ctx, 9, uint64(i.handle), 0, 0, 0, 0, 0)
		if err == nil && len(result) == 1 {
			_ = i.free(wasmAllocation{uint32(result[0] >> 32), uint32(result[0])})
		}
	}
	i.invalidate()
}

func (e *wasmEngine) construct(op uint32, arg uint64, input, extra []byte, store SnapshotStore) (*wasmInstance, error) {
	i, err := e.instantiate(store)
	if err != nil {
		return nil, fmt.Errorf("%w: WASM initialization: %v", ErrCrypto, err)
	}
	r, err := i.call(op, arg, input, extra)
	if err != nil {
		i.close()
		return nil, err
	}
	if r.handle == 0 {
		err := i.invalidABI("constructor returned no handle")
		return nil, err
	}
	i.handle = r.handle
	return i, nil
}

func (e *wasmEngine) inspect(snapshot []byte, expected *SnapshotHead, successor bool) (SnapshotHead, error) {
	e.helperMu.Lock()
	defer e.helperMu.Unlock()
	if e.helper == nil || e.helper.closed || e.helper.module.IsClosed() {
		var err error
		e.helper, err = e.instantiate(nil)
		if err != nil {
			return SnapshotHead{}, fmt.Errorf("%w: WASM snapshot validator: %v", ErrCrypto, err)
		}
	}
	op := uint32(19)
	var extra []byte
	if successor {
		op = 16
		if expected != nil {
			extra = encodeWasmHead(*expected)
		}
	}
	r, err := e.helper.call(op, 0, snapshot, extra)
	if err != nil {
		return SnapshotHead{}, err
	}
	head, err := decodeWasmHead(r.data)
	if err != nil {
		return SnapshotHead{}, e.helper.invalidABI(err.Error())
	}
	return head, nil
}

func encodeWasmHead(head SnapshotHead) []byte {
	data := make([]byte, 72)
	copy(data, head.Lineage[:])
	binary.LittleEndian.PutUint64(data[32:], head.Generation)
	copy(data[40:], head.Digest[:])
	return data
}

func decodeWasmHead(data []byte) (SnapshotHead, error) {
	var head SnapshotHead
	if len(data) != 72 {
		return head, errors.New("invalid snapshot head")
	}
	copy(head.Lineage[:], data)
	head.Generation = binary.LittleEndian.Uint64(data[32:])
	copy(head.Digest[:], data[40:])
	return head, nil
}

func wasmCallback(ctx context.Context, token uint32) *wasmCallbackState {
	state, _ := ctx.Value(wasmBridgeKey{}).(*wasmCallbackState)
	if token != 1 || state == nil || state.store == nil {
		return nil
	}
	return state
}

func wasmSnapshotLoad(ctx context.Context, mod api.Module, token, ptr, capacity uint32) (result int64) {
	state := wasmCallback(ctx, token)
	if state == nil {
		return -2
	}
	defer func() {
		if problem := recover(); problem != nil {
			state.setError(fmt.Errorf("snapshot Load panic: %v", problem))
			result = -2
		}
	}()
	if ptr == 0 && capacity == 0 {
		state.clearLoad()
		snapshot, err := state.store.Load()
		if err != nil {
			state.setError(err)
			return -2
		}
		if snapshot == nil {
			return -1
		}
		state.loaded = bytes.Clone(snapshot)
		state.loadPending = true
		return int64(len(snapshot))
	}
	if !state.loadPending || uint64(len(state.loaded)) != uint64(capacity) || !mod.Memory().Write(ptr, state.loaded) {
		state.setError(errors.New("invalid snapshot Load delivery"))
		return -2
	}
	length := len(state.loaded)
	state.clearLoad()
	return int64(length)
}

func wasmSnapshotCAS(ctx context.Context, mod api.Module, token, expectedPtr, expectedLen, replacementPtr, replacementLen uint32) (result uint32) {
	state := wasmCallback(ctx, token)
	if state == nil {
		return 0
	}
	defer func() {
		if problem := recover(); problem != nil {
			state.setError(fmt.Errorf("snapshot CAS panic: %v", problem))
			result = 0
		}
	}()
	var expected *SnapshotHead
	if expectedLen != 0 {
		data, ok := mod.Memory().Read(expectedPtr, expectedLen)
		if !ok {
			state.setError(errors.New("invalid expected snapshot pointer"))
			return 0
		}
		head, err := decodeWasmHead(data)
		if err != nil {
			state.setError(err)
			return 0
		}
		expected = &head
	}
	data, ok := mod.Memory().Read(replacementPtr, replacementLen)
	if !ok {
		state.setError(errors.New("invalid replacement snapshot pointer"))
		return 0
	}
	accepted, err := state.store.CompareAndSwap(expected, bytes.Clone(data))
	if err != nil {
		state.setError(err)
		return 0
	}
	if accepted {
		return 1
	}
	return 0
}

func wasmSnapshotDestroy(ctx context.Context, token uint32) {
	if state := wasmCallback(ctx, token); state != nil {
		state.store = nil
		state.clearLoad()
	}
}
