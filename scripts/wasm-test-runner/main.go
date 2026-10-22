// SPDX-License-Identifier: 0BSD

// Command wasm-test-runner runs the Rust WASI tests with the production memory bound.
// Snapshot callbacks use an in-memory fixture with exact opaque head bytes supplied by tests.
package main

import (
	"bytes"
	"context"
	"crypto/rand"
	"errors"
	"fmt"
	"io"
	"os"
	"strings"
	"time"

	"github.com/tetratelabs/wazero"
	"github.com/tetratelabs/wazero/api"
	"github.com/tetratelabs/wazero/imports/wasi_snapshot_preview1"
	"github.com/tetratelabs/wazero/sys"
)

type store struct{ snapshot []byte }
type owner struct {
	store                  *store
	expected, pending      []byte
	loads, swaps, destroys uint32
	reject, configured     bool
	alive                  bool
}

func runGuest(args []string, stderr io.Writer) error {
	if len(args) == 0 {
		return errors.New("usage: wasm-test-runner TEST.wasm [test arguments]")
	}
	threadCount := false
	for _, arg := range args[1:] {
		threadCount = threadCount || strings.HasPrefix(arg, "--test-threads")
	}
	if !threadCount {
		args = append(args, "--test-threads=1")
	}
	ctx, cancel := context.WithTimeout(context.Background(), 2*time.Minute)
	defer cancel()
	r := wazero.NewRuntimeWithConfig(ctx, wazero.NewRuntimeConfig().
		WithMemoryLimitPages(4096).WithCloseOnContextDone(true))
	defer r.Close(ctx)
	if _, err := wasi_snapshot_preview1.Instantiate(ctx, r); err != nil {
		return err
	}
	stores, owners := map[uint32]*store{}, map[uint32]*owner{}
	get := func(id uint32) *owner {
		if current := owners[id]; current != nil {
			if current.configured && !current.alive {
				panic("snapshot callback used a destroyed context")
			}
			return current
		}
		current := &owner{store: &store{}, alive: true}
		owners[id] = current
		return current
	}
	b := r.NewHostModuleBuilder("beaconcrypt_host")
	b.NewFunctionBuilder().WithFunc(func(_ context.Context, m api.Module, id, ptr, capacity uint32) int64 {
		current := get(id)
		current.loads++
		if ptr == 0 && capacity == 0 {
			if current.store.snapshot == nil {
				return -1
			}
			current.pending = bytes.Clone(current.store.snapshot)
			return int64(len(current.pending))
		}
		if int(capacity) != len(current.pending) || !m.Memory().Write(ptr, current.pending) {
			return -2
		}
		length := len(current.pending)
		current.pending = nil
		return int64(length)
	}).Export("snapshot_load")
	b.NewFunctionBuilder().WithFunc(func(_ context.Context, m api.Module, id, expectedPtr, expectedLen, ptr, length uint32) uint32 {
		current := get(id)
		current.swaps++
		expected, validHead := m.Memory().Read(expectedPtr, expectedLen)
		replacement, validReplacement := m.Memory().Read(ptr, length)
		if current.reject || !validHead || !validReplacement || length == 0 ||
			!bytes.Equal(expected, current.expected) ||
			(expectedLen == 0) != (current.store.snapshot == nil) {
			return 0
		}
		current.store.snapshot = bytes.Clone(replacement)
		return 1
	}).Export("snapshot_cas")
	b.NewFunctionBuilder().WithFunc(func(id uint32) {
		current := get(id)
		current.destroys++
		current.alive = false
	}).Export("snapshot_destroy")
	if _, err := b.Instantiate(ctx); err != nil {
		return err
	}
	tests := r.NewHostModuleBuilder("beaconcrypt_test")
	tests.NewFunctionBuilder().WithFunc(func(id, storage, reject uint32) {
		if stores[storage] == nil {
			stores[storage] = &store{}
		}
		owners[id] = &owner{store: stores[storage], reject: reject != 0, configured: true, alive: true}
	}).Export("configure_store")
	tests.NewFunctionBuilder().WithFunc(func(_ context.Context, m api.Module, id, ptr, length uint32) {
		head, ok := m.Memory().Read(ptr, length)
		if !ok || length != 72 {
			panic("invalid expected snapshot head in test")
		}
		get(id).expected = bytes.Clone(head)
	}).Export("expected_head")
	tests.NewFunctionBuilder().WithFunc(func(id, metric uint32) uint32 {
		current := owners[id]
		if current == nil {
			panic("unknown test context")
		}
		switch metric {
		case 0:
			return current.loads
		case 1:
			return current.swaps
		case 2:
			return current.destroys
		default:
			panic("unknown test metric")
		}
	}).Export("store_count")
	if _, err := tests.Instantiate(ctx); err != nil {
		return err
	}
	wasm, err := os.ReadFile(args[0])
	if err != nil {
		return err
	}
	config := wazero.NewModuleConfig().WithArgs(args...).WithStdout(os.Stdout).
		WithStderr(stderr).WithRandSource(rand.Reader).WithSysWalltime().
		WithSysNanotime().WithSysNanosleep()
	_, err = r.InstantiateWithConfig(ctx, wasm, config)
	return err
}

func run(args []string) error {
	if len(args) == 0 {
		return errors.New("usage: wasm-test-runner TEST.wasm [test arguments]")
	}
	for _, arg := range args[1:] {
		if arg == "--list" {
			return runGuest(args, os.Stderr)
		}
	}
	const probe = "tests::wasm_store_tests::snapshot_load_max_length_allocation_failure_probe"
	regular := append(append([]string{}, args...), "--skip", probe)
	if err := runGuest(regular, os.Stderr); err != nil {
		return err
	}
	var stderr bytes.Buffer
	err := runGuest([]string{args[0], "--exact", probe, "--nocapture"}, &stderr)
	allocationTrap := err != nil && strings.Contains(err.Error(), "wasm error: unreachable")
	if !allocationTrap || !bytes.Contains(stderr.Bytes(), []byte("memory allocation of 2147483647 bytes failed")) {
		return fmt.Errorf("snapshot size-bound probe must fail allocation under the guest memory limit; got %v: %s", err, stderr.String())
	}
	fmt.Println("isolated snapshot size-bound allocation-failure probe ... ok")
	return nil
}

func main() {
	if err := run(os.Args[1:]); err != nil {
		var exit *sys.ExitError
		if errors.As(err, &exit) {
			os.Exit(int(exit.ExitCode()))
		}
		fmt.Fprintln(os.Stderr, err)
		os.Exit(1)
	}
}
