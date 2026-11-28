// SPDX-License-Identifier: 0BSD
//go:build cgo && !beaconcrypt_wazero

package beaconcrypt

import (
	"bytes"
	"os"
	"runtime"
	"runtime/debug"
	"sync"
	"sync/atomic"
	"testing"
	"time"
)

// Empty byte strings must never reach Go as a small non-null address such as
// Rust's dangling 0x1. The runtime treats a value below 4096 in a pointer-typed
// stack slot as corruption and aborts the whole process when it copies a stack
// holding one, so these tests fail by crashing rather than by reporting.

//go:noinline
func growGoroutineStack(depth int) byte {
	var pad [2048]byte
	pad[depth%len(pad)] = byte(depth)
	if depth == 0 {
		return pad[0]
	}
	return growGoroutineStack(depth-1) + pad[(depth+1)%len(pad)]
}

// stressStackShrinking repeatedly runs operation on goroutines that keep a
// large, mostly unused stack while another goroutine forces GC cycles, so the
// runtime shrinks (copies) stacks while values returned by or passed from the
// native library are live. BEACONCRYPT_STACK_STRESS sets a longer duration.
func stressStackShrinking(t *testing.T, operation func() bool) {
	t.Helper()
	duration := time.Second
	if value := os.Getenv("BEACONCRYPT_STACK_STRESS"); value != "" {
		parsed, err := time.ParseDuration(value)
		if err != nil {
			t.Fatal(err)
		}
		duration = parsed
	}
	defer debug.SetGCPercent(debug.SetGCPercent(1))
	var stop atomic.Bool
	var collector sync.WaitGroup
	collector.Add(1)
	go func() {
		defer collector.Done()
		for !stop.Load() {
			runtime.GC()
		}
	}()
	defer func() {
		stop.Store(true)
		collector.Wait()
	}()
	deadline := time.Now().Add(duration)
	for ok := true; ok && time.Now().Before(deadline); {
		done := make(chan struct{})
		go func() {
			defer close(done)
			growGoroutineStack(256)
			for range 64 {
				if ok = operation(); !ok {
					return
				}
			}
		}()
		<-done
	}
}

func newEmptyPointerRowServer(t *testing.T) *CachedRowServer {
	t.Helper()
	// The cached store implements Expect, so absence checks travel through that callback too.
	store := &cachedRowTestStore{rowTestStore: &rowTestStore{database: &rowDatabase{rows: make(map[string][]byte)}}}
	var lineage [32]byte
	lineage[0] = 97
	server, err := NewCachedRowServer(19, bytes.Repeat([]byte{3}, 32), bytes.Repeat([]byte{4}, 32), store, lineage, 1)
	if err != nil {
		t.Fatal(err)
	}
	t.Cleanup(server.Close)
	if _, err := server.Transaction(func(session *RowSession) ([]byte, error) {
		return nil, session.Store([]byte("empty"), []byte{})
	}); err != nil {
		t.Fatal(err)
	}
	return server
}

func TestRowEmptyValuesSurviveStackCopies(t *testing.T) {
	t.Run("transaction result", func(t *testing.T) {
		server := newEmptyPointerRowServer(t)
		stressStackShrinking(t, func() bool {
			empty, err := server.Transaction(func(*RowSession) ([]byte, error) { return []byte{}, nil })
			if err != nil || empty == nil || len(empty) != 0 {
				t.Errorf("empty transaction result: %v %v", empty, err)
				return false
			}
			return true
		})
	})
	t.Run("session load of present empty value", func(t *testing.T) {
		server := newEmptyPointerRowServer(t)
		stressStackShrinking(t, func() bool {
			_, err := server.Transaction(func(session *RowSession) ([]byte, error) {
				value, err := session.Load([]byte("empty"))
				if err == nil && (value == nil || len(value) != 0) {
					t.Errorf("present empty value: %v", value)
				}
				return []byte{1}, err
			})
			if err != nil {
				t.Errorf("load transaction: %v", err)
				return false
			}
			return true
		})
	})
	t.Run("store callback with empty value", func(t *testing.T) {
		server := newEmptyPointerRowServer(t)
		stressStackShrinking(t, func() bool {
			_, err := server.Transaction(func(session *RowSession) ([]byte, error) {
				return []byte{1}, session.Store([]byte("empty"), []byte{})
			})
			if err != nil {
				t.Errorf("store transaction: %v", err)
				return false
			}
			return true
		})
	})
	t.Run("registration with empty completion context", func(t *testing.T) {
		server := newEmptyPointerRowServer(t)
		pk, _ := server.IdentityPK()
		ml, _ := server.MLDSAPublicKey()
		stressStackShrinking(t, func() bool {
			beacon, err := NewBeacon(19, pk, ml)
			if err != nil {
				t.Error(err)
				return false
			}
			defer beacon.Close()
			request, err := beacon.GenerateRegistration()
			if err != nil {
				t.Error(err)
				return false
			}
			output, err := server.RegistrationTransaction(func(session *RowSession) (RowRegistrationDecision, error) {
				accepted, err := session.AcceptRegistration(request)
				if err == nil && !accepted {
					t.Error("fresh registration refused")
				}
				return RowRegistrationDecision{Continue: true, Data: []byte{}}, err
			}, func(session *RowSession, context []byte) ([]byte, error) {
				if context == nil || len(context) != 0 {
					t.Errorf("empty completion context: %v", context)
				}
				value, err := session.CompleteRegistration(nil)
				if err != nil {
					return nil, err
				}
				return value.Message.Data, nil
			})
			if err != nil {
				t.Errorf("registration: %v", err)
				return false
			}
			if _, err := beacon.ProcessInitialMessage(output); err != nil {
				t.Errorf("initial message: %v", err)
				return false
			}
			return true
		})
	})
}
