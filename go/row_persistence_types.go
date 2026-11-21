// SPDX-License-Identifier: 0BSD

package beaconcrypt

import "errors"

// ErrPersistenceUnsupported reports that row database callbacks require the native backend.
var ErrPersistenceUnsupported = errors.New("beaconcrypt: row persistence is unavailable in the WASM backend")

// RowStore supplies serializable, durable database transactions. Begin starts an
// outer transaction. Load returns nil for an absent key. Protect every read,
// including absence, with locks or atomic read-set validation at commit. Store
// replaces opaque secret bytes. Commit durably commits before returning nil. An error can mean
// an uncertain commit; the server suppresses output and reloads on its next call.
// Rollback must safely end a failed transaction or do nothing if none is active,
// including after Begin or Commit errors.
// Callbacks cannot reenter their RowServer. Give each concurrent worker a separate
// RowServer and database connection; protect the database from rollback and tampering.
type RowStore interface {
	Begin() error
	Load(key []byte) ([]byte, error)
	Store(key, value []byte) error
	Commit() error
	Rollback() error
}

// RowMessage contains ciphertext or plaintext with its authenticated peer ID and
// the sequence of the consumed key. It contains no ratchet state. RowServer
// convenience methods return committed messages; RowSession methods return
// pending messages that must not be published before the outer call succeeds.
type RowMessage struct {
	Data  []byte
	KeyID uint64
	Seq   uint64
}

// StatusStorage reports a failed database callback, possibly after commit.
const StatusStorage PersistenceStatus = 13

// ErrRowSessionExpired reports access after a transaction callback returned.
var ErrRowSessionExpired = errors.New("beaconcrypt: row session callback has ended")

// StatusInvalidSession reports an invalid native operation or repeated attempt
// within a transaction session. The transaction cannot commit after such an error.
const StatusInvalidSession PersistenceStatus = 14

// RowTransition describes pending native state. Message may be nil even when
// Changed is true. Do not publish Message before the outer transaction succeeds.
type RowTransition struct {
	Message *RowMessage
	Changed bool
}

// RowRegistrationDecision either returns Data after the acceptance transaction,
// or carries Data to completion after a confirmed accepted-registration commit.
// Continue requires a successful AcceptRegistration in the callback.
type RowRegistrationDecision struct {
	Continue bool
	Data     []byte
}

type RowRegistrationPhase uint32

const (
	RowAcceptance RowRegistrationPhase = 1
	RowCompletion RowRegistrationPhase = 2
)

// RowRegistrationError identifies the transaction that failed. Completion means
// acceptance definitely committed. Either phase can have an uncertain commit;
// consult authoritative application rows before retrying the application request.
type RowRegistrationError struct {
	Phase RowRegistrationPhase
	Cause error
}

func (e *RowRegistrationError) Error() string {
	phase := "acceptance"
	if e.Phase == RowCompletion {
		phase = "completion"
	}
	return "beaconcrypt: registration " + phase + ": " + e.Cause.Error()
}
func (e *RowRegistrationError) Unwrap() error { return e.Cause }

// ErrRowConflict signals that a cached predecessor expectation does not match
// the authoritative row. The transaction must not commit.
var ErrRowConflict = errors.New("beaconcrypt: row expectation conflicted")

// CachedRowStore optionally avoids fetching warm peer rows. Expect protects the
// exact expected bytes or absence (nil) through Commit, either by checking under
// a lock or staging an atomic CAS condition. A non-nil empty slice is a present
// empty value. Return ErrRowConflict for mismatch, or another error for a storage
// failure. If unsupported, cached servers use Load and compare automatically.
type CachedRowStore interface {
	RowStore
	Expect(key, expected []byte) error
}
