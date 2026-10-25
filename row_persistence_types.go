// SPDX-License-Identifier: 0BSD

package beaconcrypt

import "errors"

// ErrPersistenceUnsupported reports that row database callbacks require the native backend.
var ErrPersistenceUnsupported = errors.New("beaconcrypt: row persistence is unavailable in the WASM backend")

// RowStore supplies serializable, durable database transactions. Begin starts an
// outer transaction. Load returns nil for an absent key and locks rows (including
// absent-key insertion races) until Commit or Rollback. Store replaces opaque
// secret bytes. Commit durably commits before returning nil. An error can mean
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

// StatusStorage reports a failed database callback, possibly after commit.
const StatusStorage PersistenceStatus = 13
