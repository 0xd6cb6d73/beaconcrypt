This example uses the local checkout through the `replace` directive in [`go.mod`](go.mod). First build the native library with the `gobinds` feature using the platform-specific commands in the main [README](../../README.md#building). Then run:

```bash
go run .
```

`Server` and `Beacon` serialize operations on their native handles and are safe to share between goroutines. Always call `Close` when finished; it is idempotent and safe to call concurrently with other operations.

The `State` field returned by state-update methods is an inert per-peer view and cannot restore a server. Full-server checkpoints use `ExportState` and `NewServerFromState`, as shown in the example. Checkpoints contain plaintext secret material and do not authenticate themselves. Save immediately after every state-changing call and before using its output. Restoring a standalone exported file trusts it as current and cannot detect stale rollback; production deployments that require crash-safe or multi-owner no-rollback persistence need a durable authoritative `SnapshotStore` on the Rust side.

Because Go's build cache does not detect changes to libraries linked through cgo, use `go run -a .` after rebuilding the Rust static library.
