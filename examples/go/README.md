This example uses the local checkout through the `replace` directive in [`go.mod`](go.mod). First build the native library with the `gobinds` feature using the platform-specific commands in the main [README](../../README.md#building). Then run:

```bash
go run .
```

`Server` and `Beacon` serialize operations on their native handles and are safe to share between goroutines. Always call `Close` when finished; it is idempotent and safe to call concurrently with other operations.

The `State` and `Key` fields returned by state-update methods contain live secret material. Do not log them. Persist state securely and atomically, and do not clone or roll back a state snapshot.

Because Go's build cache does not detect changes to libraries linked through cgo, use `go run -a .` after rebuilding the Rust static library.
