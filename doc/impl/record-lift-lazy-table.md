# Persistent lazy uniform table for the record lift

`PqxdhRecordLiftLazyTable` supplies a generic table component for the evolving-chain ideal world. A coordinate is an arbitrary oracle input, and its answer type may depend on that input. In the record layer, a coordinate can later be `(slot, direction, position)` and an answer can be the joint message-key, nonce and next-chain output. The module imports only VCVio's generic lazy random-oracle library and does not import any BeaconCrypt record or cryptographic model.

The implementation is VCVio's `QueryImpl.withCachingAux` with uniform sampling on a cache miss. It stores a cache and two natural-number counters. A hit returns the saved answer, increments `lookups`, and leaves `draws` unchanged. A miss samples one uniform answer, extends the cache, and increments both counters. These are counts of logical table operations and uniform sampling operations. They do not claim a bound of one primitive coin query per sample, and they do not account for unrelated work in a surrounding protocol experiment.

The following statements are checked:

| Theorem | Exact meaning |
| --- | --- |
| `run_miss` | On a missing coordinate, the complete answer, updated cache and counters are exactly one uniform sample followed by the explicit state update. |
| `run_hit` | On a cached coordinate, the entire result is deterministic and no fresh sample is charged. |
| `miss_continuation` | The miss equation remains exact for an arbitrary probabilistic continuation receiving both the answer and the full updated table state. |
| `step_facts` | Every supported one-query outcome records the answer, preserves all previous answers, adds exactly one lookup, and adds exactly the pre-query miss indicator to the draw counter. |
| `run_project` | For every adaptive oracle program, forgetting only the counters gives exactly VCVio's lazy random oracle, including its complete final cache. |
| `run_cache_mono` | An arbitrary adaptive sequence of table queries only extends the cache. |
| `run_retains` | Every previously cached answer survives an arbitrary adaptive table continuation. |
| `rollback_hit` | Restoring the caller's private state while retaining the table yields the same cached answer on re-query, with no new sample. |
| `rollback_after_adaptive` | The answer to a first query survives arbitrary intervening adaptive table work followed by caller-only rollback. |
| `run_draws_le_lookups` | Additional fresh draws never exceed additional logical lookups, even from a nonempty initial cache and arbitrary initial counter values. |
| `run_budget` | A structural bound of `q` adaptive table queries increases each counter by at most `q`, for every supported execution. |

The rollback functions model failed-operation rollback within an execution. They explicitly retain the table effects while restoring only caller-owned transactional state. This module does not model saved snapshots, durable storage, or restoring an old table. A later record-world integration must prove that its rejected-receive path uses this separation; the generic lemmas do not assert that correspondence by themselves.

No computational security contract is assumed here. The only type requirements are decidable coordinate equality and VCVio's `SampleableType` instances for the answer types. Every theorem has an exact axiom guard listing only `propext`, `Classical.choice`, and `Quot.sound`. The component does not equate production HKDF with a random function, prove an evolving-chain hybrid, bound aliases or collisions, or lift CTX/AEAD. Those reductions and source correspondences remain separate obligations of the record lift.
