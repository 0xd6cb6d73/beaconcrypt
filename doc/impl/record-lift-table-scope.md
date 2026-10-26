# Table-slot provenance through actual local operations

`PqxdhRecordLiftTableScope` supplies the table-domain join needed by the dynamic World compiler when its session seeds are sampled lazily. It proves that a complete actual local send or receive cannot introduce a table entry for an unrelated slot. The seed bytes and all primitive state remain arbitrary. This statement concerns the private coordinate labels used by the existing source compiler; it does not recover a slot from a key's bytes.

## The exact lookup footprint

`TableAllowed allowed table` says that each populated table coordinate names a slot satisfying `allowed`. The predicate can later be instantiated with presence in the actual partial seed cache. `LookupWritesOnly` describes supported results of the actual lookup computation: every populated post-table coordinate was populated before, or is exactly the coordinate requested by that call. It imposes no condition on output bytes, key independence, probability, primitive replies, native counters or cache contents. The concrete callback must prove this operational footprint from its actual update equations.

`tableAllowed_empty` establishes the initial table property without requiring a seed. `tableAllowed_mono` keeps the same table valid when the allowed slot set grows. `lookup_allowed` turns one actual supported footprint result into post-table allowedness when the requested slot is allowed.

The footprint alone does not assert table persistence or correctness of existing values. Those are the separate, already reviewed `LookupPreserves` and `LookupRealized` properties. This module uses only the footprint needed to prove slot attribution and does not turn it into a security contract.

## Source receive and send

`receive_allowed` follows the actual source driver's recursion. Its existing `Tracked` invariant makes each KDF request an advance of the original receive coordinate, so every skipped and target derivation retains that coordinate's slot. Each supported lookup reply preserves table allowedness using the write footprint. The rejected path retains its entire table, and the opening path changes only the full native primitive state. A failed opening can therefore restore its kernel while retaining the derived table entries for retry, with every retained entry still attributed to an allowed slot.

`admitted_receive_allowed` starts from the literal `RawCtxChainReceive.normalBegin` operation, which supplies tracking for every target. No capacity, alignment, successful authentication or selected schedule is assumed by this narrower table-domain claim. It covers cached, future and rejected receives because it follows the actual operation, including its failure replies.

`send_allowed` follows the literal source send start. Counter exhaustion leaves the table unchanged; an admitted request names the original send coordinate and writes only there. The actual sealing callback retains the table while executing all native effects, including a writer failure after source advancement. `admitted_send_allowed` obtains its tracking premise from the original source admission operation. Receive and send each need allowedness only for their own live direction; the opposite chain is irrelevant to that operation's table writes.

## Boundary and remaining work

The writer-log lifting theorem transports the same lookup footprint while preserving the complete native state and actual frame list. It applies to the already reviewed `LoggedAdapters.liftLookup`, which frames the writer list only during lookup; it makes no unchanged-log claim for sealing.

All results quantify over the full supported computation, with arbitrary opening, sealing and lookup continuations. They add no oracle call and replace no computation. Source query counts, shared hash cache, actual optional plaintext and writer replies remain in the existing complete state; no ambient work is assigned zero cost.

The dynamic compiler still establishes the concrete mixed callback's footprint, instantiates `allowed` with actual seed-cache presence, and derives the global installed-state invariant through dynamic routing and installation. No independent session family, input-distinctness premise, cryptographic game, secrecy event, alias bound or full protocol theorem is proved here. Persistence and saved-state restoration remain outside the model.
