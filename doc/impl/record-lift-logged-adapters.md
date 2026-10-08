# Record-lift native writer-log framing

`PqxdhRecordLiftLoggedAdapters` supplies the complete local operation boundary needed by the dynamic World compiler when it carries a native produced-frame log beside its primitive state. Its 16 theorems use the existing `PqxdhDeploymentNative.frameLog` and `.logged` operations. The log contains every frame handed to the source writer, including a frame whose writer subsequently returns failure. The module preserves the actual reply, complete primitive poststate and exact frame list, without assuming that sealing leaves the log unchanged.

## Actual per-command logging

`loggedNative` executes each literal `frameLog` query under an arbitrary stateful mixed native interpreter. It only rearranges the pair containing primitive state and frame list. `program_logged` proves the resulting complete adaptive computation equal to interpreting the original logged program, from an arbitrary initial frame list. Its proof follows oracle-program composition rather than re-proving the protocol state machine. `program_native_logged` starts from the empty list and gives exactly the common experiment's existing per-command `Native.logged` operation.

`logged_kdf` proves that an actual KDF query keeps the writer log unchanged while retaining the original typed response and all primitive effects. `logged_writer` proves the complementary behavior for a writer query: it appends exactly the supplied frame and retains the actual optional writer reply, including failure. Neither result assumes a successful primitive reply or a pure interpreter. The shared hash cache, native query counters and all other primitive fields remain inside the arbitrary complete state.

## Framing coordinate lookups

`liftKdf` and `liftLookup` carry the existing writer list unchanged while executing their original KDF or coordinate-table operation. Only this unrelated log is framed; the actual table and primitive state can still change. `liftLookup_preserves` transports the existing table validity, persistence and stored-response property. `liftLookup_realized` transports the complete native response and primitive-state realization equation. `liftKdf_real` retains the existing ordinary functional native-response law. `realLookup_lift` shows that the literal real table interpreter itself commutes with adding the untouched writer log, including repeated coordinates that still invoke the source KDF.

These results introduce no new realization or security contract. The generic table equations remain those of the already reviewed local compiler, and functional `KdfReal` remains equality with the existing source response. The global compiler must discharge that law using its actual native handler and supply the existing table/kernel-reference invariants.

## Mixed adapter and complete local joins

`receiveNative` and `sendNative` are the original mixed native receive/send inclusions. `receiveNative_kdf` and `sendNative_kdf` prove that each forwards the same original typed KDF request. `receiveKdf_logged` and `sendKdf_logged` connect the exact native-adapter KDF callbacks to `liftKdf`; their unchanged-log conclusion is confined to KDF calls. `receive_program_logged` and `send_program_logged` retain complete native logging through the corresponding mixed adapter work. In particular, a send still records its actual writer frame and optional result.

`real_receive_logged` and `real_send_logged` are the requested complete local command boundaries. Their left sides execute the labeled source kernel with the lifted real coordinate-table lookup and the actual logged native opening/sealing callback. Their right sides execute the original receive/send source program, through the original whole-owner/source-send adapter and original mixed adapter, under literal `Native.logged`. Equality retains the complete native kernel, actual optional API result, entire primitive poststate and exact produced-frame list. The receive theorem therefore keeps original failed-opening rollback, while the send theorem keeps its original advancement before sealing and its writer-failure log. The private coordinate table is erased using its actual final contents, as in the companion source compiler.

## Scope and query accounting

The final local joins require only the existing functional native KDF law, real-table validity and available live-chain/skipped-material references. All callback and writer state is retained; no new primitive game, independence premise, successful authentication premise or security event appears. Sixteen exact dependency guards allow only the permitted Lean built-ins; the lookup-preservation theorem needs only `propext` and `Quot.sound`.

The whole-program equation forwards the original primitive calls and continuation replies. Logging records frames and rearranges state locally; it does not discard native KDF/hash/AEAD/writer work or declare it free. Existing source and WorldBudget counters remain in the complete primitive state. A real lookup still invokes the native KDF on every call, including hits, and the frame logger adds no extra native call.

Raw parsing, dynamic peer/owner routing, actual installation, seed-cache framing, per-handle provenance and the complete World handler equality remain the dynamic compiler's responsibility. This module does not prove global source reachability, a source event for a selected secrecy challenge, evolving-key independence, an alias bound, a cryptographic reduction or full protocol security. It is an exact local operational join using the existing produced-frame semantics, with no persistence or saved-state restoration model.
