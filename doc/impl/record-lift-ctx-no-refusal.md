# Removing the selected-nonce refusal from the source experiment

`PqxdhRecordLiftCtxNoRefusal` proves that the artificial selected-nonce stop in the global CTX source comparator is unreachable for the actual initialized protocol program. It uses the already checked private source history before each service request. The proof does not condition on successful execution, require an honest selected identity, assume distinct byte keys, or recover any hidden plaintext.

## Why the guard cannot trigger

The stopped comparator selects a sealing operation by its literal material coordinate and the existing associated-data width check. Its nonce ghost records that selected operation's attempted nonce even when the frame writer returns `None`. `UsedSound` states the exact relation needed by the guard: if the selected nonce has already been used, the selected structural coordinate occurs in the prior attempted-seal history. It says nothing about nonce equality across unrelated keys or coordinates.

`fresh_no_refusal` combines this relation with `ProtocolHistory.Fresh`, which states that the current sealing coordinate is absent from the prior history before the service answers. A repeated selected nonce would require that same coordinate to be both present and absent. `advance_sound` proves that the literal `advanceUsed` update preserves the relation after every private request, independently of its eventual source result. The empty selected nonce history establishes the relation without a premise.

The source history theorem covers every typed reply path. It therefore remains usable at the prefix where a chosen interpreter would otherwise refuse, rather than relying on a completed successful stopped run. Malformed or nonselected requests retain their existing behavior, and writer failure remains an ordinary attempted sealing operation.

## Complete execution equality

`trackingInterpreter` is the literal `bareInterpreter` with the selected-attempt ghost carried alongside it and no refusal branch. `stop_free` proves equality of the entire stopped execution and this total execution tagged with outer `Except.ok`. It retains the full result and final `CutState`, including the actual source cache, table, seed state, effects and pending/produced frames. Actual optional plaintext and writer results remain inside their original typed replies; an outer successful tag does not imply that authentication or writing succeeded.

`tracking_query` and `tracking_schedule` erase only the selected-attempt ghost and recover the exact bare source operations and arbitrary adaptive continuation. `bare_no_refusal` composes this erasure with stop elimination. Its general prefix form states the precise `UsedSound` and pre-query history conditions; the initialized corollaries derive those conditions from the source.

`initial_schedule_no_refusal` covers every actual initialized adaptive world schedule, every selected coordinate and nonce, and any supplied bare private state. `program_no_refusal` specializes it to both frozen environment/adversary programs, retaining the returned environment, ledger, adversary output and public control. `program_world_no_refusal` starts at the actual initial source private state and identifies the result with the complete mixed `WorldCompiler.run`, after the existing explicit native/uniform counter projection from `CtxProtocol`. No additional source field is discarded here.

`program_reduction_no_refusal` joins the constructed ordinary selected-key CTX reduction to the unstopped global bare source. The selected component's nonce list starts empty, as it does in its existing ordinary initial state. The source program supplies all later pre-query freshness conditions. The existing already-ideal selected table condition remains explicit: this theorem is an exact simulation at that intermediate game, not a proof that an arbitrary chosen key is uniform or hidden.

## Scope and accounting

This stage removes a protocol-source refusal branch and adds no cryptographic contract. It adds no oracle service or stronger service reply. The previously proved source and ordinary reduction query bills still apply; proof-side history bookkeeping does not erase source primitive work. Known-key byte aliases remain allowed, and nonce equality between unrelated keys is not forbidden.

The actual selected-key missing-entry distribution, target-free observer construction, numerical global syntax budgets, record/session selection, alias bounds and final integrity/privacy events remain their separate composition joins. The existing counter projection is still explicit, and the final source/reduction bills must charge the actual work. No primitive implementation, snapshot or persistence proof is attempted.

## Provenance

Adapted from Codex WIP `b1fb622690c682168787b60369bf8c7abd85ef69223c7741af00906895ade306` (the module source, published byte for byte unchanged) and `262bad3b7431bd7b3d0867695a640aa363f8f2749e17045809021c7809c5cf14` (this guide, of which only this provenance section and the validation status below are new). Codex wrote the module and the guide. Before Codex stopped on 2026-10-08, an independent semantic and source-hygiene review inside Codex's lane approved exactly these source bytes; its receipt is preserved with the other inherited WIP files on the takeover branch `codex/deployment-record-wip`. Claude took over handoff items 4 and 5 by the owner's decision of 2026-10-08 and publishes the module as part of record-lift increment A.

## Validation status

All ten statements have exact `#print axioms` guards that allow only `propext`, `Classical.choice` and `Quot.sound`. The unchanged source passes the focused single-module check against the published `LEAN_PATH` of central `80560f92`, as recorded in `doc/impl/proof-receipts/record-lift-increment-a.json`. A confirming independent semantic review by a Claude reviewer, the increment's publication checks and the central integration are recorded in that receipt when they complete.
