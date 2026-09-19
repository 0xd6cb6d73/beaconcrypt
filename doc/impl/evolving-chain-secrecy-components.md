# Evolving-chain secrecy components (HB-112)

The topic work now contains 311 Lean modules and 1,891 guarded public statements across six checkpoints supporting the evolving-chain secrecy composition. The stage remains incomplete: the concrete source experiment, original freshness interfaces, corrected private-query observer and full resource certificates are proved, while the final random-child event connection, complete first-half source comparison and final aggregate reductions remain unfinished at the requested pause. HB-110 retains its historical paused work; HB-111 is the completed authenticated-root milestone; HB-112 is the current evolving-chain milestone. The sections below preserve each checkpoint’s scope and explain every substantial component.

Public HKDF calls always use the fixed production function in the intended source and final experiments. Modules that temporarily mask public or retained projections are explicitly intermediate comparison components. No public-HKDF/random-table advantage is a negligibility premise. Primitive algorithms and implementations are unchanged trusted contracts. Snapshots, persistence, restoration and their consequences are outside this proof.

The retained-parent component bound uses two separately constructed reductions: the main output observer and the real-input recovery tester. It pays one Extract advantage and one ordinary two-query HMAC advantage for each, plus the full-output image term 2^-352 and the independent-input candidate term q/2^256. The image term applies to a complete 76-byte child comparison. It is not a 64-byte-output image bound. Real-child guesses are not treated as independent guesses. The actual family freshness proxy may incur additional copies of the same explicitly counted alias event; the final global coefficients have not yet been established.

The source family gives private-derivation cap S+51R, seal cap S, opening cap R, caller uniform cap U, public commitment cap H, real public HKDF cap K and read cap E. Its concrete observer pays U+64(S+R+H) uniform requests and grows its candidate list by at most S+51R+K+E. The consuming source proof must supply the actual prior cache/history values in the initial list; duplicates are retained, and the subsequent source-execution checkpoint derives chronological cache provenance. These are logical query and sampling counts; ordinary local cryptographic evaluation, copying, parsing, lookup, allocation and serialization still contribute to runtime. A captured continuation's original remaining source budget must be proved, not assumed free.

The registration builder's factored initializer component derives all nine native one-call caps for every supplied initializer answer, including failure and divergence. Its uniform bill is 64+5*qAux, where the five auxiliary callback bounds remain explicit. The first-child component consumes either half of one actual uniform 64-byte initializer while retaining the opposite half and complete prior context. The real, Extract, HMAC and independent-child games each pay their own exact sampling costs. The final source service must retain the Server and later Beacon initializer at their original callback positions and preserve repeated-root correlation.

Each module below has been read for statement scope and checked directly with its guarded dependency reports. Its explanation and each public statement's purpose are recorded here. Operational equalities, resource theorems and conditional primitive reductions remain distinct; none of the operational modules alone proves secrecy. The integration receipt will record the full Lake and inventory checks separately.


## PqxdhInitialBuilderCut

The exact original registration builder is factored at its pure 64-byte initializer result. Its current allocation/binding checks, identity validation and peer reservation still precede initialization, and plaintext allocation, first send, erasure, serialization, publication and reinstallation remain the original tail. The factored code never reads the root field. This is a source-derived continuation for an initializer hybrid, not a new protocol or an arbitrary compatibility premise.

- `candidate_source`: The full original candidate tail consumes exactly the supplied source initializer result in its original order.

- `used_source`: Rechecks of the exact current Server control and binding precede the same source-derived initializer tail.

- `ready_source`: The actual accepted-root builder uses its same consumed context and exactly one factored initializer result.

- `ready_root_unused`: Once the initializer result is supplied, every complete accepted builder effect is independent of the Ready root field.

- `protocol_source`: Factoring initialization retains the entire real registration protocol state, first send and selected Server reinstallation.

- `protocol_root_unused`: The original complete protocol builder no longer reads Ready.root after its initializer is supplied; all other fields and shared effects remain present.

- `erased_fields`: The retained initializer context contains a fixed dummy root and preserves every other Ready field.

- `protocol_erased_source`: The actual registration builder can be executed with a root-erased context and its same source initializer result before the first send.


[Checked Lean source](../../beaconcrypt-core/proofs/lean/BeaconcryptCore/Computational/PqxdhInitialBuilderCut.lean).


## PqxdhInitialBuilderQueryBounds

The factored initializer builder pays its actual original callback classes even for an arbitrary supplied initializer result. Allocation and binding checks retain their source order; failed or divergent initializer results add no later callback. The source and randomized initializer continuations therefore use the same nine-class native ledger, rather than an opaque assumed builder budget.

- `candidate_bound`: Each actual candidate callback class has cap one for every initializer result, including diagnostic failure and divergence.

- `continue_bound`: Pure diagnostic control adds no callback before the exact original continuation.

- `used_bound`: Original binding preparation adds no callback before the bounded candidate tail, for every supplied initializer result.

- `ready_bound`: All factored accepted-root callbacks retain their source one-call cap independently of the initializer answer.

- `native_class`: The native partition names exactly the original callback predicates.

- `native_partition`: The factored builder has one-call caps on all nine original native interfaces for every initializer answer.

- `weighted_bound`: Each interpreted callback pays its stated primitive cost; the arbitrary initializer result does not conceal any native work.

- `protocol_uniform`: The exact factored protocol builder pays at most one commitment miss and five explicitly costed auxiliary calls for every initializer answer.

- `observer_uniform`: The actual initializer observer pays the derived full builder bill before its explicitly bounded outside continuation.

- `reduction_queries`: The concrete initializer reduction makes at most two HMAC challenge calls and pays the full root sampler, first-send builder and outside continuation.

- `challenger_queries`: Each challenger world pays its own random bytes plus the same concrete first-send and outside bill; the comparison full 76-byte draw is not assigned to the source initializer.

- `random_queries`: The actual randomized initializer pays exactly its 64-byte draw plus the derived original builder and explicit outside sampling budgets.


[Checked Lean source](../../beaconcrypt-core/proofs/lean/BeaconcryptCore/Computational/PqxdhInitialBuilderQueryBounds.lean).


## PqxdhInitialBuilderSecrecy

The initial-secret component is consumed by the original registration builder before its first record is sent. The challenge is explicitly sampled before the factored builder and paid even when the builder rejects before initialization. The original fixed initializer is pure, so its actual game is literally the source builder; no random generator interchange is inferred from that fact. The global root-miss sampler remains a caller supplied distribution, whose context must be established by the authenticated-root composition. This module supplies its concrete source continuation rather than a security assumption about arbitrary established roles.

- `native_source`: The component's actual initializer observer is exactly the original source builder and its complete caller continuation, with the sampled root installed only for the source calculation.

- `native_bound`: The actual source builder before its first send reduces to the same explicit fixed-Extract and HMAC games on the root/context sampler.

- `native_uniform`: The actual source consumer pays the complete sampler, real builder callback bill and caller continuation, including rejected registrations.


[Checked Lean source](../../beaconcrypt-core/proofs/lean/BeaconcryptCore/Computational/PqxdhInitialBuilderSecrecy.lean).


## RawCtxBadEventMixture

A shared original sampler averages the same explicit local bad-event costs over its complete context. These arithmetic laws retain the sampler distribution and do not replace it by a worst-case source-independent state. They construct no cryptographic reduction; their consuming protocol proof must discharge each local comparison for its actual continuation.

- `local_probability`: An explicit Boolean bad-event probability bounds the one-sided probability change implied by a local advantage bound.

- `bind_probability`: The same complete context sampler averages local comparison costs into the original bad-event game.

- `bind_bound`: Averaging the same local absolute differences charges one full sampled bad-event probability, with coefficient one.


[Checked Lean source](../../beaconcrypt-core/proofs/lean/BeaconcryptCore/Computational/RawCtxBadEventMixture.lean).


## RawCtxFamilyCompletionFreshness

A selected record continues inside an original non-read family operation. This prefix retains its full optional result and family state, all earlier candidates and the unchanged direct-read flag. The original outside LIVE client then resumes after its one history tick. Its final freshness invariant is derived from this exact prefix and actual outside source schedule, without assuming a final history correspondence or excluding public guesses from freshness.

- `prefix_state`: The complete non-read prefix preserves its direct-read flag and every earlier available-input candidate, including on unsuccessful operations.

- `completion_invariant`: Every supported completion and original outside LIVE execution derives its final disclosure witness and candidate inclusion from the actual initial history.

- `completion_fresh_proxy`: Outside the same full candidate event, the actual selected completion's byte freshness equals the executable proxy.

- `completion_event_bound`: The complete in-progress source continuation changes from actual freshness to its target-free proxy by at most its original final candidate event, with no disclosure probability added.

- `stopped_event_bound`: The bound consumes the actual reached material-only Context.stopped program, including its pending owner, Server or Beacon, family publication and unchanged outer LIVE client.

- `initial_length`: The initial candidate ledger explicitly charges every earlier candidate and every actual prior/history disclosed value, with duplicates retained.


[Checked Lean source](../../beaconcrypt-core/proofs/lean/BeaconcryptCore/Computational/RawCtxFamilyCompletionFreshness.lean).


## RawCtxFamilyFreshnessProxy

Actual finite-family disclosure freshness is separated from the selected input's unavailable bytes. The proxy checks retained known ancestors and material values together with the sticky direct-read flag. Known reveal aliases remain explicit candidates, including prior authorized disclosures. Public outputs are not freshness exclusions. Native family lookups, optional rejection and original history observations are kept exact. These operational statements take the current hybrid's blocked values; they do not reevaluate a fixed-source lineage after an ancestor replacement.

- `value_before`: Every unflagged optional family reply is exactly the target-free reply, independent of owner labels.

- `direct_disclosed`: A flagged current-chain read puts the selected input bytes in the actual native disclosure history.

- `known_note`: Appending the exact original timestamped observation appends precisely its actual disclosed values.

- `family_observation`: The tracked observation is exactly the actual source reveal at the selected owner in the complete finite family.

- `witness_note`: Every new direct-read bit is witnessed by its actual native optional reply; earlier witness values remain in the original history.

- `witness_tick`: An earlier hidden-read witness survives every non-read API timestamp advance.

- `fresh_clear`: Actual permitted-disclosure freshness forces the derived direct-read flag to be clear, without conditioning the experiment.

- `no_alias`: An unavailable input can coincide with an available disclosed value only through its explicitly recorded 32-byte candidate.

- `fresh_proxy`: Outside the explicit known-disclosure candidate event, actual byte freshness equals the target-free proxy once the source-derived read witness is retained.

- `observation_inputs`: The original optional read contributes exactly the same 32-byte value to the input-candidate ledger.

- `label_inputs`: The family reader's available-value projection is the exact existing per-read candidate list, including skipped-key material.

- `knownInputs_note_length`: Each actual reveal appends at most one candidate and preserves every prior disclosed value.


[Checked Lean source](../../beaconcrypt-core/proofs/lean/BeaconcryptCore/Computational/RawCtxFamilyFreshnessProxy.lean).


## RawCtxFamilyObservationBudgets

The original finite-family observer's uniform budget is U+64(S+R+H). Its actual opening and sealing adapters each reserve one possible 64-byte shared commitment-cache miss, preserving parser rejection, AEAD failure, optional plaintext/ciphertext and writer failure. Caller coins cost one; private KDF, real public fixed HKDF and live reads add no uniform sampling. These are uniform-query counts, not claims that deterministic cryptographic, parser, lookup or serialization work is free.
The same original all-reply source budget supplies a candidate increment cap S+51R+K+E. The trace retains its entire initial candidate prefix and every duplicate, rejected attempt and actual optional disclosed value. Candidate bounds hold for an arbitrary callback implementation and direct-read flag; uniform bounds use the concrete target-free retained-parent handler. Complete actual family results, role state, chronology, shared primitive state and instrumentation are retained. A reached stopped context must separately supply original outside-client budget provenance and the in-progress operation completion bill; neither follows merely from a Context type. Prior cache/history candidates remain an explicit initial prefix to be counted by that consuming source theorem.

- `native_uniform`: The actual fixed native backend spends uniform calls only on its shared commitment-cache misses.

- `open_uniform`: The actual raw opening executor reserves one shared commitment miss and retains all parser and AEAD rejection paths.

- `seal_uniform`: The actual sealing executor reserves one shared commitment miss, including AEAD and writer failure.

- `receive_open_uniform`: The source opening adapter keeps its no-material rejection and reserves the same one inner opening.

- `send_seal_uniform`: The source sealing adapter retains the exact source getter arguments and returned optional ciphertext.

- `handler_uniform`: Each actual target-free callback has its explicit uniform cost; private KDF and public fixed HKDF evaluations remain real local work.

- `observed_uniform`: Candidate recording and the sticky read flag add no hidden random calls to an actual callback.

- `complete_uniform`: The complete adaptive target-free continuation pays the exact class-weighted coin and commitment bill, retaining all private trace state.

- `inputs_length`: Only actual known private inputs, real public HKDF inputs and optional disclosed values add candidate entries, at most one per callback.

- `trace_length`: Every supported complete candidate trace retains its initial prefix and charges the three actual candidate-producing classes, including repetitions and rejected operations.

- `source_uniform`: The actual finite-family observer pays U+64(S+R+H), derived from the original adaptive source budget with every read and callback retained.

- `source_candidates`: The actual family continuation retains all prior candidates and adds at most S+51R+K+E, without dropping duplicate guesses or failed attempts.


[Checked Lean source](../../beaconcrypt-core/proofs/lean/BeaconcryptCore/Computational/RawCtxFamilyObservationBudgets.lean).


## RawCtxFamilyPendingCompiler

The enriched pending family interface erases only the private pending payload and original read owner tag already retained by the source history. Its non-read callbacks remain the actual receive/send/public capability. The original complete family client and the selected in-progress completion compile to the same old primitive/read program. No target bytes, source compatibility assumption or resource premise is added.

- `calls_erased`: Erasing enriched pending receive/send calls gives the actual original chain calls, including every attempted opening or sealing operation.

- `calls_forwarded`: The forwarded pending calls retain exactly the original public primitive capability.

- `program_source`: The complete original pending LIVE family program is exactly the source compiler used by the derived freshness invariant.

- `lift_source`: The in-progress non-read family completion finishes before the same original outside LIVE client and its single history tick.

- `stopped_source`: The actual material-only selected family context has this exact completion-prefix and outside-client factorization.


[Checked Lean source](../../beaconcrypt-core/proofs/lean/BeaconcryptCore/Computational/RawCtxFamilyPendingCompiler.lean).


## RawCtxFamilyPrimitiveBudgets

The actual slot receive/send programs and literal original finite-family/read compiler supply seven separate primitive-interface caps: private KDF S+51R, sealing S, opening R, caller coins U, public commitment H, real public HKDF K and reads E. Every possible typed reply, rejection and selected role is retained. Public HKDF calls and reads never become private KDF calls, and no callback budget is assumed at the final source theorem.
Opening and sealing interface calls contain their actual inner commitment/AEAD/writer work; their shared hash uniform costs are accounted by the consuming interpreter ledger. This module counts source primitive interfaces and does not declare inner or deterministic local work free. It does not bound an arbitrary stopped context merely from its type: reached original outside-client budget provenance and pending completion costs remain separate consuming statements. No cryptographic or freshness premise is introduced.

- `receive_calls`: The original generic receive syntax retains its KDF and opening reservations through the actual alias primitive compiler.

- `send_calls`: The original send syntax retains one KDF and one sealing callback, including optional sealing failure.

- `public_calls`: Every original public service makes exactly its own primitive-class request, including real HKDF evaluation.

- `primitive_forward`: Forwarding a complete primitive program into the live interface preserves every original primitive-class query.

- `read_calls`: The exact family read compiler charges only a read attempt and never a record/public primitive class.

- `source_step`: The literal original family/read compiler supplies every concrete primitive-class step bound.

- `source_class`: The original adaptive family source supplies KDF S+51R, seal S, open R, caller coins U, public hashes H, real public HKDF K and reads E.


[Checked Lean source](../../beaconcrypt-core/proofs/lean/BeaconcryptCore/Computational/RawCtxFamilyPrimitiveBudgets.lean).


## RawCtxFamilyReadCompiler

The finite-family reader retains its original owner in the outer source history while forwarding only the private read kind and optional selected kernel to the existing selected-live primitive interface. Missing owners reject without a primitive callback. The native optional value, candidate append and sticky direct-disclosure flag are exact. Complete non-read programs retain the same flag, original callbacks and candidate log; all supported traces preserve their prior candidate prefix.
These are operational source/trace equations. They do not assume that the direct flag is unlikely or that candidates miss a hidden input. Whole-family freshness and alias reductions must consume the original returned-value history. Each read uses at most one private read query and contributes at most one available candidate; the original source attempt and local lookup/copy work remain accounted separately. Snapshots and persistence are excluded.

- `native_value`: The read compiler removes only the private owner tag and returns the actual native optional reply.

- `trace_read`: The concrete private-alias reader retains the original shared state and appends exactly the available values and direct-disclosure flag.

- `primitive_step`: Every non-read primitive preserves the direct-disclosure bit and retains the same reply, shared effects and candidate append.

- `primitive_complete`: An arbitrary adaptive non-read program preserves the sticky bit while retaining every original primitive callback and candidate entry.

- `retained_candidates`: Every supported full trace retains all prior candidates, including across arbitrary non-read callbacks.

- `compiler_total`: A family read spends at most one private read-interface query; absent owners reject without a callback.

- `candidates_length`: Each original read attempt contributes at most one available candidate value.


[Checked Lean source](../../beaconcrypt-core/proofs/lean/BeaconcryptCore/Computational/RawCtxFamilyReadCompiler.lean).


## RawCtxFamilySourceFreshness

The original finite-family source client is compiled through its actual record/public frontend and exact selected-owner read callback. All state, history, optional replies, shared primitive state and candidate logs remain present. The source program itself derives that a sticky hidden-read flag has an actual disclosed-value witness. On clear-flag executions, every original disclosed value is in the existing available-input candidate ledger. No final freshness or history correspondence is assumed. Public operations remain the supplied common real interface; their candidates are retained and never become freshness exclusions.

- `compiler_source`: The literal compiler is exactly the original generic family/read source frontend, with its same record/public calls individually forwarded and its same selected-owner read.

- `read_step`: The original selected-owner read preserves all shared state and records its actual native reply, available candidates and exact sticky bit in the same execution.

- `nonread_step`: Every original non-read role/public operation retains its complete source effects and candidate log, advances the original history and leaves the direct-read bit unchanged.

- `step_invariant`: Every supported original family step derives its actual disclosure witness and retains all available disclosed bytes in the existing candidate ledger on clear-bit paths.

- `schedule_invariant`: The complete original adaptive source schedule derives the witness and candidate inclusion at every supported final state.

- `source_project`: The supported source execution is exactly the same original compiled primitive client used by the retained-parent games, with only tuple association changed.

- `initial_invariant`: Starting with a clear bit and the exact prior/history candidate list derives the source invariant without a freshness assumption.

- `source_fresh_proxy`: In every supported original execution, actual finite-value freshness equals the unavailable-input-free proxy outside the same total candidate event.

- `source_event_bound`: Replacing actual byte freshness by the executable known-value proxy costs at most the original complete candidate-hit probability; forbidden direct reveals incur no additional probability term.

- `compiled_event_bound`: The same probability bridge applies directly to the original old-interface compiled client used by the computational hop, preserving its full private state and candidate list.


[Checked Lean source](../../beaconcrypt-core/proofs/lean/BeaconcryptCore/Computational/RawCtxFamilySourceFreshness.lean).


## RawCtxFlaggedQueryAgreement

Masking a query-derived disclosure preserves the unconditioned final good event when its original complete callback is unchanged outside that disclosure. Both candidate history and disclosure history remain in the same result. The callback equation is an operational premise discharged by the actual optional-read implementation; it is not a security premise or a bound on disclosure probability.

- `flag_step`: Each supported callback retains the original flag or marks the current disclosure, independently of its actual reply.

- `sticky`: The original disclosure flag is sticky for every supported callback result.

- `agree_good`: Complete good transitions agree when the original callbacks agree outside the explicitly marked query.

- `event_good`: The same full adaptive event restricted to the original good flag has exactly the same unconditioned probability, including prior exposure.


[Checked Lean source](../../beaconcrypt-core/proofs/lean/BeaconcryptCore/Computational/RawCtxFlaggedQueryAgreement.lean).


## RawCtxFlaggedQueryTrace

Candidate logging and a query-derived sticky disclosure flag retain their original complete state. Reassociation exposes the existing checked alias coupling without resetting either history. The flag is private analysis state and does not alter the primitive reply. This module supplies operational coupling, not a source reachability or guessing bound.

- `step`: Reassociation preserves the primitive reply, complete state, prior candidate prefix and sticky flag on each query.

- `complete`: The full adaptive computation retains both histories; only tuple association changes.

- `mark_routed`: Exact-byte routing changes only the primitive callback; it retains the same query-derived disclosure flag.

- `distance`: Exact-byte routing is charged to the same complete candidate list while preserving the separate original disclosure flag.


[Checked Lean source](../../beaconcrypt-core/proofs/lean/BeaconcryptCore/Computational/RawCtxFlaggedQueryTrace.lean).


## RawCtxFullPreimageTester

A separately constructed full-output distinguisher tests whether any actual public candidate evaluation reproduces the supplied child output. The hidden input is retained only by the private winning event, never passed to this tester. For an independently uniform 76-byte child, acceptance implies membership in the complete image of the fixed 32-byte-input function, whose probability is at most 2^-352 even if the candidate list is chosen adaptively after seeing the child.
The real-child membership event is therefore bounded by the actual joint-sampler full-output Extract and ordinary two-query HMAC PRF advantages plus this image term. This is a separate reduction from an independent-input guessing bound; no real-child independence is asserted. Public HKDF remains fixed and real, with at most one instrumented full evaluation per returned candidate. The source sampler and complete observer must still be instantiated by the reached protocol execution and their own budgets. No freshness, source reachability, initial-output sampler, global hybrid, or small primitive advantage is assumed by this generic endpoint. Snapshots, persistence and restoration are excluded.

- `test_iff`: The tester compares only public candidate evaluations with the supplied full output.

- `uniform_image`: Even adaptively chosen candidates can accept only outputs in the fixed function's finite image.

- `full_card`: A full 76-byte output has exactly 608 bits.

- `uniform_image352`: The complete fixed 32-byte input image occupies at most a 2^-352 fraction of uniform full 76-byte outputs.

- `uniform_tester`: The complete adaptive observer cannot cause acceptance outside the fixed input image.

- `actual_test`: A real target in the returned candidates always makes the target-free tester accept.

- `independent_test`: The complete sampler precedes the independently uniform child, with no restriction on subsequent adaptive candidates.

- `source_test`: Serialization preserves the exact source tester computation, including the complete continuation.

- `source_alias_bound`: Real-child target recovery is bounded by a separately constructed full-output Extract/PRF tester and the finite-image term.

- `evaluate_real`: The instrumented tester is the same real public computation; it does not replace public HKDF by a random oracle.

- `evaluate_queries`: Every possible evaluation reply is counted, including repeats; at most one real full HKDF evaluation per candidate is needed.

- `tester_uniform`: The tester retains every uniform call made by the supplied observer, adding no uniform sampling of its own.

- `byteSampler_uniform`: Serializing the actual vector sampler preserves its complete uniform-call budget.

- `tester_evaluated`: Instrumenting each candidate evaluation preserves the complete observer and its exact Boolean answer.

- `tester_evaluation_bound`: The complete tester adds at most the supplied supported candidate count in real full-output evaluations.

- `reduction_bounds`: The separately constructed PRF reduction uses at most two ordinary HMAC challenge queries and retains every sampler/observer uniform call.

- `actual_uniform`: The actual target-bearing experiment charges its complete sampler and original continuation without using a distributional cost transport.

- `challenger_bounds`: All six source/challenger executions retain the same sampler and observer, and charge each complete challenger sample separately.


[Checked Lean source](../../beaconcrypt-core/proofs/lean/BeaconcryptCore/Computational/RawCtxFullPreimageTester.lean).


## RawCtxGenericBeacon

The actual Beacon record frontend uses the same original phase admission, outer sender identifier, pinned server, associated data and whole-owner calls with a generic private kernel representation. Every inactive phase retains its private fields. Successful or failed source callbacks preserve their full optional result and advanced or restored kernel before original publication. The kernel map and native equations are operational; the concrete retained-table interpreter must discharge their call equations.

- `native_selected`: Source owner selection reads the same native target, associated data, kernel and attempted-receive count.

- `native_reinstall`: Publication reinterprets only the returned kernel and preserves the source phase, identities and exact attempt count.

- `native_step`: The complete original Beacon frontend is the generic-kernel execution when its actual receive and send calls realize that kernel representation.

- `established`: Established dispatch uses the exact selected owner and reinstalls its whole returned kernel.

- `step_map`: Changing only the installed kernel representation preserves the complete Beacon API step and all callback effects.

- `schedule_map`: The same representation law covers the complete adaptive Beacon schedule and every optional reply.


[Checked Lean source](../../beaconcrypt-core/proofs/lean/BeaconcryptCore/Computational/RawCtxGenericBeacon.lean).


## RawCtxGenericFamilyBudgets

The actual generic Server/Beacon frontends retain the query caps of their exact receive, send, public and read callbacks. Every empty-input, decode, sender/AD/peer, phase and publication branch is included. The original aggregate source budget then accumulates weighted costs across both role families and every adaptive typed reply, with no operational session multiplier.
These are compositional syntax bounds. Their callback caps are explicit operational obligations, discharged by the concrete slot or native callback ledger in the consuming module. They are not cryptographic or source freshness assumptions and do not declare local routing, parsing, lookup, copying or public evaluation free. No distribution-based cost transport or persistence interface is introduced.

- `owner_raw`: Original raw admission can invoke only its one actual receive program; all rejection paths spend no primitive query.

- `owner_send`: Empty sends reject before callbacks, and every active send executes only its original full send program.

- `server_raw`: Server routing and all peer/AD admission gates retain the complete original receive-program cap.

- `server_send`: Server AD lookup, sender selection and original peer publication add no primitive request to the actual send program.

- `beacon_step`: Every Beacon phase either rejects or invokes exactly the original established owner, retaining its send/raw resource class.

- `family_step`: The full finite family charges the selected actual role program and original public service under every possible reply.

- `family_schedule`: Original aggregate source budgets accumulate the concrete family step costs with no session-count multiplier.

- `live_step`: Actual family reads add their own callback cost while retaining original optional replies, roles and history.

- `live_schedule`: The full original family/public/read schedule consumes its own source budget through every possible callback continuation.


[Checked Lean source](../../beaconcrypt-core/proofs/lean/BeaconcryptCore/Computational/RawCtxGenericFamilyBudgets.lean).


## RawCtxGenericFamilyFrontend

The full finite family dispatches each original Server or Beacon request to the exact indexed generic role frontend and updates only that returned role state. Public services use the same supplied handler outside both role families. The same chain-independent original client can interleave arbitrary requests and stop adaptively while all installed peers, inactive phases and backend effects remain private and intact.
The two complete representation laws consume exact receive/send call-map equations; they do not assume target freshness, parent-table consistency or kernel independence. Concrete native and retained-slot interpreters must discharge those call equations in the source composition. This module supplies no key distribution or cryptographic advantage. Original raw parsing, admission and publication remain in the checked role frontends; snapshots and persistence are excluded.

- `step_map`: Every selected role update commutes with the whole-family kernel map and keeps all other roles unchanged.

- `schedule_map`: The original adaptive family client receives identical replies while every role and backend effect is retained.


[Checked Lean source](../../beaconcrypt-core/proofs/lean/BeaconcryptCore/Computational/RawCtxGenericFamilyFrontend.lean).


## RawCtxGenericFamilyInterpretation

The same oracle interpreter commutes with the original generic Server, Beacon and full finite-family frontends. Its receive/send and public programs retain all replies and complete effects. These equations only reorganize the same source interpretation and introduce no callback-compatibility, freshness or security premise. They let the original pending/live compiler retain an entire family through concrete primitive forwarding.

- `server_interpretation`: The original Server frontend commutes with the same complete receive/send interpreter without a compatibility premise.

- `beacon_interpretation`: The same interpreter preserves every active or inactive original Beacon branch and complete optional result.

- `step_interpretation`: One indexed role or public operation interprets exactly the same callbacks and preserves the entire family.

- `schedule_interpretation`: The complete adaptive role/public client uses the same separately interpreted callbacks before any state or result projection.


[Checked Lean source](../../beaconcrypt-core/proofs/lean/BeaconcryptCore/Computational/RawCtxGenericFamilyInterpretation.lean).


## RawCtxGenericFamilyLive

The actual finite-role request schedule is extended by original current-chain and skipped-material reads. Each read privately receives the kernel selected from the complete family at the original owner, returns its original dependent optional reply, and appends that request/reply at the exact original history position. All other operations tick the same history. Kernel-map laws preserve the complete family and history under exact receive, send and read effect equations, and retain the same public services and original adaptive client.
These statements do not provide a hidden-input observer with unknown native bytes or a target-dependent freshness decision. A masked Slot reader must discharge the appropriate event coupling; byte aliases and public guesses remain explicit candidate events. The read payload and final whole state are private interpreter data. Native source interpretation, resource accounting and security advantages are separate consuming results. Snapshot and persistence behavior are excluded.

- `read_step`: Original live reads forward the actual selected kernel and record the original optional reply at the original API position.

- `step_map`: The complete original role/read step commutes with kernel conversion and retains the exact actual read history.

- `schedule_map`: Every adaptive original record/public/live-read continuation retains all role state, optional replies and exact history.


[Checked Lean source](../../beaconcrypt-core/proofs/lean/BeaconcryptCore/Computational/RawCtxGenericFamilyLive.lean).


## RawCtxGenericFamilyNative



- `step`: The full original role step is realized through an arbitrary backend, preserving every installed role and public effect.

- `live_step`: The full native live step retains the actual source optional read, original history and arbitrary backend effects.

- `live_schedule`: Arbitrary adaptive original live schedules preserve every native role, actual optional reply, history entry and backend effect.

- `actual`: The complete original live source has a concrete native-kernel representation under any mutable backend, without a supplied realization premise.


[Checked Lean source](../../beaconcrypt-core/proofs/lean/BeaconcryptCore/Computational/RawCtxGenericFamilyNative.lean).


## RawCtxGenericFamilyRead

A private typed read request retains the original finite-family owner and read kind together with the actual optional selected kernel. Its dependent reply is exactly the original source optional current chain or skipped material. The native reader forwards the extracted lookup result and rejects absent kernels. Kernel representation conversion preserves this whole reply. Reads contribute one read-interface attempt and no additional uniform requests, without claiming zero deterministic lookup or copying work.
The actual family frontend must supply the selected kernel and retain the original read history. The read payload is private interpreter state, not an adversary-visible secret. Hidden-input masking and freshness require their own consuming reader and source correspondence; these representation statements do not supply them. Snapshots and persistence are excluded.

- `source_value`: The typed family read returns the actual source optional value at the original requested owner.

- `map_value`: Private representation conversion leaves every actual optional read value unchanged.

- `native_uniform`: The actual native read makes no uniform request; its deterministic lookup and copying remain actual work.

- `query_total`: Each forwarded live-read attempt spends one read-interface query, including rejection and repetition.


[Checked Lean source](../../beaconcrypt-core/proofs/lean/BeaconcryptCore/Computational/RawCtxGenericFamilyRead.lean).


## RawCtxGenericLiveRead

The same live read frontend is parameterized by the private current-chain representation. It retains the original optional native-chain/material reply types, complete owner and history state, and a supplied operational exposure test. Native-byte and selected-slot instantiations use the same source query schedule; the selected exposure test does not become a secret-byte argument to the frontend. This module establishes exact interfaces and source-read equations, not a security or freshness assumption.

- `slot_compiler`: Instantiating private selected slots gives exactly the existing retained live frontend, including its exposure bit.

- `native_reader`: Native-byte kernels retain the exact existing optional chain/skipped-material lookup, including malformed slots.

- `native_source_forward`: The generic native reader is exactly the actual selected-role source read with its original history and full shared poststate.

- `read_step`: One compiled read retains the actual reply, complete owner/history state and the operational exposure bit.

- `primitive_handler`: Adding live reads leaves every full pending primitive callback and all of its effects unchanged.

- `read_total`: Every attempted live read issues exactly its one typed callback; optional rejection does not remove the attempt.

- `read_uniform`: The read interpreter makes no uniform request; native lookup, comparison, logging and copying remain deterministic local work.

- `original_step`: Every original public/record step retains the complete pending-owner computation and advances only the live-history timestamp.


[Checked Lean source](../../beaconcrypt-core/proofs/lean/BeaconcryptCore/Computational/RawCtxGenericLiveRead.lean).


## RawCtxGenericNativeCalls

The original interpreted receive and send programs are compiled through the native adapters into any native backend monad. Their concrete Calls reconstruct precisely the original complete source kernel and optional output, with no callback-realization premise. Every mutable backend effect remains in the same monad, including private KDF table, cursor, caches and instrumentation.
This operational construction may therefore be used before a selected cut with a dynamically changing selective interpreter. It does not assume the prefix uses a fixed retained table. It introduces no primitive, uniform-input, freshness, success or key-independence premise. The family frontend and pending compiler must still connect this exact call construction to their complete original source program.

- `receive_realized`: Any native interpreter realizes the complete source receive, retaining all mutable primitive effects and optional replies.

- `send_realized`: Any native interpreter realizes the source send including failed sealing and its complete advanced state.


[Checked Lean source](../../beaconcrypt-core/proofs/lean/BeaconcryptCore/Computational/RawCtxGenericNativeCalls.lean).


## RawCtxGenericOwnerInterpretation

Interpreting the actual kernel calls commutes with the original whole owner frontend. These laws only move the same oracle interpreter through the source syntax; they add no functional, distribution or security premise. The same query replies, owner fields, raw validation branches, optional failures and complete ambient effects remain present, including arbitrary public interleavings.

- `raw_interpretation`: Interpreting the original raw receive calls preserves every actual validation, optional reply and owner poststate.

- `send_interpretation`: The same send interpreter preserves empty rejection, actual optional sealing and failed-seal advancement.

- `owner_interpretation`: The complete original mixed-owner step uses exactly the separately interpreted source callbacks.

- `public_interpretation`: Public callbacks are interpreted by the same primitive handler without altering owner fields or replies.

- `public_schedule_interpretation`: Every complete adaptive original send/raw/public execution equals the same frontend over separately interpreted calls.


[Checked Lean source](../../beaconcrypt-core/proofs/lean/BeaconcryptCore/Computational/RawCtxGenericOwnerInterpretation.lean).


## RawCtxGenericOwnerMap

Changing only the private kernel representation commutes with the original established-owner adapter whenever the two concrete receive and send calls commute with that representation. The hypotheses are complete functional call equations in the same lawful monad, preserving all callback effects and optional replies; they are not distribution, freshness or security assumptions. The consuming retained-parent interpreter discharges these equations using its actual source calls. Empty sends, all raw rejection paths, successful publication, metadata, associated data, expected sender and attempted-receive counts remain present.

- `raw_map`: Every raw rejection and publication path changes only the kernel representation, retaining the actual attempts and complete effects.

- `send_map`: Empty sends reject before callbacks; all other send outcomes retain their actual post-kernel and every owner field.

- `owner_map`: The original mixed send/raw query and optional response types are unchanged under the private owner map.

- `schedule_map`: The complete adaptive mixed-owner continuation commutes with the same kernel map and original replies.

- `public_schedule_map`: Arbitrary interleaving with unchanged public callbacks preserves all source replies and the complete mapped owner.


[Checked Lean source](../../beaconcrypt-core/proofs/lean/BeaconcryptCore/Computational/RawCtxGenericOwnerMap.lean).


## RawCtxGenericRoleFamily

The entire finite Server/Beacon family changes only its installed kernel representation. Every Server peer entry, Beacon phase, identity, metadata and attempted-receive field remains at its original index. Native reconstruction and composition act on all kernels, including correlated paired owners. Original live-read owner lookup commutes with both native reconstruction and generic kernel maps, preserving missing-peer and inactive-phase rejection.
These are complete representation laws. The consuming generic frontends must prove actual source dispatch and publication and the cryptographic interpreters must supply their source call equations. No key independence, secret-input distribution, target freshness, allocation or registration behavior, security advantage or runtime bound is assumed or concluded.

- `roundtrip`: The full finite family reconstructs every original native role and peer at the same index.

- `compose`: Representation composition acts on every installed kernel without changing any role field.

- `native_selected`: An actual native reveal selects the same original owner and kernel after the whole-family representation map.

- `map_selected`: Whole-family kernel conversion preserves every accepted or rejected owner lookup.


[Checked Lean source](../../beaconcrypt-core/proofs/lean/BeaconcryptCore/Computational/RawCtxGenericRoleFamily.lean).


## RawCtxGenericRoleStorage

The finite role family retains every original Server peer and Beacon phase field while changing only the representation of installed ratchet kernels. Inactive Beacon variants retain all original identity and prekey material. The generic storage has the same original routing identifiers, associated-data inputs, metadata and attempted-receive counters. Native projection is a representation map, not a freshness or cryptographic assumption; the consuming source frontends must prove their complete operational correspondence.

- `phase_compose`: Two private representation changes preserve every inactive phase field and compose on the established kernel alone.

- `server_compose`: The entire native Server peer map retains the same fields through successive kernel interpretations.

- `beacon_compose`: Beacon projection composes on its installed kernel and preserves every other phase and outer identity field.

- `server_roundtrip`: A kernel representation that reconstructs each input preserves the entire original Server state, including every peer.

- `beacon_roundtrip`: Reconstructing kernels preserves every original Beacon phase, identity field and attempted-receive count.


[Checked Lean source](../../beaconcrypt-core/proofs/lean/BeaconcryptCore/Computational/RawCtxGenericRoleStorage.lean).


## RawCtxGenericServer

The original Server routing, identity-derived associated-data lookup and same-peer selection are parameterized by the private kernel representation. Raw header routing precedes the exact owner validation; sending retains AD lookup and sender selection before empty-input rejection. Complete peer maps, metadata, optional replies and every raw attempt remain present. The source correspondence is operational and does not assume distinct peer identities, target-free family state or freshness.

- `associated_map`: The same original identities supply associated data after any private kernel interpretation.

- `put_map`: Publication changes the same assigned peer and retains every other complete entry, including equal-identity aliases.

- `raw_map`: Exact route, AD lookup, peer selection and raw publication commute with the private kernel map.

- `send_map`: Source sends retain AD and sender lookup order and publish the same advanced peer on every optional outcome.

- `server_map`: Every original Server API query retains its complete optional reply and interpreted peer family.

- `schedule_map`: Any adaptive mixed Server schedule preserves all original API replies, every peer and all effects.


[Checked Lean source](../../beaconcrypt-core/proofs/lean/BeaconcryptCore/Computational/RawCtxGenericServer.lean).


## RawCtxGenericServerNative

The generic Server frontend realizes the original native mixed Server source program through complete receive/send call equations. These are operational equations in the same lawful monad and retain optional replies and every primitive effect. The native specialization and complete adaptive transport retain all routing, peer metadata, assigned IDs and attempted receives; they add no identity-injectivity, freshness or security premise.

- `associated_native`: Native AD uses exactly the same two original identity fields.

- `put_native`: Native publication changes the same peer kernel while preserving the rest of the entire Server.

- `raw_native`: The original native raw Server executes the same selected receive and exact full-map publication.

- `send_native`: The original native send retains routing order, every optional sealing result and the same advanced peer.

- `server_native`: One complete original native Server query realizes the generic source query with the same full state.

- `schedule_native`: Arbitrary original adaptive Server execution retains every peer and all effects under the concrete native interpreter.


[Checked Lean source](../../beaconcrypt-core/proofs/lean/BeaconcryptCore/Computational/RawCtxGenericServerNative.lean).


## RawCtxInitialChildSecrecy

The first evolving derivation in either direction consumes the selected half of one actual uniform 64-byte initializer. Its exact joint sampler retains the complete prior context and the other directional half. The child is the full 76-byte source output; no extra initial nonce is sampled. These component laws must be consumed by the actual initializer and family continuation, including retained initializer aliases and source freshness.

- `parts_observed`: Both orientations split the same actual initializer draw through an arbitrary complete continuation.

- `joint_separated`: The exact selected half is uniform independently of the complete prior context and retained opposite half, including adaptive direction selection before the initializer draw.

- `actual_source`: The initial-half child game supplies the exact serialized source input, other half and full original continuation to the ordinary secret-input endpoint.

- `primitive_bound`: Each first directional derivation has coefficient-one fixed-salt Extract and ordinary two-query HMAC reductions at this exact initial-half joint sampler.

- `sample_bound`: The source sampler pays the complete prior context and exactly one 64-byte initializer draw, without a distribution-based cost transfer.

- `joint_bound`: Serializing the selected half keeps the complete original initializer sampling budget.

- `reduction_queries`: The ordinary HMAC reduction uses two challenge calls and includes all prior, actual initializer and complete observer sampling.

- `execution_queries`: All source and challenger worlds count the original 64-byte initializer and their respective Extract, HMAC or independent 76-byte child draws.


[Checked Lean source](../../beaconcrypt-core/proofs/lean/BeaconcryptCore/Computational/RawCtxInitialChildSecrecy.lean).


## RawCtxInitialSecrecy

One exact root/context sampler feeds the actual paired 64 source initializer. The two role constructors consume the same 64 bytes and preserve opposite directions, zero counters, empty cache and the complete RustM result. The primitive observer receives the earlier context and the paired initializer results only after expansion; neither the root nor an initial half is added to its pre-Extract context. Public operations inside the observer remain the same real code.
The reduction reuses the checked full 76 endpoint through an explicit prefix-only comparison observer. That comparison pays two HMAC challenge calls and its own full 76/random-block draws. The actual randomized initializer draws only 64 bytes, charged separately. These are conditional ordinary-game reductions at the displayed exact joint sampler; the authenticated-root composition and source family must instantiate that sampler and observer.

- `root_field_unused`: The source's completed initializer depends on the role and response, not the consumed pending root field.

- `root_initializer`: The registration builder and paired source initializer consume the same exact 64-byte response.

- `root_address`: Serialization supplies exactly the original 32-byte root and shared ratchet domain to initialization.

- `source_pair`: Both actual source roles consume one shared 64 prefix and can be constructed without retaining the consumed root field.

- `actual_source`: The exact source initializer game is the existing secret-input game on the serialized root and unchanged pre-expansion context.

- `random_comparison`: The prefix-only full 76 comparison has the same evaluated complete observation as the actual 64 randomized initializer.

- `primitive_bound`: The actual paired 64 initializer reduces with coefficient one to fixed-salt Extract on this exact root/context sampler and ordinary HMAC PRF.

- `joint_bound`: Serializing the root into the exact Extract sampler retains every earlier uniform query without adding a draw.

- `reduction_bounds`: The existing full-output comparison reduction pays two HMAC challenge queries and the entire root sampler and original continuation.

- `actual_uniform`: The actual fixed initializer adds no uniform draw; all sampler and continuation sampling remains charged.

- `random_uniform`: The actual randomized initializer separately pays its one 64-byte draw, including a challenge discarded by later rejection.

- `challenger_uniform`: Every endpoint of the full 76 comparison is billed separately; none of its extra random bytes is assigned to the actual 64 source execution.


[Checked Lean source](../../beaconcrypt-core/proofs/lean/BeaconcryptCore/Computational/RawCtxInitialSecrecy.lean).


## RawCtxLiveLineage

Freshness uses the finite source lineage of one selected record input. Its forbidden 32-byte values are the selected material key, that input and every source root/first/next ancestor. Actual optional current-chain and skipped-key replies enter a monotone private history by value across owner names. Prior authorized disclosures remain in the history; disposed secrets are never added as new live capabilities. This is finite operational exposure bookkeeping, not unbounded public-function closure, a no-collision premise or a secrecy theorem. Public guessing and accidental aliases retain their separate computational terms.

- `self_mem`: Every source handle occurs in its own finite lineage.

- `ancestor_subset`: Earlier ancestors are retained transitively; first 32 and second 32 edges are both followed.

- `ancestor_forbidden`: Any original input ancestor is forbidden by its actual bytes, independently of owner or handle aliases.

- `material_key_forbidden`: A skipped-material disclosure exposes exactly first(input), so the target record key itself is forbidden.

- `forbidden_length`: A disclosure check scans one record key and the finite input lineage; no unbounded closure is evaluated.

- `disclosed_length`: Each actual optional reveal contributes at most one 32-byte value; rejected reveals contribute none.

- `fresh_note`: Recording the actual reply preserves prior knowledge and invalidates freshness exactly on a forbidden value.

- `fresh_tick`: Advancing the API timestamp leaves all earlier disclosed values intact.

- `freshValues_append`: Appending any actual 32-byte disclosure retains all earlier knowledge, including roots and public views.

- `exposedValues_false`: The finite exposure flag is exactly the negation of value freshness for the returned block list.

- `known_ancestor_not_fresh`: Previously returned root or ancestor bytes invalidate the selected record even after that native secret has disappeared.

- `known_first_alias_not_fresh`: A disclosed record key is also a disclosed first 32-derived chain for every target descended from that handle.

- `known_material_not_fresh`: A successful disclosure of the target record key invalidates that target regardless of its owner label.


[Checked Lean source](../../beaconcrypt-core/proofs/lean/BeaconcryptCore/Computational/RawCtxLiveLineage.lean).


## RawCtxLiveSourceFreshness

The finite live-disclosure freshness ledger is interpreted over the original native role/source experiment. The private arbitrary-predicate induction is the same complete-output sum argument used by StatefulGoodEvent, specialized through source-derived monotonicity below. Every actual optional reply, native role state, shared primitive state and timestamp remains present. Freshness can only be lost as history grows; no allowed later operation removes earlier knowledge. The fixed source and prior root/public disclosure list are unchanged. These statements supply operational freshness interfaces, not the missing cryptographic distribution or the complete global reveal policy.

- `source_step_fresh`: A fresh actual source poststate implies a fresh prestate, including failed operations and optional reveal rejection.

- `source_schedule_fresh`: Freshness at the end of any actual adaptive schedule excludes forbidden knowledge from its original history.

- `masked_step_fresh`: Masking cannot erase earlier forbidden knowledge: the original actual reply remains in private history.

- `step_agree`: Every complete fresh native transition has exactly the same probability after suppressing forbidden reveal replies.

- `output_fresh`: Masking forbidden live replies preserves every complete final native output whose actual private history is fresh.

- `event_fresh`: The final-fresh event is unconditioned: forbidden disclosures excluded by that event incur no additive probability term.


[Checked Lean source](../../beaconcrypt-core/proofs/lean/BeaconcryptCore/Computational/RawCtxLiveSourceFreshness.lean).


## RawCtxPendingFamilyLiveQueries

The actual whole-family live client forwards complete original role programs through one enriched pending primitive interface. A live-read query contains the original request and actual optional selected kernel; its original optional response is recorded in the unchanged timestamped history. Only private query arguments carry kernels. No unavailable target is added to the client, and these operational equations do not assert freshness or secrecy.

- `primitive_handler`: Forwarding a private role callback preserves that exact callback, including its complete ambient effect.

- `step_interpretation`: One whole original live operation uses the same interpreted pending calls and reader while preserving complete role state and original history.

- `program_interpretation`: Every complete adaptive role/public/live-read execution retains its original optional replies, full family, history and shared callback effects.


[Checked Lean source](../../beaconcrypt-core/proofs/lean/BeaconcryptCore/Computational/RawCtxPendingFamilyLiveQueries.lean).


## RawCtxPendingFamilyLiveTails

The actual original live client retains both complete role families and its timestamped read history through a selected private pending KDF. Source syntax derives the original family tail and complete external live continuation. The private read payload retains the original owner selection; the original optional reply is noted before the outside client resumes. No arbitrary native continuation or target-free-state premise is supplied.

- `program_original`: Every original role operation finishes its exact family program before ticking the original history and resuming the outside live client.

- `program_read`: The actual live read uses the requested current optional kernel and records its exact optional reply before continuing.

- `program_tail`: Every selected query in the actual full LIVE source schedule derives its original family tail, unchanged history and complete outside LIVE client.

- `reached_tail`: A supported cut of the actual complete LIVE program derives its concrete original family and outside-client tail, retaining the same reached primitive state.


[Checked Lean source](../../beaconcrypt-core/proofs/lean/BeaconcryptCore/Computational/RawCtxPendingFamilyLiveTails.lean).


## RawCtxPendingFamilyNative

The original complete native family and live-reveal source is exactly the enriched pending program under any mutable native backend. All original roles, optional replies and reveal history survive the native/refined projection, while the backend retains its entire private table, cursor, hash cache and other state. No fixed-source consistency or pending-call realization premise is supplied. The material-only context and state-dependent selected sampler are subsequent consumers of this exact execution equality.

- `program_interpretation`: The enriched complete family program runs the exact native calls, public services and original optional live reader in the same arbitrary backend monad.

- `actual`: The actual original full live source equals the same enriched source execution, preserving the complete native family and all mutable backend effects.


[Checked Lean source](../../beaconcrypt-core/proofs/lean/BeaconcryptCore/Computational/RawCtxPendingFamilyNative.lean).


## RawCtxPendingFamilyTails

A pending private KDF in the actual replicated role frontend keeps the complete original role family and its original outside family client. Server witnesses retain their original assigned-peer program; Beacon witnesses retain the exact established controls and associated data. The inner source tail is derived rather than supplied as an arbitrary native function. These operational source provenance statements do not assert freshness, independent keys or secrecy.

- `program_query`: Each complete role/public operation precedes the original adaptive family continuation.

- `server_selected`: A Server operation retains the exact selected Server program before replacing only its original family index.

- `beacon_selected`: An active Beacon operation retains its actual established controls and owner program before whole-family publication.

- `program_tail`: Every selected private query in the actual mixed role-family schedule has a concrete original Server or Beacon tail and full outside family client.

- `reached_tail`: The same actual supported family prefix yields its concrete pending role tail while retaining the complete reached primitive state.


[Checked Lean source](../../beaconcrypt-core/proofs/lean/BeaconcryptCore/Computational/RawCtxPendingFamilyTails.lean).


## RawCtxPendingLiveQueries

The full pending owner interface also retains the existing selected owner's adaptive live reads, original history and exposure bit. Erasure reconstructs the same original compiler before any private state or public reply is projected. Private full pending payloads are not network or reveal capabilities. This is an operational interface theorem; reached-input freshness and cryptographic hybrids remain separate consuming obligations. Snapshots, persistence and restoration are excluded.

- `primitive_erase`: Erasing a full pending primitive retains the existing original primitive's whole reply interface.

- `step_erase`: All live/public/record steps retain exact optional replies, owner fields, chronology and exposure bookkeeping.

- `schedule_erase`: Every finite adaptive live schedule erases before projecting any retained private state or public result.

- `source_project`: Full pending queries produce the same original live source trace and complete owner/history/primitive/candidate state.

- `query_bound_iff`: Enrichment preserves each query class on the full all-reply adaptive program, including live reads and repeated calls.


[Checked Lean source](../../beaconcrypt-core/proofs/lean/BeaconcryptCore/Computational/RawCtxPendingLiveQueries.lean).


## RawCtxPendingLiveTails

The generic live frontend retains the original owner program, its full history and exposure state, and the original external live client. Selected pending continuations are classified from the actual compiled source syntax; no arbitrary retaggable native callback is supplied. This is source continuation provenance, separate from freshness and the cryptographic hybrid bound.

- `program_original`: Every original owner request finishes its actual owner computation before ticking history and resuming the same external live client.

- `program_read`: An actual live read updates the original observation history and exposure bit before the unchanged external client receives its optional reply.

- `program_tail`: Every selected occurrence of the actual full live source program has an original owner tail followed by the same history update and external live client.

- `selected_slot`: The generic private selector specializes to the original mixed live scanner's exact send/receive callback classes.

- `reached_tail`: A supported stop of the actual full live source program supplies its concrete original owner and external-client tail without any separately assumed continuation property.


[Checked Lean source](../../beaconcrypt-core/proofs/lean/BeaconcryptCore/Computational/RawCtxPendingLiveTails.lean).


## RawCtxPendingMixedPrefix

The original adaptive computation is stopped immediately before its selected query, with the complete dependent query, reply continuation and interpreter state retained. The index counts every selected original callback, including repeated inputs; all other callbacks execute normally and preserve their effects. The owner and live specializations select both send and receive KDF calls. These are exact operational cuts, not a fresh-input or cache-miss premise. Snapshots, persistence and restoration are excluded.

- `scan_pure`: Completion retains the exact result and full reached interpreter state.

- `scan_selected_zero`: The selected original callback is stopped before any reply or callback effect.

- `scan_selected_succ`: Passing a prior selected slot executes its actual callback and counts it once even when the input repeats.

- `scan_other`: Every unselected callback executes normally without consuming the private-KDF selection index.

- `scan_finish`: Resuming the actual selected query restores the same complete execution, including early completion and all earlier effects.

- `pending_selected`: Every supported pending cut is an actual selected callback of the original program.

- `completed_query_bound`: Completed cuts preserve each underlying query budget by literal program equality, without distribution-based cost transport.

- `source_cut`: The selected mixed cut resumes to the same original live source result and complete retained state.


[Checked Lean source](../../beaconcrypt-core/proofs/lean/BeaconcryptCore/Computational/RawCtxPendingMixedPrefix.lean).


## RawCtxPendingNativeCallbacks

These callback equations expose the actual private KDF query beneath enriched native pending requests. Non-KDF callbacks retain their original full primitive work. They are used to compare adjacent mutable selective interpreters before a source-selected miss, not to assume fixed outputs or discard local work.

- `receive_kdf`: The selected receive callback forwards its original actual KDF request and decodes the complete actual reply in the same backend.

- `send_kdf`: The selected send callback forwards the same actual request and retains the actual decoded full response.

- `non_kdf`: Every non-KDF pending callback retains all original opening, sealing or public work when only native KDF replies may differ.


[Checked Lean source](../../beaconcrypt-core/proofs/lean/BeaconcryptCore/Computational/RawCtxPendingNativeCallbacks.lean).


## RawCtxPendingNativeCalls

The private pending source compiler executes the actual native receive/send adapters in any lawful backend monad. Each original KDF query retains its real request and complete decoded reply; the enriched pending payload is erased only at that callback. Opening, sealing and public operations preserve all backend state. This supports mutable private tables and cursors without fixing their values before the execution or postulating call-realization equations.

- `receive_call`: The complete pending receive call is the original native call under the same arbitrary mutable backend.

- `send_call`: The pending send preserves the actual advanced kernel and optional seal under the same mutable backend.

- `calls_interpretation`: Both interpreted pending callbacks form exactly the original native call record; no realization premise is supplied.

- `public_interpretation`: Every public query retains its actual callback and every state effect under the same mutable interpreter.


[Checked Lean source](../../beaconcrypt-core/proofs/lean/BeaconcryptCore/Computational/RawCtxPendingNativeCalls.lean).


## RawCtxPendingOwnerQueries

Private full pending receive/send requests factor the existing mixed owner compiler. Public queries, raw admission, optional replies, failed-send advancement and the complete owner state retain their original interfaces. Erasure removes only the added private pending context; it neither changes KDF inputs nor samples new values. The generic chain payload specializes to actual native chains or selected private labels.
These are operational equalities, not input secrecy or freshness assumptions. They support selecting the original adaptive KDF callback before its reply, with all pending state available to the private reduction. Snapshots, persistence and restoration are excluded.

- `receive_erase`: Erasure retains the exact original receive request and its full possible reply interface.

- `send_erase`: The pending send query preserves the exact original input and advanced sealing tail.

- `receive_call`: Full receive admission and every skip/open continuation survive pending erasure.

- `send_call`: Full send admission retains the original exhaustion, advancement and optional sealing reply.

- `step_erase`: Every original public or owner operation erases to the unchanged complete stateful source step.

- `schedule_erase`: Erasure commutes with every finite adaptive mixed schedule before any owner or reply projection.

- `selected_schedule`: The selected-label specialization is precisely the existing common source compiler.

- `query_bound_iff`: Every all-reply query-class bound is preserved on literal programs, including repeated private and public calls.


[Checked Lean source](../../beaconcrypt-core/proofs/lean/BeaconcryptCore/Computational/RawCtxPendingOwnerQueries.lean).


## RawCtxPendingOwnerTails

Every selected KDF occurrence in the actual mixed source schedule has a concrete original receive or send tail: complete pending resume/seal, exact owner publication, then the unchanged external source client. The pre-draw owner and that source client are retained separately from the new reply. Whole source induction discharges callback-origin obligations for arbitrary native or private-label chain payloads. Supported original cuts therefore derive the tail rather than assuming an arbitrary function on unavailable bytes can be retagged.
These are source syntax and provenance laws, not a fresh-input or security conclusion. A consuming native/label simulation must still preserve these concrete tails under its actual primitive interface and retained lookup. Snapshots, persistence and restoration are excluded.

- `program_query`: The actual public source query completes before its original adaptive continuation receives the reply.

- `receive_requested`: A reached original receive KDF is followed by its whole resume, owner publication and original source continuation.

- `receive_opening`: A completed receive opening publishes its exact optional reply before the original outer client continues.

- `receive_rejected`: Receive rejection retains the original kernel and publishes one failed original attempt.

- `send_requested`: The actual send KDF precedes the complete advanced sealing tail and unchanged outer source client.

- `program_tail`: Every selected occurrence in the actual mixed source schedule has an original receive or send tail and its unchanged public source continuation.

- `reached_tail`: Every supported original mixed KDF cut derives its exact concrete source tail, with no supplied retagging or callback-origin premise.


[Checked Lean source](../../beaconcrypt-core/proofs/lean/BeaconcryptCore/Computational/RawCtxPendingOwnerTails.lean).


## RawCtxPendingQueryTails

The original full receive/send programs have only their exact pending KDF continuations and occurrences in their actual completed callback tails. The receive proof follows the source skip rank; the send proof includes the advanced optional sealing result. These are compositional syntax laws. Concrete outer source induction must discharge the explicit continuation-property premises, so no security or arbitrary retagging premise is introduced. Snapshots, persistence and restoration are excluded.

- `receive_occurs`: Complete receive syntax has only original pending tails or occurrences in its actual completed callback continuation.

- `send_occurs`: Complete send syntax has only its original pending tail or occurrences after the actual advanced seal result.


[Checked Lean source](../../beaconcrypt-core/proofs/lean/BeaconcryptCore/Computational/RawCtxPendingQueryTails.lean).


## RawCtxPendingReceivePrefix

The original receive program is scanned at a chronological KDF callback index. Before that callback, all original effects and the complete private state execute unchanged; the saved stop retains the actual full pending request and its arbitrary outer continuation. Resuming the same stop gives the exact full original result and poststate, including completion before the selected index. A stop supported by the recursive receive program has its original normalResume continuation, derived from source syntax.
A callback index is not a distinct table-miss index. These operational statements do not claim a new entry, uniform native HKDF output, secrecy or absence of live exposure. The pending payload and stored continuation are private interpreter context, not a new public or reveal capability. Snapshots, persistence and restoration remain excluded.

- `scan_pending_succ`: Passing an earlier original KDF slot executes its original stateful callback before continuing the scan.

- `scan_pure`: Completion before the selected index retains the exact final result and current state.

- `scan_pending_zero`: Selecting the next KDF call stops before its original callback, with the entire unchanged state and continuation.

- `scan_open`: An opening executes its original optional callback without consuming a KDF selection index.

- `scan_finish`: Resuming the selected original request retains every preceding effect and the full adaptive continuation, including completion before that request.

- `program_pending`: A stop reached by the actual recursive receive program carries its original full pending payload and exact remaining receive continuation.


[Checked Lean source](../../beaconcrypt-core/proofs/lean/BeaconcryptCore/Computational/RawCtxPendingReceivePrefix.lean).


## RawCtxPendingReceiveQueries

The receive driver exposes its complete pending KDF payload only to a private internal interpreter. Forwarding that query to the original pending.request erases the added context and gives the exact original recursive source program. Rejected, staged-skip and opening branches retain all fields and optional replies; the same source rank terminates every possible reply continuation. No fuel fallback or target-dependent reconstruction is introduced.
Arbitrary lawful stateful interpretations preserve the complete result and their entire state. Selective query bounds are equivalent on the actual programs, and actual source admission retains at most 51 KDF callbacks and one opening callback. The added private payload is neither a public operation nor a live secret disclosure. These operational laws enable chronological selection of the original pending source request; they do not themselves prove a reached cache miss, uniform response, hidden selected input, alias exclusion or small live exposure. Local callback work is still governed by its original interpreter. Snapshots, persistence and restoration are excluded.

- `program_forward`: Erasing only the private pending payload yields the same complete original receive computation.

- `query_bound_iff`: Full private query payloads change neither the original selective call class nor its possible reply continuations.

- `program_query_bound`: The complete enriched source driver has exactly the original all-reply selective budget.

- `program_interpreted`: Any lawful stateful source interpreter runs the same complete receive program after private pending erasure.

- `receive_bound`: Original source admission still permits at most 51 pending KDF callbacks, counting all possible replies.

- `opening_bound`: Every original effect, including malformed pending states, retains the one-opening callback bound.


[Checked Lean source](../../beaconcrypt-core/proofs/lean/BeaconcryptCore/Computational/RawCtxPendingReceiveQueries.lean).


## RawCtxPendingSelectiveFamily

The actual selective private-table family game is executed through the enriched original LIVE source compiler. A state-dependent scan retains the complete original pending receive/send payload while the same mutable table and cursor choose the actual selected miss. Public HKDF stays the original real backend. The initial family may be arbitrary here: these operational laws do not establish an initial root distribution, identify cursor depth with a source sequence, or derive child-address separation from the parent miss. Those consuming source and alias obligations remain explicit.

- `source_program`: The complete enriched program is exactly the original selective native family game, retaining every original role/history field and complete mutable table, cursor and primitive state.

- `handler_same`: Adjacent selective stages agree literally on every complete enriched callback execution before the actual selected miss.

- `scan_same`: Adjacent complete source stages have the same enriched prefix before the selected miss.

- `scan_complete`: Completing the enriched scan retains the exact original selective source family at every cut depth and run stage, including early completion.

- `adjacent_complete`: Both adjacent actual family stages resume the same source-derived complete prefix with their original pending callbacks and full states.

- `reached_context`: Every supported dynamic selected miss derives the original complete source context, exact pending address and actual cache/match/depth facts from that same reached interpreter state.

- `source_query_bounds`: The same actual selective source and enriched program have identical selective underlying query caps by literal execution equality, retaining all complete state.


[Checked Lean source](../../beaconcrypt-core/proofs/lean/BeaconcryptCore/Computational/RawCtxPendingSelectiveFamily.lean).


## RawCtxPendingServerTails

A selected pending KDF inside the actual Server frontend retains the complete pre-call Server, assigned peer and original outside Server client. Its inner continuation is derived from the actual single-owner source program. Publication changes the same selected peer before the external Server continuation resumes. These source provenance statements do not assume that arbitrary native functions can be retagged and do not establish freshness or secrecy.

- `program_query`: The original Server operation completes before its original outside client receives the actual reply.

- `raw_selected`: A routed raw operation invokes the exact original selected-owner source program, then the same full Server publication and outside client.

- `send_selected`: A selected send completes its original owner operation before updating the same peer and continuing the original Server client.

- `program_tail`: Every selected occurrence in the actual adaptive Server program derives an original owner tail, exact peer publication and original outside client.

- `reached_tail`: A supported original Server cut derives its concrete tail from the same actual program and reached primitive state.


[Checked Lean source](../../beaconcrypt-core/proofs/lean/BeaconcryptCore/Computational/RawCtxPendingServerTails.lean).


## RawCtxQueryOccurrence

Syntactic provenance of complete dependent query continuations in the original finite oracle program. Occurrence permits every typed reply branch and thus needs no primitive success or probability premise. Supported mixed scanning derives occurrence in this same original program. The relation keeps the entire original continuation rather than only the query value.

- `pure_impossible`: A completed original program contains no later query.

- `query_cases`: An occurrence is either the exact current dependent query and continuation or one original typed reply branch.

- `here`: The exact current query and its original continuation occur at this node.

- `later`: An occurrence after any original typed reply remains an occurrence of the original whole program.

- `scan_occurs`: A supported stop of the actual mixed scanner contains a query and full continuation from the same original program.


[Checked Lean source](../../beaconcrypt-core/proofs/lean/BeaconcryptCore/Computational/RawCtxQueryOccurrence.lean).


## RawCtxQueryOccurrenceComposition

The complete original query continuation is preserved by sequential composition and literal query forwarding. These syntactic decomposition laws classify original program branches without assuming their runtime reachability or any primitive success.

- `bind_cases`: An original bound program occurrence comes from the left program with its same outer continuation, or from an original outer-client branch.

- `inl_cases`: Literal left forwarding retains the original query and entire forwarded continuation; no query can originate in the added capability.


[Checked Lean source](../../beaconcrypt-core/proofs/lean/BeaconcryptCore/Computational/RawCtxQueryOccurrenceComposition.lean).


## RawCtxReachedParentCut

The original pending receive queries use one concrete full 76 table and the original opening effects. Source memoization erases only the private table; chronological scanning retains the complete reached table and auxiliary state. Hits and misses remain separate actual callback branches. A uniform miss is an explicit comparison draw, not an assumption that source HKDF is uniform. The private stop and table are not public or live-reveal capabilities.

- `source_table`: The source table is the original fixed-function memoization, including all earlier bindings and opening effects.

- `kdf_run`: The selected KDF callback evaluates the address carried by that original pending request, then decodes the same complete response and retains both state components.

- `source_scan`: Scanning and then finishing the same source memo execution retains all original callback effects, including completion before selection.

- `atStop_source`: Selecting the original source response gives exactly the original full continuation, without altering the executed prefix or cache.

- `atStop_miss`: The reached miss invokes the supplied sampler once at the original pending address, inserts that same response and runs the original continuation with the complete next state.

- `atStop_hit`: A reached hit never invokes the selected sampler and retains the entire cache for the original continuation.

- `reached_miss`: A stop supported by the actual receive program resumes its original pending control and complete cache; no separately supplied successful cut or continuation is assumed.

- `retained_entry`: The full original continued program after the selected insertion realizes the retained predecessor entry over its actual prior cache; the final cache is erased only after this entire continuation.


[Checked Lean source](../../beaconcrypt-core/proofs/lean/BeaconcryptCore/Computational/RawCtxReachedParentCut.lean).


## RawCtxReachedParentSource

Concrete source opening and receive interpretation of the reached predecessor cut. The same pending receive state, prior cache, original full 76 response and complete shared primitive state feed the retained-entry continuation. The equations preserve rejected openings and every remaining skipped derivation. Selected-output uniformity and live freshness remain separate hybrid obligations.

- `view_program`: Erasing only the enriched pending-query payload retains the exact original chain program and full stateful opening effects.

- `view_native`: The retained cache lookup and actual source opening run the unchanged native typed receive driver with its complete shared primitive state.

- `recorded_native`: The actual continued memo cache after insertion realizes the original native receive with precisely that retained entry and the same shared primitive state.

- `recorded_cut`: The original pending resumption with its exact sampled response is the retained-entry label cut, before all remaining native skip and opening work.

- `reached_native`: Every supported original receive stop at a reached miss consumes its actual pending state and retained prior cache in the concrete native continuation, with the real opening interpreter.


[Checked Lean source](../../beaconcrypt-core/proofs/lean/BeaconcryptCore/Computational/RawCtxReachedParentSource.lean).


## RawCtxRetainedTable

A fixed-source memo handler retains every earlier cache binding, including outputs inserted by earlier hybrid steps. The complete adaptive continuation sees exactly the initial cache lookup with the actual fixed source as fallback. Only the final private table is erased after that continuation has finished. No consistency, freshness, output-uniformity or key-injectivity premise is used. The table is private proof context and supplies no new reveal capability.

- `view_stable`: Recording the value already selected by the complete cache view changes no later lookup.

- `memo_view`: An actual fixed-source query returns the retained binding when present and the original source output otherwise.

- `complete`: Every adaptive continuation retains the original result and auxiliary state for an arbitrary initial cache, including prior hybrid entries.

- `recorded_complete`: After recording one complete predecessor response, the whole continued memo execution realizes that retained entry and every original prior binding.


[Checked Lean source](../../beaconcrypt-core/proofs/lean/BeaconcryptCore/Computational/RawCtxRetainedTable.lean).


## RawCtxSelectedFamilyContext

A concrete selected context retains the original owner, Server, entire role family and live-history continuations as typed original source clients. Its pending receive/send is obtained from the actual source grammar. The stopped program accepts only the retained material coordinate: it retags all saved pre-draw kernels as known and installs the new hidden chain only at the selected pending resume. No arbitrary native function, target value or target-free family-state premise is stored in the context.

- `tail_context`: Every selected tail of the original complete LIVE family program has a context made solely from its original typed source frames.

- `frame_address`: The context address is the same complete original request carried by its saved source frame.

- `reached_context`: A supported original-index scan of the actual complete LIVE family source derives its concrete material-only context and original pending address, retaining the same reached mutable backend state.


[Checked Lean source](../../beaconcrypt-core/proofs/lean/BeaconcryptCore/Computational/RawCtxSelectedFamilyContext.lean).


## RawCtxSelectedFamilyNativeContext

The original selected KDF frame receives the actual full 76 response and runs its saved source continuations through the owner, Server or Beacon, entire family and original LIVE history. The same execution is obtained from the material-only stopped context by interpreting its hidden chain privately. Every original field and shared primitive effect is retained. The correspondence is proved from the concrete pending frame constructors, not assumed for an arbitrary continuation.

- `owner_cut`: The original pending owner frame receives the actual native response and finishes its complete original outside client from the material-only stopped context.

- `server_cut`: The exact assigned-peer publication and saved original Server continuation preserve the native owner result and every other peer.

- `family_cut`: The saved Server or Beacon frame reinstalls its actual returned state and preserves the entire original family continuation.

- `frame_cut`: The actual selected complete LIVE frame receives the same native full response and preserves all family fields and actual read history under the material-only source cut.

- `frame_run`: Evaluating the complete source cut preserves the entire mutable shared primitive state; only private kernel representation is mapped.


[Checked Lean source](../../beaconcrypt-core/proofs/lean/BeaconcryptCore/Computational/RawCtxSelectedFamilyNativeContext.lean).


## RawCtxSelectedInitialConstructor

The actual 64-byte source initializer installs two oppositely oriented chains and no initialization nonce. Its private first 32-hidden constructor retains the other 32 bytes, zero counters, empty cache slots and complete RustM result. A full 76 analysis response enters only through its exact shared 64-byte prefix; no source call or nonce draw is added. The complete uniform 64 law will preserve arbitrary continuations and both role orientations without exposing the first 32 coordinate through the retained constructor.

- `halves64`: Both 32-byte halves are exactly the original consumed response bytes.

- `new_map`: The original zero-counter/empty-slot constructor commutes with the private chain map and preserves its entire RustM result.

- `split64`: The exact extracted split chooses opposite directions from the same 64-byte output for Beacon and Server.

- `from64_initial`: The actual 64-byte initializer is exactly the first 32-hidden zero-state constructor, with no source nonce.

- `full_prefix`: A full 76 analysis response contributes exactly its shared 64-byte prefix to the original initializer.

- `full_initial`: The retained full 76 entry initializes only the selected first 32 and other directional 32, irrespective of its analysis nonce.

- `source_initial`: The actual fixed-source 64 initializer supplies exactly this complete hidden-first constructor in either role.

- `opposite_roles`: The same pair of chain values has opposite source orientation in the two roles; no independent second draw is introduced.

- `split_reconstruct`: The two initial halves reconstruct every byte of the exact original 64-byte response.

- `uniform_native`: The complete 64-byte draw supplies both directional chains before the same full continuation, preserving all prior context.

- `uniform_native_bound`: The literal initial 64 execution charges its complete prior sampler,64-byte draw and original initializer continuation.

- `delayed_initial`: After the same initial 64 split, the concrete private constructor can run before drawing only its omitted first 32 coordinate.


[Checked Lean source](../../beaconcrypt-core/proofs/lean/BeaconcryptCore/Computational/RawCtxSelectedInitialConstructor.lean).


## RawCtxSelectedInitialEntry

A retained initialization entry omits first 32 entirely. Its second 32 and final12 coordinates reconstruct the same full 76 value when the private selected chain is supplied; initial 64 is exactly that value's shared prefix. A matching public first 32 projection is direct disclosure. This is private coupling bookkeeping, not an adversary interface or a claim that a reached source output is uniform.

- `realize_fromOutput`: The same full response is recovered without storing the selected first 32 in the entry.

- `projection_parts`: Each public view selects its exact coordinate from the same reconstructed full response.

- `public_table`: The cached public view keeps the same full 76 and the real source at every other address.

- `public_before`: Before matching first 32 disclosure, every public reply is independent of the missing initial chain.

- `public_exposed`: A matching first 32 view discloses the selected initial chain, although the request input is its root.

- `public_source`: Retaining a real initializer response leaves every public evaluation exactly the fixed source.

- `initial_prefix`: Initial 64 is precisely selected first 32 followed by the retained other directional chain.

- `source_initial_chains`: The actual source initializer obtains both directional values from this same ratchet-domain entry.


[Checked Lean source](../../beaconcrypt-core/proofs/lean/BeaconcryptCore/Computational/RawCtxSelectedInitialEntry.lean).


## RawCtxSelectedInitialMask

Replacing the retained initializer first 32 coordinate changes a private known-input KDF callback only when its exact input is the initializer root. Both directions share the actual ratchet domain, so this case is charged to the original candidate list rather than excluded by a new freshness rule. Public projections, optional live replies and complete shared effects stay identical on both sides. The supplied child response may be arbitrary; this module makes no target-independence or small-alias-probability claim.

- `initializer_exact`: A known private initializer request is exactly an equality of the actual 32 input bytes.

- `query_safe`: Outside a recorded initializer-root input the full primitive callback does not use the retained first 32 coordinate.

- `routed_eq`: Exact-input routing replaces the coordinate throughout the same full primitive interface.

- `distance`: The full adaptive replacement costs the actual initializer-root candidate event, with every prior candidate and separate live-disclosure flag retained.

- `inputs_bound`: Each actual primitive callback adds at most one private known-input candidate.


[Checked Lean source](../../beaconcrypt-core/proofs/lean/BeaconcryptCore/Computational/RawCtxSelectedInitialMask.lean).


## RawCtxSelectedInitialSampler

The initial first 32 coordinate is delayed only from explicitly uniform 64/76-byte samplers. Both laws quantify over the complete continuation and retain the other directional chain, the full 76 nonce when sampled, the address and all earlier context. They do not transport source costs through distribution equality or claim that an arbitrary reached native response is uniform.

- `full_uniform`: Uniform full 76 splits into the retained second 32/nonce pair and the missing first 32.

- `full_observed`: Splitting the same full output preserves every effect and result of an arbitrary complete continuation.

- `delayed_eq`: Delaying only the missing first 32 retains the same original context, full 76 remainder and complete observation.

- `initial_uniform`: Uniform initial 64 contains two independent 32-byte halves, in retained-other/selected-first order.

- `initial_observed`: The two halves may be passed separately to the full continuation without discarding any initial 64 bit.

- `shared_prefix_parts`: The initial 64 split and the full 76 split select the same two byte vectors.

- `initial_delayed_eq`: An actual 64-byte uniform draw can delay first 32 past a complete observer that retains the other direction.

- `original_bound`: The full 76 source sampler pays every context, output-byte and continuation request.

- `delayed_bound`: The delayed full 76 interpreter pays 44 retained bytes, all continuation work and 32 delayed bytes.

- `initial_original_bound`: The initial 64 program pays 64 actual uniform byte requests plus all context and observation work.

- `initial_delayed_bound`: The initial 64 delayed program pays both 32-byte draws explicitly without using a distribution equality as a cost proof.


[Checked Lean source](../../beaconcrypt-core/proofs/lean/BeaconcryptCore/Computational/RawCtxSelectedInitialSampler.lean).


## RawCtxSelectedInitialSecond

The actual 64-byte initializer also supports hiding its second 32 coordinate: Beacon sends and Server receives on that coordinate. The retained state stores only first 32, with the same opposite role orientation, zero counters and empty cache. The proofs split one actual 64 draw into its two halves and retain arbitrary complete continuations. Full 76 appears only through an explicit prefix comparison; no initial nonce or additional12-byte source draw is introduced.

- `split64_second`: The exact source split places the hidden second 32 in Beacon-send and Server-receive.

- `from64_second`: The original 64-byte initializer is exactly the second 32-hidden constructor in both roles.

- `second_uniform`: Uniform 64 splits in retained-first/selected-second order without losing any original response bit.

- `second_observed`: The same two-half draw preserves an arbitrary complete continuation in retained-first order.

- `full_second`: A retained full 76 predecessor initializes only its first 32 and hidden second 32; the analysis nonce is unused.

- `source_second`: The fixed source supplies the exact second 32-hidden constructor from its actual initial 64 response.

- `uniform_native_second`: Splitting the actual 64 draw preserves both roles and every result of the complete native continuation.

- `delayed_second`: The omitted second 32 may be drawn after a complete observer of the actual private constructor and retained first 32.

- `original_bound`: The original second 32 cut pays 64 uniform bytes and every earlier sampler and observation request.

- `delayed_bound`: The delayed interpreter separately pays both 32-byte draws and the entire retained-state observation.

- `paired_roles`: Both actual role initializers use the same selected and retained halves, with complementary directions and no second source draw.


[Checked Lean source](../../beaconcrypt-core/proofs/lean/BeaconcryptCore/Computational/RawCtxSelectedInitialSecond.lean).


## RawCtxSelectedInitialSource

The original receive and send programs run over one retained initial first 32 entry and the entire prior lookup. Both current chain fields, staged material, context and complete shared primitive effects are preserved. The labeled KDF handler explicitly retains a target parameter: a known callback at the initializer root reconstructs the target as first 32 material. The separate InitialTable.initializerQuery/step_before interface identifies that case; these exact source equations do not pretend it is target-free. Actual initial 64 uses the shared prefix and does not manufacture an initialization nonce.

- `receive_kdf`: The native request and selected initializer step share the complete response before the same full-state receive continuation.

- `receive_open`: The opening callback reads the same material, sequence and context; retaining the initializer does not alter any optional primitive effect.

- `receive_program`: Every remaining source skip/open continuation retains the initializer entry and complete callback state through original rejection and rollback.

- `send_kdf`: Both source directions use the same retained initializer response and shared primitive state.

- `send_seal`: The seal callback omits only chain fields that its actual getters do not read and retains the complete optional primitive computation.

- `send_program`: Original send admission, the one KDF callback and failed-seal advancement retain the complete same-table source program.

- `receive_query_bounds`: Exact whole-program interpretation preserves every selective underlying query bound; evaluated distribution equality is not used to infer work.

- `send_query_bounds`: The same exact selective-query preservation holds for the entire send program, including exhausted and failed-seal branches.

- `response_source`: A retained original initializer specializes every typed KDF response back to the actual fixed source; the entry carries no new primitive correctness assumption.


[Checked Lean source](../../beaconcrypt-core/proofs/lean/BeaconcryptCore/Computational/RawCtxSelectedInitialSource.lean).


## RawCtxSelectedInitialTable

One initial first 32 coordinate is omitted from the retained full 76 entry, while its other directional chain and optional analysis nonce remain present. The full retained lookup preserves every prior address. Both actual initial 64 and subsequent 76 derivations use the same ratchet domain: a known private input equal to the initializer root therefore reconstructs the selected first 32 as material, and must not be declared target-free. The explicit initializerQuery flag identifies this case for separate ancestor/alias accounting. Only full 76 comparison bookkeeping uses the nonce; no actual 64 initializer nonce is invented.

- `step_table`: The complete same-table KDF response commutes with the selected-chain representation, including retries of the initializer address.

- `step_before`: Only outside an actual known initializer-address request is this label KDF step independent of the hidden first 32 coordinate.

- `lookup_source`: An original source entry reconstructs every real fixed-HKDF response, with the same shared ratchet domain.

- `view_recorded`: A recorded full 76 comparison output retains every previous cache/fallback response while separating only first 32.

- `public_table`: Public projections select their exact coordinate of the same retained full 76 response.

- `public_before`: Public projections outside first 32 at the initializer address retain the full prior lookup and do not read the selected coordinate.

- `public_exposed`: Direct public first 32 exposure returns the actual selected initial-chain bytes.


[Checked Lean source](../../beaconcrypt-core/proofs/lean/BeaconcryptCore/Computational/RawCtxSelectedInitialTable.lean).


## RawCtxSelectedParentAliases

Exact byte aliases in either direction and public projections use the same selected child response, while all other addresses retain the prior lookup and predecessor entry. Routing preserves the complete shared primitive state, optional reads, original candidate prefix and separate direct-disclosure flag. The coupling charges an actual candidate event; its real-world and uniform-world bounds require their separate computational arguments. Neither keys nor request addresses are assumed distinct.

- `hidden_receive`: The unavailable child input uses one complete supplied response in the original receive interface.

- `known_receive`: Every known equal-byte receive input routes to that same child response; no distinct-key premise is used.

- `hidden_send`: Send and receive share the identical unavailable-input response.

- `known_send`: Known send inputs use the same concrete equality and response as receive inputs.

- `public_consistent`: In the routed comparison public aliases use the selected child response only at its exact label and input; all other public evaluations are unchanged.

- `read_consistent`: Routing never changes an actual optional live reply, including known-value aliases.

- `distance`: The complete routed continuation differs by at most its original final candidate event, retaining every prior entry and the separate direct-disclosure flag.


[Checked Lean source](../../beaconcrypt-core/proofs/lean/BeaconcryptCore/Computational/RawCtxSelectedParentAliases.lean).


## RawCtxSelectedParentCalls

The exact retained-parent receive and send interpreters instantiate whole-owner calls. Native admission, remaining skips/opening, exhausted sends and advanced optional sealing all keep the same complete primitive state. The mapping changes only private chain representation. Retained lookup applies only to private KDF calls; a consuming public frontend uses the same real fixed-source evaluation on both sides. These operational equations do not supply freshness or replace source outputs with uniform values.

- `receive_map`: Original native receive admission and every later optional source effect retain the exact interpreted whole kernel and primitive poststate.

- `send_map`: Original send exhaustion, KDF resumption and advanced optional sealing retain the same complete native kernel and primitive state.


[Checked Lean source](../../beaconcrypt-core/proofs/lean/BeaconcryptCore/Computational/RawCtxSelectedParentCalls.lean).


## RawCtxSelectedParentCandidates

The candidate tests retain the actual full predecessor draw and its material-only context. Real-child guesses pay their own Extract/HMAC tester and a finite-image term; uniform-child guesses use the separate delayed-coordinate bound. The real tester evaluates the unchanged public function on the actual returned candidates. Neither a real correlated child nor the retained predecessor is silently treated as an independent source. The native composition supplies the source-reachable prefix, stopped continuation and concrete list budget.

- `bytes_same`: The tester and main reduction receive precisely the same retained predecessor/input sampler.

- `real_bound`: Real-child input recovery pays the additional exact-sampler tester advantages; it is not assigned a uniform guessing bound.

- `uniform_bound`: With an independent child, the original full predecessor's omitted coordinate can be delayed past the entire adaptive candidate computation.

- `tester_queries`: The additional tester pays two HMAC challenge queries, all original predecessor/observer uniform calls and its actual candidate evaluations of the real public function.


[Checked Lean source](../../beaconcrypt-core/proofs/lean/BeaconcryptCore/Computational/RawCtxSelectedParentCandidates.lean).


## RawCtxSelectedParentCompiler

The actual private pending owner/live compiler executes the same retained-parent source calls and real public backend. Its full source query, original optional response and owner/history state are retained through interpretation. The compiler has no target-byte argument; target bytes occur only in the mathematical native reader and representation used for the source equation. No arbitrary continuation compatibility premise is introduced.

- `calls_interpreted`: The exact original receive and send source programs interpret to the retained-parent calls, before owner publication.

- `original_step`: The same actual original public/record compiler runs the retained source calls with every owner field and public effect intact.

- `pending_step`: The full private pending payload is instrumentation; its actual source compiler interprets to the same retained owner/public step.

- `owner_program`: Every original adaptive owner/public client is interpreted with the same full owner and primitive state.

- `live_step`: The actual full live frontend runs the same pending owner source computation or original live lookup before its precise history update.

- `live_program`: The same complete original live client has no separately supplied continuation law: the actual compiled program realizes the retained interpreter directly.

- `native_program`: The native retained-table continuation equals interpretation of the original complete live compiler, retaining all source state except its added exposure ghost.


[Checked Lean source](../../beaconcrypt-core/proofs/lean/BeaconcryptCore/Computational/RawCtxSelectedParentCompiler.lean).


## RawCtxSelectedParentContext

Concrete retained-parent contexts are extracted from the same supported original live source stop. Each context stores the original owner request and typed outside client, original owner and its typed outside client, complete pending receive/send request, and live history/ghost. Its stopped observer uses only the retained material coordinate. This is an actual source grammar witness, not an arbitrary supplied cut or native continuation compatibility assumption.

- `tail_context`: Every source-derived live tail has one concrete original receive/send context, including both exact outside clients and the complete history.

- `frame_address`: The retained address is the same concrete request in the original stopped source frame, with no index or parent supplied independently.

- `native_cut`: The same concrete receive/send context gives the complete native continuation from its predecessor output and the material-only stopped observer.

- `reached_context`: A supported scan of the original complete live client derives its exact context and original pending address before the selected response, retaining the full reached primitive state.


[Checked Lean source](../../beaconcrypt-core/proofs/lean/BeaconcryptCore/Computational/RawCtxSelectedParentContext.lean).


## RawCtxSelectedParentEntry

The predecessor request retains one exact full 76 response. Its material coordinates and request address are private coupling provenance; the unavailable second 32 coordinate reconstructs that same response on every retry and public projection. A matching public second 32 view is direct ancestor-output exposure even when its input differs from the selected chain. First 32 and final12 views retain their actual coordinates.
This bookkeeping does not resurrect a disposed native secret or add a live reveal capability. Structural target-independence does not establish a reached uniform cut, exclude byte-value aliases or erase earlier authorized knowledge. Source KDF/library equations and complete local work remain explicit. Snapshots, persistence and restoration are excluded.

- `realize_fromOutput`: The retained predecessor entry reconstructs the same complete response, not a new chain or nonce draw.

- `parts`: The hidden second 32 coordinate and both retained material coordinates are projections of one full response.

- `projection_parts`: Each actual public projection has its exact stored coordinate; only second 32 contains the unavailable next chain.

- `decoded_response`: Retrying the predecessor derivation returns the same chain/material pair and cannot draw another next chain.

- `public_table`: The public response is a projection of the same retained predecessor entry, and all other addresses remain the actual source.

- `public_before`: Before an actual matching second 32 projection, the public reply cannot depend on the retained hidden chain.

- `public_exposed`: A matching predecessor second 32 request returns the actual selected chain bytes, even though its input need not equal those bytes.

- `public_source`: Retaining an actual predecessor output agrees with the original fixed public function on every address and projection.

- `step_table`: The retained predecessor returns the unavailable marker on retries; interpretation recovers the complete same-table source response, including target/predecessor cycles.

- `stream_source`: Retaining the original predecessor response changes no complete source value, even when another request aliases its address.


[Checked Lean source](../../beaconcrypt-core/proofs/lean/BeaconcryptCore/Computational/RawCtxSelectedParentEntry.lean).


## RawCtxSelectedParentFamilyMap

The retained-parent native/label source relation extends through the actual entire Server, finite role family and live-read client. It uses the concrete source receive/send equations and the original optional reader, with the same real public service. Every peer, role field, attempted-receive count, history and shared primitive effect is retained. These operational equations do not assume target freshness or a separately supplied continuation relation.

- `label_calls`: Interpreting the exact pending label calls gives the actual retained-parent receive and send programs.

- `server_program`: The complete original Server continuation retains every peer and callback effect under the actual native/label retained-parent relation.

- `family_program`: The actual entire indexed role/public continuation retains every Server, Beacon and common real public effect.

- `live_program`: The original complete adaptive LIVE family client retains its actual optional native read values and full history through the retained-parent representation.


[Checked Lean source](../../beaconcrypt-core/proofs/lean/BeaconcryptCore/Computational/RawCtxSelectedParentFamilyMap.lean).


## RawCtxSelectedParentHop

The retained predecessor hop uses the same actual joint sampler for the main Extract/HMAC observer and the additional real-input recovery tester. Only private KDF callbacks receive the selected full child output. All public HKDF evaluations stay fixed real evaluations. The complete source-derived continuation, shared state, candidate ledger and original unconditioned good event remain together. The actual source cut must instantiate this continuation; no arbitrary reached-state uniformity or global protocol freshness is inferred here.

- `local_bound`: The private/native-reader step and its target-free observer pay only the original masked input-candidate event.

- `actual_route`: The original real-child experiment and its target-free Extract observer differ by the exact real input-candidate event.

- `random_route`: The independent-child experiment pays the original delayed-coordinate candidate event when returning to the private source interface.

- `actual_bound`: The real private-to-observer comparison pays the separately constructed actual-input tester and its full 76 finite-image term.

- `random_bound`: Only the independent-child comparison uses the delayed uniform-coordinate guess bound, with the complete retained candidate list.

- `bound`: One retained-parent child replacement pays two constructed Extract observers, two ordinary two-query HMAC reductions, the real full-output image term and the separately justified uniform-input guess term.

- `observer_bounds`: Both constructed observers retain the complete original observation's uniform budget; the separate candidate tester has its own real-evaluation bill below.

- `reduction_queries`: Both reductions pay two HMAC queries and the original prefix/full-parent/observation coins; the additional tester pays up to the complete candidate count in real HKDF evaluations.

- `challenger_queries`: Both ordinary-game challengers retain every prior/parent/observer coin, the Extract replacement key and the two random HMAC blocks; the independent full child has its own 76-byte bill.


[Checked Lean source](../../beaconcrypt-core/proofs/lean/BeaconcryptCore/Computational/RawCtxSelectedParentHop.lean).


## RawCtxSelectedParentLive

The live continuation retains one prior full-output lookup and the same predecessor entry through receive, send, public views and actual optional chain/material reads. Its private sticky flag marks either an unavailable current-chain read or a public second 32 projection of that predecessor. Masking these direct disclosures preserves the unconditioned event restricted to the good flag, including an already exposed initial state. The source compiler supplies the private pending kernels; an arbitrary primitive client is not itself a proof of source reachability. Byte aliases, earlier disclosure freshness and the reached parent sampler remain separate obligations of the native composition.

- `query_safe`: Outside either direct disclosure the complete primitive transition is unchanged, including retained prior responses and optional replies.

- `flag_step`: Every supported step retains the prior flag and marks exactly this query's direct exposure.

- `sticky`: Direct disclosure remains marked through every later callback and optional reply.

- `hit_marked`: A disclosure marks the transition even when actual and masked replies differ.

- `agree_good`: Both complete good-output transition distributions agree before either actual direct disclosure.

- `event_good`: Masking both direct-disclosure interfaces preserves the same unconditioned good event on the complete adaptive continuation; prior exposure is never reset.


[Checked Lean source](../../beaconcrypt-core/proofs/lean/BeaconcryptCore/Computational/RawCtxSelectedParentLive.lean).


## RawCtxSelectedParentLiveCut

The original receive/send owner tail finishes before the same live history update and original external client. Its stopped Slot program is constructed from the original pending state, owner, public source continuation and material coordinate alone. The complete native-to-Slot equations preserve all optional replies and shared state, and project away only the added exposure ghost. Actual supported tail provenance is established by the live source grammar; no arbitrary native continuation law is assumed here.

- `after_map`: Original live history and the full external client follow the same owner result; the private exposure flag alone is omitted from native state.

- `receive_cut`: The actual receive owner tail, original history update and full external live client resume from the same predecessor response through a program that does not inspect its next-chain coordinate.

- `send_cut`: The actual send owner tail, original history update and full external live client resume from the same predecessor response through a program that does not inspect its next-chain coordinate.


[Checked Lean source](../../beaconcrypt-core/proofs/lean/BeaconcryptCore/Computational/RawCtxSelectedParentLiveCut.lean).


## RawCtxSelectedParentLiveSource

Complete retained-parent owner/public/live-read continuations preserve the actual owner, read history and shared primitive state. Both public interfaces use the real fixed-source backend. The label observer adds an exposure flag; its projection removes only that private ghost, since known byte aliases need not have the same flag as a hidden slot. Native reads retain their actual optional bytes and all observations. No input uniformity, reached-cut provenance or freshness conclusion is assumed or inferred here.

- `reader_map`: Native byte lookup is the same original read after interpreting the private kernel, including absent slots.

- `step_map`: One actual record/public/read operation retains its optional result, complete owner and native history; only the label exposure ghost is projected away.

- `schedule_map`: The same full adaptive live client preserves all original history and shared effects through retained private lookup and real public evaluation.


[Checked Lean source](../../beaconcrypt-core/proofs/lean/BeaconcryptCore/Computational/RawCtxSelectedParentLiveSource.lean).


## RawCtxSelectedParentNativeBackend

The original native mixed-owner backend uses the same retained private KDF response table as the interpreted native Calls. Every opening, sealing, commitment and writer callback remains the original full shared-state implementation. Adapter and complete call equalities discharge the concrete source-realization obligations used by the finite role frontends. This is an explicit retained-table intermediate; public HKDF remains the separate real service, and no freshness or cryptographic premise is introduced.

- `receive_adapter`: The actual native receive adapter decodes the same retained response and opens with unchanged source arguments and shared state.

- `send_adapter`: The actual send adapter uses the same retained KDF and complete original seal, commitment, serialization and optional result.

- `receive_realized`: The concrete retained-table receive discharges the original owner realization obligation for the entire native kernel.

- `send_realized`: The concrete retained-table send discharges the original owner realization obligation through failed seals and retained advanced state.

- `owner_realized`: The original raw/send owner is realized by concrete retained-table Calls without any supplied callback-compatibility premise.

- `source_backend`: Retaining an actual source response recovers the original mixed native backend on every request.

- `owner_queries`: Complete original owner interpretation preserves every selective primitive-query cap by literal program equality.


[Checked Lean source](../../beaconcrypt-core/proofs/lean/BeaconcryptCore/Computational/RawCtxSelectedParentNativeBackend.lean).


## RawCtxSelectedParentNativeCompiler

The original native-chain pending compiler is interpreted by the same retained private KDF lookup, source opening/sealing callbacks and real public services as the native owner experiment. Erasing the added private pending payload keeps each actual request, response and complete callback state. These laws close the compiler-to-native-call interface; the retained table is an explicit intermediate game, with no freshness, uniformity or security premise.

- `receive_call`: The actual native pending receive call is exactly the retained-table native driver, including all remaining skip/open work.

- `send_call`: The original pending send call retains its actual exhaustion, full KDF input, advanced sealing state and optional result.

- `calls_interpretation`: Interpreting both exact native pending calls gives the concrete source call record, with no compatibility premise.

- `public_interpretation`: Every public callback is the same real source service, preserving its complete shared primitive state.

- `compiler_step`: The exact original native-chain pending frontend interprets to the full native owner/source step.

- `compiler_schedule`: The complete original adaptive native pending program equals the same native owner/public execution before projecting any state.

- `query_bounds`: Literal full-program equality preserves every selective primitive-query cap with all native and shared state retained.


[Checked Lean source](../../beaconcrypt-core/proofs/lean/BeaconcryptCore/Computational/RawCtxSelectedParentNativeCompiler.lean).


## RawCtxSelectedParentNativeContext

The supported original native frame resumes under its actual private pending interpreter and original optional live reader. Projection removes only the added frontend exposure ghost; the original owner, live history, complete shared primitive state and adaptive outside client are retained. These equalities identify the actual source continuation with the native context used by the retained-parent cut, with no supplied compatibility or security premise.

- `live_step`: One original native live operation keeps its actual optional reply, owner and history, omitting only its operational exposure ghost.

- `live_program`: The complete original live schedule equals the same native source execution with all actual history and shared effects retained.

- `receive_tail`: The original pending receive resumption publishes the same optional opening and continues through the exact native owner tail.

- `send_tail`: The original pending send keeps its advanced native state even after a failed seal, then runs the same outside owner client.

- `lift_owner`: Completing the original owner work precedes the same native history update and entire live outside client.

- `frame_native`: Resuming the exact reached native frame at the supplied complete response gives its original native context, retaining all original state except the frontend ghost.

- `frame_reply`: The original selected callback returns precisely the frame response from its same retained full output and leaves shared state unchanged.


[Checked Lean source](../../beaconcrypt-core/proofs/lean/BeaconcryptCore/Computational/RawCtxSelectedParentNativeContext.lean).


## RawCtxSelectedParentOwner

The same retained private KDF table is interpreted through complete original owner and public schedules. Actual public HKDF evaluation remains the real fixed source on both sides, with the same public coins and shared commitment cache. Every owner field and optional reply is retained; only the private chain representation changes. An arbitrary prior private table describes an intermediate operational game, not a claim that independently replaced values equal the public function.

- `step_map`: Each original record/public operation preserves every owner field and the full actual shared primitive computation.

- `schedule_map`: The complete adaptive owner/public continuation retains original responses and full state through the concrete private interpretation.


[Checked Lean source](../../beaconcrypt-core/proofs/lean/BeaconcryptCore/Computational/RawCtxSelectedParentOwner.lean).


## RawCtxSelectedParentOwnerCut

A concrete original owner tail is retagged at its original pending KDF request, before the new chain coordinate is drawn. The stopped program retains the original owner, its actual public source continuation and all pending controls. The operational equations consume the exact full predecessor response and preserve complete native resumption, publication and later public/record effects. Reached support is supplied by the separately proved source grammar, not by an arbitrary continuation compatibility premise.

- `known_owner`: Retagging a pre-draw owner never compares with or reads the later target coordinate.

- `receive_cut`: The actual pending receive finishes its original publication and original adaptive owner/public continuation after the same full predecessor response.

- `send_cut`: The actual selected send retains its advanced kernel even when sealing fails, then resumes the same complete original owner/public client.


[Checked Lean source](../../beaconcrypt-core/proofs/lean/BeaconcryptCore/Computational/RawCtxSelectedParentOwnerCut.lean).


## RawCtxSelectedParentPrivate

The selected child is replaced only on private KDF callbacks. Public HKDF evaluations remain the supplied common real function at every input, including a successful guess of the selected input. The same complete original input list bounds changes at known private byte aliases; it may conservatively also count public inputs and live values. The read-only exposure flag and all shared primitive effects are retained. This is the native private-table comparison interface, not a public random-function game.

- `public_real`: Every original public projection stays real, even when its input is the selected private input.

- `known_receive`: A known receive alias uses the same full child response as the omitted input, while every other private input retains the predecessor lookup.

- `hidden_receive`: The unavailable receive input uses the selected complete response.

- `known_send`: Send uses the identical known-input alias test and child response.

- `hidden_send`: Send and receive reuse the same unavailable-input response.

- `read_same`: Actual optional read replies stay unchanged by private alias routing.

- `distance`: Private alias routing costs at most the same original full candidate event, retaining all source state and prior read exposure.


[Checked Lean source](../../beaconcrypt-core/proofs/lean/BeaconcryptCore/Computational/RawCtxSelectedParentPrivate.lean).


## RawCtxSelectedParentPrivateEvents

Private alias routing retains the same actual public HKDF service while hidden live reads are masked only for an unconditioned event that excludes their recorded disclosure. No disclosure probability is added. The remaining comparison cost is the original target-free masked execution's complete candidate event, in either direction. The source composition must derive the actual freshness implication and the candidate budget.

- `alternate_safe`: Private alias substitution changes no permitted optional read or callback effect.

- `query_safe`: Routing equal-byte private aliases preserves every non-exposing callback in both reader interpretations.

- `event_good`: The full original event excluding the recorded hidden read has equal unconditioned probability under the actual and masked readers, even with private aliases.

- `decision_probability`: The Boolean experiment tests the original event and the actual final disclosure flag together, without conditioning.

- `local_bound`: The original private-table experiment and target-free masked observer differ only by the complete masked candidate event; excluded disclosures have no additive charge.


[Checked Lean source](../../beaconcrypt-core/proofs/lean/BeaconcryptCore/Computational/RawCtxSelectedParentPrivateEvents.lean).


## RawCtxSelectedParentPrivatePatch

A selected child response patches only its exact private KDF address, retaining the prior private lookup and the predecessor entry's priority. The parent/child input collision is explicit and must be charged by the consuming source hybrid; it is not a freshness assumption or excluded source execution. The real public backend is untouched. These table equations realize an arbitrary child response under private alias-consistent routing.

- `address_eq`: Exact private addresses compare the original byte values, without a distinct-key or handle-injectivity premise.

- `parent_retained`: The predecessor entry keeps priority, including collisions; the explicit source collision event is not silently removed.

- `child_response`: Away from the parent-input collision, the native selected child request uses the exact arbitrary full response.

- `step_patch`: The patched private table equals routing known byte aliases to the same hidden-input response, while preserving every nonalias and parent retry.

- `native_step`: The actual native KDF response under the private patch is the interpretation of the same alias-consistent Slot response.

- `native_cut`: The complete concrete reached-parent continuation admits an arbitrary privately patched child response; its real public backend and entire source client remain unchanged.


[Checked Lean source](../../beaconcrypt-core/proofs/lean/BeaconcryptCore/Computational/RawCtxSelectedParentPrivatePatch.lean).


## RawCtxSelectedParentPrivateRealization

Private alias-consistent routing realizes the exact patched native table. The common public interface is the real fixed-source function, including at a guessed selected input. The explicit parent-address collision remains a separate event to charge. These equalities preserve the original full pending program and all optional/shared effects; the routing interpreter may know the mathematical target, while the stopped source program does not.

- `handler_patch`: Private known aliases and hidden requests use the same arbitrary child response; parent retries and every public/read/open/seal effect retain the same original behavior.

- `live_real`: The original full pending handler erases only pending payloads, retaining actual source public HKDF at every input.

- `live_patch`: The actual pending source interpreter with a private patch is exactly the private-only consistent handler; public evaluations remain real.

- `native_cut`: The concrete native one-owner tail with an arbitrary private child replacement realizes the same material-only source program under exact private alias routing and real public HKDF.


[Checked Lean source](../../beaconcrypt-core/proofs/lean/BeaconcryptCore/Computational/RawCtxSelectedParentPrivateRealization.lean).


## RawCtxSelectedParentPublic

Public HKDF projections use the same retained predecessor response and the entire prior lookup, including earlier comparison responses. Masking only the predecessor's second 32 projection removes its unavailable next-chain coordinate. Its first 32 key and final12 nonce remain the original coordinates; every other address uses the unchanged prior lookup. These equations identify direct exposure, not a small-probability guess or a security property of public HKDF. The later freshness gate must exclude direct ancestor disclosure. All retained context is private; snapshots and persistence are outside this experiment.

- `table`: Every public projection is of the exact same retained full response.

- `before`: Before direct exposure the complete public reply is independent of the retained second 32 coordinate.

- `exposed`: Direct predecessor second 32 exposure returns the actual unavailable chain bytes.


[Checked Lean source](../../beaconcrypt-core/proofs/lean/BeaconcryptCore/Computational/RawCtxSelectedParentPublic.lean).


## RawCtxSelectedParentReadMask

The final-game read mask retains one common public interface on both sides, which can be the actual fixed public HKDF. Only an unavailable current-chain read sets this direct-disclosure flag. Public guesses and accidental aliases remain separate candidate events; they are not freshness exclusions. The complete continuation retains all original private primitive state, candidates and prior exposure. Source reachability and the actual permitted-reveal freshness implication are supplied by the native composition.

- `query_safe`: Every non-exposing callback retains the exact original reply and all effects, including the common real public evaluation.

- `event_good`: The original adaptive event and candidate trace agree whenever no hidden current-chain value was disclosed. Public guesses remain in that event.

- `alias_distance`: Equal-byte routing is only an intermediate comparison, charged to the original full candidate event with the read-only flag retained.


[Checked Lean source](../../beaconcrypt-core/proofs/lean/BeaconcryptCore/Computational/RawCtxSelectedParentReadMask.lean).


## RawCtxSelectedParentSampler

One explicitly uniform full 76 predecessor response supplies its retained address/material and selected next-chain coordinate under the same complete continuation. Only the chain coordinate is delayed past an observer that receives the original context and retained entry. The context may contain all prior private state and cache information. This is a law of the stated sampler, not a proof that an actual reached source response is uniform or fresh; no source capability or storage service is added.

- `delayed_eq`: Delaying only the independent chain coordinate retains the same entire context, predecessor entry and observer result.

- `original_bound`: The original sampler charges the context, all 76 response bytes and every observer query on every reply.

- `delayed_bound`: The delayed program separately charges the 44 material bytes, the full observer, and the later 32 chain bytes.


[Checked Lean source](../../beaconcrypt-core/proofs/lean/BeaconcryptCore/Computational/RawCtxSelectedParentSampler.lean).


## RawCtxSelectedParentSecrecy

The same complete uniform predecessor response supplies its retained material and the next secret input. The following endpoint keeps the actual prior context, predecessor address, complete challenge response and continued observation together. The observer never receives the predecessor's second 32 coordinate. Public computations inside that observer remain actual fixed computations.
These are the primitive hop and sampling laws consumed by the native reached-cut composition. A source cut must supply its concrete observer and preserve the retained cache and exposure events; no arbitrary reached-state uniformity or absence of disclosure is assumed here. Primitive Extract security remains attached to the displayed joint sampler, and Expand uses the existing ordinary two-query HMAC game.

- `joint_separated`: Equality holds for the full joint distribution, including the retained parent entry and every prior context field.

- `actual_source`: The exact same predecessor draw and entire continuation are the source side of the existing secret-input endpoint.

- `primitive_bound`: Coefficient-one Extract and ordinary HMAC terms at the same actual predecessor/input/context distribution.

- `joint_bound`: Sampling the prior context and complete parent response is charged in the actual original order.

- `reduction_bounds`: Every constructed HMAC reduction retains the complete predecessor and observer costs and makes at most two challenge queries.

- `actual_uniform`: The actual parent-then-child source execution retains both the complete parent draw and all observer work.

- `challenger_bounds`: All challenger worlds pay for the same parent sampler, both random HMAC blocks where used, and the full original observer.

- `candidate_bound`: The complete target-free continuation may retain prior entries and repeat candidates; the unconditioned hit bound counts its actual whole list.


[Checked Lean source](../../beaconcrypt-core/proofs/lean/BeaconcryptCore/Computational/RawCtxSelectedParentSecrecy.lean).


## RawCtxSelectedParentSource

The original pending receive/send continuations run over one retained prior lookup plus the selected predecessor entry. Exact callback equations preserve both live chain coordinates, all staged material/control/context and complete shared primitive effects. The receive cut is before the remaining skip/open continuation; the send cut uses the actual extracted resumption and preserves advancement even when sealing fails. Only chain fields proved unread by primitive getters are omitted from those callbacks.
The supplied predecessor response and pending state remain private source context. A reached prefix must still establish their exact request/entry correspondence and the prior cache/miss distribution before any uniform replacement. These operational laws do not provide that correspondence, a target-free reached sampler, small exposure, an alias exclusion or a public random-HKDF assumption. The fixed-source specialization reconstructs actual typed responses from the original predecessor output. Selective query bounds transfer through literal full-program equality; local lookup/KDF/conversion work and the separately sampled full 76 response remain charged. Snapshots, persistence and restoration are excluded.

- `receive_kdf`: The native request and selected predecessor step share the complete response before the same full-state receive continuation.

- `receive_open`: The opening callback reads the same material, sequence and context; retaining the predecessor does not alter any optional primitive effect.

- `receive_program`: Every remaining source skip/open continuation retains the predecessor entry and complete callback state through original rejection and rollback.

- `receive_cut`: The stopped point is the actual source KDF resumption, before any remaining skipped derivation or optional opening. The same complete predecessor output supplies the material and hidden next chain.

- `send_kdf`: Both source directions use the same retained predecessor response and shared primitive state.

- `send_seal`: The seal callback omits only chain fields that its actual getters do not read and retains the complete optional primitive computation.

- `send_program`: Original send admission, the one KDF callback and failed-seal advancement retain the complete same-table source program.

- `send_ready`: The actual extracted send resumption installs the predecessor's same second 32 chain and first 32/final12 material before sealing.

- `send_cut`: After the actual KDF response, the same source seal and full advanced state survive both success and failure; the label continuation cannot inspect the next chain.

- `receive_query_bounds`: Exact whole-program interpretation preserves every selective underlying query bound; evaluated distribution equality is not used to infer work.

- `send_query_bounds`: The same exact selective-query preservation holds for the entire send program, including exhausted and failed-seal branches.

- `response_source`: A retained original predecessor specializes every typed KDF response back to the actual fixed source; the entry carries no new primitive correctness assumption.


[Checked Lean source](../../beaconcrypt-core/proofs/lean/BeaconcryptCore/Computational/RawCtxSelectedParentSource.lean).


## RawCtxSelectedParentTable

The selected predecessor response overrides only its exact original address in a retained prior lookup. Every other prior response remains unchanged. The concrete finite-cache view after recording that response equals the same retained-entry lookup, so previous bindings and fallback values are not reset. Both hidden requests and known predecessor retries reconstruct this same complete response without chain or address injectivity.
The uniform memo handler is an explicit comparison sampler. Its hit equation returns the original response and cache; a miss draws and records one full 76 response in that cache, with a proved 76-byte query cap. No theorem here replaces publicly evaluable HKDF by this sampler or assumes that native source outputs are uniform. The actual reached chronological hybrid must derive the prior lookup and selected miss, preserve previous knowledge and prove its source/input exposure conditions. Prior lookup, cache and entry are private protocol/coupling context, not new adversary capabilities. Local lookup, conversion and KDF work remains computation. Snapshots, persistence and restoration are excluded.

- `step_table`: The exact prior stream is retained at every other address; the selected predecessor response is shared on both hidden and known aliases.

- `lookup_source`: Specializing the prior stream to the original fixed source recovers every original complete response.

- `view_recorded`: Recording the selected complete output preserves every other prior cache binding and fallback value; only its unavailable coordinate is represented separately.

- `memo_miss`: At an actual miss, this comparison handler draws exactly one complete response and records it in the same prior cache.

- `memo_hit`: An actual hit returns the recorded response and whole unchanged cache, with no fresh draw.

- `memo_uniform_bound`: Every comparison-table query pays at most the complete 76-byte miss draw; hits retain their exact zero-draw equation.


[Checked Lean source](../../beaconcrypt-core/proofs/lean/BeaconcryptCore/Computational/RawCtxSelectedParentTable.lean).


## RawCtxSelectedPendingCut

The selected predecessor entry is constructed from the original pending source KDF request and its full 76 reply. Every old chain is retained as known before this new draw; the stopped send or receive continuation uses only its material projection and a hidden next-chain marker. The exact original callback is included before all remaining receive skips/opening or the advanced send/seal tail. Full state, optional failure, prior lookup values and equal-byte aliases are preserved.
These equations describe the same source driver under the explicitly retained lookup. Its fixed-source specialization is supplied by the preceding response laws. They do not prove that this pending request is reached at a fresh table miss, that its response is uniform, or that prior/live ancestor knowledge is absent. Neither a target-dependent rebase nor byte distinctness is used to construct the stop. Full 76 sampling and local lookup/KDF/conversion work are separate from these literal program equations; no work bound is inferred from evaluated distribution equality. All pending fields are private protocol context, not an adversary API. Snapshots, persistence and restoration are excluded.

- `receive_pending`: All original pending chains remain known before the selected draw; no comparison with that future draw constructs the stopped context.

- `send_pending`: Source send likewise retains its original complete pending state without inspecting the future chain coordinate.

- `receive_cut`: The original pending receive and its exact request address produce the stopped continuation from material alone, before every remaining skip/open effect.

- `send_cut`: The original send request supplies the entry address, while its complete advanced sealing continuation is constructed without the new chain coordinate.

- `response_requested`: The selected response belongs to the original requested address, with the same prior lookup retained everywhere else.

- `receive_requested`: The selected callback is the next actual pending receive request, followed by its entire remaining source driver.

- `send_requested`: The actual send KDF query at the original request address precedes the same advanced sealing tail.


[Checked Lean source](../../beaconcrypt-core/proofs/lean/BeaconcryptCore/Computational/RawCtxSelectedPendingCut.lean).


## RawCtxSelectiveChainBudgets

The actual selective finite Server/Beacon family and its exact stopped prefix have uniform-call cap U + 76*(S+51*R) + 64*(S+R+H). The all-reply source budgets count original sends S, raw attempts R, caller coins U, public commitments H, public HKDF views K and reveals E. Private KDF calls are bounded by S+51*R; public HKDF views remain fixed real evaluations and never cause private-table sampling. Every attempted record and possible callback continuation is included, without a cache consistency, selected-miss, target honesty or freshness premise.
The proof derives the backend's three costs directly from its original syntax, derives the caller-coin cap from the complete source schedule, and consumes the existing native KDF/hash source caps. The exact prefix bound follows from literal scan-and-finish equality. It does not transfer costs across equality of distributions or assert a bound for an arbitrary hidden-input observer. Initial generation, reduction challengers and deterministic primitive, parser, lookup, copying, hash and table work remain separate explicit work. No cryptographic assumption or secrecy conclusion is added.

- `native_uniform`: The real native backend's only additional uniform work is its possible full 64 commitment-cache sample.

- `compiled_uniform`: The compiled backend charges private full 76 draws separately from caller coins and shared commitment hashes.

- `backend_uniform`: Every possible backend continuation retains the three separate actual query reservations.

- `native_coins`: Native operation lifting cannot manufacture a caller coin request.

- `protocol_coins`: Both role frontends and all public services forward only original caller coins.

- `reveal_coins`: Every live read retains its original reply and adds no caller coin.

- `source_coins`: The original source budget supplies the caller-coin reservation for the entire native family.

- `family_uniform`: The actual selective family charges all source work without a target, miss or honesty premise.

- `prefix_uniform`: Stopping before an original private callback cannot spend more uniform calls than the complete same source execution.


[Checked Lean source](../../beaconcrypt-core/proofs/lean/BeaconcryptCore/Computational/RawCtxSelectiveChainBudgets.lean).


## RawCtxSelectiveChainDepth

The actual private-only finite-family compiler supplies S+51R possible private KDF calls, including cache hits, failed operations and all adaptive continuations. Every callback preserves or advances the selected cursor, with at most one advance per private call and none for public evaluations or other backend operations. Complete executions therefore stay below their original depth plus S+51R. A supported selected stop is strictly before that bound because its unexecuted private query remains charged.
Starting the cursor at zero gives a proved finite bound for selected hybrid stages. This is cursor-stage coverage; it does not by itself equate an arbitrary native entry counter with zero or identify an accepted record with that cursor. Actual initialization, direction/record provenance and final target selection consume those separate source correspondences. No fresh-miss, honesty, success, uniformity or cryptographic premise is added, and no probability or cost is transported across distribution equality.

- `step`: Each supported original callback advances the cursor at most once; public and other native callbacks cannot advance it.

- `complete`: Every complete adaptive schedule preserves prior depth and spends at most its all-reply private-query cap, including cache hits.

- `compiled_private`: Private-only compilation preserves the original native KDF cap; public HKDF evaluations do not enter it.

- `source_private`: The actual finite-family source supplies S+51R private calls under every possible callback continuation.

- `pending`: A supported selected stop occurs strictly before the original private-call cap, with its unexecuted callback still charged.

- `family_depth`: Every supported actual family execution stays within the source-derived private-call depth cap.

- `stage_lt`: Starting at logical depth zero, every supported selected cut has a stage index in the finite source private-call catalogue.

- `family_stage_lt`: The original finite-family source instantiates the strict stage cap S+51R without an opaque protocol budget or fresh-miss premise.


[Checked Lean source](../../beaconcrypt-core/proofs/lean/BeaconcryptCore/Computational/RawCtxSelectiveChainDepth.lean).


## RawCtxSelectiveChainGame

The complete original finite native family and reveal program runs under one shared private full 76-byte cache and a selected-direction cursor. Only a private cache miss at the cursor's exact ratchet address can be randomized, and only before the chosen stage depth. All other misses remain fixed-source evaluations. Hits retain complete earlier bindings. A matching original call advances the cursor through that same reply's next 32-byte projection; nonmatching calls leave its position unchanged. Public HKDF bypasses the private table and remains real.
Stage zero retains the complete native execution, shared primitive state, all role/history fields and the complete private cache after erasing only cursor instrumentation. Adjacent stages differ only at an actual matching miss at their common selected depth. These are exact operational games, not a proof that a chosen logical record reaches a fresh miss, that native byte values cannot alias, or that the selected initial input has the required computational distribution. The consuming protocol reduction must discharge those source and freshness conditions, then instantiate the explicit Extract/PRF observer. No later descendant or unrelated-direction miss is made uniform merely by being a private KDF request. Snapshot, persistence and restoration are excluded.

- `private_hit`: Repeated private addresses keep their complete response, even when they match the current cursor.

- `private_selected`: A selected-prefix miss samples exactly one full response before advancing through its actual next 32-byte projection.

- `private_real`: Every unselected miss remains the actual fixed source computation.

- `cache_hit`: Recording a hit does not change any prior table entry.

- `private_zero`: Stage zero is the original fixed memoized callback with only private cursor bookkeeping added.

- `zero_complete`: Zero selected substitutions retain the complete original result, common state and prior table under every adaptive continuation.

- `adjacent_same`: The only point where adjacent stages may differ is an actual matched miss at the selected logical depth.

- `adjacent_splice`: An eligible adjacent hop changes one real full response to one uniform full response, retaining the same actual table and cursor update continuation.

- `private_state`: Every supported private reply retains exactly its complete cache update and actual cursor transition.

- `advance_depth`: Nonmatching calls leave the selected logical position unchanged; a matching original call advances it once.

- `private_uniform`: The full 76-byte reservation is charged even though the selected-direction cursor uses only its next 32-byte projection.

- `family_zero`: Zero substitutions preserve the complete private table as well as every native state field and original reply.

- `source_zero`: Erasing only analysis cache/cursor recovers the original native family with its full role, history and shared primitive state.


[Checked Lean source](../../beaconcrypt-core/proofs/lean/BeaconcryptCore/Computational/RawCtxSelectiveChainGame.lean).


## RawCtxSelectiveChainPrefix

Two neighboring actual selective native games have the same complete prefix up to the first matched cache miss at the selected logical depth. The scanner saves the original dependent query continuation and the complete reached interpreter state before its callback. The exact adjacent decompositions retain every original source result and state field, including early completion and the entire private table.
At a supported private cut, the earlier stage uses the actual full output and the next stage samples one full output; both then execute the same complete real future backend. Cursor depth never decreases, so later descendants and permitted current-chain reveals are not replaced by additional uniform tables. The actual finite native family instantiates this same common-prefix equality. This is a checked operational splice; the reached source sampler and concrete family native-to-Slot continuation must still establish a target-free Extract/PRF observer. The saved private state and arbitrary saved function are not claimed available to such an observer. No fresh miss, uniform input, source target lineage or small primitive advantage is assumed. Snapshots, persistence and restoration are excluded.

- `scan_pure`: The complete client result and reached state survive early completion.

- `scan_cut`: The first eligible original callback is saved with its complete original continuation.

- `scan_other`: Every preceding query executes with its original optional reply and complete state effect.

- `handler_same`: Before the cut, the two complete stateful interpreters are literally the same operation.

- `scan_finish`: Completing the actual cut resumes exactly the original complete stateful client.

- `scan_same`: The entire prefix before the selected miss is identical in both neighboring native stages.

- `adjacent_complete`: Both complete neighboring stages use the same actual reached prefix, followed by their complete original resumed programs.

- `pending_origin`: A supported cut is an eligible callback of the actual original program, with its same dependent continuation and reached state.

- `handler_monotone`: Every actual backend step preserves or increases the cursor depth, including failed operations and cache hits.

- `saturated_step`: Once its selected prefix is past, the stage uses the real memoized backend for every future callback.

- `saturated_run`: Every complete continuation after the selected prefix keeps all future derivations real, including later current-chain reveals and descendants.

- `private_isCut`: The Boolean private cut test is exactly the stated source cache/match/depth event.

- `finish_real`: At the actual selected cut, the real stage resumes the original full future program through the unchanged real backend.

- `finish_random`: The neighboring stage draws one full child and runs the same complete real future continuation, retaining its next-chain descendants.

- `family_adjacent`: The actual finite native family has one common reached prefix for each adjacent stage, retaining its original complete role/reveal continuation.


[Checked Lean source](../../beaconcrypt-core/proofs/lean/BeaconcryptCore/Computational/RawCtxSelectiveChainPrefix.lean).


## RawCtxSelectiveKdfFamily

The complete actual finite native Server/Beacon role and reveal program is compiled with one shared table for private record KDF requests only. Every public HKDF view goes to the unchanged fixed real backend, even if its input equals a private table address. All native replies, paired-role correlations, role state, history and shared primitive effects are retained.
The real fixed-source table equality requires its explicit functional consistency condition. Hybrid tables need separate selected-input alias and freshness arguments; public views must not silently be answered from those tables. The source uniform ledger is transported through literal computation equality, not equality of evaluated distributions. This module does not choose a target, assert input secrecy or prove a hybrid step. Local deterministic computation is retained. Snapshot, persistence and restoration interfaces are excluded.

- `compiler_real`: At the real fixed source, private-only compilation preserves every backend reply and state effect.

- `public_compiler`: Public HKDF projections bypass the private table at their complete original request.

- `backend_complete`: The exact native backend is the one-table computation before any output or state projection.

- `source_complete`: Both native directions and all peers share one private table while every public evaluation and reveal retains its real source behavior.

- `source_uniform`: Memoization preserves the source's complete underlying uniform ledger, including every failed receive.


[Checked Lean source](../../beaconcrypt-core/proofs/lean/BeaconcryptCore/Computational/RawCtxSelectiveKdfFamily.lean).


## RawCtxSelectiveTargets

A finite catalogue names a Server peer and a Beacon handle for each selected established session. Target choices add one physical direction and a bounded logical record index relative to the supplied entry chains. Source selection reads the existing directional sender's installed send chain; it invents no owner or replacement kernel. The selected family keeps the original native schedule, bounds the randomized prefix by that target's record number and runs stage zero when the selected sender is absent.
The final adversary-selected target is handled by an exact winning-event partition of the same original execution, then an explicit sum over all targets or the full sessionCount*2*recordCount factor. No pre-execution choice by the adversary is assumed. The catalogue itself does not prove shared-root establishment, zero counters, record reachability, secrecy or a uniform source sampler. Those consuming source facts must tie catalogue entries to actual initialization; nonzero entry counters require explicit source sequence offsets. Snapshot, persistence and restoration are excluded.

- `orientations`: Both orientations point at the actual complementary handles, with no independent-owner premise.

- `target_card`: Source target selection has exactly the finite session, two-direction and logical-record factors.

- `record_bound`: The selected record is positive and lies within the explicit catalogue's record bound.

- `starting_missing`: Missing native owners remain absent, rather than being replaced by a fresh selected kernel.

- `starting_present`: A supported selected input is exactly the existing native send-chain field.

- `event_partition`: A post-execution adaptive target choice partitions the original winning event exactly, without preselecting the adversary's eventual choice.

- `selection_sum`: Fixed-target reductions are summed over the adversary's original final-choice partition.

- `selection_factor`: A common per-target bound pays the full established-session, two-direction and reachable-record selection factor.

- `selected_zero`: At stage zero the selected experiment retains the complete real family cache/state regardless of target availability.

- `selected_missing`: Selecting an absent native sender never changes the ongoing original family schedule.


[Checked Lean source](../../beaconcrypt-core/proofs/lean/BeaconcryptCore/Computational/RawCtxSelectiveTargets.lean).


## RawCtxSourceValueLedger

A private finite value ledger observes actual source replies without changing the native role state, original reveal history, public randomness or shared primitive effects. It records both real public HKDF 32-byte projections and the existing optional live chain/material replies. The nonce projection is 12 bytes and does not directly disclose a 32-byte chain. Arbitrary computations on public bytes remain adversarial candidate work, not an unbounded knowledge closure. Prior actual root disclosures can enter the initial ledger without inventing a later root-read service. Freshness still uses the actual values of the consuming hybrid's finite lineage.

- `public_chains`: Both source 32-byte projections record their actual reply, including the shared first 64-byte prefix.

- `returned_length`: One original source callback returns at most one directly exposed 32-byte key/chain coordinate.

- `step_values`: The observed source step preserves every original reply and state, retaining the complete prior ledger.

- `schedule_projection`: Erasing only the private value ledger recovers the complete original adaptive execution syntactically.

- `schedule_values`: Every adaptive source schedule retains its prior value ledger and adds at most its explicit total callback budget.

- `schedule_fresh`: Disjointness of the complete value ledger implies disjointness of its prior prefix. This auxiliary predicate includes public outputs and is not the protocol freshness rule; public-output aliases must be charged as candidate events.

- `source_public`: The actual public projection reply, native roles, original history and shared state are all retained in the ledger step.

- `uniform_bound`: Every underlying uniform-oracle bill is unchanged by the adaptive source value ledger; only finite local bookkeeping is added.


[Checked Lean source](../../beaconcrypt-core/proofs/lean/BeaconcryptCore/Computational/RawCtxSourceValueLedger.lean).


## RawCtxStatefulPendingPrefix

This scanner stops before a query selected by its complete current interpreter state. It retains the original dependent pending payload, exact outside continuation and full reached state. This allows a source KDF pending request to remain available while the private cache/cursor determines whether the callback is the next selected miss. Every unselected callback executes normally, including repeated table hits and optional failures. The generic operational laws do not assert that a cut occurs or that an input is fresh or uniform.

- `scan_pure`: Early completion retains the actual result and complete reached state.

- `scan_cut`: The actual state-dependent selected callback is saved before its reply or effect.

- `scan_other`: Every unselected callback preserves its original reply and complete state effects before scanning its original continuation.

- `scan_finish`: Resuming the same saved frame gives the exact original complete stateful execution, including executions that finish before any cut.

- `scan_same`: Literal agreement on unselected callback executions gives one common complete prefix, without comparing evaluated costs or conditioning on a cut.

- `pending_origin`: A supported pending result derives the actual selection condition and original syntactic query occurrence with the same complete continuation and reached state.


[Checked Lean source](../../beaconcrypt-core/proofs/lean/BeaconcryptCore/Computational/RawCtxStatefulPendingPrefix.lean).


## RawCtxStatefulPrefixInvariant

A state-dependent pending prefix may use a source invariant to establish the same complete prefix under two handlers. The invariant is checked on every supported unselected callback, and the common computation is an exact OracleComp equality. Completed and pending outputs retain their actual final state. These generic operational premises must be derived by the source consumer; they neither assume selection occurs nor condition on a selected branch.

- `scan_same`: Agreement only at invariant states suffices when actual unselected callbacks preserve that invariant.

- `scan_valid`: Every completed or pending supported prefix retains the invariant at its actual reached state.


[Checked Lean source](../../beaconcrypt-core/proofs/lean/BeaconcryptCore/Computational/RawCtxStatefulPrefixInvariant.lean).

## Source execution and final-lineage checkpoint

This topic checkpoint adds 65 modules and 365 guarded statements. It connects the current authenticated uniform-root experiment to one shared initial64 response, constructs executable carried source contexts and exact adjacent source continuations, and appends a private final-lineage checker to the original completed family execution. It is not the completed evolving-chain secrecy stage. The global cached-hit probability recurrence, initializer equal-root routing, concrete first-chain source integration, common original-direction lineage across all hops and final total reduction remain consuming work. The following explanations describe exactly what each added module establishes.

### PqxdhInitialCurrentSecrecy

PqxdhInitialCurrentSecrecy connects the exact currently integrated uniform-root endpoint to a selected-coordinate64-byte initializer hybrid. It consumes LegalObserver.current_game, which derives the actual pre-root context and a complete response-only continuation. The sampled root is not passed to the ordinary observer. The source continuation includes the actual Server builder, first send and arbitrary post schedule including Beacon installation; no arbitrary established-state uniformity is assumed.

1. response_prefix identifies the exact typed source64 response with the first64 bytes of the same fixed76 expansion. It adds no source nonce.
2. source_game instantiates the ordinary secret-input source game with the actual prepared-context/root sampler and complete current observer.
3. random_comparison proves full76-prefix comparison and fresh64 source response have the same complete evaluated continuation. The extra comparison bytes remain comparison costs.
4. primitive_bound has the CURRENT uniformGame(rootReduction(protocol ...)) as its left endpoint. Its right endpoint replaces only the selected-coordinate initializer response by one uniform64 response reused across every selected request. The bound is coefficient-one fixed-salt Extract plus ordinary HMAC PRF, with the exact constructed sampler and reductions displayed. Public HKDF and every nonselected initializer remain real.
5. hmac_queries proves the existing prefix-only full-output comparison uses two ordinary HMAC challenge queries. Sampler and observer work are separately charged by consuming resource lemmas; this theorem does not declare them free.

Functional SourceFullCorrect is the existing primitive wiring contract for the actual labels and shared expansion. No cryptographic implementation proof or protocol-security premise is introduced. Equal root bytes at different coordinates are not assumed impossible. The selected-coordinate hybrid is not yet asserted to equal a globally input-consistent random initializer service; that requires the separate explicit alias accounting. All five actual standard-three guarded axiom checks pass.

### PqxdhInitialFusedBeacon

The actual adjacent private Beacon root and initializer operations are now expressed by a service that returns only an optional typed64-byte initializer response. Its executable tail interface contains native raw operations, the original application getter and that response-only service. It contains no raw root reply. The native service interpreter performs the original root callback, stops on None, and otherwise performs the exact original initializer callback before returning the64 bytes.

`raw_native` preserves every raw callback. `afterInitial_native` recovers the complete concrete root-erased receive continuation from the restricted interface. `afterRoot_response` factors the actual original source initializer request from that root-free continuation while keeping the source request and root handling private. `tail_native` proves exact source-order equality of the complete original shared tail, including root rejection, actual initialization, application access, raw opening, sequence-one/binding checks and staged publication.

The interface factorization adds no security premise and moves no random sample or callback. It does not yet assert an ordinary Extract simulation across the entire root cache: target labels, other-root consistency, root/input aliases, reveal freshness and source query bills remain explicit consumers. No public HKDF evaluation is replaced.

### PqxdhInitialFusedCompiler

The actual current Beacon owner has an executable compiler whose private initializer callback names a root-family coordinate or locally known root and receives only an optional complete64-byte initializer response. The compiler takes no selected raw root and retains every original owner, shared primitive and private identity field. All preparation, raw opening and application getter work uses the previously derived root-cache-free original computations.

`preparation_source` and `data_source` preserve the actual non-root callbacks. `private_native` proves the original fused root-then-initializer effect, including optional control flow and unchanged shared/private state; it discharges the actual initializer callback through SourceAux.initial_complete. `private_source` identifies that sequence with its concrete source-derived private request. No caller-supplied compatibility or state-independence premise is used.

`step_source` combines all callback classes. `program_source` preserves every adaptive fused callback continuation and complete shared/private result. `native_program` identifies the compiler's native interpretation with the literal original whole callback interpreter. `owner_source` finally consumes the actual fused-owner source theorem, obtaining the complete original Beacon owner including inactive/failed preparation, sequence-one and binding checks, raw processing, and publication.

This module discharges the whole Beacon owner seam needed by the ordinary initializer observer. The current outer post scheduler and erased Server builder remain separate source consumers. It proves no cryptographic replacement or hidden-root independence from an arbitrary supplied context. Actual local and public work keeps the existing source resource bills, while selected/nonselected initializer cache work is accounted by the response service. All eight actual guarded axiom reports pass with standard Lean logical axioms only.

### PqxdhInitialFusedOwner

The complete current Beacon owner now runs through an interface whose private tail service accepts the actual collected root secrets and returns only an optional typed 64-byte initializer response. The service implementation performs the original private root request, rejects its absent result, and then makes the original initializer request. The executable fused tail never receives the raw root. This is an operational interface theorem; it does not claim that the service is already a legal secret-independent Extract observer.

`pre_program` preserves every original preparation callback, in order, under the fused owner interface. `tail_program` preserves every fused tail callback under its original native interpretation. `owner_native` combines these equations through the actual owner branches: inactive states, failed preparation, and successful preparation followed by exact sequence-one/binding validation and publication. The full original prior owner state is retained.

`finish_source` specializes this owner equation to the current authenticated-root post scheduler. For every attempted Beacon finish it preserves the complete live-role state, shared primitive state, private identity state and returned optional application bytes. It uses the actual post scheduler handles, including original root and initializer effects; it has no caller-supplied source-compatibility or successful-execution premise.

All four statements were checked directly with their actual guarded axiom reports. Only Lean standard logical axioms occur. No primitive security, distribution replacement, query-cost transport or final freshness claim is asserted here.

### PqxdhInitialLabelBuilder

The actual Server builder is compiled with its Ready root erased before any operation. Its one initializer callback is translated to the selected family coordinate in its original position, after identity and reservation checks. The compiler never receives the selected raw root.

`response_program` proves that this coordinate translation supplies the same complete typed64-byte response at the actual initializer site, while every ordinary callback and full root cache remain unchanged. `root_unused` proves literal independence from the Ready root field for the complete compiled builder. `build_response` consumes the previous exact response-supplied Server proof, retaining all consumed-registration fields, first-send work and full protocol/shared result.

`kernel_source` identifies the response-only kernel with the exact original source initializer when the supplied response is real at that root. `build_source` then obtains the complete original actual Server build, with the root cache unchanged. No successful-build premise is used. Gates and first-send effects retain source order. The comparison primitive may supply its challenge response before the observer starts; this module neither moves a source sample nor transfers its query costs through a distribution equality.

These five statements close the Server builder's selected-root no-use obligation. The same selected response remains available to later Beacon service requests in the outer observer. Public HKDF and actual native ratchet work remain real. All five actual guarded axiom reports pass with standard Lean logical axioms only.

### PqxdhInitialLabelCompiler

`coins_source` proves that the response-only initializer compiler preserves the complete original ordinary sampling computation and source order. `source_step` identifies each compiled private request with the original cached uniform-root service followed by its real initializer; known roots perform real local initialization and family-coordinate requests preserve the complete root cache. `source_program` lifts this exact equation through every adaptive response-only client.

These three operational statements connect the current owner compiler to the private root-label service. They do not replace public HKDF, sample independent replies for repeated root bytes, or assert that different coordinates are injective. The selected raw root appears only in the separate private cache-reconstruction law, not in this compiler. Actual source/client instantiation and query bills remain explicit consumers. All three actual guarded axiom reports pass with standard Lean logical axioms only.

### PqxdhInitialLabelPost

The current actual post-registration scheduler now uses one response-only private initializer interface for every attempted Beacon finish. `public_no_root` derives zero private-root requests for the original public channel without any local-cost premise. `finish_source` consumes the concrete fused owner compiler and preserves complete installation of the original role, shared primitive and private identity state on successful, failed and inactive attempts.

`public_source` preserves every original record, reveal and public query computation, using the syntactically derived root-free interpretation. `step_source` combines these original callbacks with attempted finishes. `program_source` proves the full adaptive schedule equation, retaining all replies, stopping decisions and complete final protocol/private state. No final state relation or successful-finish premise is supplied by the caller.

The executable scheduler has no selected raw-root argument. Its private initializer service takes only a source-derived family coordinate or locally computed root, and source interpretation uses the original root cache. The source/reduction primitive interpreters and their original query bills remain explicit. This theorem does not infer a global secrecy result or independent root input for arbitrary existing states; the actual first-miss preparation and erased Server builder supply that distribution boundary separately. All five actual guarded axiom reports pass with standard Lean logical axioms only.

### PqxdhInitialLegalObserver

PqxdhInitialLegalObserver establishes the actual current authenticated-root continuation as a legal initializer observer. It does not use the older protocol experiment or assume an arbitrary installed state has uniform chains. The complete actual preparation happens before the independent selected root draw; the executable observer receives the prepared state and typed64 initializer response only. The Ready root field is erased and the private root cache is reconstructed only in the source interpretation. Public HKDF remains real and both source roles consume the same selected response on repeated coordinate requests. Different coordinates may still have equal root bytes; no injectivity or absence of aliases is claimed here.

1. localCoins_source identifies the original Server builder coin lift with the original root interface, retaining every coin and complete continuation.
2. post_source proves equality of the entire original post schedule, including all final role and private state plus the reconstructed original root cache.
3. accepted_root_unused proves literal equality of the complete executable accepted-root observer under any replacement of the unused Ready root field.
4. accepted_source joins the actual Server builder and adaptive post schedule, preserving original order and all state.
5. accepted_decision_source projects that complete source equality at the actual first-miss cache. Only the source interpreter holds the selected root cache entry.
6. first_miss_observer matches the current protocol's completed and pending modes. A fresh32-byte root is sampled independently of the actual preparation. Completed modes ignore that draw, whose distributional removal is proved for the entire observation. The draw remains an explicit32-query cost of the comparison sampler.
7. current_game connects this exact sampler and observer to the currently integrated uniformGame(rootReduction(protocol ...)) endpoint. It consumes the checked actual first-miss decomposition, not a new secrecy assumption.

All seven actual guarded axiom checks pass with only the standard Lean logical axioms. Primitive reduction, resource instantiation and equal-root alias accounting are separate consuming work, not conclusions of these source equalities.

### PqxdhInitialReplyErasure

The extracted initializer reads the root only in forming its private input request. Once the complete typed 64-byte response is fixed, its full kernel result depends on the role orientation and those bytes. `kernel_root_unused` proves this for both actual constructors. `beacon_kernel_root_unused` derives the same equality for the normalized actual Beacon kernel, using the extracted panic-free result rather than an arbitrary choice-invariance assumption. `original_program` proves that the fixed-reply interpreter changes no unrelated callback or full continuation. `kernel_supplied` places that interpreter at the actual initializer request and reconstructs the same kernel using a fixed dummy root.

These four operational helpers use arbitrary typed64 responses and no cryptographic premise. They preserve initializer position and introduce no sample. Complete Server/Beacon continuations, repeated target-root service translation and ordinary observer legality are separate consumers; no root-containing Ready/cache value is licensed as pre-Extract context.

### PqxdhInitialResponseCache

The common private initializer service now caches the complete original 64-byte response under the exact input and info request. Role orientation is not part of the cache key. A Server reply and a later Beacon request for the same root therefore use identical bytes.

`consistent_empty` derives the initial real-source cache invariant. `consistent_record` preserves every earlier binding when the actual fixed reply is recorded. `memo_step` handles both a real hit and a real miss with the same complete reply and retained cache. `source_program` erases only the added private memo table and recovers the entire original adaptive callback program and base effects. `uniform_miss` defines the explicit comparison miss by sampling exactly one 64-byte output before its reply conversion. `uniform_hit` retains the previous complete reply and draws nothing. `uniform_bound` derives zero uniform-byte requests for a hit and 64 for a miss from those actual programs. `recorded_roles` proves reuse across the two actual opposite role orientations.

Real-source memoization changes no public HKDF and introduces no cryptographic assumption. The uniform cache is an explicit comparison interface, not an assertion that arbitrary known-input initializer outputs are secret. This cache contains private inputs and responses and must not be handed to an ordinary Extract observer. Any future same-address 76-byte KDF response must retain this same 64-byte prefix; a consuming hybrid must use the existing shared-prefix construction or charge the relevant root/input alias event. The module neither samples an extra source nonce nor replaces subsequent full responses independently. Request equality, cache lookup and update, fixed HKDF evaluation and reply conversion are local operations; only the stated uniform-query bill is claimed.

### PqxdhInitialResponseService

The five statements define a common private initializer response capability with the exact extracted SymmetricRatchetKdfRequest (complete input and info) and complete64-byte InitialRatchetKdfResponse. The source interpreter evaluates the actual fixed no-salt HKDF at that request. No uniform output or new security assumption is inferred.

`source_original` and `original_program` preserve every old callback and complete adaptive old program. `kernel_source` executes the extracted role start/request/resume boundary with the actual source response and gives precisely the original complete RustM initializer result. `same_request` proves Server and Beacon use the same input and label; role orientation belongs only to the extracted projection. `kernel_total` counts one private initializer response per attempted kernel. Public HKDF and private32-byte root processing remain separate original interfaces. The consistent initializer cache and current authenticated-root source consumers must be supplied separately; this capability alone neither creates independence nor changes source order.

### PqxdhInitialRootContext

The current authenticated-root uniform game now has a checked first-root source cut. Its exact original preparation samples the complete prepared state before any root response, while the private root cache is empty. A pending initial root request therefore draws one fresh 32-byte root at its exact original coordinate. The complete subsequent execution receives the same root and retained cache; matching later root requests reuse that cached value. Completed or absent-initial-root outcomes preserve their original continuation.

`coins_complete` preserves all original coin effects, result and unchanged cache. `first_miss` factors the actual initial root callback through its empty-cache uniform draw and complete continuation. `reduction_complete` retains the entire actual preparation and final root cache. `current_game` specializes that full program equality to the currently integrated authenticated-root protocol and its original Boolean endpoint. `current_continuation` recovers the enriched Server/Beacon initializer interface with the same entire continuation and root cache. No marginal generator interchange is used.

The supplied root, Ready records and cached roots remain private interpreter data after the draw. This module does not make a root-containing cache or Ready record legal pre-Extract observer context. An ordinary initializer reduction still needs source-derived root erasure or target labels and explicit alias/reveal handling. No independence of existing role state is assumed; only the actual new root draw is after the complete pre-root context. This is an operational decomposition, with the already established root-game contracts and query bills; it adds no primitive security claim, free sample or replacement of public HKDF.

### PqxdhInitialRootFreeCallbacks

`root_free` proves that an actual LocalPost program with zero private-root requests is exactly its original public computation lifted into the root interface. The internal fallback for a private request is unreachable by the syntactic zero count. The result retains every public callback and all its effects; it is not an equality of marginal root distributions.

`handle_roots` transports the existing intrinsic root callback bound through the unchanged current private KEM-handle translation. It requires no uniform-cost bound or state-independence premise for local callbacks. `callback_no_root` then proves zero private-root calls for every original preparation callback, raw-record callback and application getter in the fused interface. This includes arbitrary local callback state effects and optional rejection replies.

`callback_source` derives the complete root-cache-free interpretation of those actual callbacks. `cache_source` records the exact original root-cache preservation while retaining the returned source reply and complete shared/private identity state. The actual public interpretation uses the original KEM/public channel, and no selected raw root is an argument of the resulting callback interpreter.

These five statements supply the non-root callback side of the concrete legal initializer observer. They do not make its ambient work free: local sampling, public decapsulation and all actual callback budgets remain those of the existing source/reduction ledger. The selected initializer and whole adaptive owner are connected by separate source compiler laws. All five actual guarded axiom reports pass with standard Lean logical axioms only.

### PqxdhInitialRootLabelBridge

The actual Beacon fused root/initializer callback now has a concrete private request translation. The selected shared-secret marker names the original complete four-DH-coordinate family message. A locally recovered shared secret names its actual fixed-source root. Neither translation assumes that different family messages yield different roots.

`initial_request` identifies the actual Beacon request with the shared typed64-byte initializer service. `root_initial_program` proves that the original root-then-initializer sequence is exactly a family-root query followed by its real initializer, or the real local initializer on an already recovered root. All optional effects are preserved; the source-specific routed root service always supplies the successful root in these two cases. This does not assert arbitrary native KEM decapsulation success.

`root_initial_source` retains the complete uniform-root-cache result of that actual sequence. `labelled_source` consumes the checked private cache reconstruction to obtain the same source result from the selected-coordinate supplied-response interface. Only the source side takes the selected raw root; the executable labelled service takes the supplied response.

These four laws discharge the root/initializer branch of the fused current Beacon owner. The remaining non-root callbacks and whole adaptive owner/post scheduler must still be connected through their actual source compiler. Value aliases at other coordinates remain explicit bad events in later comparison games. No primitive-security, query-cost or independent-established-state claim is inferred. All four actual guarded axiom reports pass with standard Lean logical axioms only.

### PqxdhInitialRootLabelService

The response-only private initializer service receives either a complete root-family coordinate or a locally known 32-byte root. Its labelled implementation takes the selected coordinate and a typed64-byte response; it never takes the selected raw root. Selected coordinates always return that response and preserve the other root cache. Other coordinates use the original cached uniform32-byte root service and real HKDF; known roots use real HKDF directly. Equal bytes at different coordinates are permitted.

`selected_reply` proves exact repeated selected-coordinate reuse. `cache_record` proves that recording another coordinate commutes with reconstruction of the selected private cache entry. `native_step` proves exact native response and full-cache equality after private reconstruction, for selected requests, known roots, cache hits and fresh misses. `full_step` retains each unchanged ordinary callback, and `complete_source` lifts the result through arbitrary adaptive continuations with complete final cache. `empty_source` specializes the source correspondence to the actual first-miss cache shape: only the private source interpreter contains the selected root entry.

`labelled_uniform_bound` bills each service call at most32 uniform-byte queries. Selected, known and cached calls are pure; only a nonselected fresh root samples. Real HKDF, comparisons, memo operations and response conversion remain explicit local computation. The initial selected root sample and ordinary callback costs must still be billed by the actual caller.

The exact source equality supplies the real initializer response at the selected root. It does not assert that the complete current source client is yet root-independent: the actual fused-owner/request and erased-Server compiler must discharge that concrete wiring. Different-coordinate or locally known roots that equal the selected root are retained as explicit candidate-alias events when relating response-substitution hybrids. Public HKDF remains the same real service. All seven actual guards pass, with standard Lean logical axioms only.

### PqxdhInitialServiceBuilder

The six statements make the initializer callback explicit at its actual Server source position. `candidate_source` proves that the initializer service runs after identity validation and peer reservation, then executes the original plaintext allocation, binding construction, first send, erasure, serialization and publication. The first two callbacks retain their actual Boolean results; rejection does not advance to initialization. `used_source` preserves the prior current-control, next-key and consumed-registration binding checks. `ready_source` consumes the exact accepted Ready root at the initializer request while retaining all original fields.

`tail_source` and `tail_program` interpret all original callbacks using the original registration backend and complete shared primitive state, forwarding every real coin and every optional result. Only the new private initializer call is separately visible. `protocol_source` identifies the full enriched service builder with PqxdhRegistrationProtocolState.build, including consumption and selected Server reinstallation, as used by the current PqxdhAuthenticatedRootExperiment.targetAccepted. No initializer sample is commuted before the original gates. These are literal program equalities, not distribution-based cost transport. The Beacon post-finish source consumer and consistent shared initializer table are separate following steps. Primitive correctness is unchanged; no whole-builder resource or security premise is introduced.

### PqxdhInitialServiceExperiment

One enriched execution now exposes the same private 64-byte initializer callback in the current authenticated-root Server builder and adaptive Beacon completion scheduler. It retains the exact original preparation, completed and pending modes, optional roots, CCA/public calls, root requests, complete role state and shared primitive state. The real interpreter for the added initializer callback is the fixed source HKDF.

The six statements establish the interface boundary. `builder_source` preserves the actual coin channel while sharing initializer queries. `accepted_source` recovers the current `PqxdhAuthenticatedRootExperiment.targetAccepted`, including the first send before later post operations. `resume_source` recovers every branch of the current protocol resume without an honest-target or success assumption. `rootPost_source` preserves the original blocked public service and consistent matching-ciphertext root family while interpreting initializers. `rootResume_source` preserves the exact initial root request and all subsequent root requests. `reduction_source` recovers the current `PqxdhCorrelatedExpand.rootReduction` instantiated with the current authenticated-root protocol, with its complete original preparation before any root or initializer request.

These are literal computational-program equalities. They do not sample an initializer before its source gates, assert uniform established state, replace public HKDF, or infer resource costs from distributions. The prepared KEM secret remains an interpreter-private reduction field. Uniform root cache interpretation, actual first-miss context, repeated initializer consistency, secret-input comparisons and syntactic query ledgers are explicit subsequent consumers.

### PqxdhInitialServicePost

The initializer service is now threaded through the current authenticated post-root scheduler. Each exact Beacon initializer request receives its complete 64-byte response from the same service interface as Server registration. Root derivation, raw opening, the sequence-one check, the binding check and final publication remain in their original order. Every identity, shared-primitive and live-role field remains retained. Public HKDF and all other public or private callbacks are unchanged.

The six statements are operational equalities. `handles_source` shows that interpreting the added callback by the fixed real source recovers every original shared handle, including the exact complete initializer response. `handles_program` extends this equality to an arbitrary complete shared-handle continuation. `finish_source` recovers the current target Beacon finish, including failures and installation. `target_source` recovers one original source, selector or finish request. `target_program` preserves the complete original adaptive scheduler and its result. `finish_native` then composes this equality with the existing native Beacon source bridge on its explicitly good KEM sample; it does not assume perfect correctness globally or introduce a new primitive contract.

The module samples no initializer output and states no secrecy or independence claim. Its source service is the actual deterministic fixed HKDF response. Repeated-input consistency and uniform-root or uniform-initializer comparisons are separate consumers. No query budget is inferred from these operational equalities; added initializer callbacks require an explicit syntactic ledger in the consuming experiment.

### PqxdhInitialSuppliedBeacon

The actual shared Beacon continuation after initialization can be run from the supplied typed64-byte response without retaining its root. `raw_forward` preserves every native raw callback. `afterRoot_supplied` identifies the complete original application getter, optional raw receive, sequence-one and binding checks, and staged-publication result with an explicit root-free continuation. `afterRoot_complete` retains an arbitrary complete private/shared state and outside continuation under that exact source equality.

The proof derives root non-use from the actual extracted kernel normalization and original program, not from a caller-provided continuation-invariance premise. The fixed response replaces only the initializer callback in this local tail; it introduces no sample and preserves every raw return value. Target root-label routing, other-root services, cache consistency, reveal freshness and ordinary observer legality remain subsequent consumers. The complete-continuation equality alone does not license a continuation that receives the hidden root as ordinary public context.

### PqxdhInitialSuppliedBuilder

The current Server builder now consumes a supplied typed64-byte initializer response through its actual private callback. The resulting complete program is the original factored builder with its Ready root replaced by a fixed dummy value. Every other Ready field, consumed-state update, Server field, peer state, shared primitive state and original reply remains intact.

`candidate_supplied` retains actual identity validation and peer reservation before the initializer callback and the full source tail after it. `used_supplied` preserves the earlier control, allocation and binding checks. `ready_supplied` establishes the exact root-erased Ready continuation. `tail_supplied` preserves one original send/allocation/publication primitive and its complete shared effect. `tail_program` proves the complete callback-program interpretation. `protocol_supplied` recovers the current full protocol builder, including first send, serialization, publication and Server reinstallation, using the root-erased context and response-derived kernel.

No no-use premise is supplied by a caller: these equalities follow from the actual source-shaped builder definitions. The typed response is arbitrary and is supplied purely at its original call position. The module moves no random sample through the admission gates, asserts no uniform state, and does not yet simulate target-only replacement across other roots or a private root cache. Such routing and ordinary Extract observer legality remain explicit consumers.

### PqxdhInitialSuppliedPositions

`pair_refines` applies the existing generic extracted initializer refinement to one arbitrary typed 64-byte response. It establishes both exact returned kernels, the second half as Beacon-send/Server-receive origin, the first half as Server-send/Beacon-receive origin, and complete zero-state kernel refinements with empty ideal skipped lists. No new nonce is drawn and no entropy or distinctness is assumed.

`pair_positioned` derives the existing source live-history positional invariant at those returned directional origins and proves the complementary chain equalities. `server_positioned` specializes the same theorem to the actual response-supplied Server kernel. `beacon_positioned` specializes it to the exact normalized Beacon kernel used by the actual response-only tail, for every original pending root. Root erasure is the previously checked operational equality.

These four statements discharge initialization premises of the existing positional preservation results for arbitrary supplied initializer responses. They apply before the Server first send or Beacon registration receive, whose advancement remains the existing source operation. They do not by themselves install a family-wide positional relation or prove a hybrid distribution theorem. All four actual guarded axiom checks pass with standard Lean logical axioms only.

### RawCtxFamilyAdaptiveFreshness

The native freshness comparison now allows its remaining forbidden values to be computed from the final full observed result. The omitted target coordinate remains separately forbidden, and the computation of the remaining list has no target parameter. Pointwise source disclosure invariants establish the actual freshness/proxy relation for that computed list, so no freshness-equivalence premise is supplied. The same complete source execution and target-free observer differ by at most three times the existing clear-disclosure candidate event. Direct compromise contributes no extra probability; it is excluded by the original freshness event. The final stopped-source theorem retains the actual pending operation, family publication and complete history. A consuming finite-lineage construction must still supply and justify the computed list before telescoping; these four theorems alone do not claim that distinct hop events agree. All four actual guards contain only standard Lean logical axioms.

### RawCtxFamilyCompletionBudgets

The pending material-only completion now has a source-derived resource bound. pending_kdf uses the actual u8 remaining counter and the checked decreasing receive allowance: after the selected answer, no more than 254 further KDF callbacks remain. This deliberately conservative datatype reserve is separate from the original complete-source S+51R cap; it is not inferred by moving a cost bound across distribution equality. receive_effect retains the entire skip/open continuation, including one possible opening. receive_owner preserves actual successful or failed publication and proves the quiet captured owner client adds no queries. send_owner begins after the selected KDF response and counts only the original sealing operation before its quiet publication.

owner_stopped, server_stopped and family_stopped carry those exact branch-specific caps through the original owner, peer and indexed role-family installers. The zero-call outside clients are the witnesses derived by QuietOwnerTails, QuietServerTails, QuietFamilyTails and FamilyResidualBudget; they are not an assumed property of arbitrary captured source code. source_cost_mono transports each primitive class from the proved residual source budget to the original budget. stopped_class consumes the exact pending-to-source compiler and gives the entire actual material-only LIVE observer seven separate bounds: its pending reserve plus private KDF S+51R, seals S, opens R, coins U, public hashes H, real public HKDF K and reads E.

reserve_shape proves that the pending reserve is either receive (254 KDF, one open) or send (one seal). Thus a subsequent uniform ledger may charge only one additional commitment operation, not both branches. The retained state, caches, optional replies, public evaluations, original outside clients and history survive. There is no cryptographic, freshness, successful-execution, cache-miss or uniformity premise. The Fits certificate is derived from the same source-selected frame by FamilyResidualBudget.program_context. All ten statements use default elaboration settings; source_cost_mono has no axioms, and the other nine use only the standard three.

### RawCtxFamilyFreshnessEvent

The actual family completion retains its native optional reads, full source history and pending continuation. The comparison changes only the final unconditioned freshness predicate and the explicitly charged private alias routing. completion_good_bound strengthens the earlier unconditional candidate charge to candidates on clear-disclosure executions. good_alias_bound uses the existing good-event coupling and private routing bound to charge at most twice the target-free masked candidate event. completion_decision_bound exposes the original fresh-and-decision Boolean game. completion_bound then adds the one-copy private-to-masked observer charge, giving an explicit factor three. stopped_bound consumes the exact actual material-only family Context.stopped program through its source factorization. There is no compromise-probability charge and no public guess is excluded by freshness. Public views are the common supplied interface; the source consumer instantiates the literal real fixed HKDF. No joint sampler independence, global target selection, source budget or cache provenance is assumed or proved here. No cryptographic primitive security premise is added. All five dependency guards admit only propext, Classical.choice and Quot.sound.

### RawCtxFamilyHistoryBudget

source_context follows the original bounded LIVE client and derives its exact selected frame, complete saved context and actual residual source budget together. All inner owner, Server and family outside clients are quiet by their literal singleton source origin. The captured history and remaining reveal allowance satisfy knownInputs(prior,savedHistory).length + residualE ≤ knownInputs(prior,initialHistory).length + originalE. Each actual optional read adds at most one disclosed value and consumes one reveal coordinate; every record/public operation keeps the original history values while ticking its time. The proof covers every typed read reply and source branch, rather than assuming a final history provenance condition.

source_candidates consumes this same certificate with the concrete material-only stopped observer. Before any later handler, direct-read predicate, material, earlier candidate list or private-state choice, it constructs a context whose supported full candidate list is bounded by initialKnown.length + earlierCandidates.length + 254 + S + 51R + K + E. Prefix disclosures and residual reads share one E term. Every prior known value and earlier chronological private-input candidate remains explicit, including duplicates; no private function-table enumeration is used. The selected frame and Fits certificate also instantiate the existing U+64(S+R+H+1) observer uniform bound.

These two statements discharge numerical source/history resource provenance. They do not assume primitive security, freshness, cache misses, uniformity or independence, and they do not replace the actual earlier private-input log bound. Both use only the standard three axioms and default elaboration settings.

### RawCtxFamilyLineageCompletion

The checker is appended after the complete original in-progress family operation and its full original outside LIVE client have finished. It calls the same private receive-derivation primitive and uses the same candidate ledger, shared primitive state and sticky disclosure flag. It returns a private lineage list to the reduction alongside the complete original result, family and history. It sends no reply to the adversary and resumes no network client.

`checker_primitive` proves the checker is literally a forwarded non-read primitive program. `checked_invariant` extends the original source-derived disclosure witness and candidate inclusion through this exact appended program: its private calls retain all earlier candidates and leave the original history and disclosure flag unchanged. `checked_contains` proves the hidden starting input remains in the returned lineage under every backend, including the masked comparison.

`checked_fresh` identifies the complete interpreted returned list plus all earlier ancestors with the hidden input plus its retained known values. `checked_fresh_proxy` combines that identity with the actual source invariant. Outside the same final candidate event, the original unconditioned byte-value freshness is exactly the executable clear-disclosure proxy. It assumes no value injectivity and makes no compromise event artificially unlikely.

`derivation_response` proves every checker request uses the same actual private byte-alias routing and full supplied response as receive. `checker_evaluate` evaluates the entire private lineage using that actual function. `recording_erasure` erases only candidate/disclosure instrumentation from the full primitive execution, preserving every original callback result and shared effect. `checker_native` combines these facts with the actual native-step theorem: each supported returned checker list is exactly the complete native private lineage, including the final material key. The local parent/child separation branch remains explicit and must be charged in the source hop.

These nine statements close the executable final-checker/source-freshness interface, but they do not yet establish the same full initial-direction lineage across all ordered source hops. The global consumer must retain the earlier ancestors, append the checker before private-state projection and prove that source-position relation. Its extra n+1 private derivations, candidate entries and local fixed-HKDF evaluations need their explicit appended budgets. The factor-three probabilistic comparison and cryptographic reductions are consuming theorems, not assumed here. All actual guards use only the existing three standard logical axioms; no primitive implementation or persistence behavior is proved.

### RawCtxFamilyParentSecrecy

The typed continuation consists of the exact family completion, its outside source program, original disclosure history, earlier candidates, private shared state and retained cache. The parent response supplies its actual joint material and hidden next-chain coordinate; no post-draw hidden input is supplied as public context. local_bound constructs the target-free remaining-freshness observer from that same completion and charges three copies of its candidate event. actual_route and random_route average those local bounds over the original complete parent/context sampler. actual_bound pays the separate real-input full76-output tester, yielding its Extract and HMAC advantages plus2^-352. random_bound uses only the independently justified delayed-coordinate qCandidates/2^256 term. bound proves actual fresh-and-decision distinguishing advantage ≤ mainExtract + mainHMAC +3*(testerExtract+testerHMAC+2^-352+qCandidates/2^256). Intentional target disclosure contributes no probability term; public HKDF remains the literal production function in all games. The main and tester reductions each make two HMAC queries and at most(qSample+76)+qObserve uniform requests. The tester separately makes at mostqCandidates real full HKDF evaluations. The factor three weights the advantage, not the query count of an individual constructed reduction. challenger_queries separately charges each Extract/HMAC/independent-child world, including all64/76/128 byte draws. These component query premises remain explicit until the source-budget consumer instantiates them; deterministic local work is not free. The actual source predecessor/cache sampler and reached continuation, initial half-child composition, finite adjacent global hybrids and logical target-record provenance remain consumers. All eight actual dependency guards permit only propext, Classical.choice and Quot.sound.

### RawCtxFamilyResidualBudget

The exact original bounded LIVE source derives its saved context and resource certificate together. remaining_below proves that consuming any request decreases only its original source coordinate. fits_mono transports the resulting residual certificate to a larger original budget. program_context follows every possible source reply, derives the actual dependent frame at the selected query, and attaches both quiet inner family continuations and a six-coordinate residual Bounded certificate for every captured outside LIVE reply. The frame includes complete reached role state, history, pending payload and original clients.

bill_mono transports any nonnegative operational query weights from that residual to the original source bill. reached_context obtains the same certificate from the actual supported selected prefix without changing its reached primitive state. The program_context theorem also applies directly to a state-dependent cut once its existing scanner supplies occurrence and selected-query facts.

No budget for an arbitrary Context, generator uniformity, cache miss, target honesty, cryptographic assumption or freshness premise is inserted. The inner pending material-only completion remains a separate explicit reduction overhead, and prefix history/prior-cache candidate lengths remain charged by their own source ledgers. All five theorems use default elaboration settings and the standard three proof axioms only.

### RawCtxFamilyStoppedResources

uniform instantiates the actual read-mask observer on the concrete material-only pending family program. Its full random-query cap is U+64(S+R+H+1), derived from the original six-coordinate source budget plus the actual pending completion; receive/open and send/seal are exclusive, so the completion adds only one possible 64-byte commitment draw. All opening, sealing, shared cache, optional plaintext, original outside-client and public-query behavior remains present.

candidates derives the supported full candidate-list length from the same seven-class syntax certificate. It counts the complete initial prefix plus at most 254+S+51R+K+E new entries, including duplicates, public guesses, failed records and read attempts. history_candidates instantiates the actual freshness initialization knownInputs(prior,savedHistory)++earlierCandidates, preserving and charging both terms explicitly. It does not assume this saved history is empty or supplied for free.

source_context constructs the context and all these operational prerequisites from the same selected occurrence in the original bounded LIVE source, before every later material/output/read-view/private-state choice. It derives Fits through FamilyResidualBudget rather than assuming an arbitrary whole observer budget. These are resource and source-provenance statements; they add no security, freshness, cache-miss or uniform-sampler premise. Numerical prefix-history and chronological private-log bounds are separate source consumers. All four guards use only the standard three proof axioms and default elaboration settings.

### RawCtxFiniteLineageCheck

The finite checker follows the actual private derivation function from one selected input through n further chain transitions, then includes the selected record material key. It preserves the whole list, including repeated values and possible aliases. It runs only after the original adversary has stopped and produces no new network or reveal reply. The consuming source theorem must append it before private-state projection; this module alone does not establish that placement or a final source security experiment.

`key_map` retains every selected material-key byte. `queries` proves an all-reply cap of n+1 derivation requests. `evaluate` evaluates the whole checker under a deterministic backend, with its lawful ambient effects retained. `trace_map` maps each actual step and key into an exact complete native lineage. `native_trace` instantiates that equation with the existing private-patched native function. Its parent-input separation premise remains explicit and must be charged by the source hop; it is not assumed negligible here.

`trace_contains` keeps the starting input even if later steps revisit it. `trace_length` gives n+2 retained values, including the final material key. `interpreted_mem` identifies the exact interpreted list membership as hidden-coordinate membership or a retained known value. `interpreted_fresh` therefore proves value-based freshness equivalence whenever the hidden starting coordinate is present. `native_fresh` consumes the actual native-step equation, retaining aliases and repeated projections without an injectivity assumption. `returned_contains` proves the starting input remains in the returned checker list under every adaptive private backend, not only under deterministic evaluation.

The actual primitive forwarding, candidate ledger, unchanged source history and disclosure flag, local HKDF cost, and final common lineage across ordered source hops are separate consuming obligations. Every known checker input must be recorded in the same candidate ledger; the n+1 extra private derivations must be billed explicitly. No public HKDF call is replaced or exposed by this module, no cryptographic premise is added, and no primitive implementation is proved. All eleven actual dependency guards admit only the standard three imported axioms.

### RawCtxFirstParentPrefix

The original selective cursor increments on every matching callback, including cache hits. Consequently a depth-selected predecessor need not be a fresh draw, and its stored response may already occur in the pre-cut cache. This module closes that operational distinction by scanning the actual source until the first matched cache hit or the requested predecessor depth. A collision is an explicit saved branch with its original response and full continuation. It is not silently resampled, removed or assumed unlikely.

`selected_private` proves that the concrete selector stops only at an actual private KDF callback. It is the coverage premise consumed by the forward source annotation scanner; no inverse of an arbitrary saved continuation is needed.

`unchosen` proves that every matching callback which this scan executes is an actual cache miss and does not skip the requested predecessor depth. Thus scanning cannot pass an earlier matched cache hit unnoticed. `selected_cases` proves the complementary stopped classification from the same actual cache: either a cached response exists, or the callback is an actual miss at precisely the requested depth. Neither fact is a supplied source invariant.

`scan_same` proves literal equality of the two complete prefixes for stages d+1 and d+2, starting with cursor depth at most d. It consumes the original callback equations and depth preservation, including every opening, sealing, public operation and optional read. The first-hit selector may stop earlier than the old depth-only selector, but it never changes an executed callback.

`scan_complete` proves that finishing every saved branch with its original handler recovers the exact original source family. Full native results, every role and peer, live history, shared primitive state, private table/cursor and chronological input log remain present. The collision branch continues normally in this source equation.

`reached_context` derives the complete original material-only Context from actual supported source syntax, together with its exact pending address, match, reached depth and cache coverage. A stopped cache hit gives an actual earlier recorded input and the retained full response. The other branch derives cache=None and depth=d. The supplied initial cache-coverage condition is the existing source invariant derived from the actual empty cache or a proved preceding source segment, not an enumeration of an arbitrary lookup function.

`pending_dispatch` consumes the same selected frame. Its hit branch runs the original continuation with its cached full response. Only the derived fresh branch samples one complete 76-byte parent output, then runs that same saved continuation with the actual updated state. The active stage condition is explicit and holds for both adjacent stages d+1 and d+2.

`adjacent_complete` packages both original source games over their one common prefix. It does not claim that the collision continuations under the two stages are equal or that a cached parent's next-chain input is independent. The global ordered recurrence must account for that already-bad branch at the earlier child or initial-half input hop. The final event remains one event on the complete source result; no per-hop freshness replacement or probability bound is asserted here.

All eight statements are checked with their actual dependency guards. This module supplies exact source scheduling and branch provenance. Its source scan uses the same concrete forward annotation and structural resource bounds; it introduces no probability-to-cost transport, primitive security assumption, custom axiom or new public capability.

### RawCtxForwardAnnotation

The annotated oracle interface carries an optional concrete source descriptor alongside each original query. Its dependent reply is exactly the original reply. erase_query preserves the complete actual query and all following replies; erase_mapTags shows that changing descriptor data does not change any source operation or complete erased program. sound_pure and sound_query expose a structural invariant: every present descriptor names the exact actual query and its whole erased continuation, and every following reply remains sound.

The invariant verifies descriptor data constructed by a source compiler. It does not reconstruct a descriptor from an Occurs witness, decide equality of arbitrary functions or invoke Classical.choose. A consuming state-dependent sampler can return a carried descriptor directly and use the proved full-continuation equality for its pack law. No security, freshness or source capability is assumed. The four statements use default elaboration settings; sound_pure and sound_query have no axioms, and the erasure laws use only propext and Quot.sound. Concrete source compiler soundness is established by the following owner and role-family modules.

### RawCtxForwardAnnotationComposition

`RawCtxForwardAnnotationComposition.sound_map_bind` transports an explicitly carried source descriptor through mapping and the full original outside continuation. Its premise is the literal frame-splice equation, which the concrete owner, Server and family frame constructors must discharge; it assumes no security or arbitrary occurrence inversion. `covered_map_bind` proves that mapping descriptors and appending covered continuations preserve annotation presence exactly at every selected callback. Neither theorem derives a descriptor by searching higher-order functions. Actual guards permit only propext/Quot.sound for the first theorem and propext for the second; no classical-choice dependency occurs. Query, reply and source-state erasure remain unchanged.

### RawCtxForwardAnnotationLift

`RawCtxForwardAnnotationLift.erase_lift` proves that adding the LIVE read interface and mapping a carried descriptor forwards every original family query and the complete erased continuation unchanged. `sound_lift_bind` preserves the literal source frame through that sum-interface lift and its entire original outside client; the concrete frame-splice equation remains an operational obligation for the source wrapper. `covered_lift_bind` preserves exact selected-query coverage under the same explicit query injection and outside program. No descriptor is obtained by inverting a function, and no security or key-distribution premise occurs. All three actual dependency guards pass with only propext and Quot.sound (coverage uses propext alone). These helper statements do not yet claim completed native source sampling.

### RawCtxForwardCosts

`erase_class` proves exact preservation of every primitive query predicate when forward descriptors are erased. It follows the entire original callback syntax under every possible adaptive reply, not merely its evaluated distribution.

`descriptor_class` uses actual static coverage to identify descriptor-carrying callbacks with the original private derivation callbacks. Consequently the concrete source private-call cap also bounds descriptor construction, including repeated calls and cache hits. The concrete family sampler must instantiate this equality with its source-derived S + 51R ledger; that consuming statement is separate. This is a callback count; copying or retaining each finite source context or continuation remains explicit local work proportional to the chosen representation and is not asserted to take constant time.

Both guarded statements use only propext and Quot.sound, with default options. They add no cryptographic or source compatibility premise and no primitive implementation proof. The actual concrete compiler supplies Covered, which is a syntactic annotation property rather than a security assumption.

### RawCtxForwardCoverage

Covered checks the actual annotated syntax under every possible reply. The optional descriptor is present exactly when the original query is selected. covered_pure discharges completed code; covered_query exposes the exact current presence equation and the full continuation obligation. This excludes an all-none annotation from satisfying the selected-query sampler requirements, and also rejects tags on unselected operations. Concrete owner and role-family source compilers derive coverage directly, without choosing a context from an occurrence witness. Both checked statements have no axioms and use default elaboration settings.

### RawCtxForwardFamily

The complete finite family compiler attaches its original selected Server or established Beacon, selected role index and whole original outside source program before each private derivation. Its erasure theorem is exact for arbitrary adaptive family clients and complete states: original routing, inactive Beacon phases, owner operations, original optional replies, all public requests and role installation are preserved. Sound reconstructs the complete erased pending frame from the descriptor that execution carried forward. Coverage proves every private derivation carries one and every other callback carries none under all replies. Helper continuation equations are discharged by the actual recursive source theorem, not a user-supplied whole-source assumption. The ten results concern protocol wiring only, not key independence or secrecy. All ten actual guards contain only standard Lean logical axioms.

### RawCtxForwardLive

The actual LIVE source compiler carries each original family descriptor together with the saved original disclosure history and full outside LIVE client. It constructs these fields directly while interpreting the original source program. Every read queries the actual requested owner and optional current kernel, records the original optional reply and resumes its original outside program. The descriptor remains private execution metadata and is never returned through the protocol API.

`program_query` exposes the complete family-or-read source dispatch. `family_erase` proves that forwarding the actual family operation preserves its entire original execution and history tick before the already compiled outside client runs. `family_sound` proves that the carried descriptor names precisely that whole pending family continuation, its saved original history and outside LIVE client. `family_covered` preserves a descriptor at every selected private callback through the complete family operation and its continuation. These local helpers consume only operational certificates about their concrete inner program and continuation.

`program_erase`, `program_sound` and `program_covered` discharge those certificates for the actual entire adaptive LIVE source using the checked Family and Owner source proofs and original recursive outside client. Their statements assume no continuation correspondence, target freshness, uniform input or honest operation. They preserve all indexed owners, attempted operations, inactive role outcomes, public callbacks, actual optional disclosures and timestamped history. Public and read queries carry no descriptor; every private derivation carries its exact original Context before the primitive reply exists.

The final concrete carried scanner uses these source certificates to retrieve an existing descriptor without existential search or inversion of function equality. This module establishes the source annotation boundary, not a cryptographic secrecy bound. No custom axiom, primitive implementation proof or new security premise is introduced. All seven actual guards pass with the standard three imported axioms and default elaboration options. Literal erasure preserves callback effects; descriptor copying/retention is separate finite local work whose construction count is accounted by the source private-call ledger.

### RawCtxForwardOwner

The forward owner compiler constructs an actual `OwnerContext.receive` or `OwnerContext.send` value immediately before each private derivation query. Its saved fields are the original owner, original source outside client and complete pending request. It does not recover a descriptor by choosing an existential witness or inverting equality of continuations. Actual opening, sealing and public queries carry no descriptor. Every source frontend gate, failed receive publication, successful publication and updated send state remain unchanged.

`receive_erase` preserves the original ranked receive program followed by the entire compiled source continuation. `send_erase` preserves the original derivation, sealing request using the advanced state, and publication continuation. These are syntax equalities under descriptor erasure, so no query is inserted, removed or assigned a cost by a marginal distribution argument.

`receive_sound` and `send_sound` establish the exact query and full continued program named by each carried descriptor. Their local premises concern the erasure and soundness of the supplied concrete continuation; the whole-source theorem discharges them using its original recursive outside client. Neither premise is a cryptographic assumption. The receive proof covers every resumed reply and uses the actual decreasing receive rank.

`program_query` exposes one actual source step, including all empty-input, decoding and frame-validation gates. `program_erase` proves that the entire annotated adaptive source client erases to the original pending owner program. It preserves complete owner state and the original returned reply in every source branch.

`receive_covered` and `send_covered` prove that every actual private request has a descriptor and every other request has none, across every adaptive reply. `program_sound` and `program_covered` discharge all local continuation premises for the actual whole source compiler. Together with erasure these prevent a vacuous all-unannotated construction and let the source scanner consume a carried descriptor directly.

These ten statements close the owner portion of the executable source annotation boundary; the Server, family and LIVE wrappers and final sampler consume them separately. They do not claim input secrecy, freshness, a cryptographic reduction or full evolving-chain completion. No new security premise, custom axiom, source runtime operation or primitive implementation proof is introduced. Lean reports only the standard imported `propext`, `Classical.choice` and `Quot.sound`; the compiler contains no choice-based descriptor extraction. The only local elaboration option is `backward.isDefEq.respectTransparency false` on `program_erase`, with the default heartbeat bound retained.

### RawCtxForwardParentSampler

This is the actual executable carried-context sampler for the complete native finite family and original LIVE source client. It compiles the original client using the checked forward owner, Server, family and LIVE compilers, preserves the native/refined initial representation, and scans the same logged primitive interpreter. The source constructs the Context before each private call. The sampler retrieves this literal carried value and never invokes the earlier mathematical classifier, chooses an existential witness, or inversely analyzes a continuation function.

`compiled_erase` connects the annotated native family client to the exact enriched original source program. `pack_promote` maps only completion or an existing carried Context into the old continuation interface. `parent_private` derives private-query selection for the original predecessor selector, and `supported_valid` is its operational support specialization: reached cache provenance, source address and depth follow from the same original prefix.

`carried_pack` proves the exact complete original state-dependent source prefix for any selector whose actual selection is within private derivations. This is a syntactic selector certificate, discharged by the concrete first-hit selector. `carried_no_other` proves the sampler cannot return the mathematical classifier's unsupported fallback. `carried_origin` derives actual selection and reached chronological cache provenance from a supported carried Context. `carried_finish` proves that resuming the full saved continuation gives the same complete original logged source execution. Every original family field, optional disclosure/history, callback reply, prior table, cursor, log and shared primitive effect remains present.

`source_uniform` derives the complete logged source uniform-query cap U + 76(S + 51R) + 64(S + R + H) from the original all-reply source budget through literal log/source projection. `carried_uniform` gives that same conservative actual sampler cap using the exact prefix-and-finish program and prefix-of-bind rule. No opaque sampler budget or equality-of-distributions cost transfer is assumed. `source_descriptors` separately bounds descriptor-carrying source callbacks by S + 51R, including cache hits and repeats. Copying or retaining finite saved contexts and source continuations remains explicit local work; it is not asserted to have constant bit complexity.

`first_pack` specializes the sampler to the actual earliest matched cache-hit or desired predecessor stopping rule. `first_origin` derives the actual recorded-input cache-hit branch or the fresh parent at precisely the requested depth. It never resamples a cached response as fresh. `first_adjacent` proves that both complete adjacent source family games use this same executable sampler and their original full continuations, preserving collisions and early completion. Its cursor-depth precondition is the ordinary operational starting invariant; actual zero initialization supplies it. Charging the collision branch and proving the final cryptographic/freshness recurrence remain separate consumers.

All fourteen actual guarded statements pass with only the standard imported three axioms and default options. The code uses no choice-based descriptor extraction, custom axiom, primitive implementation proof, source-honesty restriction or cryptographic premise. Arbitrary retained initial state in the operational theorems does not assert it is uniform or secret; actual initialization and cryptographic distribution arguments are established separately.

### RawCtxForwardScan

The forward scanner returns either the actual completed result and full state or the descriptor already carried by a selected query and the full state before that query. Its result datatype has no missing-tag or arbitrary-frame fallback. A static coverage certificate and the checked inclusion of state-dependent selection in the private-query class justify retrieving the literal `some` value with `Option.get`. The operation performs no existential search and never inverts a continuation equality. These proof arguments do not select a descriptor; it is present in the actual source query before the primitive runs.

`scan_pure`, `scan_cut` and `scan_other` give the exact three execution cases. A cut occurs before the selected primitive reply or state effect. Every unselected callback preserves its original reply and entire updated state before the scan continues. Thus optional failure, cache hits, repeated requests and all public work remain in the prefix.

`scan_pack` proves that packing each returned carried descriptor through its checked frame equals the original stateful prefix of the erased annotated source program. `scan_finish` proves that running its exact full continuation yields the complete same source execution. `pending_origin` derives the actual selection condition and original syntactic occurrence from a supported returned descriptor. It does not claim a fresh or uniform input.

`scan_uniform` bounds this actual sampler by the complete same-source uniform-query bound, using literal scan-and-finish equality and the prefix-of-bind rule. The concrete source wrapper must supply the existing source-derived budget; this generic theorem does not assign an opaque sampler a free cost and does not transport a cost across equality of evaluated distributions. Packing the saved tag and proof-erased retrieval add deterministic finite bookkeeping rather than primitive queries.

The primary scanner equations and resource theorem use no `Classical.choice` (only `propext` and `Quot.sound`, or no axioms). The support/occurrence corollary imports the standard three axioms. No custom axiom, security premise, unsupported fallback, descriptor choice or primitive implementation proof is introduced. The owner/family/LIVE source annotation and the concrete logged-parent sampler instantiate the static coverage, frame soundness and source budget separately. This module alone does not claim evolving-chain secrecy.

### RawCtxForwardServer

The actual Server compiler constructs its selected peer and complete original outside context before each private owner derivation. Erasing these private descriptors yields exactly the original routing, peer lookup, optional failure, raw-attempt instrumentation and same-peer publication, for every adaptive continuation. The Sound theorem proves each carried descriptor denotes that complete erased pending frame; Coverage proves every private derivation carries one, including all later callbacks after any failure or cache response. The main three theorems derive their helper continuation conditions from the actual recursive source compiler; no caller supplies a whole-source simulation or a descriptor recovered from a function. No security conclusion, uniformity, cache-miss or freshness premise is introduced. All seven actual guards contain only standard Lean logical axioms.

### RawCtxInitialChildCandidates

real_bound instantiates the existing full76 preimage tester on the exact selected-half64 initializer sampler, retaining the opposite half and complete prior context. It pays its own Extract/HMAC pair plus2^-352, never a uniform bound for a real correlated child. uniform_delayed proves a complete evaluated-distribution equality for either direction, moving the selected32-byte half after the entire independent-child and adaptive candidate computation. uniform_bound then charges q/2^256 on the actual supported candidate list, including duplicates, without a direction/stopping loss or conditioning. tester_queries counts two HMAC challenges, qPrior+64+qObserve uniform queries and up toqCandidates real fullHKDF evaluations. uniform_queries separately charges the literal original candidate experiment qPrior+64+76+qObserve, without transporting cost from a distribution equality. There is no12-byte initial nonce draw. These are first-child component laws; actual source initialization, retained root/initializer aliases, native family state/freshness and original budgets require consumers. All five actual guards allow only the standard propext, Classical.choice and Quot.sound dependencies.

### RawCtxInitialSentinel

The first-child observer can use the existing selected-chain table interpreter with an analysis-only root-domain marker. Every actual private ratchet request has the fixed ratchet label, so the marker cannot be reached regardless of chain bytes. Its entry retains only the opposite initial half and a reduction-only twelve-byte coordinate; the target initial half is absent. Both private lookup and label-step specialization are exact and keep the same original retained table and supplied full child. No source predecessor, initializer nonce or public override is introduced. The actual64 distribution and complete native family specialization are separate consumers. The four actual guarded theorems depend only on standard Lean logical axioms.

### RawCtxInitialSentinelBackend

`native_marker` proves an exact equality of the complete original native LIVE pending interpreter with the original retained source backend when the retained-parent entry is the unreachable root-domain analysis marker. Every real private ratchet request has the ratchet domain, so its response ignores the marker regardless of its chain bytes. This remains true for all adaptive receive and send callbacks.

The proof separates actual derivation replies from every other callback. The private derivations use the existing typed `lookup_private` domain-exclusion law. The non-KDF branches use the complete original pending callback congruence, preserving optional opening, failed or successful sealing, commitment hashes, publication and every shared-state effect. Public calls remain the real original public service for any retained lookup, and the full optional LIVE reader is unchanged. It therefore avoids assuming whole-call compatibility or dropping opaque primitive work.

The marker is private analysis bookkeeping and never an actual source cache binding, initial nonce or extra initialization output. The opposite initial half and reduction-only twelve bytes cannot affect any actual private ratchet call through this marker. The initial64 distribution and the separate charge for those twelve reduction bytes remain the neighboring sampler theorem's obligations. This statement is operational and introduces no input secrecy, freshness, uniformity or cryptographic assumption.

The main theorem's actual guard passes with only the standard three imported axioms. The proof uses default elaboration limits, adds no custom axiom and does not prove any primitive implementation. All callback and uniform-query effects are identical because the entire QueryImpl is equal, rather than merely its evaluated distribution.

### RawCtxInitialSentinelSampler

Either selected half of the actual uniform64 initializer is exactly the same pair distribution as the retained-opposite/hidden-selected coordinates of a comparison76 draw, after ignoring its additional twelve bytes. The proof applies this law to the complete evaluated continuation, first proving both source constructor orientations and exact64 byte reconstruction. native_observed retains the original pre-draw context, its chosen direction, actual typed64 response and complete original constructor result. It does not assume a reached initializer is uniform: the current initializer reduction must supply that comparison stage. The source program pays qPrior+64+qNext; the comparison sampler separately pays qPrior+76+qNext. The extra12 belongs only to reduction bookkeeping and creates no source nonce or primitive call. Both programs preserve all further local computation and optional effects inside the original continuation. All six actual guarded results depend only on standard Lean logical axioms.

### RawCtxLoggedParentPrefix

The six statements retain the original complete native source family and its chronological private-input log. scan_same derives one common prefix before the matched predecessor at depth d under both child stages d+1 and d+2; the selector includes cache hits and uses the actual callback depth invariant. scan_complete resumes every completed or pending saved result to recover the original logged family game. scan_projection erases only the private list while preserving the exact dependent query, continuation and full reached state. reached_context derives the complete original family/live context, address, match and depth from that same supported prefix. adjacent_complete resumes the common prefix under both original stage handlers, retaining genuine early completion and cached predecessor responses. reached_empty additionally starts with the actual empty private cache and derives that every reached cache binding occurs in this same chronological input list; it assumes no enumeration of a functional table. Shared primitive state, original family/history, private table and cursor remain present. The pending request has not yet executed and is not yet in the prior list. These are source-prefix and provenance laws, not a cache-miss, source-initialization, logarithm-length, secrecy or parent/child alias bound. The actual initial root inputs and earlier history must be connected separately. All six actual guards permit only propext, Classical.choice and Quot.sound.

### RawCtxLoggedParentResponse

The six statements identify the actual original predecessor callback and its entire source continuation. frame_step derives the complete private hit-or-miss response equation by inspecting the real owner, Server or Beacon, family and live context constructors. logged_frame_step preserves that same response/shared state/table/cursor and appends the executed original address to the chronological list. frame_hit returns the retained full cache response and original update without a parent draw. frame_miss performs one actual uniform76 draw only when the original cache is empty at the matched address and its reached depth is before the current stage. execute_hit and execute_miss consume these equations for the exact saved family continuation; the hit branch remains a real continuation and can still encounter a fresh child later. These are operational branch equations. The actual source prefix supplies the matched/depth/missing or cached cases; no supplied arbitrary continuation compatibility is used. Later child substitution, prior-input alias charging, source initialization and native secrecy remain separate consumers. All six actual guards allow only propext, Classical.choice and Quot.sound.

### RawCtxLoggedParentSampler

These seven statements are a mathematical source-sampler factorization and a separate forward-compiler consumer. pack_classify proves that choosing an existing source-context witness preserves the entire original dependent frame and reached state. sample_run preserves the exact common logged predecessor prefix and its complete finish. sample_supported derives full cache-input coverage, actual match and depth from the same supported source execution; no unsupported fallback has positive support when the initial cache is covered. after_run and sample_after split the actual predecessor response into the retained cached FullOutput or the original full76 draw before the same complete native continuation. adjacent_empty starts with the actual empty private table and depth-zero cursor and obtains both full adjacent family games from one such mathematical sampler, with no supplied cache-miss, separation, continuation or state-preservation premise. The input value and initial family still require the actual initializer consumer. carried_run separately accepts a forward annotated sampler and its concrete full frame-erasure equation; it does not call classify. The Classical.choose classifier is private analysis only: equality of arbitrary saved continuation functions is not computationally inverted by an executable reduction, and no finite runtime claim is made for it. The final standard-game reduction must use a forward source compiler carrying the descriptor before erasure, with its own exact erasure/resource laws. Public services and actual final Result/family/history/shared state remain intact; no per-hop Fresh event is fixed. Child substitution, native retained-cache interpretation, prior-address alias charging, initial source law and final target lineage remain separate consuming work. All seven actual guards allow only propext, Classical.choice and Quot.sound.

### RawCtxPendingBackendInterpretation

The three statements are exact lawful compiler equations. pending_compose derives interpretation through the original pending receive/open, send/seal and public programs from their actual adapter composition; no callback equality premise is supplied. family_compose adds the actual complete optional native reader and preserves the same complete backend monad. program_compose lifts this equation through every adaptive pending program and all result types. A StateT backend retains its complete shared/cache/cursor state, so the later selective-to-retained-view bridge can reuse the original lower backend laws. These are operational equalities, not resource transport, cache consistency, source freshness or secrecy statements. All three actual guards permit only propext, Classical.choice and Quot.sound.

### RawCtxPendingChildDraw

The actual pending source family has a single remaining selected private child draw after its matched parent callback. These six equations preserve the complete original result, role family, live-read history and shared primitive state; they remove only the completed private cache, cursor and chronological input log. Public HKDF remains the real fixed source service. The parent response may itself have come from a cache hit.

`pending_uniform` instantiates the generic single-draw distribution equation with the actual pending source compiler. It preserves every original native backend callback. The child cache miss is explicit at this local statement. Moving the complete 76-byte draw before the remaining client gives the same final distribution, including paths that never request the child; it does not assert syntactic equality or transport query costs.

`logged_uniform` uses the exact original log projection to obtain the same equation with the chronological input log present. It preserves all original native result and shared state fields, discarding only completed private instrumentation.

`parent_random` applies that concrete equation after the actual matched parent response. The actual cursor advance proves that stage d+2 has exactly one selected draw remaining. The original full saved source continuation receives the same typed parent reply, and all previous cache bindings remain in the retained lookup.

`updated_covered` proves that recording the actual parent input preserves the cache-domain/input-list relation for every parent output. `child_missing` then derives absence from the reached private cache whenever the child address is absent from the actual prior input list followed by that parent address. This list records actual callbacks, including repeated hits; it is not an enumeration supplied for an arbitrary function.

`parent_random_of_unlisted` consumes these two source-provenance facts. The random-child equation therefore needs only the explicit complement of the prior/parent address event, instead of an unexplained cache-miss premise. The consuming hop must charge that event; none of these statements assumes its probability is zero or discards its executions. The complete final output permits one common final event, including later target lineage, across adjacent source stages.

The early comparison draw has the separate 76-byte sampling bill proved by RawCtxSelectiveSingleDraw.early_uniform. No cost is inferred from equality of evaluated distributions. These statements do not establish initialization, an executable source cut sampler, cryptographic secrecy, or the final finite hybrid bound. All six actual guarded checks use only the standard imported axioms.

### RawCtxPendingChildRealization

The two actual source stages after a matched parent callback now use one complete material-only stopped family program. The real stage retains the actual fixed child response; the random stage draws one full child response and patches only its private address. Both preserve the original result, every family and peer field, actual live history and shared primitive effects. The completed private cache/cursor/log alone is projected. Public HKDF and optional read values remain real.

`child_address` proves that the actual matched parent cursor advance points to precisely the returned next32 chain input, including the original fixed ratchet label and byte representation. `child_table` proves that recording separate parent and child inputs gives exactly the original prior lookup with the child address privately patched and the full parent entry retained at priority. The separation is a local branch condition, not an assumption excluding a source execution.

`real` combines the actual saturated source execution, concrete retained native backend and complete native/label family Context relation. It gives literal equality for the full original native continuation without a cache-miss or address-separation premise. All cached parent responses remain possible in this equation; their nextChain is not claimed to be a fresh uniform input.

`random` consumes the actual chronological cache-coverage invariant and the complement of the prior/parent input event. These derive the required child cache miss and parent/child separation. The checked single-draw source equation then gives equality of complete final distributions to one early child draw followed by the same stopped program under the private patch. Paths that never request that child are included; the comparison draw has its own 76-byte bill and no cost is transferred from equality of distributions.

`real_patch` proves that patching the original fixed-source child response does not change the retained lookup when the child input is absent from the actual earlier input list. `real_patched` uses that fact to express the real source stage in precisely the same privately patched stopped-program interface as the random stage, now supplying its original fixed-source full response.

These full-state equations allow one final event on the complete original native output. They do not equate separate per-hop freshness conditions or construct the final lineage checker. Any private lineage checker must be appended under the same interpreter before final private-state projection, using the separately checked continuation/lineage equations. Likewise the actual first-hit source scanner must provide the fresh parent sampler; these equations never resample an already cached parent. The remaining collision branches and source-derived resource bounds are retained for the consuming adjacent-hop proof. All six actual guards use only standard imported logical axioms, with no custom axiom or primitive-security premise.

### RawCtxPendingNonKdfStore

The actual enriched pending family callback preserves its entire private KDF table and selected cursor whenever its source query has no KDF address. Opening and sealing still execute their original optional AEAD, shared commitment and writer calls; public services execute the same original real public backend; live reads return the actual optional kernel value. Shared primitive state can change. The theorem preserves the complete Store, not just its depth or marginal distribution.

Four exact syntax lemmas prove that the source inner opening/sealing and their material adapters contain zero private KDF requests. Native non-KDF callback equality retains the original Store, and structural induction extends this to every all-reply zero-KDF native program. The actual interpreted receive/send adapters consume those syntax bounds. The public callback equation and support corollary retain the same Store. Finally callback_store covers all original enriched opening, sealing, public and read branches; its only branch premise is the exact queryAddress=None condition. No freshness, miss, cache-consistency, successful execution or cryptographic assumption is introduced.

These eleven statements support the chronological predecessor scan: ordinary callbacks cannot change the selected cursor before a matching private request, while the existing private_state/advance_depth theorems account for actual matching hits and misses. Four declarations locally relax definitional-equality transparency for inherited dependent native/public Range aliases; this changes no proposition, axiom or computational resource bound. Local deterministic work remains ordinary source/primitive work; zero private queries does not mean zero shared state effects or runtime.

### RawCtxPendingParentCallbacks

The predecessor is selected at the actual matched callback and depth, including a private cache hit. `receive_step` and `send_step` expose the exact original native full-response decoding and private hit-or-miss execution; all cache/cursor changes and the same shared primitive state are retained. `kdf_state` derives the actual cache update and cursor advance from every supported callback result, without a freshness, successful operation or missing-cache premise.

`parentCut_iff` identifies the selector as exactly the current matching address and depth; cache presence is deliberately independent. `kdf_preserve` derives that unselected private callbacks cannot pass the predecessor depth when starting at or below it: unmatched callbacks retain depth, lower matches advance one, and a match at the predecessor depth is the unexecuted saved cut. `before_child` then rules out the fresh child cut while the cursor is still at or below the predecessor depth. The complete source invariant additionally requires the separately derived Store preservation of non-KDF callbacks.

These six statements preserve the cached predecessor branch. They do not claim a missing predecessor draw is common completion, bound a cache alias event, supply an initial input distribution or identify logical source sequence with cursor depth. All six actual standard-three guards passed in the final direct check with an empty log.

### RawCtxPendingParentPrefix

The actual entire native family is scanned before the matched predecessor callback at a chosen cursor depth. The selector is independent of cache presence. `scan_complete` proves exact recovery of the complete original selective family game by resuming that prefix with its original handler. Genuine completion before selection retains its actual result and full state; a cached predecessor request remains an explicit pending branch.

`reached_context` derives the original full owner/Server-or-Beacon/family/LIVE frame, dependent continuation, exact request address and actual matched cursor depth from the same supported prefix. It supplies no cache-miss or address-separation assumption. `step_preserve` discharges the full predecessor-depth invariant using actual private callback cursor updates and the exact Store preservation of every opening, sealing, public and optional-read callback.

`scan_same` proves that child stages d+1 and d+2 share the same original complete prefix before the matched callback at depth d, starting from actual cursor depth at most d. The source initial cursor zero discharges that arithmetic premise in the later consumer. `adjacent_complete` recovers both original whole-family stages by resuming that one common prefix with their actual handlers. `scan_valid` retains the depth invariant in every supported completed or pending result. No protocol preservation premise, success premise or evaluated-cost transport is supplied.

The next source consumer must split the actual predecessor cache hit from its fresh full76 draw, retain chronological cache-input provenance and compose the material-only observer with the ordinary child endpoint. These six operational laws do not charge a cached predecessor alias by themselves, infer uniformity from reachability, or identify a cursor with the final logical record. All six actual standard-three dependency guards passed in the final direct check with an empty log.

### RawCtxPendingRetainedExecution

The four statements consume the actual pending backend compiler, not a supplied callback equation. saturated lifts the existing exact monotone-cursor saturation law to every original pending family program. retained_run then projects only the completed private table/cursor and equates the entire original result/shared state with the fixed retained view of the original cache, including earlier hybrid outputs and the actual fixed source fallback. logged_retained additionally removes only the private chronological input list after the complete continuation; the original family, live history, ratchet state and primitive shared state remain in the returned result. parent_resume consumes the actual matched predecessor response and depth to identify the complete real-child future with the retained original prior plus that full76 parent entry. Neither a fresh-parent premise nor prior/child address separation is required for this operational real-stage equation. Public source evaluations are unchanged. The random-child early-draw splice, label interpretation, alias charging, source initialization and final secrecy remain later consumers. No evaluated equality transports resource or runtime costs. All four actual guards allow only propext, Classical.choice and Quot.sound.

### RawCtxQuietFamilyTails

The actual single family operation derives quiet captured source continuations at every inner layer. server_tail lifts the exact singleton Server witness through the original indexed Server installer. beacon_tail lifts the exact singleton owner witness through the original Beacon phase installer. step_tail covers all role indices, public operations and inactive Beacon rejection; single_tail supplies the zero-query outside client directly from the literal single source query.

The witness retains complete original owner, peer, role family, phase controls, associated data, pending payload and dependent continuation. Zero-call evidence is derived from the source syntax, rather than supplied for an arbitrary Context. The pending operation still requires a separately charged material-only completion; the outer LIVE continuation requires its original residual source budget. No cryptographic, freshness, success, key equality or cache-miss premise is added. All four statements use default elaboration settings and the standard three axioms only.

### RawCtxQuietOwnerTails

An original singleton owner source request carries only its own return continuation. The three statements make that resource provenance explicit. zero_pure proves that a source program with total query cap zero is an actual pure return, preserving its result. step_tail analyzes the original send/raw/public frontend and proves that any selected private KDF callback inside a request with a zero-query outside client has an exact original OwnerContext frame and the same zero-query outside-client evidence. single_tail discharges that premise from the actual singleton source query and its literal pure return.

All source admission, empty-input, parser, sender/associated-data, rejection, send advancement and receive publication branches remain. A selected query cannot arise after the operation has finished because that outside source client has no calls. The original full pending context is returned together with its exact Sigma(query,continuation) equality. This is a proved source-budget witness, not a newly assumed bound on an arbitrary Context. The pending material-only resumption itself still has a separate source-derived completion bill. Server/family single-request lifting and the outer LIVE residual budget are subsequent consumers. One declaration locally relaxes dependent Range alias transparency; no heartbeat, trust or cryptographic assumption changes.

### RawCtxQuietServerTails

The exact singleton Server operation derives its original OwnerContext and ServerContext together with zero-query evidence for both captured source continuations. owner_tail obtains the quiet owner witness from the actual singleton selected-owner request, then lifts its exact dependent frame through the original peer installer. step_tail retains the original send/raw route, peer and associated-data selection, including missing routes and peers, and proves that no selected private query occurs in the zero-call outside source client. single_tail discharges the quiet Server continuation from the literal single source query and pure return.

The complete original peer, Server state, attempt count, pending payload and dependent continuation survive. These three statements establish source resource provenance, not a bound assumed for an arbitrary saved context. They add no cryptographic, freshness, successful execution or peer-equality premise. The pending material-only operation still needs its separately counted completion; family lifting and the outer LIVE residual source budget are subsequent consumers. All declarations use the default elaboration settings and standard three proof axioms only.

### RawCtxRetainedParentBackend

The retained complete pending family interpreter is exactly the existing native retained-parent LIVE interpreter. Its private KDF lookup is the actual earlier cache view extended with the same parent entry and next-chain value. It preserves all original shared primitive effects and every optional live read. No freshness, successful callback, distinct key or source compatibility premise is supplied.

`native` proves that forwarding native calls through the private-only retained compiler equals the existing retained-parent mixed backend. Private derivation replies use the exact full76 lookup. Every other native operation remains the original implementation, including opening, sealing, commitments and publication.

`public_calls` proves that caller coins, public commitment work and public HKDF views remain the actual real source service for every retained lookup. Public calls bypass the private table rather than receiving independently sampled values.

`pending` discharges the exact pending receive/send/public handler identity. It consumes the already checked native receive and send adapter equations, preserving full KDF responses, original opening arguments, complete advanced sealing state and optional failure behavior. No external whole-call equality is assumed.

`retained_live` combines these concrete identities with the unchanged actual native reader, proving the entire QueryImpl equality requested by the original family frame continuation. This supplies the operational connection from the saturated logged-source backend to the retained-parent native/label source relation. It does not itself assert a cryptographic hop or evolving-chain secrecy. Query effects remain identical by literal interpreter equality, including the full shared state; no costs are transported between merely equal evaluated distributions.

All four guarded statements pass with only the standard imported three axioms and default elaboration limits. No custom axiom, primitive implementation proof or additional security premise is introduced.

### RawCtxScaledBadEventMixture

local_probability converts a local Boolean distinguishing bound with its finite candidate coefficient into a one-sided ENNReal probability inequality. bind_probability averages that same inequality over the complete original sampler and keeps the coefficient outside the same bad-event game. bind_bound applies both directions to recover the absolute distinguishing advantage. All laws allow subprobability/divergent samplers, use no conditioning and introduce no cryptographic or source-distribution premise. The consuming proof must supply its actual local source comparison. All three actual guards retain only the standard propext, Classical.choice and Quot.sound dependencies.

### RawCtxSelectiveFamilyLog

Every executed private receive/send callback appends its actual request address to the chronological list, including cache hits and requests used by later rejected operations. Non-KDF callbacks append nothing and retain their full shared effects. The log is private instrumentation and is updated after the actual callback; a pending predecessor saved before execution is not silently included in its prior list.

`program_projection` removes only this log after the complete enriched execution and gives the exact original result, primitive state, private cache and cursor. `source_projection` applies the same equation to the actual complete original native family game, retaining every family and history field. `scan_projection` gives the corresponding literal equality for any state-dependent pending scan, preserving its original dependent query/continuation and reached state. None of these equalities removes a native field, cache binding, earlier history or primitive effect.

`Covered` means every existing cache binding address occurs in the retained input list. `empty_covered` derives the initial case for the actual empty private cache without enumerating a functional table. `step_covered` consumes the actual KDF cache update and actual non-KDF Store preservation; a new binding adds its exact request, and every other binding remains covered. `program_covered` and `scan_covered` carry this property through every supported complete or pending adaptive execution. Initializer inputs and earlier source history may be retained in an explicit initial list; their own source provenance must still be supplied by the initializer/history consumer.

These seven operational laws establish log/cache provenance and exact source projection. They do not make cached inputs independently uniform, bound a cache-hit event, establish a source log-length cap or supply the final adjacent hybrid sampler. The exact query and source-budget consumers follow separately; deterministic list/lookup work remains real local work. Actual dependency output gave no axioms for the empty-cache theorem and only the standard three for the other six; all seven final guarded direct checks passed with an empty log.

### RawCtxSelectiveFamilyLogBounds

receive_private and send_private count the actual enriched pending callbacks under every possible chain/material reply: an original receive has at most 51 private KDF calls and a send at most one, with exhaustion rejecting before a call. family_private preserves those counts through every actual sender/AD/peer/Beacon-phase gate and indexed role update. source_step forwards the complete original role work and adds no private KDF call for public services or reads. program_private and source_private consume the original six-coordinate source budget and derive S+51R on the literal enriched LIVE program, including repeated cache hits and rejected record attempts. No cost bound is transported through a distribution equality.

inputs_length proves that the chronological log appends exactly one address for each executed private callback and otherwise stays unchanged. program_length bounds every supported complete logged execution by the actual initial list length plus its structural private-call cap. scan_length does the same for any state-dependent scan and every complete or pending outcome. A saved pending query has not executed and is not yet included in that log. source_length applies the bound to the actual full native family game, preserving its native role and history projection. source_scan_length applies it to the actual original-family pending program before a state-dependent cut.

The resulting complete and prefix caps are initialInputs.length+S+51R. Initializer/root addresses and any earlier list remain explicitly counted; no functional private table is enumerated. The existing Log7 cache-domain invariant proves every cache binding is represented by this actual list. All local hashing, cache lookup and list work remains actual deterministic work; these bounds introduce no cryptographic, freshness, cache-miss or uniformity premise. All eleven guards use only the standard three axioms and default elaboration settings.

### RawCtxSelectiveSingleDraw

The three statements isolate the final selected private draw while preserving the entire adaptive continuation. saturated_view projects only the completed private cache/cursor and obtains the fixed view retaining every prior private binding and all common source state. single_uniform starts with one derivation remaining and the actual current cursor address absent from that cache. It proves exact evaluated-distribution equality to drawing one complete76 response early and inserting it only in the private retained view before the same full client. The proof covers genuine completion before any child query, arbitrary shared backend effects, unrelated private hits/misses and the actual selected query followed by its saturated tail. Independent sampling commutes only at the evaluated-distribution level; no syntactic sampling-order equality or work transfer is asserted. The original full Result and common state are retained, so concrete family/history and final target lineage may remain in that result. The missing-current-address condition is an operational branch fact; final source secrecy must derive it outside the explicitly charged prior-cache/parent-input candidate event and keep the other branch. early_uniform independently bounds the literal early-draw comparison by76 plus every all-reply continuation uniform query, including an unused draw when the original client would complete early. Public and other callbacks remain the unchanged other handler; this is a private KDF substitution only. Actual initializer linkage, source Context/label realization, alias probability and final secrecy remain consuming work. All three actual guards allow only propext, Classical.choice and Quot.sound.

### RawCtxSourceLineagePositions

`RawCtxSourceLineagePositions` connects the finite private ancestry syntax to the actual source position model. `chain_position` and `material_position` identify every interpreted input and complete record material with the original fixed-source chain and record index. `earlier_mem` and `earlier_forbidden` derive ancestor membership without any injectivity or distinct-key premise. `current_descendant_not_fresh` consumes an actual optional current-chain reply, its original directional origin/counter relation, and retained disclosure history to invalidate every later same-direction record. `skipped_record_not_fresh` consumes the actual successful skipped-key reply, derives its positive wire sequence, and proves that appending the reply invalidates precisely that record. These are operational exposure laws; the initializer must establish the existing position relation, and the evolving hybrid must establish its own representation. All six actual axiom reports were checked and guarded; only Lean’s standard propositional extensionality, classical choice and quotient soundness occur. No snapshot, persistence or restoration service is included.

## Initialization, complete continuation and source-risk checkpoint

This topic checkpoint adds 53 modules and 301 guarded statements. It proves the source-derived initializer query bounds and equal-root comparison, the actual first-send and complete current post continuation representation, the adaptive first-cache-hit risk bound, supported stopped contexts and checked freshness reductions. It also retains original directional origins, successful publication records and supported replay under the final private view. This remains a component checkpoint. The actual full-post compiler must still expose private derivation requests to the stopped reduction, preserve the builder and Beacon-finish tails, establish the common final publication/freshness event across every adjacent game and derive the total reduction ledger. The 53 explanations below identify what is established and what remains a consuming obligation.

### PqxdhInitialAliasBound

PqxdhInitialAliasBound closes value-correlation accounting for the selected initializer response at an independent32-byte root. The sampler retains the complete earlier context, then samples the root and one64-byte response. The root is absent from the original labelled client, supplied response and entire private cache/known-root observer. Public HKDF stays real.

1. pointwise applies the checked original candidate coupling while retaining target root, full64 response, result, root cache and candidate list.
2. cut_distance averages that full coupling over exactly the shared context/root/response draw and charges the original final candidate event.
3. delayed proves a complete-continuation interchange moving the hidden root after the independent response and entire adaptive observer. It preserves all cached/generated/known root effects and all final fields. It is not a marginal distribution argument.
4. candidates_bound uses the source client's all-reply initializer count and actual recorded roots to derive the unconditioned qInitial/2^256 candidate bound. No freshness or root-coordinate injectivity premise occurs.
5. cut_bound derives the same explicit full-state statistical distance to the value-consistent selected-response interpreter. In the real response world, RootAliases.consistent_real is exact, so no separate real-response tester loss is needed for this comparison.

All five actual standard-three guards pass with default heartbeats and recursion limits. Source-derived concrete client/query-cap consumption follows in the current-protocol specialization.

### PqxdhInitialBeaconAmbient

The ambient lift retains the actual shared primitive state together with the private identity state and the separate root-family cache. A primitive computation updates its original shared state and leaves the other two components unchanged. This does not remove any effect; it is the exact packing used by the current native raw callback.

`lift_pure`, `lift_bind` and `lift_map` prove the literal monad and reply-map equations. `simulate_lift` applies the same lift to every adaptive source callback, and `compose_lift` preserves actual adapter composition. `receive_lift` applies these equations to the complete native receive program. `selected_receive` discharges the retained-parent native/Slot receive equation in this full ambient state. No fixed-cache, freshness or cryptographic assumption appears. These syntax equalities preserve the original callback work; no query costs are inferred from marginal distribution equality.

### PqxdhInitialBuilderServiceBound

The actual Server registration builder makes at most one private 64-byte initializer request. `candidate_initial` follows identity validation and peer reservation, then the single initializer followed by its complete native continuation. `used_initial` includes allocation, consumed-registration and binding gates. `tail_initial` shows every ordinary native/auxiliary callback retains its coins and state without gaining an initializer interface. `protocol_initial` includes the actual selected Server state and reinstallation. `compiler_initial` preserves this cap when the request is labelled by its actual selected root coordinate. `build_initial` proves the complete labelled builder cap of one.

`accepted_initial` combines that actual builder cap with the original source post budget. The full accepted current initializer client has at most 1 + c.privatePost private service requests, where c.privatePost is the source budget for post finish attempts. The bound covers every possible reply and all rejection branches, and includes repeats or failed finishes. It does not infer cost from a source-distribution equality or assume a bound on an opaque observer. Ordinary coins and primitive costs are separately charged by InitialObserverBudgets; the alias coupling consumes this service count.

### PqxdhInitialCurrentAliases

This module consumes the exact current authenticated-root prepared state and the actual response-only initializer client. observer_client identifies the root-free client in completed and pending cases. trace_decision removes only the private candidate instrumentation and recovers the actual observer. random_source retains the original context/root32/initializer64 sampling order and the complete original continuation. random_bound then applies the independently proved complete-trace root-delay law: every other private initializer evaluation contributes one candidate, so value-consistent routing differs by at most qInitial/2^256. primitive_bound composes that statistical term with the actual CurrentSecrecy fixed-salt Extract and ordinary HMAC PRF reductions. The HMAC comparison has two challenge queries and uses only the source initializer's64-byte prefix; source initialization has no nonce. Public HKDF remains real. Equal root bytes at distinct coordinates are not assumed impossible. The initializer count premise is the syntactic bound on the displayed actual client; the separate certificate ledger derives it, rather than treating ambient work as free. This local initializer capstone is not by itself the full evolving-chain theorem.

### PqxdhInitialCurrentBeacon

The current source Beacon owner is instantiated inside its exact complete ambient state: shared primitive state, private identity BareState and shared root-family cache. The original PrivateBeacon.compiler is evaluated with the actual labelledFull cache and selected64 response. Its private record KDF is the concrete retained-parent interpreter. The resulting executable Slot owner receives a supplied child response, the selected orientation and opposite32, but no selected input bytes. Its preparation and application callbacks are the original root-free computations and take no selected-chain argument.

`raw_shared` identifies the retained-parent native receive backend with the actual shared primitive callback. `coins_labelled` preserves every original probabilistic computation and its unchanged root cache. `preparation_source` and `application_source` prove that the actual compiler executes the original callbacks and complete state effects. `raw_source` proves the exact packing of the retained native raw callback into SharedState, BareState and root cache. `initializer_source` factors the actual source request through the known/selected service, preserving the original coordinate, optional reply and full cache. `initialization_map` derives the optional Slot-kernel equation from the original64 response constructor for both orientations. `source_owner` consumes all those concrete equations to prove the complete current fused Beacon owner equals the Slot owner under native projection. It retains sequence-one/binding/pin checks, failures, all phases, publication and all ambient effects; no caller supplies a callback compatibility premise.

The displayed source correspondence instantiates the Slot owner's challenge with the retained table's actual childResponse. Subsequent cryptographic hybrids supply the response through their ordinary challenge interface. The service is the coordinate-labelled cache world; equal-byte initializer-root aliases remain the separately proved CurrentAliases loss. This module adds no uniformity, freshness or query-budget premise and does not claim the final evolving-chain secrecy theorem by itself.

### PqxdhInitialCurrentBudgets

This capstone consumes only AuthenticatedRootBudgets.Certificate for the actual current initializer source. client_initial derives at most one Server initializer plus c.privatePost attempted Beacon initializers, across completed and pending modes. primitive_bound instantiates CurrentAliases with that derived count: the actual uniform-root current endpoint reaches the value-consistent random64 initializer at loss ExtractAdv + HmacAdv + (1+c.privatePost)/2^256. joint_uniform and observer_uniform derive exact literal source bills Qs=qKeygen+uPre+qBase*bPre+qDecap*dPre+qEncap+32 and Qo=uPost+qBase*bPost+qDecap*dPost+32*privatePost. reduction_bounds gives HMAC challenge cap2 and reduction-local uniform cap Qs+Qo. challenger_uniform separately charges Extract real Qs+Qo, Extract uniform Qs+64+Qo, HMAC real64+Qs+Qo, HMAC random Qs+128+Qo and independent full comparison Qs+76+Qo. extract_work bounds the actual Extract observer at Qo. random_uniform bounds the actual source64 randomized endpoint at Qs+64+Qo. Source initialization still creates no nonce; comparison-only bytes remain separately charged. No whole-protocol callback budget or source-independent established-state premise is assumed. Source primitive callback distributions/contracts and all all-reply source client counts are exactly those in the existing Certificate.

### PqxdhInitialCurrentPost

PqxdhInitialCurrentPost source and program identify the entire actual PqxdhInitialPrivateBeacon.target with the generic scheduler nativePost. The original record private KDF handler is unchanged and all coins keep their original lift. The actual public identity/CCA selector retains its original private state, public response and challenge block. The Beacon finish branch uses the exact original FusedOwner and current compiler. The equations include every query class and full adaptive continuation, with no assumption about selected kernels or success. This closes the native-side whole-scheduler interface; the retained-slot interpretation and its freshness/candidate comparison remain separate consumers.

### PqxdhInitialEvaluatedCurrent

The concrete accepted authenticated-root source endpoint is represented before the original Server first ciphertext and throughout the entire original adaptive post continuation. The pre-draw protocol state is represented using knownKernel, which is independent of the selected hidden half. The actual builder retains consumed bindings, source admission gates, failure and publication outcomes, and its complete poststate feeds the same original post client. Both the builder and post use one retained private KDF interpretation, and the original private identity state and initializer cache remain intact. The proof instantiates the concrete builder and evaluated post equations; it does not assume their correspondence. This is a full operational equation at the retained-handler intermediate, with target bytes still in mathematical native interpretation and reveal reads. Typed source-marker elimination, the source-exposed stopped compiler, common target freshness and resource/reduction consumers remain necessary before a final secrecy theorem.

### PqxdhInitialEvaluatedPost

The complete evaluated current source continuation preserves records, private identity/CCA requests and attempted Beacon initialization in their actual adaptive order. Its concrete record map is InitialEvaluatedRecords.selected_record; its concrete whole owner map is InitialCurrentBeacon.source_owner. Both are instantiated directly, so the final source theorem has no callback-compatibility assumption. The same initializer cache remains under the whole role/shared/Bare state, including optional replies and failed operations. Target bytes enter the mathematical native representation and original reveal reader, so this source equation is not yet a primitive reduction: the stopped checked continuation must replace that reader under explicit freshness, retain the source prefix and pay all outside work.

### PqxdhInitialEvaluatedRecords

The evaluated record interpreter preserves the initializer root cache. Ordinary source randomness runs in its original order, leaves that cache unchanged and retains every record reply, native protocol field and private shared-primitive effect. The selected-record equation instantiates the retained private KDF and lifts its existing complete-state source equation into the shared cache monad. This is operational correspondence; native reveal interpretation still contains the selected target and must be replaced under the checked freshness compiler before constructing an ordinary secret-input primitive adversary. There is no marginal generator interchange, security assumption, query-free ambient computation or end-to-end secrecy conclusion here.

### PqxdhInitialFusedBudgets

PqxdhInitialFusedBudgets derives all-reply callback counts for the actual response-only Beacon owner. after_total charges the application getter plus complete original raw receive:54 calls. tail_total adds the private fused root/initializer query:55 calls. owner_total includes all13 original preparation callbacks, giving68 calls on every branch, including inactive states, absent initializer responses and arbitrary supplied64-byte replies.

after_no_service proves that the remaining raw/application tail cannot request the initializer again. tail_service and owner_service derive at most one private initializer request. owner_decapsulation transports only the existing preparation decapsulation count through the actual query injection and proves the fused tail adds none, so the complete owner attempts at most one decapsulation. These are syntactic all-reply bounds, not costs moved across an evaluated-distribution equality. The consuming observer ledger must still interpret actual native, base, decapsulation and initializer-service costs; local deterministic computation is not declared free.

All seven actual guards pass with only the standard three Lean axioms and default elaboration options. No primitive or protocol security premise is introduced.

### PqxdhInitialGenericBeacon

The generic Beacon first receive changes only the private kernel representation. Its initializer returns an optional kernel, and the application getter and complete raw receive execute in the original order. The raw receive returns the kernel used by authentication and staged publication, including failed advancement. Sequence one, the eight-byte binding prefix, exact registration authentication, pinned server identity and key checks, abort state and all successful publication fields are preserved. Preparation uses the original Phase-2 program and all inactive phases retain their full state.

`opening_map` preserves sequence, length, binding and authentication branches. `finish_map` preserves abort and publication with only the kernel mapped. `afterInitial_map` retains the original application response, complete raw receive and ambient effects under the exact receive-call map. `tail_map` additionally consumes an exact optional initializer map. `owner_map` carries these equations through the original preparation and every phase. The call and initializer premises are operational equations, not cryptographic assumptions; the following native correspondence module discharges them against concrete source operations. These five theorems contain no secrecy or freshness conclusion and add no query bound.

### PqxdhInitialGenericBeaconNative

This module proves exact operational correspondence between the generic Beacon first receive and the existing fused source program. The ambient interpreter is arbitrary and may retain mutable shared state. The native call definition interprets the actual complete receive oracle; its send field is unused by this receive-only owner. The initializer maps the original optional full64-byte response to the same normalized concrete kernel at the same callback site.

`opening_native` preserves sequence-one, plaintext-prefix and registration authentication checks. `finish_native` preserves abort and successful publication, including the complete prior Beacon fields and raw-attempt count. `raw_native` proves that the directly interpreted receive calls execute the original raw admission and publication program. `afterInitial_native` retains the actual application getter, exact original initializer constructor and entire receive continuation. `tail_native` includes the optional private service and every failure. `owner_native` includes original preparation and all inactive phases with no functional compatibility premise. `owner_mapped` then changes a private kernel representation using only the exact per-receive and optional initializer equations; it derives the whole source correspondence, rather than assuming it. Concrete retained-parent calls and selected64 constructors discharge these remaining small operational equations in the consuming post wrapper. No theorem adds a cryptographic, freshness or query-budget assumption.

### PqxdhInitialGenericBuilder

PqxdhInitialGenericBuilder contains five source representation results for the actual Server registration builder. candidate_native preserves the identity check, peer reservation, supplied initializer failure, application-length checks, plaintext reservation, eight-byte key binding and first send/publication in their original order. used_native additionally preserves current allocation and occupied-peer checks; ready_native includes the actual authenticated Ready fields. These three intermediate equations name the complete send callback equation explicitly. ready_root_unused proves that a supplied typed initializer makes the old Ready root irrelevant to this executable generic builder. selected_ready discharges the send equation using the existing concrete retained-table interpreter, including every failure, raw ciphertext, private state and publication effect. The generic kernel can contain a hidden chain label before the first send. These are operational source equations, not an assumption that native kernel parameterization alone hides its bytes, and they supply no separate secrecy conclusion or query-cost transport. The whole protocol builder and initializer-half constructor must still consume them.

### PqxdhInitialGenericPost

PqxdhInitialGenericPost has three whole-scheduler representation equations. The generic/native states retain the full protocol state together with the private identity interpreter. installed_native proves that Beacon completion reinstalls exactly the same optional native owner and complete shared and identity poststate; every other owner, control and consumed field and the original history tick are preserved. step_native and schedule_native transport the original adaptive record/selector/finish schedule. They consume explicit complete record and owner equations, which the concrete current-source and retained-slot modules must discharge. These are operational equality obligations, not new primitive security assumptions. Selector replies and identity effects are common and exact. No target selection, freshness policy, key distribution or cryptographic conclusion is inferred here.

### PqxdhInitialGenericProtocol

PqxdhInitialGenericProtocol contains six complete-state representation equations. State changes only the installed kernel type, retaining every Server peer and Beacon inactive phase, registration allocation controls, consumed registration identifiers, original read history, raw-attempt counts and shared primitive state. roundtrip reconstructs the complete original state from a kernel representation with a proved inverse. selected_native proves the builder reads the same actual current fields. consume_native, install_native and finish_native preserve the exact source registration consumption, Server publication and Beacon history tick. reinstall_native covers ordinary success, failure and divergence with the same primitive poststate. These are operational equations, not secrecy conclusions or computational assumptions. The following modules must discharge concrete calls and initialization against this complete state.

### PqxdhInitialGenericProtocolBuilder

PqxdhInitialGenericProtocolBuilder connects the generic private ratchet representation to the complete actual current Server registration builder before its first send. build performs the original consumed-registration update, reads the selected current Server identity, allocation and peer fields, runs the checked generic Ready builder, and reinstalls the full result and primitive state. build_native proves literal complete-state equality with PqxdhInitialPrivateKdf.build under its displayed exact send equation, including failures and divergence. retained_backend identifies the concrete retained response interpreter with the same original shared primitive backend. selected_build uses that identity and the checked retained-table send theorem to discharge every callback compatibility premise. root_unused proves the complete supplied-initializer builder cannot use the old Ready root. All other roles, raw-attempt counters, reveal history, registration controls, consumed identifiers and shared cache remain present. The selected target occurs only in the mathematical native interpretation and retained source response; a legal reduction uses the label builder with a supplied child challenge. These operational equalities are not a secrecy theorem and do not transport cost through distribution equality. The initializer constructor/sampler and later generic poststate consumer must instantiate this source interface.

### PqxdhInitialGenericPublication

The generic registration State changes only the representation of each private ratchet kernel, retaining every existing Server peer, identity, metadata, allocation control and consumed-registration field. publish_native proves the exact original peer update and native projection. send_adapter identifies the actual registration first-send primitive adapter with the original mixed native send interface. after_native transports the entire original first-send, authenticated-plaintext erasure, optional serialization and publication tail through a full send equation in an arbitrary lawful monad, retaining all ambient effects. registration_source instantiates the native interpreter with the exact real source registration backend. selected_send discharges the full send equation concretely from the retained-table source send proof and labelled-chain interpretation. selected_after therefore preserves the entire first ciphertext/publication continuation with no caller-supplied compatibility premise; the executable labelled continuation receives a complete child response and contains no unavailable chain bytes in hidden slots. The target argument occurs only in native reconstruction and in the real source relation selecting that child response. A consuming initializer constructor and actual generic protocol wrapper must still supply the reached labelled state, selected response game, aliases/freshness and complete query bills. This module does not claim that an arbitrary existing labelled state is independently uniform.

### PqxdhInitialGenericRecords

PqxdhInitialGenericRecords has four whole-source transport results. native_source identifies the wrapper with the original PqxdhInitialPrivateKdf.records using exactly the chosen private KDF and the real public backend. record_native and schedule_native retain the complete generic protocol state, controls, consumed identifiers, source optional replies, original reveal history and shared primitive poststate under explicit full receive/send call equations. These intermediate call equations must be discharged by concrete interpreters, not assumed cryptographically. actual does so for every mutable native backend using RawCtxGenericNativeCalls; it starts from the original whole native state and reconstructs all fields. The retained-slot specialization is supplied by the following composition, and no hidden-input secrecy is inferred from these transport equations alone. Because the equality lives in an arbitrary lawful ambient monad it retains complete callback distributions; costs are provided by the source certificates, not inferred from arbitrary distributional equality.

### PqxdhInitialObserverBudgets

The current initializer sampler and full root-erased response observer now have source-derived uniform-query bounds. Let Upre = uPre + qBase·bPre + qDecap·dPre and Upost = uPost + qBase·bPost + qDecap·dPost. The actual sampler pays qKeygen + Upre + qEncap + 32, including the unused comparison root on completed branches. The complete observer pays Upost + 32·privatePost. It keeps all public HKDF and nonselected initializer calls real.

`sample_uniform` follows the actual current preparation, key generation, encapsulation and independent 32-byte root draw. `target_uniform` derives every original post callback's coins from its uniform/base/logical-decapsulation classes. `target_service` separately bounds private initializer callbacks by one per finish attempt. `post_bounds` follows the full adaptive post program under every reply and gives both its weighted coin bill and service count; `post_bill` identifies that weighted bill with the existing source classes. `labelled_step` charges zero coins for known or selected initializer replies and at most 32 for a fresh nonselected root. `labelled_uniform` accumulates these two resources through the complete labelled program. `accepted_uniform` additionally includes the actual Server builder's 64 + 5·qAux work before the post schedule. `observe_uniform` proves the same bound for the current observer, with completed branches returning directly.

The only resource premises are the existing actual-source `Certificate` and its primitive/local callback caps. These are syntactic all-reply bounds, not costs transferred through a distribution equality. The observer has no target root argument. This ledger does not itself assert initializer alias safety or evolving-chain secrecy; those use the separately constructed exact games and alias bounds. Local computation, fixed HKDF evaluations and source interpretation remain the explicit implementation/runtime contracts of the enclosing reduction.

### PqxdhInitialObserverCallbackBudgets

PqxdhInitialObserverCallbackBudgets interprets the actual response-only Beacon callback program. coins_uniform and coins_service preserve ordinary sampling and show it has no private initializer capability. public_step and public_uniform charge the original uniform, base and permitted decapsulation interfaces with their displayed primitive costs. The unused private-root fallback is pure; actual non-root callers reach it zero times by the previously checked syntax.

work_caps derives each actual preparation/raw/application callback class from the maintained PostScheduler handle bounds, retaining the complete returned shared and private state. compiler_uniform and compiler_service apply those counts to the literal new response-only compiler, for every request and state. Private initializer requests contribute one service request and no ordinary sampling at this interface; the cache interpreter is costed separately.

owner_partition consumes the actual fused owner bounds: at most68 ordinary callbacks, one decapsulation and one initializer request. The ordinary68 allowance conservatively includes the separately counted decapsulation, so owner_bounds pays69*max(qLocal,64)+qDecap uniform calls and one initializer request. This arithmetic does not infer source costs from an evaluated-distribution equality and applies to every supplied64-byte response, rejection and inactive owner. All local primitives and source effects retain their real cost contracts.

All nine guarded statements pass with the standard three Lean axioms; no new protocol-security premise is introduced. Whole adaptive post and accepted-builder bounds are consuming results, not assumptions asserted by this module.

### PqxdhInitialPostInterpretation

Two exact equations move evaluation of the private initializer service through the complete original post scheduler. Its root cache remains in the ambient state monad; the protocol role family, registration controls, primitive state and private identity state remain in their original fields. Every record/selector/finish callback and full adaptive continuation has the same evaluated distribution. No marginal key distribution or generator interchange is used; this is literal whole-program interpretation.

### PqxdhInitialPrivateBeacon

This module places the same explicit private record-KDF handler inside the actual Beacon initial receive and the complete current post scheduler. public_coins proves the original public forwarding returns the same full probabilistic work. raw_source derives the actual raw callback equality from its source interpreter, retaining the complete shared CTX state and private identity state. compiler_source leaves preparation, root/initializer and application callbacks exactly as before while the record handler is parameterized. finish_source retains the whole original fused owner and installation, including inactive and failed attempts. target_source covers original record/reveal/public traffic, unchanged identity and CCA traffic, and every attempted Beacon finish under one handler. program_source lifts the default source equality through the complete adaptive current client. The handler is active before opening the Beacon's first ciphertext. Together with PrivateKdf and PrivateBuilder it is also active before the Server's first seal. These are exact operational equations; alternative private handlers still require the separate chain security reductions. The public HKDF interface remains real, no private costs or alias probability are claimed free, and no saved-state behavior is modeled.

### PqxdhInitialPrivateBuilder

This module parameterizes the actual initializer-service Server builder by one private record-KDF handler before its first ciphertext. protocol_source proves literal equality with the actual source service when that handler is real. tail_supplied and tail_program preserve the complete native callback effects and state under a typed64 response. protocol_supplied carries that law through the actual consumed-registration state, root-erased Ready, first send, optional publication and complete reinstallation. root_unused states the erased Ready field cannot affect the executable builder. build_response interprets the original selected initializer callback, keeps its original position after identity/reservation checks, and then invokes PrivateKdf.build under the same handler. build_source returns exactly the established labelled current builder at the real handler. There is no generator reorder, independent established-state premise, or source initializer nonce. Public functions and all non-KDF callbacks are unchanged.

### PqxdhInitialPrivateCurrent

This module consumes the original current authenticated-root initializer continuation, before registration ciphertext production. accepted_source and observe_source prove that the real private record-KDF handler recovers the exact existing accepted observer and its completed/pending cases. accepted_response gives the complete source execution order: actual consumed-state Server builder, its original post-gate initializer response and first seal, then the original adaptive Phase2 post client through the same private handler, including Beacon first receive, later registration finishes, ordinary records, reveals and real public operations. The initializer root cache stays shared across that execution. random_source identifies the real-handler specialization with the current uniform64 initializer endpoint used by the checked primitive reduction. This is an operational interpreter seam only. A native concrete ratchet kernel still contains its selected directional half; an ordinary first-child reduction must additionally erase that half using the labelled-kernel constructor and prove the full source continuation transport. Parameterizing this handler alone does not establish such target independence or the complete chain-security theorem.

### PqxdhInitialPrivateKdf

This module exposes one shared private record-KDF handler at the real source boundary before the registration response is sealed. registration_source and build_source show that choosing the fixed source KDF gives exactly the original registration interpreter and complete builder. records_source proves the same equality for all actual record/public/reveal scheduler queries while retaining complete role state, shared cache, original history and control fields. build_supplied consumes the source callback-placement proof: identity and reservation gates still precede the supplied typed64 initializer response, and the first send uses the chosen private handler before publication. public_hkdf proves that public evaluations remain the actual source function even when private derivations use another handler. These are operational source equalities for arbitrary private handler effects, not a security assumption or an independent initial-state premise. Source state reassembly here is ordinary execution only; saved-state or persistence behavior is outside this task.

### PqxdhInitialRootAliases

PqxdhInitialRootAliases exposes each nonselected root-cache reply only inside the private response interpreter. It then records the same32 bytes immediately before the real64 initializer evaluation. Selected-coordinate requests return the supplied response without a selected-root argument. Public callbacks stay the original real work.

1. source_step preserves the original private service callback and its full cache.
2. source_program derives the same equality for every complete adaptive client.
3. trace_source erases only the analysis candidate list and recovers the complete original labelled execution and root cache.
4. consistent_initial routes every equal-byte root to the supplied response and retains real evaluation at all unequal roots; this includes known roots and roots obtained from any other family coordinate.
5. consistent_real proves this value routing is exactly the original handler when the supplied response is the actual source response. No absence-of-alias assumption or real-world alias loss is needed.
6. distance compares the complete recorded coordinate-labelled run and value-consistent run. The entire difference is charged to selected-root membership in the original final candidate list, including the entire supplied prior list.
7. compiler_evaluations proves each original initializer request contributes at most one known-root evaluation and selected coordinates contribute none.
8. program_evaluations transfers the original all-reply initializer cap through the actual private expansion.
9. trace_length derives the final candidate length from that same original cap, preserving all previous candidates, cache hits, repeats and failed attempts.

All nine actual standard-three guarded axiom checks pass. The following probability layer supplies the actual independent-root random-response sampler, so this file makes no small-alias-probability assumption. Real public HKDF is never programmed or filtered by a freshness premise.

### PqxdhInitialSelectedBeacon

This concrete specialization discharges the generic Beacon receive map with the existing retained-parent source backend and full native/Slot receive equations. Its private initializer reply is either known64 bytes or a selected-half orientation with the retained opposite32 bytes. The selected input is absent from the label service interface. A known response retains its exact native chains; the selected constructor is the checked nonce-free source64 constructor for either direction.

`option_map` converts complete RustM constructors to optional kernels by pattern matching and commutes with representation. `known_native` reconstructs all fields of a kernel whose chains are known. `selected_initial` derives the normalized concrete Beacon initializer from the actual64 join and the checked Sentinel constructor, without a new choice operation. `selected_receive` composes the concrete original native receive and retained-parent call map, retaining all shared effects and optional failures. `response_map` handles both initializer reply forms. `initializer_map` retains every effect of the original service and the exact returned response; it samples nothing. `owner_selected` instantiates the complete original fused Beacon owner, preparation/application callbacks and entire native state without any assumed callback correspondence.

The arbitrary service argument is an operational interface, not a uniformity or freshness premise. The following selected-service module instantiates it with the actual coordinate-labelled root cache; repeated selected coordinates reuse the same response and nonselected roots keep their real evaluation. No secrecy or query bound is inferred from this representation theorem.

### PqxdhInitialSelectedBuilder

PqxdhInitialSelectedBuilder contains six concrete initializer-to-first-send representation equations. kernel_response consumes the actual typed64 response and produces the original zero-state constructor for either role and either selected directional half; the other32 bytes remain known and no source nonce is introduced. supplied_build keeps the original initializer callback after admission checks and before the first send, then applies the complete current protocol builder map. labelled_build additionally preserves the current labelled root service and its entire private cache. known_kernel and known_state retain every preexisting chain as known, proving complete native reconstruction independently of the newly selected half. supplied_known consumes that target-independent representation in the original source builder. The source-side private KDF remains the explicit retained-table interpreter, and a later typed-source marker removal proves the root-domain sentinel is unreachable by actual record requests; no global equality for arbitrary KdfSpec inputs is claimed. These operational laws retain all source gates, ciphertexts, optional failures, publication and full private state. They neither assert independent established states nor expose a selected half to an ordinary reduction observer. Query bounds and the separate64/76 comparison sampler remain separate checked consumers.

### PqxdhInitialSelectedRecords

Five equations discharge the concrete retained-parent current record interpretation. native_backend identifies the exact original mixed shared backend with the chosen retained private KDF. receive_native and send_native consume full source callback laws, and record/schedule instantiate the generic full-protocol mapping without caller compatibility assumptions. All public HKDF and commitment services remain the actual source backend. This intermediate reader deliberately returns the original native optional bytes; it is not the target-free observer. The existing masked-reader candidate and freshness coupling must still be consumed by the final composition, so no secrecy follows from this representation alone.

### PqxdhInitialSelectedService

The target-free initializer service is constructed from the actual coordinate-labelled root cache. Its selected-coordinate reply contains only the selected-half orientation and retained opposite32 bytes, reused on every selected request. Known roots and nonselected family coordinates evaluate exactly the actual64 prefix; the nonselected family path reads or samples through the same original uniform root cache. Public and ordinary callback interpretation remains unchanged.

`known_response` uses the checked shared64/76 source law. `value_response` proves exact reply and complete StateT cache equality with the existing labelled service. `full_handler` includes every ordinary coin query, and `full_source` preserves any complete original adaptive client and its final root cache by literal interpreter equality. `service_response` uses the exact original RootLabelBridge.request at the compiled Beacon initializer site, retaining the optional reply and cache. `value_uniform` separately proves the actual syntax bill of at most32 uniform bytes per service request; known inputs, selected coordinates and cache hits are pure. Real source HKDF remains deterministic local work.

This factors the coordinate-labelled world. Equal-byte roots at different coordinates remain the explicit CurrentAliases comparison event and are not silently ruled out. The ambient shared/Bare/root-cache owner integration is proved in the following concrete current Beacon module.

### PqxdhInitialSentinelSource

PqxdhInitialSentinelSource removes the root-domain analysis marker through actual typed protocol operations. prior_source identifies the unmarked retained handler with the exact real source private HKDF at the production lookup. pending_marker proves equality on the original enriched pending interface: actual receive and send KDF callbacks carry the literal ratchet label, so neither can address the root-domain marker; all non-KDF callbacks keep the same shared effects and public replies. send_marker and receive_marker lift this typed equality to complete original native operations, preserving failed sealing, advance, skipped-key/cache paths, optional plaintext and rollback. selected_build consequently proves the full current Server builder map with the unmarked private source lookup, without a compatibility premise. supplied_source instantiates the actual production lookup and the original initializer-service builder, introducing the selected-half representation before the first ciphertext from the complete original pre-draw state. The source has no sentinel cache binding or initializer nonce. The theorem deliberately does not claim that arbitrary KdfSpec inputs use the ratchet label. Every source state field and shared effect remains retained; these operational equations introduce no cryptographic premise, secrecy inference or distribution-based resource transfer.

### PqxdhInitialSourceSampler

PqxdhInitialSourceSampler connects a uniform64 source initializer to the complete original current Server builder and an arbitrary complete continuation. source_halves consumes the checked real-private-HKDF typed-source equation, so the selected-half representation is present before the original first ciphertext. full_continuation preserves the original64 response, every builder result and complete protocol/shared poststate through an arbitrary continuation and an arbitrary prior context distribution; the selected orientation can depend on that context. It uses one shared directional draw, retaining the opposite half, and compares this with a full76 analysis draw whose extra12 bytes never enter source initialization or a source cache. The continuation is a private mathematical continuation; the theorem does not claim that an ordinary reduction receives the selected half or full private64 output. The later complete observer map must remove those unavailable values from executable context. source_uniform derives the actual builder bill64+5*qAux from the existing nine-class source proof. selected_uniform uses literal OracleComp equality, not equality of evaluated distributions. execution_queries separately proves source cost qPrior+64+(64+5*qAux)+qNext and comparison cost qPrior+76+(64+5*qAux)+qNext. Auxiliary and complete outside work are explicit resource contracts; no entire-builder budget is assumed. The only extra12-byte draw belongs to the comparison program, and no primitive implementation property is proved.

### RawCtxAdjacentCacheNormalization

The four statements consume the actual source-derived first-hit probability, rather than postulating a small cached-parent event. Both original adjacent source games share the same executable forward prefix. `source_adjacent` retains each exact saved continuation and every final native family/history, shared primitive state, private table, selected cursor and chronological log.

The normalized random endpoint executes the original real-stage continuation on exactly the earliest matched Cached branch and otherwise executes the original random-stage continuation. `normalization` bounds that replacement by one copy of the actual source collision sum from FirstParentRisk.cached_risk. Cached branches are not deleted or resampled. Initial coverage, depth, list-length bound and Clean are explicit source-state conditions; the empty-cache fact is already proved in FirstParentRisk.

`normalization_after` retains this same bound for an arbitrary common complete-state continuation. An appended private lineage checker can therefore read the same final cache, cursor and log before any projection removes them. `adjacent_bound` gives the resulting advantage triangle for one unchanged final Boolean decision, with coefficient one on the source collision sum. The remaining normalized fresh-parent comparison still requires the actual parent sampler, original lineage/event linkage and constructed primitive reductions; this module does not claim those are already instantiated.

### RawCtxCertifiedParentSource

The four statements consume a pending proof subtype from the actual common/pending source sampler. pending_mode derives the same original pending Mode support; source derives its exact constructive first-sampler support and cache miss. lineage applies the actual mutable-callback invariant to that same supported original scan, retaining all initial full bindings and the path from the original initial coordinate. earlier_actual reconstructs the prefix ancestors by a finite executable cache walk and proves its exact length, final selected address and actual binding for every earlier input. It does not invert a saved function or select a replacement Context.

This certificate permits later all-inhabitant resource bounds to be discharged from actual source support. It is still cursor/path provenance, not a supplied equality between cursor depth and successful source record sequence. The final source publication/lineage event remains a concrete consuming obligation.

### RawCtxCheckedBudgets

RawCtxCheckedBudgets charges the actual appended finite checker through the same original private receive-derivation capability. forward_class and checker_class give n+1 private callbacks and zero callbacks of every other class. These callbacks are deterministic local KDF evaluations, not free work. The checker retains a list of n+2 lineage values; its copying and actual private-function evaluation costs remain part of reduction runtime.

stopped_class consumes one exact carried source Context and its residual source certificate. It adds the original receive/send reserve, every outside source request and the n+1 checker calls. source_checked identifies that program with the type-dependent completion used by CheckedParentSecrecy, preserving the original request's exact reply type and outside continuation without choosing an inverse of the frame map.

uniform derives U+64(S+R+H+1) from the full checked program. candidates derives initialCandidates+254+S+51R+K+E+(n+1), retaining duplicate candidates and counting failed operations. history_candidates initializes that actual ledger with every saved disclosure and earlier candidate. The final source consumer must use the actual carried context's residual certificate and combined prefix-history/residual-reveal bound, rather than bill the full reveal budget twice or substitute a different equal-frame descriptor. No cryptographic-security or freshness premise is introduced by these resource statements.

All seven actual guarded statements pass with only the standard logical axioms. These statements do not themselves establish the ordered source hybrid; they supply its concrete observer costs.

### RawCtxCheckedFreshness

The actual final event evaluates the complete interpreted lineage returned by the private checker, together with all earlier ancestors, against the original source disclosure history. It is conjoined with the adversary's original Boolean decision without conditioning. The target-free event uses precisely the checker’s known values and the original clear-disclosure flag. It has no unavailable target argument.

`good_bound` derives the pointwise event relation from the actual completed source invariant and appended checker. Actual freshness implies a clear hidden-read flag; conversely the executable proxy gives actual freshness outside the same complete final candidate event. The candidate event includes all later checker queries because the checker uses the same primitive interpreter and ledger. Direct compromise does not contribute an additive probability term.

`decision_bound` lifts that relation to the original Boolean experiment without modifying the adversary or adding a freshness precondition. `bound` composes the actual reader/private-alias comparison and the target-free masked observer. The result pays three times the same masked candidate probability. Public fixed HKDF remains the actual service in every compared execution. Candidate lengths, deterministic local checker work and concrete root/child reductions are supplied by the consuming resource and secrecy theorems.

The earlier ancestor list still comes from the source prefix; connecting it and the remaining checker length to one original selected-direction target across all source stages is an operational consumer, not a premise hidden in this local event comparison. No new primitive contract or implementation proof is added. All three actual guards use only the standard logical axioms.

### RawCtxCheckedParentSecrecy

The retained-parent reductions now consume the actual appended finite checker and its complete original value-freshness event. The target-free observer runs the same complete family continuation and checker on the same primitive interface, then tests the known checker values, earlier ancestors and original disclosure flag. Each tail carries its exact source reply type and dependent outside continuation, so a reached heterogeneous family Context can construct it directly. This type-bearing description is never sampled; the actual pre-draw context remains an ordinary sampled value.

`local_bound` consumes the concrete checked final-event comparison, paying three times its complete masked candidate probability. `actual_route` averages it over the entire context and independent full76 parent sampler on the real-child side. `random_route` does the same for an independent full76 child, retaining the actual delayed-coordinate experiment. Neither route conditions on the selected cut, excludes a cache hit or assumes an arbitrary reached state is uniform.

`actual_bound` charges real-child input recovery to the constructed full76 image tester: the bound is three times its Extract advantage, its ordinary two-query HMAC advantage and 2^-352. `random_bound` alone applies the independent-input q/2^256 bound. The real-child branch never receives an unsupported independent-guess interpretation.

`bound` proves the complete checked parent-to-child loss: one main Extract advantage plus one main HMAC advantage, plus three times the tester Extract advantage, tester HMAC advantage, 2^-352 and qCandidates/2^256. These are explicit reductions to the existing full-output contracts. Public fixed HKDF remains real in every source and masked private comparison. The sample is the exact supplied joint context/full-parent sampler; the concrete source prefix consumer must establish that sampler, retained table and source continuation rather than assume fresh uniformity.

`reduction_queries` gives two HMAC challenge queries for each constructed reduction and uniform cap (qSample+76)+qObserve. The real-input tester additionally makes at most qCandidates actual full fixed-HKDF evaluations. `challenger_queries` separately counts the real/uniform Extract key, PRF key/blocks and independent child draws: (qSample+76)+qObserve; (qSample+76)+(64+qObserve); 64+((qSample+76)+qObserve); (qSample+76)+(64+(64+qObserve)); and (qSample+76)+(76+qObserve), respectively. No cost is transported through a distribution equation.

These resource statements consume explicit sampler, observer and candidate caps. The concrete source and appended-checker ledgers must discharge them, including n+1 extra private derivations and local lookup/evaluation work. The actual cached-hit source normalization, initial half, original-direction lineage and final finite hybrid remain separate consuming work. This module does not claim the final evolving-chain theorem. All eight actual guards use the existing standard logical axioms; no new primitive assumption or implementation proof is introduced.

### RawCtxCursorLineage

These nine statements connect the actual selected cursor to a finite executable cache walk from its original initial chain input. walk_extends preserves a successful walk under additions that retain existing full responses. walk_shape gives its exact earlier-input length and a real cache binding for every recorded input. private_extends and private_lineage derive these facts from every supported original privateStep, including cache hits and arbitrary repeated values. A matching callback appends its actual input and next32 response; other calls retain the previous cursor path.

callback_state and logged_state lift the relation to complete actual pending callbacks and chronological logging, retaining all non-KDF shared effects. program_state and scan_state preserve it through every original adaptive continuation and state-dependent saved prefix. initial establishes the relation at depth zero without any table-content assumption. The cache is never enumerated, and no key-distinctness or uniformity is inferred.

This is cursor provenance, not a claim that cursor depth equals a successful record sequence. Source owner/control alignment and the final common selected-record event remain separate concrete consuming work.

### RawCtxFamilyPrivateRealization

The three checked statements connect the complete privately patched family interpreter to the actual candidate-instrumented comparison interface. `handler_patch` derives each original pending receive/send/public/read equation, including the owner-tagged optional reads, from the literal private-only patch. Its sole address-separation premise is the previously exposed parent/child collision condition, to be charged by the actual source input log. Public HKDF is always the original real function.

`observed_project` removes only the private candidate list and exposure bit after an arbitrary complete old-interface program; the result and all shared primitive state remain exact. `program_patch` composes those equations for any complete pending family program. In particular the original family, role controls and history are part of its result and are retained. No callback realization, source reachability, freshness equivalence or cryptographic premise is introduced. The later common-event consumer must append its lineage checker before any projection that removes private cache information.

### RawCtxFirstParentRisk

The nine statements charge the actual earliest matched-cache-hit branch of the complete original LIVE family execution. The private table is covered by its chronological list of executed inputs, including repeated hits. Clean means that the current selected cursor address is absent from that table; Valid additionally retains the original predecessor-depth invariant and a numerical bound k on that same list.

`uniform_inputs` derives the at-most-list-length over 2^256 probability for an independent 32-byte coordinate at the exact ratchet address encoding. Repetition in the list is allowed. `full_inputs` obtains precisely that coordinate from the actual full76 draw, by the checked joint distribution rather than an assumed fresh marginal. This is probability reasoning only and supplies no query-cost transport.

`valid_step` derives cache provenance, depth and actual list-length preservation from every supported original callback. `callback_risk` examines the original complete receive/send/private handler: unmatched inputs cannot overwrite the current address and do not advance it, while a matching callback starts at a missing current input and draws the original full76 at the active stage. The next input can hit only the previous recorded list or this just-executed input. Actual opening, sealing, public and optional read callbacks preserve the complete private store and have zero such risk. Every shared primitive effect and reply remains present.

`scan_risk` applies the independently checked adaptive scan induction to those concrete facts. `source_risk` supplies the original all-reply S+51R private-call cap directly from source syntax. `carried_risk` transports the same event through the literal executable forward sampler equality; it never invokes the analysis-only classical classifier. `cached_risk` uses the actual reached selected-address equation to show that every earliest matched cached pending branch is in that event. The resulting unconditioned bound is the sum, for 0 <= j < S+51R, of (k+j+1)/2^256. It retains early completion and all original hit continuations; cached responses are not treated as independent samples.

`empty_clean` supplies the initial absence fact for the actual empty private cache at every possible initial coordinate. Consumers starting from a nonempty cache must establish its displayed initial absence and coverage rather than omit it. The remaining original-event adjacent comparison consumes this source-derived collision term separately from the cryptographic child hop. This module proves no secrecy or final common-lineage theorem by itself.

### RawCtxForwardLiveCertificates

The actual forward LIVE compiler now certifies the exact Context it constructs and the executable scanner returns. Its proof-only Certificate records a residual source budget below the original budget, Fits for that same descriptor, and a joint inequality: savedKnownInputs.length + residualReads ≤ initialKnownInputs.length + originalReads. There is no replacement context selected from a frame equality.

certificate_mono carries this single allowance through earlier source work; certificate_fits gives the conservative original source budget for the same descriptor. program_certificate proves the certificate for every literal tag in the actual forward source syntax and every reply. It consumes the derived Server/Beacon family certificates, preserves full role updates and original history ticks, and counts each actual read when its optional value is appended. Its only resource premise is the original source client's all-reply Bounded certificate. carried_certificate transports the property through the actual executable tagged scan, using the tag it returned. first_certificate instantiates the original first-hit/predecessor sampler, covering both actual cache-hit and fresh pending branches without a freshness or miss premise.

checked_candidates derives the complete source-plus-checker candidate ledger from that exact certificate. With original source caps S sends, R raw receives, K public HKDF queries, E reads and checker length n, its bound is initialKnownInputs.length + earlierCandidates.length + 254 + S + 51R + K + E + (n+1). It retains duplicates and charges the pending completion reserve and every checker derivation. Prefix disclosures and residual reads share the same E; the source read budget is not charged twice. Existing CheckedBudgets.uniform consumes certificate_fits for the matching actual descriptor, giving U+64(S+R+H+1) uniform queries. The support-certified pending sampler can therefore derive these bounds for every inhabitant of its actual Context subtype, instead of assuming them for arbitrary fabricated Context values.

All six actual guarded statements pass with only the standard logical axioms. These operational resource results introduce no primitive security assumption, desired secrecy conclusion, frame injectivity, runtime support test or cost transport through an evaluated-distribution equality.

### RawCtxForwardOwnerCertificates

The actual owner compiler directly certifies its carried descriptors. receive_quiet preserves the original zero-query outside client through every remaining skipped-key derivation and opening reply. send_quiet preserves it through key derivation, seal and full advanced-state publication. program_zero proves a source program with zero calls constructs no descriptors, regardless of its arbitrary local return value. program_quiet uses the actual source bound of at most one request to derive these facts for every literal receive/send descriptor constructed by that request, under every reply. Public operations have no descriptor and every saved outside client has zero calls. No frame inverse, injectivity assumption, replacement witness or cryptographic premise appears.

### RawCtxForwardRoleCertificates

RawCtxForwardRoleCertificates proves resource certificates for the exact descriptors constructed by the forward source compiler. server_zero and family_zero show that an original zero-query continuation is a pure return and creates no descriptor. server_owner carries a certified owner through the actual peer installer and preserves its literal zero-query outside Server continuation. server_quiet discharges that owner's certificate from the original one-call source program, including malformed routing, absent peers, send and receive branches.

family_server invokes that proved Server certificate for the exact singleton request and retains its actual family index, whole returned Server and outside continuation. family_beacon applies the original owner certificate before its exact established-role installer; inactive phases run the same original rejection and continuation. family_quiet derives both certificates from one actual family source request, and keeps public requests untagged. Its only resource premise is the original client's syntactic one-call bound. No family-quiet premise, frame inversion, replacement descriptor, cryptographic hypothesis or source-state injectivity is assumed.

These certificates allow the full LIVE compiler to attach its residual source budget and saved-history bound to the actual carried Context, rather than replacing it by another descriptor whose frame happens to be equal. All seven actual guards pass with only the standard logical axioms.

### RawCtxForwardTags

All is a predicate over every literal descriptor at every node of the annotated source syntax and every possible reply. pure_all and query_all expose the exact source cases; bind_all retains certificates in both original work and full outside continuations. mono transports a proved descriptor implication. map_all and lift_all carry explicit tags through same-interface or LIVE-sum forwarding. scan_all proves that a supported executable scanner result has the certificate of the actual tag it returned. It uses the stored option and established coverage, with no inverse of a continuation, replacement existential witness or fallback tag. These are operational proof certificates, not cryptographic or resource assumptions.

### RawCtxFunctionalFamily

The actual private retained backend is compiled through the original native, receive and send adapters. Its private-response equation returns the exact full retained response without changing the shared state. Its opening, sealing, commitment and optional writer computations remain the original native programs; public HKDF continues to use the actual real source. No callback realization premise is supplied.

The first family equality carries both directional origin certificates on all represented kernels. The consuming Stored variant instead leaves arbitrary unselected native kernels opaque and annotates only selected initialized kernels. Both variants preserve the complete original adaptive role/read program, actual optional replies, every role and original timestamped history, and the same entire shared primitive state. Stored receive/send erasure recovers the literal original native callbacks.

The replay theorem consumes a supported actual mutable-table family execution. It uses exactly that execution's final retained private view, then derives a supported annotated execution with the same complete native result and shared state. This is support inclusion only. It is not a probability equality between mutable and fixed games, does not make the reached view uniform, and transports no query cost through support inclusion. The initial annotation is a source representation: selected initialized kernels receive their certificate from the actual constructor, while other kernels need no origin premise.

The last two statements show that every supported receive/send keeps the original selected origin label and keeps unselected owners unannotated, including failed and exhausted operations. Lifting this label preservation to the selected family owner and consuming the actual publication transcript are subsequent invariants needed for the common final event. No storage, reveal or public interface is changed. All ten actual dependency guards contain only the standard three Lean axioms.

### RawCtxFunctionalPositions

The original receive and send programs preserve both directional initial origins under any fixed private KDF interpreter. The proofs consume the existing material-position invariants after erasing only their analysis KDF log. Receive rejection and failed opening retain their original kernel behavior; exhausted sends and failed seals retain their actual source state behavior. Arbitrary opening/sealing effects and the complete shared state remain supported.

The successful-send theorem identifies the actual supported sealing call behind the original optional API reply. Its returned sequence equals the entry send counter plus one, and its actual seal input uses the initial directional material at returned sequence minus one. The proof derives success from the actual optional reply; it does not equate the hybrid cursor with a successful-record count.

Located kernels carry the same native kernel, both original directional roots and the checked relation. Their receive/send callbacks use the structural SupportedSample certificate on the original computation. Both erasure theorems recover the literal original program and shared state after removing only the certificate/origin annotation. No runtime support test, rejection, repeated sampling or inverse selection is performed. The constructor theorem derives the starting relation for the actual zero-counter kernel under any fixed private interpreter.

These six results supply source invariants for the final-table support replay. They do not assert a distribution or cost equality between a changing private table and a fixed source, and they do not turn arbitrary restored kernels into initialized kernels. Roots and proof annotations are private analysis data, not a public capability or storage change. Whole-family source transport and the common final record event are subsequent consumers. All six dependency guards contain only the standard Lean axioms.

### RawCtxPublishedRecords

The executable private transcript forwards the original LIVE client query, receives its original reply, records only a successful original send response, and continues the same adaptive client. Each entry is the original Server peer or Beacon owner and the sequence carried by its actual returned encrypted response. Rejected sends, failed seals, raw receive attempts, public operations and reads produce no publication entry. The arbitrary initial transcript parameter is retained literally so the actual first registration ciphertext can be supplied by its separately verified source builder. No proof here manufactures or certifies that supplied initial prefix.

Erasing the transcript recovers the literal original client. Interpreting this equation through any complete stateful source handler preserves its original result and entire final state. The track and target-gated clients retain exactly the original six structural all-reply source-budget coordinates. There are no additional cryptographic queries, although list construction and membership testing remain local computation.

The target wrapper returns the original Boolean decision conjoined with actual publication membership. The supported Trace relation retains each original typed request, its supported actual reply and complete intermediate state. track_trace derives this relation from the executed transcript and decomposes its final list into the explicit initial prefix plus the actual later publications. target_source derives a true original decision and the corresponding source trace whenever the target-gated execution returns true. Thus the gate does not inspect secret chain bytes, a hybrid cursor, an invented success flag or a checker-created target.

The target gate is suitable as the same original Bool client in every stage and common/pending branch. The corresponding source material-position relation and final lineage/freshness comparison are separate consuming proofs, not additional assumptions introduced here. The initial builder publication has its separate source cost and provenance. All six actual dependency guards contain only the standard three Lean axioms.

### RawCtxSelectiveReplay

The actual selective private-table execution can be replayed under the fixed view of its own final table for support reasoning. The complete theorem inducts through every adaptive typed request. An ordinary callback preserves the private table and retains its actual reply and shared state. A private callback records its actual complete response; every later callback preserves that binding. Its response is consequently exactly the final-view reply, so the same full original result and ambient state remain supported under that view.

The pending theorem consumes the literal enriched backend compiler, retaining original native opening, sealing, public services and optional reads. The logged theorem erases only the chronological instrumentation after deriving support in the actual unlogged program; the complete result and shared state are retained. All initial full cache responses are preserved.

These three statements are support inclusion, not probability equality or cost transport. The final reached table is not asserted uniform or independent. The fixed replay view is used only to prove source invariants about this same execution; it is not a substituted public HKDF oracle or a security reduction. Successful-record sequence alignment and the final target event remain consumers. All three actual dependency guards contain only propext, Classical.choice and Quot.sound.

### RawCtxStatefulScanRisk

RawCtxStatefulScanRisk proves a cumulative failure bound for the actual generic stateful prefix scanner. The scanner saves a selected query before executing it, and otherwise executes the original callback with its full reply and state. The single scan_risk theorem bounds the probability that the final reached state fails Clean by the sum of risk(k+j) for j below the original all-reply counted-query cap. The index k tracks only callbacks selected by the explicit counted predicate.

The proof assumes an operational Valid invariant on each supported callback result, and a one-callback Clean failure bound: counted callbacks cost risk(k), while uncounted callbacks cost zero. It does not assume a final collision probability, source-input freshness, or that the scan reaches a cut. Both a pure completion and a selected unexecuted query have zero failure risk from a clean starting state. Unselected counted callbacks reduce the remaining source cap by one and advance the index; uncounted callbacks keep both unchanged. The proof uses the ordinary bind failure bound on the actual adaptive callback distribution. No independence assumption on later choices or replies is needed, and the error sequence need not be monotone.

The protocol consumer must discharge Valid and each callback bound from the real private cache, cursor and chronological query log. This generic theorem alone does not establish a protocol collision probability. Its actual standard-three guarded axiom check passes with default elaboration options; no custom axiom or placeholder is used.

### RawCtxStoppedParentSecrecy

RawCtxStoppedParentSecrecy keeps completed source decisions and pending selected continuations in one ordinary sampled sum. A common Bool is returned unchanged in the native and target-free observers and has an empty candidate list. It is not replaced by rejection, false, a conditioned sampler or a synthetic pending tail. Pending branches run the existing exact checked family continuation. The original complete sampler still precedes the 76-byte predecessor response, and the random child game pays another 76-byte draw even for common branches.

local_bound derives the same coefficient-three freshness comparison for both branches; common branches have zero difference. actual_route and random_route average that pointwise relation over the unchanged sum sampler and full retained predecessor. actual_bound uses the separately constructed real-input recovery tester, with its ordinary Extract/HMAC advantages and 2^-352 full-output image term. random_bound uses the delayed coordinate bound on the same full candidate ledger. bound combines the actual native comparisons into main Extract + main HMAC + 3*(tester Extract + tester HMAC + 2^-352 + qCandidates/2^256). Public fixed HKDF is unchanged in every actual observer and tester.

observed_bound and candidates_bound lift concrete pending-observer resource certificates through the literal sum dispatch, with no cost for returning a completed bit beyond the already executed sampler. observer_bounds retains every observer sample in both constructed reductions. reduction_queries proves two HMAC challenge queries and qSample+76+qObserve uniform calls for each reduction, and explicitly bounds the tester's real full-HKDF evaluations by the candidate count. challenger_queries separately charges the Extract replacement key, HMAC random blocks and independent full child draw. Deterministic interpretation, table operations and private KDF calculations remain reduction runtime; they are not declared free.

The actual source stopped sampler, concrete pending certificate and common final-event linkage are consumers of this wrapper. Its generic all-context resource premises must be supplied by the derived source certificate (for example a certified sampled-context subtype); they are not asserted for arbitrary unrelated descriptors. All eleven actual guarded statements use only the standard logical axioms.

### RawCtxStoppedParentSource

The seven statements preserve the actual complete source continuation while resolving its forward first-parent cut into either the original already-computed Boolean decision or the original fresh pending Context and logged state. Complete and cached paths execute their real-stage continuation and the same final observer before the challenge; pending paths stop before their real full76 draw. No branch is conditioned away, retried or replaced by a fabricated false decision.

prepare_real and prepare_random are literal full-program equalities to the original real stage and collision-normalized random stage, respectively. pending_source retains the exact supported constructive forward sampler result and derives its cache miss. pending_origin additionally derives Covered, actual cursor match and the requested depth. pending_draw exposes the original full76 draw and unchanged whole source continuation. sum_run maps the same data to the common-Bool or pending-pair interface. prepare_uniform charges the entire original source bill U + 76(S + 51R) + 64(S + R + H), plus the actual final observer bound, even when common processing finishes before the challenge. It removes a literal suffix from prepare_real; it does not transfer costs from evaluated distribution equality.

The final observation remains explicit and is not asserted to be target-free here. Source-derived pending certificates and the common final record-lineage event still require their concrete consumers. No primitive security, cache separation, successful-record or uniform reached-state premise is added.

### RawCtxSupportedSample

The six statements attach proof certificates by structural recursion over the original finite OracleComp syntax. certify executes each original query and forwards every reply to the corresponding original continuation. A supplied property proof is used only to annotate the same returned value; it does not select, reject, retry or replace any value. erase and run recover the literal original program and its arbitrary continuation. query_bound preserves every selective source query budget by that exact syntax equation.

The common/pending specialization annotates a pending Context with its support proof in the original sampled sum, and leaves common Boolean decisions unchanged. sum_erase and sum_run recover the exact original sum and complete continuation; sum_bound preserves its query budget. The proof subtype lets a consuming source theorem derive resource guarantees for every Context inhabitant, without assuming resource bounds on arbitrary fabricated Contexts. There is no runtime support test or Classical.choose inversion.

## Full pending source and publication checkpoint

This topic checkpoint adds 27 modules and 130 guarded statements. The original accepted execution now has a single pending builder-and-post program before the first ciphertext, with exact typed marker removal at the production private-HKDF endpoint. Full post and first-builder descriptors retain the actual continuation at each derivation. The later-parent post interpretation keeps the old initializer service and maps its future returned kernels as known; it never reinterprets that old response with the new hidden parent target. Actual successful LIVE publications are tied to the installed sender and an already executed cache path. This remains a source-boundary checkpoint: the full legal masked observer, initializer-input alias ledger, installed-session origin, common freshness event, adjacent source bounds and aggregate reduction/query ledger remain active work.

### PqxdhInitialBuilderAmbient

`PqxdhInitialBuilderAmbient` proves that the source first-send builder runs identically inside the full shared/private/cache interpreter. It derives this from every concrete admission branch and the first-send, erase, serialization and publication sequence. The shared primitive state advances exactly as in the original builder, including failure branches, while the additional private identity state and root cache are retained. There is no marginal-distribution or arbitrary continuation premise. These program equations neither establish secrecy nor discard the original auxiliary callbacks or their work.

### PqxdhInitialBuilderContext

The two checked statements describe the exact first Server ciphertext boundary. `after_factor` factors the original publication code into its actual first send followed by erase, optional serialization and publication, including failed sends. `frame_address` shows that each concrete builder or post descriptor carries the original private KDF input. The descriptor stores the original full PostSpec client, complete frontend state, pending send and original public construction fields. Its stopped form receives only message material and represents the new next chain by a private label. These statements establish source grammar only; the native/label interpreter comparison, reveal masking, alias accounting and source resource bounds are separate obligations.

### PqxdhInitialBuilderPacking

`PqxdhInitialBuilderPacking` connects the source first-send builder to the same explicit pending interpreter and reversible whole-state packing as the later post schedule. The proof derives the primitive and auxiliary forwarding equations from the actual handler, lifts the full original builder, and checks reinstallation for every ordinary, failed or divergent Rust result. In particular, a failed builder still retains the shared primitive effects already performed; the private identity state and initializer cache remain in the interpreter. The theorem is an exact program equation for the source callbacks and full state. It assumes no arbitrary continuation equality and makes no secrecy or uncharged-work claim.

### PqxdhInitialForwardBuilder

The three checked statements cover the complete actual builder followed by the original post schedule. `program_erase` proves that removing annotations gives exactly the current pending builder and its original post continuation, retaining every reply and frontend field. `program_sound` proves every carried descriptor names that literal complete future program. `program_covered` proves every private derivation is tagged under every possible callback reply. Identity, allocation, preparation, plaintext allocation and binding checks remain before the first derivation; erase, serialization, publication and later selectors and Beacon finishes remain after it in source order. These are operational source and coverage results, with no uniform-input, freshness or secrecy premise. The supplied typed initial kernel is interpreted by the separate actual initializer source bridge; annotation itself provides no cryptographic reduction.

### PqxdhInitialForwardPost

PqxdhInitialForwardPost constructs source descriptors before private derivations in the complete original post schedule. plain_erase retains each untagged callback. finish_erase preserves the actual complete preparation, optional initializer, application getter, first raw receive, exact sequence-one and binding checks, failed publication and inactive history tick. program_query follows the actual next source request. program_erase proves that removing annotations yields exactly PendingPost.compiler for the whole adaptive original PostSpec client. program_sound derives that each carried descriptor names its literal complete remaining continuation, including every later selector or Beacon finish. program_covered derives annotation coverage at every private receive/send derivation under every possible reply, while explicit non-derivation callbacks remain untagged. These laws use the previously checked literal owner and LIVE source compilers and retain complete state; they neither select a descriptor by testing function equality nor assume a reached compatible continuation. The subsequent source sampler, native-to-label interpretation, new initializer reply candidates, freshness proxy, cryptographic losses and resource bounds remain consuming obligations.

### PqxdhInitialParentContext

The five checked statements connect the actual full post source frame to its material-only stopped form. `finish_map` preserves the original first-receive registration checks, optional application result, Beacon installation and history tick under the complete kernel map. `native_primitive` and `label_primitive` identify the exact pending-owner source callbacks inside the full post service. `frame_cut` consumes the concrete record or finish descriptor: its original full76 reply resumes the complete native receive/send, performs the same source publication, and runs the same original full PostSpec continuation. The right-hand stopped program receives message material only; the new chain is a private label and every saved native kernel is represented as known. `frame_run` explicitly retains all shared primitive state, private interpreter state and initializer cache at the evaluated distribution.

This result extends the earlier LIVE-only context equation to the real full post schedule with selectors and later Beacon initialization attempts. The previous initializer response is kept as part of the old service and is not confused with the newly selected parent output. There is no supplied continuation equality or freshness assumption. External callbacks remain explicit parameters that actual source services must instantiate with their costs; this operational theorem does not treat them as free. The comparison uses native optional read values and precedes the legal masked-reader and candidate-accounting layer. Uniform-input secrecy and small alias probabilities are not conclusions of this module.

### PqxdhInitialParentPost

This module establishes a later-parent operational comparison for the complete original post schedule, retaining its full shared primitive state, private identity state and initializer cache. A previous selected initializer half is not reinterpreted as the new selected next-chain value. The original initializer service is shared on both sides; the label execution maps every optional returned native kernel to known labels. Future returned chain values must therefore be recorded as candidates by the consuming alias ledger.

`known_front` recovers every saved pre-draw role, peer, control, consumed list and live history exactly. `install_map` shows a Beacon finish installs the same updated role and advances the same history. `native_live` and `label_live` identify the explicit entire LIVE service inside the larger post interface with the same complete ambient lift. `step` derives representation equality for each original record, selector or Beacon finish, including all optional initializer and receive failures. `program` lifts those derived equations through the complete adaptive PostSpec client.

There is no continuation compatibility, freshness or secrecy premise. The retained-parent primitive receive/send equations discharge the source mapping, and all external callbacks remain explicit typed services with their entire effects. The initializer, preparation, application, selector and auxiliary services in this generic operational theorem are parameters to be instantiated by the actual current source services; their resource costs are not asserted free. The label reader in this comparison still interprets native hidden reads. A legal cryptographic observer must use the separately checked masking and candidate construction. This module itself asserts no target independence, small alias probability or endpoint security bound.

### PqxdhInitialPendingAccepted

`PqxdhInitialPendingAccepted` compiles the actual accepted authenticated-root execution into a single explicit pending program before the Server first send. It starts with the exact source-derived pre-draw protocol and private identity state, runs the original consumed-registration builder, and continues with the original post client selected by the builder response. The full initializer cache remains shared across both parts. The equations are proved by the concrete builder packing and post interpreter results; there is no arbitrary established-state or continuation-simulation premise. This is the initial-half retained-table representation used by the source bridge. A later parent cut must retain the original initializer response separately from its newly hidden child; the legal stopped-source comparison, freshness event and statistical/query bounds remain separate obligations.

### PqxdhInitialPendingAmbient

`PqxdhInitialPendingAmbient` proves that the complete explicit pending post program executes in the same shared primitive state, private identity state and initializer cache as the original post scheduler. Every record, live reveal, selector and Beacon finish keeps its original optional reply, source order and full state. The whole-client equation uses the concrete pending compiler and a reversible state packing; it does not assume an arbitrary continuation equality. This is an operational interpreter equation. The mathematical native reader still needs the separately checked masked-read and freshness comparison before it is a legal hidden-input reduction; neither secrecy nor a query budget follows from this equation alone.

### PqxdhInitialPendingBuilder

PqxdhInitialPendingBuilder emits the actual complete Server registration builder through the same explicit pending interface used by the full post schedule. after_interpretation preserves the complete first-send, erase, serialization and peer publication. candidate_interpretation preserves identity validation, peer reservation, arbitrary typed initial kernel success or Rust error, application length and allocation checks, key binding and first-send source order. ready_interpretation also retains current peer occupancy, allocation control and every preparation branch. build_interpretation adds the actual consumed-registration update, current selected Server and whole frontend reinstallation under the same interpreter. root_unused proves literal non-use of Ready.root after the typed kernel has been supplied. Every ambient callback effect stays in the interpreter; no copied shared state, arbitrary source compatibility or established-state distribution premise is supplied. The source initializer, actual current interpreter packing, cryptographic games, callback bills and target-free continuation still require their explicit consuming results.

### PqxdhInitialPendingCurrent

`PqxdhInitialPendingCurrent` instantiates the complete pending post interpreter with the actual retained-parent receive/send callbacks, original public backend, native live reader, current preparation and application getters, shared initializer service and private identity/CCA selector. Public HKDF remains the real fixed source. The selector is proved equal to a definition with no selected-chain argument. The whole original adaptive schedule has exactly the same replies and complete frontend, shared state, private identity state and initializer cache. No send, receive or continuation simulation equality is supplied as a premise. This remains an operational source equation: the native reader and selected private response still contain the mathematical target, so the legal hidden-input reduction requires the separate stopped-source and freshness comparison; no secrecy bound or free-work claim is made here.

### PqxdhInitialPendingPost

PqxdhInitialPendingPost exposes the original complete post-registration schedule as typed source queries. The full frontend retains every role kernel, registration control, consumed identifier and original disclosure history. Shared primitive state, private identity state and the root cache remain in the chosen interpreter rather than being duplicated in query state. The explicit interface includes enriched pending receive and send requests, actual optional family reads, original Beacon preparation, application getters, optional kernel initialization, selector queries and registration auxiliary requests. after_interpretation commutes interpretation through the original application and first raw receive. tail_interpretation retains the initializer before that receive. owner_interpretation retains all original preparation, inactive, rejection, sequence-one, prefix and publication branches. step_interpretation proves the literal full record, selector or finish compilation against those interpreted source calls. program_interpretation retains the entire original adaptive PostSpec continuation after every reply. All five laws hold for any lawful interpreter monad, so complete shared and private effects are preserved; there is no supplied compatibility, freshness or distribution premise. These laws alone do not assert that the native reader is a legal cryptographic observer, that selected input is secret, or that costs are free. Actual current-source specialization, stopped source descriptors, masked reads, explicit alias terms and resource caps remain consuming obligations.

### PqxdhInitialPostContext

PqxdhInitialPostContext stores the exact original PostSpec continuation around either a singleton original LIVE operation or a staged Beacon initial raw receive. It retains every saved pre-draw family field, control, consumed identifier, original pending owner context, candidate and publication branch. The material-only stopped program maps saved kernels as known, introduces the hidden chain only in the existing checked pending resume, and then compiles the same full outside post client. frame_address proves that its descriptor address is precisely the pending source request. This module supplies source data and operational definitions; reached provenance is derived by ForwardPost, not assumed. No arbitrary function on a hidden target, freshness premise, cryptographic independence or free resource claim is introduced.

### PqxdhInitialPostPacking

The full current protocol state is split into Front (complete roles, controls and consumed bindings) and one ambient pair (shared primitives and private identity state). pack_unpack and unpack_pack prove this field rearrangement is reversible. step checks every original record, selector and attempted finish against this representation, preserving the exact installation and history tick. schedule lifts the concrete per-query identity to the entire original adaptive PostSpec client. These equations preserve the full returned state and do not assume equal callback behavior, secrecy or marginal generator distributions. The remaining concrete source instantiation supplies the actual live handler, private selector and whole owner. Rearranging fields changes no primitive queries; local state construction/copying is still ordinary explicitly charged reduction work.

### PqxdhInitialSentinelAccepted

The four theorems close the typed initializer marker boundary through the actual accepted source. build_marker removes it from the complete original Server builder for any initializer result, including failure and complete reinstallation. accepted_marker joins that builder to every original adaptive post request in the same shared/private/root-cache interpreter. actual identifies the unmarked prior lookup with the single pending builder-and-post program before the first ciphertext. production instantiates that lookup with the fixed source HKDF and the current authenticated initializer observer. Both initial halves remain projections of the same supplied64 response. These operational equations retain native reveal interpretation; legal masked readers, source session-origin freshness and cryptographic hybrids are separate consumers. No equality for arbitrary untyped requests, free ambient work or standalone secrecy is claimed.

### PqxdhInitialSentinelBeacon

The three theorems remove the initializer analysis marker through the actual typed Beacon first receive. The raw interpreter is the original native callback lifted without changing shared, private identity or initializer cache state. The complete receive ignores the marker because its actual ratchet requests use the ratchet domain. The whole fused owner then retains identical preparation, optional initializer, application response, parser rejection, opening and publication, including inactive phases. No equality is asserted for arbitrary untyped KDF requests, and this operational equation alone is not a secrecy result.

### PqxdhInitialSentinelPost

The two theorems remove the initializer analysis marker through the complete original adaptive post scheduler. The Beacon owner law retains preparation, first receive, optional initializer, application response and publication in the shared/private/root-cache interpreter. The program law combines this with typed records and leaves the identity/CCA selector unchanged. This includes every post request and its actual optional reply. It assumes neither an established initial family nor arbitrary untyped KDF equality; it is an operational source equation, not a cryptographic bound.

### PqxdhInitialSentinelRecords

`PqxdhInitialSentinelRecords` removes the initializer analysis marker from every original record, public operation and live reveal. It first proves that public HKDF, public hashes and uniform calls are independent of the private KDF substitution. It then derives equality of the complete private receive/send callbacks from the actual typed pending interface and propagates that equality through the full native record frontend. All optional replies, source roles, controls, consumed registrations, history and shared state survive. It makes no claim about arbitrary raw KDF requests having a ratchet domain label. This is an exact operational equality, with no new security or query-cost assumption.

### RawCtxFamilyOriginLabels

RawCtxFamilyOriginLabels proves that the original established-family record interface preserves every installed owner origin label when its actual receive/send callbacks preserve that label. raw preserves labels through empty, malformed, wrong-pin and valid raw paths; send covers empty rejection and advanced optional seals; owner combines the two original requests. server_raw retains header routing, associated-data lookup, missing-peer rejection and same-peer publication for every other peer too; server_send does the same for sends, and server combines them. beacon covers all inactive phases and complete established-owner reinstallation. family preserves each selected owner at its original index across Server, Beacon and arbitrary public callbacks. live additionally retains original optional disclosures and source history updates. schedule derives the same equation for every supported final result of an arbitrary original adaptive LIVE client, retaining the whole reply, family, history and shared poststate. The callback hypotheses concern actual supported complete callback outcomes and are discharged by the concrete FunctionalFamily origin proofs; no final whole-protocol invariant is assumed. The interface has no installation operation, so the initial installed origin is an explicit source constructor obligation rather than inferred from an adversarial field. These are operational provenance statements only and introduce no security assumption, fresh-key distribution or query bound.

### RawCtxFamilyStateInvariant

The original no-install family frontend preserves a kernel predicate indexed by its actual shared state. Rules require the real callback state relation to be reflexive and transitive, the predicate to be monotone as shared state grows, and every supported receive/send to extend that state and preserve the active kernel predicate. Public and live-reader callbacks separately retain the state relation. raw, send and owner cover original admission and optional publication; server_raw, server_send and server retain every selected or untouched peer; beacon keeps established and inactive phases; family and live preserve original indices and full optional read history; schedule composes the exact adaptive source support. Unselected owners keep their predicate by monotonicity, rather than by assuming their private cache is unchanged. These are generic operational support contracts, to be discharged from the actual source interpreter. They establish neither probability equality, cryptographic secrecy, installation provenance nor query costs.

### RawCtxPublishedKernel

The four operational statements link an actual successful original send reply to the kernel installed by that same source step. The owner statement retains empty-input rejection and the actual optional callback result. The Server statement keeps identity-derived associated-data lookup, exact peer selection and same-peer installation. The Beacon statement excludes every inactive phase and retains the actual established owner. The LIVE statement uses the original publication transcript, so its owner and sequence come from the public reply actually returned to the client.

The sole generic callback premise states that a supported successful send returns the installed kernel’s sequence. RawCtxSourcePathCalls.published_call proves this for the actual selective-table source interpreter; the source publication-path consumer applies it directly. This module neither treats an internal derivation as a publication nor claims security, initialization provenance, full PostSpec installation behavior or a query-cost transfer.

### RawCtxPublishedLineage

The final source observation is one fixed event for every selective stage: the original publication-gated decision remains true and the full initial-root lineage through the selected record material is disjoint from the original final reveal history and supplied earlier disclosures. The lineage uses each execution's final private-table view. A cursor is never substituted for a successful-send sequence.

The nine statements identify this event, decode its exact full-response next chain, split it at an actual retained cache walk, transport that split through all later cache extensions, identify the retained-parent checker step, preserve exact value freshness under the split, and identify the original source-position model and selected material key. Its pure probability observation makes no uniform calls; the finite KDF evaluations and list work remain local computation, and the ordinary primitive observer separately pays the existing finite-checker query bill.

The actual cache-walk premise is supplied by the source prefix invariant, not a uniformity or separation assumption. Complete published-target reach, compatibility of the cache-erased resumed computation with this final event, the whole builder/finish source compiler and the final ordered security bound remain composition obligations. No source-event equality or primitive assumption is supplied here.

### RawCtxReceiveSendFields

The original receive driver preserves the exact sending chain and sender sequence for every supported execution under arbitrary stateful callback replies. resume_good uses the actual future-opening validation check; begin_good derives cached-opening compatibility from the real cached preparation and control operation. finish_fields covers cached and future publication, defensive rejection, and failed opening. program_fields follows every original finite receive step, including staged skips and malformed represented initial kernels. receive_fields discharges the phase predicate from the real admission step. No fixed KDF interpreter, callback preservation premise, successful authentication, material provenance or cryptographic assumption is supplied. Callback states and optional replies remain arbitrary; the result only constrains the two sender fields. The source-cache extension and final successful-publication path are separate consuming source invariants.

### RawCtxSourceFamilyPath

The three theorems derive sender-path preservation for the actual selective-table family interpreter. The step theorem consumes concrete source receive/send support laws, real public callback cache extension, and the actual pure optional reader. The schedule theorem covers the entire adaptive LIVE source client with complete role maps, optional replies, history, shared state, cache and cursor. The source theorem transports this through the existing exact native family equation, retaining the same final private cache.

The initial premise says that an installed selected sender is already at the end of an actual cached path from the specified root. It is an initializer or prefix obligation, not a supplied callback preservation assumption. This LIVE interface has no installation operation; full PostSpec finishes and the actual first builder must be connected separately. The theorem does not turn a source counter into a publication, infer secrecy from support, or transport query costs through distribution equality.

### RawCtxSourcePathCalls

The concrete callbacks used by the original generic family retain every existing private cache binding. native_extends follows the actual selective interpreter and uses only its support-level cache-extension fact; it transfers neither probability nor cost. receive_path combines that extension with the original sender-field preservation. receive_call and send_call instantiate the actual refined-kernel native adapters, retaining complete optional replies and shared/table/cursor state, and propagate any already established directional cache path. send_call includes failed seals. published_call identifies each actual successful ciphertext reply sequence with its same advanced kernel counter. public_extends applies to the actual real public interpreter, without replacing public HKDF by the private retained table. The full family publication-path invariant and its original initializer provenance remain consuming obligations.

### RawCtxSourcePublishedPath

The six statements establish actual publication provenance for the original no-install LIVE family. Every successful selected send reply is tied to its installed kernel by RawCtxPublishedKernel.live, whose callback law is discharged by RawCtxSourcePathCalls.published_call. The actual source path invariant then gives a cached walk from the initialized root through that returned sequence. Induction over the original supported publication transcript retains all such paths through subsequent cache extension, failed operations, other owners and reads. The final target-gate theorem retains the original Boolean decision and successful-publication membership; the native source theorem uses the exact complete source-family equation.

A positive-sequence cached walk contains the actual full response at the last derivation input. The final checker cannot fill a missing target derivation. The root initialization path and any initial publication prefix remain explicit source-prefix obligations. Full PostSpec finishes, actual installation/session origin and adaptive target-selection loss require their consuming proof: a fixed Owner index alone does not identify the selected root when a previously inactive Beacon later initializes. No secrecy or query-cost claim is inferred from these support statements.

### RawCtxSourceSendPath

The actual original send uses the selective private KDF handler with its entire SharedState, private table and cursor. The private_call equation retains the exact full76 response and actual hit or miss update. The original source adapter forwards that request exactly once. All native sealing, commitment and optional writer effects remain present; seal_store proves only that they leave the private table and cursor unchanged.

Path links the original sender counter and current chain to a finite walk through actual cached bindings from its original initial32 value. Every earlier binding survives a send. Exhaustion preserves the old path, while any admitted send extends it by its actual full response before sealing, even if sealing fails. The constructor theorem starts at the actual zero-counter source kernel and allows arbitrary preexisting private cache contents. No empty-cache or perfect-correctness assumption is inserted.

The reply equations derive the sequence from the actual optional seal result. Every successful source send therefore leaves a complete cached path through its returned sequence. This is a per-call theorem with an explicit incoming Path invariant; complete receive and family propagation, actual initialized-prefix provenance and consumption by the common final published-record observation remain subsequent source invariants. No source success, uniform-input, byte-injectivity, callback compatibility or cryptographic-security premise is supplied. Local parsing, list work and private computation are not declared free.

## Full source origin and stopped observer checkpoint

This checkpoint adds 34 modules and 219 guarded statements. The executable full-source predecessor sampler retains each original descriptor, continuation, private table, cursor, chronological log, shared primitive state, identity state, root cache and installation/publication trace. Both adjacent stages have the same complete prefix. Selected cached hits are charged separately; a selected miss executes its actual full76 draw. The ordinary stopped observer retains the original full post client and an explicitly counted finite lineage checker. Initializer input and both returned chains appear in its alias ledger. Actual first Server publication and successful matching Beacon installation supply source paths; the complete adaptive post client preserves them. These results still require a common source freshness event and concrete adjacent realization before the total evolving-chain theorem.

### PqxdhInitialBuilderCertificates

The three statements extend the concrete post certificate across the actual first Server builder. The initial descriptor is attached only at its original private send, after identity, peer allocation, application and binding gates, and retains the original bounded outside post client. Every later descriptor comes from the actual full post compiler and retains its quiet in-progress completion plus original remaining post allowance. program_fits establishes this for all source branches, including Rust failure/divergence, failed sealing, erasure and serialization. carried_fits gives the certificate for the exact descriptor returned by the executable full scan.

program_total derives the same7+67*qPost all-reply callback bound for the annotated source by literal annotation erasure, not distributional equality. Each descriptor is charged to its actual source query. These callback bounds do not assign zero time to constructing, retaining or inspecting finite saved state and do not hide primitive or ambient costs. The first-builder and post stopped-completion ledgers and origin-transcript extension consume these certificates separately.

### PqxdhInitialCurrentRootRetention

These four statements consume the exact current LegalObserver.sample. The private retained game keeps its previously drawn root alongside the original decision; erasure is syntactic equality to CurrentSecrecy.random, including completed source modes. The complete directional split law retains actual preparation and previous root before drawing the independent initial halves, and it quantifies over the entire continuation. The first-child serialized sampler is therefore uniform only in its omitted selected half, independently of the retained previous root and opposite half. Its syntactic retained-query bill is the same source-derived qSample+64+qObserver, with no extra random query. This retained-root context is used after the initializer comparison; it is not substituted into the earlier root-free Extract observer. It neither proves source adjacency of later chain games nor transports costs through a marginal distribution.

### PqxdhInitialFinishOrigin

The original Beacon finish is instrumented with a private optional marker computed from its actual prepared initializer Secrets. The original public result remains unchanged. Failed preparation, initializer failure, unsuccessful receive/authentication and inactive phases produce no installation marker. The marker appears exactly when the same source finish returns its successful application reply.

The erase theorem gives literal program equality for an arbitrary lawful monad. The kernel-map theorem preserves the marker while applying the existing exact receive and initializer interpretation equations. The origin theorem derives the actual supported preparation and complete first-receive tail that installed the returned state, including the same ambient states before and after that tail. A source instance can use the real initializer request coordinate or its equality-to-selected-coordinate Boolean as the marker; an Owner index is never substituted for this provenance. No target bytes need be included in the marker. The full post transcript, actual root-message marker instantiation, Server installation and final secrecy event remain consuming steps.

### PqxdhInitialFinishOriginLog

The four statements place the initializer-origin marker in explicit private state at the actual initializer callback, before the first receive can reach a selected KDF cut. Every preparation, application and ratchet callback lifts past that marker. `tail_logged` proves that the complete optional first-receive tail preserves the newly written marker. Initialization failure also writes the attempted marker, but it cannot publish an installation. `owner_logged` filters the saved marker by the actual successful finish reply and gives exactly the previously checked successful-installation transcript, for arbitrary old marker state. Inactive phases and failed preparation therefore cannot publish a stale marker.

`owner_erase` is exact program equality with the original complete finish, not merely equality after evaluating probability. `owner_query_bound` consequently preserves every syntactic oracle-class budget on all replies; the bookkeeping adds no oracle calls. This is not a claim that its local execution takes no time. The extra field can be retained in the existing private ambient state across a full post or first-builder cut, without reconstructing the earlier Secrets from a saved continuation. The marker function is still generic here: the actual selected-message equality and per-owner installation/publication transcript are separate concrete consumers. No origin, secrecy, freshness or successful-installation premise is added.

### PqxdhInitialNativeAudit

This source audit appends an ordinary chronological list beside the complete original NativeLog state. It retains the shared primitive state, selective table/cursor, executed private-input list, private identity state and root cache. Actual private receive/send inputs, public HKDF inputs, and disclosed native optional read values enter the list. An actual initializer runs once, retains every original effect, returns the same optional kernel, and logs its privately audited root plus both returned chains. No cache is enumerated; initializer aliases are candidates rather than authorized-disclosure flags.

read_length and live_length derive at most one candidate for each original private/public/read callback. query_erase and program_erase remove only the added audit and recover the exact original callback and entire adaptive program with the same full state. step_audit and program_audit show every supported run retains its whole starting list and appends at most three values per attempted query, including failures/repetition. read_step returns the exact native optional reply, leaves every original interpreter field unchanged, and appends precisely that reply's disclosed bytes. query_uniform preserves the actual syntactic uniform-query bill; it uses an oracle-program equality and map invariance, not equality of evaluated distributions. read_known_note identifies the same append with the original timestamped source disclosure history.

These are operational and resource statements. Actual pre-cut context selection, chronological-prefix query bounds, initial disclosure inclusion and the final secrecy/freshness comparison remain consuming source obligations. No target input or new primitive assumption is supplied to an ordinary observer.

### PqxdhInitialNativeCarried

The executable sampler scans the actual consumed-registration builder and its entire adaptive post client. It emits the literal source descriptor before its private callback, preserving the complete private table, cursor, chronological inputs, shared primitives, identity state, root cache and installation/publication trace. Both adjacent stages have the same annotated sampler, proved by complete callback equality and the actual unselected-callback depth invariant. This does not infer equality of saved descriptors from their non-injective packed representations. Packing and finishing recover the original complete source execution. Every supported descriptor has its own original remaining-work certificate and source occurrence; its table is covered by actual prior inputs. The selected branch is explicitly either a recorded cached hit or a matched miss at the requested depth. Only that actual miss draws the one full76-byte predecessor with its exact original response and state update. Cached hits still require their separately derived collision charge. No source freshness event or final secrecy conclusion is assumed by these operational results.

### PqxdhInitialNativeInitializer

The concrete later-chain initializer uses the original classification of the actual prepared secrets and the same retained root cache. A matching selected request returns the earlier selected root and supplied64 response; every other request keeps the original real initializer. It returns the actual normalized Beacon kernel while retaining shared and private identity state. The checked source constructor starts at send counter zero and has the established positional relation. Removing only the private root audit recovers the original labelled response service over the complete evaluated state and cache. Every supported reply carries its exact source kernel, and the service uses at most32 uniform-byte calls for a root-cache miss. The previous root and response are retained only after the earlier initializer comparison, before the later parent draw; this service never receives the new hidden chain. Deterministic constructor, lookup and copy work is not declared free by its uniform bound.

### PqxdhInitialNativeLog

The full pending source interpreter retains the shared primitive state, selective private table and cursor, chronological executed-input log, private identity state and root cache. Every LIVE callback is exactly the existing logged selective interpreter with the two additional state components retained. Every external preparation, application, initializer, selector or publication callback runs its original complete ambient computation while preserving the separate selective store and input log. Erasing only the list gives exactly the full unlogged execution. An initially empty table is covered by the input history, and every supported callback, complete execution and stopped prefix preserves this provenance. These operational equations do not assert freshness or a random input distribution; the concrete external services and source scan must still be instantiated by the secrecy consumer.

### PqxdhInitialNativePath

Every actual callback of the full pending interface preserves earlier private cache bindings. The proof retains the complete chronological log, selective cursor, shared primitive state, identity state and root cache. A whole record or owner primitive program projects to exactly the original selective family interpreter. This is an operational equality justified by the literal lifting of that same source computation, and is not used to transport resource counts. A supported record reply then consumes the checked actual send-path and publication theorems: the initialized sender path is preserved, and an actual successful published target already has its entire path in the private cache. A complete first raw receive likewise preserves its initialized send path through every malformed, rejected, failed-opening or successful outcome. The input path remains an explicit invariant to be established from the actual selected initial64 response and threaded by the whole origin-aware Post consumer. No final checker is allowed to manufacture a missing published derivation, and no source uniformity or final secrecy claim is introduced.

### PqxdhInitialNativePrefix

The original first-hit/predecessor selector now runs over the full source callback interface. Preparation, application, initialization, external selector and publication callbacks retain the independent selective table and cursor. Before the requested predecessor depth, both adjacent table stages execute exactly the same callback computation over the entire state. The actual unselected callbacks preserve that depth invariant, so the complete adjacent source prefixes are equal. A supported selected address is either an earlier logged cache hit or a matched miss at the requested depth; the theorem never assumes every selection is a miss. Finishing the retained dependent callback and continuation recovers the same original full execution. The cached-hit branch still requires its explicit collision charge in the secrecy consumer.

### PqxdhInitialNativeResponse

Every full original builder/post descriptor executes exactly its selected private-step callback, including first Server send, ordinary record and Beacon first receive. The reply is the original decoded full76 response, and the entire selective table/cursor, shared state, private identity state and root cache are retained. The input is appended to the chronological list after the callback. A cache hit reuses its response without a draw. A matched miss before the selected stage draws one full76 value and updates that same original state. The origin-aware descriptor has the identical callback and draw while retaining its actual metadata. The miss, matching and depth conditions are explicit here and must be derived from the concrete source scan; this component does not postulate unconditional uniformity.

### PqxdhInitialNativeRisk

The complete source scanner now has a derived cache-hit bound. Its original chronological log covers every previously stored private input; unselected callbacks preserve that provenance, the predecessor depth and the input count. External preparation, application, initialization, selector and publication effects preserve the separate selective table and cursor, so they add zero collision probability at this boundary. An actual private callback uses the existing full76-byte next-coordinate calculation and charges at most (k+1)/2^256 after k earlier inputs. The same adaptive scan therefore pays the sum of (k+j+1)/2^256 for j from zero through 7+67 qPost minus one, using the complete original builder/post syntax bound conservatively for private calls. Packing the actual descriptor sampler preserves this event. Its earliest cached predecessor is bounded by that sum, with no assumption that the selected request misses and no resampling of cached responses. An empty private table is proved clean for every initial coordinate. These are chronological collision terms, not a public-HKDF/random-table security claim; the common source decision and cryptographic child comparison still consume them separately.

### PqxdhInitialOriginBuilderPath

The eight statements connect the original Server first builder to the actual selective private cache under `PqxdhInitialNativeLog.handler`. The interpreter retains the original shared primitive state, private identity state, root cache, selective cache/cursor and chronological input list. Auxiliary callbacks may have arbitrary original ambient effects; the proof uses their established inability to overwrite the separate private cache.

- `send_path` projects the same supported logged send to the actual mutable private backend and consumes `RawCtxSourcePathCalls.send_call`. The sender path survives even a failed seal, retaining the already advanced state.
- `after_path` follows the actual first-send, erase and serialization order. A successful response publishes precisely the advanced sender kernel. Prior cache bindings survive the original erase and write callbacks, so its directional path remains available at the final state.
- `candidate_path` retains the original identity, reservation, plaintext allocation, length, binding and Rust gates. Every successful candidate reaches the same publication tail. Its explicit reusable premise is the supplied initial kernel's zero-position path under any existing cache; the concrete constructor later discharges it.
- `ready_path` adds the original current-key allocation, occupied-peer test and Ready preparation. Rejected or Rust failure branches cannot produce the assumed successful publication.
- `build_path` adds actual consumed-registration handling and final Server peer installation. The path belongs to the peer at the exact returned key ID in the same full supported source result.
- `supplied_path` derives send counter zero from `PqxdhInitialSuppliedPositions.pair_refines` for the actual `kernelOf false supplied64` constructor. It starts the path at that returned Server kernel's own send half under every prior table, with no entropy or distinctness premise.
- `supplied_build` supplies `ConcreteRatchetKernel.refined <$> kernelOf false supplied64` to the original builder and discharges its initial path premise. The remaining initializer equality identifies the actual Rust constructor result rather than assuming a path or backend compatibility.
- `recorded_cached` consumes the original `OriginPost.afterBuilder` recording rule. Every newly recorded publication has an already executed directional path in the final private cache, even when the outer statement quantifies over all original optional/Rust outcomes. Existing trace entries are deliberately handled by the enclosing trace invariant, not claimed by this new-publication statement.

The publication recorder uses the installed peer's actual send counter, and the cached witness is derived from that same kernel. No final checker constructs this path. No distribution equality transports support costs; these are operational support statements, with no probability, security, query-bound, snapshot or persistence claim. The complete eight guarded declarations use only `propext`, `Classical.choice` and `Quot.sound`; no placeholder or new axiom is introduced.

### PqxdhInitialOriginCertificates

The origin-aware first server builder and complete post-registration client carry source-derived continuation certificates at every private derivation. The proof follows every actual admission, allocation, receive, sealing, publication and failure branch. Each saved descriptor retains the original full continuation and the current installation/publication trace. Its resource certificate follows from the literal source syntax, including every external callback, rather than an assumed same-frame replacement. The whole first-builder plus post client uses at most 7 + 67 qPost source callbacks. The executable carried scanner returns only descriptors satisfying these certificates. These are operational source and query bounds; computational callback costs and secrecy still require the concrete interpreter and reduction consumer.

### PqxdhInitialOriginContext

The source descriptor keeps its exact original record, Beacon-finish or first-builder context, the complete private origin/publication trace, and an optional origin computed before the selected derivation. Actual forward construction will use the prepared initializer marker for a finish and the original installed-session marker for the first builder; record contexts need no marker. The total definitions also retain a missing marker without manufacturing an origin. No proof metadata or continuation inverse is used to construct these fields.

The resumed source and the material-only stopped source both finish the actual pending operation, update the private transcript and continue the same original outside PostSpec client through OriginPost.compiler. A Beacon origin is installed only after the real optional successful finish reply. The first builder retains its original erase, serialization, reinstall and successful peer lookup, then records the actual installed kernel counter. `complete_erase`, `resume_erase` and `stopped_erase` remove only the transcript fields and recover the exact original source programs. `frame_address` retains the same typed pending query. `stopped_query_bound` preserves every syntactic callback-class bound for every reply.

These statements do not infer the trace or marker of a reached source cut from mere frame equality. Actual forward annotation must carry those fields and prove its full continuation equation. The concrete native-to-label equality of the new stopped continuation follows separately using OriginPostMap. No final event equality, freshness condition, source-prefix provenance or secrecy bound is assumed or concluded here.

### PqxdhInitialOriginFinishPath

The actual later initializer is installed only at the existing External initializer branch; every other external callback is unchanged. A true marker identifies the complete selected initializer coordinate and returns exactly the previous selected root and supplied64 response, with every NativeLog state field retained. That actual source kernel starts at send counter zero, so its initial directional path exists under any prior private cache. The complete original first receive preserves this path through application retrieval, decoding, raw receive, authentication, binding checks and publication. A true marker on a supported successful finish therefore provides the exact installed kernel and its selected-session send path. An unmarked finish cannot replace an installed kernel: any remaining kernel is the original inactive-session kernel. These facts distinguish real installation provenance from an owner index and are operational source obligations for the whole publication/freshness consumer, not a secrecy or uniformity claim. Earlier input/output alias events and complete reveal freshness remain charged by that consumer.

### PqxdhInitialOriginForwardBuilder

The source compiler begins before the actual Server builder consumes registration state and before its first ciphertext. Every original admission, allocation, malformed binding, Rust failure, optional seal, erase, serialization and publication branch remains present. At the actual first derivation it carries the same original builder descriptor, current full trace and supplied installation-origin marker; after an actual successful builder response the original returned peer and counter determine the trace entry. It then runs the complete original adaptive post client through the origin-aware post compiler, which computes Beacon origins from each actual prepared initializer request. Erasing all annotations gives literal equality with OriginPost.sequence, retaining the full origin trace. Every constructed descriptor names its complete actual origin-aware continuation, and every private derivation is tagged under every oracle reply. The actual registration consumer must instantiate the supplied builder-origin marker from its selected session; this generic compiler does not identify an arbitrary supplied marker with an arbitrary root. The source scanner and certificates consume this construction; no inverse descriptor, freshness premise, free callback-cost assumption or final secrecy conclusion is introduced here.

### PqxdhInitialOriginForwardPost

The forward compiler follows the complete original adaptive post client. For an actual record request, it carries the current full installation and publication trace with the original LIVE descriptor and updates that trace from the actual successful reply before continuing. For Beacon initialization, it retains all actual preparation, initializer and application callbacks and their failure branches; before a selected first-receive derivation it attaches the marker computed from the actual prepared initializer request. A marker is installed only if that same finish succeeds. Every pending descriptor names its exact remaining origin-aware continuation, and every actual private derivation carries a descriptor under every reply. Removing annotations yields literal equality with the complete OriginPost compiler and does not discard the trace. These source laws do not infer uniformity, freshness, or a resource bound from an arbitrary supplied descriptor; the actual scan and source certificates consume the constructed program. The complete final publication/freshness and finite secrecy composition remain later consumers.

### PqxdhInitialOriginNativeContext

The four statements preserve the full origin/publication trace when the actual selected source continuation is interpreted through private chain slots. `complete_map` retains the first Server send's original erase, optional serialization, exact peer publication and complete outside post client. `post_cut` treats original record operations and Beacon first receives, including their original owner/family completion, success filter and reveal-history tick. In both cases the same captured origin updates the same owner only on actual successful publication.

`frame_cut` combines all three original context constructors using the actual full76 pending reply. Its material-only counterpart receives only the allowed material and installs the new chain as the private label; every pre-draw role, outside source continuation, origin marker, publication entry, private initializer service and ambient effect is retained. `frame_run` makes the complete result/trace and Shared/private/root-cache equality explicit. No arbitrary native continuation, final event equality, source preservation or byte-injectivity premise is supplied. The native read handler remains the operational source side of the independently checked mask comparison; public HKDF remains real.

Actual forward annotation still must construct this very descriptor and its pre-draw trace/marker from the source execution. These operational equations do not infer that provenance from equal frames, nor assert a final secrecy or finite-hybrid bound. Callback costs remain the separate literal-syntax ledger, already preserved by OriginContext.stopped_query_bound.

### PqxdhInitialOriginPost

The complete pending post compiler now carries a private per-owner installation-origin map and a publication transcript. Original record operations append only successful send replies, paired with the origin already installed at that owner. `record_member` identifies both facts for every appended entry. Beacon finishes execute the original preparation and full first-receive tail through FinishOrigin.owner; only its successful marker updates the exact Beacon index. Failure and inactive phases leave the origin map intact. `owner_interpretation` and `finish_supported` derive this marker from the same complete actual interpreted finish with its ambient effects, so the existing selected-message origin theorem applies without inventing a successful session.

The single-builder sequence retains the actual original builder result and its complete returned state before running the original adaptive post client. A successful builder reply records the origin at its returned Server peer only when that peer is present in the actual returned state. Its transcript sequence comes from that same installed kernel; the generic wrapper does not assert that an arbitrary supplied kernel started at sequence zero. `builder_recorded` states these exact conditions. The actual initialized source constructor supplies the sequence-one specialization. All original failure, divergence, serialization, erase, publication, selector and reveal-history behavior remains in place.

`step_erase`, `program_erase` and `sequence_erase` are literal source-program equalities after removing only private transcript fields. `query_bound` preserves every all-reply primitive-class bound, and `sequence_total` consumes the concrete source callback budget 7+67*qPost. These are callback counts, not free ambient interpretation or zero local runtime claims. The saved trace may contain an explicit earlier prefix; no source provenance for an arbitrary supplied prefix is invented. The native-to-label representation of these new trace updates and the corresponding source-cut annotation remain the next concrete consumers before the common final event can use this metadata. No secrecy or finite-hybrid conclusion is asserted here.

### PqxdhInitialOriginPostMap

The four statements preserve the concrete origin/publication transcript through the actual retained-parent source interpretation. `step_interpretation` compiles every original record, selector and Beacon finish to the same primitive, read, preparation, application and initializer effects before proving any representation law. `step` then uses the checked actual receive/send interpretation and exact original initializer service: all later returned initializer kernels remain known, while the selected new chain alone uses the private label. The marker comes from the same prepared request on both sides. Origin-map updates and successful-send transcript entries are identical, including all optional failures. `program` carries this equality through the original adaptive full post client and preserves all ambient Shared/private/cache effects.

`builder_trace` preserves the actually returned Server peer and its send counter under the same chain interpretation, so the initial successful response produces the same transcript entry. It does not assert sequence one for arbitrary supplied kernels; the actual initialized constructor supplies that specialization. Public HKDF remains real, and native reads here are the explicit operational source interpretation before the separate legal read-mask comparison. No target-free arbitrary observer, equality of final events, query-cost transfer or security premise is supplied. The next source-cut continuation uses these exact program equations with its carried trace and pre-draw initializer marker.

### PqxdhInitialOriginPostPath

The complete original adaptive post client preserves an installed selected-session send path and an executed cache path for every successful publication carrying that selected origin. The record case consumes its actual reply and prior installed origin. The finish case uses the complete prepared initializer coordinate, the actual supplied initial kernel and full first receive; false-origin finishes remain unselected, and an unmarked finish cannot replace an existing kernel. Other owners and every failure branch remain in the same source execution. Existing publications survive all subsequent callbacks through actual cache extension. The initial prefix invariant is explicit: the real Server builder establishes it separately, and an initially unselected Beacon obtains it only from its actual matching finish. The theorem does not manufacture a target by running a final checker, assert freshness, or transfer probability or computation cost from support equality.

### PqxdhInitialParentBuilderContext

The four checked statements complete the original first Server send and full post continuation at a selected source KDF reply. `send_reply` derives the exact advanced native kernel and optional ciphertext from the actual full76 reply; its material-only counterpart retains failed-seal advancement and every shared effect. `complete_map` preserves the original erase callback, optional serialization and exact peer publication, then resumes the same adaptive full PostSpec client. `frame_cut` combines that first-builder case with the independently checked record/Beacon-finish cases. No arbitrary native continuation over hidden chain bytes is assumed. `frame_run` explicitly preserves all shared primitive state, private interpreter state and root cache in the evaluated distribution.

The stopped descriptor stores the original current state, pending send, authenticated plaintext, candidate, metadata and exact original outside client. Every saved chain is represented as known before the new draw. The selected new chain is private and the continuation receives only its material coordinate. Later initializer services remain the same old native services and their returned kernels are mapped known. Native reads here are retained for operational source equality; legal read masking, initializer-input/output aliases, complete candidate accounting and ordinary security reductions remain subsequent consumers. External callback work remains explicit and is not assumed free. No uniformity or secrecy conclusion is claimed by these equations.

### PqxdhInitialParentObserver

The nine statements construct and interpret the complete later-parent observer. Three monad laws flatten Shared×identity/private state×root cache without losing replies, state or callback order. Its input log includes old primitive/read candidates and each initializer input plus its two returned chains, at most three per callback. The native-read handler and the executable masked reader have exactly the same full transition outside an actual hidden-chain read. Their complete adaptive event probabilities agree on the same unconditioned final clear-bit event; no compromise probability is added or conditioned away. Concrete primitive and read equations discharge the full pending source interface. The complete compiled_source equation consumes the audited compiler and matches the actual ParentPost label interpreter, with real public HKDF and every explicit external effect retained. No whole-observer security or cost premise is introduced. External callbacks remain explicit parameters for the actual-source consumer; this module alone is not the final reached-source sampler or freshness implication.

### PqxdhInitialParentObserverAliases

The full later-parent comparison keeps the actual pre-registration callbacks, application bytes, selector, initializer root lookup and cache, auxiliary serialization and complete private/shared state. Its ordinary observer has no selected chain argument. The private mathematical interpreter routes an input only after that value appears in the existing candidate interface. Public HKDF always remains real. These source and coupling statements do not by themselves claim the final evolving-chain theorem; the concrete reached sampler, freshness event, ordinary Extract/HMAC reductions and source-derived resource bills consume them next.

`audit_route` replaces a successful initializer kernel by the supplied child response’s actual shared64 prefix exactly when the audited initializer root equals the selected input. A failed initializer remains failed; an output-chain candidate hit alone does not replace the initializer. No additional nonce is introduced into the actual initializer.

`old_source` proves every original private KDF, opening, sealing, public computation and read is precisely the existing private-only alias handler inside the full ambient state. `initial_lookup` proves the original initializer lookup, including all root-cache changes, finishes unchanged before any replacement. `initial_source` proves the compiled initializer is that lookup followed by the typed audit result and the actual known-kernel encoding.

`distance` charges the entire original extended schedule to one final candidate-membership event, retaining all prior candidates and the direct-read flag. It makes no small-alias premise. `public_real` proves every public HKDF projection remains the fixed source evaluation, including a guessed selected input. `compiled_source` lifts the exact private-step and initializer-input routing equations through every original pending callback and complete adaptive continuation.

`query_safe` proves that the native and masked readers retain exactly the same complete callback outside an actual hidden-chain read. `event_good` lifts that law to the original arbitrary event conjoined with the final clear flag. It does not condition on secrecy or add a probability for an excluded disclosure.

Query accounting remains explicit in the consuming source ledger: the compiler uses at most two extended callbacks per original pending callback; every typed initializer audit contributes at most three candidate values (root and two chains), and its unchanged original lookup retains its actual uniform/base/decapsulation work. This module does not declare the original external computations free. No implementation of a cryptographic primitive is proved.

### PqxdhInitialParentObserverBudgets

The full observer resource ledger counts its actual source syntax and each complete callback’s random work. It retains the complete initial candidate list, all original shared/private/root-cache fields, failed attempts and arbitrary replies. It makes no assumption about secrecy or the whole observer’s cost.

`trace_length` proves that every supported run leaves at most the initial candidate-list length plus three times the actual extended callback count. Three accounts for the typed initializer input root and both returned chains. Other old private/public/read callbacks have their original at-most-one entry; every attempted callback remains counted, with duplicates retained.

`cost_cap` bounds the exact callback cost classes by 64+qPre+qApplication+qInitial+qSelector+qAux. Sixty-four bounds the existing concrete commitment/open/seal primitive coins. The five separate external costs remain displayed rather than treated as free. The ExternalUniform record requires the actual preparation, application, initializer, selector and auxiliary computation to satisfy its own random-call bound at every query and complete ambient state. These are ordinary resource contracts and must be discharged by the final concrete source interpreter.

`flatten_uniform` proves syntactically that reassociating the complete ambient result preserves its uniform-query budget. `handler_uniform` consumes the checked concrete old primitive interpreter and each actual external resource contract, giving the exact cost for every query class. The internal typed initializer audit returns its value with zero additional coins, after the original initializer’s full charged work.

`observed_uniform` proves that adding candidate values and the sticky direct-read flag adds no random call. `complete_uniform` applies the derived callback cap throughout the original adaptive syntax and gives qCallbacks*(64+qPre+qApplication+qInitial+qSelector+qAux). No cost is transported through an equality of evaluated distributions. The stopped-source certificate supplies qCallbacks and the complete initial-list bound in the consuming module.

### PqxdhInitialParentObserverCompiler

The seven statements give a concrete lowering for the entire original pending builder/post interface. The new oracle is the old selected primitive/read interface plus original preparation, application, selector and publication callbacks, an initializer returning its audited actual root and optional native kernel, and a initializer-reply audit whose ordinary handler returns the unchanged optional native kernel. Every returned native kernel is mapped to known labels, appropriate to a later-parent cut. The audit records the actual input even on optional failure and both returned chains on success, at most three entries including duplicates. Interpreting the audit as the identity reply gives the same full original pending interpreter for every reply, and therefore every complete adaptive pending program. Each original input emits at most two queries; a source all-reply budget q gives 2*q by direct syntax induction, not a distributional cost transfer. External callback uniform/base/KEM bills are separate source-derived consumers. The initializer audit callback accepts a typed InitialReply rather than an arbitrary list, so its at-most-three bound holds for its whole domain. This adapter alone does not prove a source sampler or secrecy; later source realization, private alias coupling and actual freshness must consume it.
The revised audit returns an optional native kernel, allowing the separately checked comparison handler to replace the initializer prefix at an explicitly recorded input-root alias; its ordinary source interpretation remains the identical kernel. All seven guarded statements were rechecked after this signature revision.

### PqxdhInitialParentStoppedBudgets

The five statements consume the original complete post-client budget, the source-carried descriptor certificate, an explicit initial candidate-list length, an explicit finite checker limit and separate uniform costs for each actual external callback. There is no whole-observer resource or secrecy premise. Let T = 2(255 + 67 qPost) + qCheck, U = T(64 + qPre + qApplication + qInitial + qSelector + qAux), and Q = qPrior + 3T. Every failed or repeated callback and each appended finite-lineage checker query is counted. The qPrior bill includes the entire actual initial candidate list; its concrete source provenance is a separate consuming obligation.

source_uniform derives the ordinary stopped observer's uniform-query cap U from its literal source syntax and individual callback caps. source_candidates derives Q for every supported complete trace, retaining the initial list and all attempted callbacks. source_bound substitutes Q into the checked local source-and-checker comparison: the exact main Extract and two-query HMAC losses, the exact preimage-tester Extract and two-query HMAC losses, 2^-352, and Q/2^256. This statement does not assert source freshness or the global sampler correspondence.

source_reduction_queries gives both actual main/tester HMAC reductions two challenge queries and qSample + 76 + U uniform queries; it also counts at most Q real fixed-HKDF evaluations by the tester. source_challenger_queries separately counts the actual 64-byte Extract/HMAC draws and 76-byte child draws in all five challenger worlds. These are uniform-query bills; separate source base/decapsulation and other deterministic work remain explicit in their source interfaces, and are not declared free. No cost is transported through a distributional equality.

### PqxdhInitialParentStoppedHop

This is the ordinary cryptographic hop for the full stopped source interface, including the registration builder’s first send, established records, attempted Beacon finishes, and the complete original post-registration continuation. Its source prefix is literally PqxdhInitialOriginContext.stopped compiled through the checked initializer-audit adapter. It then optionally runs the concrete finite lineage checker after the adversary stops, through the same private KDF interface, returning the actual checker slots alongside the full original source result. The selected parent address is the actual saved source request. The result retains the entire family, source role fields, installation/publication origin trace, ambient shared/private/root-cache state, prior candidates and the direct-read flag.

The continuation also stores an optional concrete remaining checker depth. A selected finite record uses some n and the checker makes n+1 private derivation requests; none leaves the checker list empty for an unextended local comparison. There is no arbitrary postprocessing program field. The continuation stores actual source data and explicit preparation/application/initializer/selector/publication handlers as functions of the context drawn before the parent response. It contains no arbitrary observer program function and receives no omitted parent second32 value. The ordinary observer sees the retained parent material and the challenger’s full child response. Every public HKDF evaluation remains real. The context, actual source reachability, exact native final-event interpretation and source callback resource contracts must be instantiated by the consuming common source experiment; this module does not state that an arbitrary reached state is uniform or that the final protocol freshness event is already equal to its proxy.

`decision_probability` states the unconditioned event conjoined with the final clear flag. `local_bound` connects the original routed native-reader stopped game to the target-free observer, charging one original complete candidate event. It uses the checked exact hidden-read masking law and complete-state alias coupling; no probability for an excluded disclosure is added.

`actual_route` and `random_route` lift that local comparison through the same complete original context and parent76 draw. `actual_bound` charges real-child input aliases to a separately constructed full-output preimage tester, its ordinary Extract/HMAC advantages and the exact 2^-352 finite-image term. `random_bound` uses delayed sampling of the parent’s omitted32 only in the independent-child world, obtaining qCandidates/2^256. It counts the entire list, including its prior entries and repeated values.

`bound` composes those two routing comparisons and the original coefficient-one main Extract/HMAC hop. Its displayed loss is main Extract plus main two-query HMAC, tester Extract plus tester two-query HMAC, 2^-352, and qCandidates/2^256. Both pairs use the same actual joint sampler, original complete context and retained parent material. There is no public random-HKDF-table assumption and no primitive implementation proof.

`observer_bounds` retains the complete observer uniform bill for both the main and additional tester. `reduction_queries` gives at most two HMAC challenges per constructed reduction, qSample+76+qObserve uniform calls, and at most qCandidates actual fixed-HKDF evaluations by the tester. The extra tester evaluations are explicit local work even though fixed HKDF itself requires no uniform calls.

`challenger_queries` gives separate syntactic bills for every main/tester challenger: Extract real qSample+76+qObserve; Extract uniform qSample+76+64+qObserve; HMAC real 64+qSample+76+qObserve; HMAC random qSample+76+64+64+qObserve; independent child qSample+76+76+qObserve. These are not transported through distribution equality. The subsequent source resource module derives qObserve from the actual individual callback bounds.

`base_source` instantiates the full private-step/initializer-root routing equation at the actual origin-aware stopped program, retaining the root lookup and all complete continuation effects. `checker_source` evaluates the appended checker as the exact finite routed private lineage, including the selected material key. `program_source` combines them: the complete original protocol result, history, origin trace and ambient state are retained, paired with the computed checker slots. It does not equate protocol freshness with a clear bit; the final source correspondence consumes those slots and the original revealed values. `checker_total` bills exactly n+1 additional private derivation requests for some n, and zero for none. `program_total` consumes the source-derived Fits certificate and proves at most 2*(255+67*qPost)+checkerBudget(depth) extended callbacks. The 255 is the conservative remaining in-progress receive/send reserve; 67 accounts for each original complete post call; the factor two includes typed initializer auditing. The source forward construction derives Fits from the original caller’s all-reply budget.

This revision supersedes module hash3610190c04db796da3ef68bfb3774ab3949b55d0966f3dce362b309efddcbdf4 before integration. The earlier source ended at the adversary’s stopped result and could not express the required final finite lineage check. All fifteen actual axiom guards were rerun after adding the concrete checker. The final actual source freshness/publication correspondence remains a separate checked consumer, and no native-freshness equivalence is assumed here.

### PqxdhInitialPendingSourceBounds

The thirteen statements bound the literal complete pending source under every oracle reply. A raw receive costs at most 51 derivations plus one opening; a send costs at most one derivation plus one sealing. A live source request costs at most52, including all read branches. The original first Beacon receive costs53 including its application getter, and54 including the initializer. Together with the existing thirteen preparation callbacks, every attempted Beacon registration costs at most67, including preparation rejection and inactive states. Records and selectors fit the same conservative cap, so an adaptive original post program with qPost requests costs at most67*qPost.

The Server builder retains actual check-identity, peer reservation, allocation, derivation, sealing, erasure and serialization. Its post-initialization publication tail costs4, and its full builder costs7 across all gates and Rust failure/divergence branches. The single accepted builder followed by the original adaptive post schedule therefore costs at most7+67*qPost. These are source callback counts derived from executable syntax, not transferred through equality of probability distributions. Primitive, uniform, base, decapsulation and local computation costs of interpreting each callback are separate consumers; no ambient callback is asserted free. The arbitrary-kernel formulation applies to native, selected-half and later-parent representations.

### PqxdhInitialPostCertificates

The four statements certify the actual descriptor carried by the complete post source. A single original LIVE record request has only zero-query saved LIVE, family and owner continuations; live_quiet derives that property from the literal original one-request program. A full-post descriptor records both that quiet completion and an all-reply query bound on its actual saved outer PostSpec continuation. First Beacon receive descriptors instead use the actual quiet owner from the original raw receive after preparation, initializer and application lookup.

program_fits derives these certificates by induction on the original adaptive client, preserving records, selectors, all registration phases, rejections and full callback replies. fits_mono allows the original source allowance as a conservative bound after any prefix. carried_fits consumes the executable scanner and establishes the property of the very descriptor it returns. It does not choose an equal-frame descriptor, infer a resource bound from an evaluated distribution, or assume a budget for an ambient closure. Pending-completion and interpreted primitive costs are separate consumers.

### PqxdhInitialRootAudit

The seven statements establish exact private auditing of the original known/family initializer service. Native erasure removes only the actual root field; retained erasure also keeps the selected supplied response and unchanged root cache. Candidate length is exactly three, with the original root and both normalized Beacon chains recorded even if values coincide. The source kernel keeps the previously proved zero-state positional invariant. The audit uses at most the same 32 uniform-byte queries as its syntactic response projection; no probability-to-cost transfer is used. This is a later-chain-cut service: it is not the root-free observer for the earlier initial64 Extract comparison. The earlier sampled root may be retained only after that comparison in the independent64 endpoint. No public root reveal is added.

### PqxdhInitialSelectedOrigin

The private marker is computed from the exact request made by the original compiled initializer. It is true only for the selected family coordinate; every known-root request remains unselected, even if numerical root bytes alias another root. `selectedRequest_iff` states this distinction. `value_origin` and `service_origin` prove it agrees with every actual supported response-only initializer result while retaining the full root-cache state. Nonselected cached or newly drawn roots remain known and their effects are not discarded.

`finish_origin` consumes the checked original finish transcript. A recorded true marker entails the original initSent phase, an actual supported preparation and full first-receive tail, the exact published state and a successful application reply, and the complete matching initializer request. It does not infer session identity from the Beacon index or assume injectivity of root or chain bytes. Combined with FinishOriginLog, this marker is available before a selected private cut and is installed only after actual successful publication. Per-owner origin retention through the complete post schedule and the common final target event are subsequent consumers.

### PqxdhInitialStoppedSourceBounds

The full carried operation has at most 255 remaining callbacks, including every saved receive continuation and its eventual optional open. The original remaining post schedule contributes at most 67 callbacks per request. The actual first-builder completion uses at most two callbacks before that schedule. The origin/publication trace is private deterministic bookkeeping and preserves the exact source callback predicate; the ordinary observer compiler pays up to two callbacks per source callback because initializer auditing is explicit. These are all-reply syntactic bounds, not a claim that the work inside callbacks or local copying is free. Primitive, uniform, and local computational costs require their own interpreter bounds.

## Concrete source freshness and resource checkpoint

This checkpoint adds 33 modules and 253 guarded statements. The actual experiment derives its initial kernel, selected directional root, empty selective store and origin trace; every stage uses the same successful-publication and original byte-lineage freshness event. Actual source sends derive the finite record-position allowance. Complete source sampling, candidate history and callback ledgers instantiate the stopped observer. The corrected native observer routes only private derivation aliases and preserves every future initializer reply. The complete source freshness comparison pays main Extract and HMAC advantages plus three times the separate tester advantages and its statistical terms. Actual cached-child and parent-address events have an additional source-derived input bound. The real-child event is connected to the final private table; the appended cached checker now preserves that event through the full deferred draw, while its complete suffix-observer connection and the first-half whole-source freshness consumer remain unfinished. No completed evolving-chain theorem is claimed.

### PqxdhInitialAuditedResources

The four statements instantiate the native source ledger on the same actual audited source callbacks and carried sampler. Let L be max(76, qPre, qApplication, qInitial, qSelector, qAux). The computed uniform-query cap is (7 + 67 qPost)L. The native76 term pays a possible private full output; source opening/sealing costs64, public coins1, commitment64, public real HKDF0 additional uniform queries, and native reads0. Those uniform counts do not claim deterministic local work is free.

local_bounds converts the five separately bounded actual audited callbacks into the original native external ledger. Only the initializer reply's private audit is erased; its complete effects and source order remain. source_uniform derives the actual entire audited first-builder/post uniform bill from the original all-reply post bound and these local callback contracts. carried_uniform gives the same computed cap for the literal descriptor-carrying audited prefix. All cost transport uses syntactic oracle-program equalities and query-preserving reply maps, never equality of evaluated distributions or a whole-observer premise.

retained_callbacks discharges the initializer entry for the actual NativeInitializer.initial with32 uniform requests under every ambient state and root cache. The concrete retained root, selected or unrelated root requests, source optional kernel and source cache effects remain unchanged. Only the four other separately stated preparation/application/selector/auxiliary costs remain parameters to be instantiated from their ordinary original callbacks. This module introduces no security, uniform-input or freshness premise.

### PqxdhInitialCheckedFreshness

The eight statements consume the actual complete stopped builder/post program and the literal optional finite lineage checker. A concrete nonempty checker depth guarantees its returned slots contain the omitted input under every backend. Mapping those slots through the native interpretation gives exactly the omitted input plus all returned known values; the original full final disclosure history and every earlier ancestor remain present. The stopped disclosure theorem derives the required witness and candidate inclusion from the same actual saved history and explicit earlier candidate ledger.

checked_fresh_proxy proves byte-value freshness equals its target-free proxy outside the actual complete candidate event. good_bound compares the unconditioned events using the same arbitrary full-state gate, which can retain the original decision and selected-session publication transcript. Only a candidate hit on a clear-disclosure execution contributes. Actual forbidden direct reads are excluded by the original freshness event, so they add no compromise probability. decision_bound states the same fact for Boolean decisions.

proxy_bound instantiates the existing full stopped source coupling at this literal program, exact saved-history seed and unchanged full-state event. It changes only the source's initializer/step alias routing and native read interpretation through the previously checked comparison; real public HKDF and all external effects remain. good_alias_bound costs at most two copies of the ordinary masked candidate event. The final bound combines this with the proxy comparison to give the explicit conservative factor three, including all checker candidates, with no native-freshness-equals-clear premise.

These are local source/checker event comparisons, not the final adjacent experiment theorem. The concrete consuming source must retain the same target-independent gate, source-selected saved descriptor, actual initial directional root and earlier cached ancestors across each hop. Its exact source-to-retained-view realization and publication/path theorem identify this interpreted checker with the one final source lineage. Resource bounds, ordinary Extract/HMAC reductions and finite selection factors remain separately instantiated consumers. No entropy is inferred from a reached state, and no cost is transported through evaluated distribution equality.

### PqxdhInitialCommonSecrecy

One exact common/pending sampler feeds both full source comparisons. Common outcomes return their unchanged original decision. Pending outcomes retain the complete actual stopped builder/post schedule, original publication gate, earlier ancestors, prior disclosures and final history. The native branch uses the corrected partial private-query routing; every initializer retains its original optional kernel even on a matching input. The ordinary masked observer is unchanged.

The eleven theorems give the coefficient-three native-freshness comparison, its mixture over the complete original prefix and full76 parent draw, the real-child ordinary preimage tester and independent-child input-guess bounds, and the resulting main Extract plus main HMAC plus three times tester Extract, tester HMAC, 2^-352 and Q/2^256. No public-HKDF random-table assumption is used. The same sampler, complete parent entry and actual continuation are used in each constructed reduction.

Query statements charge both HMAC calls in each reduction, original prefix coins, the full76 parent draw, complete observer coins, and up to Q real fixed-HKDF evaluations in the separate candidate tester. Factor three multiplies advantages, not the query cap of an individual reduction. Challenger costs explicitly include the64-byte Extract replacement key,64-byte HMAC key, two64-byte random HMAC responses and separate76-byte independent child. Candidate and observer bounds are supplied here as interfaces; the concrete supported source resource certificate must discharge them.

This theorem does not alone identify the table-dependent original final source event with the appended checker. The actual source realization must supply that equation off separately charged cached-child and parent-address collisions. Full source initialization, all ordered hops, selection and authenticated-root composition remain consumers. No primitive implementation or persistence behavior is modeled.

### PqxdhInitialCounterBudget

The actual full pending NativeLog handler retains its chronological private-call list and adds at most one entry per source callback. Structural induction over the same source program derives monotonicity and the original all-reply callback budget plus its initial list length. The send proof uses actual controller admission: exhaustion preserves the input kernel; every admitted send advances exactly once only after its pending private request has been appended, including cache hits and failed sealing. Actual receive source projection and the original receive-field theorem show that receives preserve the sender counter. These facts discharge the complete state-indexed owner callback rules and raw-receive consumer without an assumed callback invariant. The seven statements do not yet assert a full source publication/selection bound; that consumer must establish zero selected-origin installation and propagate the rules through builder and post. No cached-walk length or cursor-depth equality is used. All seven standard-three axiom guards pass; no Rust code, source behavior or trust-boundary assumption changes.

### PqxdhInitialCounterPublication

The original supplied Server initial64 constructor has sender counter zero. The complete original builder retains each allocation, admission, application, Rust failure, first-send, key erasure, serialization and publication branch; every successful installed selected-origin Server peer has counter at most the actual chronological private-call log length. Matching Beacon initialization uses the full original selected request coordinate, starts counter zero and retains its complete first receive. A false or absent origin cannot establish selected-session provenance. The full original record/reveal/selector/finish client propagates the invariant only for kernels whose installed origin is true, preserving arbitrary other owners and prior state. Successful send replies identify the actual installed kernel counter, so all selected-origin publications remain bounded after later callbacks. These are operational source facts rather than assumptions about a cached walk or cursor.

publication_bound consumes the same actual complete SourcePublication.sequence, its real supplied initializer and the original all-reply post allowance qPost. It derives number.val ≤ initialLogLength + 7 + 67*qPost. The initial chronological list is explicit; a fresh full-source run starts with length zero. selection_bound bounds an adaptively chosen published position by the explicit finite sum over positions in range(initialLogLength + 7 + 67*qPost + 1), retaining any same final source event. The extra position zero is a conservative allowance; no probability mass is conditioned or resampled. This handles publication-position selection for a fixed selected source owner/session. Choosing the session, direction or owner still needs its separate finite-family selection argument in the final consumer. No path/cached/counter equality or security assumption is supplied.

All eleven exported statements pass actual standard-three axiom guards. The proof changes no Rust code, protocol execution, transcript, callback costs or trust-boundary assumptions. Temporary split drafts were consolidated into this full-source consumer.

### PqxdhInitialDisclosureState

The full original post client derives its actual disclosure witness from per-query source laws. A non-read callback retains the sticky direct-read bit and every earlier candidate, while a family read records precisely its original optional native reply, available input candidates and hidden-slot exposure flag. Original record/public operations, private first receives, initializer audits, selectors and failure branches preserve the same history discipline. The reusable Rules interface is completely discharged by the actual routed ParentObserverAliases interpreter composed with the original audit compiler; no final history correspondence or freshness premise is supplied. The whole original LIVE and PostSpec schedules then preserve: a true bit has an actual disclosed target witness, and a clear bit keeps every prior/history disclosed input in the same candidate ledger. Initializer input/output aliases add candidates without being declared disclosures. The zero-read certificates classify literal source syntax; they are not computation-cost bounds. The actual stopped source, appended checker and final probability comparison consume these facts in the following module.

### PqxdhInitialHalfInitializer

PqxdhInitialHalfInitializer supplies the concrete audit callback for the first directional child after the initial64 comparison. Its value service retains the original initializer input and the existing selected-or-known initializer reply. A matching family coordinate returns the earlier private root and the selected label with the retained opposite half; a different family coordinate performs the original cached uniform root lookup and real fixed-function initialization; a known root retains that exact root and real reply.

Erasing the private input field gives precisely PqxdhInitialSelectedService and the original current Beacon initializer, including repeated matching requests. Interpreting the hidden label at the selected half reconstructs the complete PqxdhInitialNativeInitializer reply with the same actual64 response and complete shared, identity and root-cache state. The two half orientations use the same join function as the original initial sampler. The kernel's initializer input is unused only after the exact response has been obtained; no equality of different root computations is asserted.

The literal audited service has the same at-most32 uniform query bound as the source cache lookup. No extra sample is used for its audit or chain labels. The earlier root is ordinary private context only after the initial64 comparison; this module does not provide that preceding security comparison. The unavailable half is not provided to the ordinary audited initializer. Full first-half freshness and source adjacent-game composition remain consumers of these operational equations.

### PqxdhInitialHalfObserverCompiler

The first directional chain hop begins before the original Server builder's first send. Matching Beacon initializers must therefore return kernels whose selected initial chain remains hidden. The later-parent compiler intentionally turns every future initializer kernel into a known kernel and cannot supply this first-half representation.

PqxdhInitialHalfObserverCompiler preserves the full original pending Slot interface and original initializer callback. Its initializer reply retains the actual private root input and an optional Slot kernel. A separate pure audit records the input and each available known chain, omitting hidden slots, and returns the same optional kernel. The root input remains recorded even if kernel construction fails. Every audit has at most three candidates. No public output or original optional reply is changed.

The callback and whole-program equations identify literal source syntax under an arbitrary lawful interpreter. The compiler pays at most two callbacks per original callback, including the initializer and its audit, and the whole-program bound follows structural all-reply induction. Underlying callback work is not declared free; an execution consumer must instantiate its concrete costs. These are operational components, not the first-half secrecy theorem or the completed evolving-chain bound. In particular, the actual whole builder/post freshness event and initial64 source comparison must still be composed.

### PqxdhInitialHistoryBudget

These five statements close the resource origin of the stopped observer's complete initial disclosure list. The history accessor is the exact one used by StoppedDisclosure: a record descriptor uses its saved inner LIVE history, while finish and builder descriptors use their saved frontend history. Arbitrary descriptors need not identify those histories, and no such equality is assumed.

post_bound follows the actual complete annotated post source under every reply. Original reads append at most one32-byte known value; a complete family operation ticks the timestamp without adding disclosures, and all initializer/preparation/publication/selector paths preserve the disclosure list. The proof counts one original request for every possible read. program_bound extends that certificate through the actual first-builder identity checks, reservations, consumed-registration state, first private send, erase, optional serialization and publication, all of which retain the same disclosure history.

carried_bound applies those source syntax facts to the literal descriptor returned by the audited scanner, yielding savedKnown <= initialKnown + qPost. seed_includes proves that the seed contains both the exact saved disclosure list and every earlier audit entry. carried_seed combines the history result with NativeAuditCarried's chronological source bound: the complete seed length is at most initialKnown + qPost + initialAudit.length + 3(7 + 67 qPost). Duplicates remain and are paid; no root-cache function is enumerated. The bound applies to actual supported descriptors and does not postulate a whole-observer resource or freshness condition.

### PqxdhInitialNativeAdjacent

Both original full builder/post stages share the same literal carried predecessor sampler, including every private state field, external effect, root cache, origin trace and final result. source_adjacent derives this from the complete carried-program equality before the selected depth, not marginal output equality.

normalization replaces only an actually cached selected branch of the later stage by the earlier complete continuation. Its total-variation cost is at most the source-derived sum of (k + j + 1) / 2^256 for j below 7 + 67 qPost, where k bounds the initial recorded private-input log and qPost bounds every branch of the original outside post client. Initial coverage, depth and a missing current cursor address remain displayed operational premises. normalization_after proves that any identical full-state final observation preserves the same cost. adjacent_bound adds that cost once to the normalized fresh-child comparison.

This is a source normalization, not the fresh-child cryptographic reduction or a source freshness theorem. Those consumers must preserve the same observation, establish initial operational premises from the actual source initialization, and account for the entire source sampler and observer work.

### PqxdhInitialNativeAuditCarried

The source scanner executes the literal origin-aware first-builder and full adaptive post program with NativeAudit's complete chronological candidate state. No continuation is inverted and no descriptor is replaced by a frame-equivalent witness.

step_same proves complete callback equality between adjacent private-table stages while the actual selective cursor remains before the predecessor depth; initializer root/cache work and every candidate entry remain identical. step_preserve derives preservation of that cursor condition through every actually executed unselected query. carried_same uses those two facts on the literal annotated source program, retaining the same descriptor and every candidate/state field in the common sampler.

carried_projection erases only the candidate audit and returns the literal original carried source sampler, including its exact descriptor. carried_audit derives an appended candidate length of at most 3(7 + 67 qPost) from the original all-reply outside-client budget; the entire original starting list is retained, and the unexecuted selected query is not included. carried_fits transports the existing concrete source-derived stopped-continuation certificate through this exact descriptor projection. carried_uniform preserves the original source uniform bound through literal oracle-program erasure and scan-completion equations, never through an evaluated distribution equality.

The actual preexisting disclosure history and initial audit length remain explicit resource inputs. Adding the saved history's known values and proving its original-source history bound are subsequent consumers. These operational/source resource facts do not assume freshness, a uniform selected input, or small alias probability.

### PqxdhInitialNativeBudgets

The sixteen statements bound actual uniform-oracle calls of the full pending Server-builder and post-source interpreter. Each cost follows the literal original program, including all typed replies, rejection branches, cache hits, source metadata, private input log, and primitive, identity and root-cache state.

- `native_program` derives76 per private KDF and64 per shared commitment query from the actual mutable selective backend; native lifting contributes no caller coin.
- `open_hash` and `seal_hash` derive one original commitment query for each complete inner opening or sealing program.
- `open_uniform` and `seal_uniform` combine those counts with zero private derivations inside the actual primitive adapters, giving64 uniform calls each. AEAD, writer, parsing, hashing and other deterministic work are retained but are not uniform draws.
- `receive_uniform` and `send_uniform` carry the64-call bounds through the original enriched callback adapters, including missing material, failed opening, failed sealing and writer rejection.
- `public_uniform` charges the actual public coin1, commitment-cache64 and fixed real-HKDF0 uniform costs separately.
- `live_uniform` assembles the complete enriched callback classes: private derivation76, opening64, sealing64, public1/64/0, and read0. Cache hits do not require fresh draws; the76 cap covers the possible full private miss without assuming one.
- `logged_live_uniform` proves that adding the actual chronological input log and retaining the outer identity/root-cache state does not add random draws.
- `external_uniform` preserves every original preparation, application, initializer, selector and auxiliary callback effect, charging its corresponding local cap. `LocalBounds` quantifies over each original external callback and ambient state; it is explicitly a local operational interface contract, not an assumed whole observer or protocol cap.
- `step_uniform` bounds each actual full pending callback by `callbackCap = max(76, preparation, application, initializer, selector, auxiliary)`.
- `program_uniform` derives the complete interpreted uniform bill from an original syntactic callback bound and those individual callback costs.
- `source_uniform` consumes the actual source bound of seven callbacks for the first builder plus67 per original post request. The full uniform cap is `(7 + 67*qPost) * callbackCap`; no caller-supplied complete observer budget remains.
- `carried_uniform` gives that same cap for the executable descriptor-carrying predecessor sampler using literal scan-and-finish equality and the complete source program. It does not transfer costs across probability-distribution equality, and it introduces no selected-miss or cache-consistency premise.
- `initializer_uniform` specializes the actual retained root-cache initializer to its source optional kernel reply, erasing only the private audit field. Its cap is32 under every ambient state/cache, including selected reuse, known inputs and nonselected cache hits or misses. This supplies the concrete initializer entry when instantiating the local external ledger.

The conservative maximum intentionally overcounts some callback classes. The external preparation, application, selector and auxiliary caps must still be supplied from their actual primitive implementations; the theorem never declares that ambient work is free. Initializer sampling before this source execution, ordinary reduction challengers, finite lineage checking and deterministic local computation remain separately charged. These are resource statements and make no new cryptographic assumption or secrecy conclusion.

### PqxdhInitialNativeChildDraw

# One remaining child draw through the full source interface

`PqxdhInitialNativeChildDraw` extends the existing generic deferred-sampling theorem to the actual complete pending source interface. It retains preparation, application, initialization, selectors and publication callbacks alongside the original LIVE primitive requests. External effects can update their actual Shared/N/root-cache state; they cannot overwrite the separately retained private KDF table or cursor. No arbitrary callback-equality or private-table independence premise is introduced.

`bare_step` proves a literal compiler equation for every full source callback. `bare_program` lifts it to the entire adaptive original client. The compiler routes existing private KDF queries to their same shared table and forwards the complete original backend and external requests unchanged. Reassociation retains every private table/cursor field and every ambient field. Actual read replies and public HKDF computations are inherited unchanged from the original pending compiler and real backend.

`retained_compiler` proves that this exact compiler under any fixed retained private lookup is the complete `NativeRetained.retained` interpreter. It preserves both the original live primitives and the actual external effects. The internal live-lifting proofs preserve the whole ambient state rather than only an output marginal.

`bare_uniform` applies the existing checked generic single-child theorem to this explicit compiled program. When the next cursor address is actually absent from the private table and precisely one selected private derivation remains, drawing one full76 child response before the complete continuation gives the same evaluated distribution of its entire result and original ambient state. The retained lookup is the original real-HKDF fallback plus the exact existing table plus that child entry. Public queries remain real. An unused early draw is retained even if the original continuation ends before requesting the child.

`logged_uniform` is the requested full source law. It first erases only the chronological private log by a literal source equation, then consumes `bare_uniform`. Its final projection removes completed private table/cursor/log instrumentation and preserves the complete original result (including source frontend, history and installation/publication trace whenever carried by the client), shared primitive state, identity state and root cache. The source consumer must derive the child miss from its original chronological-input event and must separately relate a final event that consults the private table to the retained execution. The theorem does not discard a needed event field by assumption.

`early_uniform` separately derives the comparison execution's resource bill: `76 + queries*max(76,qPre,qApplication,qInitial,qSelector,qAux)`. It consumes the original client's all-reply query bound and actual individual external callback costs. For each early response it uses the exact stage-zero retained-program equation and the checked original callback ledger; it never transports a query bound through `logged_uniform`'s evaluated-distribution equality. Local primitive, parser and deterministic source computations remain reduction work. The per-declaration recursion allowance on this resource proof is only an elaboration limit; every statement has the standard three guarded axioms.

There is no new security assumption. Initial root distributions, source reachability, child input aliases, live freshness and the complete ordered secrecy comparison remain consuming protocol obligations. Snapshot and persistence behavior is excluded.

### PqxdhInitialNativeParentContinuation

The actual full source continuation after its selected parent response is related to the existing retained-parent native interpreter and then its material-only origin-aware context. Every statement keeps the full source result, installed origins, publication trace, saved history and shared/private/root-cache state. The earlier initializer lookup and its returned kernels remain unchanged; the new parent next-chain coordinate is not used as an initializer half.

`ambient_pure`, `ambient_bind` and `ambient_program` prove exact reassociation of SharedState × (N × C) with the original nested ambient interpreter. `retained_handler` identifies every full-interface retained callback with that original native parent handler; the primitive and optional-read cases use the actual retained-parent backend, while preparation, application, initializer, selector and auxiliary callbacks are unchanged. `retained_program` extends this literal callback identity through the whole original adaptive program.

`updated_view` identifies the actual table after recording the complete parent response with the old retained view plus that response's retained parent entry. `parent_retained` uses the actual matched cursor update to discharge saturation at original depth+1. It then derives the complete source continuation under the original native parent interpreter without a caller-supplied compatibility equation. `parent_material` composes that exact source equation with the concrete OriginNativeContext frame law. The only retained unknown parent coordinate is reconstructed after the full material-only continuation; no arbitrary saved function is retagged.

The later depth+2 stage requires a separate one-child deferred-sampling law and its actual cache-miss/candidate analysis. Private alias routing and initializer audit routing are separate comparisons. These theorems preserve the original initializer on every branch and do not identify it with a routed initializer on an alias hit. No resource costs are transported across an evaluated-distribution equality, and no snapshot or persistence behavior is considered.

### PqxdhInitialNativeParentEvent

The four theorems in `PqxdhInitialNativeParentEvent` connect the actual real-child source event to its finite native checker predicate. `parent_extends` uses the actual pre-parent cache miss to preserve earlier cache bindings. `parent_walk` then extends the original root walk by exactly the matched parent's input and returned next-chain coordinate. Repeated inputs are retained in the list.

`source_fresh` uses the supported complete post-parent execution at stage depth+1. Its matched parent update establishes saturation. The existing complete source replay supplies cache extension, and the saturated final-binding theorem supplies agreement on every actual final cache binding. The proof therefore instantiates `PublishedEvent.source_checked_fresh` without any supplied final cache-agreement or freshness-equivalence hypothesis. The exact fixed earlier list is the pre-parent walk followed by the parent's input. The parent/child address separation remains explicit. The child response is the actual retained prior response at its target address; a separate chronological-log absence theorem identifies it with the production response.

`source_decision` preserves the original Boolean result, selected-session publication gate and complete disclosure history. On that gate it consumes actual publication-cached evidence and proves that the original final-table-dependent source decision equals a function of the complete native source result and the explicit checker trace. The publication fact is supplied by the already checked complete source publication invariant; this component does not manufacture publication or assume a secret target. The random single-child case needs the separate appended native checker before private-table projection. Resource bounds are not inferred from these event identities.

### PqxdhInitialNativeParentRealization

The seven results in `PqxdhInitialNativeParentRealization` identify the actual full native continuation after its selected parent response with the compiled partial-routing observer. They retain the complete original result, role family, disclosure history and origin/publication trace, plus Shared state, auxiliary state and the original root-initialization cache. The parent/child address separation remains explicit. Initializer callbacks return their original responses throughout, including an initializer input alias.

`ambient_flatten` and `ambient_map` prove exact tuple reassociation and complete result mapping. `consistent_patch` proves that recording the already retained value changes no address. `compiled_consistent` specializes the partial observer to that actual retained child response. `frame_compiled` uses the constructive source context's exact native material-only continuation equation, and `source_compiled` discharges the actual post-parent stage's saturation from its matched cursor update. The prior is precisely the retained view of the actual pre-parent cache, not an independently supplied private function. `unlisted_source` derives the fixed production child response when its address is absent from the actual chronological input log, using the checked cache-coverage invariant.

These are operational equality and cache-origin results. They do not claim that a final table-dependent freshness event may be projected away, do not transport resource bounds through distribution equalities, and do not assume a cached parent was freshly sampled. Final source-event and random-child instantiation are separate obligations.

### PqxdhInitialNativeRetained

The full original pending source keeps its original external preparation, initializer, application, selector and publication effects. The retained interpreter removes only the private KDF table, selected cursor and chronological input log after completion; it preserves the entire result, primitive shared state, additional protocol state and root-service cache. Any family kernels, history or origin trace in the result are therefore preserved as well. External callbacks have their original Ambient type and cannot access the separate private table or cursor.

`step_depth` proves that each actual callback preserves or advances the selected cursor. `step_saturated` proves that one callback past the selected substitution stage equals the stage-zero callback, including external effects. `program_same` is the operational induction lifting pointwise equality on a preserved state invariant to an arbitrary complete adaptive client. `saturated` instantiates that induction to the actual full original handler: once the initial cursor is past the stage, the complete source execution is literally the stage-zero execution, including all private bookkeeping.

`zero_view` proves that the stage-zero memo handler records only the response already given by the initial retained lookup. `pending_view` lifts this law through the original enriched primitive compiler. `step_view` covers each complete-interface callback, including external effects. `step_retained` gives exact callback equality after private-bookkeeping projection. `program_project` lifts exact callback projection with a supported-state-stable retained parameter through a complete adaptive client. `retained_run` consequently proves exact equality between the projected actual saturated source and its initial retained-cache interpreter. Earlier hybrid cache values need not be consistent with the fixed primitive source.

`replay_larger` proves a different, support-only statement: a supported selective primitive execution replays under any retained table extending its own final bindings, and its initial bindings remain present. `pending_larger` transports that property through the actual enriched primitive compiler. `step_replay` keeps each complete-interface callback and all ambient effects under the final retained table. `program_replay` composes those callback facts using immutable earlier bindings. `complete_replay` instantiates this induction to the actual original full source and its own final table. It derives both initial-to-final cache extension and support of the identical complete result and remaining ambient state under that table's retained view.

The support replay is not a probability equality and supplies no query-cost transport. The exact evaluated retained equality requires the displayed operational stage-at-most-current-depth condition. There is no source-consistency, successful-record, fresh-miss, small-collision or hidden-input premise. No snapshot, persistence or restoration behavior is considered.

`program_stable` composes a lookup-preservation invariant along actual supported callbacks. `final_view` instantiates it to the full saturated source, proving that the final table has the same complete retained lookup as the actual initial table even when new addresses were cached. `final_binding` therefore identifies each actual final cached response with that initial lookup. Consumers must instantiate the actual timing: a substituted child response must already be installed before this law identifies its cache patch. This theorem does not insert an unqueried child into an earlier parent-only table.

### PqxdhInitialParentPrivateObserver

This interpreter models the actual later-parent source by routing only private step aliases. Original initializer lookups and optional returned kernels remain unchanged even when an audited root equals the selected input. Their input and returned-chain candidates are still appended to the same complete candidate ledger. Public HKDF evaluations remain the fixed real source. The ordinary observer, its input list and its direct-disclosure predicate are unchanged.

`old_source` identifies each old private/read/public operation with the established private-only alias interpreter. `external_same` proves that every external and initializer-audit callback equals the original ordinary callback on every branch. `audit_reply` makes the original optional initializer reply explicit, including root aliases. No source experiment is changed by treating an initializer hit as impossible.

`distance` compares the complete flagged partial-routing computation with the same ordinary observer, charging its original final candidate event once. `query_safe` proves exact native/masked callback agreement whenever the callback does not expose the unavailable chain. `event_good` lifts that agreement to the same complete event conjoined with a false disclosure bit. Thus consumers charge masked candidate probabilities and do not assume that guesses remain unlikely after legitimate chain disclosure.

`handler_patch` identifies this interpreter with an exact private table patch while preserving the original initializer. Its displayed parent/child input separation is an operational condition for the equality and remains a separately charged candidate event in the consuming source proof. `compiled_source` instantiates the complete original pending compiler under that private patch; it preserves every optional read and all shared, protocol and root-cache state. It does not assert a whole-source freshness or probability premise.

`compiler_quiet` derives a zero direct-read query bound from each original non-read source callback. `actual_quiet` therefore retains the original flag and entire earlier candidate prefix for every supported callback, including initializer audits. `actual_read` gives the exact original optional native family read, candidate append and sticky disclosure bit. `actual_rules` packages these proved callback facts for the existing full stopped-disclosure induction. No final history correspondence or freshness assumption is supplied by a caller.

These are the source and coupling interfaces for the later-parent ordinary reduction. The final stopped event, source sampler, candidate/resource instantiation and ordered hybrid summation remain consumers. Snapshots and persistence are outside the task.

### PqxdhInitialPreparedParent

The actual audited descriptor-carrying source prefix constructs one common or pending result before any selected full76 predecessor draw. A complete source execution returns its original observed bit. A cached predecessor executes its complete earlier-stage continuation and the same full-state observation immediately. Only an actually absent private-cache entry returns the exact literal descriptor with its complete reached native state and chronological candidate audit. No branch is conditioned away.

collect_real and collect_normalized identify these branches with the original earlier source and the later source normalized only on cached branches. prepare_real and prepare_normalized erase only the extra audit from the actual carried sampler and derive literal oracle-program equations for those two complete games, retaining the same full-state observation. The later unnormalized game still pays NativeAdjacent's actual cached-input collision sum.

collect_pending and supported_pending characterize pending support exactly: the same audited source descriptor/state was reached and its private entry was missing. pending_draw then derives one uniform full76 response for any selected stage beyond the cut depth, from the original source coverage and actual pending support; it preserves the original response, private table, cursor, input log and ambient cache. It does not assume the reached next32 coordinate is independent of an already executed continuation.

prepare_uniform removes the literal resumed suffix of prepare_real. Its cap is (7 + 67 qPost) max(76, qPre, qApplication, qInitial, qSelector, qAux) + qObserve, using the individual actual external callback costs and the same final observation's uniform cost. This is a syntactic oracle-program argument, not resource transport through an evaluated distribution equality. Deterministic local source, primitive, parsing and observation work remains part of reduction runtime. The final source freshness event and missing-parent self-address collision are separate consumers; the observation is not assumed to establish secrecy.

### PqxdhInitialPreparedResources

# Exact prepared-source resource consumer

`PqxdhInitialPreparedResources` maps the actual common-or-missing source sampler into the supported continuation carrier. It uses `RawCtxSupportedSample.sum`, which adds proof certificates by recursion over the original finite oracle program. This changes no query or reply, performs no runtime support test, never conditions away common branches and never reconstructs a descriptor by inverting a function. `pending` consumes the exact `PreparedParent.supported_pending` equivalence and retains the identical descriptor and reached audited state.

`sample_erase` proves the literal original prepared program is recovered by removing only those proof fields. `sample_run` extends that equation to any original common/pending continuation. The source state, optional effects, successful-publication trace, missing-cache condition and already-computed common Boolean are unchanged.

`sample_uniform` consumes the original all-reply post bound and actual separate external callback costs. Its complete bill is `(7+67*qPost)*max(76,qPre,qApplication,qInitial,qSelector,qAux)+qObserve`. The final original observation's cost remains explicit, including on common branches. This is a query-syntax argument; it does not move a resource bound through equality of evaluated distributions. The actual retained initializer supplies `qInitial=32` through `AuditedResources.retained_callbacks`.

`sample_missing` proves every supported pending output still has its actual absent parent entry. In particular, merely inhabiting the broader carried-support subtype is not taken as evidence of a miss. The actual prepared sampler supplies the stronger fact.

`pending_resources` directly consumes `SupportedCertificate` for this exact source carrier. The ordinary observer's source/checker callback cap is `2*(255+67*qPost)+(remaining+1)`, and its uniform cap is that number times the explicit stopped observer callback cap. Its candidate cap is the actual initial saved disclosure count plus `qPost`, initial audit length, `3*(7+67*qPost)`, and three times the stopped callback count. The descriptor, reached private table with real-HKDF fallback, Shared/N/root cache, earlier initializer service and complete saved-history seed are preserved. No whole-observer cost premise is introduced.

`parent_collision` separately bounds a missing fresh parent's next32 value equaling its own input address. The candidate audit stops before executing the selected parent request, and private earlier inputs need not have been disclosed, so neither fact is assumed. The theorem uses the exact full76 parent sampler following this exact prepared sampler; its probability is at most `2^-256`. It retains the other coordinates of the parent draw and requires no independence from a later real child. The common branch uses a fixed unused address and keeps its original decision. Comparing both source endpoints separately may conservatively pay two copies of this bound. This charge is distinct from the ordinary adaptive candidate/tester terms and needs no additional cryptographic assumption or tester advantage.

The complete source-to-ordinary freshness comparison and finite ordered composition consume these results separately. Primitive, local computation and challenger work remain explicitly accounted by their existing endpoint ledgers; these statements concern the actual random-query and finite candidate-list bills. Snapshot and persistence behavior is outside the task.

### PqxdhInitialPreparedRisk

The seven results bound the actual chronological private-input list at the same full source predecessor cut. scan_length charges every original callback, including failed and repeated derivations, under the original all-reply syntax budget. carried_length retains the exact source descriptor and reached state; supported_length erases only audit instrumentation to obtain the same bound on the supported sampler carrier. These proofs do not infer sequence counts from a possibly cyclic cache walk.

addresses is empty on a common outcome and contains the actual prior private-input log followed by the current unexecuted parent address on a pending outcome. addresses_length derives its length at most initialLogLength + 7 +67*qPost +1. collision_bound averages the checked full76 next-coordinate bound over the entire actual prepared sampler without conditioning. The resulting explicit probability is (initialLogLength +7+67*qPost +1)/2^256. It includes the current parent address even though that address is absent from the earlier executed log.

supported_covered derives that every reached private-cache binding is in the actual chronological log, using only the original initial coverage invariant (derived from the concrete empty state). safe_pending therefore proves actual child-cache absence, parent/child address separation and absence from the executed log outside the charged event. The concrete source experiment starts with initialLogLength zero. A consumer comparing two endpoints may conservatively pay this same explicit probability twice; the proof does not silently discard or freshly resample cached child or self-address cases. No public function is replaced, no primitive security conclusion is assumed and no query cost is transported through a distribution equality.

### PqxdhInitialPrivateCheckedFreshness

The source backend now routes only old private ratchet requests. Its initializer and initializer-audit callbacks retain the original optional kernel even when the initializer input equals the hidden chain. Public HKDF stays real and every original source effect, native optional read, full origin/publication trace and ambient field remains present. PqxdhInitialParentPrivateObserver.actual_rules discharges the complete stopped disclosure invariant from the literal source interface; the actual appended finite checker has no direct-read callbacks and therefore retains that invariant.

For an arbitrary same final full-state gate, actualDecision uses the original byte freshness set consisting of the interpreted returned checker slots plus all supplied earlier ancestors. Prior disclosures and the exact saved source history seed the candidate list. The generic checker proof includes the omitted hidden input. Outside the complete recorded alias event, actual byte freshness equals the target-free proxy with the clear disclosure bit. The first discrepancy is charged only to aliases on clear executions; an actually disclosed hidden input makes original freshness false and is not charged as a compromise probability. Exact native/masked clear-event equality and partial-routing total-variation coupling then give the same factor-three ordinary masked candidate bound.

The ordinary masked observer, its source program, sampler, resource bills and candidate interface remain definitionally those of the existing checked observer. The source-side nativeRun is the corrected partial backend. Parent-address separation is not required for this generic factor-three statement; the concrete source realization must derive its patched private-function correspondence off that separately charged collision. This module does not assert that an arbitrary gate is the final source publication/lineage event: PublishedEvent and the actual source realization supply that connection. Both real and independent full76 child values are covered. Eight actual standard-three guards pass; no runtime or cryptographic assumption changes.

### PqxdhInitialPublishedEvent

The seven statements define the same original source observation for every evolving-chain substitution stage. Gate tests the actual original Boolean result and a successful (owner, sequence) publication carrying the selected installed-session origin. It never infers a session from owner index alone. sourceEvent adds byte-value freshness for the fixed original directional root at sequence minus one under that execution's final retained private-table view, together with explicit earlier ancestors and the complete actual reveal history. source_decision is the unconditioned Boolean form. gate_map proves private kernel interpretation cannot change the original decision or publication transcript.

checked_bound instantiates the proved full stopped/checker freshness comparison with this exact publication gate. It retains every original result field, initializer effect, source history and checker candidate and charges three times the ordinary masked candidate event. The final source consumer must identify the actual checker suffix and earlier ancestors with sourceEvent; no equality of those events is assumed by the primitive game.

callback_lineage lifts the actual selective private callback walk invariant through the complete source interface. Real external preparation, initialization, application, selectors and publication callbacks retain the private table and cursor while preserving all their actual ambient effects. carried_lineage consumes the exact executable original builder/post scan and an initial cursor at the given root with depth zero. Its returned descriptor has the actual earlier cache walk at its reached cursor depth; cached and repeated attempts are retained. No cursor depth is equated with an accepted record counter.

cached_lineage uses an already published positive-sequence cached path and agreement on its existing full responses. That suffices to identify the entire finite original lineage, including the target material key, under the retained comparison interpreter. It does not require equal fallback evaluations at unqueried addresses. The actual source publication theorem supplies the cached path from the real initial64 constructor and complete original builder/post execution.

source_checked_fresh combines that cached response agreement, the actual earlier walk and final cache extension with the literal privately routed checker. It gives the exact original root/record freshness predicate as checker slots plus the original earlier ancestors. The parent-input separation remains explicit because that collision is charged by the full candidate event. All path, extension and response-agreement inputs are operational obligations of the same source execution, supplied by the carried prefix, actual callback and saturated retained-execution consumers. It does not replace those obligations with a final event-equivalence premise. This module therefore fixes the common event and its concrete realization interface; the sampled adjacent bound, actual initializer comparison and finite selection factors are the remaining aggregate consumer.

### PqxdhInitialSourceExperiment

The concrete source experiment fixes the original selected authenticated initializer coordinate, supplied64 response, original consumed-registration builder, complete adaptive post client and selected publication. Every stage retains the original primitive state, private identity state and root cache. The private selective derivation table and chronological log start empty at the actual selected directional root and depth zero. The empty origin trace is populated only by actual successful source publications.

The actual Server kernel is selected from the proved existence result for every typed64 response, not from an assumed successful-initialization condition. server_created proves its actual constructor equation. root chooses the corresponding Server send root or actual complementary Beacon send root through the existing rootFor interface. initial_valid discharges both the source cache-coverage/depth/log invariant and initial cursor-address absence without axioms. run_source identifies each stage literally with the NativeAdjacent full source program. published_cached derives the complete published lineage in the actual final table. published_bound derives number ≤7+67*qPost from the actual send controller and chronological log, without assuming a collision-free or acyclic chain.

The game uses the same original Boolean decision, selected-session publication, full original byte-lineage freshness, earlier ancestors and explicit disclosures at every stage. normalization consumes that very observation and pays the coefficient-one sum over j<7+67*qPost of (j+1)/2^256; all incoming validity conditions are derived from the actual initial state. The theorem is a concrete operational/event and cache-normalization layer, not yet the fresh-child cryptographic comparison, initial64 distribution proof, ordered aggregate or target/session selection reduction. External callbacks are unchanged and their costs remain separate obligations. The retained frontend/trace pair called Snapshot in older APIs is a runtime tuple, not saved storage; restoration and persistence are excluded.

### PqxdhInitialSourcePublication

The four statements start with an empty installed-origin/publication trace and derive the complete source invariant rather than supplying an initialized-path premise. The actual supplied64 constructor is kernelOf false response64; the constructor equality merely identifies its returned Rust kernel. Its zero counter and first-send path are the independently proved actual source facts. The same actual builder retains identity/admission checks, allocation, failed or successful sealing, erase, optional serialization and exact peer installation, and records only its returned successful publication.

builder_invariant establishes both the selected installed Server path and the already cached first publication. It also handles every failure, optional rejection and absent peer without asserting an installation. For a selected Beacon owner the builder does not set an origin. sequence_invariant then executes the same complete adaptive post client, using the actual selected initializer coordinate, retained earlier root and supplied64 response. Its original Beacon finishes establish their own selected origins only through the proved matching-message branch and complete first receive; unrelated owners and all external callback/cache effects remain present.

publication_cached states the resulting fact for any selected owner and actually recorded sequence: its original directional root has a complete executed path in the final source table before a final checker. The Server root is the actual supplied constructor's send half; the Beacon root is the actual retained initializer's native send half. The initial table is arbitrary and need not be empty, but no installed-session origin or earlier publication is invented. This is an operational support theorem, not uniformity, probability or resource transport. The accepted initializer/root experiment still supplies the actual response64 and selected-session metadata; the final secrecy theorem consumes this publication path with its fixed target, lineage event and selection loss.

### PqxdhInitialStoppedDisclosure

The eight statements derive the complete final disclosure invariant for the actual saved first-builder or post-registration continuation. The history accessor selects the literal saved LIVE history inside a record, or the saved frontend history for a finish or first builder. It does not equate arbitrary outer and inner histories. The initial state records all values already disclosed through that actual history and an explicit earlier-disclosure list, followed by the supplied earlier candidate ledger, with the direct-read bit clear.

The family continuation, original first-send completion and all three saved source constructors preserve the invariant through every original callback, erase, optional serialization, publication, finish and adaptive outside client. These intermediate statements use a small operational Rules interface. actual_stopped discharges it with the concrete audited private-alias interpreter and exact native optional reads proved in DisclosureState, so its public statement contains no callback-invariance or final-history premise. The invariant states that every set direct-read bit has an actual disclosed target witness, and every disclosed value is retained in the candidate list whenever the bit remains clear.

The actual optional finite lineage checker contains only private derivation callbacks. Its inputs still append to the candidate list, but it cannot set the adversary-disclosure bit or rewrite the original history. checked_invariant therefore applies to the literal ParentStoppedHop.program after the complete original source execution and its checker, retaining all original result fields, installed-session/publication trace and ambient effects. It does not assert final freshness, target reachability, uniformity, probability bounds or free local work. The next common-event comparison consumes these checked support facts.

### PqxdhInitialSupportedCertificate

# Source-supported stopped observer certificate

`PqxdhInitialSupportedCertificate` constructs the ordinary continuation from a subtype of the actual audited source prefix support. An element contains the literal pending origin-aware descriptor and the complete reached source state. Membership means that this exact pair was returned by the original first-builder/full-post annotated scan. It does not assert a secrecy property, a small bad event, or a final source equality. The subsequent prepared sampler can map its supported missing branch into this subtype without altering any saved field.

`continuation_state` exposes the exact construction. The retained lookup is `ParentTable.view (productionStream source.crypto) reachedStore.table`, preserving every existing response with the original fixed-HKDF fallback. The observer's ambient state is the reached shared primitive state, private identity state and root cache. Its initial list is the values from the exact saved disclosure history followed by the entire chronological reached audit, and its direct-read bit starts false. The record history comes from the actual inner LIVE continuation; finish and first-builder histories come from their saved frontend. Neither the omitted parent next-chain coordinate nor a derived child is inserted into this pre-draw state. All external callbacks are fixed before the parent draw, retaining the earlier initializer root and full64 response as appropriate.

The checked `certificate` definition derives every whole-observer resource obligation. `carried_fits` supplies the original source continuation certificate. `carried_seed` bounds the exact initial list from the actual prefix: initial disclosed-value count plus `qPost`, plus initial audit length, plus `3*(7+67*qPost)`. The seven callbacks belong to the actual first builder and the sixty-seven bound covers each attempted original post request. Every callback's separately stated uniform cost remains explicit. The checker has exactly the supplied finite remaining depth and contributes `remaining+1` private derivations. There is no arbitrary reached-state budget or whole-protocol resource premise.

`certificate_bills` states the computed totals: the stopped compiled source and checker use at most `2*(255+67*qPost)+(remaining+1)` callbacks; their uniform bill is that count times the explicit observer callback cap; and their candidate bill is the computed initial-list bound plus three times that callback count. These are conservative bounds over every reply, including failure branches and repeats.

`observer_resources` consumes the checked certificate to bound the actual ordinary stopped observer and every supported final candidate list. It includes the complete original full-post continuation and the appended finite lineage checker, not merely a LIVE suffix or a successful-operation path. Local deterministic computation is not counted as free computational work: this result states the random-query and finite-list bills, while the existing primitive endpoints separately count Extract, HMAC, CCA and tester evaluations.

The actual prepared sampler and its whole-program random cost remain a source consumer of this module. Supported pending cuts here include cache hits as well as misses; the prepared sampler must select the proved missing branch before drawing a fresh parent. The final byte-freshness/publication event and ordered hybrid composition remain separate consumers; this module does not infer an end-to-end conclusion from its resource certificate. Snapshots and persistence are outside the task.

### PqxdhInitialNativeParentChecked

The six results in `PqxdhInitialNativeParentChecked` identify the actual partial observer's native byte-freshness decision with its original stopped source result and the literal finite checker trace. `trace_project` proves that candidate logging and the sticky disclosure bit do not affect original callback replies or state. It is used only for observations that do not inspect that instrumentation.

`checker_step` and `checker_source` evaluate the exact private checker through the partial-routing backend; original initializer callbacks remain unchanged. `native_projection` retains the complete original source result, all returned checker slots and all ambient fields after removing only candidate/flag bookkeeping. `observation` specializes that equality to arbitrary observations of the original result and checker slots. `decision_source` instantiates the actual original publication gate and full byte-value freshness predicate, including earlier ancestors and the full original disclosure history, and identifies it with `NativeParentEvent.nativeDecision` on the reconstructed native source result.

This projection does not discard a candidate or disclosure condition from the security comparison. The separate checked-freshness theorem uses the complete instrumented run and charges its masked candidate event; the decision proved here does not inspect those private bookkeeping fields. No source cache is projected on the basis of a distribution equality, no initializer alias is routed to a different response, and no resource bill is inferred from the operational equality.

### PqxdhInitialNativeParentChild

The three results in `PqxdhInitialNativeParentChild` preserve the exact actual post-parent cache when an early child response is installed. `child_view` proves that the two actual cache insertions equal the retained parent lookup over a private child patch; every other prior address is unchanged. Parent/child address separation is explicit.

`frame_compiled` instantiates the complete original native parent continuation with that child patch and proves equality to the material-only partial observer. The entire original result, role family, disclosure history and origin trace are reconstructed, and all Shared, auxiliary and initializer-cache effects remain. The original initializer replies are preserved, including root-input aliases. `retained_compiled` combines the actual post-parent cache view with the original full retained interpreter, so an early-child comparison uses the same complete stopped source and ambient state.

These are exact operational source equations. They do not finish the randomized child source-event consumer: the source final-table freshness must still be observed through the appended cached native checker before projection, split at the actual prefix walk, and joined to the ordinary stopped comparison. Cached-child and parent-address cases remain separately charged by the source-derived collision bound. No additional theorem or resource transfer is inferred from this checkpoint.

### PqxdhInitialNativeLineageCheck

The complete original source observation may inspect its own final private cache to compute byte-level lineage freshness. Projecting that cache before observing it would lose necessary information. This module appends the existing finite native checker to the literal original private-query program after the adversary has stopped, returns its complete lineage in the program result, and then projects only completed private bookkeeping.

The forwarding compiler emits the actual ratchet request address and decodes its actual full76 response. Under a fixed retained view, the checker computes exactly RawCtxPublishedLineage.step and its finite trace while leaving all ambient fields unchanged. Under the mutable selective handler, its Cached condition requires every queried address to have the full retained response already present. The cached theorem proves the literal computation preserves the entire original private table and ambient state; the private cursor may advance and is projected. No claim is made that matching cache-hit queries preserve that cursor.

walk_cached discharges this operational condition from the existing concrete cache walk for n+1 derivations. Its proof splits the actual finite walk at the first response and recurses through the same next32 coordinate. The condition is thus usable with the original successful-publication cached-path theorem. It imposes no assumption on unqueried addresses, no absence of aliases, no secrecy assumption and no final event equality premise.

appended_cached retains the complete original result and all ambient state, and identifies the gated checker result with the original source's own final-table lineage. A false gate appends no query. appended_retained identifies the same program under the early patched retained view. appended_uniform applies the independently checked deferred single-draw theorem to this complete extended program. Its exact evaluated equality therefore retains the lineage observation that was previously unavailable after projecting the source table. The only operational premises are the actual selected cache miss and the supported original publication gate's already executed cache walk; consuming source theorems must derive both.

The checker makes at most n+1 private requests on all replies; the extended program has the separately stated original-client budget plus n+1. These are analysis/reduction requests after the original client, not network messages or user-visible reveals. No source query cost is transported through the evaluated distribution equation. The ordinary reduction may retain its separately billed suffix checker after the existing cached-prefix decomposition. The logged_uniform theorem instantiates the generic comparison with the exact full NativeLog compiler and every original external callback. Its internal logged_flat lemma is a literal complete-state program equation, and support_map derives the required cache witness directly from supported original source executions. The result retains the entire original frontend result, gated lineage, Shared state, private auxiliary state and root cache; no caller-provided representation or support correspondence is needed.

All eleven declared guards allow only propext, Classical.choice and Quot.sound. Snapshot, persistence and restoration are excluded.

### PqxdhInitialHalfObserver

PqxdhInitialHalfObserver interprets the dedicated first-half audit compiler while retaining the full shared, private and initializer-cache state. Unlike the later-parent observer, it accepts actual optional Slot kernels from the initializer unchanged; matching selected initializers can therefore preserve the unavailable initial half before their first receive. The ordinary interpreter takes the challenge child output and available private context but no unavailable chain bytes. Its public HKDF view is the original real source view.

The exact callback and whole-program source equations preserve all original pending primitives, native optional reads, external callbacks and initializer replies. Initializer audits append the actual input and available known chains, at most three candidates. Only a read of the unavailable chain sets the direct-disclosure flag. Native and masked readers have the same complete event probability on the clear-bit event, without conditioning, retries or a compromise-probability term.

These six equations are operational and read-mask components of the first-half proof. The actual initializer is supplied by PqxdhInitialHalfInitializer. Private byte aliases, original final freshness and the full first-builder/post source game remain explicit later consumers; this module alone does not claim first-half secrecy.

### PqxdhInitialHalfPrivateObserver

PqxdhInitialHalfPrivateObserver supplies the mathematical byte-alias interpretation of the ordinary first-half observer. Only the old private ratchet interface routes matching available chain inputs to the selected child. Every original external callback and the initializer audit returns its original optional Slot kernel, including when an initializer input equals the unavailable chain. The full initializer input and its available known chain outputs remain in the same candidate ledger.

The full flagged execution differs from its ordinary counterpart by at most that ordinary final candidate event. Native and masked reads agree on the same unconditioned clear-bit event. Private handler equality with the actual patched table retains an explicit parent-address separation condition; the first-half sentinel consumer discharges it from literal domain inequality, rather than assuming fresh chain bytes. The whole pending-program source equation preserves every initializer reply and all shared, private and cache effects.

The original non-read source callbacks compile to zero direct-disclosure queries, and the actual read callback returns the native optional value while recording the original available candidates and hidden-chain disclosure flag. These concrete callback laws discharge PqxdhInitialDisclosureState.Rules for the actual first-half interpreter, including initializer callbacks. No final freshness equivalence, runtime support test or forbidden-read probability is assumed. The actual whole-source first-half game and its published-record freshness remain required consumers.

### PqxdhInitialHalfSourceMap

PqxdhInitialHalfSourceMap proves the complete original post representation equation for a first-half initializer. The ordinary side keeps the actual optional known/hidden initializer kernel unchanged. The native side interprets that same reply at the selected half; concrete_initial identifies this callback with PqxdhInitialNativeInitializer using the exact original selected/known root service and full ambient cache, with no supplied callback-compatibility premise.

The step and whole adaptive program equations preserve all record operations, original optional native reads, external selectors and every attempted Beacon finish. Successful finish installation and publication metadata are computed by the actual source compiler on both sides. The proof interprets only private chain fields and retains full role state, original reveal history, registration controls, consumed-state fields, shared effects, private ambient state and root cache. Record routing uses the existing exact retained-parent source equations; initializer mapping is the first-half mapping rather than conversion to known labels.

This module closes the full post representation component. It does not yet provide the original firstbuilder prefix map, the whole first-half disclosure/freshness comparison, the source stage0-to-stage1 probability bound, or the completed ordered evolving-chain theorem. Those remain unfinished at the requested pause. The generic post equations expose their original initializer program explicitly, and concrete_initial discharges the actual selected service specialization; they do not assert a security property for arbitrary callbacks.

### Requested pause

All completed work at the pause is preserved in this topic checkpoint. The common supported observer/resource view, final real/random adjacent source comparison, whole first-half builder/freshness comparison, initial64/authenticated-root composition and final finite ordered reduction remain unfinished. The full cached-lineage deferred-draw equality is proved, but its final source/partial-observer consumer has not been assembled. The composition branch and vcvio are unchanged.
