# Actual registration encapsulation cut and ordinary KEM reduction

Status: 18 modules and 72 statements pass final focused Lean checks with exact standard-axiom guards; independent semantic review approved the scoped result with no findings. This is a bounded, filtered KEM hop for the actual registration command compiler. It does not close the global computational/symbolic proof.

## Result and source boundary

The executable reduction now stops immediately before an actual Server encapsulation request and resumes the literal remaining source callback with the ordinary ML-KEM challenger's ciphertext and candidate shared secret. The hook records the original caller-supplied raw registration bytes and the actual verified PQ public key passed to encapsulation. It preserves the preceding parsing, three signature verifications, freshness/reservation work and ephemeral generation, and retains the complete subsequent native/owner continuation. It does not reconstruct a desired accepted transcript or assume that the selected candidate belongs to an honest owner.

Interpreting the hook with the existing real encapsulator recovers the complete original command program. Scanning to any ordinal occurrence and then finishing that exact callback also recovers the complete original program, including early completion and unsuccessful attempts. These are equalities of complete oracle programs, not equalities of marginal public keys or selected successful results.

The backend is the previously checked one-Server/many-Beacons source14 registration interface. Its native root service still uses the previously documented restricted Extract-ROM analysis backend. The present KEM hop changes neither that service nor the production HKDF contract. Connecting the resulting exact 192-byte root input and continuation to the corrected secret-input Extract/HMAC games remains a separate obligation. Source14 is not a claim to cover every Rust API method; raw constructor rejection, new one-time-key APIs, deletion and full record scheduling remain outside this command surface.

## Exact experiment and reduction

`KemChallenge.pre` runs the actual Server constructor, samples all `n` unselected KEM reservations and runs the original adaptive command compiler until the selected zero-based encapsulation occurrence. The selected creation position lies in `Fin (n + 1)`. Only the selected public key enters this executable prephase. The selected secret appears exclusively in the mathematical ordinary CCA/source interpreters. Other locally generated pairs remain in the saved context, together with actual constructor origin, complete runtime/native state, both private-service histories and the literal pending callback.

A failed constructor, a selected-KEM reveal stop, completion before the requested occurrence or a pending request whose actual PQ field differs from the challenge public key is inactive in the filtered decision experiment and returns false. A later selected-KEM reveal also stops the continuation and returns false. These are explicit restrictions of this intermediate event, not assertions that such behavior cannot occur. The full inactive or stopped context is retained before projecting the final Boolean decision. Active executions return only the original source client's Boolean decision.

The postphase supplies exactly the source optional ciphertext/shared-secret pair built from the ordinary challenge ciphertext and candidate bytes. Every later public encapsulation remains real. The existing post router answers an exact selected challenge-ciphertext request using the supplied candidate and never forwards that ciphertext to the blocked CCA oracle. All permitted other ciphertexts and other-key work keep their original routing and histories. Equality with the real stopped source uses ordinary recipient correctness on the actual key-generation and encapsulation supports and the existing functional-decapsulation implementation contract.

`KemCertified.adversary` is the constructed ordinary one-key IND-CCA adversary. Its advantage is exactly the distance between `KemGame.sourceReal` and `KemGame.branch false`, with coefficient one. Both fixed branches include the ordinary challenger's selected key generation, one encapsulation and one branch-independent uniform shared-secret draw, including inactive selections. Initialization failures and early completion therefore do not make this challenger work free.

The source-order reservation interchange and creation-index correspondence remain the preceding `KemInitialization` and `KemCommands.selected_source` results. Comparing this reserved experiment to an unrestricted source run requires the stated room condition `qCreate ≤ n + 1`. The present statement has no public-key injectivity, cross-key secret uniqueness, honest-target, latest-successful-bundle or successful-accept premise. The original private seed correlation for Ed25519/X25519 remains within the existing exact joint-identity interface.

## Saved-context certificates

A raw pending callback is an arbitrary oracle program at the type level. A finite postchallenge resource claim cannot quantify over all such values merely because real executions are bounded. `KemCertified` instead uses `RawCtxSupportedSample.certify` to attach a proof that the actual returned context belongs to the support of the exact executable prephase at its recorded public challenge key.

This support is structural over arbitrary ordinary challenger replies and arbitrary public keys. It is not only support under honest generated keys or the real branch. The annotation is forward recursion on the same finite oracle program. Erasing it restores the exact original syntax, including every query and reply branch. It performs no runtime support test, conditioning, rejection sampling or inverse search for a prior state.

`KemCutSupport.successful_support` transports successful optional-router results back to the literal source scan. `KemCutBounds.residual` then supplies a bound for every possible reply to the saved encapsulation callback, including failure. `KemSavedBills.saved` derives all four saved resource certificates from the actual source command budget. Consequently the ordinary adversary's postphase bounds quantify over every value of its declared saved-context type and every ciphertext/candidate reply without an additional ambient budget hypothesis.

## Query accounting

Write `qCreate = budget (.inl 1)`, `qBundle = budget (.inl 2)`, `qAccept = budget (.inl 3)` and `qFinish = budget (.inl 5)`. The other source coordinates retain the existing public coin, build, HMAC, hash and two live-read allowances. Primitive resource contracts are `KemCaps`/`KemBound`; they bound ordinary primitive query counts and the full cost of interpreting base callbacks. No primitive implementation is proved. These are oracle-query bounds; they do not establish a total polynomial-time bound for arbitrary pure adversary computation or runtime callbacks.

The source command compiler retains at most `qCreate` identity creations and KEM creations, `3*qBundle` signing calls, `qFinish + qAccept` private static-DH calls, `qFinish` logical decapsulation attempts and the previous live-read cap. It exposes at most `qAccept` encapsulation requests. These statements hold for every typed callback reply, including replacement replies, repeated equal public keys and failures.

Let `E = caps.encapsCost`, `G = caps.keygenCost`, `Dᵤ = caps.decapsUniform`, `Dᵦ = caps.decapsBase`, and let the previous complete native uniform allowance be:

```text
U = qCoin + 32*qCreate + 32*qBundle + (96 + E)*qAccept
    + 64*qBuild + 3584*qFinish + 64*qHmac + 64*qHash
    + qIdentityRead + qKemRead
V = 32*qCreate + (U + E*qAccept) + Dᵤ*qFinish
```

The exposed compiler keeps the old `U` as a conservative bound even though the hook itself draws no coins. Interpreting earlier or later real encapsulations adds `E*qAccept`. This deliberate overestimate retains both allowances; it does not assert that the exposed hook performs the old encapsulation work twice.

`KemReductionBills.adversary_bound` establishes the following separate ordinary client caps:

| Resource | Prechallenge | Postchallenge |
| --- | --- | --- |
| Uniform requests | `qInit + 32*g + G*n + V` | `V` |
| External base requests | `Dᵦ*qFinish` | `Dᵦ*qFinish` |
| Logical CCA decapsulation requests | `qFinish` | `qFinish` |

Here `g` is one for a generated Server identity and zero for caller-supplied identity material. The prephase charges initialization even on failure and all `n` local reservations even if unused. Selected challenger key generation, its encapsulation and the ghost uniform draw are additional challenger work. Local encapsulation/base work already interpreted into public uniform operations is distinguished from direct external base requests of local decapsulation; neither is free.

The separate phase caps conservatively give at most `2*qFinish` logical reduction requests and `2*Dᵦ*qFinish` external base requests. The original source budget remains `qFinish`; this cohort does not claim a tight shared residual counter across phases. Signing is still bounded by `3*qBundle` in the source compiler; the KEM reduction runs that joint-identity work locally and does not acquire a new signature oracle assumption.

`KemCutSelection.source_occurrence` proves that every reached pending source cut has an occurrence index below `qAccept`. This identifies a finite selection family. No creation-index, session or occurrence-selection multiplier is yet applied: the exact coefficient-one equality is for each fixed filtered selection. The later global event decomposition must justify its selection factors and freshness rules.

## Checked statements

The following table explains every module's statements. `PqxdhRegistrationJoint` is omitted from filenames.

| Module | Statements | Meaning |
| --- | --- | --- |
| `KemEncapsulation` | `forward_actual`, `prefix_query`, `prefix_program`, `prepare_actual`, `lift_actual`, `accept_actual`, `query_actual`, `program_actual`, `commands_actual` | Real interpretation of the exposed hook preserves every complete source callback, program and native/owner result. |
| `KemCut` | `scan_target`, `scan_prior`, `scan_other`, `scan_finish`, `commands_cut` | Stop before the exact ordinal request, execute earlier requests in place and recover the whole source by resuming. |
| `KemChallenge` | `pre_source` | The initialized public-key-only prephase equals the complete stopped source interpretation. |
| `KemResume` | `post_source`, `supported_source` | The exact candidate reply resumes the saved source and agrees with the real source under ordinary supported correctness. |
| `KemGame` | `branch_source`, `branch_real`, `advantage` | The explicit filtered source branches are those of the constructed ordinary one-key KEM adversary. |
| `KemExposedCounts` | `forward_bound`, `lift_no_encapsulation`, `prefix_step`, `prefix_bound`, `accept_bound`, `backend_step`, `command_bound` | Only actual Server accept calls can expose encapsulation, with total cap `qAccept`. |
| `KemExposedPrivate` | `lift_bound`, `prefix_step`, `prefix_bound`, `prepare_bound`, `accept_bound`, `backend_step`, `backend_program`, `command_bound` | Every old private service cap survives arbitrary encapsulation replacement replies. |
| `KemExposedUniform` | `lift_bound`, `prefix_step`, `prefix_bound`, `prepare_bound`, `accept_bound`, `backend_step`, `command_bound` | Full native uniform work retains its previous conservative bound on all states and replies. |
| `KemCutBounds` | `bind_prefix`, `actual_bound`, `scan_bound`, `residual` | Bound the scan and each actual saved continuation, charging interpreted encapsulations. |
| `KemCertified` | `prefix_erase`, `branch_erase`, `advantage` | Forward support annotation preserves the complete ordinary game and its coefficient-one reduction. |
| `KemCutSupport` | `successful_support`, `pre_bound` | Transport the exact executable prephase support to the original pending callback. |
| `KemProgramBills` | `creates_class`, `decaps_class`, `count_private`, `commands` | Relate source classes to router classes and supply all four actual source resource certificates. |
| `KemCutInterpreted` | `encaps_private`, `encaps_uniform`, `actual_bills`, `scan_bills` | Preserve private caps and charge real local encapsulation work during scanning and resumption. |
| `KemSavedBills` | `saved`, `pending` | Every declared saved adversary context has source-derived bounds for every candidate reply. |
| `KemPostBills` | `post_bound`, `adversary_post` | Bound complete postchallenge work on every valid context and arbitrary challenger reply. |
| `KemPreBills` | `scan_bills`, `uniform`, `excluded`, `decapsulations`, `base` | Include constructor, reservation, source scan and complete prechallenge routing costs. |
| `KemReductionBills` | `annotated_bound`, `adversary_bound` | Supply the existing ordinary `MakesAtMostQueries` endpoint with the explicit six caps. |
| `KemCutSelection` | `occurrence_lt`, `source_occurrence` | Every actual reached ordinal lies within the finite source acceptance allowance. |

## Remaining composition

The issued-attempt tuple and actual source authentication event must be joined to this exact pending raw candidate and addressed owner. The earlier creation-index/PQ provenance result then supplies unchanged owner KEM routing; attacker-owned candidates and unissued fields remain explicit event alternatives. The complete global schedule needs a justified selection sum and freshness preconditions connecting these filtered decisions to advertised events. The exact saved root input/continuation must be connected to the corrected real-HKDF Extract/HMAC endpoint, evolving chains and adaptive receive games. This cohort supplies neither that final hybrid chain nor the ProVerif computational interpretation by itself.

There are no Rust, codec, primitive implementation, snapshot or persistence changes. No primitive security theorem, custom axiom, runtime guard, new protocol security assumption or selected-secret recovery procedure is introduced.
