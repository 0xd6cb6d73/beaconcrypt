# Current-field registration disclosures

This checkpoint extends the executable one-Server/many-Beacon registration schedule with explicit reads of current Beacon fields. It proves an operational interface and complete-state correspondence. It does not claim that a disclosed target remains fresh or secure. The native Server's internal identity/DH use is still an explicit source macro; multi-Server imported pending handles and the final global secrecy/authentication reductions remain separate work.

## Exact exposed fields

A request contains an owner-list address and one of five field names. A missing owner returns `None`. Present owners return a typed value with the following exact scope.

| Field | When readable | Actual value |
| --- | --- | --- |
| Identity | Every phase | Current native identity seed, including its Ed25519/X25519 joint use |
| KEM | Fresh, FreshWithCoins, InitSent | Current KEM secret at that owner's exact generated private slot |
| Prekey | Fresh, FreshWithCoins, InitSent | Current private prekey scalar |
| One-time | FreshWithCoins, InitSent | Current private one-time scalar |
| Kernel | Established | Entire current ratchet kernel, including both current chains and current skipped-key cache |

A whole-kernel disclosure is intentionally broad: the theorem does not pretend that current-chain compromise protects descendants. The interface has no saved-state operation and does not reconstruct erased roots, prekeys, one-time keys, KEM secrets or prior chain material. A transient root reveal, narrower individual chain/skipped-key reveals, and a freshness monitor consuming all public compromise requests belong to later experiment construction. Current local-field reads make no primitive-service request, so their disclosure must be tracked at this explicit public interface rather than inferred from the private primitive histories alone.

`PqxdhRegistrationJointLiveRead.entryClient` checks the current encoded owner phase before any KEM reveal. The old key may remain in the interpreter-private analysis pool, but an Established or Aborted owner emits no KEM service request and returns `None`. Identity reads query the exact generated identity handle; KEM reads query the exact handle currently carried by the live phase. No equality of public bytes is used to identify either private slot. The returned values are actual secrets under this explicit compromise capability, not secret values silently inserted into unrelated adversarial requests.

## Seven field correspondence statements

`entry_source` proves equality of the actual private-service execution and a native current-field projection with the complete updated private pool state. The representation premise is the previously generated exact-slot ownership invariant, and it does not restrict whether a caller may compromise a target. `entry_value` proves the reply depends only on the actual current native field; `entry_slots` proves every private seed and KEM pair is unchanged while the exact service disclosure histories can grow.

`read_source` lifts this equality through owner lookup, the complete service backend and all encoded owners/shared state. Missing addresses are included. `read_owned` preserves the representation invariant for all owners, allowing arbitrary subsequent operations. `read_projection` erases only private service annotations and gives the literal native current-field read with unchanged complete protocol state. `erased_client` proves that an unavailable current KEM handle yields a pure rejection, with no lookup or history append even when an older pool slot exists.

## Six adaptive schedule statements

`PqxdhRegistrationJointRevealSchedule.Spec` is the sum of the original nine-class scheduling interface and the new addressed field reads. No original request or optional outcome is removed. `query_source` and `query_owned` join the original handlers and disclosures in one stateful experiment. `program_source` then proves the complete encoded execution equal to its source distribution for an arbitrary adaptive OracleComp program, including its full continued computation and all intermediate states.

`generated_source` starts with an empty owner registry and discharges every slot premise through actual construction and supported transitions. It has no caller-supplied honest-target, successful-finish or no-compromise premise. `query_projection` and `program_projection` separately prove that forgetting the private annotations yields the entire native schedule with its literal current-field reads. These are equalities of full programs and states, not marginal key-distribution equalities or a cryptographic hybrid hop.

## Eight resource statements

`PqxdhRegistrationJointRevealCosts` extends the source partition to fourteen coordinates: the original nine, followed by identity, KEM, prekey, one-time and kernel disclosure attempts. All caps quantify over every possible typed reply. Missing addresses, erased fields and failed original requests remain counted as attempts.

`entry_bound`, `read_bound`, `query_bound`, `cost_total` and `program_bound` give the emitted-service ledger. All previously proved totals remain unchanged: at most `qCreate` identity births and KEM births, `3*qBundle` signing requests, `qFinish` logical decapsulations and joint DH requests, `56*qFinish` native-tail calls, and `qCoin + 32*qCreate + 32*qBundle` directly emitted uniform calls. Original accept/build/HMAC/hash/Server-kernel-read macro requests keep their respective source-attempt caps. The formerly unused private `other` class now has allowance `qRevealIdentity + qRevealKem`; actual emitted requests in this extension are the two explicit private reveal constructors. Prekey, one-time and kernel reads emit no backend request. This bound is about oracle calls, not local computation time.

`query_uniform`, `program_uniform` and `uniform_bill` preserve the full separately evaluated source bill:

```text
qCoin + (64+G)*qCreate + 32*qBundle + (96+E)*qAccept
  + 64*qBuild + 69*max(64,D)*qFinish + 64*qHmac + 64*qHash
```

`G`, `E` and `D` include the declared interpreted KEM/base uniform work. Every current-field read consumes zero random samples, which does not declare its local computation free. Native macros retain their real implementation and complete shared-state effects; they are not new primitive security assumptions. Server/runtime initialization is still separately charged outside this typed scheduling interface.

## Review and integration status

All three modules have direct Lean 4.34 checks and 21 exact standard-axiom guards. Independent semantic review approved this frozen checkpoint without findings; central integration remains pending. No Rust, ProVerif, primitive implementation, persistence or serialization implementation changed. The final common experiment still needs freshness/selection monitors, Server-side joint-service compilation, the remaining cryptographic hybrids and their global losses. Existing downstream `noCreate`/`noSign` restrictions are not silently removed by this operational result.
