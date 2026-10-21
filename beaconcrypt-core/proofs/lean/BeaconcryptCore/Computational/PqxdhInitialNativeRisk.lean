import BeaconcryptCore.Computational.PqxdhInitialNativeCarried
import BeaconcryptCore.Computational.RawCtxFirstParentRisk

/-!
The complete source predecessor sampler charges actual cached hits through its original chronological private-input log. External preparation, initialization, application, selector and publication callbacks preserve that separate private table and cursor. The earlier fresh-coordinate calculation therefore lifts to the same full source execution without resampling a hit or assuming that a selected request misses.
-/
open OracleComp OracleSpec CoreModels Aeneas ENNReal
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhInitialNativeRisk
open PqxdhJointKdf PqxdhJointKdfGame PqxdhInitialNativeLog PqxdhInitialNativePrefix PqxdhInitialBeaconAmbient
variable {ι I D K X Response Shared A N C Result : Type} {extra : OracleSpec ι} {S B : Nat}

def counted : (Spec extra RatchetChain I D K X Response Shared S B).Domain → Prop
  | .inl query => RawCtxSelectiveFamilyLogBounds.privateQuery query
  | .inr _ => False

instance : DecidablePred (counted (extra := extra) (I := I) (D := D) (K := K) (X := X) (Response := Response) (Shared := Shared) (S := S) (B := B)) :=
  fun query => match query with
    | .inl request => inferInstanceAs (Decidable (RawCtxSelectiveFamilyLogBounds.privateQuery request))
    | .inr _ => isFalse id

def Clean (state : State A N C) : Prop := RawCtxFirstParentRisk.Clean state.1

def Valid (depth k : Nat) (state : State A N C) : Prop := RawCtxFirstParentRisk.Valid depth k state.1

set_option backward.isDefEq.respectTransparency false in
/-- Each actual unselected callback preserves private-cache provenance, predecessor depth and the chronological counted-input bound. -/
theorem valid_step (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (depth stage k : Nat)
    (external : QueryImpl (External extra RatchetChain I D K X Response Shared) (Ambient A N C))
    (query : (Spec extra RatchetChain I D K X Response Shared S B).Domain) (state : State A N C)
    (valid : Valid depth k state) (unchosen : selected (extra := extra) depth query state = false)
    (result : (Spec extra RatchetChain I D K X Response Shared S B).Range query × State A N C)
    (supported : result ∈ support ((handler source writer stage external query).run state)) :
    Valid depth (k + if counted (extra := extra) query then 1 else 0) result.2 := by
  cases query with
  | inl query =>
      rw [live_handler] at supported
      simp only [support_map, Set.mem_image] at supported
      obtain ⟨reply, actual, rfl⟩ := supported
      exact RawCtxFirstParentRisk.valid_step source writer depth stage k query state.1 valid unchosen reply actual
  | inr query =>
      rw [external_handler] at supported
      simp only [support_map, Set.mem_image] at supported
      obtain ⟨reply, actual, rfl⟩ := supported
      simpa only [counted, ite_false, Nat.add_zero, Valid, RawCtxFirstParentRisk.Valid, RawCtxSelectiveFamilyLog.Covered] using valid

set_option backward.isDefEq.respectTransparency false in
/-- Every external callback has zero cache-collision risk; each actual private step has only the existing full76 next-coordinate risk from its chronological inputs. -/
theorem callback_risk (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (depth k : Nat)
    (external : QueryImpl (External extra RatchetChain I D K X Response Shared) (Ambient A N C))
    (query : (Spec extra RatchetChain I D K X Response Shared S B).Domain) (state : State A N C)
    (valid : Valid depth k state) (clean : Clean state)
    (unchosen : selected (extra := extra) depth query state = false) :
    Pr[fun result => ¬Clean result.2 | (handler source writer (depth + 1) external query).run state] ≤
      if counted (extra := extra) query then ((k + 1 : Nat) : ℝ≥0∞) * (2 ^ 256 : ℝ≥0∞)⁻¹ else 0 := by
  cases query with
  | inl query =>
      rw [live_handler, probEvent_map]
      exact RawCtxFirstParentRisk.callback_risk_vcvioLegacy source writer depth k query state.1 valid clean unchosen
  | inr query =>
      rw [external_handler, probEvent_map]
      simp only [Clean, RawCtxFirstParentRisk.Clean] at clean ⊢
      simp [Function.comp_def, counted, clean]

/-- The full-interface first-hit scan accumulates only its actual counted source calls, with collision terms indexed by the retained chronological input bound. -/
theorem scan_risk (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (depth k calls : Nat)
    (external : QueryImpl (External extra RatchetChain I D K X Response Shared) (Ambient A N C))
    (client : OracleComp (Spec extra RatchetChain I D K X Response Shared S B) Result)
    (bounded : client.IsQueryBoundP (counted (extra := extra)) calls) (state : State A N C)
    (valid : Valid depth k state) (clean : Clean state) :
    Pr[fun result => ¬Clean result.2 | RawCtxStatefulPendingPrefix.scan (selected (extra := extra) depth)
      (handler source writer (depth + 1) external) client state] ≤
      ∑ j ∈ Finset.range calls, ((k + j + 1 : Nat) : ℝ≥0∞) * (2 ^ 256 : ℝ≥0∞)⁻¹ :=
  RawCtxStatefulScanRisk.scan_risk_vcvioLegacy _ _ counted Clean (Valid depth)
    (fun count => ((count + 1 : Nat) : ℝ≥0∞) * (2 ^ 256 : ℝ≥0∞)⁻¹)
    (fun count query before unchosen valid _ result supported =>
      valid_step source writer depth (depth + 1) count external query before valid unchosen result supported)
    (fun count query before unchosen valid clean =>
      callback_risk source writer depth count external query before valid clean unchosen)
    client calls k bounded state valid clean

section Source
open PqxdhInitialNativeCarried
variable {M P Origin : Type}
variable (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
  (mark : PqxdhBeaconPhase2Shared.Secrets Shared → Origin)
  (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
  (execution : Execution extra M P I D K Result Origin S B)

/-- The complete original consumed-registration builder and adaptive post client supply the concrete source callback cap used in the chronological collision sum. -/
theorem source_risk (depth k qPost : Nat)
    (external : QueryImpl (External extra RatchetChain I D K X Response Shared) (Ambient A N C))
    (bounded : ∀ reply, (execution.outside reply).IsTotalQueryBound qPost)
    (state : State A N C) (valid : Valid depth k state) (clean : Clean state) :
    Pr[fun result => ¬Clean result.2 | RawCtxStatefulPendingPrefix.scan (selected (extra := extra) depth)
      (handler source writer (depth + 1) external) (original source mark sender route decode execution) state] ≤
      ∑ j ∈ Finset.range (7 + qPost * 67), ((k + j + 1 : Nat) : ℝ≥0∞) * (2 ^ 256 : ℝ≥0∞)⁻¹ :=
  scan_risk source writer depth k (7 + qPost * 67) external (original source mark sender route decode execution)
    (PqxdhInitialOriginPost.sequence_total source execution.initial mark execution.origin sender route decode
      execution.index execution.metadata execution.ready execution.outside qPost bounded
      (execution.before, execution.trace)).isQueryBoundP state valid clean

/-- The executable descriptor-carrying sampler pays the same source-derived collision sum while retaining its complete original state and continuation. -/
theorem carried_risk (depth k qPost : Nat)
    (external : QueryImpl (External extra RatchetChain I D K X Response Shared) (Ambient A N C))
    (bounded : ∀ reply, (execution.outside reply).IsTotalQueryBound qPost)
    (state : State A N C) (valid : Valid depth k state) (clean : Clean state) :
    Pr[fun result => ¬Clean (RawCtxForwardScan.pack
      (PqxdhInitialOriginContext.frame (X := X) (Response := Response) mark sender route decode) result).2 |
      carried source writer mark sender route decode execution depth (depth + 1) external state] ≤
      ∑ j ∈ Finset.range (7 + qPost * 67), ((k + j + 1 : Nat) : ℝ≥0∞) * (2 ^ 256 : ℝ≥0∞)⁻¹ := by
  have bound := source_risk source writer mark sender route decode execution depth k qPost external bounded state valid clean
  rw [← carried_pack source writer mark sender route decode execution depth (depth + 1) external state, probEvent_map] at bound
  exact bound

def Cached : Carried extra M P I D K Result Origin A N C S B → Prop
  | .complete _ _ => False
  | .pending context state => state.1.1.2.1 (PqxdhInitialBuilderContext.address context.original) ≠ none

/-- The earliest actual cached predecessor is charged by the full source collision sum; no hit is discarded, resampled or granted a freshness premise. -/
theorem cached_risk (depth k qPost : Nat)
    (external : QueryImpl (External extra RatchetChain I D K X Response Shared) (Ambient A N C))
    (bounded : ∀ reply, (execution.outside reply).IsTotalQueryBound qPost)
    (state : State A N C) (valid : Valid depth k state) (clean : Clean state) :
    Pr[Cached | carried source writer mark sender route decode execution depth (depth + 1) external state] ≤
      ∑ j ∈ Finset.range (7 + qPost * 67), ((k + j + 1 : Nat) : ℝ≥0∞) * (2 ^ 256 : ℝ≥0∞)⁻¹ := by
  apply (probEvent_mono (q := fun result => ¬Clean (RawCtxForwardScan.pack
      (PqxdhInitialOriginContext.frame (X := X) (Response := Response) mark sender route decode) result).2) ?_).trans
    (carried_risk source writer mark sender route decode execution depth k qPost external bounded state valid clean)
  intro result supported bad
  cases result with
  | complete value reached => exact False.elim bad
  | pending context reached =>
      have cases := carried_cases source writer mark sender route decode execution depth (depth + 1) external state reached valid.1 context supported
      have same : PqxdhInitialBuilderContext.address context.original = RawCtxSelectiveChainGame.cursorAddress reached.1.1.2.2 := by
        simpa only [RawCtxSelectiveChainGame.matched, decide_eq_true_eq] using cases.1
      change reached.1.1.2.1 (RawCtxSelectiveChainGame.cursorAddress reached.1.1.2.2) ≠ none
      rw [← same]
      exact bad

end Source

/-- The actual empty selective store starts clean independently of the retained initial chain and other private state. -/
theorem empty_clean (primitive : RawCtxSharedPrimitive.SharedState A) (cursor : RawCtxSelectiveChainGame.Cursor)
    (past : List JointKdfAddress) (privateState : N) (cache : C) :
    Clean (((primitive, ((fun _ => none), cursor)), past), (privateState, cache)) := rfl

end BeaconcryptCore.Computational.PqxdhInitialNativeRisk

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialNativeRisk.valid_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialNativeRisk.valid_step
/-- info: 'BeaconcryptCore.Computational.PqxdhInitialNativeRisk.callback_risk' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialNativeRisk.callback_risk
/-- info: 'BeaconcryptCore.Computational.PqxdhInitialNativeRisk.scan_risk' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialNativeRisk.scan_risk
/-- info: 'BeaconcryptCore.Computational.PqxdhInitialNativeRisk.source_risk' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialNativeRisk.source_risk
/-- info: 'BeaconcryptCore.Computational.PqxdhInitialNativeRisk.carried_risk' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialNativeRisk.carried_risk
/-- info: 'BeaconcryptCore.Computational.PqxdhInitialNativeRisk.cached_risk' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialNativeRisk.cached_risk
/-- info: 'BeaconcryptCore.Computational.PqxdhInitialNativeRisk.empty_clean' does not depend on any axioms -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialNativeRisk.empty_clean
