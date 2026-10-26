import BeaconcryptCore.Computational.PqxdhLaterChallengePrefixMass

/-! Transport the same complete paired source prefixes through the literal completed/cached/missing collector. -/
open OracleComp OracleSpec CoreModels Aeneas OracleComp.ProgramLogic.Relational
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhLaterChallengeCollectorCoupling
open PqxdhNativeSharedPrefix RawCtxForwardScan CtxRomAuth

/-- Split only the native product representation; preserve every local field and its actual ROM cache. -/
def detach {A N C : Type} : PqxdhInitialNativeAudit.State A N C → Local A N C × CtxRO.QueryCache
  | (((((shared, cache), store), inputs), (privateState, roots)), audit) =>
      (⟨shared, store, inputs, privateState, roots, audit⟩, cache)

/-- Recover the original shared result representation from a whole native cut, including complete results. -/
def unrestore {Tag Result A N C : Type} : Cut Tag Result (PqxdhInitialNativeAudit.State A N C) →
    Cut Tag Result (Local A N C) × CtxRO.QueryCache
  | .complete result state => (.complete result (detach state).1, (detach state).2)
  | .pending tag state => (.pending tag (detach state).1, (detach state).2)

/-- The representation split recovers the exact original shared cut and cache, not merely its visible output. -/
theorem unrestore_restore {Tag Result A N C : Type} (result : Cut Tag Result (Local A N C) × CtxRO.QueryCache) :
    unrestore (RawCtxSharedPrefixScan.restore attach result) = result := by
  rcases result with ⟨cut, cache⟩
  cases cut with
  | complete result state => cases state; rfl
  | pending tag state => cases state; rfl

/-- Native reassembly recovers the original full backend state in both cut branches. -/
theorem restore_unrestore {Tag Result A N C : Type} (cut : Cut Tag Result (PqxdhInitialNativeAudit.State A N C)) :
    RawCtxSharedPrefixScan.restore attach (unrestore cut) = cut := by
  cases cut with
  | complete result state => rfl
  | pending tag state => rfl

section Prepared
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
open PqxdhJointKdfGame PqxdhSecretInputKdf PqxdhCorrelatedExpand PqxdhCorrelatedExtractFamily
open PqxdhKemIndCca PqxdhEd25519EufCma PqxdhJointIdentity PqxdhStatefulPhase1EufCma
open PqxdhPhase2GeneratedDriver PqxdhAuthenticatedRootExperiment PqxdhPhase1AcceptanceOracle
open PqxdhPrivateKemSource PqxdhGeneratedBeaconState PqxdhNativeSharedPrefix
open CtxRomAuth AdaptiveCtxSharedHash
variable {ι M P I K X Response A KemSK : Type} {baseSpec : OracleSpec ι} {S B : Nat}
variable {setup : StatefulPhase1Setup baseSpec}
    (original : PqxdhAuthenticatedRootExperiment.Environment setup M P I K X Response A S B)
    (callbacks : PqxdhSourceAuxiliary.Callbacks A)

variable (baseImpl : QueryImpl baseSpec ProbComp) (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes) (primitives : Primitives)
    (secret : KemSK) (challenge : MlKem768Ciphertext)
local notation "env" => PqxdhPreparedSharedPrefix.environment original callbacks
local notation "zeroRoot" => (List.Vector.replicate 32 0 : RootOutput)
local notation "Input" => PqxdhInitialPreparedSourceInput.Input (M := M) (P := P) (I := I) (K := K) (X := X)
    (Response := Response) (A := A) (S := S) (B := B) (setup := setup)
local notation "pre" => PqxdhPreparedPrefixCallbacks.preparation attachedVerify primitives 1 original.source original.localImpl baseImpl kem secret challenge
local notation "application" => PqxdhPreparedPrefixCallbacks.application attachedVerify primitives 1 original.source original.localImpl baseImpl kem secret challenge
local notation "selector" => PqxdhPreparedPrefixCallbacks.selectorLocal (A := A) (PqxdhInitialPendingCurrent.selector attachedVerify primitives 1 baseImpl kem secret challenge)
local notation "aux" => PqxdhPreparedPrefixCallbacks.auxiliaryLocal callbacks

open PqxdhLaterChallengeCapture PqxdhLaterChallengeBuilderCapture

open PqxdhLaterChallengePreparedCapture
local notation "Pending" => PqxdhSharedParentCollect.Pending (SelectorSpec baseSpec) M P (IdentityHandle I) (DhPair setup) (KemHandle K) A (BareState 1) RootOracle.QueryCache S (B + 1)
local notation "Details" => PqxdhLaterChallengeCapture.Details (SelectorSpec baseSpec) M P (IdentityHandle I) (DhPair setup) (KemHandle K) Bool S (B + 1)
local notation "NativeCut" => PqxdhLaterChallengeBuilderCoupling.Outcome (extra := SelectorSpec baseSpec)
  (M := M) (P := P) (I := IdentityHandle I) (D := DhPair setup) (K := KemHandle K) (Origin := Bool)
  (Local := PqxdhInitialNativeAudit.State A (BareState 1) RootOracle.QueryCache) (S := S) (B := B + 1)

/-- The collector on the exact original local/cache representation of this native cut. Its decisions and final cache remain in the output. -/
noncomputable def step (start : Input) (output : HmacBlock) (depth : Nat) (cut : NativeCut) :=
  (simulateQ hashImpl (PqxdhLaterChallengePreparedCapture.collect original callbacks baseImpl kem attachedVerify primitives secret challenge
    start output depth (unrestore cut).1)).run (unrestore cut).2

/-- The literal completed/cached/missing collector does not read the input's outside Post field; that continuation is already stored inside its actual cut descriptor. -/
theorem collect_post (start : Input) (output : HmacBlock) (depth : Nat)
    (owner : RawCtxProtocolReveals.Owner S (B + 1)) (number : U64) (bit : Bool)
    (adversary : PqxdhInitialBuilderContext.BuildResult → OracleComp
      (PqxdhFirstRecordConfidentiality.AdvSpec (SelectorSpec baseSpec) S (B + 1)) Bool)
    (cut : CapturedCut (setup := setup) (M := M) (P := P) (I := I) (K := K) (A := A) (S := S) (B := B)) :
    PqxdhLaterChallengePreparedCapture.collect original callbacks baseImpl kem attachedVerify primitives secret challenge
      (withPost (setup := setup) start owner number bit adversary) output depth cut =
    PqxdhLaterChallengePreparedCapture.collect original callbacks baseImpl kem attachedVerify primitives secret challenge start output depth cut := rfl

/-- The complete original prepared run factors through the same fully reassembled native prefix and the unchanged collector. This retains all final decisions and actual cache state. -/
theorem run_split (start : Input) (output : HmacBlock) (depth : Nat)
    (owner : RawCtxProtocolReveals.Owner S (B + 1)) (number : U64) (bit : Bool)
    (adversary : PqxdhInitialBuilderContext.BuildResult → OracleComp
      (PqxdhFirstRecordConfidentiality.AdvSpec (SelectorSpec baseSpec) S (B + 1)) Bool) (cache : CtxRO.QueryCache) :
    (simulateQ hashImpl (PqxdhLaterChallengePreparedCapture.run original callbacks baseImpl kem attachedVerify primitives secret challenge
      start output depth owner number bit adversary)).run cache =
      (RawCtxSharedPrefixScan.restore attach <$> (simulateQ hashImpl
        (capturedPrefix original callbacks baseImpl kem attachedVerify primitives secret challenge start output depth owner number bit adversary)).run cache) >>=
        step original callbacks baseImpl kem attachedVerify primitives secret challenge start output depth := by
  simp only [PqxdhLaterChallengePreparedCapture.run, simulateQ_bind, StateT.run_bind, bind_map_left,
    step, unrestore_restore, collect_post]

/-- A pending collected result is the same full native cut, including its original descriptor, local state and reached ROM cache. Completed and cached decisions cannot manufacture such a result. -/
theorem step_pending (start : Input) (output : HmacBlock) (depth : Nat) (cut : NativeCut)
    (pending : Pending) (details : Option Details) (after : CtxRO.QueryCache)
    (supported : (Sum.inr (pending, details), after) ∈ support
      (step original callbacks baseImpl kem attachedVerify primitives secret challenge start output depth cut)) :
    cut = .pending (pending.1, details) (attach pending.2 after) := by
  have same := PqxdhLaterChallengeSampleChronology.collect_evaluated original callbacks baseImpl kem attachedVerify primitives secret challenge
    start output depth (unrestore cut).1 pending details (unrestore cut).2 after supported
  calc
    cut = RawCtxSharedPrefixScan.restore attach ((unrestore cut).1, (unrestore cut).2) := (restore_unrestore cut).symm
    _ = _ := by rw [same.1, ← same.2]; rfl

/-- A genuine missing-address collector returns the exact pending descriptor, local state and unchanged actual ROM cache. -/
theorem step_missing (start : Input) (output : HmacBlock) (depth : Nat)
    (context : PqxdhInitialOriginContext.Context (SelectorSpec baseSpec) M P (IdentityHandle I) (DhPair setup) (KemHandle K) Bool Bool S (B + 1))
    (details : Option Details) (state : Local A (BareState 1) RootOracle.QueryCache) (cache : CtxRO.QueryCache)
    (missing : state.store.1 (PqxdhInitialBuilderContext.address context.original) = none) :
    step original callbacks baseImpl kem attachedVerify primitives secret challenge start output depth
      (.pending (context, details) (attach state cache)) = pure (Sum.inr ((context, state), details), cache) := by
  simp only [step, unrestore, detach, attach, PqxdhLaterChallengePreparedCapture.collect,
    PqxdhPreparedSharedParent.collect, PqxdhSharedParentCollect.collect, PqxdhLaterChallengeCapture.cutMap]
  rw [ite_eq_left missing]
  rfl

/-- Every cached-address continuation keeps its actual Boolean decision and reached cache; none of its outcomes is relabelled as a pending descriptor. -/
theorem step_cached (start : Input) (output : HmacBlock) (depth : Nat)
    (context : PqxdhInitialOriginContext.Context (SelectorSpec baseSpec) M P (IdentityHandle I) (DhPair setup) (KemHandle K) Bool Bool S (B + 1))
    (details : Option Details) (state : Local A (BareState 1) RootOracle.QueryCache) (cache : CtxRO.QueryCache)
    (cached : state.store.1 (PqxdhInitialBuilderContext.address context.original) ≠ none)
    (result : (Bool ⊕ (Pending × Option Details)) × CtxRO.QueryCache)
    (supported : result ∈ support (step original callbacks baseImpl kem attachedVerify primitives secret challenge start output depth
      (.pending (context, details) (attach state cache)))) :
    ∃ decision, result.1 = Sum.inl decision := by
  have logical := PqxdhFirstRecordStopTagged.support_state_simulation hashImpl _ cache result supported
  simp only [unrestore, detach, attach, PqxdhLaterChallengePreparedCapture.collect,
    PqxdhPreparedSharedParent.collect, PqxdhSharedParentCollect.collect, PqxdhLaterChallengeCapture.cutMap,
    ite_eq_right cached, map_bind, map_pure, mem_support_bind_iff, mem_support_pure_iff] at logical
  obtain ⟨_, _, same⟩ := logical
  exact ⟨_, same⟩

/-- Completed or post-admission native outcomes remain explicit in the collector comparison. -/
def Late : NativeCut → Prop
  | .complete _ _ => True
  | .pending (_, details) _ =>
      PqxdhLaterChallengeSavedClassification.phase details = .inside ∨
        PqxdhLaterChallengeSavedClassification.phase details = .used

/-- Complementary collector outcomes retain their actual decision and cache or their full post-admission pending state. -/
def Residual (result : (Bool ⊕ (Pending × Option Details)) × CtxRO.QueryCache) : Prop :=
  match result.1 with
  | .inl _ => True
  | .inr (_, details) =>
      PqxdhLaterChallengeSavedClassification.phase details = .inside ∨
        PqxdhLaterChallengeSavedClassification.phase details = .used

/-- Reassemble only an actual pending result; a completed/cached decision remains absent. -/
def pendingView (result : (Bool ⊕ (Pending × Option Details)) × CtxRO.QueryCache) : Option NativeCut :=
  match result.1 with
  | .inl _ => none
  | .inr (pending, details) => some (.pending (pending.1, details) (attach pending.2 result.2))

/-- The complete collector outputs retain either their paired original pending cuts or both complete/post-admission residual outcomes. -/
noncomputable def Related (owner : RawCtxProtocolReveals.Owner S (B + 1)) (number : U64) (first second : Bool)
    (adversary : PqxdhInitialBuilderContext.BuildResult → OracleComp
      (PqxdhFirstRecordConfidentiality.AdvSpec (SelectorSpec baseSpec) S (B + 1)) Bool)
    (left right : (Bool ⊕ (Pending × Option Details)) × CtxRO.QueryCache) : Prop :=
  (∃ leftCut rightCut, pendingView left = some leftCut ∧ pendingView right = some rightCut ∧
    PqxdhLaterChallengeBuilderCoupling.Related owner number first second adversary leftCut rightCut) ∨
      (Residual left ∧ Residual right)

/-- The literal collector keeps every full completed/post-admission outcome in its explicit residual branch. -/
theorem step_late (start : Input) (output : HmacBlock) (depth : Nat) (cut : NativeCut) (late : Late cut)
    (result : (Bool ⊕ (Pending × Option Details)) × CtxRO.QueryCache)
    (supported : result ∈ support (step original callbacks baseImpl kem attachedVerify primitives secret challenge start output depth cut)) :
    Residual result := by
  rcases result with ⟨decision | ⟨pending, details⟩, after⟩
  · trivial
  · have same := step_pending original callbacks baseImpl kem attachedVerify primitives secret challenge start output depth cut pending details after supported
    rw [same] at late
    exact late

/-- Two related pending cuts with the same real address and local/cache state take the same cache branch. Missing outputs retain their full relation; cached executions retain both original decision distributions. -/
theorem step_same_address (start : Input) (output : HmacBlock) (depth : Nat)
    (owner : RawCtxProtocolReveals.Owner S (B + 1)) (number : U64) (first second : Bool)
    (adversary : PqxdhInitialBuilderContext.BuildResult → OracleComp
      (PqxdhFirstRecordConfidentiality.AdvSpec (SelectorSpec baseSpec) S (B + 1)) Bool)
    (leftContext rightContext : PqxdhInitialOriginContext.Context (SelectorSpec baseSpec) M P (IdentityHandle I) (DhPair setup) (KemHandle K) Bool Bool S (B + 1))
    (leftDetails rightDetails : Option Details) (state : Local A (BareState 1) RootOracle.QueryCache) (cache : CtxRO.QueryCache)
    (same : PqxdhInitialBuilderContext.address leftContext.original = PqxdhInitialBuilderContext.address rightContext.original)
    (related : PqxdhLaterChallengeBuilderCoupling.Related owner number first second adversary
      (.pending (leftContext, leftDetails) (attach state cache)) (.pending (rightContext, rightDetails) (attach state cache))) :
    RelTriple
      (step original callbacks baseImpl kem attachedVerify primitives secret challenge start output depth (.pending (leftContext, leftDetails) (attach state cache)))
      (step original callbacks baseImpl kem attachedVerify primitives secret challenge start output depth (.pending (rightContext, rightDetails) (attach state cache)))
      (Related owner number first second adversary) := by
  by_cases missing : state.store.1 (PqxdhInitialBuilderContext.address leftContext.original) = none
  · have rightMissing : state.store.1 (PqxdhInitialBuilderContext.address rightContext.original) = none := by
      rw [← same]
      exact missing
    rw [step_missing original callbacks baseImpl kem attachedVerify primitives secret challenge start output depth leftContext leftDetails state cache missing,
      step_missing original callbacks baseImpl kem attachedVerify primitives secret challenge start output depth rightContext rightDetails state cache rightMissing]
    exact relTriple_pure_pure (Or.inl ⟨_, _, rfl, rfl, related⟩)
  · have rightCached : state.store.1 (PqxdhInitialBuilderContext.address rightContext.original) ≠ none := by
      rw [← same]
      exact missing
    refine relTriple_post_mono (PqxdhFirstRecordStopTagged.product_coupling
      (step_cached original callbacks baseImpl kem attachedVerify primitives secret challenge start output depth leftContext leftDetails state cache missing)
      (step_cached original callbacks baseImpl kem attachedVerify primitives secret challenge start output depth rightContext rightDetails state cache rightCached)) ?_
    rintro left right ⟨⟨leftDecision, leftEq⟩, ⟨rightDecision, rightEq⟩⟩
    exact Or.inr ⟨by simp only [Residual, leftEq], by simp only [Residual, rightEq]⟩

/-- Every paired full native prefix transports through the actual collector. The cache test uses the same literal address before admission; all other outcomes keep both complete evaluated distributions. -/
theorem step_coupled (start : Input) (output : HmacBlock) (depth : Nat)
    (owner : RawCtxProtocolReveals.Owner S (B + 1)) (number : U64) (first second : Bool)
    (adversary : PqxdhInitialBuilderContext.BuildResult → OracleComp
      (PqxdhFirstRecordConfidentiality.AdvSpec (SelectorSpec baseSpec) S (B + 1)) Bool)
    (left right : NativeCut)
    (related : PqxdhLaterChallengeBuilderCoupling.Related owner number first second adversary left right) :
    RelTriple (step original callbacks baseImpl kem attachedVerify primitives secret challenge start output depth left)
      (step original callbacks baseImpl kem attachedVerify primitives secret challenge start output depth right)
      (Related owner number first second adversary) := by
  rcases related with ⟨callback, state, rfl, rfl⟩ | ⟨leftCut, rightCut, rfl, rfl, shared⟩
  · apply step_same_address original callbacks baseImpl kem attachedVerify primitives secret challenge start output depth
      owner number first second adversary _ _ _ _ (detach state).1 (detach state).2
    · simp only [PqxdhLaterChallengeSavedMonitor.append_address]
    · exact Or.inl ⟨callback, state, rfl, rfl⟩
  · rcases shared with ⟨details, state, before, rfl, rfl⟩ | ⟨leftLate, rightLate⟩
    · apply step_same_address original callbacks baseImpl kem attachedVerify primitives secret challenge start output depth
        owner number first second adversary _ _ _ _ (detach state).1 (detach state).2
      · simp only [PqxdhLaterChallengeScanCoupling.tagged, PqxdhLaterChallengeSavedMonitor.append_address]
      · exact Or.inr ⟨_, _, rfl, rfl, Or.inl ⟨details, state, before, rfl, rfl⟩⟩
    · have liftedLeft : Late (PqxdhLaterChallengeBuilderCoupling.liftCut leftCut) := by
        cases leftCut <;> exact leftLate
      have liftedRight : Late (PqxdhLaterChallengeBuilderCoupling.liftCut rightCut) := by
        cases rightCut <;> exact rightLate
      exact relTriple_post_mono (PqxdhFirstRecordStopTagged.product_coupling
        (step_late original callbacks baseImpl kem attachedVerify primitives secret challenge start output depth _ liftedLeft)
        (step_late original callbacks baseImpl kem attachedVerify primitives secret challenge start output depth _ liftedRight))
        (fun _ _ both => Or.inr both)

/-- The two complete original prepared runs have a coupling through their literal collector, including every initial-builder result, cached decision, missing cut, private state and reached ROM cache. -/
theorem prepared (start : Input) (output : HmacBlock) (depth : Nat)
    (owner : RawCtxProtocolReveals.Owner S (B + 1)) (number : U64) (first second : Bool)
    (adversary : PqxdhInitialBuilderContext.BuildResult → OracleComp
      (PqxdhFirstRecordConfidentiality.AdvSpec (SelectorSpec baseSpec) S (B + 1)) Bool) (cache : CtxRO.QueryCache) :
    RelTriple
      ((simulateQ hashImpl (PqxdhLaterChallengePreparedCapture.run original callbacks baseImpl kem attachedVerify primitives secret challenge
        start output depth owner number first adversary)).run cache)
      ((simulateQ hashImpl (PqxdhLaterChallengePreparedCapture.run original callbacks baseImpl kem attachedVerify primitives secret challenge
        start output depth owner number second adversary)).run cache)
      (Related owner number first second adversary) := by
  rw [run_split, run_split]
  exact relTriple_bind
    (PqxdhLaterChallengePrefixCoupling.prepared original callbacks baseImpl kem attachedVerify primitives secret challenge
      start output depth owner number first second adversary cache)
    (step_coupled original callbacks baseImpl kem attachedVerify primitives secret challenge start output depth owner number first second adversary)

end Prepared
end BeaconcryptCore.Computational.PqxdhLaterChallengeCollectorCoupling

/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeCollectorCoupling.unrestore_restore' does not depend on any axioms -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeCollectorCoupling.unrestore_restore

/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeCollectorCoupling.restore_unrestore' does not depend on any axioms -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeCollectorCoupling.restore_unrestore

/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeCollectorCoupling.collect_post' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeCollectorCoupling.collect_post

/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeCollectorCoupling.run_split' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeCollectorCoupling.run_split

/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeCollectorCoupling.step_pending' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeCollectorCoupling.step_pending

/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeCollectorCoupling.step_missing' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeCollectorCoupling.step_missing

/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeCollectorCoupling.step_cached' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeCollectorCoupling.step_cached

/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeCollectorCoupling.step_late' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeCollectorCoupling.step_late

/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeCollectorCoupling.step_same_address' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeCollectorCoupling.step_same_address

/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeCollectorCoupling.step_coupled' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeCollectorCoupling.step_coupled

/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeCollectorCoupling.prepared' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeCollectorCoupling.prepared
