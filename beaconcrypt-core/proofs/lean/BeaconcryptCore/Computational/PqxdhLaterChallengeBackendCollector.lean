-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhLaterChallengeBackendPrefix
import BeaconcryptCore.Computational.PqxdhLaterChallengeCollectorCoupling

/-! Transport the same complete paired source prefixes through the literal completed/cached/missing collector. -/
open OracleComp OracleSpec CoreModels Aeneas OracleComp.ProgramLogic.Relational
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhLaterChallengeBackendCollector
open PqxdhNativeSharedPrefix RawCtxForwardScan CtxRomAuth

/-- Reassociate the full local/backend pair without forgetting any history field. -/
def unrestore {Tag Result Local Backend : Type} : Cut Tag Result (Local × Backend) → Cut Tag Result Local × Backend
  | .complete result state => (.complete result state.1, state.2)
  | .pending tag state => (.pending tag state.1, state.2)

/-- Reassembly followed by splitting preserves the entire original result. -/
theorem unrestore_restore {Tag Result Local Backend : Type} (result : Cut Tag Result Local × Backend) :
    unrestore (RawCtxSharedPrefixBackend.restore result) = result := by
  rcases result with ⟨cut, cache⟩
  cases cut <;> rfl

section Prepared
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
open PqxdhJointKdfGame PqxdhSecretInputKdf PqxdhCorrelatedExpand PqxdhCorrelatedExtractFamily
open PqxdhKemIndCca PqxdhEd25519EufCma PqxdhJointIdentity PqxdhStatefulPhase1EufCma
open PqxdhPhase2GeneratedDriver PqxdhAuthenticatedRootExperiment PqxdhPhase1AcceptanceOracle
open PqxdhPrivateKemSource PqxdhGeneratedBeaconState PqxdhNativeSharedPrefix
open CtxRomAuth AdaptiveCtxSharedHash
variable {ι M P I K X Response A KemSK Backend : Type} {baseSpec : OracleSpec ι} {S B : Nat}
variable {setup : StatefulPhase1Setup baseSpec}
    (original : PqxdhAuthenticatedRootExperiment.Environment setup M P I K X Response A S B)
    (callbacks : PqxdhSourceAuxiliary.Callbacks A)

variable (baseImpl : QueryImpl baseSpec ProbComp) (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes) (primitives : Primitives)
    (secret : KemSK) (challenge : MlKem768Ciphertext)
    (backend : QueryImpl HashSpec (StateT Backend ProbComp))
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
  (Local := (Local A (BareState 1) RootOracle.QueryCache × Backend)) (S := S) (B := B + 1)

/-- The collector on the exact original local/cache representation of this native cut. Its decisions and final cache remain in the output. -/
noncomputable def step (start : Input) (output : HmacBlock) (depth : Nat) (cut : NativeCut) :=
  (simulateQ backend (PqxdhLaterChallengePreparedCapture.collect original callbacks baseImpl kem attachedVerify primitives secret challenge
    start output depth (unrestore cut).1)).run (unrestore cut).2

open PqxdhLaterChallengeCollectorCoupling (collect_post)

/-- The complete original prepared run factors through the same fully reassembled native prefix and the unchanged collector. This retains all final decisions and actual cache state. -/
theorem run_split (start : Input) (output : HmacBlock) (depth : Nat)
    (owner : RawCtxProtocolReveals.Owner S (B + 1)) (number : U64) (bit : Bool)
    (adversary : PqxdhInitialBuilderContext.BuildResult → OracleComp
      (PqxdhFirstRecordConfidentiality.AdvSpec (SelectorSpec baseSpec) S (B + 1)) Bool) (cache : Backend) :
    (simulateQ backend (PqxdhLaterChallengePreparedCapture.run original callbacks baseImpl kem attachedVerify primitives secret challenge
      start output depth owner number bit adversary)).run cache =
      (RawCtxSharedPrefixBackend.restore <$> (simulateQ backend
        (capturedPrefix original callbacks baseImpl kem attachedVerify primitives secret challenge start output depth owner number bit adversary)).run cache) >>=
        step original callbacks baseImpl kem attachedVerify primitives secret challenge backend start output depth := by
  simp only [PqxdhLaterChallengePreparedCapture.run, simulateQ_bind, StateT.run_bind, bind_map_left,
    step, unrestore_restore, collect_post]

/-- A pending collected result is the same full native cut, including its original descriptor, local state and complete reached backend. Completed and cached decisions cannot manufacture such a result. -/
theorem step_pending (start : Input) (output : HmacBlock) (depth : Nat) (cut : NativeCut)
    (pending : Pending) (details : Option Details) (after : Backend)
    (supported : (Sum.inr (pending, details), after) ∈ support
      (step original callbacks baseImpl kem attachedVerify primitives secret challenge backend start output depth cut)) :
    cut = .pending (pending.1, details) (pending.2, after) := by
  cases cut with
  | complete value state =>
      simp only [step, unrestore, PqxdhLaterChallengePreparedCapture.collect,
        PqxdhPreparedSharedParent.collect, PqxdhSharedParentCollect.collect, PqxdhLaterChallengeCapture.cutMap,
        simulateQ_pure, StateT.run_pure, map_pure, mem_support_pure_iff] at supported
      cases supported
  | pending tag state =>
      rcases tag with ⟨context, captured⟩
      rcases state with ⟨localState, cache⟩
      simp only [step, unrestore, PqxdhLaterChallengePreparedCapture.collect,
        PqxdhPreparedSharedParent.collect, PqxdhSharedParentCollect.collect, PqxdhLaterChallengeCapture.cutMap] at supported
      split at supported
      · simp only [simulateQ_pure, StateT.run_pure, map_pure, mem_support_pure_iff] at supported
        change (Sum.inr (pending, details), after) = (Sum.inr ((context, localState), captured), cache) at supported
        simp only [Prod.mk.injEq, Sum.inr.injEq] at supported
        rcases supported with ⟨⟨rfl, rfl⟩, rfl⟩
        rfl
      · have logical := PqxdhFirstRecordStopTagged.support_state_simulation backend _ cache _ supported
        simp only [map_bind, map_pure, mem_support_bind_iff, mem_support_pure_iff] at logical
        obtain ⟨_, _, impossible⟩ := logical
        cases impossible

/-- A genuine missing-address collector returns the exact pending descriptor, local state and unchanged complete backend. -/
theorem step_missing (start : Input) (output : HmacBlock) (depth : Nat)
    (context : PqxdhInitialOriginContext.Context (SelectorSpec baseSpec) M P (IdentityHandle I) (DhPair setup) (KemHandle K) Bool Bool S (B + 1))
    (details : Option Details) (state : Local A (BareState 1) RootOracle.QueryCache) (cache : Backend)
    (missing : state.store.1 (PqxdhInitialBuilderContext.address context.original) = none) :
    step original callbacks baseImpl kem attachedVerify primitives secret challenge backend start output depth
      (.pending (context, details) (state, cache)) = pure (Sum.inr ((context, state), details), cache) := by
  simp only [step, unrestore, PqxdhLaterChallengePreparedCapture.collect,
    PqxdhPreparedSharedParent.collect, PqxdhSharedParentCollect.collect, PqxdhLaterChallengeCapture.cutMap]
  rw [ite_eq_left missing]
  rfl

/-- Every cached-address continuation keeps its actual Boolean decision and reached cache; none of its outcomes is relabelled as a pending descriptor. -/
theorem step_cached (start : Input) (output : HmacBlock) (depth : Nat)
    (context : PqxdhInitialOriginContext.Context (SelectorSpec baseSpec) M P (IdentityHandle I) (DhPair setup) (KemHandle K) Bool Bool S (B + 1))
    (details : Option Details) (state : Local A (BareState 1) RootOracle.QueryCache) (cache : Backend)
    (cached : state.store.1 (PqxdhInitialBuilderContext.address context.original) ≠ none)
    (result : (Bool ⊕ (Pending × Option Details)) × Backend)
    (supported : result ∈ support (step original callbacks baseImpl kem attachedVerify primitives secret challenge backend start output depth
      (.pending (context, details) (state, cache)))) :
    ∃ decision, result.1 = Sum.inl decision := by
  have logical := PqxdhFirstRecordStopTagged.support_state_simulation backend _ cache result supported
  simp only [unrestore, PqxdhLaterChallengePreparedCapture.collect,
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
def Residual (result : (Bool ⊕ (Pending × Option Details)) × Backend) : Prop :=
  match result.1 with
  | .inl _ => True
  | .inr (_, details) =>
      PqxdhLaterChallengeSavedClassification.phase details = .inside ∨
        PqxdhLaterChallengeSavedClassification.phase details = .used

/-- Reassemble only an actual pending result; a completed/cached decision remains absent. -/
def pendingView (result : (Bool ⊕ (Pending × Option Details)) × Backend) : Option NativeCut :=
  match result.1 with
  | .inl _ => none
  | .inr (pending, details) => some (.pending (pending.1, details) (pending.2, result.2))

/-- The complete collector outputs retain either their paired original pending cuts or both complete/post-admission residual outcomes. -/
noncomputable def Related (owner : RawCtxProtocolReveals.Owner S (B + 1)) (number : U64) (first second : Bool)
    (adversary : PqxdhInitialBuilderContext.BuildResult → OracleComp
      (PqxdhFirstRecordConfidentiality.AdvSpec (SelectorSpec baseSpec) S (B + 1)) Bool)
    (left right : (Bool ⊕ (Pending × Option Details)) × Backend) : Prop :=
  (∃ leftCut rightCut, pendingView left = some leftCut ∧ pendingView right = some rightCut ∧
    PqxdhLaterChallengeBuilderCoupling.Related owner number first second adversary leftCut rightCut) ∨
      (Residual left ∧ Residual right)

/-- The literal collector keeps every full completed/post-admission outcome in its explicit residual branch. -/
theorem step_late (start : Input) (output : HmacBlock) (depth : Nat) (cut : NativeCut) (late : Late cut)
    (result : (Bool ⊕ (Pending × Option Details)) × Backend)
    (supported : result ∈ support (step original callbacks baseImpl kem attachedVerify primitives secret challenge backend start output depth cut)) :
    Residual result := by
  rcases result with ⟨decision | ⟨pending, details⟩, after⟩
  · trivial
  · have same := step_pending original callbacks baseImpl kem attachedVerify primitives secret challenge backend start output depth cut pending details after supported
    rw [same] at late
    exact late

/-- Two related pending cuts with the same real address and local/cache state take the same cache branch. Missing outputs retain their full relation; cached executions retain both original decision distributions. -/
theorem step_same_address (start : Input) (output : HmacBlock) (depth : Nat)
    (owner : RawCtxProtocolReveals.Owner S (B + 1)) (number : U64) (first second : Bool)
    (adversary : PqxdhInitialBuilderContext.BuildResult → OracleComp
      (PqxdhFirstRecordConfidentiality.AdvSpec (SelectorSpec baseSpec) S (B + 1)) Bool)
    (leftContext rightContext : PqxdhInitialOriginContext.Context (SelectorSpec baseSpec) M P (IdentityHandle I) (DhPair setup) (KemHandle K) Bool Bool S (B + 1))
    (leftDetails rightDetails : Option Details) (state : Local A (BareState 1) RootOracle.QueryCache) (cache : Backend)
    (same : PqxdhInitialBuilderContext.address leftContext.original = PqxdhInitialBuilderContext.address rightContext.original)
    (related : PqxdhLaterChallengeBuilderCoupling.Related owner number first second adversary
      (.pending (leftContext, leftDetails) (state, cache)) (.pending (rightContext, rightDetails) (state, cache))) :
    RelTriple
      (step original callbacks baseImpl kem attachedVerify primitives secret challenge backend start output depth (.pending (leftContext, leftDetails) (state, cache)))
      (step original callbacks baseImpl kem attachedVerify primitives secret challenge backend start output depth (.pending (rightContext, rightDetails) (state, cache)))
      (Related owner number first second adversary) := by
  by_cases missing : state.store.1 (PqxdhInitialBuilderContext.address leftContext.original) = none
  · have rightMissing : state.store.1 (PqxdhInitialBuilderContext.address rightContext.original) = none := by
      rw [← same]
      exact missing
    rw [step_missing original callbacks baseImpl kem attachedVerify primitives secret challenge backend start output depth leftContext leftDetails state cache missing,
      step_missing original callbacks baseImpl kem attachedVerify primitives secret challenge backend start output depth rightContext rightDetails state cache rightMissing]
    exact relTriple_pure_pure (Or.inl ⟨_, _, rfl, rfl, related⟩)
  · have rightCached : state.store.1 (PqxdhInitialBuilderContext.address rightContext.original) ≠ none := by
      rw [← same]
      exact missing
    refine relTriple_post_mono (PqxdhFirstRecordStopTagged.product_coupling
      (step_cached original callbacks baseImpl kem attachedVerify primitives secret challenge backend start output depth leftContext leftDetails state cache missing)
      (step_cached original callbacks baseImpl kem attachedVerify primitives secret challenge backend start output depth rightContext rightDetails state cache rightCached)) ?_
    rintro left right ⟨⟨leftDecision, leftEq⟩, ⟨rightDecision, rightEq⟩⟩
    exact Or.inr ⟨by simp only [Residual, leftEq], by simp only [Residual, rightEq]⟩

/-- Every paired full native prefix transports through the actual collector. The cache test uses the same literal address before admission; all other outcomes keep both complete evaluated distributions. -/
theorem step_coupled (start : Input) (output : HmacBlock) (depth : Nat)
    (owner : RawCtxProtocolReveals.Owner S (B + 1)) (number : U64) (first second : Bool)
    (adversary : PqxdhInitialBuilderContext.BuildResult → OracleComp
      (PqxdhFirstRecordConfidentiality.AdvSpec (SelectorSpec baseSpec) S (B + 1)) Bool)
    (left right : NativeCut)
    (related : PqxdhLaterChallengeBuilderCoupling.Related owner number first second adversary left right) :
    RelTriple (step original callbacks baseImpl kem attachedVerify primitives secret challenge backend start output depth left)
      (step original callbacks baseImpl kem attachedVerify primitives secret challenge backend start output depth right)
      (Related owner number first second adversary) := by
  rcases related with ⟨callback, state, rfl, rfl⟩ | ⟨leftCut, rightCut, rfl, rfl, shared⟩
  · apply step_same_address original callbacks baseImpl kem attachedVerify primitives secret challenge backend start output depth
      owner number first second adversary _ _ _ _ state.1 state.2
    · simp only [PqxdhLaterChallengeSavedMonitor.append_address]
    · exact Or.inl ⟨callback, state, rfl, rfl⟩
  · rcases shared with ⟨details, state, before, rfl, rfl⟩ | ⟨leftLate, rightLate⟩
    · apply step_same_address original callbacks baseImpl kem attachedVerify primitives secret challenge backend start output depth
        owner number first second adversary _ _ _ _ state.1 state.2
      · simp only [PqxdhLaterChallengeScanCoupling.tagged, PqxdhLaterChallengeSavedMonitor.append_address]
      · exact Or.inr ⟨_, _, rfl, rfl, Or.inl ⟨details, state, before, rfl, rfl⟩⟩
    · have liftedLeft : Late (PqxdhLaterChallengeBuilderCoupling.liftCut leftCut) := by
        cases leftCut <;> exact leftLate
      have liftedRight : Late (PqxdhLaterChallengeBuilderCoupling.liftCut rightCut) := by
        cases rightCut <;> exact rightLate
      exact relTriple_post_mono (PqxdhFirstRecordStopTagged.product_coupling
        (step_late original callbacks baseImpl kem attachedVerify primitives secret challenge backend start output depth _ liftedLeft)
        (step_late original callbacks baseImpl kem attachedVerify primitives secret challenge backend start output depth _ liftedRight))
        (fun _ _ both => Or.inr both)

/-- The two complete original prepared runs have a coupling through their literal collector, including every initial-builder result, cached decision, missing cut, private state and reached ROM cache. -/
theorem prepared (start : Input) (output : HmacBlock) (depth : Nat)
    (owner : RawCtxProtocolReveals.Owner S (B + 1)) (number : U64) (first second : Bool)
    (adversary : PqxdhInitialBuilderContext.BuildResult → OracleComp
      (PqxdhFirstRecordConfidentiality.AdvSpec (SelectorSpec baseSpec) S (B + 1)) Bool) (cache : Backend) :
    RelTriple
      ((simulateQ backend (PqxdhLaterChallengePreparedCapture.run original callbacks baseImpl kem attachedVerify primitives secret challenge
        start output depth owner number first adversary)).run cache)
      ((simulateQ backend (PqxdhLaterChallengePreparedCapture.run original callbacks baseImpl kem attachedVerify primitives secret challenge
        start output depth owner number second adversary)).run cache)
      (Related owner number first second adversary) := by
  rw [run_split, run_split]
  exact relTriple_bind
    (PqxdhLaterChallengeBackendPrefix.prepared original callbacks baseImpl kem attachedVerify primitives secret challenge
      start output depth owner number first second adversary backend cache)
    (step_coupled original callbacks baseImpl kem attachedVerify primitives secret challenge backend start output depth owner number first second adversary)

end Prepared
end BeaconcryptCore.Computational.PqxdhLaterChallengeBackendCollector


/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeBackendCollector.unrestore_restore' does not depend on any axioms -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeBackendCollector.unrestore_restore

/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeBackendCollector.run_split' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeBackendCollector.run_split

/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeBackendCollector.step_pending' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeBackendCollector.step_pending

/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeBackendCollector.step_missing' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeBackendCollector.step_missing

/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeBackendCollector.step_cached' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeBackendCollector.step_cached

/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeBackendCollector.step_late' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeBackendCollector.step_late

/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeBackendCollector.step_same_address' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeBackendCollector.step_same_address

/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeBackendCollector.step_coupled' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeBackendCollector.step_coupled

/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeBackendCollector.prepared' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeBackendCollector.prepared
