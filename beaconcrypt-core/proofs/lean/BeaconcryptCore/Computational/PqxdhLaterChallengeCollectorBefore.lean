import BeaconcryptCore.Computational.PqxdhLaterChallengeCollectorCoupling

/-! Observe the exact before-admission saved callback and complete native state in the complete collector distribution, retaining all complementary mass. -/
open OracleComp OracleSpec CoreModels Aeneas OracleComp.ProgramLogic.Relational
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhLaterChallengeCollectorBefore

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


/-- Extract the original complete before callback and native state only from an actual pending collector result. The None branch retains every other outcome. -/
noncomputable def beforeKey (result : (Bool ⊕ (Pending × Option Details)) × CtxRO.QueryCache) :=
  (PqxdhLaterChallengeCollectorCoupling.pendingView result).bind PqxdhLaterChallengePrefixMass.beforeKey

/-- The explicit completed/inside/used residual contributes to the same complementary outcome; it is not assigned zero probability. -/
theorem residual_key (result : (Bool ⊕ (Pending × Option Details)) × CtxRO.QueryCache)
    (residual : PqxdhLaterChallengeCollectorCoupling.Residual result) : beforeKey result = none := by
  rcases result with ⟨decision | ⟨pending, details⟩, after⟩
  · rfl
  · cases details with
    | none => rfl
    | some details =>
      rcases residual with inside | used
      · simp only [beforeKey, PqxdhLaterChallengeCollectorCoupling.pendingView, Option.bind_some,
          PqxdhLaterChallengePrefixMass.beforeKey, inside, reduceCtorEq, ite_false]
      · simp only [beforeKey, PqxdhLaterChallengeCollectorCoupling.pendingView, Option.bind_some,
          PqxdhLaterChallengePrefixMass.beforeKey, used, reduceCtorEq, ite_false]

/-- The complete collector relation preserves the exact before callback and entire native state, including None's complementary mass. -/
theorem related_key (owner : RawCtxProtocolReveals.Owner S (B + 1)) (number : U64) (first second : Bool)
    (adversary : PqxdhInitialBuilderContext.BuildResult → OracleComp
      (PqxdhFirstRecordConfidentiality.AdvSpec (SelectorSpec baseSpec) S (B + 1)) Bool)
    (left right : (Bool ⊕ (Pending × Option Details)) × CtxRO.QueryCache)
    (related : PqxdhLaterChallengeCollectorCoupling.Related owner number first second adversary left right) :
    beforeKey left = beforeKey right := by
  rcases related with ⟨leftCut, rightCut, leftView, rightView, cuts⟩ | ⟨leftResidual, rightResidual⟩
  · simp only [beforeKey, leftView, rightView, Option.bind_some]
    exact PqxdhLaterChallengePrefixMass.related_key owner number first second adversary leftCut rightCut cuts
  · exact (residual_key left leftResidual).trans (residual_key right rightResidual).symm

/-- A pending view determines the full original collected descriptor, local state and actual ROM cache. -/
theorem pending_view (result : (Bool ⊕ (Pending × Option Details)) × CtxRO.QueryCache)
    (context : PqxdhInitialOriginContext.Context (SelectorSpec baseSpec) M P (IdentityHandle I) (DhPair setup) (KemHandle K) Bool Bool S (B + 1))
    (details : Option Details) (state : PqxdhInitialNativeAudit.State A (BareState 1) RootOracle.QueryCache)
    (same : PqxdhLaterChallengeCollectorCoupling.pendingView result = some (.pending (context, details) state)) :
    result = ((Sum.inr ((context, (PqxdhLaterChallengeCollectorCoupling.detach state).1), details)),
      (PqxdhLaterChallengeCollectorCoupling.detach state).2) := by
  rcases result with ⟨decision | ⟨⟨callback, localState⟩, captured⟩, after⟩
  · cases same
  · simp only [PqxdhLaterChallengeCollectorCoupling.pendingView, Option.some.injEq,
      RawCtxForwardScan.Cut.pending.injEq, Prod.mk.injEq] at same
    rcases same with ⟨⟨rfl, rfl⟩, rfl⟩
    cases localState
    rfl

/-- A before observation in the complete prefix relation identifies the same actual saved callback and whole native state, with only each world's original outside wrapper differing. -/
theorem cut_matched (owner : RawCtxProtocolReveals.Owner S (B + 1)) (number : U64) (first second : Bool)
    (adversary : PqxdhInitialBuilderContext.BuildResult → OracleComp
      (PqxdhFirstRecordConfidentiality.AdvSpec (SelectorSpec baseSpec) S (B + 1)) Bool)
    (left right : NativeCut)
    (related : PqxdhLaterChallengeBuilderCoupling.Related owner number first second adversary left right)
    (details : Details) (state : PqxdhInitialNativeAudit.State A (BareState 1) RootOracle.QueryCache)
    (key : PqxdhLaterChallengePrefixMass.beforeKey left = some (details, state)) :
    left = PqxdhLaterChallengeBuilderCoupling.liftCut (.pending (PqxdhLaterChallengeScanCoupling.tagged owner number first details) state) ∧
    right = PqxdhLaterChallengeBuilderCoupling.liftCut (.pending (PqxdhLaterChallengeScanCoupling.tagged owner number second details) state) := by
  rcases related with ⟨callback, native, rfl, rfl⟩ | ⟨leftCut, rightCut, rfl, rfl, wrapper⟩
  · simp only [PqxdhLaterChallengePrefixMass.beforeKey, PqxdhLaterChallengeBuilderCoupling.tagged, reduceCtorEq] at key
  · rcases wrapper with ⟨actualDetails, native, before, rfl, rfl⟩ | ⟨leftLate, rightLate⟩
    · simp only [PqxdhLaterChallengePrefixMass.beforeKey, PqxdhLaterChallengeBuilderCoupling.liftCut,
        PqxdhLaterChallengeCapture.cutMap, PqxdhLaterChallengeScanCoupling.tagged, before, ite_true,
        Option.some.injEq, Prod.mk.injEq] at key
      rcases key with ⟨rfl, rfl⟩
      exact ⟨rfl, rfl⟩
    · rw [PqxdhLaterChallengePrefixMass.late_key leftCut leftLate] at key
      cases key

/-- Reconstruct the exact saved before-admission descriptor, including its own original outside wrapper, complete local state and reached ROM cache. -/
noncomputable def pending (owner : RawCtxProtocolReveals.Owner S (B + 1)) (number : U64) (bit : Bool)
    (details : Details) (state : PqxdhInitialNativeAudit.State A (BareState 1) RootOracle.QueryCache) :
    (Bool ⊕ (Pending × Option Details)) × CtxRO.QueryCache :=
  ((Sum.inr (((PqxdhLaterChallengeScanCoupling.tagged owner number bit details).1,
    (PqxdhLaterChallengeCollectorCoupling.detach state).1), some details)),
    (PqxdhLaterChallengeCollectorCoupling.detach state).2)

/-- A before outcome in one complete collector world forces both exact actual saved descriptors and the same complete native state, rather than merely the same observable reply. -/
theorem matched (owner : RawCtxProtocolReveals.Owner S (B + 1)) (number : U64) (first second : Bool)
    (adversary : PqxdhInitialBuilderContext.BuildResult → OracleComp
      (PqxdhFirstRecordConfidentiality.AdvSpec (SelectorSpec baseSpec) S (B + 1)) Bool)
    (left right : (Bool ⊕ (Pending × Option Details)) × CtxRO.QueryCache)
    (related : PqxdhLaterChallengeCollectorCoupling.Related owner number first second adversary left right)
    (details : Details) (state : PqxdhInitialNativeAudit.State A (BareState 1) RootOracle.QueryCache)
    (key : beforeKey left = some (details, state)) :
    left = pending owner number first details state ∧ right = pending owner number second details state := by
  rcases related with ⟨leftCut, rightCut, leftView, rightView, cuts⟩ | ⟨leftResidual, rightResidual⟩
  · have nativeKey : PqxdhLaterChallengePrefixMass.beforeKey leftCut = some (details, state) := by
      simpa only [beforeKey, leftView, Option.bind_some] using key
    have same := cut_matched owner number first second adversary leftCut rightCut cuts details state nativeKey
    rw [same.1] at leftView
    rw [same.2] at rightView
    exact ⟨pending_view left _ _ state leftView, pending_view right _ _ state rightView⟩
  · rw [residual_key left leftResidual] at key
    cases key

end BeaconcryptCore.Computational.PqxdhLaterChallengeCollectorBefore

/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeCollectorBefore.residual_key' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeCollectorBefore.residual_key

/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeCollectorBefore.related_key' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeCollectorBefore.related_key

/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeCollectorBefore.pending_view' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeCollectorBefore.pending_view

/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeCollectorBefore.cut_matched' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeCollectorBefore.cut_matched

/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeCollectorBefore.matched' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeCollectorBefore.matched
