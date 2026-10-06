import BeaconcryptCore.Computational.PqxdhLaterChallengePrefixCoupling

/-! Equality of the actual measured before-cut descriptor/state distribution follows from the complete prefix coupling. Its None outcome retains all complementary mass, including Builder and completed/post-admission branches. -/
open OracleComp OracleSpec CoreModels Aeneas OracleComp.ProgramLogic.Relational
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhLaterChallengePrefixMass
open PqxdhLaterChallengeCapture PqxdhLaterChallengeSavedClassification
variable {ι M P I D K Origin Local : Type} {extra : OracleSpec ι} {S B : Nat}

/-- Keep the full actual callback/request and native state at a before cut; all other outcomes are one explicit complementary outcome, with no conditioning or resampling. -/
noncomputable def beforeKey (cut : PqxdhLaterChallengeBuilderCoupling.Outcome
    (extra := extra) (M := M) (P := P) (I := I) (D := D) (K := K) (Origin := Origin) (Local := Local) (S := S) (B := B)) :
    Option (Details extra M P I D K Origin S B × Local) :=
  match cut with
  | .pending (_, some details) state => if phase (some details) = .before then some (details, state) else none
  | _ => none

/-- Completed and post-admission wrapper outcomes contribute to the explicit complementary mass. -/
theorem late_key (cut : PqxdhLaterChallengeScanCoupling.Outcome
    (extra := extra) (M := M) (P := P) (I := I) (D := D) (K := K) (Origin := Origin) (Local := Local) (S := S) (B := B))
    (late : PqxdhLaterChallengeScanPhase.Late cut) :
    beforeKey (PqxdhLaterChallengeBuilderCoupling.liftCut cut) = none := by
  cases cut with
  | complete value state => rfl
  | pending tag state =>
      rcases late with inside | used
      · simp only [beforeKey, PqxdhLaterChallengeBuilderCoupling.liftCut, cutMap, inside, reduceCtorEq, ite_false]
      · simp only [beforeKey, PqxdhLaterChallengeBuilderCoupling.liftCut, cutMap, used, reduceCtorEq, ite_false]

/-- The full prefix relation implies exact equality of the before-cut callback, source request/continuation and whole native state, with all complementary outputs mapped to None on both sides. -/
theorem related_key (owner : RawCtxProtocolReveals.Owner S B) (number : U64) (first second : Bool)
    (adversary : PqxdhInitialBuilderContext.BuildResult → OracleComp (PqxdhFirstRecordConfidentiality.AdvSpec extra S B) Bool)
    (left right : PqxdhLaterChallengeBuilderCoupling.Outcome
      (extra := extra) (M := M) (P := P) (I := I) (D := D) (K := K) (Origin := Origin) (Local := Local) (S := S) (B := B))
    (related : PqxdhLaterChallengeBuilderCoupling.Related owner number first second adversary left right) :
    beforeKey left = beforeKey right := by
  rcases related with ⟨callback, state, rfl, rfl⟩ | ⟨left, right, rfl, rfl, wrapper⟩
  · rfl
  · rcases wrapper with ⟨details, state, _, rfl, rfl⟩ | ⟨lateLeft, lateRight⟩
    · rfl
    · exact (late_key left lateLeft).trans (late_key right lateRight).symm

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
/-- The measured before-cut distribution of the actual prepared sampler is exactly bit-independent, including the full callback/continuation/native state at each Some and the entire complementary probability at None. This is a consequence of the full-pair coupling, not a support-only argument. -/
theorem prepared_before
    [MeasurableSpace (Option (PqxdhLaterChallengeCapture.Details (SelectorSpec baseSpec) M P
      (IdentityHandle I) (DhPair setup) (KemHandle K) Bool S (B + 1) ×
        PqxdhInitialNativeAudit.State A (BareState 1) RootOracle.QueryCache))]
    (start : Input) (output : HmacBlock) (depth : Nat)
    (owner : RawCtxProtocolReveals.Owner S (B + 1)) (number : U64) (first second : Bool)
    (adversary : PqxdhInitialBuilderContext.BuildResult → OracleComp
      (PqxdhFirstRecordConfidentiality.AdvSpec (SelectorSpec baseSpec) S (B + 1)) Bool) (cache : CtxRO.QueryCache) :
    𝒟[beforeKey <$> (RawCtxSharedPrefixScan.restore attach <$> (simulateQ hashImpl
        (capturedPrefix original callbacks baseImpl kem attachedVerify primitives secret challenge start output depth owner number first adversary)).run cache)] =
    𝒟[beforeKey <$> (RawCtxSharedPrefixScan.restore attach <$> (simulateQ hashImpl
        (capturedPrefix original callbacks baseImpl kem attachedVerify primitives secret challenge start output depth owner number second adversary)).run cache)] := by
  exact evalDist_eq_of_evalSPMF_eq _ _ (evalSPMF_map_eq_of_relTriple (relTriple_post_mono
    (PqxdhLaterChallengePrefixCoupling.prepared original callbacks baseImpl kem attachedVerify primitives secret challenge start output depth
      owner number first second adversary cache) (related_key owner number first second adversary)))

end Prepared
end BeaconcryptCore.Computational.PqxdhLaterChallengePrefixMass

/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengePrefixMass.late_key' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengePrefixMass.late_key

/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengePrefixMass.related_key' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengePrefixMass.related_key

/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengePrefixMass.prepared_before' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengePrefixMass.prepared_before
