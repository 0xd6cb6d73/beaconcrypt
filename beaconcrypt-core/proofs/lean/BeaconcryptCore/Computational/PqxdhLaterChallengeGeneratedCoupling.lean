import BeaconcryptCore.Computational.PqxdhLaterChallengePreparationCoupling

/-! Preserve actual generated selection and private preparation when coupling the full later-record sampler. -/
open OracleComp OracleSpec CoreModels Aeneas OracleComp.ProgramLogic.Relational
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhLaterChallengeGeneratedCoupling
open PqxdhEd25519EufCma PqxdhJointIdentity PqxdhStatefulPhase1EufCma PqxdhPrivateKemSource
open PqxdhGeneratedBeaconState PqxdhPhase1AcceptanceOracle PqxdhKemIndCca PqxdhInitializerSecrecy
open CtxRomAuth AdaptiveCtxSharedHash PqxdhSecretInputKdf PqxdhFullSecretInputKdf
open RawCtxSelectedParentEntry PqxdhOrderedChainHybrids PqxdhCorrelatedExpand
variable {ι M P I K X Response A KemSK : Type} {baseSpec : OracleSpec ι} {S B : Nat}
variable (setup : StatefulPhase1Setup baseSpec)
    (env : PqxdhAuthenticatedRootExperiment.Environment setup M P I K X Response A S B)
    (callbacks : PqxdhSourceAuxiliary.Callbacks A)
    (program : PqxdhPhase2GeneratedDriver.Program baseSpec setup.Context S (B + 1))
    (adversary : program.Selection → PqxdhInitialBuilderContext.BuildResult → OracleComp
      (PqxdhFirstRecordConfidentiality.AdvSpec (SelectorSpec baseSpec) S (B + 1)) Bool)
    (owner : RawCtxProtocolReveals.Owner S (B + 1)) (number : U64)
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (ancestors disclosed : List RatchetChain)
local notation "env0" => PqxdhSourceSharedPreparation.environment setup env callbacks ∅
local notation "Packet" => PqxdhSourceSharedPreparation.Packet
  (PqxdhSourceSharedPreparation.LocalOutput (M := M) (P := P) (I := I) (K := K) (A := A) setup program) KemSK
local notation "LocalPacket" => PqxdhSharedParentInput.LocalPacket (setup := setup) (M := M) (P := P) (I := I) (K := K)
    (X := X) (Response := Response) (A := A) (S := S) (B := B)
abbrev Details := PqxdhLaterChallengeCapture.Details (SelectorSpec baseSpec) M P (IdentityHandle I) (DhPair setup) (KemHandle K) Bool S (B + 1)

local notation "Input" => PqxdhInitialPreparedSourceInput.Input (M := M) (P := P) (I := I) (K := K) (X := X)
    (Response := Response) (A := A) (S := S) (B := B) (setup := setup)


local notation "Pending" => PqxdhSharedParentCollect.Pending (SelectorSpec baseSpec) M P (IdentityHandle I) (DhPair setup) (KemHandle K) A (BareState 1) RootOracle.QueryCache S (B + 1)
local notation "CaptureDetails" => Details (setup := setup) (M := M) (P := P) (I := I) (K := K) (S := S) (B := B)
local notation "Post" => PqxdhAuthenticatedRootExperiment.Post (baseSpec := baseSpec) program.Selection S (B + 1)

/-- Replacing the unused original Post field before installing the actual world wrapper leaves the entire collector sampler unchanged. -/
theorem prepared_post (secret : KemSK) (challenge : MlKem768Ciphertext)
    (start : Input) (output : HmacBlock) (depth : Nat) (bit : Bool)
    (continuation : PqxdhInitialBuilderContext.BuildResult → OracleComp
      (PqxdhFirstRecordConfidentiality.AdvSpec (SelectorSpec baseSpec) S (B + 1)) Bool)
    (other : PqxdhInitialBuilderContext.BuildResult → OracleComp
      (PqxdhInitialGenericPost.Spec (SelectorSpec baseSpec) S (B + 1)) Bool) :
    PqxdhLaterChallengeSampler.prepared setup env callbacks owner number bit attachedVerify primitives baseImpl kem
      secret challenge {start with post := other} output depth continuation =
    PqxdhLaterChallengeSampler.prepared setup env callbacks owner number bit attachedVerify primitives baseImpl kem
      secret challenge start output depth continuation := by
  rfl

/-- Copy the literal stored source input and collector output into the existing packet representation, retaining its reached cache. -/
noncomputable def encodePrepared (secret : KemSK) (challenge : MlKem768Ciphertext)
    (start : Input) (output : HmacBlock) (bit : Bool)
    (continuation : PqxdhInitialBuilderContext.BuildResult → OracleComp
      (PqxdhFirstRecordConfidentiality.AdvSpec (SelectorSpec baseSpec) S (B + 1)) Bool)
    (result : (Bool ⊕ (Pending × Option CaptureDetails)) × CtxRO.QueryCache) :
    (LocalPacket × Option CaptureDetails) × CtxRO.QueryCache :=
  let originalStart := PqxdhErasedParentSample.forgetStart
    (PqxdhPreparedSharedPrefix.input env0 callbacks baseImpl kem attachedVerify primitives secret challenge
      (PqxdhLaterChallengePreparedCapture.withPost (setup := setup) start owner number bit continuation), output)
  (match result.1 with
    | .inl decision => (.inr (originalStart, .inl decision), none)
    | .inr (pending, details) => (.inr (originalStart, .inr pending), details), result.2)

/-- The complete evaluated prepared carrier is only this deterministic representation map over the exact original collector distribution. -/
theorem prepared_map (secret : KemSK) (challenge : MlKem768Ciphertext)
    (start : Input) (output : HmacBlock) (depth : Nat) (bit : Bool)
    (continuation : PqxdhInitialBuilderContext.BuildResult → OracleComp
      (PqxdhFirstRecordConfidentiality.AdvSpec (SelectorSpec baseSpec) S (B + 1)) Bool) (cache : CtxRO.QueryCache) :
    (simulateQ hashImpl (PqxdhLaterChallengeSampler.prepared setup env callbacks owner number bit attachedVerify primitives baseImpl kem
      secret challenge start output depth continuation)).run cache =
    encodePrepared setup env callbacks owner number attachedVerify primitives baseImpl kem secret challenge start output bit continuation <$>
      (simulateQ hashImpl (PqxdhLaterChallengePreparedCapture.run env0 callbacks baseImpl kem attachedVerify primitives
        secret challenge start output depth owner number bit continuation)).run cache := by
  simp only [PqxdhLaterChallengeSampler.prepared, bind_pure_comp, simulateQ_map, StateT.run_map]
  rfl

/-- Both prepared carriers contain exactly the paired collector outputs and the same complete source input with each world's own wrapper installed. -/
noncomputable def PreparedRelated (secret : KemSK) (challenge : MlKem768Ciphertext)
    (start : Input) (output : HmacBlock) (first second : Bool)
    (continuation : PqxdhInitialBuilderContext.BuildResult → OracleComp
      (PqxdhFirstRecordConfidentiality.AdvSpec (SelectorSpec baseSpec) S (B + 1)) Bool)
    (left right : (LocalPacket × Option CaptureDetails) × CtxRO.QueryCache) : Prop :=
  ∃ leftResult rightResult,
    left = encodePrepared setup env callbacks owner number attachedVerify primitives baseImpl kem secret challenge start output first continuation leftResult ∧
    right = encodePrepared setup env callbacks owner number attachedVerify primitives baseImpl kem secret challenge start output second continuation rightResult ∧
    PqxdhLaterChallengeCollectorCoupling.Related owner number first second continuation leftResult rightResult

/-- Lift the checked complete collector coupling to its actual stored source-input carrier without dropping common or cached outcomes. -/
theorem prepared (secret : KemSK) (challenge : MlKem768Ciphertext)
    (start : Input) (output : HmacBlock) (depth : Nat) (first second : Bool)
    (continuation : PqxdhInitialBuilderContext.BuildResult → OracleComp
      (PqxdhFirstRecordConfidentiality.AdvSpec (SelectorSpec baseSpec) S (B + 1)) Bool) (cache : CtxRO.QueryCache) :
    RelTriple
      ((simulateQ hashImpl (PqxdhLaterChallengeSampler.prepared setup env callbacks owner number first attachedVerify primitives baseImpl kem
        secret challenge start output depth continuation)).run cache)
      ((simulateQ hashImpl (PqxdhLaterChallengeSampler.prepared setup env callbacks owner number second attachedVerify primitives baseImpl kem
        secret challenge start output depth continuation)).run cache)
      (PreparedRelated setup env callbacks owner number attachedVerify primitives baseImpl kem secret challenge start output first second continuation) := by
  rw [prepared_map, prepared_map]
  apply relTriple_map
  exact relTriple_post_mono
    (PqxdhLaterChallengeCollectorCoupling.prepared env0 callbacks baseImpl kem attachedVerify primitives secret challenge
      start output depth owner number first second continuation cache)
    (fun left right related => ⟨left, right, rfl, rfl, related⟩)

end BeaconcryptCore.Computational.PqxdhLaterChallengeGeneratedCoupling

/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeGeneratedCoupling.prepared_post' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeGeneratedCoupling.prepared_post

/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeGeneratedCoupling.prepared_map' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeGeneratedCoupling.prepared_map

/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeGeneratedCoupling.prepared' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeGeneratedCoupling.prepared
