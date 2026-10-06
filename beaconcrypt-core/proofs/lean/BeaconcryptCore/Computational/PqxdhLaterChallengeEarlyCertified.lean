-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhLaterChallengeEarlyCompiled
import BeaconcryptCore.Computational.PqxdhLaterChallengeRandomCompiled

/-! Use original source certificates to remove the semantic allowance test from the complete early program. -/
open OracleComp OracleSpec CoreModels Aeneas OracleComp.ProgramLogic.Relational
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhLaterChallengeEarlyCertified
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

local notation "Output" => PqxdhBorrowedSharedPrefix.LocalOutput (M := M) (P := P) (I := I) (K := K) (A := A) setup program

local notation "Carrier" => PqxdhLaterChallengeSampler.Carrier (setup := setup) (M := M) (P := P) (I := I) (K := K)
  (X := X) (Response := Response) (A := A) (KemSK := KemSK) (S := S) (B := B)

open PqxdhJointKdf PqxdhNativeSharedPrefix PqxdhFirstRecordConfidentiality PqxdhJointKdfGame RawCtxSelectedMessageDriver RawCtxSelectedParentTable
local notation "zeroRoot" => (List.Vector.replicate 32 0 : RootOutput)
local notation "Key" => PqxdhLaterChallengeRandomBefore.Key setup program (M := M) (P := P) (I := I) (K := K) (A := A) (X := X) (Response := Response) (KemSK := KemSK)

local notation "backend" => PqxdhLaterChallengeRandomBackend.handler (RawCtxUniversalDecoder.decoder env.decode) env.source.crypto
local notation "impl" => confRandomImpl (RawCtxUniversalDecoder.decoder env.decode) env.source.crypto

/-- Source proof-certificate attachment for the same complete generated carrier. -/
abbrev Certified (q : Nat) := PqxdhLaterChallengeGeneratedFits.Certified setup program owner number
  (M := M) (P := P) (I := I) (K := K) (X := X) (Response := Response) (A := A) (KemSK := KemSK) q

/-- The actual early source continuation has no semantic budget branch. Initial Builders use their structural allowance; before callbacks use the proved original source certificate. -/
noncomputable def continuation (q : Nat) (bit : Bool) (result : Certified setup program owner number (M := M) (P := P) (I := I) (K := K)
      (X := X) (Response := Response) (A := A) (KemSK := KemSK) q) :
    OracleComp AdaptiveCtxDynamicKnownKeys.Spec Bool :=
  match PqxdhLaterChallengeRandomEarly.sourceKey setup program (result.1, ∅) with
  | none => PqxdhLaterChallengeBeforeUnguarded.client setup env callbacks program owner number attachedVerify primitives baseImpl kem (1 + q) bit
      (PqxdhLaterChallengeGeneratedBeforeObservation.beforeKey setup program (result.1, ∅))
      (PqxdhLaterChallengeBeforeUnguarded.key_fits setup program owner number q result.1 ∅ result.2)
  | some payload => PqxdhLaterChallengeBuilderConsumer.client setup env callbacks program adversary owner number attachedVerify primitives baseImpl kem
      (1 + q) bit (some payload)

/-- Removing the old before resource guard leaves the exact complete two-branch source continuation and every oracle call unchanged. -/
theorem continuation_eq (q : Nat) (bit : Bool) (result : Certified setup program owner number (M := M) (P := P) (I := I) (K := K)
      (X := X) (Response := Response) (A := A) (KemSK := KemSK) q) :
    continuation setup env callbacks program adversary owner number attachedVerify primitives baseImpl kem q bit result =
    PqxdhLaterChallengeEarlyCompiled.continuation setup env callbacks program adversary owner number attachedVerify primitives baseImpl kem
      (1 + q) bit result.1 ∅ := by
  cases key : PqxdhLaterChallengeRandomEarly.sourceKey setup program (result.1, ∅) <;>
    simp only [continuation, PqxdhLaterChallengeEarlyCompiled.continuation, key,
      PqxdhLaterChallengeBeforeUnguarded.client_eq]

/-- The complete source reduction forwards the actual generated prefix, attaches its proved cap and executes both early callback cases without a semantic test. -/
noncomputable def compiled (depth : Nat) (budget : PqxdhPhase2SourceSchedulerBounds.Budget)
    (bounded : PqxdhRecordConfidentialityChallenge.AdvBounded program owner adversary budget)
    (prefixBit continuationBit : Bool) : OracleComp AdaptiveCtxDynamicKnownKeys.Spec Bool := do
  let result ← simulateQ RawCtxSourceSharedRom.forward
    (PqxdhLaterChallengeGeneratedFits.certified setup env callbacks program adversary owner number prefixBit
      attachedVerify primitives baseImpl kem ancestors disclosed depth budget bounded)
  continuation setup env callbacks program adversary owner number attachedVerify primitives baseImpl kem
    (FinitePartitionQueryBounds.bill (fun _ => 1) budget) continuationBit result

/-- The executable source certificate erases to the exact complete two-bit program, preserving both Builder and before callbacks, full source prefix, state and all oracle calls. -/
theorem compiled_eq (depth : Nat) (budget : PqxdhPhase2SourceSchedulerBounds.Budget)
    (bounded : PqxdhRecordConfidentialityChallenge.AdvBounded program owner adversary budget)
    (prefixBit continuationBit : Bool) :
    compiled setup env callbacks program adversary owner number attachedVerify primitives baseImpl kem ancestors disclosed
      depth budget bounded prefixBit continuationBit =
    PqxdhLaterChallengeEarlyCompiled.client setup env callbacks program adversary owner number attachedVerify primitives baseImpl kem
      ancestors disclosed depth (1 + FinitePartitionQueryBounds.bill (fun _ => 1) budget) prefixBit continuationBit := by
  have erased := congrArg (simulateQ RawCtxSourceSharedRom.forward)
    (PqxdhLaterChallengeGeneratedFits.certified_erase setup env callbacks program adversary owner number prefixBit
      attachedVerify primitives baseImpl kem ancestors disclosed depth budget bounded)
  rw [simulateQ_map] at erased
  unfold compiled PqxdhLaterChallengeEarlyCompiled.client
  simp only [continuation_eq]
  rw [← erased, bind_map_left]

/-- The actual guard-free source reduction, including initial Builder and later before callbacks, has equal true probability in the two complete ordinary random worlds. -/
theorem random (depth : Nat) (budget : PqxdhPhase2SourceSchedulerBounds.Budget)
    (bounded : PqxdhRecordConfidentialityChallenge.AdvBounded program owner adversary budget) :
    𝒟[Prod.fst <$> (simulateQ impl (compiled setup env callbacks program adversary owner number attachedVerify primitives baseImpl kem ancestors disclosed
      depth budget bounded false false)).run randomInitial] {true} =
    𝒟[Prod.fst <$> (simulateQ impl (compiled setup env callbacks program adversary owner number attachedVerify primitives baseImpl kem ancestors disclosed
      depth budget bounded true true)).run randomInitial] {true} := by
  rw [compiled_eq, compiled_eq]
  exact PqxdhLaterChallengeEarlyCompiled.random setup env callbacks program adversary owner number attachedVerify primitives baseImpl kem
    ancestors disclosed depth (1 + FinitePartitionQueryBounds.bill (fun _ => 1) budget)

end BeaconcryptCore.Computational.PqxdhLaterChallengeEarlyCertified

/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeEarlyCertified.continuation_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeEarlyCertified.continuation_eq

/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeEarlyCertified.compiled_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeEarlyCertified.compiled_eq

/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeEarlyCertified.random' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeEarlyCertified.random
