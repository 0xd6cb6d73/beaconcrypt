-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhLaterChallengeSamplerFits

/-! Derive the before-client certificate from the complete generated source and its original finite source-query budget. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhLaterChallengeGeneratedFits
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
    (owner : RawCtxProtocolReveals.Owner S (B + 1)) (number : U64) (bit : Bool)
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (ancestors disclosed : List RatchetChain)
local notation "post" => PqxdhRecordConfidentialityChallenge.post adversary owner number bit
local notation "env0" => PqxdhSourceSharedPreparation.environment setup env callbacks ∅
local notation "Packet" => PqxdhSourceSharedPreparation.Packet
  (PqxdhSourceSharedPreparation.LocalOutput (M := M) (P := P) (I := I) (K := K) (A := A) setup program) KemSK
local notation "LocalPacket" => PqxdhSharedParentInput.LocalPacket (setup := setup) (M := M) (P := P) (I := I) (K := K)
    (X := X) (Response := Response) (A := A) (S := S) (B := B)
local notation "input" => PqxdhSourceSharedInput.input setup env callbacks program post attachedVerify primitives baseImpl kem owner number ancestors disclosed
abbrev Details := PqxdhLaterChallengeCapture.Details (SelectorSpec baseSpec) M P (IdentityHandle I) (DhPair setup) (KemHandle K) Bool S (B + 1)

local notation "Input" => PqxdhInitialPreparedSourceInput.Input (M := M) (P := P) (I := I) (K := K) (X := X)
    (Response := Response) (A := A) (S := S) (B := B) (setup := setup)

open PqxdhLaterChallengeSampler

/-- The complete generated carrier preserves the source-derived allowances of its literal pending callback; carried selection metadata and all material draws add no condition. -/
theorem run_fits (depth q : Nat)
    (bounded : ∀ selection reply, (adversary selection reply).IsTotalQueryBound q)
    (result : PqxdhLaterChallengeGeneratedContinuation.Carrier setup program (M := M) (P := P) (I := I) (K := K)
      (X := X) (Response := Response) (A := A) (KemSK := KemSK) (S := S) (B := B))
    (supported : result ∈ support (PqxdhLaterChallengeGeneratedContinuation.run setup env callbacks program adversary owner number bit
      attachedVerify primitives baseImpl kem ancestors disclosed depth)) :
    PqxdhLaterChallengeSamplerFits.PacketFits setup owner number q (result.1.1.2.1.1.1, result.1.2) := by
  apply PqxdhLaterChallengeSamplerFits.run_fits setup env callbacks program adversary owner number bit
    attachedVerify primitives baseImpl kem ancestors disclosed depth q bounded result.1
  rw [← PqxdhLaterChallengeGeneratedContinuation.run_erase setup env callbacks program adversary owner number bit
    attachedVerify primitives baseImpl kem ancestors disclosed depth, support_map]
  exact ⟨result, supported, rfl⟩

/-- Summing the original finite per-kind source allowance bounds every adversary request once, including either directional challenge send and every reveal, selector, raw-delivery or finish request. -/
theorem adversary_total (budget : PqxdhPhase2SourceSchedulerBounds.Budget)
    (bounded : PqxdhRecordConfidentialityChallenge.AdvBounded program owner adversary budget)
    (selection : program.Selection) (reply : PqxdhInitialBuilderContext.BuildResult) :
    (adversary selection reply).IsTotalQueryBound (FinitePartitionQueryBounds.bill (fun _ => 1) budget) := by
  classical
  let classify : (PqxdhFirstRecordConfidentiality.AdvSpec (SelectorSpec baseSpec) S (B + 1)).Domain →
      PqxdhPhase2SourceSchedulerBounds.Kind := fun query => match query with
    | .inl request => PqxdhPhase2SourceSchedulerBounds.classify (baseSpec := baseSpec) request
    | .inr pair => PqxdhPhase2SourceSchedulerBounds.classify (baseSpec := baseSpec)
        (PqxdhRecordConfidentialityChallenge.sendRequest owner pair.1)
  apply FinitePartitionTotal.bound classify (adversary selection reply) budget
  intro kind
  apply IsQueryBoundP.of_imp ?_ (bounded selection reply kind)
  intro query counted
  rcases query with request | pair
  · exact counted
  · exact Or.inl counted

local notation "Generated" => PqxdhLaterChallengeGeneratedContinuation.Carrier setup program (M := M) (P := P) (I := I) (K := K)
  (X := X) (Response := Response) (A := A) (KemSK := KemSK) (S := S) (B := B)

/-- Certificates contain only a proof derived from this run's syntactic support and the original source query allowance. -/
abbrev Certified (q : Nat) := { result : Generated //
  PqxdhLaterChallengeSamplerFits.PacketFits setup owner number q (result.1.1.2.1.1.1, result.1.2) }

/-- Run the literal complete source prelude and attach the proven continuation cap; no runtime test of a semantic resource predicate occurs. -/
noncomputable def certified (depth : Nat) (budget : PqxdhPhase2SourceSchedulerBounds.Budget)
    (bounded : PqxdhRecordConfidentialityChallenge.AdvBounded program owner adversary budget) :
    OracleComp HashSpec (Certified setup program owner number (M := M) (P := P) (I := I) (K := K)
      (X := X) (Response := Response) (A := A) (KemSK := KemSK) (FinitePartitionQueryBounds.bill (fun _ => 1) budget)) :=
  (fun result => ⟨result.1, run_fits setup env callbacks program adversary owner number bit attachedVerify primitives baseImpl kem
    ancestors disclosed depth _ (adversary_total setup program adversary owner budget bounded) result.1 result.2⟩) <$>
      MonadAttach.attach (PqxdhLaterChallengeGeneratedContinuation.run setup env callbacks program adversary owner number bit
        attachedVerify primitives baseImpl kem ancestors disclosed depth)

/-- Erasing the proof recovers exact complete source syntax, including source order, all private state and every complementary result. -/
theorem certified_erase (depth : Nat) (budget : PqxdhPhase2SourceSchedulerBounds.Budget)
    (bounded : PqxdhRecordConfidentialityChallenge.AdvBounded program owner adversary budget) :
    Subtype.val <$> certified setup env callbacks program adversary owner number bit attachedVerify primitives baseImpl kem
      ancestors disclosed depth budget bounded =
    PqxdhLaterChallengeGeneratedContinuation.run setup env callbacks program adversary owner number bit
      attachedVerify primitives baseImpl kem ancestors disclosed depth := by
  unfold certified Certified
  rw [Functor.map_map]
  exact WeaklyLawfulMonadAttach.map_attach (m := OracleComp HashSpec)

end BeaconcryptCore.Computational.PqxdhLaterChallengeGeneratedFits

/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeGeneratedFits.run_fits' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeGeneratedFits.run_fits

/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeGeneratedFits.adversary_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeGeneratedFits.adversary_total

/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeGeneratedFits.certified_erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeGeneratedFits.certified_erase
