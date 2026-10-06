-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhLaterChallengeEarlyResources

/-! Connect the complete initial Builder and before-source comparison to ordinary modified CTX reductions. -/
open OracleComp OracleSpec CoreModels Aeneas OracleComp.ProgramLogic.Relational
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhLaterChallengeEarlyPrivacy
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

variable (budget : PqxdhPhase2SourceSchedulerBounds.Budget)
    (bounded : PqxdhRecordConfidentialityChallenge.AdvBounded program owner adversary budget)
local notation "q" => FinitePartitionQueryBounds.bill (fun _ => 1) budget
local notation "compiled" => PqxdhLaterChallengeEarlyCertified.compiled setup env callbacks program adversary owner number attachedVerify primitives baseImpl kem ancestors disclosed

/-- The concrete ordinary selected-key game now runs the complete source-derived reduction without a semantic Fits test. -/
noncomputable def source (depth : Nat) (bit : Bool) : ProbComp Bool :=
  Prod.fst <$> AdaptiveCtxDynamicKnownKeys.sourceGame true (RawCtxUniversalDecoder.decoder env.decode) env.source.crypto
    (compiled depth budget bounded bit bit)

/-- Each loss names the guard-free complete source reduction and charges the original prefix plus both saved-wrapper allowances. -/
noncomputable def loss (depth qHashPre : Nat) (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery) (bit : Bool) :=
  privacyLoss (RawCtxUniversalDecoder.decoder env.decode) env.source.crypto (compiled depth budget bounded bit bit) fallback
    (qHashPre + (1 + (1 + q))) (1 + (1 + q))

variable (original : PqxdhAuthenticatedRootExperiment.Post (baseSpec := baseSpec) program.Selection S (B + 1))

/-- Each complete guard-free early source game is connected to the ordinary random game by the existing adaptive raw CTX reductions, with its whole prefix and both possible continuations charged. -/
theorem source_random (c : PqxdhAuthenticatedRootBudgets.Certificate env0 baseImpl kem program original)
    (depth qHashPre qUniformPre : Nat) (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery) (bit : Bool)
    (hashBound : (PqxdhLaterChallengeGeneratedContinuation.run setup env callbacks program adversary owner number bit
      attachedVerify primitives baseImpl kem ancestors disclosed depth).IsQueryBoundP (HashClass true) qHashPre)
    (uniformBound : (PqxdhLaterChallengeGeneratedContinuation.run setup env callbacks program adversary owner number bit
      attachedVerify primitives baseImpl kem ancestors disclosed depth).IsQueryBoundP (HashClass false) qUniformPre)
    (small : 1 + (1 + q) < 2 ^ 96) :
    𝒟[source setup env callbacks program adversary owner number attachedVerify primitives baseImpl kem ancestors disclosed budget bounded depth bit] {true} ≤
      𝒟[Prod.fst <$> (simulateQ impl (compiled depth budget bounded bit bit)).run randomInitial] {true} +
        loss setup env callbacks program adversary owner number attachedVerify primitives baseImpl kem ancestors disclosed budget bounded depth qHashPre fallback bit ∧
    𝒟[Prod.fst <$> (simulateQ impl (compiled depth budget bounded bit bit)).run randomInitial] {true} ≤
      𝒟[source setup env callbacks program adversary owner number attachedVerify primitives baseImpl kem ancestors disclosed budget bounded depth bit] {true} +
        loss setup env callbacks program adversary owner number attachedVerify primitives baseImpl kem ancestors disclosed budget bounded depth qHashPre fallback bit := by
  have bills := PqxdhLaterChallengeEarlyResources.compiled_bills setup env callbacks program adversary owner number attachedVerify primitives baseImpl kem
    ancestors disclosed original c depth qHashPre qUniformPre budget bounded bit bit hashBound uniformBound
  have paired := PqxdhFirstRecordConfidentiality.source_random (RawCtxUniversalDecoder.decoder env.decode) env.source.crypto
    (compiled depth budget bounded bit bit) fallback (qHashPre + (1 + (1 + q))) (1 + (1 + q)) (1 + (1 + q))
    bills.2.1 bills.2.2.1 bills.2.2.2 small
  simpa only [randomView_collapse, source, loss] using paired

/-- The two complete source-derived reductions inherit the checked full-history random middle and ordinary CTX losses. Both initial Builder and before continuations are retained. No honest-target or resource-guard premise is added; address alias, source-event/freshness/refusal joins and remaining phases are still separate obligations. -/
theorem pair (c : PqxdhAuthenticatedRootBudgets.Certificate env0 baseImpl kem program original)
    (depth qHashPre qUniformPre : Nat)
    (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery)
    (hashBound : ∀ bit, (PqxdhLaterChallengeGeneratedContinuation.run setup env callbacks program adversary owner number bit
      attachedVerify primitives baseImpl kem ancestors disclosed depth).IsQueryBoundP (HashClass true) qHashPre)
    (uniformBound : ∀ bit, (PqxdhLaterChallengeGeneratedContinuation.run setup env callbacks program adversary owner number bit
      attachedVerify primitives baseImpl kem ancestors disclosed depth).IsQueryBoundP (HashClass false) qUniformPre)
    (small : 1 + (1 + q) < 2 ^ 96) :
    𝒟[source setup env callbacks program adversary owner number attachedVerify primitives baseImpl kem ancestors disclosed budget bounded depth false] {true} ≤
      𝒟[source setup env callbacks program adversary owner number attachedVerify primitives baseImpl kem ancestors disclosed budget bounded depth true] {true} +
        (loss setup env callbacks program adversary owner number attachedVerify primitives baseImpl kem ancestors disclosed budget bounded depth qHashPre fallback false +
         loss setup env callbacks program adversary owner number attachedVerify primitives baseImpl kem ancestors disclosed budget bounded depth qHashPre fallback true) ∧
    𝒟[source setup env callbacks program adversary owner number attachedVerify primitives baseImpl kem ancestors disclosed budget bounded depth true] {true} ≤
      𝒟[source setup env callbacks program adversary owner number attachedVerify primitives baseImpl kem ancestors disclosed budget bounded depth false] {true} +
        (loss setup env callbacks program adversary owner number attachedVerify primitives baseImpl kem ancestors disclosed budget bounded depth qHashPre fallback false +
         loss setup env callbacks program adversary owner number attachedVerify primitives baseImpl kem ancestors disclosed budget bounded depth qHashPre fallback true) := by
  have first := source_random setup env callbacks program adversary owner number attachedVerify primitives baseImpl kem ancestors disclosed
    budget bounded original c depth qHashPre qUniformPre fallback false (hashBound false) (uniformBound false) small
  have second := source_random setup env callbacks program adversary owner number attachedVerify primitives baseImpl kem ancestors disclosed
    budget bounded original c depth qHashPre qUniformPre fallback true (hashBound true) (uniformBound true) small
  have equal := PqxdhLaterChallengeEarlyCertified.random setup env callbacks program adversary owner number attachedVerify primitives baseImpl kem
    ancestors disclosed depth budget bounded
  rw [equal] at first
  constructor
  · have bound := _root_.add_le_add second.2 (le_refl
      (loss setup env callbacks program adversary owner number attachedVerify primitives baseImpl kem ancestors disclosed budget bounded depth qHashPre fallback false))
    exact (first.1.trans bound).trans_eq (by ac_rfl)
  · have bound := _root_.add_le_add first.2 (le_refl
      (loss setup env callbacks program adversary owner number attachedVerify primitives baseImpl kem ancestors disclosed budget bounded depth qHashPre fallback true))
    exact (second.1.trans bound).trans_eq (by ac_rfl)

end BeaconcryptCore.Computational.PqxdhLaterChallengeEarlyPrivacy

/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeEarlyPrivacy.source_random' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeEarlyPrivacy.source_random

/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeEarlyPrivacy.pair' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeEarlyPrivacy.pair
