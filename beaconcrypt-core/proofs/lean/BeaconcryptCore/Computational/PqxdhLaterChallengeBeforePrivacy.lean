-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhLaterChallengeRandomCompiled

/-! Execute the actual source-derived before callback with its literal private credentials and retained parent material, keeping all refusal and terminal monitor events. -/
open OracleComp OracleSpec CoreModels Aeneas OracleComp.ProgramLogic.Relational
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhLaterChallengeBeforePrivacy
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

local notation "compiled" => PqxdhLaterChallengeRandomCompiled.client setup env callbacks program adversary owner number attachedVerify primitives baseImpl kem ancestors disclosed

/-- The ordinary selected-key source experiment of the actual generated prefix and saved before continuation. -/
noncomputable def source (depth qPost : Nat) (bit : Bool) : ProbComp Bool :=
  Prod.fst <$> AdaptiveCtxDynamicKnownKeys.sourceGame true (RawCtxUniversalDecoder.decoder env.decode) env.source.crypto
    (compiled depth qPost bit bit)

/-- Every loss names the constructed complete prefix-and-continuation reduction and includes the actual forwarded prefix hash allowance. -/
noncomputable def loss (depth qPost qHashPre : Nat) (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery) (bit : Bool) :=
  privacyLoss (RawCtxUniversalDecoder.decoder env.decode) env.source.crypto (compiled depth qPost bit bit) fallback
    (qHashPre + (1 + qPost)) (1 + qPost)

/-- Each actual generated source world is connected to its ordinary random interpretation by the existing adaptive CTX reduction, with the complete prefix included in its bill. -/
theorem source_random (depth qPost qHashPre qUniformPre : Nat)
    (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery) (bit : Bool)
    (hashBound : (PqxdhLaterChallengeGeneratedContinuation.run setup env callbacks program adversary owner number bit
      attachedVerify primitives baseImpl kem ancestors disclosed depth).IsQueryBoundP (HashClass true) qHashPre)
    (uniformBound : (PqxdhLaterChallengeGeneratedContinuation.run setup env callbacks program adversary owner number bit
      attachedVerify primitives baseImpl kem ancestors disclosed depth).IsQueryBoundP (HashClass false) qUniformPre)
    (small : 1 + qPost < 2 ^ 96) :
    𝒟[source setup env callbacks program adversary owner number attachedVerify primitives baseImpl kem ancestors disclosed depth qPost bit] {true} ≤
      𝒟[Prod.fst <$> (simulateQ impl (compiled depth qPost bit bit)).run randomInitial] {true} +
        loss setup env callbacks program adversary owner number attachedVerify primitives baseImpl kem ancestors disclosed depth qPost qHashPre fallback bit ∧
    𝒟[Prod.fst <$> (simulateQ impl (compiled depth qPost bit bit)).run randomInitial] {true} ≤
      𝒟[source setup env callbacks program adversary owner number attachedVerify primitives baseImpl kem ancestors disclosed depth qPost bit] {true} +
        loss setup env callbacks program adversary owner number attachedVerify primitives baseImpl kem ancestors disclosed depth qPost qHashPre fallback bit := by
  have bounded := PqxdhLaterChallengeRandomCompiled.bills setup env callbacks program adversary owner number attachedVerify primitives baseImpl kem ancestors disclosed
    depth qPost qHashPre qUniformPre bit bit hashBound uniformBound
  have paired := PqxdhFirstRecordConfidentiality.source_random (RawCtxUniversalDecoder.decoder env.decode) env.source.crypto
    (compiled depth qPost bit bit) fallback (qHashPre + (1 + qPost)) (1 + qPost) (1 + qPost) bounded.2.2 bounded.1 bounded.2.1 small
  simpa only [randomView_collapse, source, loss] using paired

/-- Both generated before-source worlds are connected by the two explicitly constructed ordinary CTX reductions. The random middle is the checked full-history compiled game; there is no guessed prefix or reset state. -/
theorem pair (depth qPost qHashPre qUniformPre : Nat)
    (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery)
    (hashBound : ∀ bit, (PqxdhLaterChallengeGeneratedContinuation.run setup env callbacks program adversary owner number bit
      attachedVerify primitives baseImpl kem ancestors disclosed depth).IsQueryBoundP (HashClass true) qHashPre)
    (uniformBound : ∀ bit, (PqxdhLaterChallengeGeneratedContinuation.run setup env callbacks program adversary owner number bit
      attachedVerify primitives baseImpl kem ancestors disclosed depth).IsQueryBoundP (HashClass false) qUniformPre)
    (small : 1 + qPost < 2 ^ 96) :
    𝒟[source setup env callbacks program adversary owner number attachedVerify primitives baseImpl kem ancestors disclosed depth qPost false] {true} ≤
      𝒟[source setup env callbacks program adversary owner number attachedVerify primitives baseImpl kem ancestors disclosed depth qPost true] {true} +
        (loss setup env callbacks program adversary owner number attachedVerify primitives baseImpl kem ancestors disclosed depth qPost qHashPre fallback false +
         loss setup env callbacks program adversary owner number attachedVerify primitives baseImpl kem ancestors disclosed depth qPost qHashPre fallback true) ∧
    𝒟[source setup env callbacks program adversary owner number attachedVerify primitives baseImpl kem ancestors disclosed depth qPost true] {true} ≤
      𝒟[source setup env callbacks program adversary owner number attachedVerify primitives baseImpl kem ancestors disclosed depth qPost false] {true} +
        (loss setup env callbacks program adversary owner number attachedVerify primitives baseImpl kem ancestors disclosed depth qPost qHashPre fallback false +
         loss setup env callbacks program adversary owner number attachedVerify primitives baseImpl kem ancestors disclosed depth qPost qHashPre fallback true) := by
  have first := source_random setup env callbacks program adversary owner number attachedVerify primitives baseImpl kem ancestors disclosed
    depth qPost qHashPre qUniformPre fallback false (hashBound false) (uniformBound false) small
  have second := source_random setup env callbacks program adversary owner number attachedVerify primitives baseImpl kem ancestors disclosed
    depth qPost qHashPre qUniformPre fallback true (hashBound true) (uniformBound true) small
  have equal := PqxdhLaterChallengeRandomCompiled.random setup env callbacks program adversary owner number attachedVerify primitives baseImpl kem ancestors disclosed depth qPost
  rw [equal] at first
  constructor
  · have bound := _root_.add_le_add second.2 (le_refl
      (loss setup env callbacks program adversary owner number attachedVerify primitives baseImpl kem ancestors disclosed depth qPost qHashPre fallback false))
    exact (first.1.trans bound).trans_eq (by ac_rfl)
  · have bound := _root_.add_le_add first.2 (le_refl
      (loss setup env callbacks program adversary owner number attachedVerify primitives baseImpl kem ancestors disclosed depth qPost qHashPre fallback true))
    exact (second.1.trans bound).trans_eq (by ac_rfl)

end BeaconcryptCore.Computational.PqxdhLaterChallengeBeforePrivacy

/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeBeforePrivacy.source_random' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeBeforePrivacy.source_random

/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeBeforePrivacy.pair' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeBeforePrivacy.pair
