-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhLaterChallengeBeforeUnguarded

/-! The actual source budget removes the resource guard from the complete before-source privacy reductions and their explicit query accounting. -/
open OracleComp OracleSpec CoreModels Aeneas OracleComp.ProgramLogic.Relational
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhLaterChallengeCertifiedPrivacy
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
local notation "compiled" => PqxdhLaterChallengeBeforeUnguarded.compiled setup env callbacks program adversary owner number attachedVerify primitives baseImpl kem ancestors disclosed

/-- The concrete ordinary selected-key game now runs the complete source-derived reduction without a semantic Fits test. -/
noncomputable def source (depth : Nat) (bit : Bool) : ProbComp Bool :=
  Prod.fst <$> AdaptiveCtxDynamicKnownKeys.sourceGame true (RawCtxUniversalDecoder.decoder env.decode) env.source.crypto
    (compiled depth budget bounded bit bit)

/-- Each loss names the guard-free complete source reduction and charges the original prefix plus both saved-wrapper allowances. -/
noncomputable def loss (depth qHashPre : Nat) (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery) (bit : Bool) :=
  privacyLoss (RawCtxUniversalDecoder.decoder env.decode) env.source.crypto (compiled depth budget bounded bit bit) fallback
    (qHashPre + (1 + (1 + q))) (1 + (1 + q))

/-- Removing the source-discharged guard preserves the complete ordinary CTX query bill, including the full prelude. Uniform bounds here concern the prefix; the actual suffix uniform allowance remains separately charged. -/
theorem bills (depth qHashPre qUniformPre : Nat) (prefixBit continuationBit : Bool)
    (hashBound : (PqxdhLaterChallengeGeneratedContinuation.run setup env callbacks program adversary owner number prefixBit
      attachedVerify primitives baseImpl kem ancestors disclosed depth).IsQueryBoundP (HashClass true) qHashPre)
    (uniformBound : (PqxdhLaterChallengeGeneratedContinuation.run setup env callbacks program adversary owner number prefixBit
      attachedVerify primitives baseImpl kem ancestors disclosed depth).IsQueryBoundP (HashClass false) qUniformPre) :
    (compiled depth budget bounded prefixBit continuationBit).IsQueryBoundP
      (AdaptiveCtxDynamicKnownBounds.TargetClass AdaptiveCtxQueryBounds.SourceSeal) (1 + (1 + q)) ∧
    (compiled depth budget bounded prefixBit continuationBit).IsQueryBoundP
      (AdaptiveCtxDynamicKnownBounds.TargetClass AdaptiveCtxReceive.IsRawQuery) (1 + (1 + q)) ∧
    (compiled depth budget bounded prefixBit continuationBit).IsQueryBoundP
      AdaptiveCtxDynamicKnownBounds.HashRoute (qHashPre + (1 + (1 + q))) := by
  rw [PqxdhLaterChallengeBeforeUnguarded.compiled_eq]
  exact PqxdhLaterChallengeRandomCompiled.bills setup env callbacks program adversary owner number attachedVerify primitives baseImpl kem
    ancestors disclosed depth (1 + q) qHashPre qUniformPre prefixBit continuationBit hashBound uniformBound

/-- The two complete source-derived reductions inherit the checked full-history random middle and ordinary CTX losses. No honest-target or resource-guard premise is added; address alias, source-event/refusal joins and remaining phases are still separate obligations. -/
theorem pair (depth qHashPre qUniformPre : Nat)
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
  simpa only [source, loss, PqxdhLaterChallengeBeforeUnguarded.compiled_eq, PqxdhLaterChallengeBeforePrivacy.source,
    PqxdhLaterChallengeBeforePrivacy.loss] using
    PqxdhLaterChallengeBeforePrivacy.pair setup env callbacks program adversary owner number attachedVerify primitives baseImpl kem
      ancestors disclosed depth (1 + q) qHashPre qUniformPre fallback hashBound uniformBound small

end BeaconcryptCore.Computational.PqxdhLaterChallengeCertifiedPrivacy

/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeCertifiedPrivacy.bills' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeCertifiedPrivacy.bills

/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeCertifiedPrivacy.pair' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeCertifiedPrivacy.pair
