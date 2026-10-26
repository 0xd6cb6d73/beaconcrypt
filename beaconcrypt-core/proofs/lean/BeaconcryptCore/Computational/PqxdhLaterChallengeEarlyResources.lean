-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhLaterChallengeEarlyCertified
import BeaconcryptCore.Computational.PqxdhLaterChallengeBuilderBills
import BeaconcryptCore.Computational.PqxdhLaterChallengeRandomCompiled

/-! Bill the complete generated prefix and either source-derived early continuation in all four query classes. -/
open OracleComp OracleSpec CoreModels Aeneas OracleComp.ProgramLogic.Relational
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhLaterChallengeEarlyResources
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

open PqxdhLaterChallengeEarlyCertified

/-- Both actual early callbacks and their entire selected continuations are billed at the original source allowance. No branch makes adaptive opening attempts free. -/
theorem continuation_bills (q : Nat) (bit : Bool)
    (result : Certified setup program owner number (M := M) (P := P) (I := I) (K := K)
      (X := X) (Response := Response) (A := A) (KemSK := KemSK) q)
    (bounded : ∀ selection reply, (adversary selection reply).IsTotalQueryBound q) :
    (continuation setup env callbacks program adversary owner number attachedVerify primitives baseImpl kem q bit result).IsQueryBoundP
      (AdaptiveCtxDynamicKnownBounds.TargetClass AdaptiveCtxQueryBounds.SourceSeal) (1 + (1 + q)) ∧
    (continuation setup env callbacks program adversary owner number attachedVerify primitives baseImpl kem q bit result).IsQueryBoundP
      (AdaptiveCtxDynamicKnownBounds.TargetClass AdaptiveCtxReceive.IsRawQuery) (1 + (1 + q)) ∧
    (continuation setup env callbacks program adversary owner number attachedVerify primitives baseImpl kem q bit result).IsQueryBoundP
      AdaptiveCtxDynamicKnownBounds.HashRoute (1 + (1 + q)) := by
  unfold continuation
  split
  · simpa only [PqxdhLaterChallengeBeforeUnguarded.client_eq] using
      PqxdhLaterChallengeBeforeConsumer.client_bills setup env callbacks program owner number attachedVerify primitives baseImpl kem
        (1 + q) bit (PqxdhLaterChallengeGeneratedBeforeObservation.beforeKey setup program (result.1, ∅))
  · exact PqxdhLaterChallengeBuilderBills.client_bills setup env callbacks program adversary owner number attachedVerify primitives baseImpl kem
      (1 + q) bit _ (fun selection reply => (bounded selection reply).mono (by omega))

variable (original : PqxdhAuthenticatedRootExperiment.Post (baseSpec := baseSpec) program.Selection S (B + 1))

/-- Both source-derived early callbacks pay the complete uniform bill, including the actual original primitive, base and auxiliary callback allowances. -/
theorem continuation_uniform (c : PqxdhAuthenticatedRootBudgets.Certificate env0 baseImpl kem program original)
    (q : Nat) (bit : Bool)
    (result : Certified setup program owner number (M := M) (P := P) (I := I) (K := K)
      (X := X) (Response := Response) (A := A) (KemSK := KemSK) q)
    (bounded : ∀ selection reply, (adversary selection reply).IsTotalQueryBound q) :
    (continuation setup env callbacks program adversary owner number attachedVerify primitives baseImpl kem q bit result).IsQueryBoundP
      AdaptiveCtxDynamicKnownBounds.UniformRoute
      (PqxdhLaterChallengeBeforeResources.suffixAllowance setup env callbacks program baseImpl kem original c (1 + q)) := by
  unfold continuation
  split
  · exact PqxdhLaterChallengeBeforeResources.client_uniform setup env callbacks program owner number attachedVerify primitives baseImpl kem
      original c (1 + q) bit _ _
  · exact PqxdhLaterChallengeBuilderBills.client_uniform setup env callbacks program adversary owner number attachedVerify primitives baseImpl kem
      original c (1 + q) bit _ (fun selection reply => (bounded selection reply).mono (by omega))

/-- The complete guard-free source reduction bills its actual full prefix and either early continuation in all four component query classes. -/
theorem compiled_bills (c : PqxdhAuthenticatedRootBudgets.Certificate env0 baseImpl kem program original)
    (depth qHashPre qUniformPre : Nat) (budget : PqxdhPhase2SourceSchedulerBounds.Budget)
    (bounded : PqxdhRecordConfidentialityChallenge.AdvBounded program owner adversary budget)
    (prefixBit continuationBit : Bool)
    (hashBound : (PqxdhLaterChallengeGeneratedContinuation.run setup env callbacks program adversary owner number prefixBit
      attachedVerify primitives baseImpl kem ancestors disclosed depth).IsQueryBoundP (HashClass true) qHashPre)
    (uniformBound : (PqxdhLaterChallengeGeneratedContinuation.run setup env callbacks program adversary owner number prefixBit
      attachedVerify primitives baseImpl kem ancestors disclosed depth).IsQueryBoundP (HashClass false) qUniformPre) :
    let q := FinitePartitionQueryBounds.bill (fun _ => 1) budget
    (compiled setup env callbacks program adversary owner number attachedVerify primitives baseImpl kem ancestors disclosed
      depth budget bounded prefixBit continuationBit).IsQueryBoundP AdaptiveCtxDynamicKnownBounds.UniformRoute
      (qUniformPre + PqxdhLaterChallengeBeforeResources.suffixAllowance setup env callbacks program baseImpl kem original c (1 + q)) ∧
    (compiled setup env callbacks program adversary owner number attachedVerify primitives baseImpl kem ancestors disclosed
      depth budget bounded prefixBit continuationBit).IsQueryBoundP AdaptiveCtxDynamicKnownBounds.HashRoute (qHashPre + (1 + (1 + q))) ∧
    (compiled setup env callbacks program adversary owner number attachedVerify primitives baseImpl kem ancestors disclosed
      depth budget bounded prefixBit continuationBit).IsQueryBoundP
      (AdaptiveCtxDynamicKnownBounds.TargetClass AdaptiveCtxQueryBounds.SourceSeal) (1 + (1 + q)) ∧
    (compiled setup env callbacks program adversary owner number attachedVerify primitives baseImpl kem ancestors disclosed
      depth budget bounded prefixBit continuationBit).IsQueryBoundP
      (AdaptiveCtxDynamicKnownBounds.TargetClass AdaptiveCtxReceive.IsRawQuery) (1 + (1 + q)) := by
  dsimp only
  rw [← PqxdhLaterChallengeGeneratedFits.certified_erase setup env callbacks program adversary owner number prefixBit
    attachedVerify primitives baseImpl kem ancestors disclosed depth budget bounded, isQueryBoundP_map_iff] at hashBound uniformBound
  have forwarded := RawCtxPrefixKeyOrder.forward_bills _ qHashPre qUniformPre hashBound uniformBound
  have total := PqxdhLaterChallengeGeneratedFits.adversary_total setup program adversary owner budget bounded
  have suffix := fun result => continuation_bills setup env callbacks program adversary owner number
    attachedVerify primitives baseImpl kem _ continuationBit result total
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact isQueryBoundP_bind forwarded.2.1 (fun result _ => continuation_uniform setup env callbacks program adversary owner number
      attachedVerify primitives baseImpl kem original c _ continuationBit result total)
  · exact isQueryBoundP_bind forwarded.1 (fun result _ => (suffix result).2.2)
  · simpa only [Nat.zero_add, compiled] using isQueryBoundP_bind forwarded.2.2.1 (fun result _ => (suffix result).1)
  · simpa only [Nat.zero_add, compiled] using isQueryBoundP_bind forwarded.2.2.2 (fun result _ => (suffix result).2.1)

end BeaconcryptCore.Computational.PqxdhLaterChallengeEarlyResources

/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeEarlyResources.continuation_bills' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeEarlyResources.continuation_bills

/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeEarlyResources.continuation_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeEarlyResources.continuation_uniform

/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeEarlyResources.compiled_bills' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeEarlyResources.compiled_bills
