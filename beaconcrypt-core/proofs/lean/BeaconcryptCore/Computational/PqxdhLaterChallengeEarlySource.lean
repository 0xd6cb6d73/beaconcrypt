-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhLaterChallengeEarlyPrivacy
import BeaconcryptCore.Computational.PqxdhLaterChallengeSourceBills
import BeaconcryptCore.Computational.PqxdhLaterSharedMessageResources
import BeaconcryptCore.Computational.PqxdhLaterChallengeCertifiedPrivacy

/-! Discharge the complete early source comparison resources from the original concrete generator and callback interfaces. -/
open OracleComp OracleSpec CoreModels Aeneas OracleComp.ProgramLogic.Relational
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhLaterChallengeEarlySource
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
local notation "Key" => PqxdhLaterChallengeGeneratedBeforeObservation.Key setup program (M := M) (P := P) (I := I) (K := K) (A := A) (X := X) (Response := Response) (KemSK := KemSK)

open PqxdhSourceSharedPreparationResources PqxdhLaterSharedMessageResources
variable (qSelector qLocal qPeer qPlaintext qWriter : Nat)
    (selectorBound : ∀ secret query state,
      (evalKem baseImpl kem secret ((borrowedSelector attachedVerify primitives 1 query).run state)).IsTotalQueryBound qSelector)
    (localBound : ∀ secret query state, PqxdhOrdinaryNativeCache.sourceSafe query →
      ((PqxdhOrdinaryNativeCache.cacheFree attachedVerify primitives 1 env.source env.localImpl baseImpl kem secret query).run state).IsTotalQueryBound qLocal)
    (peerBound : ∀ state, (callbacks.reservePeer.run state).IsTotalQueryBound qPeer)
    (plaintextBound : ∀ size state, ((callbacks.reservePlaintext size).run state).IsTotalQueryBound qPlaintext)
    (writerBound : ∀ fields state, ((callbacks.responseWrite fields).run state).IsTotalQueryBound qWriter)

variable (qEphemeral qEncaps : Nat)
    (ephemeralBound : (simulateQ (kemAmbientImpl baseImpl) env.ephemeralGen).IsTotalQueryBound qEphemeral)
    (nativeEncapsBound : ∀ target, (simulateQ (kemAmbientImpl baseImpl) (env.native.encaps target)).IsTotalQueryBound qEncaps)
    (encapsBound : ∀ target, (simulateQ (kemAmbientImpl baseImpl) (kem.encaps target)).IsTotalQueryBound qEncaps)

variable (qPre qOne qPhase1Write qMain : Nat)
    (preBound : ∀ identity, (simulateQ (kemAmbientImpl baseImpl) (setup.prekey identity)).IsTotalQueryBound qPre)
    (oneBound : ∀ identity before target, (simulateQ (kemAmbientImpl baseImpl) (setup.oneTime identity before target)).IsTotalQueryBound qOne)
    (phase1WriteBound : ∀ candidate state, ((callbacks.phase1Write candidate).run state).IsTotalQueryBound qPhase1Write)
    (mainBound : ∀ published, (program.main published).IsTotalQueryBound qMain)


variable (qKeygen : Nat)
    (keygenBound : (simulateQ (kemAmbientImpl baseImpl) kem.keygen).IsTotalQueryBound qKeygen)

variable (budget : PqxdhPhase2SourceSchedulerBounds.Budget)
    (bounded : PqxdhRecordConfidentialityChallenge.AdvBounded program owner adversary budget)
    (original : PqxdhAuthenticatedRootExperiment.Post (baseSpec := baseSpec) program.Selection S (B + 1))
local notation "q" => FinitePartitionQueryBounds.bill (fun _ => 1) budget

open PqxdhLaterChallengeSourceBills (hashAllowance uniformAllowance prefix_bills)

include bounded selectorBound localBound peerBound plaintextBound writerBound ephemeralBound nativeEncapsBound encapsBound
    preBound oneBound phase1WriteBound mainBound keygenBound in
/-- Every query class of the same complete guard-free Builder/before reduction is billed from original source calls: full uniform work, public hashes, selected seals and adaptive raw openings. -/
theorem source_bills (c : PqxdhAuthenticatedRootBudgets.Certificate env0 baseImpl kem program original)
    (depth : Nat) (prefixBit continuationBit : Bool) :
    (PqxdhLaterChallengeEarlyCertified.compiled setup env callbacks program adversary owner number attachedVerify primitives baseImpl kem ancestors disclosed
      depth budget bounded prefixBit continuationBit).IsQueryBoundP AdaptiveCtxDynamicKnownBounds.UniformRoute
      (uniformAllowance setup env callbacks program baseImpl kem qSelector qLocal qPeer qPlaintext qWriter qEphemeral qEncaps
          qPre qOne qPhase1Write qMain qKeygen budget original c +
        PqxdhLaterChallengeBeforeResources.suffixAllowance setup env callbacks program baseImpl kem original c (1 + q)) ∧
    (PqxdhLaterChallengeEarlyCertified.compiled setup env callbacks program adversary owner number attachedVerify primitives baseImpl kem ancestors disclosed
      depth budget bounded prefixBit continuationBit).IsQueryBoundP AdaptiveCtxDynamicKnownBounds.HashRoute
      (hashAllowance qMain budget + (1 + (1 + q))) ∧
    (PqxdhLaterChallengeEarlyCertified.compiled setup env callbacks program adversary owner number attachedVerify primitives baseImpl kem ancestors disclosed
      depth budget bounded prefixBit continuationBit).IsQueryBoundP
      (AdaptiveCtxDynamicKnownBounds.TargetClass AdaptiveCtxQueryBounds.SourceSeal) (1 + (1 + q)) ∧
    (PqxdhLaterChallengeEarlyCertified.compiled setup env callbacks program adversary owner number attachedVerify primitives baseImpl kem ancestors disclosed
      depth budget bounded prefixBit continuationBit).IsQueryBoundP
      (AdaptiveCtxDynamicKnownBounds.TargetClass AdaptiveCtxReceive.IsRawQuery) (1 + (1 + q)) := by
  have preludeCaps := fun hash => prefix_bills setup env callbacks program adversary owner number attachedVerify primitives baseImpl kem ancestors disclosed
    qSelector qLocal qPeer qPlaintext qWriter selectorBound localBound peerBound plaintextBound writerBound
    qEphemeral qEncaps ephemeralBound nativeEncapsBound encapsBound qPre qOne qPhase1Write qMain
    preBound oneBound phase1WriteBound mainBound qKeygen keygenBound budget bounded original c depth prefixBit hash
  exact PqxdhLaterChallengeEarlyResources.compiled_bills setup env callbacks program adversary owner number attachedVerify primitives baseImpl kem
    ancestors disclosed original c depth _ _ budget bounded prefixBit continuationBit (preludeCaps true) (preludeCaps false)

include bounded selectorBound localBound peerBound plaintextBound writerBound ephemeralBound nativeEncapsBound encapsBound
    preBound oneBound phase1WriteBound mainBound keygenBound in
/-- The complete initial-Builder and before-source comparison has explicit ordinary CTX losses whose prefix bounds are derived from original source interfaces, with the full uniform ledger established by `source_bills`. Remaining event, alias, refusal and phase joins are unchanged. -/
theorem pair (c : PqxdhAuthenticatedRootBudgets.Certificate env0 baseImpl kem program original)
    (depth : Nat) (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery)
    (small : 1 + (1 + q) < 2 ^ 96) :
    𝒟[PqxdhLaterChallengeEarlyPrivacy.source setup env callbacks program adversary owner number attachedVerify primitives baseImpl kem ancestors disclosed budget bounded depth false] {true} ≤
      𝒟[PqxdhLaterChallengeEarlyPrivacy.source setup env callbacks program adversary owner number attachedVerify primitives baseImpl kem ancestors disclosed budget bounded depth true] {true} +
        (PqxdhLaterChallengeEarlyPrivacy.loss setup env callbacks program adversary owner number attachedVerify primitives baseImpl kem ancestors disclosed budget bounded depth (hashAllowance qMain budget) fallback false +
         PqxdhLaterChallengeEarlyPrivacy.loss setup env callbacks program adversary owner number attachedVerify primitives baseImpl kem ancestors disclosed budget bounded depth (hashAllowance qMain budget) fallback true) ∧
    𝒟[PqxdhLaterChallengeEarlyPrivacy.source setup env callbacks program adversary owner number attachedVerify primitives baseImpl kem ancestors disclosed budget bounded depth true] {true} ≤
      𝒟[PqxdhLaterChallengeEarlyPrivacy.source setup env callbacks program adversary owner number attachedVerify primitives baseImpl kem ancestors disclosed budget bounded depth false] {true} +
        (PqxdhLaterChallengeEarlyPrivacy.loss setup env callbacks program adversary owner number attachedVerify primitives baseImpl kem ancestors disclosed budget bounded depth (hashAllowance qMain budget) fallback false +
         PqxdhLaterChallengeEarlyPrivacy.loss setup env callbacks program adversary owner number attachedVerify primitives baseImpl kem ancestors disclosed budget bounded depth (hashAllowance qMain budget) fallback true) := by
  have preludeCaps := fun bit hash => prefix_bills setup env callbacks program adversary owner number attachedVerify primitives baseImpl kem ancestors disclosed
    qSelector qLocal qPeer qPlaintext qWriter selectorBound localBound peerBound plaintextBound writerBound
    qEphemeral qEncaps ephemeralBound nativeEncapsBound encapsBound qPre qOne qPhase1Write qMain
    preBound oneBound phase1WriteBound mainBound qKeygen keygenBound budget bounded original c depth bit hash
  exact PqxdhLaterChallengeEarlyPrivacy.pair setup env callbacks program adversary owner number attachedVerify primitives baseImpl kem ancestors disclosed
    budget bounded original c depth _ _ fallback (fun bit => preludeCaps bit true) (fun bit => preludeCaps bit false) small

end BeaconcryptCore.Computational.PqxdhLaterChallengeEarlySource

/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeEarlySource.source_bills' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeEarlySource.source_bills

/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeEarlySource.pair' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeEarlySource.pair
