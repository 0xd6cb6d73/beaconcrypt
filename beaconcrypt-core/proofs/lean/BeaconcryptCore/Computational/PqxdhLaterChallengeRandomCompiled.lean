-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhLaterChallengeRandomConsumer

/-! Execute the actual source-derived before callback with its literal private credentials and retained parent material, keeping all refusal and terminal monitor events. -/
open OracleComp OracleSpec CoreModels Aeneas OracleComp.ProgramLogic.Relational
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhLaterChallengeRandomCompiled
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

/-- The concrete saved client never reads the proof-only native public-cache coordinate. Its complete local state, source context and compiled oracle calls remain unchanged. -/
theorem cache_irrelevant (qPost : Nat) (bit : Bool) (result : Carrier × Option program.Selection)
    (first second : CtxRO.QueryCache) :
    PqxdhLaterChallengeBeforeConsumer.client setup env callbacks program owner number attachedVerify primitives baseImpl kem qPost bit
      (PqxdhLaterChallengeGeneratedBeforeObservation.beforeKey setup program (result, first)) =
    PqxdhLaterChallengeBeforeConsumer.client setup env callbacks program owner number attachedVerify primitives baseImpl kem qPost bit
      (PqxdhLaterChallengeGeneratedBeforeObservation.beforeKey setup program (result, second)) := by
  rcases result with ⟨⟨⟨credentials, ⟨⟨⟨packet, parent⟩, target⟩, nonce, next⟩⟩, captured⟩, selection⟩
  rcases packet with decision | ⟨stored, decision | pending⟩
  · rfl
  · rfl
  · cases captured with
    | none => rfl
    | some details =>
      simp only [PqxdhLaterChallengeGeneratedBeforeObservation.beforeKey]
      split
      · simp only [PqxdhLaterChallengeBeforeConsumer.client]
        rfl
      · rfl

/-- The full-state proof observation executes exactly the state-blind source client at the same reached interpreter state. The empty cache below is an ignored observation coordinate, never an interpreter reset. -/
theorem resume_blind (qPost : Nat) (bit : Bool) (result : Carrier × Option program.Selection) (state : RandomState) :
    PqxdhLaterChallengeRandomConsumer.resume setup env callbacks program owner number attachedVerify primitives baseImpl kem qPost bit
      (PqxdhLaterChallengeRandomBefore.beforeKey setup program (result, state)) =
    Prod.fst <$> (simulateQ impl
      (PqxdhLaterChallengeBeforeConsumer.client setup env callbacks program owner number attachedVerify primitives baseImpl kem qPost bit
        (PqxdhLaterChallengeGeneratedBeforeObservation.beforeKey setup program (result, ∅)))).run state := by
  rw [cache_irrelevant setup env callbacks program owner number attachedVerify primitives baseImpl kem qPost bit result
    ∅ (PqxdhLaterChallengeRandomProjection.cache state), PqxdhLaterChallengeRandomBefore.retained]
  cases PqxdhLaterChallengeGeneratedBeforeObservation.beforeKey setup program
      (result, PqxdhLaterChallengeRandomProjection.cache state) with
  | none => rfl
  | some payload => rfl

/-- A single actual oracle program forwards the complete generated prelude, then executes the original saved client. It has no access to any challenger state or history. -/
noncomputable def client (depth qPost : Nat) (prefixBit continuationBit : Bool) :
    OracleComp AdaptiveCtxDynamicKnownKeys.Spec Bool := do
  let result ← simulateQ RawCtxSourceSharedRom.forward
    (PqxdhLaterChallengeGeneratedContinuation.run setup env callbacks program adversary owner number prefixBit
      attachedVerify primitives baseImpl kem ancestors disclosed depth)
  PqxdhLaterChallengeBeforeConsumer.client setup env callbacks program owner number attachedVerify primitives baseImpl kem qPost continuationBit
    (PqxdhLaterChallengeGeneratedBeforeObservation.beforeKey setup program (result, ∅))

/-- The proof decomposition equals the complete single-interpreter program, including the actual prefix-created histories and every optional/complementary outcome. -/
theorem evaluated (depth qPost : Nat) (prefixBit continuationBit : Bool) :
    Prod.fst <$> (simulateQ impl (client setup env callbacks program adversary owner number attachedVerify primitives baseImpl kem ancestors disclosed
      depth qPost prefixBit continuationBit)).run randomInitial =
    PqxdhLaterChallengeRandomConsumer.run setup env callbacks program adversary owner number attachedVerify primitives baseImpl kem ancestors disclosed
      depth qPost prefixBit continuationBit := by
  simp only [client, simulateQ_bind, StateT.run_bind, map_bind, PqxdhLaterChallengeRandomConsumer.run,
    PqxdhLaterChallengeRandomBackend.forwarded]
  exact bind_congr fun result => (resume_blind setup env callbacks program owner number attachedVerify primitives baseImpl kem
    qPost continuationBit result.1 result.2).symm

/-- The concrete single-interpreter generated before game has equal success probability in both random challenge worlds; no backend-state operation is available to its client. -/
theorem random (depth qPost : Nat) :
    𝒟[Prod.fst <$> (simulateQ impl (client setup env callbacks program adversary owner number attachedVerify primitives baseImpl kem ancestors disclosed
      depth qPost false false)).run randomInitial] {true} =
    𝒟[Prod.fst <$> (simulateQ impl (client setup env callbacks program adversary owner number attachedVerify primitives baseImpl kem ancestors disclosed
      depth qPost true true)).run randomInitial] {true} := by
  rw [evaluated, evaluated]
  exact PqxdhLaterChallengeRandomConsumer.random setup env callbacks program adversary owner number attachedVerify primitives baseImpl kem
    ancestors disclosed depth qPost

/-- The complete client includes the actual prefix hash cap and the entire saved continuation allowance. Selected seals and raw openings are absent only from the forwarding prefix, not from the continuation. -/
theorem bills (depth qPost qHashPre qUniformPre : Nat) (prefixBit continuationBit : Bool)
    (hashBound : (PqxdhLaterChallengeGeneratedContinuation.run setup env callbacks program adversary owner number prefixBit
      attachedVerify primitives baseImpl kem ancestors disclosed depth).IsQueryBoundP (HashClass true) qHashPre)
    (uniformBound : (PqxdhLaterChallengeGeneratedContinuation.run setup env callbacks program adversary owner number prefixBit
      attachedVerify primitives baseImpl kem ancestors disclosed depth).IsQueryBoundP (HashClass false) qUniformPre) :
    (client setup env callbacks program adversary owner number attachedVerify primitives baseImpl kem ancestors disclosed depth qPost prefixBit continuationBit).IsQueryBoundP
      (AdaptiveCtxDynamicKnownBounds.TargetClass AdaptiveCtxQueryBounds.SourceSeal) (1 + qPost) ∧
    (client setup env callbacks program adversary owner number attachedVerify primitives baseImpl kem ancestors disclosed depth qPost prefixBit continuationBit).IsQueryBoundP
      (AdaptiveCtxDynamicKnownBounds.TargetClass AdaptiveCtxReceive.IsRawQuery) (1 + qPost) ∧
    (client setup env callbacks program adversary owner number attachedVerify primitives baseImpl kem ancestors disclosed depth qPost prefixBit continuationBit).IsQueryBoundP
      AdaptiveCtxDynamicKnownBounds.HashRoute (qHashPre + (1 + qPost)) := by
  have forwarded := RawCtxPrefixKeyOrder.forward_bills _ qHashPre qUniformPre hashBound uniformBound
  have suffix := fun result => PqxdhLaterChallengeBeforeConsumer.client_bills setup env callbacks program owner number
    attachedVerify primitives baseImpl kem qPost continuationBit
    (PqxdhLaterChallengeGeneratedBeforeObservation.beforeKey setup program (result, ∅))
  refine ⟨?_, ?_, ?_⟩
  · simpa only [Nat.zero_add, client] using isQueryBoundP_bind forwarded.2.2.1 (fun result _ => (suffix result).1)
  · simpa only [Nat.zero_add, client] using isQueryBoundP_bind forwarded.2.2.2 (fun result _ => (suffix result).2.1)
  · exact isQueryBoundP_bind forwarded.1 (fun result _ => (suffix result).2.2)

end BeaconcryptCore.Computational.PqxdhLaterChallengeRandomCompiled

/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeRandomCompiled.cache_irrelevant' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeRandomCompiled.cache_irrelevant

/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeRandomCompiled.resume_blind' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeRandomCompiled.resume_blind

/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeRandomCompiled.evaluated' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeRandomCompiled.evaluated

/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeRandomCompiled.random' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeRandomCompiled.random

/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeRandomCompiled.bills' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeRandomCompiled.bills
