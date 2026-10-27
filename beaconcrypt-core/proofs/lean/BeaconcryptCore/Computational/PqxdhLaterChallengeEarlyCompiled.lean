-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhLaterChallengeEarlyConsumer
import BeaconcryptCore.Computational.PqxdhLaterChallengeRandomCompiled

/-! Compile both early callbacks into one ordinary oracle program without reading or resetting component history. -/
open OracleComp OracleSpec CoreModels Aeneas OracleComp.ProgramLogic.Relational
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhLaterChallengeEarlyCompiled
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

/-- Dispatch both actual early callbacks without reading component history. The old before branch will be replaced by its source-certified equal client. -/
noncomputable def continuation (qPost : Nat) (bit : Bool) (result : Carrier × Option program.Selection)
    (cache : CtxRO.QueryCache) : OracleComp AdaptiveCtxDynamicKnownKeys.Spec Bool :=
  match PqxdhLaterChallengeRandomEarly.sourceKey setup program (result, cache) with
  | none => PqxdhLaterChallengeBeforeConsumer.client setup env callbacks program owner number attachedVerify primitives baseImpl kem qPost bit
      (PqxdhLaterChallengeGeneratedBeforeObservation.beforeKey setup program (result, ∅))
  | some payload => PqxdhLaterChallengeBuilderConsumer.client setup env callbacks program adversary owner number attachedVerify primitives baseImpl kem qPost bit
      (some payload)

/-- The public-cache observation coordinate is ignored by the actual early client, and never installed into the component interpreter. -/
theorem cache_irrelevant (qPost : Nat) (bit : Bool) (result : Carrier × Option program.Selection)
    (first second : CtxRO.QueryCache) :
    continuation setup env callbacks program adversary owner number attachedVerify primitives baseImpl kem qPost bit result first =
    continuation setup env callbacks program adversary owner number attachedVerify primitives baseImpl kem qPost bit result second := by
  rcases result with ⟨⟨⟨credentials, ⟨⟨⟨packet, parent⟩, target⟩, nonce, next⟩⟩, captured⟩, selection⟩
  rcases packet with decision | ⟨stored, decision | ⟨⟨original, trace, origin⟩, localState⟩⟩
  · rfl
  · rfl
  · cases captured with
    | some details => rfl
    | none =>
      cases original with
      | inl request => rfl
      | inr saved => cases selection <;> rfl

/-- The full-state proof observation executes exactly this source client from the same reached interpreter state, with no reset and no history-reading operation. -/
theorem resume_blind (qPost : Nat) (bit : Bool) (result : Carrier × Option program.Selection) (state : RandomState) :
    PqxdhLaterChallengeEarlyConsumer.resume setup env callbacks program adversary owner number attachedVerify primitives baseImpl kem qPost bit
      (PqxdhLaterChallengeRandomEarly.earlyKey setup program (result, state)) =
    Prod.fst <$> (simulateQ impl
      (continuation setup env callbacks program adversary owner number attachedVerify primitives baseImpl kem qPost bit result ∅)).run state := by
  rw [cache_irrelevant setup env callbacks program adversary owner number attachedVerify primitives baseImpl kem qPost bit result
    ∅ (PqxdhLaterChallengeRandomProjection.cache state)]
  simp only [PqxdhLaterChallengeRandomEarly.earlyKey]
  rw [PqxdhLaterChallengeRandomEarly.retained]
  cases key : PqxdhLaterChallengeRandomEarly.sourceKey setup program
      (result, PqxdhLaterChallengeRandomProjection.cache state) with
  | none =>
    simp only [key, Option.map_none, PqxdhLaterChallengeEarlyConsumer.resume, continuation]
    exact PqxdhLaterChallengeRandomCompiled.resume_blind setup env callbacks program owner number
      attachedVerify primitives baseImpl kem qPost bit result state
  | some payload => simp only [Option.map_some, PqxdhLaterChallengeEarlyConsumer.resume, continuation, key]

/-- A single ordinary oracle program forwards the complete generated source prefix and resumes either actual early callback without reading interpreter state. -/
noncomputable def client (depth qPost : Nat) (prefixBit continuationBit : Bool) :
    OracleComp AdaptiveCtxDynamicKnownKeys.Spec Bool := do
  let result ← simulateQ RawCtxSourceSharedRom.forward
    (PqxdhLaterChallengeGeneratedContinuation.run setup env callbacks program adversary owner number prefixBit
      attachedVerify primitives baseImpl kem ancestors disclosed depth)
  continuation setup env callbacks program adversary owner number attachedVerify primitives baseImpl kem qPost continuationBit result ∅

/-- The complete single-interpreter early program equals the full-prefix proof decomposition, including every actual prelude-created history and optional or complementary outcome. -/
theorem evaluated (depth qPost : Nat) (prefixBit continuationBit : Bool) :
    Prod.fst <$> (simulateQ impl (client setup env callbacks program adversary owner number attachedVerify primitives baseImpl kem ancestors disclosed
      depth qPost prefixBit continuationBit)).run randomInitial =
    PqxdhLaterChallengeEarlyConsumer.run setup env callbacks program adversary owner number attachedVerify primitives baseImpl kem ancestors disclosed
      depth qPost prefixBit continuationBit := by
  simp only [client, simulateQ_bind, StateT.run_bind, map_bind, PqxdhLaterChallengeEarlyConsumer.run,
    PqxdhLaterChallengeRandomBackend.forwarded]
  exact bind_congr fun result => (resume_blind setup env callbacks program adversary owner number attachedVerify primitives baseImpl kem
    qPost continuationBit result.1 result.2).symm

/-- The concrete single-interpreter generated early game has equal success probability in both random challenge worlds; no backend-state operation is available to its client. -/
theorem random (depth qPost : Nat) :
    𝒟[Prod.fst <$> (simulateQ impl (client setup env callbacks program adversary owner number attachedVerify primitives baseImpl kem ancestors disclosed
      depth qPost false false)).run randomInitial] {true} =
    𝒟[Prod.fst <$> (simulateQ impl (client setup env callbacks program adversary owner number attachedVerify primitives baseImpl kem ancestors disclosed
      depth qPost true true)).run randomInitial] {true} := by
  rw [evaluated, evaluated]
  exact PqxdhLaterChallengeEarlyConsumer.random setup env callbacks program adversary owner number attachedVerify primitives baseImpl kem
    ancestors disclosed depth qPost

end BeaconcryptCore.Computational.PqxdhLaterChallengeEarlyCompiled

/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeEarlyCompiled.cache_irrelevant' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeEarlyCompiled.cache_irrelevant

/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeEarlyCompiled.resume_blind' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeEarlyCompiled.resume_blind

/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeEarlyCompiled.evaluated' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeEarlyCompiled.evaluated

/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeEarlyCompiled.random' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeEarlyCompiled.random
