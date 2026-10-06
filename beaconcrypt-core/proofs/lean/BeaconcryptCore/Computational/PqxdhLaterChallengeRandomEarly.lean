-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhLaterChallengeRandomSampler
import BeaconcryptCore.Computational.PqxdhLaterChallengeBackendCollectorBefore
import BeaconcryptCore.Computational.PqxdhLaterChallengeRandomProjection
import BeaconcryptCore.Computational.PqxdhLaterChallengeGeneratedBeforeObservation
import BeaconcryptCore.Computational.PqxdhLaterChallengeBuilderObservation
import BeaconcryptCore.Computational.PqxdhLaterChallengeRandomBefore

/-! Retain initial Builder and before-admission source observations in the same complete generated ordinary-random experiment. -/
open OracleComp OracleSpec CoreModels Aeneas OracleComp.ProgramLogic.Relational
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhLaterChallengeRandomEarly
open PqxdhEd25519EufCma PqxdhJointIdentity PqxdhStatefulPhase1EufCma PqxdhPrivateKemSource
open PqxdhGeneratedBeaconState PqxdhPhase1AcceptanceOracle PqxdhKemIndCca PqxdhInitializerSecrecy
open CtxRomAuth AdaptiveCtxSharedHash PqxdhSecretInputKdf PqxdhFullSecretInputKdf
open PqxdhFirstRecordConfidentiality
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
local notation "backend" => PqxdhLaterChallengeRandomBackend.handler (RawCtxUniversalDecoder.decoder env.decode) env.source.crypto
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

open PqxdhLaterChallengeGeneratedBeforeObservation (inputKey)

/-- The actual initial Builder observation retains the private selected KEM packet, full source input, normalized callback, native state, material, selected continuation and complete random interpreter state. -/
noncomputable def builderKey (result : (Carrier × Option program.Selection) × RandomState) :=
  match result with
  | ((((credentials, (((Sum.inr (stored, Sum.inr pending), parent), target), nonce, next)), none), selection), cache) =>
      match pending.1.original with
      | .inr saved => some ((credentials, inputKey setup stored.1, stored.2,
          PqxdhLaterChallengeSavedMonitor.builderOnly saved pending.1.trace pending.1.origin,
          PqxdhNativeSharedPrefix.attach pending.2 (PqxdhLaterChallengeRandomProjection.cache cache),
          parent, target, nonce, next, selection), cache)
      | _ => none
  | _ => none

/-- Every non-Builder collector outcome contributes to the complete generated observation's complementary mass. -/
theorem encoded_none (packet : Packet) (start : Input) (output : HmacBlock) (bit : Bool)
    (continuation : PqxdhInitialBuilderContext.BuildResult → OracleComp
      (PqxdhFirstRecordConfidentiality.AdvSpec (SelectorSpec baseSpec) S (B + 1)) Bool)
    (parent : FullOutput) (nonce : NonceOutput) (next : RootOutput)
    (result : (Bool ⊕ (Pending × Option CaptureDetails)) × RandomState)
    (key : (PqxdhLaterChallengeBackendCollector.pendingView result).bind
      PqxdhLaterChallengeBuilderObservation.builderKey = none) :
    builderKey setup program (PqxdhLaterChallengeRandomSampler.finishSelected setup program packet parent nonce next
      (PqxdhLaterChallengeBackendGenerated.encodePrepared setup env callbacks owner number attachedVerify primitives baseImpl kem
        packet.secretKey packet.ciphertext start output bit continuation result)) = none := by
  rcases result with ⟨decision | ⟨⟨context, localState⟩, details⟩, cache⟩
  · rfl
  · cases details with
    | some details => rfl
    | none =>
      rcases context with ⟨original, trace, origin⟩
      cases original with
      | inl request => rfl
      | inr saved => cases key

/-- Completed and post-admission collector outcomes remain in the explicit complementary Builder outcome. -/
theorem encoded_residual (packet : Packet) (start : Input) (output : HmacBlock) (bit : Bool)
    (continuation : PqxdhInitialBuilderContext.BuildResult → OracleComp
      (PqxdhFirstRecordConfidentiality.AdvSpec (SelectorSpec baseSpec) S (B + 1)) Bool)
    (parent : FullOutput) (nonce : NonceOutput) (next : RootOutput)
    (result : (Bool ⊕ (Pending × Option CaptureDetails)) × RandomState)
    (residual : PqxdhLaterChallengeBackendCollector.Residual result) :
    builderKey setup program (PqxdhLaterChallengeRandomSampler.finishSelected setup program packet parent nonce next
      (PqxdhLaterChallengeBackendGenerated.encodePrepared setup env callbacks owner number attachedVerify primitives baseImpl kem
        packet.secretKey packet.ciphertext start output bit continuation result)) = none := by
  rcases result with ⟨decision | ⟨pending, details⟩, cache⟩
  · rfl
  · cases details with
    | some details => rfl
    | none => rcases residual with h | h <;> cases h

/-- A paired initial Builder cut retains the same generated material and actual selected callback in both complete source worlds. -/
theorem encoded_pending (packet : Packet) (start : Input) (output : HmacBlock) (first second : Bool)
    (continuation : PqxdhInitialBuilderContext.BuildResult → OracleComp
      (PqxdhFirstRecordConfidentiality.AdvSpec (SelectorSpec baseSpec) S (B + 1)) Bool)
    (parent : FullOutput) (nonce : NonceOutput) (next : RootOutput)
    (callback : PqxdhInitialOriginContext.Context (SelectorSpec baseSpec) M P (IdentityHandle I) (DhPair setup) (KemHandle K)
      PqxdhInitialBuilderContext.BuildResult Bool S (B + 1))
    (state : PqxdhNativeSharedPrefix.Local A (BareState 1) RootOracle.QueryCache × RandomState) :
    builderKey setup program (PqxdhLaterChallengeRandomSampler.finishSelected setup program packet parent nonce next
      (PqxdhLaterChallengeBackendGenerated.encodePrepared setup env callbacks owner number attachedVerify primitives baseImpl kem
        packet.secretKey packet.ciphertext start output first continuation
        (Sum.inr (((PqxdhLaterChallengeBuilderCoupling.tagged owner number first continuation callback).1, state.1), none), state.2))) =
    builderKey setup program (PqxdhLaterChallengeRandomSampler.finishSelected setup program packet parent nonce next
      (PqxdhLaterChallengeBackendGenerated.encodePrepared setup env callbacks owner number attachedVerify primitives baseImpl kem
        packet.secretKey packet.ciphertext start output second continuation
        (Sum.inr (((PqxdhLaterChallengeBuilderCoupling.tagged owner number second continuation callback).1, state.1), none), state.2))) := by
  simp only [builderKey, PqxdhLaterChallengeRandomSampler.finishSelected,
    PqxdhLaterChallengeRandomSampler.finish, PqxdhLaterChallengeBackendGenerated.encodePrepared,
    PqxdhLaterChallengeBuilderCoupling.tagged]
  simp only [PqxdhLaterSharedMessagePrefix.address, PqxdhErasedParentSample.address,
    PqxdhSharedParentInput.restore, PqxdhSharedParentCollect.restore,
    PqxdhLaterChallengeSavedMonitor.append_address]
  rcases callback with ⟨original, trace, origin⟩
  rcases original with (record | finish) | builder <;> rfl

/-- The full collector relation preserves the initial Builder observation without losing completed or post-admission mass. -/
theorem encoded_related (packet : Packet) (start : Input) (output : HmacBlock) (first second : Bool)
    (continuation : PqxdhInitialBuilderContext.BuildResult → OracleComp
      (PqxdhFirstRecordConfidentiality.AdvSpec (SelectorSpec baseSpec) S (B + 1)) Bool)
    (parent : FullOutput) (nonce : NonceOutput) (next : RootOutput)
    (left right : (Bool ⊕ (Pending × Option CaptureDetails)) × RandomState)
    (related : PqxdhLaterChallengeBackendCollector.Related owner number first second continuation left right) :
    builderKey setup program (PqxdhLaterChallengeRandomSampler.finishSelected setup program packet parent nonce next
      (PqxdhLaterChallengeBackendGenerated.encodePrepared setup env callbacks owner number attachedVerify primitives baseImpl kem
        packet.secretKey packet.ciphertext start output first continuation left)) =
    builderKey setup program (PqxdhLaterChallengeRandomSampler.finishSelected setup program packet parent nonce next
      (PqxdhLaterChallengeBackendGenerated.encodePrepared setup env callbacks owner number attachedVerify primitives baseImpl kem
        packet.secretKey packet.ciphertext start output second continuation right)) := by
  rcases related with ⟨leftCut, rightCut, leftView, rightView, cuts⟩ | ⟨leftResidual, rightResidual⟩
  · rcases cuts with ⟨callback, state, rfl, rfl⟩ | ⟨leftCut, rightCut, rfl, rfl, wrapper⟩
    · have leftEq := PqxdhLaterChallengeBackendCollectorBefore.pending_view left _ _ state leftView
      have rightEq := PqxdhLaterChallengeBackendCollectorBefore.pending_view right _ _ state rightView
      rw [leftEq, rightEq]
      exact encoded_pending setup env callbacks program owner number attachedVerify primitives baseImpl kem
        packet start output first second continuation parent nonce next callback state
    · have leftKey : (PqxdhLaterChallengeBackendCollector.pendingView left).bind
          PqxdhLaterChallengeBuilderObservation.builderKey = none := by
        rw [leftView]
        cases leftCut <;> rfl
      have rightKey : (PqxdhLaterChallengeBackendCollector.pendingView right).bind
          PqxdhLaterChallengeBuilderObservation.builderKey = none := by
        rw [rightView]
        cases rightCut <;> rfl
      exact (encoded_none setup env callbacks program owner number attachedVerify primitives baseImpl kem
        packet start output first continuation parent nonce next left leftKey).trans
        (encoded_none setup env callbacks program owner number attachedVerify primitives baseImpl kem
          packet start output second continuation parent nonce next right rightKey).symm
  · exact (encoded_residual setup env callbacks program owner number attachedVerify primitives baseImpl kem
      packet start output first continuation parent nonce next left leftResidual).trans
      (encoded_residual setup env callbacks program owner number attachedVerify primitives baseImpl kem
        packet start output second continuation parent nonce next right rightResidual).symm

/-- The full actual generated-carrier relation implies equality of its complete Builder observation, including all private source context/material and the complementary None outcome. -/
theorem related_key (first second : Bool)
    (left right : (Carrier × Option program.Selection) × RandomState)
    (related : PqxdhLaterChallengeRandomSampler.CarriedRelated setup env callbacks program adversary owner number
      attachedVerify primitives baseImpl kem ancestors disclosed first second left right) :
    builderKey setup program left = builderKey setup program right := by
  rcases related with ⟨beforeLeft, beforeRight, output, parent, nonce, next, leftAfter, rightAfter, packets, collected, rfl, rfl⟩
  rcases collected with ⟨leftDecision, rightDecision, _, _, rfl, rfl⟩ |
      ⟨prefixOutput, ephemeral, start, rfl, _, _, prepared⟩
  · rfl
  · rcases prepared with ⟨leftResult, rightResult, rfl, rfl, collector⟩
    exact encoded_related setup env callbacks program owner number attachedVerify primitives baseImpl kem
      beforeLeft.1 start output first second (adversary prefixOutput.context.selection.1) parent nonce next leftResult rightResult collector

/-- Joint early observation. Builder and before callbacks remain distinct; all complementary mass is retained in their absent coordinates. -/
noncomputable def earlyKey (result : (Carrier × Option program.Selection) × RandomState) :=
  (builderKey setup program result, PqxdhLaterChallengeRandomBefore.beforeKey setup program result)

/-- One coupling preserves both early observations simultaneously in the full generated random distribution; this is stronger than equality of their separate marginal laws. -/
theorem carried (depth : Nat) (first second : Bool) (state : RandomState) :
    RelTriple
      (earlyKey setup program <$> (simulateQ backend (PqxdhLaterChallengeGeneratedContinuation.run setup env callbacks program adversary owner number first attachedVerify primitives baseImpl kem ancestors disclosed depth)).run state)
      (earlyKey setup program <$> (simulateQ backend (PqxdhLaterChallengeGeneratedContinuation.run setup env callbacks program adversary owner number second attachedVerify primitives baseImpl kem ancestors disclosed depth)).run state)
      Eq := by
  apply relTriple_map
  apply relTriple_post_mono (PqxdhLaterChallengeRandomSampler.carried setup env callbacks program adversary owner number
    attachedVerify primitives baseImpl kem ancestors disclosed depth first second state)
  intro left right related
  exact Prod.ext (related_key setup env callbacks program adversary owner number attachedVerify primitives baseImpl kem
    ancestors disclosed first second left right related)
    (PqxdhLaterChallengeRandomBefore.related_key setup env callbacks program adversary owner number attachedVerify primitives baseImpl kem
      ancestors disclosed first second left right related)

/-- The Builder payload is a source-level observation; the public dictionary is only a metadata coordinate, not an installed component state. -/
noncomputable def sourceKey (result : (Carrier × Option program.Selection) × CtxRO.QueryCache) :=
  match result with
  | ((((credentials, (((Sum.inr (stored, Sum.inr pending), parent), target), nonce, next)), none), selection), cache) =>
      match pending.1.original with
      | .inr saved => some (credentials, inputKey setup stored.1, stored.2,
          PqxdhLaterChallengeSavedMonitor.builderOnly saved pending.1.trace pending.1.origin,
          PqxdhNativeSharedPrefix.attach pending.2 cache, parent, target, nonce, next, selection)
      | _ => none
  | _ => none

/-- The operational source payload and the separately retained complete random state are exactly the joint Builder observation. No component state is reconstructed from the dictionary. -/
theorem retained (result : (Carrier × Option program.Selection) × RandomState) :
    builderKey setup program result =
      (sourceKey setup program (result.1, PqxdhLaterChallengeRandomProjection.cache result.2)).map
        (fun payload => (payload, result.2)) := by
  rcases result with ⟨result, state⟩
  rcases result with ⟨⟨⟨credentials, ⟨⟨⟨packet, parent⟩, target⟩, nonce, next⟩⟩, captured⟩, selection⟩
  rcases packet with decision | ⟨stored, decision | ⟨⟨original, trace, origin⟩, localState⟩⟩
  · rfl
  · rfl
  · cases captured with
    | some details => rfl
    | none => cases original <;> rfl

/-- Type of an operational Builder payload with no access to the random interpreter. -/
abbrev SourceKey := Option ((KemSK × MlKem768Ciphertext) × Input × HmacBlock ×
  PqxdhInitialOriginContext.Context (SelectorSpec baseSpec) M P (IdentityHandle I) (DhPair setup) (KemHandle K)
    PqxdhInitialBuilderContext.BuildResult Bool S (B + 1) ×
  PqxdhInitialNativeAudit.State A (BareState 1) RootOracle.QueryCache × Entry × RootOutput × NonceOutput × RootOutput × Option program.Selection)

end BeaconcryptCore.Computational.PqxdhLaterChallengeRandomEarly

/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeRandomEarly.encoded_none' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeRandomEarly.encoded_none

/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeRandomEarly.encoded_residual' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeRandomEarly.encoded_residual

/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeRandomEarly.encoded_pending' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeRandomEarly.encoded_pending

/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeRandomEarly.encoded_related' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeRandomEarly.encoded_related

/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeRandomEarly.related_key' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeRandomEarly.related_key

/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeRandomEarly.carried' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeRandomEarly.carried

/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeRandomEarly.retained' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeRandomEarly.retained
