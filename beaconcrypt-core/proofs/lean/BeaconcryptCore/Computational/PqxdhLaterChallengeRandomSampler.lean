-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhLaterChallengeBackendGenerated
import BeaconcryptCore.Computational.PqxdhLaterChallengeRandomBackend
import BeaconcryptCore.Computational.PqxdhLaterChallengeGeneratedSamplerCoupling

/-! Join the actual forwarded random interpreter, generated preparation, selected source input and every original material draw in the complete later challenge sampler. -/
open OracleComp OracleSpec CoreModels Aeneas OracleComp.ProgramLogic.Relational
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhLaterChallengeRandomSampler
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

open PqxdhLaterChallengeGeneratedSamplerCoupling (sourceInput pending_input after_pending)

/-- The relation records actual incoming packets and complete random states, their literal selected source input, and the complete resulting prepared-carrier relation. Common completed decisions are retained exactly. -/
noncomputable def AfterRelated (output : HmacBlock) (first second : Bool)
    (beforeLeft beforeRight : Packet × RandomState)
    (left right : (LocalPacket × Option CaptureDetails) × RandomState) : Prop :=
  (∃ leftDecision rightDecision,
    beforeLeft.1.state = .completed leftDecision ∧ beforeRight.1.state = .completed rightDecision ∧
    left = ((Sum.inl leftDecision, none), beforeLeft.2) ∧ right = ((Sum.inl rightDecision, none), beforeRight.2)) ∨
  ∃ prefixOutput ephemeral start,
    beforeLeft = beforeRight ∧ beforeLeft.1.state = .pending prefixOutput ephemeral ∧
    sourceInput setup env callbacks program owner number attachedVerify primitives baseImpl kem ancestors disclosed
      (PqxdhRecordConfidentialityChallenge.post adversary owner number false) beforeLeft.1 = Sum.inr start ∧
    PqxdhLaterChallengeBackendGenerated.PreparedRelated setup env callbacks owner number attachedVerify primitives baseImpl kem
      beforeLeft.1.secretKey beforeLeft.1.ciphertext start output first second (adversary prefixOutput.context.selection.1) left right

/-- Couple the actual post-preparation sampler at its actual generated packets, preserving selected adversary provenance and every common/cached outcome. -/
theorem after (output : HmacBlock) (depth : Nat) (first second : Bool)
    (beforeLeft beforeRight : Packet × RandomState)
    (related : PqxdhLaterChallengeBackendPreparation.PacketRelated setup program beforeLeft beforeRight) :
    RelTriple
      ((simulateQ backend (PqxdhLaterChallengeSampler.after setup env callbacks program adversary owner number first attachedVerify primitives baseImpl kem ancestors disclosed
        beforeLeft.1 output depth)).run beforeLeft.2)
      ((simulateQ backend (PqxdhLaterChallengeSampler.after setup env callbacks program adversary owner number second attachedVerify primitives baseImpl kem ancestors disclosed
        beforeRight.1 output depth)).run beforeRight.2)
      (AfterRelated setup env callbacks program adversary owner number attachedVerify primitives baseImpl kem ancestors disclosed output first second beforeLeft beforeRight) := by
  rcases related with rfl | ⟨leftCompleted, rightCompleted⟩
  · rcases beforeLeft with ⟨⟨publicKey, secret, state, ciphertext⟩, cache⟩
    cases state with
    | completed decision =>
      exact relTriple_pure_pure (Or.inl ⟨decision, decision, rfl, rfl, rfl, rfl⟩)
    | pending prefixOutput ephemeral =>
      obtain ⟨start, same⟩ : ∃ start, sourceInput setup env callbacks program owner number attachedVerify primitives baseImpl kem ancestors disclosed
        (PqxdhRecordConfidentialityChallenge.post adversary owner number false)
        ⟨publicKey, secret, .pending prefixOutput ephemeral, ciphertext⟩ = Sum.inr start := ⟨_, rfl⟩
      rw [after_pending setup env callbacks program adversary owner number attachedVerify primitives baseImpl kem ancestors disclosed publicKey secret prefixOutput ephemeral ciphertext start same output depth first,
        after_pending setup env callbacks program adversary owner number attachedVerify primitives baseImpl kem ancestors disclosed publicKey secret prefixOutput ephemeral ciphertext start same output depth second]
      exact relTriple_post_mono
        (PqxdhLaterChallengeBackendGenerated.prepared setup env callbacks owner number attachedVerify primitives baseImpl kem backend
          secret ciphertext start output depth first second (adversary prefixOutput.context.selection.1) cache)
        (fun _ _ paired => Or.inr ⟨prefixOutput, ephemeral, start, rfl, rfl, same, paired⟩)
  · rcases beforeLeft with ⟨⟨leftPublic, leftSecret, leftState, leftCiphertext⟩, leftCache⟩
    rcases beforeRight with ⟨⟨rightPublic, rightSecret, rightState, rightCiphertext⟩, rightCache⟩
    cases leftState with
    | pending _ _ => exact False.elim leftCompleted
    | completed leftDecision =>
      cases rightState with
      | pending _ _ => exact False.elim rightCompleted
      | completed rightDecision =>
        exact relTriple_pure_pure (Or.inl ⟨leftDecision, rightDecision, rfl, rfl, rfl, rfl⟩)

local notation "Carrier" => PqxdhLaterChallengeSampler.Carrier (setup := setup) (M := M) (P := P) (I := I) (K := K)
  (X := X) (Response := Response) (A := A) (KemSK := KemSK) (S := S) (B := B)

/-- Assemble the original final carrier from its actual private packet, reached collector state and full random backend and source-ordered parent/nonce/next-chain material. -/
noncomputable def finish (packet : Packet) (parent : FullOutput) (nonce : NonceOutput) (chain : RootOutput)
    (result : (LocalPacket × Option CaptureDetails) × RandomState) : Carrier × RandomState :=
  ((((packet.secretKey, packet.ciphertext),
    (((result.1.1, fromOutput (PqxdhLaterSharedMessagePrefix.address setup result.1.1) parent), nextChain parent), nonce, chain)), result.1.2), result.2)

/-- Retain the actual two preparation outcomes and collector results, together with all common original material draws, inside the final complete carrier relation. -/
noncomputable def Related (first second : Bool) (left right : Carrier × RandomState) : Prop :=
  ∃ beforeLeft beforeRight output parent nonce chain leftAfter rightAfter,
    PqxdhLaterChallengeBackendPreparation.PacketRelated setup program beforeLeft beforeRight ∧
    AfterRelated setup env callbacks program adversary owner number attachedVerify primitives baseImpl kem ancestors disclosed
      output first second beforeLeft beforeRight leftAfter rightAfter ∧
    left = finish setup program beforeLeft.1 parent nonce chain leftAfter ∧
    right = finish setup program beforeRight.1 parent nonce chain rightAfter

/-- The two full original later-challenge samplers are coupled from actual KEM generation through source selection, the literal collector and every original material draw. Complete common/cached/refusal outcomes retain both full marginals, including all public-hash observation histories. -/
theorem run (depth : Nat) (first second : Bool) (cache : RandomState) :
    RelTriple
      ((simulateQ backend (PqxdhLaterChallengeSampler.run setup env callbacks program adversary owner number first attachedVerify primitives baseImpl kem ancestors disclosed depth)).run cache)
      ((simulateQ backend (PqxdhLaterChallengeSampler.run setup env callbacks program adversary owner number second attachedVerify primitives baseImpl kem ancestors disclosed depth)).run cache)
      (Related setup env callbacks program adversary owner number attachedVerify primitives baseImpl kem ancestors disclosed first second) := by
  simp only [PqxdhLaterChallengeSampler.run, simulateQ_bind, StateT.run_bind, simulateQ_pure, StateT.run_pure]
  refine relTriple_bind
    (PqxdhLaterChallengeBackendPreparation.prepare setup env callbacks program attachedVerify primitives baseImpl kem backend
      (PqxdhRecordConfidentialityChallenge.post adversary owner number first)
      (PqxdhRecordConfidentialityChallenge.post adversary owner number second) cache) ?_
  intro beforeLeft beforeRight packets
  simp only [PqxdhLaterChallengeRandomBackend.coins, bind_map_left]
  refine relTriple_bind (relTriple_refl _) ?_
  rintro output _ rfl
  refine relTriple_bind
    (after setup env callbacks program adversary owner number attachedVerify primitives baseImpl kem ancestors disclosed
      output depth first second beforeLeft beforeRight packets) ?_
  intro leftAfter rightAfter collected
  refine relTriple_bind (relTriple_refl _) ?_
  rintro parent _ rfl
  refine relTriple_bind (relTriple_refl _) ?_
  rintro nonce _ rfl
  refine relTriple_bind (relTriple_refl _) ?_
  rintro chain _ rfl
  exact relTriple_pure_pure ⟨beforeLeft, beforeRight, output, parent, nonce, chain, leftAfter, rightAfter,
    packets, collected, rfl, rfl⟩

/-- Keep the actual generated selection next to the same complete source carrier. -/
noncomputable def finishSelected (packet : Packet) (parent : FullOutput) (nonce : NonceOutput) (chain : RootOutput)
    (result : (LocalPacket × Option CaptureDetails) × RandomState) :
    (Carrier × Option program.Selection) × RandomState :=
  let selection := match packet.state with
    | .completed _ => none
    | .pending before _ => some before.context.selection.1
  (((finish setup program packet parent nonce chain result).1, selection), result.2)

/-- The complete carried relation additionally retains the literal source-chosen selection used by existing chronology and source-event exclusion results. -/
noncomputable def CarriedRelated (first second : Bool)
    (left right : (Carrier × Option program.Selection) × RandomState) : Prop :=
  ∃ beforeLeft beforeRight output parent nonce chain leftAfter rightAfter,
    PqxdhLaterChallengeBackendPreparation.PacketRelated setup program beforeLeft beforeRight ∧
    AfterRelated setup env callbacks program adversary owner number attachedVerify primitives baseImpl kem ancestors disclosed
      output first second beforeLeft beforeRight leftAfter rightAfter ∧
    left = finishSelected setup program beforeLeft.1 parent nonce chain leftAfter ∧
    right = finishSelected setup program beforeRight.1 parent nonce chain rightAfter

/-- The actual selection-retaining sampler has the same full coupling, with complete common outcomes, source-selected continuation and all original material draws kept. This is the carrier used by the same-source event lemmas. -/
theorem carried (depth : Nat) (first second : Bool) (cache : RandomState) :
    RelTriple
      ((simulateQ backend (PqxdhLaterChallengeGeneratedContinuation.run setup env callbacks program adversary owner number first attachedVerify primitives baseImpl kem ancestors disclosed depth)).run cache)
      ((simulateQ backend (PqxdhLaterChallengeGeneratedContinuation.run setup env callbacks program adversary owner number second attachedVerify primitives baseImpl kem ancestors disclosed depth)).run cache)
      (CarriedRelated setup env callbacks program adversary owner number attachedVerify primitives baseImpl kem ancestors disclosed first second) := by
  simp only [PqxdhLaterChallengeGeneratedContinuation.run, simulateQ_bind, StateT.run_bind, simulateQ_pure, StateT.run_pure]
  refine relTriple_bind
    (PqxdhLaterChallengeBackendPreparation.prepare setup env callbacks program attachedVerify primitives baseImpl kem backend
      (PqxdhRecordConfidentialityChallenge.post adversary owner number first)
      (PqxdhRecordConfidentialityChallenge.post adversary owner number second) cache) ?_
  intro beforeLeft beforeRight packets
  simp only [PqxdhLaterChallengeRandomBackend.coins, bind_map_left]
  refine relTriple_bind (relTriple_refl _) ?_
  rintro output _ rfl
  refine relTriple_bind
    (after setup env callbacks program adversary owner number attachedVerify primitives baseImpl kem ancestors disclosed
      output depth first second beforeLeft beforeRight packets) ?_
  intro leftAfter rightAfter collected
  refine relTriple_bind (relTriple_refl _) ?_
  rintro parent _ rfl
  refine relTriple_bind (relTriple_refl _) ?_
  rintro nonce _ rfl
  refine relTriple_bind (relTriple_refl _) ?_
  rintro chain _ rfl
  exact relTriple_pure_pure ⟨beforeLeft, beforeRight, output, parent, nonce, chain, leftAfter, rightAfter,
    packets, collected, rfl, rfl⟩

end BeaconcryptCore.Computational.PqxdhLaterChallengeRandomSampler

/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeRandomSampler.after' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeRandomSampler.after

/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeRandomSampler.run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeRandomSampler.run

/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeRandomSampler.carried' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeRandomSampler.carried
