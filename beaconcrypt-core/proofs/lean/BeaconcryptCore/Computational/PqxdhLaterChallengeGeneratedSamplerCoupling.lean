import BeaconcryptCore.Computational.PqxdhLaterChallengeGeneratedCoupling

/-! Join actual generated preparation, selected source input and every original material draw in the complete later challenge sampler. -/
open OracleComp OracleSpec CoreModels Aeneas OracleComp.ProgramLogic.Relational
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhLaterChallengeGeneratedSamplerCoupling
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

/-- The concrete input extracted from this actual generated packet and its chosen outside continuation. -/
noncomputable def sourceInput (post : Post) (packet : Packet) :=
  PqxdhSourceSharedInput.input setup env callbacks program post attachedVerify primitives baseImpl kem owner number ancestors disclosed packet

/-- Changing the outside continuation of an actual pending packet changes only its Post field, with the same literal selected application continuation. -/
theorem pending_input (first second : Post) (publicKey : TargetKemPublicKey) (secret : KemSK)
    (prefixOutput : Output) (ephemeral : List.Vector UInt8 32) (ciphertext : MlKem768Ciphertext) (start : Input)
    (same : sourceInput setup env callbacks program owner number attachedVerify primitives baseImpl kem ancestors disclosed first
      ⟨publicKey, secret, .pending prefixOutput ephemeral, ciphertext⟩ = Sum.inr start) :
    sourceInput setup env callbacks program owner number attachedVerify primitives baseImpl kem ancestors disclosed second
      ⟨publicKey, secret, .pending prefixOutput ephemeral, ciphertext⟩ =
      Sum.inr {start with post := second prefixOutput.context.selection.1} := by
  simp only [sourceInput, PqxdhSourceSharedInput.input, PqxdhInitialPreparedSourceInput.input,
    PqxdhSourceSharedPreparation.restore, PqxdhCommonSharedDispatch.restoreMode, Sum.inr.injEq] at same
  subst start
  rfl

/-- The actual pending source packet executes the prepared carrier with its own selected adversary and the shared source input; only the explicit world wrapper differs. -/
theorem after_pending (publicKey : TargetKemPublicKey) (secret : KemSK)
    (prefixOutput : Output) (ephemeral : List.Vector UInt8 32) (ciphertext : MlKem768Ciphertext) (start : Input)
    (same : sourceInput setup env callbacks program owner number attachedVerify primitives baseImpl kem ancestors disclosed
      (PqxdhRecordConfidentialityChallenge.post adversary owner number false)
      ⟨publicKey, secret, .pending prefixOutput ephemeral, ciphertext⟩ = Sum.inr start)
    (output : HmacBlock) (depth : Nat) (bit : Bool) :
    PqxdhLaterChallengeSampler.after setup env callbacks program adversary owner number bit attachedVerify primitives baseImpl kem ancestors disclosed
      ⟨publicKey, secret, .pending prefixOutput ephemeral, ciphertext⟩ output depth =
    PqxdhLaterChallengeSampler.prepared setup env callbacks owner number bit attachedVerify primitives baseImpl kem
      secret ciphertext start output depth (adversary prefixOutput.context.selection.1) := by
  have actual := pending_input setup env callbacks program owner number attachedVerify primitives baseImpl kem ancestors disclosed
    (PqxdhRecordConfidentialityChallenge.post adversary owner number false)
    (PqxdhRecordConfidentialityChallenge.post adversary owner number bit) publicKey secret prefixOutput ephemeral ciphertext start same
  change (match sourceInput setup env callbacks program owner number attachedVerify primitives baseImpl kem ancestors disclosed
      (PqxdhRecordConfidentialityChallenge.post adversary owner number bit)
      ⟨publicKey, secret, .pending prefixOutput ephemeral, ciphertext⟩ with
    | .inl decision => pure (Sum.inl decision, none)
    | .inr input => PqxdhLaterChallengeSampler.prepared setup env callbacks owner number bit attachedVerify primitives baseImpl kem
        secret ciphertext input output depth (adversary prefixOutput.context.selection.1)) = _
  rw [actual]
  exact PqxdhLaterChallengeGeneratedCoupling.prepared_post setup env callbacks owner number attachedVerify primitives baseImpl kem
    secret ciphertext start output depth bit (adversary prefixOutput.context.selection.1) _

/-- The relation records actual incoming packets and caches, their literal selected source input, and the complete resulting prepared-carrier relation. Common completed decisions are retained exactly. -/
noncomputable def AfterRelated (output : HmacBlock) (first second : Bool)
    (beforeLeft beforeRight : Packet × CtxRO.QueryCache)
    (left right : (LocalPacket × Option CaptureDetails) × CtxRO.QueryCache) : Prop :=
  (∃ leftDecision rightDecision,
    beforeLeft.1.state = .completed leftDecision ∧ beforeRight.1.state = .completed rightDecision ∧
    left = ((Sum.inl leftDecision, none), beforeLeft.2) ∧ right = ((Sum.inl rightDecision, none), beforeRight.2)) ∨
  ∃ prefixOutput ephemeral start,
    beforeLeft = beforeRight ∧ beforeLeft.1.state = .pending prefixOutput ephemeral ∧
    sourceInput setup env callbacks program owner number attachedVerify primitives baseImpl kem ancestors disclosed
      (PqxdhRecordConfidentialityChallenge.post adversary owner number false) beforeLeft.1 = Sum.inr start ∧
    PqxdhLaterChallengeGeneratedCoupling.PreparedRelated setup env callbacks owner number attachedVerify primitives baseImpl kem
      beforeLeft.1.secretKey beforeLeft.1.ciphertext start output first second (adversary prefixOutput.context.selection.1) left right

/-- Couple the actual post-preparation sampler at its actual generated packets, preserving selected adversary provenance and every common/cached outcome. -/
theorem after (output : HmacBlock) (depth : Nat) (first second : Bool)
    (beforeLeft beforeRight : Packet × CtxRO.QueryCache)
    (related : PqxdhLaterChallengePreparationCoupling.PacketRelated setup program beforeLeft beforeRight) :
    RelTriple
      ((simulateQ hashImpl (PqxdhLaterChallengeSampler.after setup env callbacks program adversary owner number first attachedVerify primitives baseImpl kem ancestors disclosed
        beforeLeft.1 output depth)).run beforeLeft.2)
      ((simulateQ hashImpl (PqxdhLaterChallengeSampler.after setup env callbacks program adversary owner number second attachedVerify primitives baseImpl kem ancestors disclosed
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
        (PqxdhLaterChallengeGeneratedCoupling.prepared setup env callbacks owner number attachedVerify primitives baseImpl kem
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

/-- Assemble the original final carrier from its actual private packet, reached collector state and source-ordered parent/nonce/next-chain material. -/
noncomputable def finish (packet : Packet) (parent : FullOutput) (nonce : NonceOutput) (chain : RootOutput)
    (result : (LocalPacket × Option CaptureDetails) × CtxRO.QueryCache) : Carrier × CtxRO.QueryCache :=
  ((((packet.secretKey, packet.ciphertext),
    (((result.1.1, fromOutput (PqxdhLaterSharedMessagePrefix.address setup result.1.1) parent), nextChain parent), nonce, chain)), result.1.2), result.2)

/-- Retain the actual two preparation outcomes and collector results, together with all common original material draws, inside the final complete carrier relation. -/
noncomputable def Related (first second : Bool) (left right : Carrier × CtxRO.QueryCache) : Prop :=
  ∃ beforeLeft beforeRight output parent nonce chain leftAfter rightAfter,
    PqxdhLaterChallengePreparationCoupling.PacketRelated setup program beforeLeft beforeRight ∧
    AfterRelated setup env callbacks program adversary owner number attachedVerify primitives baseImpl kem ancestors disclosed
      output first second beforeLeft beforeRight leftAfter rightAfter ∧
    left = finish setup program beforeLeft.1 parent nonce chain leftAfter ∧
    right = finish setup program beforeRight.1 parent nonce chain rightAfter

/-- The two full original later-challenge samplers are coupled from actual KEM generation through source selection, the literal collector and every original material draw. Complete common/cached/refusal outcomes retain both full marginals. -/
theorem run (depth : Nat) (first second : Bool) (cache : CtxRO.QueryCache) :
    RelTriple
      ((simulateQ hashImpl (PqxdhLaterChallengeSampler.run setup env callbacks program adversary owner number first attachedVerify primitives baseImpl kem ancestors disclosed depth)).run cache)
      ((simulateQ hashImpl (PqxdhLaterChallengeSampler.run setup env callbacks program adversary owner number second attachedVerify primitives baseImpl kem ancestors disclosed depth)).run cache)
      (Related setup env callbacks program adversary owner number attachedVerify primitives baseImpl kem ancestors disclosed first second) := by
  simp only [PqxdhLaterChallengeSampler.run, simulateQ_bind, StateT.run_bind, simulateQ_pure, StateT.run_pure]
  refine relTriple_bind
    (PqxdhLaterChallengePreparationCoupling.prepare setup env callbacks program attachedVerify primitives baseImpl kem
      (PqxdhRecordConfidentialityChallenge.post adversary owner number first)
      (PqxdhRecordConfidentialityChallenge.post adversary owner number second) cache) ?_
  intro beforeLeft beforeRight packets
  simp only [RawCtxSelectiveSharedRom.coins_complete, bind_map_left]
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
    (result : (LocalPacket × Option CaptureDetails) × CtxRO.QueryCache) :
    (Carrier × Option program.Selection) × CtxRO.QueryCache :=
  let selection := match packet.state with
    | .completed _ => none
    | .pending before _ => some before.context.selection.1
  (((finish setup program packet parent nonce chain result).1, selection), result.2)

/-- The complete carried relation additionally retains the literal source-chosen selection used by existing chronology and source-event exclusion results. -/
noncomputable def CarriedRelated (first second : Bool)
    (left right : (Carrier × Option program.Selection) × CtxRO.QueryCache) : Prop :=
  ∃ beforeLeft beforeRight output parent nonce chain leftAfter rightAfter,
    PqxdhLaterChallengePreparationCoupling.PacketRelated setup program beforeLeft beforeRight ∧
    AfterRelated setup env callbacks program adversary owner number attachedVerify primitives baseImpl kem ancestors disclosed
      output first second beforeLeft beforeRight leftAfter rightAfter ∧
    left = finishSelected setup program beforeLeft.1 parent nonce chain leftAfter ∧
    right = finishSelected setup program beforeRight.1 parent nonce chain rightAfter

/-- The actual selection-retaining sampler has the same full coupling, with complete common outcomes, source-selected continuation and all original material draws kept. This is the carrier used by the same-source event lemmas. -/
theorem carried (depth : Nat) (first second : Bool) (cache : CtxRO.QueryCache) :
    RelTriple
      ((simulateQ hashImpl (PqxdhLaterChallengeGeneratedContinuation.run setup env callbacks program adversary owner number first attachedVerify primitives baseImpl kem ancestors disclosed depth)).run cache)
      ((simulateQ hashImpl (PqxdhLaterChallengeGeneratedContinuation.run setup env callbacks program adversary owner number second attachedVerify primitives baseImpl kem ancestors disclosed depth)).run cache)
      (CarriedRelated setup env callbacks program adversary owner number attachedVerify primitives baseImpl kem ancestors disclosed first second) := by
  simp only [PqxdhLaterChallengeGeneratedContinuation.run, simulateQ_bind, StateT.run_bind, simulateQ_pure, StateT.run_pure]
  refine relTriple_bind
    (PqxdhLaterChallengePreparationCoupling.prepare setup env callbacks program attachedVerify primitives baseImpl kem
      (PqxdhRecordConfidentialityChallenge.post adversary owner number first)
      (PqxdhRecordConfidentialityChallenge.post adversary owner number second) cache) ?_
  intro beforeLeft beforeRight packets
  simp only [RawCtxSelectiveSharedRom.coins_complete, bind_map_left]
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

end BeaconcryptCore.Computational.PqxdhLaterChallengeGeneratedSamplerCoupling

/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeGeneratedSamplerCoupling.pending_input' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeGeneratedSamplerCoupling.pending_input

/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeGeneratedSamplerCoupling.after_pending' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeGeneratedSamplerCoupling.after_pending

/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeGeneratedSamplerCoupling.after' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeGeneratedSamplerCoupling.after

/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeGeneratedSamplerCoupling.run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeGeneratedSamplerCoupling.run

/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeGeneratedSamplerCoupling.carried' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeGeneratedSamplerCoupling.carried
