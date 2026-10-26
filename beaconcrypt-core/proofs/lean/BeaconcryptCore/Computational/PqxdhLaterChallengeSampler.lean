import BeaconcryptCore.Computational.PqxdhLaterChallengePreparedCapture
import BeaconcryptCore.Computational.PqxdhLaterSavedSampler

/-! Retain the actual generated selection and wrapper callback while executing the complete original later-record sampler. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhLaterChallengeSampler
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
    (owner : RawCtxProtocolReveals.Owner S (B + 1)) (number : U64) (bit : Bool)
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (ancestors disclosed : List RatchetChain)
local notation "post" => PqxdhRecordConfidentialityChallenge.post adversary owner number bit
local notation "env0" => PqxdhSourceSharedPreparation.environment setup env callbacks ∅
local notation "Packet" => PqxdhSourceSharedPreparation.Packet
  (PqxdhSourceSharedPreparation.LocalOutput (M := M) (P := P) (I := I) (K := K) (A := A) setup program) KemSK
local notation "LocalPacket" => PqxdhSharedParentInput.LocalPacket (setup := setup) (M := M) (P := P) (I := I) (K := K)
    (X := X) (Response := Response) (A := A) (S := S) (B := B)
local notation "input" => PqxdhSourceSharedInput.input setup env callbacks program post attachedVerify primitives baseImpl kem owner number ancestors disclosed
abbrev Details := PqxdhLaterChallengeCapture.Details (SelectorSpec baseSpec) M P (IdentityHandle I) (DhPair setup) (KemHandle K) Bool S (B + 1)

local notation "Input" => PqxdhInitialPreparedSourceInput.Input (M := M) (P := P) (I := I) (K := K) (X := X)
    (Response := Response) (A := A) (S := S) (B := B) (setup := setup)

/-- Preserve the prepared input and the exact local capture beside the existing normalization of completed and pending results. -/
noncomputable def prepared (secret : KemSK) (challenge : MlKem768Ciphertext)
    (start : Input) (output : HmacBlock) (depth : Nat)
    (continuation : PqxdhInitialBuilderContext.BuildResult → OracleComp
      (PqxdhFirstRecordConfidentiality.AdvSpec (SelectorSpec baseSpec) S (B + 1)) Bool) :
    OracleComp HashSpec (LocalPacket × Option (Details (setup := setup) (M := M) (P := P) (I := I) (K := K) (S := S) (B := B))) := do
  let result ← PqxdhLaterChallengePreparedCapture.run env0 callbacks baseImpl kem attachedVerify primitives
    secret challenge start output depth owner number bit continuation
  let originalStart := PqxdhErasedParentSample.forgetStart
    (PqxdhPreparedSharedPrefix.input env0 callbacks baseImpl kem attachedVerify primitives secret challenge
      (PqxdhLaterChallengePreparedCapture.withPost (setup := setup) start owner number bit continuation), output)
  pure (match result with
    | .inl decision => (.inr (originalStart, .inl decision), none)
    | .inr (pending, details) => (.inr (originalStart, .inr pending), details))

/-- The complete prepared packet projects to the unchanged source packet before interpreting the shared ROM. -/
theorem prepared_erase (secret : KemSK) (challenge : MlKem768Ciphertext)
    (start : Input) (output : HmacBlock) (depth : Nat)
    (continuation : PqxdhInitialBuilderContext.BuildResult → OracleComp
      (PqxdhFirstRecordConfidentiality.AdvSpec (SelectorSpec baseSpec) S (B + 1)) Bool) :
    Prod.fst <$> prepared setup env callbacks owner number bit attachedVerify primitives baseImpl kem secret challenge start output depth continuation =
      PqxdhSharedParentInput.run env0 callbacks baseImpl kem attachedVerify primitives secret challenge
        (PqxdhLaterChallengePreparedCapture.withPost (setup := setup) start owner number bit continuation) output depth := by
  unfold prepared PqxdhSharedParentInput.run
  rw [← PqxdhLaterChallengePreparedCapture.run_erase]
  simp only [map_bind, map_pure, bind_map_left]
  apply bind_congr
  intro result
  cases result <;> rfl

/-- The generated source packet supplies its literal selected adversary continuation. The original common branch and complete prepared collector remain unchanged. -/
noncomputable def after (packet : Packet) (output : HmacBlock) (depth : Nat) :
    OracleComp HashSpec (LocalPacket × Option (Details (setup := setup) (M := M) (P := P) (I := I) (K := K) (S := S) (B := B))) :=
  match packet.state with
  | .completed _ => (fun result => (result, none)) <$>
      PqxdhLaterSharedParent.after setup env callbacks program post attachedVerify primitives baseImpl kem owner number ancestors disclosed packet output depth
  | .pending prefixOutput _ =>
    match input packet with
    | .inl decision => pure (.inl decision, none)
    | .inr start => prepared setup env callbacks owner number bit attachedVerify primitives baseImpl kem
        packet.secretKey packet.ciphertext start output depth (adversary prefixOutput.context.selection.1)

/-- Erasing the generated request metadata restores the actual original source parent sampler, with its source-chosen selection and all common/cache decisions. -/
theorem after_erase (packet : Packet) (output : HmacBlock) (depth : Nat) :
    Prod.fst <$> after setup env callbacks program adversary owner number bit attachedVerify primitives baseImpl kem ancestors disclosed packet output depth =
      PqxdhLaterSharedParent.after setup env callbacks program post attachedVerify primitives baseImpl kem owner number ancestors disclosed packet output depth := by
  rcases packet with ⟨publicKey, secretKey, state, ciphertext⟩
  cases state with
  | completed decision =>
      simp only [after, Functor.map_map]
      exact congrFun Functor.map_id _
  | pending prefixOutput ephemeral =>
      simp only [after, PqxdhLaterSharedParent.after, PqxdhSourceSharedInput.input, PqxdhInitialPreparedSourceInput.input, PqxdhSourceSharedPreparation.restore, PqxdhCommonSharedDispatch.restoreMode]
      exact prepared_erase setup env callbacks owner number bit attachedVerify primitives baseImpl kem secretKey ciphertext _ output depth (adversary prefixOutput.context.selection.1)

abbrev Carrier := PqxdhLaterSavedSampler.Carrier (setup := setup) (M := M) (P := P) (I := I) (K := K)
    (X := X) (Response := Response) (A := A) (KemSK := KemSK) (S := S) (B := B) ×
  Option (Details (setup := setup) (M := M) (P := P) (I := I) (K := K) (S := S) (B := B))

/-- Execute the same preparation and every original material draw, retaining only the callback metadata generated by that run. -/
noncomputable def run (depth : Nat) : OracleComp HashSpec (Carrier (setup := setup) (M := M) (P := P) (I := I) (K := K)
    (X := X) (Response := Response) (A := A) (KemSK := KemSK) (S := S) (B := B)) := do
  let packet ← PqxdhSourceSharedPreparation.prepare setup env callbacks program post attachedVerify primitives baseImpl kem
  let output ← simulateQ RawCtxSelectiveSharedRom.coins ($ᵗ HmacBlock)
  let localPacket ← after setup env callbacks program adversary owner number bit attachedVerify primitives baseImpl kem ancestors disclosed packet output depth
  let parent ← simulateQ RawCtxSelectiveSharedRom.coins ($ᵗ FullOutput)
  let nonce ← simulateQ RawCtxSelectiveSharedRom.coins ($ᵗ NonceOutput)
  let chain ← simulateQ RawCtxSelectiveSharedRom.coins ($ᵗ RootOutput)
  pure (((packet.secretKey, packet.ciphertext),
    (((localPacket.1, fromOutput (PqxdhLaterSharedMessagePrefix.address setup localPacket.1) parent), nextChain parent), nonce, chain)), localPacket.2)

/-- Metadata erasure restores the complete earlier private callback carrier and all original source draws, including common and cached branches. -/
theorem run_erase (depth : Nat) :
    Prod.fst <$> run setup env callbacks program adversary owner number bit attachedVerify primitives baseImpl kem ancestors disclosed depth =
      PqxdhLaterSavedSampler.run setup env callbacks program post attachedVerify primitives baseImpl kem owner number ancestors disclosed depth := by
  simp only [run, PqxdhLaterSavedSampler.run, map_bind, map_pure]
  apply bind_congr
  intro packet
  apply bind_congr
  intro output
  rw [← after_erase]
  simp only [bind_map_left]

/-- The complete captured sampler evaluates to exactly the original full material sampler and its reached shared cache. -/
theorem source (depth : Nat) :
    (fun result => PqxdhLaterSharedMessagePrefix.restore setup result.1.1.2 result.2) <$>
      (simulateQ hashImpl (run setup env callbacks program adversary owner number bit attachedVerify primitives baseImpl kem ancestors disclosed depth)).run ∅ =
      PqxdhErasedParentMaterial.prepare env.source env.recordWriter env.senderId env.route env.decode depth
        (PqxdhInitialPreparedSourceInput.prior env0 baseImpl kem attachedVerify primitives program post owner number ancestors disclosed) := by
  rw [← PqxdhLaterSavedSampler.source setup env callbacks program post attachedVerify primitives baseImpl kem owner number ancestors disclosed depth,
    ← run_erase setup env callbacks program adversary owner number bit attachedVerify primitives baseImpl kem ancestors disclosed depth]
  simp only [simulateQ_map, StateT.run_map, Functor.map_map]

/-- All complete source-interface budgets are unchanged; retaining the request metadata adds no query or sampler draw. -/
theorem run_budget {Budget : Type} (depth : Nat) (budget : Budget)
    (canQuery : HashSpec.Domain → Budget → Prop) (cost : HashSpec.Domain → Budget → Budget) :
    (run setup env callbacks program adversary owner number bit attachedVerify primitives baseImpl kem ancestors disclosed depth).IsQueryBound budget canQuery cost ↔
      (PqxdhLaterSavedSampler.run setup env callbacks program post attachedVerify primitives baseImpl kem owner number ancestors disclosed depth).IsQueryBound budget canQuery cost := by
  rw [← run_erase setup env callbacks program adversary owner number bit attachedVerify primitives baseImpl kem ancestors disclosed depth,
    isQueryBound_map_iff]

/-- Only an actual pending descriptor is required to carry callback composition; original outer and inner common decisions remain unrestricted. -/
noncomputable def JoinedPacket
    (packet : LocalPacket × Option (Details (setup := setup) (M := M) (P := P) (I := I) (K := K) (S := S) (B := B))) : Prop :=
  match packet.1 with
  | .inl _ => True
  | .inr (_, .inl _) => True
  | .inr (_, .inr pending) => PqxdhLaterChallengeBuilderCapture.JoinedCapture owner number bit (pending.1, packet.2)

/-- The complete prepared packet carries the exact descriptor/remainder certificate of its own source callback. -/
theorem prepared_joined (secret : KemSK) (challenge : MlKem768Ciphertext)
    (start : Input) (output : HmacBlock) (depth : Nat)
    (continuation : PqxdhInitialBuilderContext.BuildResult → OracleComp
      (PqxdhFirstRecordConfidentiality.AdvSpec (SelectorSpec baseSpec) S (B + 1)) Bool)
    (result : LocalPacket × Option (Details (setup := setup) (M := M) (P := P) (I := I) (K := K) (S := S) (B := B)))
    (supported : result ∈ support (prepared setup env callbacks owner number bit attachedVerify primitives baseImpl kem secret challenge start output depth continuation)) :
    JoinedPacket setup owner number bit result := by
  simp only [prepared, mem_support_bind_iff, mem_support_pure_iff] at supported
  obtain ⟨value, reached, rfl⟩ := supported
  cases value with
  | inl decision => trivial
  | inr pending =>
      exact PqxdhLaterChallengePreparedCapture.run_joined env0 callbacks baseImpl kem attachedVerify primitives secret challenge start output depth owner number bit continuation pending.1 pending.2 reached

/-- The actual generated selection supplies the same callback certificate; neither completed preparation nor cached completion imposes a new condition on its Boolean. -/
theorem after_joined (packet : Packet) (output : HmacBlock) (depth : Nat)
    (result : LocalPacket × Option (Details (setup := setup) (M := M) (P := P) (I := I) (K := K) (S := S) (B := B)))
    (supported : result ∈ support (after setup env callbacks program adversary owner number bit attachedVerify primitives baseImpl kem ancestors disclosed packet output depth)) :
    JoinedPacket setup owner number bit result := by
  rcases packet with ⟨publicKey, secretKey, state, ciphertext⟩
  cases state with
  | completed decision =>
      simp only [after, PqxdhLaterSharedParent.after, PqxdhSourceSharedInput.input, PqxdhInitialPreparedSourceInput.input,
        PqxdhSourceSharedPreparation.restore, PqxdhCommonSharedDispatch.restoreMode, map_pure, mem_support_pure_iff] at supported
      subst result
      trivial
  | pending prefixOutput ephemeral =>
      simp only [after] at supported
      split at supported
      · simp only [mem_support_pure_iff] at supported
        subst result
        trivial
      · exact prepared_joined setup env callbacks owner number bit attachedVerify primitives baseImpl kem _ _ _ _ _ _ _ supported

/-- Every actual supported full sampler retains the request-time composition certificate of its pending descriptor. All material draws and original completed outcomes remain present. -/
theorem run_joined (depth : Nat)
    (result : Carrier (setup := setup) (M := M) (P := P) (I := I) (K := K)
      (X := X) (Response := Response) (A := A) (KemSK := KemSK) (S := S) (B := B))
    (supported : result ∈ support (run setup env callbacks program adversary owner number bit attachedVerify primitives baseImpl kem ancestors disclosed depth)) :
    JoinedPacket setup owner number bit (result.1.2.1.1.1, result.2) := by
  simp only [run, mem_support_bind_iff, mem_support_pure_iff] at supported
  obtain ⟨packet, _, output, _, localPacket, reached, parent, _, nonce, _, chain, _, rfl⟩ := supported
  exact after_joined setup env callbacks program adversary owner number bit attachedVerify primitives baseImpl kem ancestors disclosed packet output depth localPacket reached

/-- The same request certificate holds after the complete actual shared-ROM execution, without assuming a descriptor or a sampler support law. -/
theorem evaluated_joined (depth : Nat)
    (result : Carrier (setup := setup) (M := M) (P := P) (I := I) (K := K)
      (X := X) (Response := Response) (A := A) (KemSK := KemSK) (S := S) (B := B) × CtxRO.QueryCache)
    (supported : result ∈ support ((simulateQ hashImpl
      (run setup env callbacks program adversary owner number bit attachedVerify primitives baseImpl kem ancestors disclosed depth)).run ∅)) :
    JoinedPacket setup owner number bit (result.1.1.2.1.1.1, result.1.2) := by
  apply run_joined setup env callbacks program adversary owner number bit attachedVerify primitives baseImpl kem ancestors disclosed depth
  apply support_simulateQ_run'_subset hashImpl _ ∅
  rw [StateT.run'_eq, support_map]
  exact ⟨result, supported, rfl⟩

/-- Erasing the captures before the original mathematical observer preserves its literal Gate/Fresh Boolean, full selected-key draw, and every common/cached decision. This is event transport, not an admissibility or secrecy claim for that observer. -/
theorem original_event (depth : Nat) :
    (do
      let result ← (simulateQ hashImpl (run setup env callbacks program adversary owner number bit attachedVerify primitives baseImpl kem ancestors disclosed depth)).run ∅
      let key ← $ᵗ RootOutput
      PqxdhErasedParentMaterial.observe env.source env.recordWriter env.senderId env.route env.decode
        (PqxdhLaterSharedMessagePrefix.restore setup result.1.1.2 result.2) key) =
      PqxdhErasedParentMaterial.ideal env.source env.recordWriter env.senderId env.route env.decode depth
        (PqxdhInitialPreparedSourceInput.prior env0 baseImpl kem attachedVerify primitives program post owner number ancestors disclosed) := by
  unfold PqxdhErasedParentMaterial.ideal
  rw [← source setup env callbacks program adversary owner number bit attachedVerify primitives baseImpl kem ancestors disclosed depth]
  simp only [bind_map_left]

end BeaconcryptCore.Computational.PqxdhLaterChallengeSampler

/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeSampler.prepared_erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeSampler.prepared_erase
/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeSampler.after_erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeSampler.after_erase
/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeSampler.run_erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeSampler.run_erase
/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeSampler.source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeSampler.source
/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeSampler.run_budget' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeSampler.run_budget
/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeSampler.prepared_joined' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeSampler.prepared_joined
/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeSampler.after_joined' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeSampler.after_joined
/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeSampler.run_joined' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeSampler.run_joined
/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeSampler.evaluated_joined' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeSampler.evaluated_joined
/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeSampler.original_event' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeSampler.original_event
