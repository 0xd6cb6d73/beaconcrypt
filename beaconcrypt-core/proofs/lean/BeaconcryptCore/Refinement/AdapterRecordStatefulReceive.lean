-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.AdapterRecordRequestExtraction
import BeaconcryptCore.Refinement.AdapterRecordReceive

/-! The generated request-body specialization equals the actual Aeneas body by a kernel-checked proof. Stateful interpretation uses a separate request for each dynamic occurrence, so repeated identical requests may receive different replies and retain all primitive effects. -/

open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM ControlFlow beaconcrypt_core

set_option autoImplicit false
set_option warningAsError true

namespace BeaconcryptCore.Refinement.AdapterRecordStatefulReceive
open AdapterRecordRequestMonad

/-- The lifting transformation preserves the extracted body for every primitive implementation. -/
theorem body_specializes [beaconcrypt.ratchet.Operations]
    (effect : record_effects.RecordReceiveEffect) :
    AdapterRecordRequestExtraction.body (m := RustM) effect =
      beaconcrypt.ratchet.execute_record_receive_loop.body effect := by
  cases effect <;> try rfl
  simp! only [AdapterRecordRequestExtraction.body,
    beaconcrypt.ratchet.execute_record_receive_loop.body,
    Lifted.transcriptMut, Lifted.suppliedCommitment,
    Lifted.commitmentResume, Lifted.toSlice, liftRust, Operations.hash,
    Operations.compare, beaconcrypt.ratchet.execute_commitment_hash,
    beaconcrypt_crypto.utils.memcmp, record_effects.RecordReceiveCommitment.transcript_mut,
    bind_tc_ok, pure]
  congr 1
  funext ⟨actual, transcript⟩
  cases actual <;> simp! only [bind_tc_ok, bind_assoc_eq]

abbrev NativeSpec := (ratchet.SymmetricRatchetKdfRequest →ₒ ratchet.RatchetKdfResponse) +
  ((Pqxdh.Bytes →ₒ Option (Array Std.U8 64#usize)) +
    (BeaconcryptCore.Computational.RawCtxSourceOpen.BaseInput →ₒ Option (alloc.vec.Vec Std.U8)))

open BeaconcryptCore.Computational

/-- Typed native primitive replies retain optional failure without presupposing any security property. -/
def native (erased : Array Std.U8 227#usize) : QueryImpl Spec (OracleComp NativeSpec)
  | .kdf request => .ok <$> NativeSpec.query (.inl request)
  | .hash transcript => (fun digest => .ok (digest, { bytes := erased })) <$>
      NativeSpec.query (.inr (.inl (PqxdhRefinement.absBytes transcript.bytes)))
  | .aead none => pure (.ok none)
  | .aead (some request) => .ok <$>
      NativeSpec.query (.inr (.inr (RecordEffectsReceiveProgram.aeadQuery request)))
  | .compare left right => pure (.ok (decide
      (left.val.map PqxdhRefinement.absByte = right.val.map PqxdhRefinement.absByte)))

/-- The abstract receive model uses the same dynamic requests and exact byte representations. -/
def abstractNative : QueryImpl RawCtxSourceOpen.NativeSpec (OracleComp NativeSpec)
  | .inl request => NativeSpec.query (.inl request)
  | .inr (.inl bytes) => Option.map PqxdhRefinement.absBytes <$>
      NativeSpec.query (.inr (.inl bytes))
  | .inr (.inr request) => Option.map (fun bytes => bytes.val.map PqxdhRefinement.absByte) <$>
      NativeSpec.query (.inr (.inr request))

abbrev Result := ratchet.concrete.ConcreteRatchetKernel × Option beaconcrypt.shared.Decrypted

def drive : Nat → record_effects.RecordReceiveEffect → Program Result
  | 0, _ => liftRust .div
  | fuel + 1, effect => do
      let control ← AdapterRecordRequestExtraction.body (m := Program) effect
      match control with
      | .cont next => drive fuel next
      | .done result => pure result

def interpret {α : Type} (erased : Array Std.U8 227#usize) (work : Program α) :
    OracleComp NativeSpec (RustM α) := simulateQ (native erased) work.run

@[simp] theorem interpret_pure {α : Type} (erased : Array Std.U8 227#usize) (value : α) :
    interpret erased (pure value) = pure (.ok value) := rfl

@[simp] theorem interpret_lift {α : Type} (erased : Array Std.U8 227#usize) (value : RustM α) :
    interpret erased (liftRust value) = pure value := rfl

/-- Source bind retains the primitive state from the entire prefix on failure and divergence. -/
theorem interpret_bind {α β : Type} (erased : Array Std.U8 227#usize)
    (work : Program α) (next : α → Program β) :
    interpret erased (work >>= next) = (do
      let result ← interpret erased work
      match result with
      | .ok value => interpret erased (next value)
      | .fail error => pure (.fail error)
      | .div => pure .div) := by
  change simulateQ (native erased) (do
    let result ← work.run
    match result with
    | .ok value => (next value).run
    | .fail error => pure (.fail error)
    | .div => pure .div) = _
  rw [simulateQ_bind]
  refine bind_congr fun result => ?_
  cases result <;> rfl

@[simp] theorem interpret_query (erased : Array Std.U8 227#usize) (request : Request) :
    interpret erased (Program.query request) = native erased request := by
  exact simulateQ_spec_query (native erased) request

/-- A complete AEAD phase returns the generated output closure's exact result and retained kernel. -/
theorem drive_aead (fuel : Nat) (erased : Array Std.U8 227#usize)
    (pending : record_effects.RecordReceiveAead) :
    (fun result => AdapterRecordReceive.decodeResult <$> result) <$>
      interpret erased (drive (fuel + 1) (.AeadRequested pending)) =
      simulateQ abstractNative (RecordEffectsReceiveProgram.execute erased (.AeadRequested pending)) := by
  obtain ⟨request, requested⟩ := BeaconcryptCore.PanicFreedom.RecordEffects.RecordReceiveAead_request_total pending
  rw [RecordEffectsReceiveProgram.execute, ← QueryImpl.simulateQ_compose]
  simp only [RecordEffectsReceiveProgram.executeAead, requested,
    RawCtxInterpretedOpening.bindResult]
  simp only [drive, AdapterRecordRequestExtraction.body, Lifted.aeadRequest,
    Lifted.aeadFinish, Lifted.outputMap, Operations.aead, interpret,
    Program.run_bind, Program.run_lift, Program.run_pure, Program.query,
    simulateQ_bind, simulateQ_spec_query, requested, pure_bind]
  cases request with
  | none =>
      obtain ⟨⟨kernel, opened⟩, finished⟩ :=
        BeaconcryptCore.PanicFreedom.RecordEffects.RecordReceiveAead_finish_total pending
          (none : Option (alloc.vec.Vec Std.U8))
      simp only [native, pure_bind, finished, AdapterRecordReceive.output_map,
        simulateQ_pure, Program.run_pure, map_pure]
      have finishedBytes : pending.finish (none : Option Pqxdh.Bytes) =
          ok (kernel, Option.map AdapterRecordReceive.abstractOpened opened) := by
        simpa only [Option.map_none, finished, AdapterRecordReceive.rust_map_eq_bind, bind_tc_ok] using
          (AdapterRecordReceive.finish_bytes pending none).symm
      simp only [finishedBytes, simulateQ_pure]
      cases opened <;> rfl
  | some request =>
      simp only [native, bind_map_left, bind_assoc, map_bind, simulateQ_bind,
        simulateQ_spec_query, QueryImpl.apply_compose, RawCtxSourceOpen.openLift,
        abstractNative]
      refine bind_congr fun plaintext => ?_
      obtain ⟨⟨kernel, opened⟩, finished⟩ :=
        BeaconcryptCore.PanicFreedom.RecordEffects.RecordReceiveAead_finish_total pending plaintext
      have finishedBytes : pending.finish
          (Option.map (fun bytes => bytes.val.map PqxdhRefinement.absByte) plaintext) =
          ok (kernel, Option.map AdapterRecordReceive.abstractOpened opened) := by
        simpa only [finished, AdapterRecordReceive.rust_map_eq_bind, bind_tc_ok] using
          (AdapterRecordReceive.finish_bytes pending plaintext).symm
      simp only [finished, finishedBytes, AdapterRecordReceive.output_map,
        simulateQ_pure, pure_bind, Program.run_pure, map_pure]
      cases opened <;> rfl

@[simp] theorem drive_rejected (fuel : Nat) (erased : Array Std.U8 227#usize)
    (kernel : ratchet.concrete.ConcreteRatchetKernel) :
    interpret erased (drive (fuel + 1) (.Rejected kernel)) = pure (.ok (kernel, none)) := rfl

/-- Native comparison on the generated array slices is exact byte equality. -/
theorem native_compare_arrays (erased : Array Std.U8 227#usize)
    (left right : Array Std.U8 64#usize) :
    native erased (.compare left.to_slice right.to_slice) =
      pure (.ok (decide (PqxdhRefinement.absBytes left = PqxdhRefinement.absBytes right))) := rfl

theorem native_hash (erased : Array Std.U8 227#usize)
    (transcript : commitment.CommitmentTranscript) :
    native erased (.hash transcript) = (fun digest => .ok (digest, { bytes := erased })) <$>
      (NativeSpec.query (.inr (.inl (PqxdhRefinement.absBytes transcript.bytes))) :
        OracleComp NativeSpec (Option (Array Std.U8 64#usize))) := rfl

theorem native_kdf (erased : Array Std.U8 227#usize)
    (request : ratchet.SymmetricRatchetKdfRequest) :
    native erased (.kdf request) = .ok <$>
      (NativeSpec.query (.inl request) : OracleComp NativeSpec ratchet.RatchetKdfResponse) := rfl

attribute [local irreducible] native

/-- Hash failure and commitment rejection retain the overwritten transcript and all hash effects. -/
theorem drive_commitment (fuel : Nat) (erased : Array Std.U8 227#usize)
    (pending : record_effects.RecordReceiveCommitment) :
    (fun result => AdapterRecordReceive.decodeResult <$> result) <$>
      interpret erased (drive (fuel + 2) (.CommitmentRequested pending)) =
      simulateQ abstractNative (RecordEffectsReceiveProgram.execute erased (.CommitmentRequested pending)) := by
  rw [drive, RecordEffectsReceiveProgram.execute, ← QueryImpl.simulateQ_compose]
  simp! only [AdapterRecordRequestExtraction.body, Lifted.transcriptMut,
    Lifted.suppliedCommitment, Lifted.commitmentResume, Lifted.toSlice,
    Operations.hash, Operations.compare, interpret, Program.run_bind,
    Program.run_lift, Program.run_pure, Program.query, simulateQ_bind,
    simulateQ_spec_query, record_effects.RecordReceiveCommitment.transcript_mut,
    pure_bind, native_hash]
  simp only [RecordEffectsReceiveProgram.executeCommitment,
    record_effects.RecordReceiveCommitment.transcript, record.OpenCommitment.impl.transcript,
    commitment.CommitmentTranscript.as_bytes, RawCtxInterpretedOpening.bindResult,
    simulateQ_bind, simulateQ_spec_query, QueryImpl.apply_compose,
    RawCtxSourceOpen.openLift, abstractNative, bind_map_left, bind_assoc, map_bind]
  refine bind_congr fun digest => ?_
  cases digest with
  | none =>
      simp! only [record_effects.RecordReceiveCommitment.transcript_mut,
        commitment.CommitmentTranscript.as_mut_bytes, RecordEffectsReceiveProgram.compareDigest,
        record_effects.RecordReceiveCommitment.resume, record.OpenCommitment.resume,
        ratchet.concrete.ReceiveOpen.reject, Program.run_bind, Program.run_lift,
        Program.run_pure, simulateQ_pure, pure_bind, Bool.false_eq_true, ite_false]
      simp! only [bind_tc_ok, simulateQ_pure, pure_bind,
        AdapterRecordRequestExtraction.body, Program.run_pure, map_pure]
      rfl
  | some digest =>
      simp! only [Program.run_bind, Program.run_lift, Program.run_pure,
        record_effects.RecordReceiveCommitment.transcript_mut,
        commitment.CommitmentTranscript.as_mut_bytes, RecordEffectsReceiveProgram.compareDigest,
        record_effects.RecordReceiveCommitment.supplied_commitment,
        record.OpenCommitment.supplied_commitment, ratchet.concrete.ReceiveOpen.impl.context,
        Aeneas.Std.lift, bind_tc_ok, pure_bind, simulateQ_bind,
        simulateQ_spec_query, Option.map_some]
      cases matched : decide (PqxdhRefinement.absBytes digest =
          PqxdhRefinement.absBytes pending.pending.opening.context.commitment)
      all_goals simp only [native_compare_arrays, pure_bind, matched]
      case false =>
        simp! only [matched, record_effects.RecordReceiveCommitment.resume,
          record.OpenCommitment.resume, ratchet.concrete.ReceiveOpen.reject,
          bind_tc_ok, Bool.false_eq_true, ite_false, simulateQ_pure, pure_bind,
          AdapterRecordRequestExtraction.body, Program.run_pure, map_pure]
        rfl
      case true =>
        simp! only [matched, record_effects.RecordReceiveCommitment.resume,
          record.OpenCommitment.resume, bind_tc_ok, ite_true, simulateQ_pure, pure_bind]
        simpa only [drive, AdapterRecordRequestExtraction.body, interpret,
          RecordEffectsReceiveProgram.execute, ← QueryImpl.simulateQ_compose] using
          drive_aead fuel erased ⟨{ opening := pending.pending.opening }⟩

/-- The mechanically lifted complete receive loop agrees as a request program, for every dynamic primitive reply history. The rank allowance covers every KDF continuation plus commitment and AEAD phases. -/
theorem drive_source (fuel : Nat) (erased : Array Std.U8 227#usize)
    (effect : record_effects.RecordReceiveEffect)
    (enough : RecordEffectsReceiveRank.rank effect + 2 ≤ fuel) :
    (fun result => AdapterRecordReceive.decodeResult <$> result) <$>
      interpret erased (drive fuel effect) =
      simulateQ abstractNative (RecordEffectsReceiveProgram.execute erased effect) := by
  induction fuel generalizing effect with
  | zero => omega
  | succ fuel ih =>
      cases effect with
      | Rejected kernel =>
          simp only [drive_rejected, map_pure, RecordEffectsReceiveProgram.execute, simulateQ_pure]
          rfl
      | AeadRequested pending => exact drive_aead fuel erased pending
      | CommitmentRequested pending =>
          cases fuel with
          | zero => simp [RecordEffectsReceiveRank.rank] at enough
          | succ fuel => exact drive_commitment fuel erased pending
      | KdfRequested pending =>
          rw [drive, RecordEffectsReceiveProgram.execute_kdf]
          simp only [AdapterRecordRequestExtraction.body, Lifted.kdfRequest, Lifted.kdfResume,
            Operations.kdf, record_effects.RecordReceiveKdf.request,
            ratchet.concrete.ReceiveKdf.impl.request, interpret, Program.run_bind,
            Program.run_lift, Program.query, simulateQ_bind,
            simulateQ_spec_query, pure_bind, native_kdf, abstractNative,
            bind_map_left, bind_assoc, map_bind]
          refine bind_congr fun response => ?_
          obtain ⟨next, resumed⟩ :=
            BeaconcryptCore.PanicFreedom.RecordEffects.RecordReceiveKdf_resume_total pending response
          simp only [resumed, RawCtxInterpretedOpening.bindResult]
          apply ih next
          have decreasing := RecordEffectsReceiveRank.resume_decreasing pending response next resumed
          omega

/-- Fixed native replies recover the original extracted RustM receiver. -/
def deterministic (replies : AdapterRecordReceive.Replies) : QueryImpl NativeSpec Id
  | .inl request => replies.kdf request
  | .inr (.inl bytes) => replies.hash bytes
  | .inr (.inr request) => replies.aead request

/-- Concrete byte adaptation recovers the established original-source interpreter exactly. -/
theorem abstract_deterministic (replies : AdapterRecordReceive.Replies) :
    deterministic replies ∘ₛ abstractNative = AdapterRecordReceive.implementation replies := by
  funext request
  cases request with
  | inl request =>
      simp only [QueryImpl.apply_compose, abstractNative, simulateQ_spec_query,
        deterministic, AdapterRecordReceive.implementation]
  | inr request =>
      cases request <;> simp only [QueryImpl.apply_compose, abstractNative, simulateQ_map,
        simulateQ_spec_query, deterministic, AdapterRecordReceive.implementation] <;> rfl

/-- The complete lifted loop's fixed-reply specialization is the actual extracted controller, including its output closure and full returned kernel. -/
theorem controller_specializes (replies : AdapterRecordReceive.Replies)
    (erased : Array Std.U8 227#usize) (effect : record_effects.RecordReceiveEffect) :
    simulateQ (deterministic replies)
      ((fun result => AdapterRecordReceive.decodeResult <$> result) <$>
        interpret erased (drive (RecordEffectsReceiveRank.rank effect + 2) effect)) =
      AdapterRecordReceive.decodeResult <$>
        @beaconcrypt.ratchet.execute_record_receive (AdapterRecordReceive.operations replies erased) effect := by
  rw [drive_source _ _ _ (Nat.le_refl _), ← QueryImpl.simulateQ_compose,
    abstract_deterministic]
  exact (AdapterRecordReceive.receiver_source replies erased effect).symm

/-- Both certificates of the checked source transformation and full-state execution correspondence are retained at this endpoint. Primitive state may contain the shared caches, counters and histories of an arbitrary preceding execution. -/
theorem source_stateful {PrimitiveState ι : Type} {base : OracleSpec ι}
    (impl : QueryImpl NativeSpec (StateT PrimitiveState (OracleComp base)))
    (erased : Array Std.U8 227#usize) (effect : record_effects.RecordReceiveEffect)
    (state : PrimitiveState) :
    (∀ (ops : beaconcrypt.ratchet.Operations),
      letI : beaconcrypt.ratchet.Operations := ops
      AdapterRecordRequestExtraction.body (m := RustM) effect =
        beaconcrypt.ratchet.execute_record_receive_loop.body effect) ∧
    (simulateQ impl ((fun result => AdapterRecordReceive.decodeResult <$> result) <$>
      interpret erased (drive (RecordEffectsReceiveRank.rank effect + 2) effect))).run state =
    (simulateQ impl (simulateQ abstractNative
      (RecordEffectsReceiveProgram.execute erased effect))).run state := by
  constructor
  · intro ops
    exact @body_specializes ops effect
  · exact congrArg (fun work => (simulateQ impl work).run state)
      (drive_source _ _ _ (Nat.le_refl _))

/-- Arbitrary later API calls and observations run from the same complete primitive poststate; optional failures retain their prior effects. -/
theorem source_stateful_continuation {PrimitiveState ι Output : Type} {base : OracleSpec ι}
    (impl : QueryImpl NativeSpec (StateT PrimitiveState (OracleComp base)))
    (erased : Array Std.U8 227#usize) (effect : record_effects.RecordReceiveEffect)
    (later : RustM RecordEffectsReceiveProgram.Result → OracleComp NativeSpec Output)
    (state : PrimitiveState) :
    (simulateQ impl (do
      let result ← (fun result => AdapterRecordReceive.decodeResult <$> result) <$>
        interpret erased (drive (RecordEffectsReceiveRank.rank effect + 2) effect)
      later result)).run state =
    (simulateQ impl (do
      let result ← simulateQ abstractNative (RecordEffectsReceiveProgram.execute erased effect)
      later result)).run state := by
  simp only [simulateQ_bind, StateT.run_bind]
  rw [(source_stateful impl erased effect state).2]

/-- Admission is the actual extracted core entrypoint. The complete loop is driven with its proved sufficient allowance. -/
def receive (kernel : ratchet.concrete.ConcreteRatchetKernel) (sequence : Std.U64)
    (payload : Slice Std.U8) (ad : Array Std.U8 151#usize) (sender : Std.U64) : Program Result := do
  let effect ← liftRust (record_effects.begin_record_receive kernel sequence payload ad sender)
  drive (RecordEffectsReceiveRank.rank effect + 2) effect

/-- Actual admission followed by the lifted generated controller equals the maintained request semantics. -/
theorem receive_source (erased : Array Std.U8 227#usize)
    (kernel : ratchet.concrete.ConcreteRatchetKernel) (sequence : Std.U64)
    (payload : Slice Std.U8) (ad : Array Std.U8 151#usize) (sender : Std.U64) :
    (fun result => AdapterRecordReceive.decodeResult <$> result) <$>
      interpret erased (receive kernel sequence payload ad sender) =
      simulateQ abstractNative
        (RecordEffectsReceiveProgram.receive erased kernel sequence payload ad sender) := by
  obtain ⟨effect, admitted⟩ := BeaconcryptCore.PanicFreedom.RecordEffects.begin_record_receive_total
    kernel sequence payload ad sender
  simp only [receive, interpret_bind, interpret_lift, admitted, pure_bind,
    RecordEffectsReceiveProgram.receive, RawCtxInterpretedOpening.bindResult]
  exact drive_source _ _ _ (Nat.le_refl _)

/-- Composition reaches the existing source-native receive bridge with optional failures and the full returned protocol kernel retained. -/
theorem receive_native_model (erased : Array Std.U8 227#usize)
    (kernel : ratchet.concrete.ConcreteRatchetKernel) (sequence : Std.U64)
    (payload : Slice Std.U8) (ad : Array Std.U8 151#usize) (sender : Std.U64) :
    (fun result => AdapterRecordReceive.decodeResult <$> result) <$>
      interpret erased (receive kernel sequence payload ad sender) =
      simulateQ abstractNative
        (RawCtxInterpretedOpening.bindResult (record.OpenFrameContext.from_frame payload ad sender)
          (fun admitted => match admitted with
            | none => pure (.ok (kernel, none))
            | some context => PqxdhOpenContextBridge.executeReceiveFrom erased kernel sequence context)) := by
  exact (receive_source erased kernel sequence payload ad sender).trans
    (congrArg (simulateQ abstractNative)
      (RecordEffectsReceiveBridge.receive_execution erased kernel sequence payload ad sender))

/-- All later callbacks run from exactly the same returned protocol value and primitive state. This equality permits an arbitrary shared stateful KDF/hash/AEAD implementation and arbitrary preceding primitive histories. -/
theorem receive_stateful_continuation {PrimitiveState ι Output : Type} {base : OracleSpec ι}
    (impl : QueryImpl NativeSpec (StateT PrimitiveState (OracleComp base)))
    (erased : Array Std.U8 227#usize)
    (kernel : ratchet.concrete.ConcreteRatchetKernel) (sequence : Std.U64)
    (payload : Slice Std.U8) (ad : Array Std.U8 151#usize) (sender : Std.U64)
    (later : RustM RecordEffectsReceiveProgram.Result → OracleComp NativeSpec Output)
    (state : PrimitiveState) :
    (simulateQ impl (do
      let result ← (fun result => AdapterRecordReceive.decodeResult <$> result) <$>
        interpret erased (receive kernel sequence payload ad sender)
      later result)).run state =
    (simulateQ impl (do
      let result ← simulateQ abstractNative
        (RecordEffectsReceiveProgram.receive erased kernel sequence payload ad sender)
      later result)).run state := by
  rw [receive_source]

end BeaconcryptCore.Refinement.AdapterRecordStatefulReceive

/-- info: 'BeaconcryptCore.Refinement.AdapterRecordStatefulReceive.body_specializes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterRecordStatefulReceive.body_specializes

/-- info: 'BeaconcryptCore.Refinement.AdapterRecordStatefulReceive.interpret_pure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterRecordStatefulReceive.interpret_pure

/-- info: 'BeaconcryptCore.Refinement.AdapterRecordStatefulReceive.interpret_lift' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterRecordStatefulReceive.interpret_lift

/-- info: 'BeaconcryptCore.Refinement.AdapterRecordStatefulReceive.interpret_bind' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterRecordStatefulReceive.interpret_bind

/-- info: 'BeaconcryptCore.Refinement.AdapterRecordStatefulReceive.interpret_query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterRecordStatefulReceive.interpret_query

/-- info: 'BeaconcryptCore.Refinement.AdapterRecordStatefulReceive.drive_aead' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterRecordStatefulReceive.drive_aead

/-- info: 'BeaconcryptCore.Refinement.AdapterRecordStatefulReceive.drive_rejected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterRecordStatefulReceive.drive_rejected

/-- info: 'BeaconcryptCore.Refinement.AdapterRecordStatefulReceive.native_compare_arrays' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterRecordStatefulReceive.native_compare_arrays

/-- info: 'BeaconcryptCore.Refinement.AdapterRecordStatefulReceive.native_hash' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterRecordStatefulReceive.native_hash

/-- info: 'BeaconcryptCore.Refinement.AdapterRecordStatefulReceive.native_kdf' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterRecordStatefulReceive.native_kdf

/-- info: 'BeaconcryptCore.Refinement.AdapterRecordStatefulReceive.drive_commitment' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterRecordStatefulReceive.drive_commitment

/-- info: 'BeaconcryptCore.Refinement.AdapterRecordStatefulReceive.drive_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterRecordStatefulReceive.drive_source

/-- info: 'BeaconcryptCore.Refinement.AdapterRecordStatefulReceive.abstract_deterministic' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterRecordStatefulReceive.abstract_deterministic

/-- info: 'BeaconcryptCore.Refinement.AdapterRecordStatefulReceive.controller_specializes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterRecordStatefulReceive.controller_specializes

/-- info: 'BeaconcryptCore.Refinement.AdapterRecordStatefulReceive.source_stateful' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterRecordStatefulReceive.source_stateful

/-- info: 'BeaconcryptCore.Refinement.AdapterRecordStatefulReceive.source_stateful_continuation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterRecordStatefulReceive.source_stateful_continuation

/-- info: 'BeaconcryptCore.Refinement.AdapterRecordStatefulReceive.receive_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterRecordStatefulReceive.receive_source

/-- info: 'BeaconcryptCore.Refinement.AdapterRecordStatefulReceive.receive_native_model' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterRecordStatefulReceive.receive_native_model

/-- info: 'BeaconcryptCore.Refinement.AdapterRecordStatefulReceive.receive_stateful_continuation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterRecordStatefulReceive.receive_stateful_continuation
