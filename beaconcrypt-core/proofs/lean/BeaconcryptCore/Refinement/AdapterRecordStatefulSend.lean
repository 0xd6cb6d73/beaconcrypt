-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.AdapterRecordSendRequestExtraction
import BeaconcryptCore.Refinement.AdapterRecordSendBorrow
/-! Exact specialization and common-state interpretation of the actual outer send driver. Its private local leaf requests are interpreted by the trusted runtime; they are not public allocator requests. All optional failures and enclosing Rust outcomes retain the reached common state. -/
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 2048
namespace BeaconcryptCore.Refinement.AdapterRecordStatefulSend
open AdapterRecordSendRequestMonad
open AdapterPublicWrapperRustT (RustT)
abbrev Result := beaconcrypt_core.ratchet.concrete.ConcreteRatchetKernel ×
  core.option.Option beaconcrypt_record_send.shared.Encrypted

/-- The lifted body specializes exactly to the actual extracted outer source driver for every local primitive implementation. -/
theorem body_specializes [beaconcrypt_record_send.ratchet.Operations]
    (kernel : beaconcrypt_core.ratchet.concrete.ConcreteRatchetKernel)
    (context : beaconcrypt_core.record_effects.SealFrameContext) :
    AdapterRecordSendRequestExtraction.execute (m := RustM) kernel context =
      beaconcrypt_record_send.ratchet.execute_record_send kernel context := by
  rfl

def program (kernel : beaconcrypt_core.ratchet.concrete.ConcreteRatchetKernel)
    (context : beaconcrypt_core.record_effects.SealFrameContext) : OracleComp Spec (RustM Result) :=
  letI : Operations (RustT (OracleComp Spec)) := freeOperations
  (AdapterRecordSendRequestExtraction.execute (m := RustT (OracleComp Spec)) kernel context).run

def execute {m : Type → Type} [Monad m] (implementation : QueryImpl Spec m)
    (kernel : beaconcrypt_core.ratchet.concrete.ConcreteRatchetKernel)
    (context : beaconcrypt_core.record_effects.SealFrameContext) : m (RustM Result) :=
  letI : Operations (RustT m) := operations implementation
  (AdapterRecordSendRequestExtraction.execute (m := RustT m) kernel context).run
section Interpretation
variable {m : Type → Type} [Monad m] [LawfulMonad m] {A B : Type}
private def evaluate (implementation : QueryImpl Spec m) (work : RustT (OracleComp Spec) A) : RustT m A :=
  ⟨simulateQ implementation work.run⟩
omit [LawfulMonad m] in
private theorem evaluate_pure (implementation : QueryImpl Spec m) (value : A) :
    evaluate implementation (pure value) = pure value := rfl
omit [LawfulMonad m] in
private theorem evaluate_lift (implementation : QueryImpl Spec m) (value : RustM A) :
    evaluate implementation (AdapterRecordRequestMonad.liftRust value) =
      AdapterRecordRequestMonad.liftRust value := rfl
private theorem evaluate_bind (implementation : QueryImpl Spec m) (work : RustT (OracleComp Spec) A)
    (next : A → RustT (OracleComp Spec) B) :
    evaluate implementation (work >>= next) =
      (evaluate implementation work >>= fun value => evaluate implementation (next value)) := by
  apply RustT.ext
  simp only [evaluate, RustT.run_bind, simulateQ_bind]
  apply bind_congr
  intro result
  cases result <;> simp only [simulateQ_pure]
private theorem evaluate_kdf (implementation : QueryImpl Spec m)
    (request : beaconcrypt_core.ratchet.SymmetricRatchetKdfRequest) :
    evaluate implementation (@Operations.kdf (RustT (OracleComp Spec)) freeOperations request) =
      (⟨implementation (.kdf request)⟩ : RustT m beaconcrypt_core.ratchet.RatchetKdfResponse) := by
  apply RustT.ext
  exact simulateQ_spec_query implementation (.kdf request)

private theorem evaluate_sealing (implementation : QueryImpl Spec m)
    (request : beaconcrypt_core.record_effects.AeadSealRequest) :
    evaluate implementation (@Operations.sealing (RustT (OracleComp Spec)) freeOperations request) =
      (⟨implementation (.sealing request)⟩ : RustT m (core.option.Option (alloc.vec.Vec U8 × Array U8 16#usize))) := by
  apply RustT.ext
  exact simulateQ_spec_query implementation (.sealing request)

private theorem evaluate_hash (implementation : QueryImpl Spec m)
    (transcript : beaconcrypt_core.commitment.CommitmentTranscript) :
    evaluate implementation (@Operations.hash (RustT (OracleComp Spec)) freeOperations transcript) =
      (⟨implementation (.hash transcript)⟩ : RustT m
        (core.option.Option (Array U8 64#usize) × beaconcrypt_core.commitment.CommitmentTranscript)) := by
  apply RustT.ext
  exact simulateQ_spec_query implementation (.hash transcript)

private theorem evaluate_writer (implementation : QueryImpl Spec m)
    (request : beaconcrypt_core.record_effects.RecordWriteRequest) :
    evaluate implementation (@Operations.writer (RustT (OracleComp Spec)) freeOperations request) =
      (⟨implementation (.writer request)⟩ : RustT m (core.option.Option (alloc.vec.Vec U8))) := by
  apply RustT.ext
  exact simulateQ_spec_query implementation (.writer request)

attribute [local handler_simp] evaluate_bind evaluate_pure evaluate_lift evaluate_kdf evaluate_sealing evaluate_hash evaluate_writer
attribute [local handler_simp] Lifted.beginSend Lifted.kdfRequest Lifted.kdfResume
  Lifted.sealRequest Lifted.sealResume Lifted.transcriptMut Lifted.commitmentResume
  Lifted.writerRequest Lifted.writerFinish Lifted.asRef Lifted.asSlice Lifted.outputMap

/-- Every dynamic request is interpreted in the same monad as its source continuation, preserving all values, optional failures, enclosing Rust outcomes and shared poststates. -/
theorem interpreted (implementation : QueryImpl Spec m)
    (kernel : beaconcrypt_core.ratchet.concrete.ConcreteRatchetKernel)
    (context : beaconcrypt_core.record_effects.SealFrameContext) :
    simulateQ implementation (program kernel context) = execute implementation kernel context := by
  have same :
      evaluate implementation (letI : Operations (RustT (OracleComp Spec)) := freeOperations;
        AdapterRecordSendRequestExtraction.execute (m := RustT (OracleComp Spec)) kernel context) =
      (letI : Operations (RustT m) := operations implementation;
        AdapterRecordSendRequestExtraction.execute (m := RustT m) kernel context) := by
    dsimp only [AdapterRecordSendRequestExtraction.execute]
    repeat' first
      | rfl
      | simp only [handler_simp]
      | split
      | (apply bind_congr; intro value)

  exact congrArg RustT.run same

end Interpretation

end BeaconcryptCore.Refinement.AdapterRecordStatefulSend

/-- info: 'BeaconcryptCore.Refinement.AdapterRecordStatefulSend.body_specializes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterRecordStatefulSend.body_specializes

/-- info: 'BeaconcryptCore.Refinement.AdapterRecordStatefulSend.interpreted' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterRecordStatefulSend.interpreted
