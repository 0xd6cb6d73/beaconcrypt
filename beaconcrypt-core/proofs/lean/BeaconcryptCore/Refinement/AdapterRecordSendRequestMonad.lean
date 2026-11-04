-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.AdapterRecordSendExtraction.Funs
import BeaconcryptCore.Refinement.AdapterPublicWrapperRustT
/-! The actual outer send body keeps every extracted pure core call and moves only its four effectful local leaves to the common monad. A dynamic occurrence is a separate request, including repeated byte-identical inputs. Enclosing Rust failure/divergence and mutable transcript replacement remain literal. -/
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true
namespace BeaconcryptCore.Refinement.AdapterRecordSendRequestMonad
open AdapterRecordRequestMonad (LiftRust liftRust)
open AdapterPublicWrapperRustT (RustT)
class Operations (m : Type → Type) where
  kdf : beaconcrypt_core.ratchet.SymmetricRatchetKdfRequest → m beaconcrypt_core.ratchet.RatchetKdfResponse
  sealing : beaconcrypt_core.record_effects.AeadSealRequest → m (core.option.Option (alloc.vec.Vec U8 × Array U8 16#usize))
  hash : beaconcrypt_core.commitment.CommitmentTranscript → m (core.option.Option (Array U8 64#usize) × beaconcrypt_core.commitment.CommitmentTranscript)
  writer : beaconcrypt_core.record_effects.RecordWriteRequest → m (core.option.Option (alloc.vec.Vec U8))
instance [ops : beaconcrypt_record_send.ratchet.Operations] : Operations RustM where
  kdf := ops.kdf
  sealing := ops.sealing
  hash := ops.hash
  writer := ops.writer
namespace Lifted
variable {m : Type → Type} [Monad m] [LiftRust m]
open beaconcrypt_core
def beginSend (kernel : ratchet.concrete.ConcreteRatchetKernel) (context : record_effects.SealFrameContext) :=
  liftRust (record_effects.begin_record_send kernel context) (m := m)
def kdfRequest (pending : record_effects.RecordSendKdf) := liftRust pending.request (m := m)
def kdfResume (pending : record_effects.RecordSendKdf) (reply : ratchet.RatchetKdfResponse) :=
  liftRust (pending.resume reply) (m := m)
def sealRequest (pending : record_effects.SealAead) := liftRust pending.request (m := m)
def sealResume (pending : record_effects.SealAead) (reply : core.option.Option (Slice U8 × Array U8 16#usize)) :=
  liftRust (pending.resume reply) (m := m)
def transcriptMut (pending : record_effects.SealCommitment) := liftRust pending.transcript_mut (m := m)
def commitmentResume (pending : record_effects.SealCommitment) (reply : core.option.Option (Array U8 64#usize)) :=
  liftRust (pending.resume reply) (m := m)
def writerRequest (pending : record_effects.SealWrite) := liftRust pending.request (m := m)
def writerFinish (pending : record_effects.SealWrite) (reply : core.option.Option (alloc.vec.Vec U8)) :=
  liftRust (pending.finish reply) (m := m)
def asRef {T : Type} (value : core.option.Option T) := liftRust (core.option.Option.as_ref value) (m := m)
def asSlice (value : alloc.vec.Vec U8) := liftRust (alloc.vec.Vec.as_slice value) (m := m)
def outputMap (value : core.option.Option (record_effects.SealedRecord (alloc.vec.Vec U8))) :=
  liftRust (core.option.Option.map
    beaconcrypt_record_send.ratchet.execute_record_send.closure.Insts.CoreOpsFunctionFnOnceTupleSealedRecordVecU8Encrypted
    value ()) (m := m)
end Lifted

inductive Request where
  | kdf (request : beaconcrypt_core.ratchet.SymmetricRatchetKdfRequest)
  | sealing (request : beaconcrypt_core.record_effects.AeadSealRequest)
  | hash (transcript : beaconcrypt_core.commitment.CommitmentTranscript)
  | writer (request : beaconcrypt_core.record_effects.RecordWriteRequest)
abbrev Response : Request → Type
  | .kdf _ => beaconcrypt_core.ratchet.RatchetKdfResponse
  | .sealing _ => core.option.Option (alloc.vec.Vec U8 × Array U8 16#usize)
  | .hash _ => core.option.Option (Array U8 64#usize) × beaconcrypt_core.commitment.CommitmentTranscript
  | .writer _ => core.option.Option (alloc.vec.Vec U8)
abbrev Spec : OracleSpec Request := fun request => RustM (Response request)
@[instance_reducible]
def operations {m : Type → Type} [Monad m] (implementation : QueryImpl Spec m) : Operations (RustT m) where
  kdf request := ⟨implementation (.kdf request)⟩
  sealing request := ⟨implementation (.sealing request)⟩
  hash transcript := ⟨implementation (.hash transcript)⟩
  writer request := ⟨implementation (.writer request)⟩
@[instance_reducible]
def freeOperations : Operations (RustT (OracleComp Spec)) :=
  operations (fun request => OracleComp.lift (Spec.query request))
end BeaconcryptCore.Refinement.AdapterRecordSendRequestMonad
