-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.AdapterRecordExtraction.Funs
import BeaconcryptCore.Computational.VCVioForwardOracleComp

/-! A request interpretation for the selected extracted receive-loop body. The transformation retains the original pure core calls and moves only the four explicitly enumerated primitive calls into requests. Failure and divergence are short circuiting results; an optional primitive failure remains an ordinary reply and keeps the primitive poststate. -/

open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core

set_option autoImplicit false
set_option warningAsError true

namespace BeaconcryptCore.Refinement.AdapterRecordRequestMonad

class LiftRust (m : Type → Type) where
  liftRust {α : Type} : RustM α → m α

export LiftRust (liftRust)

instance : LiftRust RustM where
  liftRust value := value

class Operations (m : Type → Type) where
  kdf : ratchet.SymmetricRatchetKdfRequest → m ratchet.RatchetKdfResponse
  hash : commitment.CommitmentTranscript →
    m (Option (Array Std.U8 64#usize) × commitment.CommitmentTranscript)
  aead : Option record.AeadRequest → m (Option (alloc.vec.Vec Std.U8))
  compare : Slice Std.U8 → Slice Std.U8 → m Bool

instance [ops : beaconcrypt.ratchet.Operations] : Operations RustM where
  kdf := ops.kdf
  hash := ops.hash
  aead := ops.aead
  compare := ops.compare

namespace Lifted
variable {m : Type → Type} [Monad m] [LiftRust m]

def kdfRequest (pending : record_effects.RecordReceiveKdf) :=
  liftRust (record_effects.RecordReceiveKdf.request pending) (m := m)

def kdfResume (pending : record_effects.RecordReceiveKdf)
    (response : ratchet.RatchetKdfResponse) :=
  liftRust (record_effects.RecordReceiveKdf.resume pending response) (m := m)

def transcriptMut (pending : record_effects.RecordReceiveCommitment) :=
  liftRust (record_effects.RecordReceiveCommitment.transcript_mut pending) (m := m)

def suppliedCommitment (pending : record_effects.RecordReceiveCommitment) :=
  liftRust (record_effects.RecordReceiveCommitment.supplied_commitment pending) (m := m)

def commitmentResume (pending : record_effects.RecordReceiveCommitment) (matched : Bool) :=
  liftRust (record_effects.RecordReceiveCommitment.resume pending matched) (m := m)

def aeadRequest (pending : record_effects.RecordReceiveAead) :=
  liftRust (record_effects.RecordReceiveAead.request pending) (m := m)

def aeadFinish (pending : record_effects.RecordReceiveAead)
    (plaintext : Option (alloc.vec.Vec Std.U8)) :=
  liftRust (record_effects.RecordReceiveAead.finish pending plaintext) (m := m)

def outputMap (opened : Option (record.OpenedRecord (alloc.vec.Vec Std.U8))) :=
  liftRust (core.option.Option.map
    beaconcrypt.ratchet.execute_record_receive.closure.Insts.CoreOpsFunctionFnOnceTupleOpenedRecordVecU8Decrypted
    opened ()) (m := m)

def toSlice {n : Std.Usize} (bytes : Array Std.U8 n) :=
  liftRust (lift (Array.to_slice bytes)) (m := m)

end Lifted

inductive Request where
  | kdf (request : ratchet.SymmetricRatchetKdfRequest)
  | hash (transcript : commitment.CommitmentTranscript)
  | aead (request : Option record.AeadRequest)
  | compare (left right : Slice Std.U8)

abbrev Response : Request → Type
  | .kdf _ => ratchet.RatchetKdfResponse
  | .hash _ => Option (Array Std.U8 64#usize) × commitment.CommitmentTranscript
  | .aead _ => Option (alloc.vec.Vec Std.U8)
  | .compare _ _ => Bool

abbrev Spec : OracleSpec Request := fun request => RustM (Response request)

structure Program (α : Type) where
  run : OracleComp Spec (RustM α)

namespace Program

def pure {α : Type} (value : α) : Program α := ⟨Pure.pure (.ok value)⟩

def bind {α β : Type} (work : Program α) (next : α → Program β) : Program β :=
  ⟨do
    let result ← work.run
    match result with
    | .ok value => (next value).run
    | .fail error => Pure.pure (.fail error)
    | .div => Pure.pure .div⟩

instance : Monad Program where
  pure := pure
  bind := bind

instance : LiftRust Program where
  liftRust value := ⟨Pure.pure value⟩

def query (request : Request) : Program (Response request) :=
  ⟨OracleComp.lift (Spec.query request)⟩

instance : Operations Program where
  kdf request := query (.kdf request)
  hash transcript := query (.hash transcript)
  aead request := query (.aead request)
  compare left right := query (.compare left right)

@[simp] theorem run_pure {α : Type} (value : α) :
    (Pure.pure value : Program α).run = Pure.pure (.ok value) := rfl

@[simp] theorem run_lift {α : Type} (value : RustM α) :
    (liftRust value : Program α).run = Pure.pure value := rfl

@[simp] theorem run_bind {α β : Type} (work : Program α) (next : α → Program β) :
    (work >>= next).run = (do
      let result ← work.run
      match result with
      | .ok value => (next value).run
      | .fail error => Pure.pure (.fail error)
      | .div => Pure.pure .div) := rfl

theorem ext {α : Type} (left right : Program α) (same : left.run = right.run) : left = right := by
  cases left
  cases right
  cases same
  rfl

instance : LawfulMonad Program := LawfulMonad.mk' Program
  (by
    intro α work
    apply ext
    change (work.run >>= fun result => match result with
      | .ok value => Pure.pure (.ok value)
      | .fail error => Pure.pure (.fail error)
      | .div => Pure.pure .div) = work.run
    have same : (fun result : RustM α => match result with
        | .ok value => Pure.pure (.ok value)
        | .fail error => Pure.pure (.fail error)
        | .div => Pure.pure .div) = (Pure.pure : RustM α → OracleComp Spec (RustM α)) := by
      funext result
      cases result <;> rfl
    rw [same, bind_pure])
  (by intros; rfl)
  (by
    intro α β γ work next last
    apply ext
    simp only [run_bind, bind_assoc]
    refine bind_congr fun result => ?_
    cases result <;> simp only [pure_bind])

end Program

end BeaconcryptCore.Refinement.AdapterRecordRequestMonad

/-- info: 'BeaconcryptCore.Refinement.AdapterRecordRequestMonad.Program.run_pure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterRecordRequestMonad.Program.run_pure

/-- info: 'BeaconcryptCore.Refinement.AdapterRecordRequestMonad.Program.run_lift' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterRecordRequestMonad.Program.run_lift

/-- info: 'BeaconcryptCore.Refinement.AdapterRecordRequestMonad.Program.run_bind' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterRecordRequestMonad.Program.run_bind

/-- info: 'BeaconcryptCore.Refinement.AdapterRecordRequestMonad.Program.ext' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterRecordRequestMonad.Program.ext
