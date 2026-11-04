-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationServerRecordExecutor
import BeaconcryptCore.Refinement.AdapterRecordNativeWriter
import Cslib.Foundations.Control.Monad.IsMonadHom

/-! The actual first-record continuations are driven in an arbitrary shared monad. The writer returns its enclosing RustM result, so allocator or serializer failure/divergence remains distinct from an optional absent ciphertext. Only an actual successful borrowed slice is passed to ServerRecordWrite.resume. Initial KDF, ratchet KDF, seal and commitment callbacks retain their original order and optional failures. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformServerRecord
open RegistrationRecordPrimitives (Spec)
open RegistrationServerRecordExecutor (Result)
variable {m : Type → Type} [Monad m]

def continueWith {Input : Type} (action : RustM Input)
    (next : Input → m (RustM Result)) : m (RustM Result) :=
  match action with
  | .ok value => next value
  | .fail error => pure (.fail error)
  | .div => pure .div

def continueResult {Input : Type} (action : RustM (core.result.Result Input pqxdh.ServerState))
    (next : Input → m (RustM Result)) : m (RustM Result) :=
  match action with
  | .ok (.Ok value) => next value
  | .ok (.Err previous) => pure (.ok (.Err previous))
  | .fail error => pure (.fail error)
  | .div => pure .div

def fromWrite
    (write : record_effects.RecordWriteRequest → m (RustM (core.option.Option (Slice U8))))
    (pending : registration.ServerRecordWrite) : m (RustM Result) :=
  continueWith pending.request fun request => do
    let result ← write request
    pure (do let reply ← result; pending.resume reply)

def fromCommitment (record : QueryImpl Spec m)
    (write : record_effects.RecordWriteRequest → m (RustM (core.option.Option (Slice U8))))
    (pending : registration.ServerRecordCommitment) : m (RustM Result) :=
  continueWith pending.transcript fun transcript => do
    let reply ← record (.hash transcript)
    continueResult (pending.resume reply) (fromWrite write)

def fromAead (record : QueryImpl Spec m)
    (write : record_effects.RecordWriteRequest → m (RustM (core.option.Option (Slice U8))))
    (pending : registration.ServerRecordAead) : m (RustM Result) :=
  continueWith pending.request fun request => do
    let reply ← record (.seal request)
    continueResult (pending.resume reply) (fromCommitment record write)

def fromRatchet (record : QueryImpl Spec m)
    (write : record_effects.RecordWriteRequest → m (RustM (core.option.Option (Slice U8))))
    (pending : registration.ServerInitialSeal) : m (RustM Result) :=
  continueWith pending.request fun request => do
    let reply ← record (.ratchetKdf request)
    continueResult (pending.resume reply) (fromAead record write)

def fromInitial (record : QueryImpl Spec m)
    (write : record_effects.RecordWriteRequest → m (RustM (core.option.Option (Slice U8))))
    (pending : registration.ServerInitialKdf) : m (RustM Result) :=
  continueWith pending.request fun request => do
    let reply ← record (.initialKdf request)
    continueResult (pending.resume reply) (fromRatchet record write)

private theorem continueWith_simulate {Input : Type} (record : QueryImpl Spec m)
    (action : RustM Input) (next : Input → OracleComp Spec (RustM Result)) :
    simulateQ record (RegistrationServerRecordExecutor.continueWith action next) =
      continueWith action (fun value => simulateQ record (next value)) := by
  cases action <;> rfl

private theorem continueResult_simulate {Input : Type} (record : QueryImpl Spec m)
    (action : RustM (core.result.Result Input pqxdh.ServerState))
    (next : Input → OracleComp Spec (RustM Result)) :
    simulateQ record (RegistrationServerRecordExecutor.continueResult action next) =
      continueResult action (fun value => simulateQ record (next value)) := by
  cases action with
  | ok result => cases result <;> rfl
  | fail error => rfl
  | div => rfl

variable [LawfulMonad m]

theorem fromWrite_pure (record : QueryImpl Spec m) (pending : registration.ServerRecordWrite) :
    fromWrite (fun request => RustM.ok <$> record (.write request)) pending =
      simulateQ record (RegistrationServerRecordExecutor.fromWrite pending) := by
  unfold fromWrite RegistrationServerRecordExecutor.fromWrite
  rw [continueWith_simulate]
  apply congrArg (continueWith pending.request)
  funext request
  simp only [simulateQ_bind, simulateQ_spec_query, simulateQ_pure, bind_map_left]
  rfl

theorem fromCommitment_pure (record : QueryImpl Spec m) (pending : registration.ServerRecordCommitment) :
    fromCommitment record (fun request => RustM.ok <$> record (.write request)) pending =
      simulateQ record (RegistrationServerRecordExecutor.fromCommitment pending) := by
  unfold fromCommitment RegistrationServerRecordExecutor.fromCommitment
  rw [continueWith_simulate]
  apply congrArg (continueWith pending.transcript)
  funext transcript
  rw [simulateQ_bind, simulateQ_spec_query]
  apply bind_congr
  intro reply
  rw [continueResult_simulate]
  apply congrArg (continueResult (pending.resume reply))
  funext next
  exact fromWrite_pure record next

theorem fromAead_pure (record : QueryImpl Spec m) (pending : registration.ServerRecordAead) :
    fromAead record (fun request => RustM.ok <$> record (.write request)) pending =
      simulateQ record (RegistrationServerRecordExecutor.fromAead pending) := by
  unfold fromAead RegistrationServerRecordExecutor.fromAead
  rw [continueWith_simulate]
  apply congrArg (continueWith pending.request)
  funext request
  rw [simulateQ_bind, simulateQ_spec_query]
  apply bind_congr
  intro reply
  rw [continueResult_simulate]
  apply congrArg (continueResult (pending.resume reply))
  funext next
  exact fromCommitment_pure record next

theorem fromRatchet_pure (record : QueryImpl Spec m) (pending : registration.ServerInitialSeal) :
    fromRatchet record (fun request => RustM.ok <$> record (.write request)) pending =
      simulateQ record (RegistrationServerRecordExecutor.fromRatchet pending) := by
  unfold fromRatchet RegistrationServerRecordExecutor.fromRatchet
  rw [continueWith_simulate]
  apply congrArg (continueWith pending.request)
  funext request
  rw [simulateQ_bind, simulateQ_spec_query]
  apply bind_congr
  intro reply
  rw [continueResult_simulate]
  apply congrArg (continueResult (pending.resume reply))
  funext next
  exact fromAead_pure record next

theorem fromInitial_pure (record : QueryImpl Spec m) (pending : registration.ServerInitialKdf) :
    fromInitial record (fun request => RustM.ok <$> record (.write request)) pending =
      simulateQ record (RegistrationServerRecordExecutor.fromInitial pending) := by
  unfold fromInitial RegistrationServerRecordExecutor.fromInitial
  rw [continueWith_simulate]
  apply congrArg (continueWith pending.request)
  funext request
  rw [simulateQ_bind, simulateQ_spec_query]
  apply bind_congr
  intro reply
  rw [continueResult_simulate]
  apply congrArg (continueResult (pending.resume reply))
  funext next
  exact fromRatchet_pure record next

section Map
variable {left right : Type → Type} [Monad left] [Monad right]
variable {F : ∀ {Value : Type}, left Value → right Value}
variable (hom : Cslib.IsMonadHom left right F)
include hom

private theorem continueWith_map {Input : Type} (action : RustM Input)
    (next : Input → left (RustM Result)) :
    F (continueWith action next) = continueWith action (fun value => F (next value)) := by
  cases action <;> first | rfl | exact hom.map_pure _

private theorem continueResult_map {Input : Type} (action : RustM (core.result.Result Input pqxdh.ServerState))
    (next : Input → left (RustM Result)) :
    F (continueResult action next) = continueResult action (fun value => F (next value)) := by
  cases action with
  | ok result => cases result <;> first | rfl | exact hom.map_pure _
  | fail error => exact hom.map_pure _
  | div => exact hom.map_pure _

theorem fromWrite_map
    (write : record_effects.RecordWriteRequest → left (RustM (core.option.Option (Slice U8))))
    (pending : registration.ServerRecordWrite) :
    F (fromWrite write pending) = fromWrite (fun request => F (write request)) pending := by
  unfold fromWrite
  rw [continueWith_map hom]
  apply congrArg (continueWith pending.request)
  funext request
  rw [hom.map_bind]
  apply bind_congr
  intro result
  exact hom.map_pure _

theorem fromCommitment_map (record : QueryImpl Spec left)
    (write : record_effects.RecordWriteRequest → left (RustM (core.option.Option (Slice U8))))
    (pending : registration.ServerRecordCommitment) :
    F (fromCommitment record write pending) =
      fromCommitment (fun query => F (record query)) (fun request => F (write request)) pending := by
  unfold fromCommitment
  rw [continueWith_map hom]
  apply congrArg (continueWith pending.transcript)
  funext transcript
  rw [hom.map_bind]
  apply bind_congr
  intro reply
  rw [continueResult_map hom]
  apply congrArg (continueResult (pending.resume reply))
  funext next
  exact fromWrite_map hom write next

theorem fromAead_map (record : QueryImpl Spec left)
    (write : record_effects.RecordWriteRequest → left (RustM (core.option.Option (Slice U8))))
    (pending : registration.ServerRecordAead) :
    F (fromAead record write pending) =
      fromAead (fun query => F (record query)) (fun request => F (write request)) pending := by
  unfold fromAead
  rw [continueWith_map hom]
  apply congrArg (continueWith pending.request)
  funext request
  rw [hom.map_bind]
  apply bind_congr
  intro reply
  rw [continueResult_map hom]
  apply congrArg (continueResult (pending.resume reply))
  funext next
  exact fromCommitment_map hom record write next

theorem fromRatchet_map (record : QueryImpl Spec left)
    (write : record_effects.RecordWriteRequest → left (RustM (core.option.Option (Slice U8))))
    (pending : registration.ServerInitialSeal) :
    F (fromRatchet record write pending) =
      fromRatchet (fun query => F (record query)) (fun request => F (write request)) pending := by
  unfold fromRatchet
  rw [continueWith_map hom]
  apply congrArg (continueWith pending.request)
  funext request
  rw [hom.map_bind]
  apply bind_congr
  intro reply
  rw [continueResult_map hom]
  apply congrArg (continueResult (pending.resume reply))
  funext next
  exact fromAead_map hom record write next

theorem fromInitial_map (record : QueryImpl Spec left)
    (write : record_effects.RecordWriteRequest → left (RustM (core.option.Option (Slice U8))))
    (pending : registration.ServerInitialKdf) :
    F (fromInitial record write pending) =
      fromInitial (fun query => F (record query)) (fun request => F (write request)) pending := by
  unfold fromInitial
  rw [continueWith_map hom]
  apply congrArg (continueWith pending.request)
  funext request
  rw [hom.map_bind]
  apply bind_congr
  intro reply
  rw [continueResult_map hom]
  apply congrArg (continueResult (pending.resume reply))
  funext next
  exact fromRatchet_map hom record write next

end Map

omit [LawfulMonad m] in
theorem fromWrite_run {σ : Type}
    (write : record_effects.RecordWriteRequest → StateT σ m (RustM (core.option.Option (Slice U8))))
    (pending : registration.ServerRecordWrite) (before : σ) :
    (fromWrite write pending).run before =
      match pending.request with
      | .ok request => do
          let result ← (write request).run before
          pure ((do let reply ← result.1; pending.resume reply), result.2)
      | .fail error => pure (.fail error, before)
      | .div => pure (.div, before) := by
  unfold fromWrite continueWith
  cases pending.request with
  | ok request => exact StateT.run_bind _ _ _
  | fail error => rfl
  | div => rfl

end BeaconcryptCore.Computational.RegistrationNativePlatformServerRecord

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformServerRecord.fromWrite_pure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformServerRecord.fromWrite_pure
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformServerRecord.fromCommitment_pure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformServerRecord.fromCommitment_pure
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformServerRecord.fromAead_pure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformServerRecord.fromAead_pure
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformServerRecord.fromRatchet_pure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformServerRecord.fromRatchet_pure
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformServerRecord.fromInitial_pure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformServerRecord.fromInitial_pure
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformServerRecord.fromWrite_map' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformServerRecord.fromWrite_map
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformServerRecord.fromCommitment_map' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformServerRecord.fromCommitment_map
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformServerRecord.fromAead_map' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformServerRecord.fromAead_map
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformServerRecord.fromRatchet_map' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformServerRecord.fromRatchet_map
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformServerRecord.fromInitial_map' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformServerRecord.fromInitial_map
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformServerRecord.fromWrite_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformServerRecord.fromWrite_run
