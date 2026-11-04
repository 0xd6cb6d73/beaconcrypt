-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformSourceRecord
/-! The actual two-KDF first-record prefix remains inside the private interpreter. It retains the original source requests, optional replies, every enclosing control failure and the complete common poststate before the suffix with its retained advanced kernel erased begins. -/
open OracleComp OracleSpec CoreModels Aeneas beaconcrypt_core
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPrivateRecordPrefix
variable {m : Type → Type} [Monad m]

def privatePrefix (record : QueryImpl RegistrationRecordPrimitives.Spec m) (initial : registration.ServerInitialKdf) :
    m (RustM (core.result.Result registration.ServerRecordAead pqxdh.ServerState)) :=
  match initial.request with
  | .fail error => pure (.fail error)
  | .div => pure .div
  | .ok request => do
    let reply ← record (.initialKdf request)
    match initial.resume reply with
    | .fail error => pure (.fail error)
    | .div => pure .div
    | .ok (.Err previous) => pure (.ok (.Err previous))
    | .ok (.Ok pending) => match pending.request with
      | .fail error => pure (.fail error)
      | .div => pure .div
      | .ok request => do
        let reply ← record (.ratchetKdf request)
        pure (pending.resume reply)

variable [LawfulMonad m]

/-- The literal source controller first executes exactly its private initial/ratchet KDF prefix, then the unchanged actual sealing/hash/writer suffix at the reached common state. -/
theorem source (record : QueryImpl RegistrationRecordPrimitives.Spec m)
    (sealing : record_effects.AeadSealRequest → m (RustM (core.option.Option (Slice U8 × Std.Array U8 16#usize))))
    (hash : commitment.CommitmentTranscript → m RegistrationNativePlatformCommitment.HashReply)
    (write : record_effects.RecordWriteRequest → m (RustM (core.option.Option (Slice U8))))
    (initial : registration.ServerInitialKdf) :
    RegistrationNativePlatformSourceRecord.fromInitialWithHash record sealing hash write initial = (do
      let selected ← privatePrefix record initial
      RegistrationNativePlatformServerRecord.continueResult selected
        (RegistrationNativePlatformSourceRecord.fromAeadWithHash sealing hash write)) := by
  unfold RegistrationNativePlatformSourceRecord.fromInitialWithHash privatePrefix
  cases asked : initial.request with
  | fail error => simp only [RegistrationNativePlatformServerRecord.continueWith, pure_bind]; rfl
  | div => simp only [RegistrationNativePlatformServerRecord.continueWith, pure_bind]; rfl
  | ok request =>
    simp only [RegistrationNativePlatformServerRecord.continueWith, bind_assoc]
    apply bind_congr
    intro reply
    cases resumed : initial.resume reply with
    | fail error => simp only [RegistrationNativePlatformServerRecord.continueResult, pure_bind]
    | div => simp only [RegistrationNativePlatformServerRecord.continueResult, pure_bind]
    | ok answer => cases answer with
      | Err previous => simp only [RegistrationNativePlatformServerRecord.continueResult, pure_bind]
      | Ok pending =>
        simp only [RegistrationNativePlatformServerRecord.continueResult, RegistrationNativePlatformSourceRecord.fromRatchetWithHash]
        cases requested : pending.request with
        | fail error => simp only [RegistrationNativePlatformServerRecord.continueWith, pure_bind]
        | div => simp only [RegistrationNativePlatformServerRecord.continueWith, pure_bind]
        | ok request => simp only [RegistrationNativePlatformServerRecord.continueWith, bind_assoc, pure_bind]

end BeaconcryptCore.Computational.RegistrationNativePlatformPrivateRecordPrefix

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPrivateRecordPrefix.source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPrivateRecordPrefix.source
