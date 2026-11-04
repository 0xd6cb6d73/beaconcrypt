-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.AdapterPublicServerBuildBody
import BeaconcryptCore.Computational.RegistrationNativePlatformSourceRecord
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
/-! The actual Server builder's first-record suffix composes with the existing source-native record controller. Detached seal, mutable transcript hash and byte writer remain literal source leaf programs with their complete RustM failures and shared state. Only the individual initial/ratchet HKDF normal functional interpretations are selected separately. -/
namespace BeaconcryptCore.Refinement.AdapterPublicServerRecord
open AdapterPublicWrapperRustT (RustT)
open AdapterPublicWrapperRequestMonad
open AdapterRecordRequestMonad (liftRust)
open BeaconcryptCore.Computational
open AdapterPublicServerBuildBody (Server Reply)
variable [material : PublicWrapperPlatform.Material] [platform : PublicWrapperPlatform.Platform]
variable [primitive : AdapterInitEdPrimitive.Operations] [PublicWrapperPlatform.Allocator]
variable [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations]
variable {m : Type → Type} [Monad m] [LawfulMonad m]
variable [localOps : LocalOperations (RustT m)]
variable [containers : ContainerOperations (RustT m)] [children : ChildOperations (RustT m)]

noncomputable def afterRecord (self : Server) : RustM RegistrationServerRecordExecutor.Result → m (RustM Reply)
  | .fail error => pure (.fail error)
  | .div => pure .div
  | .ok (.Err _) => pure (.ok (.None, self))
  | .ok (.Ok pending) => (AdapterPublicServerBuildBody.sign self pending).run

omit localOps containers children in
def resumeResult {A Error : Type} (self : Server) (action : RustM (core.result.Result A Error))
    (next : A → m (RustM Reply)) : m (RustM Reply) :=
  match action with
  | .fail error => pure (.fail error)
  | .div => pure .div
  | .ok (.Err _) => pure (.ok (.None, self))
  | .ok (.Ok value) => next value

omit localOps containers children [PublicWrapperPlatform.Allocator] [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations] in
theorem checked {A Error : Type} (self : Server) (action : RustM (core.result.Result A Error))
    (next : A → RustT m Reply) :
    (AdapterPublicServerBuildBody.checked self action next).run = resumeResult self action (fun value => (next value).run) := by
  cases action with
  | fail error | div => simp only [AdapterPublicServerBuildBody.checked, RustT.run_bind, RustT.run_liftRust, pure_bind, resumeResult]
  | ok result => cases result <;>
      simp only [AdapterPublicServerBuildBody.checked, RustT.run_bind, RustT.run_liftRust, pure_bind, RustT.run_pure, resumeResult]

private theorem fused {A : Type} (self : Server) (action : RustM (core.result.Result A pqxdh.ServerState))
    (next : A → m (RustM RegistrationServerRecordExecutor.Result)) :
    (do let result ← RegistrationNativePlatformServerRecord.continueResult action next
        afterRecord self result) = resumeResult self action (fun value => do let result ← next value; afterRecord self result) := by
  cases action with
  | fail error | div => simp only [RegistrationNativePlatformServerRecord.continueResult, pure_bind, afterRecord, resumeResult]
  | ok result => cases result <;>
      simp only [RegistrationNativePlatformServerRecord.continueResult, pure_bind, afterRecord, resumeResult]

noncomputable def writeLeaf (request : record_effects.RecordWriteRequest) :
    m (RustM (core.option.Option (Slice U8))) := (do
  let output ← localOps.ratchet_execute_write_request request
  liftRust (core.option.Option.as_deref (alloc.vec.Vec.Insts.CoreOpsDerefDerefSlice U8) output) :
    RustT m (core.option.Option (Slice U8))).run

noncomputable def sealWork (request : record_effects.AeadSealRequest) :
    RustT m (core.option.Option (Slice U8 × Std.Array U8 16#usize)) := do
  let detached ← localOps.ratchet_execute_seal_request request
  let view ← liftRust (core.option.Option.as_ref detached)
  AdapterPublicWrapperRequestMonad.Option.map
    beaconcrypt_public_request.server.ProviderServerServer.build_registration_response.closure.Insts.CoreOpsFunctionFnOnceTupleSharedPairVecU8ArrayU816PairSharedSliceU8ArrayU816 view ()

noncomputable def sealLeaf (request : record_effects.AeadSealRequest) :
    m (RustM (core.option.Option (Slice U8 × Std.Array U8 16#usize))) := (sealWork request).run

theorem write (self : Server) (pending : registration.ServerRecordWrite) :
    (AdapterPublicServerBuildBody.write (m := m) self pending).run = (do
      let result ← RegistrationNativePlatformServerRecord.fromWrite writeLeaf pending
      afterRecord self result) := by
  unfold AdapterPublicServerBuildBody.write RegistrationNativePlatformServerRecord.fromWrite
  cases requested : pending.request with
  | fail error | div =>
    simp only [RustT.run_bind, RustT.run_liftRust, pure_bind,
      RegistrationNativePlatformServerRecord.continueWith, afterRecord]
  | ok request =>
    simp only [RustT.run_bind, RustT.run_liftRust, pure_bind,
      RegistrationNativePlatformServerRecord.continueWith, bind_assoc]
    unfold writeLeaf
    simp only [RustT.run_bind, bind_assoc]
    apply bind_congr
    intro written
    cases written with
    | fail error | div => simp only [pure_bind, afterRecord, bind_tc_fail, bind_tc_div]
    | ok output =>
      simp only [pure_bind, RustT.run_liftRust, pure_bind]
      cases borrowed : core.option.Option.as_deref (alloc.vec.Vec.Insts.CoreOpsDerefDerefSlice U8) output with
      | fail error | div => simp only [afterRecord, bind_tc_fail, bind_tc_div]
      | ok view =>
        simp only [checked, bind_tc_ok]
        cases resumed : pending.resume view with
        | fail error | div => rfl
        | ok answer => cases answer <;> rfl

theorem commitment (self : Server) (pending : registration.ServerRecordCommitment) :
    (AdapterPublicServerBuildBody.commit (m := m) self pending).run = (do
      let result ← RegistrationNativePlatformCommitment.fromCommitment
        (fun transcript => (children.commitmentHash transcript).run) writeLeaf pending
      afterRecord self result) := by
  unfold AdapterPublicServerBuildBody.commit RegistrationNativePlatformCommitment.fromCommitment
  cases requested : pending.transcript_mut with
  | fail error | div =>
      simp only [RustT.run_bind, RustT.run_liftRust, pure_bind,
        RegistrationNativePlatformServerRecord.continueWith, afterRecord]
  | ok selected =>
      rcases selected with ⟨transcript, back⟩
      simp only [RustT.run_bind, RustT.run_liftRust, pure_bind,
        RegistrationNativePlatformServerRecord.continueWith, bind_assoc]
      apply bind_congr
      intro hashed
      cases hashed with
      | fail error | div => simp only [pure_bind, RegistrationNativePlatformServerRecord.continueResult, afterRecord, bind_tc_fail, bind_tc_div]
      | ok hashed =>
          rcases hashed with ⟨digest, updated⟩
          simp only [checked, fused, write, bind_tc_ok]

theorem aead (self : Server) (pending : registration.ServerRecordAead) :
    (AdapterPublicServerBuildBody.sealRecord (m := m) self pending).run = (do
      let result ← RegistrationNativePlatformSourceRecord.fromAeadWithHash sealLeaf
        (fun transcript => (children.commitmentHash transcript).run) writeLeaf pending
      afterRecord self result) := by
  have grouped : AdapterPublicServerBuildBody.sealRecord (m := m) self pending = (do
      let request ← liftRust pending.request
      let borrowed ← sealWork request
      AdapterPublicServerBuildBody.checked self (pending.resume borrowed) (AdapterPublicServerBuildBody.commit self)) := by
    simp only [AdapterPublicServerBuildBody.sealRecord, sealWork, bind_assoc]
  rw [grouped]
  unfold RegistrationNativePlatformSourceRecord.fromAeadWithHash
  cases requested : pending.request with
  | fail error | div =>
      simp only [RustT.run_bind, RustT.run_liftRust, pure_bind,
        RegistrationNativePlatformServerRecord.continueWith, afterRecord]
  | ok request =>
      simp only [RustT.run_bind, RustT.run_liftRust, pure_bind,
        RegistrationNativePlatformServerRecord.continueWith, sealLeaf, bind_assoc]
      apply bind_congr
      intro sealed
      cases sealed with
      | fail error | div =>
          simp only [RegistrationNativePlatformServerRecord.continueResult,
            bind_tc_fail, bind_tc_div, pure_bind, afterRecord]
      | ok borrowed =>
          simp only [checked, bind_tc_ok, fused, commitment]

structure Kdf (m : Type → Type) where
  initial : ratchet.SymmetricRatchetKdfRequest → m (Std.Array U8 64#usize)
  ratchet : ratchet.SymmetricRatchetKdfRequest → m ratchet.RatchetKdfResponse

structure KdfContract (operations : Kdf m) : Prop where
  initial : ∀ request, (localOps.ratchet_initial_ratchet_hkdf request).run = RustM.ok <$> operations.initial request
  ratchet : ∀ request, (children.ratchetHkdf request).run = RustM.ok <$> operations.ratchet request

omit localOps containers children in
def recordOperations (operations : Kdf m) : QueryImpl RegistrationRecordPrimitives.Spec m
  | .initialKdf request => (fun bytes => core.option.Option.Some (⟨bytes⟩ : pqxdh.concrete.InitialRatchetKdfResponse)) <$> operations.initial request
  | .ratchetKdf request => core.option.Option.Some <$> operations.ratchet request
  | .rootKdf _ | .hash _ | .seal _ | .openAead _ | .write _ => pure .None

noncomputable def fromRatchet (self : Server) (pending : registration.ServerInitialSeal) : RustT m Reply := do
  let request ← liftRust pending.request
  let response ← children.ratchetHkdf request
  AdapterPublicServerBuildBody.checked self (pending.resume (.Some response)) (AdapterPublicServerBuildBody.sealRecord self)

theorem ratchet (operations : Kdf m) (contract : KdfContract operations)
    (self : Server) (pending : registration.ServerInitialSeal) :
    (fromRatchet (m := m) self pending).run = (do
      let result ← RegistrationNativePlatformSourceRecord.fromRatchetWithHash (recordOperations operations) sealLeaf
        (fun transcript => (children.commitmentHash transcript).run) writeLeaf pending
      afterRecord self result) := by
  unfold fromRatchet RegistrationNativePlatformSourceRecord.fromRatchetWithHash
  cases requested : pending.request with
  | fail error | div =>
    simp only [RustT.run_bind, RustT.run_liftRust, pure_bind,
      RegistrationNativePlatformServerRecord.continueWith, afterRecord]
  | ok request =>
    simp only [RustT.run_bind, RustT.run_liftRust, pure_bind,
      RegistrationNativePlatformServerRecord.continueWith, contract.ratchet,
      recordOperations, bind_map_left, bind_assoc]
    apply bind_congr
    intro response
    simp only [checked, fused, aead]

theorem record (operations : Kdf m) (contract : KdfContract operations)
    (self : Server) (pending : registration.ServerInitialKdf) :
    (AdapterPublicServerBuildBody.record (m := m) self pending).run = (do
      let result ← RegistrationNativePlatformSourceRecord.fromInitialWithHash (recordOperations operations) sealLeaf
        (fun transcript => (children.commitmentHash transcript).run) writeLeaf pending
      afterRecord self result) := by
  change (do let request ← liftRust pending.request
             let bytes ← localOps.ratchet_initial_ratchet_hkdf request
             let response ← liftRust (pqxdh.concrete.InitialRatchetKdfResponse.from_bytes bytes)
             AdapterPublicServerBuildBody.checked self (pending.resume (.Some response)) (fromRatchet self)).run = _
  unfold RegistrationNativePlatformSourceRecord.fromInitialWithHash
  cases requested : pending.request with
  | fail error | div =>
    simp only [RustT.run_bind, RustT.run_liftRust, pure_bind,
      RegistrationNativePlatformServerRecord.continueWith, afterRecord]
  | ok request =>
    simp only [RustT.run_bind, RustT.run_liftRust, pure_bind,
      RegistrationNativePlatformServerRecord.continueWith, contract.initial,
      recordOperations, bind_map_left, bind_assoc]
    apply bind_congr
    intro bytes
    simp only [pqxdh.concrete.InitialRatchetKdfResponse.from_bytes,
      checked, fused, ratchet operations contract]
end BeaconcryptCore.Refinement.AdapterPublicServerRecord

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicServerRecord.checked' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicServerRecord.checked

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicServerRecord.write' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicServerRecord.write

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicServerRecord.commitment' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicServerRecord.commitment

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicServerRecord.aead' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicServerRecord.aead

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicServerRecord.ratchet' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicServerRecord.ratchet

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicServerRecord.record' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicServerRecord.record
