-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.AdapterPublicFinishRecord
/-! Individual native first-record operations compose with the actual extracted public first-open/install suffix. Equality retains all shared monadic state and optional failures; the selected HKDF leaf is functional and normal. The recursive proof follows actual Core progress, so no whole controller correspondence or security conclusion is a premise. -/
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Refinement.AdapterPublicFinishInterpret
open AdapterPublicWrapperRustT (RustT)
open AdapterPublicWrapperRequestMonad
open BeaconcryptCore.Computational
open AdapterPublicFinishRecord (Primitives handler)
variable {m : Type → Type} [Monad m] [LawfulMonad m]

/-- Individual native record operations, including their complete shared-monad effects. -/
structure Leaves (primitive : Primitives m) (native : QueryImpl RegistrationRecordPrimitives.Spec m) : Prop where
  initial : ∀ request, native (.initialKdf request) = (fun bytes => core.option.Option.Some (⟨bytes⟩ : pqxdh.concrete.InitialRatchetKdfResponse)) <$> primitive.initial request
  kdf : ∀ request, native (.ratchetKdf request) = core.option.Option.Some <$> primitive.kdf request
  hash : ∀ request, native (.hash request) = Prod.fst <$> primitive.hash request
  aead : ∀ request, native (.openAead request) = AdapterPublicInitPublication.borrowed <$> primitive.aead request

omit [LawfulMonad m] in
private theorem continue_equal {Input : Type} (action : RustM Input)
    (left right : Input → OracleComp RegistrationRecordPrimitives.Spec (RustM RegistrationBeaconRecordExecutor.Result))
    (primitive : Primitives m) (native : QueryImpl RegistrationRecordPrimitives.Spec m)
    (same : ∀ value, simulateQ (handler primitive) (left value) = simulateQ native (right value)) :
    simulateQ (handler primitive) (RegistrationBeaconRecordExecutor.continueWith action left) =
      simulateQ native (RegistrationBeaconRecordExecutor.continueWith action right) := by
  cases action with
  | fail error | div => rfl
  | ok value => exact same value

theorem program (primitive : Primitives m) (native : QueryImpl RegistrationRecordPrimitives.Spec m)
    (leaves : Leaves primitive native) (phase : registration.BeaconInitialOpen) :
    simulateQ (handler primitive) (RegistrationBeaconRecordExecutor.program phase) =
      simulateQ native (RegistrationBeaconRecordExecutor.program phase) := by
  cases phase with
  | KdfRequested pending =>
      rw [RegistrationBeaconRecordExecutor.program.eq_def]
      apply continue_equal
      intro request
      simp only [simulateQ_bind, simulateQ_spec_query, handler, ← leaves.kdf]
      apply bind_congr
      intro response
      cases resumed : pending.resume response with
      | fail error | div => rfl
      | ok answer => cases answer with
        | Err control => rfl
        | Ok next => exact program primitive native leaves next
  | CommitmentRequested pending =>
      rw [RegistrationBeaconRecordExecutor.program.eq_def]
      apply continue_equal
      intro transcript
      simp only [simulateQ_bind, simulateQ_spec_query, handler, ← leaves.hash]
      apply bind_congr
      intro digest
      apply continue_equal
      intro supplied
      cases resumed : pending.resume (RegistrationBeaconRecordExecutor.commitmentMatches digest supplied) with
      | fail error | div => rfl
      | ok answer => cases answer with
        | Err control => rfl
        | Ok next => exact program primitive native leaves next
  | AeadRequested pending =>
      rw [RegistrationBeaconRecordExecutor.program.eq_def]
      apply continue_equal
      intro request
      cases request with
      | none => rfl
      | some request => simp only [simulateQ_bind, simulateQ_spec_query, handler, ← leaves.aead, simulateQ_pure]
termination_by RegistrationBeaconRecordExecutor.rank phase
decreasing_by
  · exact RegistrationBeaconRecordExecutor.kdf_rank pending response next resumed
  · exact RegistrationBeaconRecordExecutor.commitment_rank pending _ next resumed

theorem initial_program (primitive : Primitives m) (native : QueryImpl RegistrationRecordPrimitives.Spec m)
    (leaves : Leaves primitive native) (agreement : agreement.BeaconAgreement) :
    simulateQ (handler primitive) (RegistrationBeaconRecordExecutor.begin agreement) =
      simulateQ native (RegistrationBeaconRecordExecutor.begin agreement) := by
  unfold RegistrationBeaconRecordExecutor.begin
  apply continue_equal
  intro pending
  unfold RegistrationBeaconRecordExecutor.fromInitial
  apply continue_equal
  intro request
  simp only [simulateQ_bind, simulateQ_spec_query, handler, ← leaves.initial]
  apply bind_congr
  intro response
  cases resumed : pending.resume response with
  | fail error | div => rfl
  | ok answer => cases answer with
    | Err control => rfl
    | Ok next => exact program primitive native leaves next

variable [material : PublicWrapperPlatform.Material] [platform : PublicWrapperPlatform.Platform]
variable [ed : AdapterInitEdPrimitive.Operations]
variable [localOps : LocalOperations (RustT m)] [children : ChildOperations (RustT m)]

/-- The literal source initial HKDF and first-open/install suffix has the native execution under individual primitive contracts. -/
theorem source (primitive : Primitives m) (native : QueryImpl RegistrationRecordPrimitives.Spec m)
    (sourceLeaves : AdapterPublicFinishRecord.Contract primitive) (nativeLeaves : Leaves primitive native)
    (initialLeaf : ∀ request, (localOps.ratchet_initial_ratchet_hkdf request).run = RustM.ok <$> primitive.initial request)
    (self : beaconcrypt_public_wrapper.beacon.Beacon) (agreement : agreement.BeaconAgreement) :
    (AdapterPublicFinishBody.beginOpen (m := m) self agreement).run =
      (fun answer => AdapterPublicFinishRecord.wrap self (AdapterPublicFinishRecord.result self.identity_key_kid answer)) <$>
        simulateQ native (RegistrationBeaconRecordExecutor.begin agreement) := by
  rw [AdapterPublicFinishRecord.initial primitive sourceLeaves initialLeaf, initial_program primitive native nativeLeaves]
end BeaconcryptCore.Refinement.AdapterPublicFinishInterpret

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicFinishInterpret.program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicFinishInterpret.program

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicFinishInterpret.initial_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicFinishInterpret.initial_program

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicFinishInterpret.source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicFinishInterpret.source
