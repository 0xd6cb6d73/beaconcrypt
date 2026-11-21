-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPrivateRecordPrefix
import BeaconcryptCore.Computational.RegistrationNativePlatformSeedPublic
/-! An explicit post-KDF source descriptor contains the source state, seal context, public send control and material44, with no root request or advanced kernel field. The private interpreter retains the actual kernel separately. This internal protocol descriptor is never an external allocator request; allocator requests remain public site/capacity data. -/
open OracleComp OracleSpec CoreModels Aeneas beaconcrypt_core
open Aeneas.Std hiding namespace core alloc
open RustM ratchet ratchet.concrete
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformRecordDescriptor

structure Descriptor where
  state : registration.ServerRecordState
  context : record_effects.SealFrameContext
  logical : ratchet.control.SendKey
  sequence : U64
  material : ratchet.RatchetMaterial

def describe (pending : registration.ServerRecordAead) : Descriptor :=
  ⟨pending.state, pending.pending.seal.context, pending.pending.seal.logical,
    pending.pending.seal.sequence, pending.pending.seal.material⟩

def atKernel (descriptor : Descriptor) (kernel : ConcreteRatchetKernel) : registration.ServerRecordAead :=
  ⟨descriptor.state, ⟨⟨kernel, descriptor.context, descriptor.logical, descriptor.sequence, descriptor.material⟩⟩⟩

private theorem describe_restore (pending : registration.ServerRecordAead) (placeholder : ConcreteRatchetKernel) :
    RegistrationKernelErasure.selected pending.pending.seal.advanced (atKernel (describe pending) placeholder) = pending := rfl

private noncomputable def placeholder : ConcreteRatchetKernel := PqxdhRecordLiftWorld.kernel .server
  (RegistrationBoundKeySchedule.zero, RegistrationBoundKeySchedule.zero)

def split (pending : registration.ServerRecordAead) : Descriptor × ConcreteRatchetKernel :=
  (describe pending, pending.pending.seal.advanced)

def erase (stage : RustM (core.result.Result (Descriptor × ConcreteRatchetKernel) pqxdh.ServerState)) :
    RustM (core.result.Result Descriptor pqxdh.ServerState) :=
  RegistrationPublicationKernelErasure.mapOk Prod.fst <$> stage

def restore (stage : RustM (core.result.Result (Descriptor × ConcreteRatchetKernel) pqxdh.ServerState))
    (result : RustM RegistrationServerRecordExecutor.Result) : RustM RegistrationServerRecordExecutor.Result :=
  match stage with
  | .ok (.Ok selected) => RegistrationKernelErasure.mapResult selected.2 result
  | _ => result

variable {m : Type → Type} [Monad m] [LawfulMonad m]

def privatePrefix (record : QueryImpl RegistrationRecordPrimitives.Spec m) (initial : registration.ServerInitialKdf) :
    m (RustM (core.result.Result (Descriptor × ConcreteRatchetKernel) pqxdh.ServerState)) :=
  (fun stage => RegistrationPublicationKernelErasure.mapOk split <$> stage) <$>
    RegistrationNativePlatformPrivateRecordPrefix.privatePrefix record initial

noncomputable def suffix
    (sealing : record_effects.AeadSealRequest → m (RustM (core.option.Option (Slice U8 × Std.Array U8 16#usize))))
    (hash : commitment.CommitmentTranscript → m RegistrationNativePlatformCommitment.HashReply)
    (write : record_effects.RecordWriteRequest → m (RustM (core.option.Option (Slice U8))))
    (descriptor : Descriptor) : m (RustM RegistrationServerRecordExecutor.Result) :=
  RegistrationNativePlatformSourceRecord.fromAeadWithHash sealing hash write (atKernel descriptor placeholder)

private theorem rust_map_fail {A B : Type} (f : A → B) (error : Error) :
    f <$> (RustM.fail error : RustM A) = RustM.fail error := rfl
private theorem rust_map_div {A B : Type} (f : A → B) : f <$> (RustM.div : RustM A) = RustM.div := rfl

/-- The entire actual source KDF/seal/hash/write computation exposes only its internal root-free descriptor to the suffix and retains its generated whole kernel in the private prefix. -/
theorem source (record : QueryImpl RegistrationRecordPrimitives.Spec m)
    (sealing : record_effects.AeadSealRequest → m (RustM (core.option.Option (Slice U8 × Std.Array U8 16#usize))))
    (hash : commitment.CommitmentTranscript → m RegistrationNativePlatformCommitment.HashReply)
    (write : record_effects.RecordWriteRequest → m (RustM (core.option.Option (Slice U8))))
    (initial : registration.ServerInitialKdf) :
    RegistrationNativePlatformSourceRecord.fromInitialWithHash record sealing hash write initial = (do
      let stage ← privatePrefix record initial
      restore stage <$> RegistrationNativePlatformServerRecord.continueResult (erase stage) (suffix sealing hash write)) := by
  rw [RegistrationNativePlatformPrivateRecordPrefix.source]
  unfold privatePrefix
  rw [bind_map_left]
  apply bind_congr
  intro stage
  cases stage with
  | fail error =>
    simp only [rust_map_fail, erase, RegistrationNativePlatformServerRecord.continueResult, map_pure]
    rfl
  | div =>
    simp only [rust_map_div, erase, RegistrationNativePlatformServerRecord.continueResult, map_pure]
    rfl
  | ok answer => cases answer with
    | Err previous =>
      simp only [RawCtxMaterialInterpretation.rust_map_ok, RegistrationPublicationKernelErasure.mapOk, erase,
        RegistrationNativePlatformServerRecord.continueResult, map_pure]
      rfl
    | Ok pending =>
      change RegistrationNativePlatformSourceRecord.fromAeadWithHash sealing hash write pending =
        RegistrationKernelErasure.mapResult pending.pending.seal.advanced <$>
          RegistrationNativePlatformSourceRecord.fromAeadWithHash sealing hash write (atKernel (describe pending) placeholder)
      have same := RegistrationNativePlatformSeedPublic.fromAead pending.pending.seal.advanced sealing hash write
        (atKernel (describe pending) placeholder)
      rw [describe_restore] at same
      exact same

def outputDescriptor (initial : RegistrationBoundKeySchedule.PublicInitial) (output : PqxdhServerAuthKeySchedule.Output) :
    RustM (core.result.Result Descriptor pqxdh.ServerState) :=
  RegistrationPublicationKernelErasure.mapOk describe <$>
    RegistrationSeedErasure.selected (RegistrationBoundKeySchedule.restore initial)
      (RawCtxSelectedInitialConstructor.response64 (RegistrationBoundKeySchedule.zero ++ output.2))
      (RawCtxKdfRequestTable.fullResponse output.1)

/-- The actual source descriptor at a supplied 108-byte reply depends only on material44 and the public initial data, never either private generated chain. -/
theorem material (initial : RegistrationBoundKeySchedule.PublicInitial) (known : PqxdhDeploymentHiddenLayout.Material)
    (seed : PqxdhRecordLiftSeed.Seed) :
    outputDescriptor initial (PqxdhDeploymentHiddenLayout.joinOutput known seed) =
      outputDescriptor initial (PqxdhDeploymentHiddenLayout.joinOutput known
        (RegistrationBoundKeySchedule.zero, RegistrationBoundKeySchedule.zero)) := by
  let fixed : PqxdhRecordLiftSeed.Seed := (RegistrationBoundKeySchedule.zero, RegistrationBoundKeySchedule.zero)
  obtain ⟨selected, actual, _kernel⟩ := RegistrationBoundKeySchedule.factored_kernel initial known fixed
  have mapped := RegistrationSeedPublic.selected_map (RegistrationBoundKeySchedule.restore initial)
    (PqxdhRootTableInitialization.rootArray RegistrationBoundKeySchedule.zero) rfl known fixed seed
    (PqxdhRecordLiftWorld.kernel .server seed) (PqxdhRecordLiftWorld.kernel_exact .server seed)
  rw [actual, RawCtxMaterialInterpretation.rust_map_ok, RegistrationPublicationKernelErasure.mapOk] at mapped
  simp only [outputDescriptor, PqxdhDeploymentHiddenLayout.joinOutput] at actual mapped ⊢
  simp only [fixed] at actual
  rw [actual, mapped]
  rfl


end BeaconcryptCore.Computational.RegistrationNativePlatformRecordDescriptor

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordDescriptor.source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordDescriptor.source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordDescriptor.material' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordDescriptor.material
