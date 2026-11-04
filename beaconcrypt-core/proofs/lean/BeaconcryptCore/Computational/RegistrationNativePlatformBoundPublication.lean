-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformSeedPublic
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicationKernel
import BeaconcryptCore.Computational.RegistrationBoundPublication
/-! The actual source continuation after the two key-schedule replies factors into position-one material44 and a private whole kernel. All source allocation, enclosing failure/divergence, mutable commitment, response signing and stateful source encoding remain in the same monad. The thin continuation receives no private seed. Initial KDF execution and restricted frontend restoration remain separate composition steps. -/
open OracleComp OracleSpec CoreModels Aeneas beaconcrypt_core
open Aeneas.Std hiding namespace core alloc
open RustM ratchet ratchet.concrete
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformBoundPublication
open RegistrationBoundKeySchedule (PublicInitial restore zero)
variable {Encoded : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
variable (sealing : record_effects.AeadSealRequest → m (RustM (core.option.Option (Slice U8 × Std.Array U8 16#usize))))
variable (hash : commitment.CommitmentTranscript → m RegistrationNativePlatformCommitment.HashReply)
variable (write : record_effects.RecordWriteRequest → m (RustM (core.option.Option (Slice U8))))
variable (sign : QueryImpl RegistrationSigningShared.Spec m)
variable (encode : registration.SignedResponseView → m (RustM (core.option.Option Encoded)))

def record (initial : PublicInitial) (output : PqxdhServerAuthKeySchedule.Output) : m (RustM RegistrationServerRecordExecutor.Result) :=
  RegistrationNativePlatformServerRecord.continueResult
    (RegistrationSeedErasure.selected (restore initial)
      (RawCtxSelectedInitialConstructor.response64 (zero ++ output.2))
      (RawCtxKdfRequestTable.fullResponse output.1))
    (RegistrationNativePlatformSourceRecord.fromAeadWithHash sealing hash write)

def supplied (initial : registration.ServerInitialKdf) (left right : PqxdhSecretInputKdf.RootOutput)
    (output : PqxdhFullSecretInputKdf.FullOutput) : m (RustM RegistrationServerRecordExecutor.Result) :=
  RegistrationNativePlatformServerRecord.continueResult
    (RegistrationSeedErasure.selected initial (RawCtxSelectedInitialConstructor.response64 (left ++ right))
      (RawCtxKdfRequestTable.fullResponse output))
    (RegistrationNativePlatformSourceRecord.fromAeadWithHash sealing hash write)

omit [LawfulMonad m] in
/-- Actual admission removes the root request and unused initializer coordinate from the stateful source continuation. -/
theorem supplied_factored (control : pqxdh.ServerState) (current : session.ServerAuthenticationPin)
    (availability : pqxdh.KeyIdAvailability) (agreement : agreement.ServerAgreement) (application : Slice U8)
    (initial : registration.ServerInitialKdf)
    (actual : registration.begin_server_completion control current availability agreement application = .ok (.Ok initial))
    (left right : PqxdhSecretInputKdf.RootOutput) (output : PqxdhFullSecretInputKdf.FullOutput) :
    supplied sealing hash write initial left right output =
      record sealing hash write (RegistrationBoundKeySchedule.publicInitial initial) (output, right) := by
  unfold supplied record
  rw [RegistrationSeedErasure.server_left_unused control current availability agreement application initial actual left zero right output]
  rw [RegistrationBoundKeySchedule.root_unused initial agreement.root.bytes
    (RegistrationSeedKernel.server_pending control current availability agreement application initial actual)]

/-- Actual source raw-record execution changes only its retained private kernel when material44 stays fixed. -/
theorem record_map (initial : PublicInitial) (material : PqxdhDeploymentHiddenLayout.Material)
    (first second : PqxdhRecordLiftSeed.Seed) (kernel : ConcreteRatchetKernel)
    (kernelRun : PqxdhRecordLiftSeed.serverKernel second = .ok kernel) :
    record sealing hash write initial (PqxdhDeploymentHiddenLayout.joinOutput material second) =
      RegistrationKernelErasure.mapResult kernel <$>
        record sealing hash write initial (PqxdhDeploymentHiddenLayout.joinOutput material first) := by
  obtain ⟨selected, actual, _kernel⟩ := RegistrationBoundKeySchedule.factored_kernel initial material first
  have mapped := RegistrationSeedPublic.selected_map (restore initial)
    (PqxdhRootTableInitialization.rootArray zero) rfl material first second kernel kernelRun
  rw [actual, RawCtxMaterialInterpretation.rust_map_ok, RegistrationPublicationKernelErasure.mapOk] at mapped
  simp only [record, PqxdhDeploymentHiddenLayout.joinOutput] at actual mapped ⊢
  rw [actual, mapped]
  simp only [RegistrationNativePlatformServerRecord.continueResult]
  exact RegistrationNativePlatformSeedPublic.fromAead kernel sealing hash write selected

def after (completed : RustM RegistrationServerRecordExecutor.Result) : m (RustM (RegistrationWorldServerPublication.Result Encoded)) :=
  RegistrationNativePlatformServerPublication.continueResult completed
    (RegistrationNativePlatformServerPublication.program sign encode)

def program (initial : PublicInitial) (output : PqxdhServerAuthKeySchedule.Output) :
    m (RustM (RegistrationWorldServerPublication.Result Encoded)) := do
  let completed ← record sealing hash write initial output
  after sign encode completed

private theorem after_map (kernel : ConcreteRatchetKernel) (completed : RustM RegistrationServerRecordExecutor.Result) :
    after sign encode (RegistrationKernelErasure.mapResult kernel completed) =
      RegistrationPublicationKernelErasure.result kernel <$> after sign encode completed := by
  cases completed with
  | fail error => simp only [after, RegistrationNativePlatformServerPublication.continueResult, map_pure]; rfl
  | div => simp only [after, RegistrationNativePlatformServerPublication.continueResult, map_pure]; rfl
  | ok value => cases value with
    | Err previous => simp only [after, RegistrationNativePlatformServerPublication.continueResult, map_pure]; rfl
    | Ok pending => exact RegistrationNativePlatformPublicationKernel.program_map kernel sign encode pending

/-- Complete actual record/hash/sign/stateful-encoding execution retains every public effect under private seed replacement. -/
theorem program_map (initial : PublicInitial) (material : PqxdhDeploymentHiddenLayout.Material)
    (first second : PqxdhRecordLiftSeed.Seed) (kernel : ConcreteRatchetKernel)
    (kernelRun : PqxdhRecordLiftSeed.serverKernel second = .ok kernel) :
    program sealing hash write sign encode initial (PqxdhDeploymentHiddenLayout.joinOutput material second) =
      RegistrationPublicationKernelErasure.result kernel <$>
        program sealing hash write sign encode initial (PqxdhDeploymentHiddenLayout.joinOutput material first) := by
  unfold program
  rw [record_map sealing hash write initial material first second kernel kernelRun]
  simp only [bind_map_left, map_bind]
  apply bind_congr
  intro completed
  exact after_map sign encode kernel completed

def thin (initial : PublicInitial) (material : PqxdhDeploymentHiddenLayout.Material) :
    m (RustM (RegistrationWorldServerPublication.Result Encoded)) :=
  program sealing hash write sign encode initial
    (PqxdhDeploymentHiddenLayout.joinOutput material RegistrationBoundPublication.fixedSeed)

/-- The source thin continuation receives material44 only; the actual private World supplies its whole generated kernel. -/
theorem split (initial : PublicInitial) (material : PqxdhDeploymentHiddenLayout.Material) (seed : PqxdhRecordLiftSeed.Seed) :
    program sealing hash write sign encode initial (PqxdhDeploymentHiddenLayout.joinOutput material seed) =
      RegistrationPublicationKernelErasure.result (PqxdhRecordLiftWorld.kernel .server seed) <$>
        thin sealing hash write sign encode initial material :=
  program_map sealing hash write sign encode initial material RegistrationBoundPublication.fixedSeed seed _
    (PqxdhRecordLiftWorld.kernel_exact .server seed)

/-- The complete public source reply and all actual platform effects are independent of the private seed at fixed material44. -/
theorem public_program (initial : PublicInitial) (material : PqxdhDeploymentHiddenLayout.Material) (seed : PqxdhRecordLiftSeed.Seed) :
    RegistrationBoundPublication.publicResult <$>
      program sealing hash write sign encode initial (PqxdhDeploymentHiddenLayout.joinOutput material seed) =
      RegistrationBoundPublication.publicResult <$> thin sealing hash write sign encode initial material := by
  rw [split, Functor.map_map]
  apply congrArg (fun observer => observer <$> thin sealing hash write sign encode initial material)
  funext value
  cases value with
  | fail error => rfl
  | div => rfl
  | ok value => cases value <;> rfl


end BeaconcryptCore.Computational.RegistrationNativePlatformBoundPublication

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformBoundPublication.supplied_factored' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformBoundPublication.supplied_factored

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformBoundPublication.record_map' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformBoundPublication.record_map

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformBoundPublication.program_map' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformBoundPublication.program_map

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformBoundPublication.split' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformBoundPublication.split

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformBoundPublication.public_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformBoundPublication.public_program
