-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformBoundCompilerSeed
import BeaconcryptCore.Computational.RegistrationNativePlatformMaterializedEffects
import BeaconcryptCore.Computational.RegistrationNativeG3MaterializedFrontend
/-! The actual corrected dynamic Server supplied-material stage has the same source as its opaque-slot stage under fixed private-seed materialization. All source publication, allocator and writer outcomes remain literal. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformMaterializedServer
open RegistrationNativePlatformEffectCompiler (Spec)
open RegistrationNativePlatformBoundCompiler (PublicState compile target program liftPlatform)
variable {n : Nat} {E Platform : Type}
variable [primitive : BeaconcryptCore.Refinement.AdapterSealPrimitive.Operations]
variable (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (BeaconcryptCore.Refinement.AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))

open RegistrationNativePlatformMaterializedEffects (realize effect)
open RegistrationNativePlatformPairedServerCompiler (known forward)

private theorem effects (initial : RegistrationBoundKeySchedule.PublicInitial)
    (output : PqxdhServerAuthKeySchedule.Output) {A : Type}
    (work : OracleComp (PqxdhRecordLiftInterface.EnvEffects n) A)
    (before : PublicState Platform) :
    (simulateQ (RegistrationNativePlatformPairedServerCompiler.target source view failure allocation erased helper sign writer initial output)
      (simulateQ forward work)).run before =
      (fun value => (value, before)) <$> simulateQ effect work := by
  rw [← QueryImpl.simulateQ_compose]
  have same : RegistrationNativePlatformPairedServerCompiler.target source view failure allocation erased helper sign writer initial output ∘ₛ forward =
      (effect (n := n)).liftTarget (StateT (PublicState Platform) (OracleComp (Spec n))) := by
    funext query
    rfl
  rw [same, simulateQ_liftTarget, StateT.run_monadLift, monadLift_self, bind_pure_comp]
/-- The concrete corrected Server source stage runs its actual dynamic publication with a dummy private seed in the opaque-slot branch; fixed-seed World materialization recovers the full known stage without changing any public or platform outcome. -/
theorem stage (control : pqxdh.ServerState) (slot : PqxdhRecordLiftInterface.Slot n)
    (initial : RegistrationBoundKeySchedule.PublicInitial) (material : PqxdhDeploymentHiddenLayout.Material)
    (seeds : RegistrationNativeG3AuditedWorld.Seeds n) (before : PublicState Platform) :
    (simulateQ (RegistrationNativePlatformPairedServerCompiler.target source view failure allocation erased helper sign writer initial
      (PqxdhDeploymentHiddenLayout.joinOutput material (seeds slot))) (known control)).run before =
      simulateQ (realize seeds)
        ((simulateQ (RegistrationNativePlatformPairedServerCompiler.target source view failure allocation erased helper sign writer initial
          (PqxdhDeploymentHiddenLayout.joinOutput material RegistrationBoundPublication.fixedSeed)) (RegistrationNativePlatformPairedServerCompiler.hidden control slot)).run before) := by
  simp only [known, RegistrationNativePlatformPairedServerCompiler.hidden, simulateQ_bind, simulateQ_spec_query,
    RegistrationNativePlatformPairedServerCompiler.target, StateT.run_bind]
  rw [RegistrationNativePlatformBoundCompilerSeed.split (n := n) source view failure allocation erased helper sign writer initial material (seeds slot)]
  simp only [StateT.run_map, bind_map_left]
  rw [RegistrationNativePlatformMaterializedEffects.state_free seeds _
    (RegistrationNativePlatformPairedPublicationFree.compile source view failure allocation erased helper sign writer initial _) before]
  apply bind_congr
  intro published
  rw [effects, effects]
  simp only [simulateQ_map]
  exact congrArg (Functor.map (fun value => (value, published.2)))
    (RegistrationNativePlatformMaterializedEffects.after_replaced control slot seeds published.1)
omit primitive in
private theorem known_after_free (control : pqxdh.ServerState)
    (seeds : RegistrationNativeG3AuditedWorld.Seeds n)
    (published : RustM (RegistrationWorldServerPublication.Result (alloc.vec.Vec U8))) :
    simulateQ (realize seeds) (simulateQ effect (RegistrationNativePairedServerService.knownAfter control published)) =
      simulateQ effect (RegistrationNativePairedServerService.knownAfter control published) := by
  cases published with
  | fail error | div => rfl
  | ok value => cases value with
    | Err previous => rfl
    | Ok completed =>
      change simulateQ (realize seeds) (simulateQ effect (RegistrationNativePairedServerService.knownInstall control completed)) =
        simulateQ effect (RegistrationNativePairedServerService.knownInstall control completed)
      obtain ⟨result, prepared, retained⟩ := BeaconcryptCore.Refinement.PeerOwnership.peer_insert_begin_retains control completed
      cases result with
      | Err previous =>
        simp only [RegistrationNativePairedServerService.knownInstall, prepared]
        rfl
      | Ok pending =>
        rw [RegistrationNativePairedServerService.knownInstall_native control completed pending prepared]
        rfl

private theorem known_free (control : pqxdh.ServerState) (initial : RegistrationBoundKeySchedule.PublicInitial)
    (output : PqxdhServerAuthKeySchedule.Output)
    (seeds : RegistrationNativeG3AuditedWorld.Seeds n) (before : PublicState Platform) :
    (simulateQ (RegistrationNativePlatformPairedServerCompiler.target source view failure allocation erased helper sign writer initial output)
      (known control)).run before =
      simulateQ (realize seeds)
        ((simulateQ (RegistrationNativePlatformPairedServerCompiler.target source view failure allocation erased helper sign writer initial output)
          (known control)).run before) := by
  simp only [known, simulateQ_bind, simulateQ_spec_query,
    RegistrationNativePlatformPairedServerCompiler.target, StateT.run_bind]
  rw [RegistrationNativePlatformMaterializedEffects.state_free seeds _
    (RegistrationNativePlatformPairedPublicationFree.compile source view failure allocation erased helper sign writer initial _) before]
  apply bind_congr
  intro published
  rw [effects]
  simp only [simulateQ_map, known_after_free]

/-- Each literal corrected Server branch compares full known material with its opaque material44/slot continuation on the same public receipt/platform state. The fixed private seed table occurs only in the outer installation translation. -/
theorem branch (control : pqxdh.ServerState) (initial : RegistrationBoundKeySchedule.PublicInitial)
    (choice : RegistrationNativePairedChoice.Choice n) (seeds : RegistrationNativeG3AuditedWorld.Seeds n)
    (before : PublicState Platform) :
    (RegistrationNativePlatformServerRestrictedService.branch source view failure allocation erased helper sign writer control initial
      (RegistrationNativeG3MaterializedFrontend.materialize seeds choice)).run before =
      simulateQ (realize seeds)
        ((RegistrationNativePlatformServerRestrictedService.branch source view failure allocation erased helper sign writer control initial choice).run before) := by
  cases choice with
  | known output => exact known_free source view failure allocation erased helper sign writer control initial output seeds before
  | hidden reference => exact stage source view failure allocation erased helper sign writer control reference.slot initial reference.material seeds before
end BeaconcryptCore.Computational.RegistrationNativePlatformMaterializedServer

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformMaterializedServer.stage' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformMaterializedServer.stage

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformMaterializedServer.branch' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformMaterializedServer.branch
