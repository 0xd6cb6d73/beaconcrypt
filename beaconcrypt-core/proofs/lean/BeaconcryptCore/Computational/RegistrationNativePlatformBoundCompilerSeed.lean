-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPairedPublicationFree
/-! The actual free first-record/publication compiler retains exactly its public requests and common platform state under private seed replacement. This supplies the concrete known-material to opaque-slot source join; the private kernel is changed only in its internal returned capability. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformBoundCompilerSeed
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

omit primitive in
private theorem publication (pending : registration.ServerResponseHash) :
    simulateQ (RegistrationNativePlatformPublicationCompiler.target (n := n) source (fun _ => none) sign writer)
      (RegistrationNativePlatformPublicationCompiler.program pending) =
      RegistrationNativePlatformServerPublication.program
        (RegistrationNativePlatformSigningCompiler.signing source (fun _ => none) sign)
        (RegistrationNativePlatformPublicationCompiler.encoding writer) pending := by
  unfold RegistrationNativePlatformPublicationCompiler.program
  rw [RegistrationNativePlatformServerPublication.program_interpret]
  simp only [RegistrationNativePlatformPublicationCompiler.signLift,
    RegistrationNativePlatformPublicationCompiler.encodeLift, simulateQ_spec_query,
    RegistrationNativePlatformPublicationCompiler.target]

omit primitive in
private theorem lift_map {A B : Type} (change : A → B)
    (work : StateT Platform (OracleComp (Spec n)) A) :
    liftPlatform (change <$> work) = change <$> liftPlatform work := by
  funext before
  rw [show (change <$> liftPlatform work) before =
      Prod.map change id <$> (liftPlatform work).run before from StateT.run_map change (liftPlatform work) before]
  change (fun result => (result.1, (before.1, result.2))) <$> (change <$> work).run before.2 =
    Prod.map change id <$> ((fun result => (result.1, (before.1, result.2))) <$> work.run before.2)
  rw [StateT.run_map]
  simp only [Functor.map_map]
  rfl

private theorem record_map (initial : RegistrationBoundKeySchedule.PublicInitial)
    (material : PqxdhDeploymentHiddenLayout.Material)
    (first second : PqxdhRecordLiftSeed.Seed) (kernel : ConcreteRatchetKernel)
    (kernelRun : PqxdhRecordLiftSeed.serverKernel second = .ok kernel) :
    RegistrationNativePlatformRecordCompiler.record (n := n) source view failure allocation erased helper initial
      (PqxdhDeploymentHiddenLayout.joinOutput material second) =
      RegistrationKernelErasure.mapResult kernel <$>
        RegistrationNativePlatformRecordCompiler.record source view failure allocation erased helper initial
          (PqxdhDeploymentHiddenLayout.joinOutput material first) := by
  exact RegistrationNativePlatformBoundPublication.record_map _ _ _ initial material first second kernel kernelRun

/-- The literal compiler changes only its internal returned kernel when its selected seed changes, retaining every failed source allocation/hash/sign/writer prefix and common platform poststate. -/
theorem program_map (initial : RegistrationBoundKeySchedule.PublicInitial)
    (material : PqxdhDeploymentHiddenLayout.Material)
    (first second : PqxdhRecordLiftSeed.Seed) (kernel : ConcreteRatchetKernel)
    (kernelRun : PqxdhRecordLiftSeed.serverKernel second = .ok kernel) :
    compile (n := n) source view failure allocation erased helper sign writer initial
      (PqxdhDeploymentHiddenLayout.joinOutput material second) =
      RegistrationPublicationKernelErasure.result kernel <$>
        compile source view failure allocation erased helper sign writer initial
          (PqxdhDeploymentHiddenLayout.joinOutput material first) := by
  unfold compile program
  simp only [simulateQ_bind, simulateQ_spec_query, target]
  rw [record_map source view failure allocation erased helper initial material first second kernel kernelRun]
  rw [lift_map, bind_map_left, map_bind]
  apply bind_congr
  intro completed
  cases completed with
  | fail error | div => rfl
  | ok value => cases value with
    | Err previous => rfl
    | Ok pending =>
      simp only [RegistrationKernelErasure.mapResult, RawCtxMaterialInterpretation.rust_map_ok, RegistrationKernelErasure.mapCore,
        RegistrationNativePlatformServerPublication.continueResult, simulateQ_spec_query, target]
      rw [publication, publication]
      exact RegistrationNativePlatformPublicationKernel.program_map kernel _ _ pending
/-- The actual compiler can execute with a fixed dummy seed and retain the chosen canonical kernel privately; public requests and every platform outcome remain identical. -/
theorem split (initial : RegistrationBoundKeySchedule.PublicInitial)
    (material : PqxdhDeploymentHiddenLayout.Material) (seed : PqxdhRecordLiftSeed.Seed) :
    compile (n := n) source view failure allocation erased helper sign writer initial
      (PqxdhDeploymentHiddenLayout.joinOutput material seed) =
      RegistrationPublicationKernelErasure.result (PqxdhRecordLiftWorld.kernel .server seed) <$>
        compile source view failure allocation erased helper sign writer initial
          (PqxdhDeploymentHiddenLayout.joinOutput material RegistrationBoundPublication.fixedSeed) :=
  program_map source view failure allocation erased helper sign writer initial material
    RegistrationBoundPublication.fixedSeed seed _ (PqxdhRecordLiftWorld.kernel_exact .server seed)
end BeaconcryptCore.Computational.RegistrationNativePlatformBoundCompilerSeed

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformBoundCompilerSeed.program_map' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformBoundCompilerSeed.program_map

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformBoundCompilerSeed.split' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformBoundCompilerSeed.split
