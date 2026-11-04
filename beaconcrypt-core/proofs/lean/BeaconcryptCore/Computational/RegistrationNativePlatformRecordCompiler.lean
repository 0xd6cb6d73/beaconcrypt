-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformEffectCompiler
import BeaconcryptCore.Computational.RegistrationNativePlatformSourceRecordLower
/-! The actual first-record service has a concrete free restricted client. Its public state is only the common platform state; World access is a typed hash request and public draws have their own oracle branch. Local AEAD, actual source writing and dynamic allocation run as the proved World-free source computations. Concrete allocation privacy and trusted source-codec instantiation remain explicit at the enclosing client. -/
open OracleComp OracleSpec CoreModels Aeneas beaconcrypt_core
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformRecordCompiler
open PqxdhServerAuthExperiment (Setup Codec)
open RegistrationNativePlatformEffectCompiler (Spec compile close effect close_pure close_bind close_public close_effect)
open RegistrationServerRootCompiler (Local)
open RegistrationServerRecordWorldSource (project)
variable {n : Nat} {E Platform ι KemSK Reader Response : Type} {base : OracleSpec ι}
variable [primitive : BeaconcryptCore.Refinement.AdapterSealPrimitive.Operations]

noncomputable def record (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (BeaconcryptCore.Refinement.AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (initial : RegistrationBoundKeySchedule.PublicInitial) (output : PqxdhServerAuthKeySchedule.Output) :
    StateT Platform (OracleComp (Spec n)) (RustM RegistrationServerRecordExecutor.Result) :=
  RegistrationNativePlatformBoundPublication.record
    (fun request => compile (RegistrationNativePlatformSourceSealLower.sealing source view failure allocation request))
    (RegistrationNativePlatformSourceHashLower.hashing effect erased)
    (fun request => compile (RegistrationNativePlatformSourceCompletion.writeWith helper request)) initial output

omit primitive in
private theorem hom : Cslib.IsMonadHom
    (StateT Platform (OracleComp (Spec n))) (StateT (Local n) (StateT Platform ProbComp))
    (fun {A} (work : StateT Platform (OracleComp (Spec n)) A) => close work) :=
  .mk' close_pure close_bind

omit primitive in
private theorem hash_close (erased transcript : commitment.CommitmentTranscript) :
    close (RegistrationNativePlatformSourceHashLower.hashing (effect (n := n) (Platform := Platform)) erased transcript) =
      RegistrationNativePlatformSourceHashLower.hashing
        (RegistrationNativePlatformPairedServerService.nativeEffects (n := n)
          (Auxiliary := RegistrationServerRoleBackend.State) RegistrationNativePlatformMldsaProgram.coins) erased transcript := by
  unfold RegistrationNativePlatformSourceHashLower.hashing
  rw [close_bind, close_effect]
  apply bind_congr
  intro digest
  exact close_pure _

/-- The concrete free client interprets to the same common-platform/local first-record execution, with public random draws outside private native counters. -/
theorem interpret (setup : Setup base KemSK)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (BeaconcryptCore.Refinement.AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (initial : RegistrationBoundKeySchedule.PublicInitial) (output : PqxdhServerAuthKeySchedule.Output) :
    close (record (n := n) setup.source view failure allocation erased helper initial output) =
      RegistrationNativePlatformSourceRecordLower.lowered RegistrationNativePlatformMldsaProgram.coins setup
        view failure allocation erased helper initial output := by
  unfold record RegistrationNativePlatformSourceRecordLower.lowered RegistrationNativePlatformBoundPublication.record
  cases stage : RegistrationSeedErasure.selected (RegistrationBoundKeySchedule.restore initial)
      (RawCtxSelectedInitialConstructor.response64 (RegistrationBoundKeySchedule.zero ++ output.2))
      (RawCtxKdfRequestTable.fullResponse output.1) with
  | fail error => exact close_pure _
  | div => exact close_pure _
  | ok result => cases result with
    | Err previous => exact close_pure _
    | Ok pending =>
      change close (RegistrationNativePlatformSourceRecord.fromAeadWithHash _ _ _ pending) = _
      rw [RegistrationNativePlatformSourceRecord.fromAeadWithHash_map hom]
      simp only [close_public, hash_close]
      rfl

/-- The literal source first record is the interpreted concrete restricted client under the explicitly stated source accounting view, retaining all persistent platform effects and failures. -/
theorem source (setup : Setup base KemSK) (codec : Codec Reader Response)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (BeaconcryptCore.Refinement.AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (initial : registration.ServerInitialKdf) (root : PqxdhSecretInputKdf.RootOutput)
    (role : initial.pending = PqxdhInitialRatchetComplementarity.serverPending
      (PqxdhRootTableInitialization.rootArray root)) (before : Local n) :
    Prod.map id project <$> (RegistrationNativePlatformSourceRecord.fromInitialWithHash
      (RegistrationNativePlatformServerCompletion.records RegistrationNativePlatformMldsaProgram.coins setup codec)
      (RegistrationNativePlatformSourceSeal.sealing RegistrationNativePlatformMldsaProgram.coins setup codec view failure allocation)
      (RegistrationNativePlatformSourceSeal.hash RegistrationNativePlatformMldsaProgram.coins setup codec erased)
      (RegistrationNativePlatformSourceBuild.write helper) initial).run before =
      (close (record setup.source view failure allocation erased helper (RegistrationBoundKeySchedule.publicInitial initial)
        (PqxdhServerAuthKeySchedule.fromRoot setup.source root))).run (project before) := by
  rw [interpret]
  exact RegistrationNativePlatformSourceRecordLower.source RegistrationNativePlatformMldsaProgram.coins setup codec
    view failure allocation erased helper initial root role before

end BeaconcryptCore.Computational.RegistrationNativePlatformRecordCompiler

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordCompiler.interpret' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordCompiler.interpret

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordCompiler.source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordCompiler.source
