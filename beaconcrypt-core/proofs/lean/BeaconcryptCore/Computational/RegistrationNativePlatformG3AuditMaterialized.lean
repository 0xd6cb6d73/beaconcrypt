-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformG3MaterializedTrace
import BeaconcryptCore.Computational.RegistrationNativePlatformG3RepeatRun
import BeaconcryptCore.Computational.RegistrationNativeG3MaterializedRetainedLazy
import BeaconcryptCore.Computational.RegistrationNativeG3MaterializedProtocol

/-! The actual corrected source audit is compared to the same materialized source chronology. Fixed callbacks supply the explicit accounting projection internally; every raw result, ledger, source return and persistent platform state remains in the observed value. -/
open OracleComp OracleSpec CoreModels Aeneas ENNReal
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformG3AuditMaterialized
open PqxdhServerAuthExperiment (Setup Codec Checks)
open RegistrationNativeG3AuditTraceRun (cold)
variable {n : Nat} {I KemSK ProviderState Reader Response Platform E A : Type} {base : OracleSpec I}
variable (table : PqxdhRecordLiftInterface.Slot n → PqxdhDeploymentHiddenLayout.Material)
    (setup : Setup base KemSK) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (seeds : RegistrationNativeG3AuditedWorld.Seeds n) (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes) (candidate : PqxdhKemIndCca.MlKemSharedSecret)
    (provider : RegistrationNativeHiddenInterpreter.Provider KemSK ProviderState)
variable [primitive : BeaconcryptCore.Refinement.AdapterSealPrimitive.Operations]
    (checks : Checks) (source : RegistrationNativeMldsa.Source) (selectedOwner selectedAccept : Nat)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
    (reserveFrame : Nat → StateT Platform ProbComp (core.result.Result Unit E)) (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (BeaconcryptCore.Refinement.AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (serverKeyId : U64) (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) A) (front : RegistrationNativePlatformPublicFrontend.State source Platform)
    (frame : RegistrationNativeSelectiveHiddenInterpreter.State n KemSK ProviderState) (world : PqxdhRecordLiftWorld.State n)
local notation "canonical" => RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire
local notation "tree" => RegistrationNativePlatformMaterializedWhole.tree (n := n) setup wire sign scalar checks source selectedOwner selectedAccept
  view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer serverKeyId bounds mode work front
local notation "tracedTree" => RegistrationNativeG2Trace.program tree

noncomputable def full := Prod.fst <$>
  (simulateQ (RegistrationNativeG3MaterializedLocal.handler true table seeds setup codec route canonical sign seed scalar candidate provider)
    tracedTree).run (cold frame ∅, world)

/-- The actual corrected full material source and selective known source retain the same entire native G2 chronology, raw ledger and P. -/
theorem known_source :
    full table setup codec route seeds wire sign seed scalar candidate provider checks source selectedOwner selectedAccept
      view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer serverKeyId bounds mode work front frame world =
      Prod.fst <$> RegistrationNativePlatformG3RepeatRun.known setup codec route seeds wire sign seed scalar candidate provider checks source selectedOwner selectedAccept
        view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer serverKeyId bounds mode work front frame
        (RegistrationNativeG3LocalMaterialCompletedSource.cache table) world := by
  let before : RegistrationNativeG3LocalKeys.State n KemSK ProviderState := (cold frame ∅, world)
  have mixed := congrArg (fun program => Prod.fst <$>
    (simulateQ (RegistrationNativeG3LocalMaterialCompletion.fixed table setup codec route canonical sign seed scalar candidate provider) program).run before)
    (RegistrationNativePlatformG3MaterializedTrace.run_source setup checks wire source sign selectedOwner selectedAccept (setup.dh.publicKey scalar)
      view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer seeds serverKeyId bounds mode work front)
  have actual := congrArg (Functor.map Prod.fst)
    (RegistrationNativeG3LocalMaterialCompletedSource.world_source table setup codec route canonical sign seed scalar candidate provider
      (simulateQ (RegistrationNativeG3MaterializedLocal.translate false seeds) tracedTree) before)
  have pulled := congrArg (fun actual =>
    (fun result => result.1.1) <$> (simulateQ (CborRecordWorldSimulation.guarded setup codec route) actual).run world)
    (RegistrationNativeG3MaterializedSelectivePullback.program_source setup canonical sign seed scalar candidate provider seeds tracedTree
      (RegistrationNativeG3LocalMaterialCompletion.put before (RegistrationNativeG3LocalMaterialCompletedSource.cache table)).1)
  simp only [Functor.map_map, Prod.map_def, id_eq, before] at mixed actual
  have normalized := congrArg (Functor.map Prod.fst)
    (RegistrationNativeG3MaterializedLocalKeys.fixed_program_project table setup codec route canonical sign seed scalar candidate provider
      (simulateQ (RegistrationNativeG3MaterializedLocal.translate false seeds) tracedTree) before)
  simp only [Functor.map_map, Prod.map_def, id_eq, before] at normalized
  have sameRealize : RegistrationNativeG3GuardedMaterializedWorld.realize seeds = RegistrationNativeG3MaterializedWorld.realize seeds := rfl
  have combined := mixed.trans (normalized.trans (actual.symm.trans pulled.symm))
  simpa only [full, RegistrationNativePlatformG3RepeatRun.known, RegistrationNativePlatformG3AliasAudit.known,
    RegistrationNativeG3GuardedCoupling.known, RegistrationNativeG3GuardedMaterializedWorld.source, sameRealize,
    RegistrationNativeG3MaterializedLocal.handler, QueryImpl.simulateQ_compose,
    RegistrationNativeG3LocalMaterialCompletion.put, RegistrationNativeG3LocalMaterialFrame.put,
    RegistrationNativePlatformMaterializedWhole.tree, before, cold, Functor.map_map, Prod.map_def, id_eq, Function.comp_def] using combined

/-- Every actual marked source outcome is charged to repetition in that same full native material execution. -/
theorem mark_bound (unused : ∀ slot role, world.used slot role = false) :
    Pr{let result ← (RegistrationNativePlatformG3RepeatRun.original setup codec route seeds wire sign seed scalar candidate provider checks source selectedOwner selectedAccept
      view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer serverKeyId bounds mode work front frame
      (RegistrationNativeG3LocalMaterialCompletedSource.cache table) world)}[result.2.2 = true] ≤
    Pr{let result ← (full table setup codec route seeds wire sign seed scalar candidate provider checks source selectedOwner selectedAccept
      view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer serverKeyId bounds mode work front frame world)}[
      RegistrationNativeG2Trace.RepeatedRoleAttempt (RegistrationNativeRelatedFamily.input setup.joint setup.dh seed scalar)
        (RegistrationNativeSelectiveHiddenService.selected (RegistrationNativeKeyFamilyPreparation.inside (setup.joint.staticDh seed (setup.dh.publicKey scalar))) candidate)
        result.2.events] := by
  rw [known_source, prEvent_map]
  exact RegistrationNativePlatformG3RepeatRun.mark_bound setup codec route seeds wire sign seed scalar candidate provider checks source selectedOwner selectedAccept
    view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer serverKeyId bounds mode work front frame
    (RegistrationNativeG3LocalMaterialCompletedSource.cache table) world unused

end BeaconcryptCore.Computational.RegistrationNativePlatformG3AuditMaterialized

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformG3AuditMaterialized.known_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformG3AuditMaterialized.known_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformG3AuditMaterialized.mark_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformG3AuditMaterialized.mark_bound
