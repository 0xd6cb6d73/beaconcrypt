-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformBeaconMaterialFrontend
import BeaconcryptCore.Computational.RegistrationNativePlatformMaterializedEffects
import BeaconcryptCore.Computational.RegistrationNativeG3MaterializedFrontend
/-! Corrected assigned-identifier Beacon installation has its literal fixed-seed materialization. Primitive opening and all source record markers stay in their original order; the seed table is used only by the outer private installation interpretation. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformMaterializedBeacon
open PqxdhRecordLiftInterface (EnvEffects Slot)
open RegistrationNativeG3AuditedWorld (Seeds)
open RegistrationWorldAgreementCompiler (EnvState)
variable {n : Nat} {Auxiliary A : Type}

noncomputable def realize (seeds : Seeds n) : QueryImpl (EnvEffects n) (OracleComp (EnvEffects n))
  | .inr (.installServer keyId binding (.hidden slot)) => (EnvEffects n).query
      (.inr (.installServer keyId binding (.known (PqxdhRecordLiftWorld.kernel .server (seeds slot)))))
  | .inr (.installBeacon owner shell (.hidden slot)) => (EnvEffects n).query
      (.inr (.installBeacon owner shell (.known (PqxdhRecordLiftWorld.kernel .beacon (seeds slot)))))
  | query => (EnvEffects n).query query

/-- The actual assigned-ID after-continuation retains every error and changes only the private kernel reference. -/
theorem after_replaced (owner : Nat) (slot : Slot n) (seeds : Seeds n)
    (result : RustM RegistrationBeaconRecordExecutor.Result) :
    RegistrationNativePlatformPairedBeaconService.after (QueryImpl.ofLift (EnvEffects n) (OracleComp (EnvEffects n))) owner
      (fun completed => .known completed.kernel)
      (RegistrationBeaconSeed.replace (PqxdhRecordLiftWorld.kernel .beacon (seeds slot)) result) =
      simulateQ (realize seeds)
        (RegistrationNativePlatformPairedBeaconService.after (QueryImpl.ofLift (EnvEffects n) (OracleComp (EnvEffects n))) owner
          (fun _ => .hidden slot) result) := by
  cases result with
  | fail error | div => rfl
  | ok result => cases result with
    | Err aborted => rfl
    | Ok completed =>
      simp only [RegistrationBeaconSeed.replace, RegistrationNativePlatformPairedBeaconService.after,
        QueryImpl.ofLift, simulateQ_bind, simulateQ_spec_query, realize, simulateQ_pure]

private theorem prim_free (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (seeds : Seeds n) :
    realize seeds ∘ₛ PqxdhDeploymentEnvironment.primFwd source.crypto source =
      PqxdhDeploymentEnvironment.primFwd source.crypto source := by
  funext query
  rcases query with request | bytes | opening
  all_goals simp only [QueryImpl.apply_compose, PqxdhDeploymentEnvironment.primFwd,
    simulateQ_pure, simulateQ_map, PqxdhDeploymentEnvironment.request,
    simulateQ_spec_query, realize]
private theorem shared_free (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (writer : RawCtxMixedShared.Writer) (seeds : Seeds n) :
    realize seeds ∘ₛ RegistrationBoundSourceCompiler.sharedCompiler source writer =
      RegistrationBoundSourceCompiler.sharedCompiler source writer := by
  funext query
  cases query with
  | inl query =>
      simp only [QueryImpl.apply_compose, RegistrationBoundSourceCompiler.sharedCompiler,
        PqxdhDeploymentEnvironment.request, simulateQ_spec_query, realize]
  | inr query =>
      change simulateQ (realize seeds)
        (simulateQ (PqxdhDeploymentEnvironment.primFwd source.crypto source)
          (RawCtxMixedShared.sharedAdapter source.crypto writer query)) = _
      rw [← QueryImpl.simulateQ_compose, prim_free]
      rfl
private theorem source_read_free (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (writer : RawCtxMixedShared.Writer) (seeds : Seeds n) (query : RegistrationRawReceiveBridge.Spec.Domain) :
    simulateQ (realize seeds) (RegistrationBeaconRecordSourceProgram.read source writer query) =
      RegistrationBeaconRecordSourceProgram.read source writer query := by
  simp only [RegistrationBeaconRecordSourceProgram.read, RegistrationBoundSourceCompiler.rawCompiler,
    QueryImpl.apply_compose, QueryImpl.simulateQ_compose]
  rw [← QueryImpl.simulateQ_compose, shared_free]
private theorem read_free (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (writer : RawCtxMixedShared.Writer) (seeds : Seeds n) :
    RegistrationBeaconMaterialRead.read (Auxiliary := Auxiliary) (realize seeds) source writer =
      RegistrationBeaconMaterialRead.read (QueryImpl.ofLift (EnvEffects n) (OracleComp (EnvEffects n))) source writer := by
  funext query env
  simp only [RegistrationBeaconMaterialRead.read, RegistrationBeaconMaterialRead.charge,
    source_read_free, simulateQ_ofLift_eq_self]
private theorem raw_program_free (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (writer : RawCtxMixedShared.Writer) (seeds : Seeds n)
    (work : OracleComp RawCtxWholeOwner.PrimitiveSpec A) (env : EnvState Auxiliary) :
    simulateQ (realize seeds)
      ((simulateQ (RegistrationBeaconChargedSource.primitive (RegistrationBeaconMaterialRead.read
        (QueryImpl.ofLift (EnvEffects n) (OracleComp (EnvEffects n))) source writer)) work).run env) =
      (simulateQ (RegistrationBeaconChargedSource.primitive (RegistrationBeaconMaterialRead.read
        (QueryImpl.ofLift (EnvEffects n) (OracleComp (EnvEffects n))) source writer)) work).run env := by
  rw [RegistrationBeaconMaterialRead.primitive_program, read_free]
private theorem after_state (owner : Nat) (slot : Slot n) (seeds : Seeds n)
    (result : RustM RegistrationBeaconRecordExecutor.Result) (env : EnvState Auxiliary) :
    (RegistrationNativePlatformPairedBeaconService.after
      (fun query => StateT.lift ((EnvEffects n).query query : OracleComp (EnvEffects n) _)) owner
      (fun completed => .known completed.kernel)
      (RegistrationBeaconSeed.replace (PqxdhRecordLiftWorld.kernel .beacon (seeds slot)) result)).run env =
      simulateQ (realize seeds)
        ((RegistrationNativePlatformPairedBeaconService.after
          (fun query => StateT.lift ((EnvEffects n).query query : OracleComp (EnvEffects n) _)) owner
          (fun _ => .hidden slot) result).run env) := by
  cases result with
  | fail error | div => rfl
  | ok result => cases result with
    | Err aborted => rfl
    | Ok completed =>
      simp only [RegistrationBeaconSeed.replace, RegistrationNativePlatformPairedBeaconService.after,
        StateT.run_map, StateT.run_lift, bind_pure_comp,
        simulateQ_map, simulateQ_spec_query, realize]

/-- The complete corrected first-open stage changes only private seed materialization, preserving the exact reached local environment and every install failure. -/
theorem stage (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (owner : Nat) (slot : Slot n) (descriptor : RegistrationBeaconBoundSource.PublicAgreement)
    (material : PqxdhDeploymentHiddenLayout.Material) (seeds : Seeds n) (env : EnvState Auxiliary) :
    (RegistrationNativePlatformPairedBeaconOwner.knownStage source
      (RegistrationBeaconChargedSource.primitive (RegistrationBeaconMaterialRead.read
        (QueryImpl.ofLift (EnvEffects n) (OracleComp (EnvEffects n))) source writer))
      (fun query => StateT.lift ((EnvEffects n).query query : OracleComp (EnvEffects n) _)) owner descriptor
      (PqxdhDeploymentHiddenLayout.joinOutput material (seeds slot))).run env =
      simulateQ (realize seeds)
        ((RegistrationNativePlatformPairedBeaconOwner.publicHidden source
          (RegistrationBeaconChargedSource.primitive (RegistrationBeaconMaterialRead.read
            (QueryImpl.ofLift (EnvEffects n) (OracleComp (EnvEffects n))) source writer))
          (fun query => StateT.lift ((EnvEffects n).query query : OracleComp (EnvEffects n) _)) owner descriptor
          ⟨slot, material⟩).run env) := by
  simp only [RegistrationNativePlatformPairedBeaconOwner.knownStage,
    RegistrationNativePlatformPairedBeaconOwner.publicHidden, RegistrationNativePlatformPairedBeaconOwner.hiddenStage,
    StateT.run_bind]
  rw [RegistrationBeaconSeed.program_split source descriptor material (seeds slot)]
  simp only [RegistrationBeaconSeed.publicProgram, simulateQ_map, StateT.run_map, bind_map_left, simulateQ_bind]
  rw [raw_program_free]
  apply bind_congr
  rintro ⟨result, reached⟩
  exact after_state owner slot seeds result reached
private theorem known_after_free (owner : Nat) (seeds : Seeds n)
    (result : RustM RegistrationBeaconRecordExecutor.Result) (env : EnvState Auxiliary) :
    simulateQ (realize seeds)
      ((RegistrationNativePlatformPairedBeaconService.after
        (fun query => StateT.lift ((EnvEffects n).query query : OracleComp (EnvEffects n) _)) owner
        (fun completed => .known completed.kernel) result).run env) =
      (RegistrationNativePlatformPairedBeaconService.after
        (fun query => StateT.lift ((EnvEffects n).query query : OracleComp (EnvEffects n) _)) owner
        (fun completed => .known completed.kernel) result).run env := by
  cases result with
  | fail error | div => rfl
  | ok result => cases result with
    | Err aborted => rfl
    | Ok completed =>
      simp only [RegistrationNativePlatformPairedBeaconService.after,
        StateT.run_map, StateT.run_lift, bind_pure_comp,
        simulateQ_map, simulateQ_spec_query, realize]

/-- Actual known and opaque Beacon choices preserve the complete source opening and assigned-ID installation histories under the same private table. -/
theorem branch (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (owner : Nat) (descriptor : RegistrationBeaconBoundSource.PublicAgreement)
    (choice : RegistrationNativePairedChoice.Choice n) (seeds : Seeds n) (env : EnvState Auxiliary) :
    (RegistrationNativePlatformPairedBeaconOwner.publicBranch source
      (RegistrationBeaconChargedSource.primitive (RegistrationBeaconMaterialRead.read
        (QueryImpl.ofLift (EnvEffects n) (OracleComp (EnvEffects n))) source writer))
      (fun query => StateT.lift ((EnvEffects n).query query : OracleComp (EnvEffects n) _)) owner descriptor
      (RegistrationNativeG3MaterializedFrontend.materialize seeds choice)).run env =
      simulateQ (realize seeds)
        ((RegistrationNativePlatformPairedBeaconOwner.publicBranch source
          (RegistrationBeaconChargedSource.primitive (RegistrationBeaconMaterialRead.read
            (QueryImpl.ofLift (EnvEffects n) (OracleComp (EnvEffects n))) source writer))
          (fun query => StateT.lift ((EnvEffects n).query query : OracleComp (EnvEffects n) _)) owner descriptor choice).run env) := by
  cases choice with
  | known output =>
      simp only [RegistrationNativeG3MaterializedFrontend.materialize,
        RegistrationNativePlatformPairedBeaconOwner.publicBranch, RegistrationNativePlatformPairedBeaconOwner.knownStage,
        StateT.run_bind, simulateQ_bind]
      rw [raw_program_free]
      apply bind_congr
      rintro ⟨result, reached⟩
      exact (known_after_free owner seeds result reached).symm
  | hidden reference => exact stage source writer owner reference.slot descriptor reference.material seeds env
end BeaconcryptCore.Computational.RegistrationNativePlatformMaterializedBeacon

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformMaterializedBeacon.after_replaced' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformMaterializedBeacon.after_replaced

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformMaterializedBeacon.stage' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformMaterializedBeacon.stage

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformMaterializedBeacon.branch' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformMaterializedBeacon.branch
