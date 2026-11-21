-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationBeaconMaterialRead
import BeaconcryptCore.Computational.RegistrationNativePlatformPairedBeaconOwner
import BeaconcryptCore.Computational.RegistrationBeaconReferenceRoot
/-! The corrected executable Beacon continuation demands a public material reference before any initial-record KDF accounting. A missing reference aborts without manufacturing material. Actual source-selected replies retain all bookkeeping, the assigned identifier, owner phase and shared platform effects. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformBeaconMaterialFrontend
open RegistrationBeaconReferenceCompiler (SelectedOwner)
open RegistrationWorldAgreementCompiler (EnvState)
open PqxdhRecordLiftInterface (EnvEffects)
variable {n : Nat} {Auxiliary : Type} {source : RegistrationNativeMldsa.Source}
variable {m : Type → Type} [Monad m]
abbrev M (source : RegistrationNativeMldsa.Source) (Auxiliary : Type) (m : Type → Type) :=
  StateT (SelectedOwner source) (StateT (EnvState Auxiliary) m)

def abort (environment : QueryImpl (EnvEffects n) m) (owner : SelectedOwner source) : M source Auxiliary m Unit := do
  let _ ← StateT.lift (StateT.lift (environment (.inr (.advanceOwner owner.worldOwner .aborted))))
  pure ()

def after (environment : QueryImpl (EnvEffects n) m) (owner : SelectedOwner source) :
    RustM RegistrationNativePairedBeaconService.Result → M source Auxiliary m (RustM (Option Pqxdh.Bytes))
  | .fail error => abort environment owner *> pure (.fail error)
  | .div => abort environment owner *> pure .div
  | .ok (.Err _) => abort environment owner *> pure (.ok none)
  | .ok (.Ok completed) => do
      modify fun current => {current with phase := .established completed}
      pure (.ok (some (TranscriptAuthParts.absSlice completed.application)))

noncomputable def program (crypto : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (owner : SelectedOwner source)
    (ready : RegistrationBeaconReferenceRoot.Ready) (choice : RegistrationNativePairedChoice.Choice n) :
    M source Auxiliary (OracleComp (EnvEffects n)) (RustM (Option Pqxdh.Bytes)) := do
  let environment : QueryImpl (EnvEffects n) (OracleComp (EnvEffects n)) := QueryImpl.ofLift _ _
  let _ ← StateT.lift (RegistrationBeaconMaterialRead.charge .initialKdf)
  let _ ← if RawCtxReceive.ValidFrame ready.descriptor.candidate.server_binding.identity_key_id
    (PqxdhRefinement.absBytes ready.descriptor.binding.associated_data) (RegistrationBeaconBoundSource.frame ready.descriptor)
    then StateT.lift (RegistrationBeaconMaterialRead.charge .ratchetKdf) else pure ()
  let result ← StateT.lift (RegistrationNativePlatformPairedBeaconOwner.publicBranch crypto
    (RegistrationBeaconChargedSource.primitive (RegistrationBeaconMaterialRead.read environment crypto writer))
    (fun query => StateT.lift (environment query)) owner.worldOwner ready.descriptor choice)
  after environment owner result

noncomputable def chosen (crypto : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (environment : QueryImpl (EnvEffects n) m) (owner : SelectedOwner source)
    (ready : RegistrationBeaconReferenceRoot.Ready) (choice : RegistrationNativePairedChoice.Choice n) :
    M source Auxiliary m (RustM (Option Pqxdh.Bytes)) := fun current env =>
  simulateQ environment (((program crypto writer owner ready choice).run current).run env)

noncomputable def complete (crypto : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (environment : QueryImpl (EnvEffects n) m)
    (demand : RegistrationNativeRelatedFamily.Message → m (Option (RegistrationNativePairedChoice.Choice n)))
    (owner : SelectedOwner source) (ready : RegistrationBeaconReferenceRoot.Ready) :
    M source Auxiliary m (RustM (Option Pqxdh.Bytes)) := do
  match ← StateT.lift (StateT.lift (demand ready.reference)) with
  | none => abort environment owner *> pure (.ok none)
  | some choice => chosen crypto writer environment owner ready choice

variable [LawfulMonad m]

theorem after_run (environment : QueryImpl (EnvEffects n) m) (owner current : SelectedOwner source)
    (result : RustM RegistrationNativePairedBeaconService.Result) (env : EnvState Auxiliary) :
    simulateQ environment (((after (QueryImpl.ofLift (EnvEffects n) (OracleComp (EnvEffects n))) owner result).run current).run env) =
      ((after environment owner result).run current).run env := by
  cases result with
  | fail error | div =>
      simp only [after, abort, seqRight_eq_bind, StateT.run_lift, StateT.run_map,
        bind_pure_comp, QueryImpl.ofLift, simulateQ_map, simulateQ_spec_query]
  | ok result => cases result with
    | Err error =>
      simp only [after, abort, seqRight_eq_bind, StateT.run_lift, StateT.run_map,
        bind_pure_comp, QueryImpl.ofLift, simulateQ_map, simulateQ_spec_query]
    | Ok completed =>
      simp only [after, StateT.run_bind, StateT.run_modify, pure_bind, StateT.run_pure, simulateQ_pure]

noncomputable def installed (environment : QueryImpl (EnvEffects n) m) (owner : SelectedOwner source)
    (kernel : registration.CompletedBeacon → PqxdhRecordLiftInterface.KernelRef n)
    (result : RustM RegistrationBeaconRecordExecutor.Result) : M source Auxiliary m (RustM (Option Pqxdh.Bytes)) := do
  let completed ← StateT.lift (RegistrationNativePlatformPairedBeaconService.after
    (fun query => StateT.lift (environment query)) owner.worldOwner kernel result)
  after environment owner completed

theorem installed_run (environment : QueryImpl (EnvEffects n) m) (owner current : SelectedOwner source)
    (kernel : registration.CompletedBeacon → PqxdhRecordLiftInterface.KernelRef n)
    (result : RustM RegistrationBeaconRecordExecutor.Result) (env : EnvState Auxiliary) :
    simulateQ environment (((installed (QueryImpl.ofLift (EnvEffects n) (OracleComp (EnvEffects n))) owner kernel result).run current).run env) =
      ((installed environment owner kernel result).run current).run env := by
  cases result with
  | fail error | div =>
      simp only [installed, RegistrationNativePlatformPairedBeaconService.after, StateT.run_bind, StateT.run_lift, pure_bind]
      exact after_run environment owner current _ env
  | ok result => cases result with
    | Err error =>
      simp only [installed, RegistrationNativePlatformPairedBeaconService.after, StateT.run_bind, StateT.run_lift, pure_bind]
      exact after_run environment owner current _ env
    | Ok completed =>
      simp only [installed, RegistrationNativePlatformPairedBeaconService.after, StateT.run_bind, StateT.run_lift,
        bind_pure_comp, bind_map_left, simulateQ_bind, QueryImpl.ofLift, simulateQ_spec_query]
      apply bind_congr
      intro accepted
      exact after_run environment owner current _ env

theorem known_chosen (crypto : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (environment : QueryImpl (EnvEffects n) m) (owner : SelectedOwner source)
    (ready : RegistrationBeaconReferenceRoot.Ready) (output : PqxdhServerAuthKeySchedule.Output) :
    chosen (Auxiliary := Auxiliary) crypto writer environment owner ready (.known output) = (do
      let _ ← StateT.lift (RegistrationBeaconMaterialRead.charge .initialKdf)
      let _ ← if RawCtxReceive.ValidFrame ready.descriptor.candidate.server_binding.identity_key_id
        (PqxdhRefinement.absBytes ready.descriptor.binding.associated_data) (RegistrationBeaconBoundSource.frame ready.descriptor)
        then StateT.lift (RegistrationBeaconMaterialRead.charge .ratchetKdf) else pure ()
      let opened ← StateT.lift (simulateQ (RegistrationBeaconChargedSource.primitive
        (RegistrationBeaconMaterialRead.read environment crypto writer)) (RegistrationBeaconSeed.program crypto ready.descriptor output))
      installed environment owner (fun value => .known value.kernel) opened) := by
  apply StateT.ext
  intro current
  apply StateT.ext
  intro env
  unfold chosen program RegistrationNativePlatformPairedBeaconOwner.publicBranch RegistrationNativePlatformPairedBeaconOwner.knownStage
  by_cases valid : RawCtxReceive.ValidFrame ready.descriptor.candidate.server_binding.identity_key_id
    (PqxdhRefinement.absBytes ready.descriptor.binding.associated_data) (RegistrationBeaconBoundSource.frame ready.descriptor)
  all_goals simp only [valid, ite_true, ite_false, StateT.run_bind, StateT.run_lift,
    RegistrationBeaconMaterialRead.charge, StateT.run_modify, pure_bind, simulateQ_bind,
    bind_pure_comp, bind_map_left]
  all_goals simp only [RegistrationBeaconMaterialRead.primitive_program (n := n) (Auxiliary := Auxiliary) environment crypto writer]
  all_goals simp only [bind_assoc]
  all_goals apply bind_congr
  all_goals rintro ⟨opened, reached⟩
  all_goals
    have transported := installed_run environment owner current (fun value => .known value.kernel) opened reached
    simpa only [installed, StateT.run_bind, StateT.run_lift, bind_pure_comp,
      simulateQ_bind, bind_map_left] using transported

theorem known (crypto : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (environment : QueryImpl (EnvEffects n) m) (owner : SelectedOwner source)
    (ready : RegistrationBeaconReferenceRoot.Ready) (choice : RegistrationNativePairedChoice.Choice n) :
    complete (Auxiliary := Auxiliary) crypto writer environment (fun _ => pure (some choice)) owner ready =
      chosen crypto writer environment owner ready choice := by
  apply StateT.ext
  intro current
  apply StateT.ext
  intro env
  simp only [complete, StateT.run_bind, StateT.run_lift, StateT.run_pure, pure_bind]

theorem missing (crypto : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (environment : QueryImpl (EnvEffects n) m) (owner : SelectedOwner source)
    (ready : RegistrationBeaconReferenceRoot.Ready) :
    complete (Auxiliary := Auxiliary) crypto writer environment (fun _ => pure none) owner ready =
      abort environment owner *> pure (.ok none) := by
  apply StateT.ext
  intro current
  apply StateT.ext
  intro env
  simp only [complete, StateT.run_bind, StateT.run_lift, StateT.run_pure, pure_bind]

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformBeaconMaterialFrontend.known' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformBeaconMaterialFrontend.known

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformBeaconMaterialFrontend.missing' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformBeaconMaterialFrontend.missing

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformBeaconMaterialFrontend.after_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformBeaconMaterialFrontend.after_run

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformBeaconMaterialFrontend.installed_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformBeaconMaterialFrontend.installed_run

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformBeaconMaterialFrontend.known_chosen' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformBeaconMaterialFrontend.known_chosen

end BeaconcryptCore.Computational.RegistrationNativePlatformBeaconMaterialFrontend
