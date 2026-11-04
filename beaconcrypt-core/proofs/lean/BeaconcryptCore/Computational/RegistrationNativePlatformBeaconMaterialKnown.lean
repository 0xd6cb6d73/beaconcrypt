-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformBeaconMaterialFrontend
import BeaconcryptCore.Computational.RegistrationNativePlatformBeaconOwner
/-! The known-output reference continuation reconstructs the corrected actual native first opening and consumed-kernel installation. Only the selected scalar is removed from the executable owner. Every environment field and failed branch is retained. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformBeaconMaterialKnown
open RegistrationBeaconReferenceCompiler (SelectedOwner eraseOwner)
open RegistrationNativeBeaconFrontend (Owner Trusted)
open RegistrationWorldAgreementCompiler (EnvState)
open RegistrationBeaconReferenceNativeRecord (environment)
variable {n : Nat} {KemSK Auxiliary : Type} {source : RegistrationNativeMldsa.Source}

noncomputable def after (owner : SelectedOwner source) (result : RustM RegistrationBeaconRecordExecutor.Result) :
    RegistrationNativePlatformBeaconMaterialFrontend.M source Auxiliary (OracleComp (Trusted n KemSK))
      (RustM (Option Pqxdh.Bytes)) := do
  let completed ← StateT.lift (RegistrationNativePlatformPairedBeaconService.after
    (fun query => StateT.lift (environment query)) owner.worldOwner (fun value => .known value.kernel) result)
  RegistrationNativePlatformBeaconMaterialFrontend.after environment owner completed

theorem after_project (owner current : Owner source) (result : RustM RegistrationBeaconRecordExecutor.Result)
    (env : EnvState Auxiliary) :
    (fun value => ((value.1.1, eraseOwner value.1.2), value.2)) <$>
      ((RegistrationNativePlatformBeaconOwner.after (n := n) (KemSK := KemSK) owner result).run current).run env =
    ((after (n := n) (KemSK := KemSK) (eraseOwner owner) result).run (eraseOwner current)).run env := by
  cases result with
  | fail error | div => rfl
  | ok result => cases result with
    | Err aborted => rfl
    | Ok completed =>
        simp only [RegistrationNativePlatformBeaconOwner.after, after, RegistrationNativePlatformPairedBeaconService.after,
          StateT.run_bind, StateT.run_lift, bind_pure_comp, bind_map_left, map_bind,
          environment]
        apply bind_congr
        intro installed
        cases installed <;>
          simp only [Bool.false_eq_true, ↓reduceIte, RegistrationNativePlatformBeaconOwner.abort,
            RegistrationNativePlatformBeaconMaterialFrontend.after, RegistrationNativePlatformBeaconMaterialFrontend.abort,
            StateT.run_pure, StateT.run_modify, StateT.run_map, bind_pure_comp, map_pure, eraseOwner]
        all_goals rfl

variable {ι : Type} {base : OracleSpec ι}
theorem record_factor (setup : PqxdhServerAuthExperiment.Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (erased : Std.Array U8 357#usize) (descriptor : RegistrationBeaconBoundSource.PublicAgreement)
    (root : PqxdhSecretInputKdf.RootOutput) :
    simulateQ (RegistrationBeaconReferenceNativeOwner.record (n := n) (mlSource := source) (Auxiliary := Auxiliary) setup wire)
      (RegistrationBeaconRecordExecutor.begin (RegistrationBeaconBoundSource.atRoot descriptor root)) = (do
        let _ ← RegistrationBeaconMaterialRead.charge .initialKdf
        let _ ← if RawCtxReceive.ValidFrame descriptor.candidate.server_binding.identity_key_id
          (PqxdhRefinement.absBytes descriptor.binding.associated_data) (RegistrationBeaconBoundSource.frame descriptor)
          then RegistrationBeaconMaterialRead.charge .ratchetKdf else pure ()
        simulateQ (RegistrationBeaconChargedSource.primitive (RegistrationBeaconMaterialRead.read environment setup.source wire.frameWrite))
          (RegistrationBeaconSeed.program setup.source descriptor (PqxdhServerAuthKeySchedule.fromRoot setup.source root))) := by
  have actual : RegistrationBeaconReferenceNativeOwner.record (n := n) (mlSource := source) (Auxiliary := Auxiliary) setup wire =
      RegistrationBeaconMaterialRead.read environment setup.source wire.frameWrite ∘ₛ RegistrationRawReceiveBridge.nativeAdapter := by
    funext query
    exact RegistrationBeaconMaterialRead.native setup wire query
  rw [actual, QueryImpl.simulateQ_compose, RegistrationBeaconPostRootServices.beacon_exact erased]
  exact RegistrationBeaconChargedSource.source_factor _ setup.source
    (RegistrationBeaconMaterialRead.charge .initialKdf) (RegistrationBeaconMaterialRead.charge .ratchetKdf)
    (RegistrationBeaconMaterialRead.initial environment setup.source wire.frameWrite)
    (RegistrationBeaconMaterialRead.ratchet environment setup.source wire.frameWrite) erased descriptor root

noncomputable def postRoot (setup : PqxdhServerAuthExperiment.Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (owner : Owner source) (agreed : agreement.BeaconAgreement) :
    RegistrationNativePlatformBeaconOwner.M n KemSK Auxiliary source (RustM (Option Pqxdh.Bytes)) := do
  let result ← StateT.lift (simulateQ (RegistrationBeaconReferenceNativeOwner.record (mlSource := source) setup wire)
    (RegistrationBeaconRecordExecutor.begin agreed))
  RegistrationNativePlatformBeaconOwner.after owner result

noncomputable def factored (setup : PqxdhServerAuthExperiment.Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (owner : SelectedOwner source) (descriptor : RegistrationBeaconBoundSource.PublicAgreement)
    (root : PqxdhSecretInputKdf.RootOutput) :
    RegistrationNativePlatformBeaconMaterialFrontend.M source Auxiliary (OracleComp (Trusted n KemSK)) (RustM (Option Pqxdh.Bytes)) := do
  let _ ← StateT.lift (RegistrationBeaconMaterialRead.charge .initialKdf)
  let _ ← if RawCtxReceive.ValidFrame descriptor.candidate.server_binding.identity_key_id
    (PqxdhRefinement.absBytes descriptor.binding.associated_data) (RegistrationBeaconBoundSource.frame descriptor)
    then StateT.lift (RegistrationBeaconMaterialRead.charge .ratchetKdf) else pure ()
  let result ← StateT.lift (simulateQ (RegistrationBeaconChargedSource.primitive
    (RegistrationBeaconMaterialRead.read environment setup.source wire.frameWrite))
      (RegistrationBeaconSeed.program setup.source descriptor (PqxdhServerAuthKeySchedule.fromRoot setup.source root)))
  after owner result

theorem post_root (setup : PqxdhServerAuthExperiment.Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (erased : Std.Array U8 357#usize) (owner current : Owner source)
    (descriptor : RegistrationBeaconBoundSource.PublicAgreement) (root : PqxdhSecretInputKdf.RootOutput)
    (env : EnvState Auxiliary) :
    (fun value => ((value.1.1, eraseOwner value.1.2), value.2)) <$>
      ((postRoot (n := n) setup wire owner (RegistrationBeaconBoundSource.atRoot descriptor root)).run current).run env =
      ((factored (n := n) setup wire (eraseOwner owner) descriptor root).run (eraseOwner current)).run env := by
  simp only [postRoot, StateT.run_bind, StateT.run_lift, bind_pure_comp, bind_map_left, map_bind]
  simp only [after_project]
  rw [record_factor setup wire erased descriptor root]
  by_cases valid : RawCtxReceive.ValidFrame descriptor.candidate.server_binding.identity_key_id
    (PqxdhRefinement.absBytes descriptor.binding.associated_data) (RegistrationBeaconBoundSource.frame descriptor)
  all_goals simp only [factored, valid, ite_true, ite_false, StateT.run_bind, StateT.run_lift,
    bind_pure_comp, bind_map_left, bind_assoc]

theorem chosen_factored (setup : PqxdhServerAuthExperiment.Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (owner : SelectedOwner source) (ready : RegistrationBeaconReferenceRoot.Ready)
    (root : PqxdhSecretInputKdf.RootOutput) :
    RegistrationNativePlatformBeaconMaterialFrontend.chosen (Auxiliary := Auxiliary) setup.source wire.frameWrite environment owner ready
      (.known (PqxdhServerAuthKeySchedule.fromRoot setup.source root)) =
      factored (n := n) setup wire owner ready.descriptor root := by
  rw [RegistrationNativePlatformBeaconMaterialFrontend.known_chosen]
  rfl

theorem known_source (setup : PqxdhServerAuthExperiment.Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (erased : Std.Array U8 357#usize) (owner current : Owner source)
    (ready : RegistrationBeaconReferenceRoot.Ready) (root : PqxdhSecretInputKdf.RootOutput)
    (env : EnvState Auxiliary) :
    (fun value => ((value.1.1, eraseOwner value.1.2), value.2)) <$>
      ((postRoot (n := n) setup wire owner (RegistrationBeaconReferenceRoot.atRoot ready root)).run current).run env =
      ((RegistrationNativePlatformBeaconMaterialFrontend.chosen setup.source wire.frameWrite environment (eraseOwner owner) ready
        (.known (PqxdhServerAuthKeySchedule.fromRoot setup.source root))).run (eraseOwner current)).run env := by
  rw [chosen_factored]
  exact post_root setup wire erased owner current ready.descriptor root env

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformBeaconMaterialKnown.after_project' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformBeaconMaterialKnown.after_project

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformBeaconMaterialKnown.record_factor' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformBeaconMaterialKnown.record_factor

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformBeaconMaterialKnown.post_root' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformBeaconMaterialKnown.post_root

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformBeaconMaterialKnown.chosen_factored' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformBeaconMaterialKnown.chosen_factored

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformBeaconMaterialKnown.known_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformBeaconMaterialKnown.known_source

end BeaconcryptCore.Computational.RegistrationNativePlatformBeaconMaterialKnown
