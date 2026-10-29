-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationBeaconReferenceNativeOwner

/-! Native one-owner completion erases only the selected scalar and the record-request analysis ledger. The real root-derived sequence-one opening and consumed-kernel installation remain the actual source computations. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationBeaconReferenceNativeKnown
open PqxdhServerAuthExperiment (Setup)
open RegistrationBeaconReferenceCompiler (SelectedOwner eraseOwner)
open RegistrationNativeBeaconFrontend (Owner Trusted)
open RegistrationWorldAgreementCompiler (EnvState)
open RegistrationBeaconReferenceNativeRecord (environment erase)
variable {ι KemSK Auxiliary : Type} {base : OracleSpec ι} {n : Nat}
variable {mlSource : RegistrationNativeMldsa.Source}

/-- The actual one-owner source's initial64/ongoing76 callbacks use the same bound108 opening; only their explicit request ledger is projected. -/
theorem record_factor (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (erased : Std.Array U8 357#usize) (descriptor : RegistrationBeaconBoundSource.PublicAgreement)
    (root : PqxdhSecretInputKdf.RootOutput) (env : EnvState Auxiliary) :
    Prod.map id erase <$>
      (simulateQ (RegistrationBeaconReferenceNativeOwner.record (n := n) (mlSource := mlSource) setup wire)
        (RegistrationBeaconRecordExecutor.begin (RegistrationBeaconBoundSource.atRoot descriptor root))).run env =
      (fun result => (result, erase env)) <$>
        simulateQ environment (simulateQ (RegistrationBoundSourceCompiler.rawCompiler setup.source wire.frameWrite)
          (RegistrationNativePairedBeaconService.program setup.source descriptor
            (PqxdhServerAuthKeySchedule.fromRoot setup.source root))) := by
  have exactSource := RegistrationBeaconReferenceNativeRecord.controller (n := n) (mlSource := mlSource)
    setup wire erased descriptor root ([], env)
  rw [OracleComp.simulateQ_flattenStateT_run, RegistrationBeaconReferenceNativeOwner.record_program] at exactSource
  have viewed := congrArg (fun work => Prod.map id Prod.snd <$> work) exactSource
  simpa only [StateT.run_lift, bind_pure_comp, StateT.run_map, Functor.map_map,
    Prod.map_def, id_eq, RegistrationBeaconReferenceNativeRecord.project] using viewed

noncomputable def after (owner : SelectedOwner mlSource) (result : RustM RegistrationBeaconRecordExecutor.Result) :
    RegistrationBeaconReferenceCompletion.M (target := Trusted n KemSK) (Auxiliary := Auxiliary) mlSource
      (RustM (Option Pqxdh.Bytes)) := do
  let completed ← StateT.lift (StateT.lift (simulateQ environment
    (RegistrationNativePairedBeaconService.after owner.worldOwner owner.pin.binding.identity_key_id
      (fun value => .known value.kernel) result)))
  RegistrationBeaconReferenceCompletion.after environment owner completed

/-- Every source completion failure and successful kernel installation agrees with the scalar-free owner phase update and retains all effects. -/
theorem after_project (owner current : Owner mlSource) (result : RustM RegistrationBeaconRecordExecutor.Result)
    (env : EnvState Auxiliary) :
    (fun value => ((value.1.1, eraseOwner value.1.2), erase value.2)) <$>
      ((RegistrationBeaconReferenceNativeOwner.after (n := n) (KemSK := KemSK) owner result).run current).run env =
      ((after (n := n) (KemSK := KemSK) (eraseOwner owner) result).run (eraseOwner current)).run (erase env) := by
  cases result with
  | fail error | div => rfl
  | ok answer => cases answer with
    | Err aborted => rfl
    | Ok established =>
        simp only [RegistrationBeaconReferenceNativeOwner.after, after,
          RegistrationNativePairedBeaconService.after, simulateQ_map, simulateQ_spec_query, environment, RegistrationBeaconReferenceCompletion.after,
          StateT.run_bind, StateT.run_lift, bind_pure_comp, bind_map_left, map_bind]
        apply bind_congr
        intro installed
        cases installed <;>
          simp only [Bool.false_eq_true, ↓reduceIte, RegistrationBeaconReferenceNativeOwner.abort,
            RegistrationBeaconReferenceCompletion.abort,
            StateT.run_pure, StateT.run_modify, bind_pure_comp, StateT.run_map,
            map_pure, eraseOwner, erase]
        all_goals rfl

noncomputable def postRoot (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (owner : Owner mlSource) (agreement : agreement.BeaconAgreement) :
    RegistrationBeaconReferenceNativeOwner.M n KemSK Auxiliary mlSource (RustM (Option Pqxdh.Bytes)) := do
  let result ← StateT.lift (simulateQ (RegistrationBeaconReferenceNativeOwner.record (mlSource := mlSource) setup wire)
    (RegistrationBeaconRecordExecutor.begin agreement))
  RegistrationBeaconReferenceNativeOwner.after owner result

noncomputable def factored (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (owner : SelectedOwner mlSource) (descriptor : RegistrationBeaconBoundSource.PublicAgreement)
    (root : PqxdhSecretInputKdf.RootOutput) :
    RegistrationBeaconReferenceCompletion.M (target := Trusted n KemSK) (Auxiliary := Auxiliary) mlSource
      (RustM (Option Pqxdh.Bytes)) := do
  let result ← StateT.lift (StateT.lift (simulateQ environment
    (simulateQ (RegistrationBoundSourceCompiler.rawCompiler setup.source wire.frameWrite)
      (RegistrationNativePairedBeaconService.program setup.source descriptor
        (PqxdhServerAuthKeySchedule.fromRoot setup.source root)))))
  after owner result

/-- The whole one-owner native completion consumes exactly the source108 entry before installing its complete advanced kernel and publishing its terminal owner phase. -/
theorem post_root (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (erased : Std.Array U8 357#usize) (owner current : Owner mlSource)
    (descriptor : RegistrationBeaconBoundSource.PublicAgreement) (root : PqxdhSecretInputKdf.RootOutput)
    (env : EnvState Auxiliary) :
    (fun value => ((value.1.1, eraseOwner value.1.2), erase value.2)) <$>
      ((postRoot (n := n) setup wire owner (RegistrationBeaconBoundSource.atRoot descriptor root)).run current).run env =
      ((factored (n := n) setup wire (eraseOwner owner) descriptor root).run (eraseOwner current)).run (erase env) := by
  have continued := congrArg (fun work => work >>= fun result =>
    ((after (n := n) (KemSK := KemSK) (eraseOwner owner) result.1).run (eraseOwner current)).run result.2)
    (record_factor (mlSource := mlSource) setup wire erased descriptor root env)
  simp only [postRoot, factored, StateT.run_bind, StateT.run_lift, bind_pure_comp,
    bind_map_left, map_bind]
  simp only [after_project]
  simpa only [bind_map_left, Functor.map_map, Prod.map_def, id_eq] using continued

end BeaconcryptCore.Computational.RegistrationBeaconReferenceNativeKnown

/-- info: 'BeaconcryptCore.Computational.RegistrationBeaconReferenceNativeKnown.record_factor' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationBeaconReferenceNativeKnown.record_factor

/-- info: 'BeaconcryptCore.Computational.RegistrationBeaconReferenceNativeKnown.after_project' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationBeaconReferenceNativeKnown.after_project

/-- info: 'BeaconcryptCore.Computational.RegistrationBeaconReferenceNativeKnown.post_root' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationBeaconReferenceNativeKnown.post_root
