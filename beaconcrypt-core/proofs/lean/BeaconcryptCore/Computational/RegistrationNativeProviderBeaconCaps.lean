-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeProviderBeaconAgreement

/-! Actual Beacon post-root completion contains material, record and lifecycle work but no KEM callback. These structural certificates justify framing any KEM provider only after the actual provider-dependent agreement has run. All failed openings and installations remain present. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeProviderBeaconCaps
open PqxdhServerAuthExperiment (Setup)
open RegistrationBeaconReferenceCompiler (SelectedOwner Spec effect trustedLift)
open RegistrationWorldAgreementCompiler (EnvState)
open RegistrationNativeProviderBuildCaps (IsLocalKem)
variable {n : Nat} {ι KemSK Auxiliary Value : Type} {base : OracleSpec ι}
variable {mlSource : RegistrationNativeMldsa.Source}

theorem service_zero (work : OracleComp (RegistrationNativePairedServerService.PublicSpec n) Value) :
    (simulateQ (RegistrationBeaconReferenceFinish.service (KemSK := KemSK)) work).IsQueryBoundP IsLocalKem 0 := by
  apply OracleComp.IsQueryBoundP.simulateQ_of_step (OracleComp.isQueryBoundP_false work 0)
    (fun _ impossible => impossible.elim)
  intro query _
  simp only [RegistrationBeaconReferenceFinish.service, isQueryBoundP_query_iff, IsLocalKem]
  exact False.elim

theorem abort_zero (owner current : SelectedOwner mlSource) (env : EnvState Auxiliary) (value : Value) :
    (((RegistrationBeaconReferenceFinish.abort owner *> pure value :
      RegistrationBeaconReferenceCompletion.M (target := Spec n KemSK) (Auxiliary := Auxiliary)
        mlSource Value).run current).run env).IsQueryBoundP IsLocalKem 0 := by
  simp only [RegistrationBeaconReferenceFinish.abort, seqRight_eq_bind, StateT.run_map,
    StateT.run_lift, bind_pure_comp, isQueryBoundP_map_iff, effect,
    isQueryBoundP_query_iff, IsLocalKem]
  exact False.elim

/-- Every actual post-root branch has zero KEM queries, including opening failures and rejected installs. -/
theorem complete_zero (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (owner current : SelectedOwner mlSource) (ready : RegistrationBeaconReferenceRoot.Ready)
    (env : EnvState Auxiliary) :
    (((RegistrationBeaconReferenceFinish.complete (n := n) (KemSK := KemSK) source owner ready).run current).run env).IsQueryBoundP
      IsLocalKem 0 := by
  simp only [RegistrationBeaconReferenceFinish.complete, StateT.run_bind, StateT.run_lift,
    bind_map_left, bind_pure_comp]
  apply isQueryBoundP_bind (n := 0) (m := 0) (service_zero (KemSK := KemSK) _)
  intro completed _
  cases completed with
  | fail error => exact abort_zero owner current env _
  | div => exact abort_zero owner current env _
  | ok completed => cases completed with
    | Err aborted => exact abort_zero owner current env _
    | Ok completed => trivial

theorem after_zero (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (owner current : SelectedOwner mlSource) (result : RustM (Option RegistrationBeaconReferenceRoot.Ready))
    (env : EnvState Auxiliary) :
    (((RegistrationBeaconReferenceNativeContinuation.afterPrepared source owner result :
      RegistrationBeaconReferenceCompletion.M (target := Spec n KemSK) (Auxiliary := Auxiliary)
        mlSource (RustM (Option Pqxdh.Bytes))).run current).run env).IsQueryBoundP IsLocalKem 0 := by
  cases result with
  | fail error => exact abort_zero owner current env _
  | div => exact abort_zero owner current env _
  | ok result => cases result with
    | none => exact abort_zero owner current env _
    | some ready => exact complete_zero source owner current ready env

/-- The native source108 completion has only environment effects, so no provider state is read or advanced. -/
theorem factored_zero (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (owner current : SelectedOwner mlSource) (env : EnvState Auxiliary)
    (ready : RegistrationBeaconReferenceRoot.Ready) (root : PqxdhSecretInputKdf.RootOutput) :
    (simulateQ trustedLift
      (((RegistrationBeaconReferenceNativeKnown.factored setup wire owner ready.descriptor root :
        RegistrationBeaconReferenceCompletion.M (target := RegistrationNativeBeaconFrontend.Trusted n KemSK)
          (Auxiliary := Auxiliary) mlSource (RustM (Option Pqxdh.Bytes))).run current).run env)).IsQueryBoundP IsLocalKem 0 := by
  rw [← RegistrationNativeOrdinaryFinishSourceNative.source_complete_lift setup wire owner current env ready root,
    ← QueryImpl.simulateQ_compose]
  have same : trustedLift (n := n) (KemSK := KemSK) ∘ₛ RegistrationBeaconReferenceNativeRecord.environment = effect := by
    funext query
    simp only [QueryImpl.apply_compose, RegistrationBeaconReferenceNativeRecord.environment,
      simulateQ_spec_query, trustedLift]
  rw [same]
  exact RegistrationNativeProviderBuildCaps.effect_zero _

end BeaconcryptCore.Computational.RegistrationNativeProviderBeaconCaps

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeProviderBeaconCaps.service_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeProviderBeaconCaps.service_zero
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeProviderBeaconCaps.abort_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeProviderBeaconCaps.abort_zero
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeProviderBeaconCaps.complete_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeProviderBeaconCaps.complete_zero
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeProviderBeaconCaps.after_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeProviderBeaconCaps.after_zero
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeProviderBeaconCaps.factored_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeProviderBeaconCaps.factored_zero
