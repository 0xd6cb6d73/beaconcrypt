-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealAcceptCore
import BeaconcryptCore.Computational.RegistrationNativeSecretWordBeaconSource
/-! The actual Beacon collector, root preparation and agreement are natural under distinct persistent source and native states. The individual native-query and evaluated-prepare leaves retain every environment field and arbitrary physical World continuation. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealBeaconCore
open PqxdhServerAuthExperiment (Setup)
open RegistrationBeaconReferenceCompiler (SelectedOwner)
open RegistrationWorldAgreementCompiler (EnvState)
open RegistrationNativePlatformLorIdealAcceptCore (Leaves)
variable {n : Nat} {I KemSK NativePrivate WordPrivate Auxiliary : Type} {base : OracleSpec I}
variable {m : Type → Type} [Monad m] [LawfulMonad m]
variable (candidate : PqxdhKemIndCca.MlKemSharedSecret)
    (native : QueryImpl (RegistrationBeaconReferenceCompiler.Spec n KemSK) (StateT NativePrivate m))
    (symbolic : QueryImpl (RegistrationNativeSecretWordInterface.LocalSpec n KemSK) (StateT WordPrivate m))
    (frame : WordPrivate → NativePrivate) (leaves : Leaves candidate native symbolic frame)
include leaves

/-- The literal opaque-word collector restores exactly the native collected prefix on the projected state. -/
theorem collect_source (setup : Setup base KemSK) {source : RegistrationNativeMldsa.Source}
    (owner : SelectedOwner source) (oneTime : PqxdhJointGapDh.ScalarBytes) (authenticated : registration.AuthenticatedResponse)
    (env : EnvState Auxiliary) (before : WordPrivate) :
    Prod.map (Prod.map (Option.map (RegistrationNativeSecretWordBeaconPrepare.eval candidate)) id) frame <$>
      (simulateQ symbolic ((RegistrationNativeSecretWordBeaconCompiler.collect setup owner oneTime authenticated).run env)).run before =
      (simulateQ native ((RegistrationBeaconReferenceCompiler.collect setup owner oneTime authenticated).run env)).run (frame before) := by
  have related := OracleComp.map_run_simulateQ_eq_of_query_map_eq
    (symbolic ∘ₛ RegistrationNativeSecretWordServerSource.realize candidate) native frame leaves.native_leaf
    ((RegistrationBeaconReferenceCompiler.collect setup owner oneTime authenticated).run env) before
  have syntaxLaw := congrArg (fun work => (simulateQ symbolic work).run before)
    (RegistrationNativeSecretWordBeaconSource.collector_source setup owner oneTime authenticated candidate env)
  simp only [←QueryImpl.simulateQ_compose,simulateQ_map,StateT.run_map] at syntaxLaw
  rw [syntaxLaw] at related
  simpa only [Functor.map_map,Prod.map_def,id_eq] using related

/-- Source preparation echoes the same evaluated descriptor and retains the full projected persistent state. -/
theorem root_source (authenticated : registration.AuthenticatedResponse)
    (pending : RegistrationNativeSecretWordBeaconPrepare.Prepared registration.AuthenticatedResponse) (before : WordPrivate) :
    Prod.map (RegistrationNativeSecretWordBeaconRoot.restore candidate) frame <$>
      (simulateQ symbolic (simulateQ RegistrationNativeSecretWordInterface.prepare
        (RegistrationNativeSecretWordBeaconRoot.client authenticated pending))).run before =
      (simulateQ native (simulateQ RegistrationBeaconReferenceCompiler.prepare
        (RegistrationBeaconReferenceRoot.client authenticated (RegistrationNativeSecretWordBeaconPrepare.eval candidate pending)))).run (frame before) := by
  simp only [RegistrationNativeSecretWordBeaconRoot.client,RegistrationBeaconReferenceRoot.client,
    simulateQ_bind,simulateQ_spec_query,simulateQ_pure,StateT.run_bind,StateT.run_pure]
  rw [←RegistrationNativeSecretWordBeaconRoot.message_eval candidate pending]
  rw [←leaves.prepare (RegistrationNativeSecretWordBeaconRoot.message pending) before,bind_map_left]
  simp only [map_bind,map_pure]
  apply bind_congr
  rintro ⟨reference,after⟩
  cases reference <;> rfl

/-- The genuine collector and stateful preparation compose on every optional and failed agreement outcome. -/
theorem agreement_source (setup : Setup base KemSK) {source : RegistrationNativeMldsa.Source}
    (owner : SelectedOwner source) (oneTime : PqxdhJointGapDh.ScalarBytes) (authenticated : registration.AuthenticatedResponse)
    (env : EnvState Auxiliary) (before : WordPrivate) :
    Prod.map (Prod.map (RegistrationNativeSecretWordBeaconRoot.restore candidate) id) frame <$>
      (simulateQ symbolic ((RegistrationNativeSecretWordBeaconCompiler.agreement setup owner oneTime authenticated).run env)).run before =
      (simulateQ native ((RegistrationBeaconReferenceCompiler.agreement setup owner oneTime authenticated).run env)).run (frame before) := by
  simp only [RegistrationNativeSecretWordBeaconCompiler.agreement,RegistrationBeaconReferenceCompiler.agreement,
    StateT.run_bind,simulateQ_bind,StateT.run_bind,map_bind]
  have collected := collect_source candidate native symbolic frame leaves setup owner oneTime authenticated env before
  rw [←collected,bind_map_left]
  apply bind_congr
  rintro ⟨⟨collected,envAfter⟩,after⟩
  cases collected with
  | none =>
    simp only [Prod.map_apply,id_eq,Option.map_none,StateT.run_pure,simulateQ_pure,map_pure,
      RegistrationNativeSecretWordBeaconRoot.restore]
  | some pending =>
    simp only [Prod.map_apply,id_eq,Option.map_some,StateT.run_lift,bind_pure_comp,simulateQ_map,
      StateT.run_map,Functor.map_map]
    have rooted := root_source candidate native symbolic frame leaves authenticated pending after
    have lifted := congrArg (Functor.map (fun result => ((result.1,envAfter),result.2))) rooted
    simpa only [Functor.map_map,Prod.map_def,id_eq] using lifted

end BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealBeaconCore

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealBeaconCore.collect_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealBeaconCore.collect_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealBeaconCore.root_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealBeaconCore.root_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealBeaconCore.agreement_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealBeaconCore.agreement_source
