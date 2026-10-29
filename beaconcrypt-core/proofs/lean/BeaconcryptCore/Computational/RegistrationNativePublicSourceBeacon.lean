-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeTrustedAllowed

/-! Interpreting an actual local owner program and committing its returned owner/environment state uses the same global World and private KEM pool. This is the complete state lens below public scalar masking; native/coin/record-request instrumentation is projected by its named existing view. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePublicSourceBeacon
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativePublicSourceServer (State)
open RegistrationNativePublicSourceState (restore nativeView)
open RegistrationNativePublicSourceEffects (close)
open RegistrationServerReferenceRestore (Roots)
open RegistrationNativePublicSourceTrusted (Allowed)
variable {n : Nat} {ι KemSK Value : Type} {base : OracleSpec ι} {source : RegistrationNativeMldsa.Source}

private def commit (result : ((Value × RegistrationNativeBeaconFrontend.State source) ×
    RegistrationWorldAgreementCompiler.EnvState RegistrationServerRoleBackend.State) × RegistrationNativeExperiment.State n KemSK source) :
    Value × RegistrationNativeExperiment.State n KemSK source :=
  (result.1.1.1, { result.2 with
    beacons := result.1.1.2
    server := { result.2.server with
      world := RegistrationWorldAgreementCompiler.join result.1.2 result.2.server.world.world.1 } })

private theorem commit_view (result : ((Value × RegistrationNativeBeaconFrontend.State source) ×
    RegistrationWorldAgreementCompiler.EnvState RegistrationServerRoleBackend.State) × RegistrationNativeExperiment.State n KemSK source) :
    Prod.map id nativeView (commit (Prod.map id nativeView result)) = Prod.map id nativeView (commit result) := by
  simp only [commit, Prod.map_def, id_eq, nativeView,
    RegistrationServerMaterialSourceState.nativeView, RegistrationServerRecordWorldSource.project,
    RegistrationWorldAgreementCompiler.join, RegistrationNativeWorldView.project,
    RegistrationNativeWorldView.eraseNative, RegistrationWorldCoinCompiler.eraseCoin,
    Function.update_idem]

/-- Full local owner execution and publication commits the actual returned roster and current environment on the same reached native World. -/
theorem program_source (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (scalar : PqxdhJointGapDh.ScalarBytes)
    (credential : RegistrationNativeMldsa.Credential source) (roots : Roots)
    (work : RegistrationNativeBeaconFrontend.M n KemSK source RegistrationServerRoleBackend.State Value)
    (before : State n KemSK source)
    (allowed : (((work.run (RegistrationNativePublicSourceState.owners scalar before.1.beacons)).run
      before.1.environment)).AllQueriesSatisfy (Allowed (KemSK := KemSK))) :
    (fun result => (result.1.1.1,
      nativeView { (restore roots scalar before.1 result.2) with
        beacons := result.1.1.2
        server := { (restore roots scalar before.1 result.2).server with
          world := RegistrationWorldAgreementCompiler.join result.1.2 result.2.world } })) <$>
      (close setup created.seed scalar (simulateQ
        (RegistrationNativePublicInterpreter.handler setup wire route (RegistrationNativeMldsa.owned source credential))
        (simulateQ (RegistrationNativePublicFrontend.liftLocal false)
          (simulateQ RegistrationBeaconReferenceCompiler.trustedLift
            ((work.run (RegistrationNativePublicSourceState.owners scalar before.1.beacons)).run before.1.environment))))).run before.2 =
      Prod.map id nativeView <$>
        (RegistrationNativeExperiment.beacon setup checks representation created work).run (restore roots scalar before.1 before.2) := by
  have native := RegistrationNativePublicSourceTrusted.program_source setup checks wire route representation created scalar credential roots
    ((work.run (RegistrationNativePublicSourceState.owners scalar before.1.beacons)).run before.1.environment) allowed before
  have mapped := congrArg (fun distribution => (Prod.map id nativeView ∘ commit) <$> distribution) native
  simp only [Functor.map_map, Function.comp_def, commit_view] at mapped
  simpa only [RegistrationNativeExperiment.beacon, StateT.run, commit, Prod.map_def, id_eq,
    RegistrationNativePublicSourceState.project, nativeView, restore,
    RegistrationServerMaterialSourceState.nativeView, RegistrationServerMaterialSourceState.restore,
    RegistrationServerReferenceRestore.restore, RegistrationWorldAgreementCompiler.join,
    RegistrationWorldAgreementCompiler.erase, bind_pure_comp, Functor.map_map,
    RegistrationServerRecordWorldSource.project, RegistrationNativeWorldView.project,
    RegistrationNativeWorldView.eraseNative, RegistrationWorldCoinCompiler.eraseCoin,
    Function.update_idem] using mapped

end BeaconcryptCore.Computational.RegistrationNativePublicSourceBeacon
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePublicSourceBeacon.program_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePublicSourceBeacon.program_source
