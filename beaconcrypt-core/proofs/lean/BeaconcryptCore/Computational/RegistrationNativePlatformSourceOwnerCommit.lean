-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformSourceOwnerEmbedding
/-! Reassembling a returned owner list and the current environment commits the same reached source World and generated-key pool, with persistent P retained. The named native instrumentation view commutes with that literal memory commit, including arbitrary prior record markers. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformSourceOwnerCommit
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativePublicSourceState (restore project nativeView)
open RegistrationNativePlatformSourceOwnerJoint (Spec sourceHandler nativeHandler Allowed)
open RegistrationServerReferenceRestore (Roots)
variable {n : Nat} {ι KemSK Platform Value : Type} {base : OracleSpec ι} {source : RegistrationNativeMldsa.Source}

abbrev Output (source : RegistrationNativeMldsa.Source) (Platform Value : Type) :=
  ((Value × RegistrationNativeBeaconFrontend.State source) × RegistrationWorldAgreementCompiler.EnvState RegistrationServerRoleBackend.State) × Platform

def commit (result : Output source Platform Value × RegistrationNativeExperiment.State n KemSK source) :
    (Value × RegistrationNativeExperiment.State n KemSK source) × Platform :=
  ((result.1.1.1.1, { result.2 with
      beacons := result.1.1.1.2
      server := { result.2.server with world := RegistrationWorldAgreementCompiler.join result.1.1.2 result.2.server.world.world.1 } }), result.1.2)

def view (result : (Value × RegistrationNativeExperiment.State n KemSK source) × Platform) :=
  ((result.1.1, nativeView result.1.2), result.2)

def observe (roots : Roots) (scalar : PqxdhJointGapDh.ScalarBytes) (frontend : RegistrationNativePublicFrontend.State source)
    (result : Output source Platform Value × RegistrationNativePublicInterpreter.State n KemSK) :=
  view (commit (result.1, restore roots scalar frontend result.2))

/-- Returned source owner/environment writes commute with the named native view; prior request markers need not be empty. -/
theorem commit_view (result : Output source Platform Value × RegistrationNativeExperiment.State n KemSK source) :
    view (commit (Prod.map id nativeView result)) = view (commit result) := by
  simp only [commit, view, Prod.map_def, id_eq, nativeView,
    RegistrationServerMaterialSourceState.nativeView, RegistrationServerRecordWorldSource.project,
    RegistrationWorldAgreementCompiler.join, RegistrationNativeWorldView.project,
    RegistrationNativeWorldView.eraseNative, RegistrationWorldCoinCompiler.eraseCoin,
    Function.update_idem]

private theorem commit_pair_view (returned : Output source Platform Value) (before : RegistrationNativeExperiment.State n KemSK source) :
    view (commit (returned, nativeView before)) = view (commit (returned, before)) := commit_view (returned, before)

/-- Every adaptive joint owner program commits its literal reached source outputs to the same complete native view, retaining P in the result. -/
theorem program_source (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (scalar : PqxdhJointGapDh.ScalarBytes)
    (credential : RegistrationNativeMldsa.Credential source) (roots : Roots)
    (work : OracleComp (Spec n KemSK) (Output source Platform Value))
    (allowed : work.AllQueriesSatisfy (Allowed (KemSK := KemSK)))
    (frontend : RegistrationNativePublicFrontend.State source) (before : RegistrationNativePublicInterpreter.State n KemSK) :
    observe roots scalar frontend <$>
      (simulateQ (sourceHandler setup wire route (RegistrationNativeMldsa.owned source credential) created.seed scalar) work).run before =
      (view ∘ commit) <$>
        (simulateQ (nativeHandler setup checks representation created source) work).run (restore roots scalar frontend before) := by
  have raw := RegistrationNativePlatformSourceOwnerJoint.program_source setup checks wire route representation created scalar credential roots work allowed frontend before
  have mapped := congrArg (fun action => (view ∘ commit) <$> action) raw
  unfold observe
  simpa only [Functor.map_map, Function.comp_def, project, commit_pair_view, commit_view] using mapped

abbrev PublicOutput (source : RegistrationNativeMldsa.Source) (Platform Value : Type) :=
  ((Value × RegistrationNativePublicOwners.State source) × RegistrationWorldAgreementCompiler.EnvState RegistrationServerRoleBackend.State) × Platform

def restoreOutput (scalar : PqxdhJointGapDh.ScalarBytes) (result : PublicOutput source Platform Value) : Output source Platform Value :=
  (((result.1.1.1, RegistrationNativePublicSourceState.owners scalar result.1.1.2), result.1.2), result.2)

private theorem map_apply {S A B : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (change : A → B) (work : StateT S m A) (before : S) :
    (change <$> work) before = Prod.map change id <$> work before := StateT.run_map change work before

/-- The actual public owner wrapper is exactly the current owner/environment/P source tree before private interpretation. -/
theorem layout (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes) (roots : Roots)
    (work : RegistrationNativePlatformPublicOwners.M source RegistrationServerRoleBackend.State
      (RegistrationNativePlatformPublicFrontend.Base n KemSK Platform) Value)
    (before : RegistrationNativePlatformPublicSourceExecution.State n KemSK Platform source) :
    (fun result => ((result.1, project roots scalar result.2.1.1 result.2.2), result.2.1.2)) <$>
      (RegistrationNativePlatformPublicSourceExecution.execute setup wire route sign seed scalar
        (RegistrationNativePlatformPublicFrontend.executeLocal (RegistrationNativePlatformPublicFrontend.beacon work))).run before =
      observe roots scalar before.1.1 <$>
        (RegistrationNativePublicSourceEffects.close setup seed scalar
          (simulateQ (RegistrationNativePlatformPublicSourceExecution.handler setup wire route sign)
            (simulateQ RegistrationNativePlatformPublicFrontend.embedLocal
              (restoreOutput scalar <$> (((work.run before.1.1.beacons).run before.1.1.environment).run before.1.2))))).run before.2 := by
  simp only [RegistrationNativePlatformPublicSourceExecution.execute,
    RegistrationNativePlatformPublicFrontend.executeLocal, RegistrationNativePlatformPublicFrontend.beacon,
    RegistrationNativePublicSourceEffects.close, StateT.run, simulateQ_map, map_apply, Functor.map_map,
    Prod.map_def, id_eq, restoreOutput, observe, view, commit, project, restore,
    RegistrationServerMaterialSourceState.restore, RegistrationServerReferenceRestore.restore]
  rfl
end BeaconcryptCore.Computational.RegistrationNativePlatformSourceOwnerCommit

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSourceOwnerCommit.commit_view' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSourceOwnerCommit.commit_view

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSourceOwnerCommit.program_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSourceOwnerCommit.program_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSourceOwnerCommit.layout' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSourceOwnerCommit.layout
