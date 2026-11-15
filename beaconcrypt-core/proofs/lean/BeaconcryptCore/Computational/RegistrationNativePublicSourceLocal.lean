-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePublicSourceOwnerWorld

/-! Public local packing composes with the complete native source lens whenever a proved raw controller equation restores its returned roster. The premise is an operational AST equation, discharged for each concrete controller rather than assumed at a security endpoint. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePublicSourceLocal
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativePublicSourceServer (State)
open RegistrationNativePublicSourceState (restore project nativeView owners)
open RegistrationNativePublicSourceExecution (execute)
open RegistrationNativePublicSourceEffects (toPrivate)
open RegistrationServerReferenceRestore (Roots)
variable {n : Nat} {ι KemSK Value : Type} {base : OracleSpec ι} {source : RegistrationNativeMldsa.Source}

private theorem map_apply {S X Y : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (f : X → Y) (work : StateT S m X) (before : S) :
    (f <$> work) before = Prod.map f id <$> work before := by
  change (work before >>= fun result => pure (f result.1, result.2)) = _
  rw [bind_pure_comp]
  rfl

/-- Literal public packing and private restoration preserve the full reached World, pool and current environment. -/
theorem local_source (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (scalar : PqxdhJointGapDh.ScalarBytes)
    (credential : RegistrationNativeMldsa.Credential source) (selected : Nat)
    (publicPrekey : PqxdhJointIdentity.PeerEncoding) (roots : Roots)
    (work native : RegistrationNativeBeaconFrontend.M n KemSK source RegistrationServerRoleBackend.State Value)
    (before : State n KemSK source)
    (equation : Prod.map (Prod.map id (fun after => owners scalar (RegistrationNativePublicOwners.pack selected publicPrekey after))) id <$>
      ((work.run (before.1.beacons.map RegistrationNativePublicOwners.restore)).run before.1.environment) =
      ((native.run (owners scalar before.1.beacons)).run before.1.environment))
    (allowed : (((native.run (owners scalar before.1.beacons)).run before.1.environment)).AllQueriesSatisfy
      (RegistrationNativePublicSourceTrusted.Allowed (KemSK := KemSK))) :
    Prod.map id (fun after => project roots scalar after.1 after.2) <$>
      (execute setup wire route (RegistrationNativeMldsa.owned source credential) created.seed scalar
        (RegistrationNativePublicFrontend.beacon (RegistrationNativePublicOwners.executeLocal selected publicPrekey work))).run before =
      Prod.map id nativeView <$>
        (RegistrationNativeExperiment.beacon setup checks representation created native).run
          (restore roots scalar before.1 before.2) := by
  rw [RegistrationNativePublicSourceOwnerLayout.beacon_run]
  have raw := congrArg (fun program => RegistrationNativePublicSourceOwnerWorld.privateObserve roots before.1 <$>
    (simulateQ (RegistrationNativeOrdinaryFinishSourceNative.trusted setup wire route
      (RegistrationNativeMldsa.owned source credential) created.seed scalar) program).run (toPrivate before.2)) equation
  rw [RegistrationNativePublicSourceOwnerWorld.program_source setup checks wire route representation created scalar credential roots native before allowed] at raw
  simp only [RegistrationNativePublicOwners.executeLocal, StateT.run, simulateQ_map, RegistrationNativeOrdinaryFinishSourceNative.trusted, QueryImpl.simulateQ_compose,
    Functor.map_map, Prod.map_def, id_eq,
    RegistrationNativePublicSourceOwnerLayout.rebuild,
    RegistrationNativePublicSourceEffects.fromPrivate,
    project, restore] at raw ⊢
  simp only [map_apply, Functor.map_map, Prod.map_def, id_eq,
    RegistrationNativePublicSourceOwnerWorld.privateObserve, RegistrationNativePublicSourceOwnerWorld.observe,
    RegistrationNativeOrdinaryFinishSourceFrame.drop, toPrivate] at raw ⊢
  exact raw

end BeaconcryptCore.Computational.RegistrationNativePublicSourceLocal
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePublicSourceLocal.local_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePublicSourceLocal.local_source
