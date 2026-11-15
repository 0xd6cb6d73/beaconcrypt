-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePublicSourceBeacon
import BeaconcryptCore.Computational.RegistrationNativePublicSourceOwnerLayout
import BeaconcryptCore.Computational.RegistrationNativeOrdinaryFinishSourceFrame

/-! The full owner source lens depends on the complete returned environment, roster and private World/pool frame, rather than the inaccessible root memo. This lets finite private-source owner equations compose with the actual mixed Main dispatcher. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePublicSourceOwnerWorld
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativePublicSourceServer (State)
open RegistrationNativePublicSourceState (restore nativeView)
open RegistrationNativePublicSourceEffects (Private toPrivate)
open RegistrationServerReferenceRestore (Roots)
open RegistrationNativeOrdinaryFinishSourceFrame (Frame drop)
variable {n : Nat} {ι KemSK Value : Type} {base : OracleSpec ι} {source : RegistrationNativeMldsa.Source}

abbrev Output (source : RegistrationNativeMldsa.Source) (Value : Type) :=
  (Value × RegistrationNativeBeaconFrontend.State source) × RegistrationServerReferenceCompiler.Environment

def observe (roots : Roots) (frontend : RegistrationNativePublicFrontend.State source)
    (result : Output source Value × Frame n KemSK) : Value × RegistrationNativeExperiment.State n KemSK source :=
  (result.1.1.1, nativeView
    ⟨RegistrationServerMaterialSourceState.restore roots
      (frontend.server, RegistrationWorldAgreementCompiler.join result.1.2 result.2.1),
      result.1.1.2, result.2.2.1, frontend.parsedAccepts⟩)

def privateObserve (roots : Roots) (frontend : RegistrationNativePublicFrontend.State source)
    (result : Output source Value × Private n KemSK) := observe roots frontend (result.1, drop result.2)

/-- Projecting the existing native record-request markers before reassembly does not change its named full source view. -/
theorem observe_record_view (roots : Roots) (frontend : RegistrationNativePublicFrontend.State source)
    (result : Output source Value × Frame n KemSK) :
    observe roots frontend (((result.1.1.1, result.1.1.2), RegistrationBeaconReferenceNativeRecord.erase result.1.2), result.2) =
      observe roots frontend result := by
  rfl

/-- The literal private owner callbacks commit exactly the complete actual native owner controller on the existing Main World. -/
theorem program_source (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (scalar : PqxdhJointGapDh.ScalarBytes)
    (credential : RegistrationNativeMldsa.Credential source) (roots : Roots)
    (work : RegistrationNativeBeaconFrontend.M n KemSK source RegistrationServerRoleBackend.State Value)
    (before : State n KemSK source)
    (allowed : (((work.run (RegistrationNativePublicSourceState.owners scalar before.1.beacons)).run before.1.environment)).AllQueriesSatisfy
      (RegistrationNativePublicSourceTrusted.Allowed (KemSK := KemSK))) :
    privateObserve roots before.1 <$>
      (simulateQ (RegistrationNativeOrdinaryFinishSourceNative.trusted setup wire route
        (RegistrationNativeMldsa.owned source credential) created.seed scalar)
        ((work.run (RegistrationNativePublicSourceState.owners scalar before.1.beacons)).run before.1.environment)).run
          (toPrivate before.2) =
      Prod.map id nativeView <$>
        (RegistrationNativeExperiment.beacon setup checks representation created work).run (restore roots scalar before.1 before.2) := by
  rw [← RegistrationNativePublicSourceBeacon.program_source setup checks wire route representation created scalar credential roots work before allowed]
  have native := RegistrationNativePublicSourceCallbacks.program_source setup wire route
    (RegistrationNativeMldsa.owned source credential) created.seed scalar false
    (simulateQ RegistrationBeaconReferenceCompiler.trustedLift
      ((work.run (RegistrationNativePublicSourceState.owners scalar before.1.beacons)).run before.1.environment)) before.2
  have mapped := congrArg (fun distribution => privateObserve roots before.1 <$> distribution) native
  simpa only [RegistrationNativeOrdinaryFinishSourceNative.trusted, QueryImpl.simulateQ_compose,
    Functor.map_map, Prod.map_def, id_eq, privateObserve, observe, drop, toPrivate, restore,
    RegistrationNativePublicSourceState.project, RegistrationServerMaterialSourceState.restore,
    RegistrationServerReferenceRestore.restore] using mapped.symm

end BeaconcryptCore.Computational.RegistrationNativePublicSourceOwnerWorld
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePublicSourceOwnerWorld.observe_record_view' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePublicSourceOwnerWorld.observe_record_view
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePublicSourceOwnerWorld.program_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePublicSourceOwnerWorld.program_source
