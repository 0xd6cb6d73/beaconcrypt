-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeG3MaterializedInterfaceDiagram

/-! The complete mixed Beacon finish now consumes the concrete fixed-material callback diagram. The known108 and material44/reference paths have identical actual guarded outcomes under the named accounting projection. Both chronological receipt coordinates, every owner and all private key/provider state remain literal; no cache, unused-role or prefix-state invariant is supplied by a caller. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeG3MaterializedFixedBeacon
open PqxdhServerAuthExperiment (Setup Codec)
open PqxdhRecordLiftInterface (Slot)
open PqxdhDeploymentHiddenLayout (Material)
open RegistrationNativeG3AuditedWorld (Seeds)
open RegistrationNativeG3LocalKeys (State project)
open RegistrationNativeG3MaterializedState (view restore)
open RegistrationNativeG3MaterializedLocal (handler service fallback)
variable {n : Nat} {ι KemSK ProviderState Reader Response Value : Type} {base : OracleSpec ι}
variable (table : Slot n → Material) (setup : Setup base KemSK) (codec : Codec Reader Response)
  (route : RawCtxServerRouting.SenderDecoder) (wire : RegistrationNativeWire.Wire)
  (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
  (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
  (candidate : PqxdhKemIndCca.MlKemSharedSecret)
  (provider : RegistrationNativeHiddenInterpreter.Provider KemSK ProviderState)

private theorem map_apply {S A B : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (f : A → B) (work : StateT S m A) (before : S) :
    (f <$> work) before = Prod.map f id <$> work before := StateT.run_map f work before

private theorem local_source (full : Bool) (seeds : Seeds n)
    (work : OracleComp (RegistrationBeaconReferenceCompiler.Spec n KemSK) Value)
    (before : State n KemSK ProviderState) :
    Prod.map id view <$>
      (simulateQ (handler full table seeds setup codec route wire sign seed scalar candidate provider)
        (simulateQ (RegistrationNativePublicFrontend.liftLocal false) work)).run (project before) =
      Prod.map id RegistrationNativeG3MaterializedLocalCommon.project <$>
        (simulateQ (RegistrationNativeG3MaterializedInterfaceDiagram.implementation table setup codec route wire sign seed scalar candidate provider full seeds)
          work).run (view before) := by
  rw [RegistrationNativeG3MaterializedLocalSource.actual_program]
  exact (RegistrationNativeG3MaterializedInterfaceDiagram.program_source table setup codec route wire sign seed scalar candidate provider
    full seeds work (view before)).symm

/-- The literal actual guarded mixed-owner finish has the same full outcomes with known108 or public44 material and fixed canonical installations, from the derived projected input. -/
theorem finish (source : RegistrationNativeMldsa.Source) (seeds : Seeds n)
    (index : Nat) (packet : Option registration.ResponsePacket) (owners : RegistrationNativePublicOwners.State source)
    (env : RegistrationServerReferenceCompiler.Environment) (before : State n KemSK ProviderState) :
    (simulateQ (handler true table seeds setup codec route wire sign seed scalar candidate provider)
      (simulateQ (RegistrationNativePublicFrontend.liftLocal false)
        (((RegistrationNativePublicOwners.finish setup source index packet).run owners).run env))).run (project before) =
      (simulateQ (handler false table seeds setup codec route wire sign seed scalar candidate provider)
        (simulateQ (RegistrationNativePublicFrontend.liftLocal false)
          (((RegistrationNativePublicOwners.finish setup source index packet).run owners).run env))).run (project before) := by
  have materialized := RegistrationNativeG3MaterializedOwners.finish setup source wire.frameWrite sign seeds
    (service table setup seed scalar candidate) (fallback table setup codec route wire sign seed scalar candidate provider)
    index packet owners env (view before)
  have observed := congrArg (Functor.map (Prod.map id RegistrationNativeG3MaterializedLocalCommon.project)) materialized
  change Prod.map id RegistrationNativeG3MaterializedLocalCommon.project <$>
      (simulateQ (RegistrationNativeG3MaterializedInterfaceDiagram.implementation table setup codec route wire sign seed scalar candidate provider true seeds)
        (((RegistrationNativePublicOwners.finish setup source index packet).run owners).run env)).run (view before) =
    Prod.map id RegistrationNativeG3MaterializedLocalCommon.project <$>
      (simulateQ (RegistrationNativeG3MaterializedInterfaceDiagram.implementation table setup codec route wire sign seed scalar candidate provider false seeds)
        (((RegistrationNativePublicOwners.finish setup source index packet).run owners).run env)).run (view before) at observed
  rw [← local_source, ← local_source] at observed
  have restored := congrArg (Functor.map (Prod.map id restore)) observed
  simpa only [Functor.map_map, Prod.map_def, id_eq, Function.comp_def,
    RegistrationNativeG3MaterializedState.restore_view, id_map'] using restored

/-- The same concrete source equation holds at the actual typed finish dispatcher, retaining the complete frontend state and its independent environment receipts. -/
theorem typed_finish (source : RegistrationNativeMldsa.Source) (seeds : Seeds n)
    (checks : PqxdhServerAuthExperiment.Checks) (selectedOwner selectedAccept : Nat)
    (publicPrekey : PqxdhJointIdentity.PeerEncoding) (index : Nat) (packet : Option registration.ResponsePacket)
    (frontend : RegistrationNativePublicFrontend.State source) (before : State n KemSK ProviderState) :
    (simulateQ (handler true table seeds setup codec route wire sign seed scalar candidate provider)
      ((RegistrationNativePublicFrontend.handler setup checks wire source sign selectedOwner selectedAccept publicPrekey
        (.inr (.finish index packet))).run frontend)).run (project before) =
      (simulateQ (handler false table seeds setup codec route wire sign seed scalar candidate provider)
        ((RegistrationNativePublicFrontend.handler setup checks wire source sign selectedOwner selectedAccept publicPrekey
          (.inr (.finish index packet))).run frontend)).run (project before) := by
  simp only [RegistrationNativePublicFrontend.handler, RegistrationNativePublicFrontend.beacon, StateT.run,
    simulateQ_map, map_apply]
  have same := finish table setup codec route wire sign seed scalar candidate provider source seeds index packet frontend.beacons frontend.environment before
  simp only [StateT.run] at same
  rw [same]

end BeaconcryptCore.Computational.RegistrationNativeG3MaterializedFixedBeacon
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3MaterializedFixedBeacon.finish' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3MaterializedFixedBeacon.finish
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3MaterializedFixedBeacon.typed_finish' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3MaterializedFixedBeacon.typed_finish
