-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeG3MaterializedInterfaceDiagram
import BeaconcryptCore.Computational.RegistrationNativeG3MaterializedTracedOwners
import BeaconcryptCore.Computational.RegistrationNativeG3MaterializedTracedBeaconRebracket

/-! The complete mixed Beacon finish with its original chronological G2 observer consumes the concrete fixed-material callback diagram. The known108 and material44/reference paths have identical actual guarded outcomes under the named accounting projection. Both chronological receipt coordinates, every owner and all private key/provider state remain literal; no cache, unused-role or prefix-state invariant is supplied by a caller. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeG3MaterializedTracedBeacon
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

private def unresult {Key Value : Type} (reached : Value × RegistrationNativeG3MaterializedTracedServerFrontend.State n Key) :
    (Value × RegistrationNativeG2Trace.State) × RegistrationNativeG3MaterializedFrontend.State n Key :=
  ((reached.1, reached.2.2.1), (reached.2.1, reached.2.2.2))

private theorem finite_finish (source : RegistrationNativeMldsa.Source) (seeds : Seeds n)
    (index : Nat) (packet : Option registration.ResponsePacket) (owners : RegistrationNativePublicOwners.State source)
    (env : RegistrationServerReferenceCompiler.Environment) (trace : RegistrationNativeG2Trace.State)
    (before : RegistrationNativeG3MaterializedState.View n KemSK ProviderState) :
    (simulateQ (RegistrationNativeG3MaterializedInterfaceDiagram.implementation table setup codec route wire sign seed scalar candidate provider true seeds)
      ((simulateQ RegistrationNativeG3MaterializedTracedBeaconTrace.handler
        (((RegistrationNativePublicOwners.finish setup source index packet).run owners).run env)).run trace)).run before =
    (simulateQ (RegistrationNativeG3MaterializedInterfaceDiagram.implementation table setup codec route wire sign seed scalar candidate provider false seeds)
      ((simulateQ RegistrationNativeG3MaterializedTracedBeaconTrace.handler
        (((RegistrationNativePublicOwners.finish setup source index packet).run owners).run env)).run trace)).run before := by
  let implementation := fallback table setup codec route wire sign seed scalar candidate provider
  let work := (((RegistrationNativePublicOwners.finish (n := n) setup source index packet).run owners).run env)
  have materialized := RegistrationNativeG3MaterializedTracedOwners.finish setup source wire.frameWrite sign seeds
    (service table setup seed scalar candidate)
    (RegistrationNativeG3MaterializedTracedBeaconRebracket.fallback implementation)
    index packet owners env (RegistrationNativeG3MaterializedTracedBeaconRebracket.join trace before)
  have first := RegistrationNativeG3MaterializedTracedBeaconRebracket.program_source true setup.source wire.frameWrite sign seeds
    (service table setup seed scalar candidate) implementation work trace before
  have second := RegistrationNativeG3MaterializedTracedBeaconRebracket.program_source false setup.source wire.frameWrite sign seeds
    (service table setup seed scalar candidate) implementation work trace before
  have same := first.trans (materialized.trans second.symm)
  have restored := congrArg (Functor.map unresult) same
  simpa only [RegistrationNativeG3MaterializedInterfaceDiagram.implementation, work, implementation, Functor.map_map, unresult, RegistrationNativeG3MaterializedTracedBeaconRebracket.result,
    RegistrationNativeG3MaterializedTracedBeaconRebracket.join, Prod.map_def, Function.comp_def, id_eq, id_map'] using restored

/-- The actual mixed-owner finish preserves the complete original G2 trace and all source fields through known108/public44 materialization. -/
theorem finish (source : RegistrationNativeMldsa.Source) (seeds : Seeds n)
    (index : Nat) (packet : Option registration.ResponsePacket) (owners : RegistrationNativePublicOwners.State source)
    (env : RegistrationServerReferenceCompiler.Environment) (trace : RegistrationNativeG2Trace.State)
    (before : State n KemSK ProviderState) :
    (simulateQ (handler true table seeds setup codec route wire sign seed scalar candidate provider)
      ((simulateQ RegistrationNativeG2Trace.handler (simulateQ (RegistrationNativePublicFrontend.liftLocal false)
        (((RegistrationNativePublicOwners.finish setup source index packet).run owners).run env))).run trace)).run (project before) =
    (simulateQ (handler false table seeds setup codec route wire sign seed scalar candidate provider)
      ((simulateQ RegistrationNativeG2Trace.handler (simulateQ (RegistrationNativePublicFrontend.liftLocal false)
        (((RegistrationNativePublicOwners.finish setup source index packet).run owners).run env))).run trace)).run (project before) := by
  simp only [RegistrationNativeG3MaterializedTracedBeaconTrace.program_source]
  have materialized := finite_finish table setup codec route wire sign seed scalar candidate provider source seeds index packet owners env trace (view before)
  have observed := congrArg (Functor.map (Prod.map id RegistrationNativeG3MaterializedLocalCommon.project)) materialized
  rw [← local_source, ← local_source] at observed
  have restored := congrArg (Functor.map (Prod.map id restore)) observed
  simpa only [Functor.map_map, Prod.map_def, id_eq, Function.comp_def,
    RegistrationNativeG3MaterializedState.restore_view, id_map'] using restored

/-- The actual typed native finish dispatcher retains its complete original chronological G2 trace and source output. -/
theorem typed_finish (source : RegistrationNativeMldsa.Source) (seeds : Seeds n)
    (checks : PqxdhServerAuthExperiment.Checks) (selectedOwner selectedAccept : Nat)
    (publicPrekey : PqxdhJointIdentity.PeerEncoding) (index : Nat) (packet : Option registration.ResponsePacket)
    (frontend : RegistrationNativePublicFrontend.State source) (trace : RegistrationNativeG2Trace.State)
    (before : State n KemSK ProviderState) :
    (simulateQ (handler true table seeds setup codec route wire sign seed scalar candidate provider)
      ((simulateQ RegistrationNativeG2Trace.handler
        ((RegistrationNativePublicFrontend.handler setup checks wire source sign selectedOwner selectedAccept publicPrekey
          (.inr (.finish index packet))).run frontend)).run trace)).run (project before) =
    (simulateQ (handler false table seeds setup codec route wire sign seed scalar candidate provider)
      ((simulateQ RegistrationNativeG2Trace.handler
        ((RegistrationNativePublicFrontend.handler setup checks wire source sign selectedOwner selectedAccept publicPrekey
          (.inr (.finish index packet))).run frontend)).run trace)).run (project before) := by
  simp only [RegistrationNativePublicFrontend.handler, RegistrationNativePublicFrontend.beacon, StateT.run,
    simulateQ_map, map_apply]
  have same := finish table setup codec route wire sign seed scalar candidate provider source seeds index packet frontend.beacons frontend.environment trace before
  simp only [StateT.run] at same
  rw [same]

end BeaconcryptCore.Computational.RegistrationNativeG3MaterializedTracedBeacon
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3MaterializedTracedBeacon.finish' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3MaterializedTracedBeacon.finish
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3MaterializedTracedBeacon.typed_finish' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3MaterializedTracedBeacon.typed_finish
