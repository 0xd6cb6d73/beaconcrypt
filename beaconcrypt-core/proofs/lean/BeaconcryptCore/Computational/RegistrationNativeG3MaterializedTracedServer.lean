-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeG3MaterializedInterfaceDiagram
import BeaconcryptCore.Computational.RegistrationNativeG3MaterializedTracedServerCurrentEnv

/-! The actual guarded fixed-material Server build consumes the complete current-Env materialization equation. The independent private publication receipts remain in the same private state, while inlined signatures update only the current frontend Env receipts. Every failure and moved-handle outcome is retained under the proved accounting projection. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeG3MaterializedTracedServer
open PqxdhServerAuthExperiment (Setup Codec Checks)
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


/-- The exact actual local Server build retains its complete chronological G2 observer through known108/public44 materialization. -/
theorem build (seeds : Seeds n) (checks : Checks) (handle : Nat) (application : Option (Slice U8))
    (control : RegistrationServerMaterialFrontend.State) (env : RegistrationServerReferenceCompiler.Environment)
    (trace : RegistrationNativeG2Trace.State) (before : State n KemSK ProviderState) :
    (simulateQ (handler true table seeds setup codec route wire sign seed scalar candidate provider)
      ((simulateQ RegistrationNativeG2Trace.handler (simulateQ (RegistrationNativePublicFrontend.liftLocal false)
        (((RegistrationServerOpenReferenceCompiler.build setup.source wire checks sign handle application).run control).run env))).run trace)).run (project before) =
      (simulateQ (handler false table seeds setup codec route wire sign seed scalar candidate provider)
        ((simulateQ RegistrationNativeG2Trace.handler (simulateQ (RegistrationNativePublicFrontend.liftLocal false)
          (((RegistrationServerOpenReferenceCompiler.build setup.source wire checks sign handle application).run control).run env))).run trace)).run (project before) := by
  have allowed := RegistrationNativeG3MaterializedTracedServerFootprint.build_allowed (n := n) (KemSK := KemSK)
    setup.source wire checks sign handle application control env
  simp only [RegistrationNativeG3MaterializedTracedServerTrace.program_source _ allowed trace]
  have materialized := RegistrationNativeG3MaterializedTracedServerCurrentEnv.build setup.source wire checks sign seeds
    (service table setup seed scalar candidate) (fallback table setup codec route wire sign seed scalar candidate provider)
    handle application control env trace (view before)
  have observed := congrArg (Functor.map (Prod.map id RegistrationNativeG3MaterializedLocalCommon.project)) materialized
  change Prod.map id RegistrationNativeG3MaterializedLocalCommon.project <$>
      (simulateQ (RegistrationNativeG3MaterializedInterfaceDiagram.implementation table setup codec route wire sign seed scalar candidate provider true seeds)
        ((simulateQ RegistrationNativeG3MaterializedTracedServerTrace.handler
          (((RegistrationServerOpenReferenceCompiler.build setup.source wire checks sign handle application).run control).run env)).run trace)).run (view before) =
    Prod.map id RegistrationNativeG3MaterializedLocalCommon.project <$>
      (simulateQ (RegistrationNativeG3MaterializedInterfaceDiagram.implementation table setup codec route wire sign seed scalar candidate provider false seeds)
        ((simulateQ RegistrationNativeG3MaterializedTracedServerTrace.handler
          (((RegistrationServerOpenReferenceCompiler.build setup.source wire checks sign handle application).run control).run env)).run trace)).run (view before) at observed
  rw [← local_source, ← local_source] at observed
  have restored := congrArg (Functor.map (Prod.map id restore)) observed
  simpa only [Functor.map_map, Prod.map_def, id_eq, Function.comp_def,
    RegistrationNativeG3MaterializedState.restore_view, id_map'] using restored

/-- The literal typed native build dispatcher preserves the original chronological G2 trace and complete frontend/private state. -/
theorem typed_build (source : RegistrationNativeMldsa.Source) (seeds : Seeds n)
    (checks : Checks) (selectedOwner selectedAccept : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
    (handle : Nat) (application : Option (Slice U8))
    (frontend : RegistrationNativePublicFrontend.State source) (trace : RegistrationNativeG2Trace.State)
    (before : State n KemSK ProviderState) :
    (simulateQ (handler true table seeds setup codec route wire sign seed scalar candidate provider)
      ((simulateQ RegistrationNativeG2Trace.handler
        ((RegistrationNativePublicFrontend.handler setup checks wire source sign selectedOwner selectedAccept publicPrekey
          (.inr (.build handle application))).run frontend)).run trace)).run (project before) =
      (simulateQ (handler false table seeds setup codec route wire sign seed scalar candidate provider)
        ((simulateQ RegistrationNativeG2Trace.handler
          ((RegistrationNativePublicFrontend.handler setup checks wire source sign selectedOwner selectedAccept publicPrekey
            (.inr (.build handle application))).run frontend)).run trace)).run (project before) := by
  simp only [RegistrationNativePublicFrontend.handler, RegistrationNativePublicFrontend.serverOpen, StateT.run,
    simulateQ_map, map_apply]
  have same := build table setup codec route wire sign seed scalar candidate provider seeds checks handle application
    frontend.server frontend.environment trace before
  simp only [StateT.run] at same
  rw [same]

end BeaconcryptCore.Computational.RegistrationNativeG3MaterializedTracedServer

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3MaterializedTracedServer.build' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3MaterializedTracedServer.build

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3MaterializedTracedServer.typed_build' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3MaterializedTracedServer.typed_build
