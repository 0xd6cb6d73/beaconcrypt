-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeG3MaterializedTracedServer
import BeaconcryptCore.Computational.RegistrationNativeG3MaterializedTracedBeacon
import BeaconcryptCore.Computational.RegistrationNativeG3MaterializedOrdinary

/-! The concrete fixed-material comparison now runs through the actual typed frontend and its complete original raw/secrecy ledger. Server build and mixed Beacon finish consume their full guarded source equations; every other command has the literal translation identity. The sole state projection is the already proved accounting view, applied bilaterally. No whole-program simulation or cryptographic target hypothesis is supplied by a caller. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeG3MaterializedTracedProgram
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhRecordLiftInterface (Slot)
open PqxdhDeploymentHiddenLayout (Material)
open RegistrationNativeG3AuditedWorld (Seeds)
open RegistrationNativeG3MaterializedLocal (handler)
open RegistrationNativeG3LocalKeys (project)
variable {n : Nat} {ι KemSK ProviderState Reader Response Value : Type} {base : OracleSpec ι}
variable (table : Slot n → Material) (setup : Setup base KemSK) (codec : Codec Reader Response)
  (route : RawCtxServerRouting.SenderDecoder) (wire : RegistrationNativeWire.Wire)
  (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
  (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
  (candidate : PqxdhKemIndCca.MlKemSharedSecret)
  (provider : RegistrationNativeHiddenInterpreter.Provider KemSK ProviderState)

abbrev State (source : RegistrationNativeMldsa.Source) (n : Nat) (KemSK ProviderState : Type) :=
  (RegistrationNativePublicFrontend.State source × RegistrationNativeG2Trace.State) × RegistrationNativeG3LocalKeys.State n KemSK ProviderState

def frame {source : RegistrationNativeMldsa.Source} (before : State source n KemSK ProviderState) :
    State source n KemSK ProviderState := (before.1, project before.2)

noncomputable def frontend (source : RegistrationNativeMldsa.Source) (checks : Checks)
    (selectedOwner selectedAccept : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding) :
    QueryImpl RegistrationNativeRawAdapter.TypedSpec
      (StateT (RegistrationNativePublicFrontend.State source × RegistrationNativeG2Trace.State)
        (OracleComp (RegistrationNativePublicFrontend.Spec n KemSK))) :=
  (RegistrationNativeG2Trace.handler.mapStateTBase
    (RegistrationNativePublicFrontend.handler setup checks wire source sign selectedOwner selectedAccept publicPrekey)).flattenStateT

noncomputable def typed (source : RegistrationNativeMldsa.Source) (checks : Checks)
    (selectedOwner selectedAccept : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
    (full : Bool) (seeds : Seeds n) :
    QueryImpl RegistrationNativeRawAdapter.TypedSpec (StateT (State source n KemSK ProviderState) ProbComp) :=
  ((handler full table seeds setup codec route wire sign seed scalar candidate provider).mapStateTBase
    (frontend setup wire sign source checks selectedOwner selectedAccept publicPrekey)).flattenStateT

private theorem projected (full : Bool) (seeds : Seeds n)
    (work : OracleComp (RegistrationNativePublicFrontend.Spec n KemSK) Value)
    (before : RegistrationNativeG3LocalKeys.State n KemSK ProviderState) :
    Prod.map id project <$>
      (simulateQ (handler full table seeds setup codec route wire sign seed scalar candidate provider) work).run before =
      (simulateQ (handler full table seeds setup codec route wire sign seed scalar candidate provider) work).run (project before) := by
  simpa only [handler, QueryImpl.simulateQ_compose] using
    RegistrationNativeG3MaterializedLocalKeys.fixed_program_project table setup codec route wire sign seed scalar candidate provider
      (simulateQ (RegistrationNativeG3MaterializedLocal.translate full seeds) work) before

private theorem local_query (source : RegistrationNativeMldsa.Source) (checks : Checks)
    (selectedOwner selectedAccept : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
    (seeds : Seeds n) (query : RegistrationNativeRawAdapter.TypedSpec.Domain)
    (frontend : RegistrationNativePublicFrontend.State source) (trace : RegistrationNativeG2Trace.State) (before : RegistrationNativeG3LocalKeys.State n KemSK ProviderState) :
    (simulateQ (handler true table seeds setup codec route wire sign seed scalar candidate provider)
      ((simulateQ RegistrationNativeG2Trace.handler
        ((RegistrationNativePublicFrontend.handler setup checks wire source sign selectedOwner selectedAccept publicPrekey query).run frontend)).run trace)).run (project before) =
      (simulateQ (handler false table seeds setup codec route wire sign seed scalar candidate provider)
        ((simulateQ RegistrationNativeG2Trace.handler
        ((RegistrationNativePublicFrontend.handler setup checks wire source sign selectedOwner selectedAccept publicPrekey query).run frontend)).run trace)).run (project before) := by
  by_cases ordinary : RegistrationNativeG3MaterializedOrdinary.Ordinary query
  · simp only [handler, QueryImpl.simulateQ_compose]
    rw [RegistrationNativeG3MaterializedOrdinary.observed_handler_source true seeds setup checks wire source sign selectedOwner selectedAccept publicPrekey query frontend ordinary trace,
      RegistrationNativeG3MaterializedOrdinary.observed_handler_source false seeds setup checks wire source sign selectedOwner selectedAccept publicPrekey query frontend ordinary trace]
  · cases query with
    | inl coin => exact (ordinary trivial).elim
    | inr command => cases command with
      | build handle application =>
          exact RegistrationNativeG3MaterializedTracedServer.typed_build table setup codec route wire sign seed scalar candidate provider source seeds
            checks selectedOwner selectedAccept publicPrekey handle application frontend trace before
      | finish index packet =>
          exact RegistrationNativeG3MaterializedTracedBeacon.typed_finish table setup codec route wire sign seed scalar candidate provider source seeds
            checks selectedOwner selectedAccept publicPrekey index packet frontend trace before
      | _ => exact (ordinary trivial).elim

/-- Every actual typed command has the same complete fixed-material source after the derived bilateral accounting projection. -/
theorem query_source (source : RegistrationNativeMldsa.Source) (checks : Checks)
    (selectedOwner selectedAccept : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
    (seeds : Seeds n) (query : RegistrationNativeRawAdapter.TypedSpec.Domain)
    (before : State source n KemSK ProviderState) :
    Prod.map id frame <$>
      (typed table setup codec route wire sign seed scalar candidate provider source checks selectedOwner selectedAccept publicPrekey true seeds query).run before =
      (typed table setup codec route wire sign seed scalar candidate provider source checks selectedOwner selectedAccept publicPrekey false seeds query).run (frame before) := by
  rcases before with ⟨⟨front, trace⟩, current⟩
  have sourceEq := (projected table setup codec route wire sign seed scalar candidate provider true seeds
    ((simulateQ RegistrationNativeG2Trace.handler
        ((RegistrationNativePublicFrontend.handler setup checks wire source sign selectedOwner selectedAccept publicPrekey query).run front)).run trace) current).trans
    (local_query table setup codec route wire sign seed scalar candidate provider source checks selectedOwner selectedAccept publicPrekey seeds query front trace current)
  have associated := congrArg (Functor.map (fun result => (result.1.1.1, ((result.1.1.2, result.1.2), result.2)))) sourceEq
  simpa only [typed, frontend, QueryImpl.flattenStateT_mapStateTBase_apply_run, simulateQ_map, StateT.run_map, frame,
    Functor.map_map, Prod.map_def, id_eq, Function.comp_def] using associated

/-- Arbitrary adaptive typed programs retain their full frontend, both receipts, private provider state and semantic World through fixed materialization. -/
theorem program_source (source : RegistrationNativeMldsa.Source) (checks : Checks)
    (selectedOwner selectedAccept : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
    (seeds : Seeds n) (work : OracleComp RegistrationNativeRawAdapter.TypedSpec Value)
    (before : State source n KemSK ProviderState) :
    Prod.map id frame <$>
      (simulateQ (typed table setup codec route wire sign seed scalar candidate provider source checks selectedOwner selectedAccept publicPrekey true seeds) work).run before =
      (simulateQ (typed table setup codec route wire sign seed scalar candidate provider source checks selectedOwner selectedAccept publicPrekey false seeds) work).run (frame before) :=
  OracleComp.map_run_simulateQ_eq_of_query_map_eq _ _ frame
    (query_source table setup codec route wire sign seed scalar candidate provider source checks selectedOwner selectedAccept publicPrekey seeds) work before

/-- The literal original nested frontend observer retains its complete source trace and private state through fixed materialization. -/
theorem frontend_source (source : RegistrationNativeMldsa.Source) (checks : Checks)
    (selectedOwner selectedAccept : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
    (seeds : Seeds n) (work : OracleComp RegistrationNativeRawAdapter.TypedSpec Value)
    (front : RegistrationNativePublicFrontend.State source) (trace : RegistrationNativeG2Trace.State)
    (before : RegistrationNativeG3LocalKeys.State n KemSK ProviderState) :
    Prod.map id project <$>
      (simulateQ (handler true table seeds setup codec route wire sign seed scalar candidate provider)
        ((simulateQ RegistrationNativeG2Trace.handler
          ((simulateQ (RegistrationNativePublicFrontend.handler setup checks wire source sign selectedOwner selectedAccept publicPrekey)
            work).run front)).run trace)).run before =
      (simulateQ (handler false table seeds setup codec route wire sign seed scalar candidate provider)
        ((simulateQ RegistrationNativeG2Trace.handler
          ((simulateQ (RegistrationNativePublicFrontend.handler setup checks wire source sign selectedOwner selectedAccept publicPrekey)
            work).run front)).run trace)).run (project before) := by
  simp only [OracleComp.simulateQ_mapStateTBase_run_eq_map_flattenStateT RegistrationNativeG2Trace.handler
    (RegistrationNativePublicFrontend.handler setup checks wire source sign selectedOwner selectedAccept publicPrekey) work front trace,
    simulateQ_map, StateT.run_map, Functor.map_map]
  rw [OracleComp.simulateQ_mapStateTBase_run_eq_map_flattenStateT,
    OracleComp.simulateQ_mapStateTBase_run_eq_map_flattenStateT]
  have associated := congrArg (Functor.map (fun result => (((result.1, result.2.1.1), result.2.1.2), result.2.2)))
    (program_source table setup codec route wire sign seed scalar candidate provider source checks selectedOwner selectedAccept publicPrekey seeds
      work ((front, trace), before))
  simpa only [typed, frontend, frame, Functor.map_map, Prod.map_def, id_eq, Function.comp_def] using associated

/-- The original complete native ledger retains all private hidden/fresh draws and public raw replies under the same derived materialized source, without a target or whole-source premise. -/
theorem run_source (source : RegistrationNativeMldsa.Source) (checks : Checks)
    (selectedOwner selectedAccept : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
    (seeds : Seeds n) (serverKeyId : U64) (bounds : PqxdhDeploymentInterface.FreshBounds)
    (mode : PqxdhDeploymentInterface.Mode) (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (before : State source n KemSK ProviderState) :
    Prod.map id (Prod.map id frame) <$>
      RegistrationNativeFullCompiler.run setup.source.crypto wire serverKeyId bounds
        (typed table setup codec route wire sign seed scalar candidate provider source checks selectedOwner selectedAccept publicPrekey true seeds) mode work before =
      RegistrationNativeFullCompiler.run setup.source.crypto wire serverKeyId bounds
        (typed table setup codec route wire sign seed scalar candidate provider source checks selectedOwner selectedAccept publicPrekey false seeds) mode work (frame before) := by
  rw [RegistrationNativeFullCompiler.compile_run, RegistrationNativeFullCompiler.compile_run]
  have associated := congrArg (Functor.map (fun result => (result.1.1, (result.1.2, result.2))))
    (program_source table setup codec route wire sign seed scalar candidate provider source checks selectedOwner selectedAccept publicPrekey seeds
      (RegistrationNativeFullCompiler.compile setup.source.crypto wire serverKeyId bounds mode work) before)
  simpa only [Functor.map_map, Prod.map_def, id_eq, Function.comp_def] using associated

end BeaconcryptCore.Computational.RegistrationNativeG3MaterializedTracedProgram
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3MaterializedTracedProgram.query_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3MaterializedTracedProgram.query_source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3MaterializedTracedProgram.program_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3MaterializedTracedProgram.program_source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3MaterializedTracedProgram.run_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3MaterializedTracedProgram.run_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3MaterializedTracedProgram.frontend_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3MaterializedTracedProgram.frontend_source
