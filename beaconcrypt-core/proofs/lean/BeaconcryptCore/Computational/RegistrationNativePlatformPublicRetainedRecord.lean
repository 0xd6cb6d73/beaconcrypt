-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicRetained
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicWorldObservation
import BeaconcryptCore.Computational.RegistrationNativePlatformRetainedCoinEmbedding
/-! The root-valued source intermediate relocates private roots while retaining a terminal data observation of its locally interpreted World. The observation contains actual CTX cache, crypto-produced-stage frames and raw counters, never private root-memo entries or record chains. Full material still reaches this intermediate compiler; opaque-slot relocation remains separate. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicRetainedRecord
open PqxdhServerAuthExperiment (Setup)
open RegistrationNativePlatformPublicWorldObservation (RecordView recordView)
open RegistrationNativePublicRetained (clear project)
open RegistrationNativePlatformPublicRetained (source retained compiler)
variable {n : Nat} {I KemSK Value : Type} {base : OracleSpec I}
variable (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : beaconcrypt_core.registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)

noncomputable def client (work : OracleComp (RegistrationNativePlatformPublicFrontend.Spec n KemSK) Value)
    (before : RegistrationNativePublicInterpreter.State n KemSK) :
    OracleComp RegistrationNativeRetainedService.Spec (Value × RecordView) :=
  (fun result => (result.1, recordView result.2.world)) <$>
    (simulateQ (compiler setup wire route sign) work).run (clear before)

/-- The actual complete source computation preserves its terminal record-data fields when root bookkeeping moves to the retained service. -/
theorem client_source (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (work : OracleComp (RegistrationNativePlatformPublicFrontend.Spec n KemSK) Value)
    (before : RegistrationNativePublicInterpreter.State n KemSK) (cache : PqxdhSecretInputKdf.HmacOracle.QueryCache) :
    (simulateQ (RegistrationNativeRootCacheProjection.implementation setup.source setup.hmac setup.joint setup.dh seed scalar)
      ((fun result => (result.1, recordView result.2.world)) <$>
        (simulateQ (RegistrationNativePlatformPublicSourceExecution.handler setup wire route sign) work).run before)).run' cache =
      (simulateQ (RegistrationNativeRetainedSource.implementation setup.source setup.hmac
        (RegistrationNativeRelatedFamily.input setup.joint setup.dh seed scalar)
        (RegistrationNativeKeyFamilyPreparation.inside (setup.joint.staticDh seed (setup.dh.publicKey scalar))))
        (client setup wire route sign work before)).run' (before.roots, cache) := by
  have projected := congrArg (fun game => (fun result => (result.1, recordView result.2.1.world)) <$> game)
    (RegistrationNativePlatformPublicRetained.program_project setup wire route sign seed scalar work (before, cache))
  simp only [source, retained, project, StateT.run'_eq, simulateQ_map, StateT.run_map,
    Functor.map_map, Prod.map, id_eq, client, clear, RegistrationNativePublicRootFrame.replace] at projected ⊢
  rw [OracleComp.simulateQ_mapStateTBase_run_eq_map_flattenStateT,
    OracleComp.simulateQ_mapStateTBase_run_eq_map_flattenStateT]
  simpa only [Functor.map_map, Prod.map, id_eq] using projected

private theorem record_project (before : RegistrationNativePublicInterpreter.State n KemSK) :
    recordView (RegistrationNativePlatformPublicCoinView.project before).world = recordView before.world := rfl

/-- The exact external-coin embedding retains this whole terminal observation for every future material-service interpretation. Its accounting projection is invisible in the proved data-valued view. -/
theorem embedded (work : OracleComp (RegistrationNativePlatformPublicFrontend.Spec n KemSK) Value)
    (before : RegistrationNativePublicInterpreter.State n KemSK) :
    client setup wire route sign work before =
      (fun result => (result.1, recordView result.2.world)) <$>
        (simulateQ (RegistrationNativePublicRetained.compiler setup wire route sign)
          (simulateQ RegistrationNativePlatformPublicCoinEmbedding.embed work)).run
            (clear before) := by
  have sourceLaw := RegistrationNativePlatformRetainedCoinEmbedding.program setup wire route sign work (clear before)
  have observed := congrArg (fun action => (fun result => (result.1, recordView result.2.world)) <$> action) sourceLaw
  simpa only [client, Functor.map_map, Prod.map, id_eq, record_project] using observed
end BeaconcryptCore.Computational.RegistrationNativePlatformPublicRetainedRecord

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicRetainedRecord.client_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicRetainedRecord.client_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicRetainedRecord.embedded' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicRetainedRecord.embedded
