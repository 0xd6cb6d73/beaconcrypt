-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureDictionarySource
import BeaconcryptCore.Computational.RegistrationNativePlatformLorCtxClosed
import BeaconcryptCore.Computational.RegistrationNativePlatformLorSourcePreparedTraceCore
/-! Source dictionary projection commutes with the actual persistent physical service and the literal Word chronology. Only the native prepared shadow and its selected address representation are projected; every returned value, physical transition and source private coordinate is retained. -/
open OracleComp OracleSpec CoreModels
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureClosedProjection
open PqxdhServerAuthExperiment (Setup)
open RegistrationNativeSecretWordInterface (Spec)
open RegistrationNativePlatformRecordPartnerExposureExtract (Image)
open RegistrationNativePlatformRecordPartnerExposureDictionarySource (Ready)
variable {n : Nat} {I KemSK Physical : Type} {base : OracleSpec I}
abbrev Source (n : Nat) (KemSK Physical : Type) := RegistrationNativePlatformLorCtxLeaves.Symbolic n KemSK ×Physical
abbrev Target (n : Nat) (KemSK Physical : Type) := RegistrationNativePlatformRecordPartnerExposureClient.Private n KemSK Physical
def project (candidate : PqxdhKemIndCca.MlKemSharedSecret) (before : Source n KemSK Physical) : Target n KemSK Physical :=
  (RegistrationNativePlatformRecordPartnerExposureDictionarySource.project candidate before.1,before.2)
def traceProject (candidate : PqxdhKemIndCca.MlKemSharedSecret)
    (before : RegistrationNativeSecretWordFrontendTrace.State ×Source n KemSK Physical) :=
  (before.1,project candidate before.2)

variable (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (sign : beaconcrypt_core.registration.MldsaSigningRequest →ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret) (filler : PqxdhServerAuthKeySchedule.Output)
    (unused : QueryImpl RegistrationNativeSecretWordService.Combined (OracleComp (PqxdhRecordLiftInterface.WorldSpec n)))
    (selected : Nat) (pairs : List (PqxdhKemIndCca.MlKem768PublicKey ×KemSK))
    (publicKey : PqxdhKemIndCca.MlKem768PublicKey) (challenge : PqxdhKemIndCca.MlKem768Ciphertext)
    (physical : QueryImpl (PqxdhRecordLiftInterface.WorldSpec n) (StateT Physical ProbComp))
local notation "provider"=>RegistrationNativeSecretWordKemEarly.early setup.baseImpl setup.kem selected pairs publicKey challenge
local notation "native"=>RegistrationNativePlatformLorCtxClosed.implementation setup wire sign seed scalar candidate unused selected pairs publicKey challenge physical
local notation "lower"=>RegistrationNativePlatformRecordPartnerExposureClient.lowerWith setup wire sign seed scalar provider
  (RegistrationNativePlatformRecordPartnerExposureNormalize.message candidate)
local notation "realize"=>RegistrationNativePlatformRecordPartnerExposureRootSource.realization (n := n) setup.source candidate filler

noncomputable def proxy : QueryImpl (Spec n KemSK) (StateT (Target n KemSK Physical) ProbComp) :=
  (QueryImpl.mapStateTBase physical (QueryImpl.mapStateTBase realize lower)).flattenStateT

/-- Exact source query projection keeps the same arbitrary physical World transition. -/
theorem query (request : (Spec n KemSK).Domain) (before : Source n KemSK Physical)
    (image : Image candidate before.1.2) (ready : Ready setup seed scalar candidate request before.1.2) :
    Prod.map id (project candidate) <$> (native request).run before=
      (proxy setup wire sign seed scalar candidate filler selected pairs publicKey challenge physical request).run (project candidate before) := by
  have source := RegistrationNativePlatformRecordPartnerExposureDictionarySource.query setup wire sign seed scalar candidate filler unused provider request before.1 image ready
  have observed := congrArg (fun tree=>(simulateQ physical tree).run before.2) source
  have reassociated := congrArg (Functor.map (fun result=>(result.1.1,(result.1.2,result.2)))) observed
  rcases before with ⟨nativeBefore,physicalBefore⟩
  simpa only [RegistrationNativePlatformLorCtxClosed.implementation,proxy,
    QueryImpl.flattenStateT_mapStateTBase_apply_run,QueryImpl.mapStateTBase,StateT.run_mk,
    simulateQ_map,StateT.run_map,Functor.map_map,project,Prod.map_def,id_eq] using reassociated

include filler in
/-- Every actual closed source result retains the internally derived opaque-address image. -/
theorem image (request : (Spec n KemSK).Domain) (before : Source n KemSK Physical)
    (image : Image candidate before.1.2) (ready : Ready setup seed scalar candidate request before.1.2)
    (result : (Spec n KemSK).Range request ×Source n KemSK Physical)
    (supported : result∈support ((native request).run before)) : Image candidate result.2.1.2 := by
  rw [RegistrationNativePlatformLorCtxClosed.implementation,QueryImpl.flattenStateT_mapStateTBase_apply_run,support_map] at supported
  obtain ⟨⟨reached,physicalAfter⟩,called,equal⟩ := supported
  cases equal
  apply RegistrationNativePlatformRecordPartnerExposureDictionarySource.image setup wire sign seed scalar candidate filler unused provider request before.1 image ready reached
  apply OracleComp.support_simulateQ_run'_subset physical _ before.2
  rw [StateT.run'_eq,support_map]
  exact Set.mem_image_of_mem Prod.fst called

private theorem map_apply {S X Y : Type} {m : Type →Type} [Monad m] [LawfulMonad m]
    (f : X →Y) (work : StateT S m X) (before : S) :
    (f <$>work) before=Prod.map f id <$>work before := StateT.run_map _ _ _

private theorem trace_run {Private : Type} (implementation : QueryImpl (Spec n KemSK) (StateT Private ProbComp))
    (request : (Spec n KemSK).Domain) (before : RegistrationNativeSecretWordFrontendTrace.State ×Private) :
    (RegistrationNativePlatformLorStatefulSupport.trace implementation request).run before=
      (fun result=>(result.1,(RegistrationNativeSecretWordFrontendTrace.finish request result.1
        (RegistrationNativeSecretWordFrontendTrace.begin request before.1),result.2))) <$>
        (implementation request).run before.2 := by
  rw [RegistrationNativePlatformLorStatefulSupport.trace,QueryImpl.flattenStateT_mapStateTBase_apply_run]
  simp only [RegistrationNativeSecretWordFrontendTrace.handler,StateT.run,simulateQ_map,simulateQ_spec_query,
    map_apply,Functor.map_map,Prod.map_def,id_eq]

/-- The literal Word trace sees the same original query and reply on both projected source executions. -/
theorem trace_query (request : (Spec n KemSK).Domain)
    (before : RegistrationNativeSecretWordFrontendTrace.State ×Source n KemSK Physical)
    (image : Image candidate before.2.1.2) (ready : Ready setup seed scalar candidate request before.2.1.2) :
    Prod.map id (traceProject candidate) <$> (RegistrationNativePlatformLorStatefulSupport.trace native request).run before=
      (RegistrationNativePlatformLorStatefulSupport.trace (proxy setup wire sign seed scalar candidate filler selected pairs publicKey challenge physical) request).run
        (traceProject candidate before) := by
  rw [trace_run,trace_run]
  have mapped := congrArg (Functor.map (fun result=>(result.1,(RegistrationNativeSecretWordFrontendTrace.finish request result.1
    (RegistrationNativeSecretWordFrontendTrace.begin request before.1),result.2))))
    (query setup wire sign seed scalar candidate filler unused selected pairs publicKey challenge physical request before.2 image ready)
  simpa only [Functor.map_map,Prod.map_def,traceProject,id_eq] using mapped

include filler in
/-- Observing the source chronology preserves the same reached native image invariant. -/
theorem trace_image (request : (Spec n KemSK).Domain)
    (before : RegistrationNativeSecretWordFrontendTrace.State ×Source n KemSK Physical)
    (held : Image candidate before.2.1.2) (ready : Ready setup seed scalar candidate request before.2.1.2)
    (result : (Spec n KemSK).Range request ×(RegistrationNativeSecretWordFrontendTrace.State ×Source n KemSK Physical))
    (supported : result∈support ((RegistrationNativePlatformLorStatefulSupport.trace native request).run before)) : Image candidate result.2.2.1.2 :=
  image setup wire sign seed scalar candidate filler unused selected pairs publicKey challenge physical request before.2 held ready
    (result.1,result.2.2) (RegistrationNativePlatformLorSourceKemTrace.query_support native request before result supported)

end BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureClosedProjection
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureClosedProjection.query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureClosedProjection.query

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureClosedProjection.image' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureClosedProjection.image

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureClosedProjection.trace_query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureClosedProjection.trace_query

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureClosedProjection.trace_image' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureClosedProjection.trace_image
