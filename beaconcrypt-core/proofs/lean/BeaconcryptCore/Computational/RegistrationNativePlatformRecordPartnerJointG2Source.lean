-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerSlotTraceSource
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerJointG2Source
open PqxdhServerAuthExperiment (Setup)
variable {n : Nat} {I KemSK ProviderState Physical A : Type} {base : OracleSpec I}
/-- Dropping only the slot ghost retains the exact nested original native/G2 interpretation, every private state and the complete reached physical state. -/
theorem source (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest →ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret)
    (provider : RegistrationNativeHiddenInterpreter.Provider KemSK ProviderState)
    (physical : QueryImpl (PqxdhRecordLiftInterface.WorldSpec n) (StateT Physical ProbComp))
    (work : OracleComp (RegistrationNativePublicFrontend.Spec n KemSK) A)
    (privateBefore : RegistrationNativeSelectiveHiddenInterpreter.State n KemSK ProviderState) (physicalBefore : Physical)
    (slots : RegistrationNativePlatformPublicRecordSlots.State n) (trace : RegistrationNativeG2Trace.State) :
    (fun result=>(((result.1,result.2.2.1),result.2.2.2.1),result.2.2.2.2)) <$>
      (simulateQ (RegistrationNativePlatformRecordPartnerSlotTrace.handler setup wire sign seed scalar candidate provider physical) work).run
        (slots,trace,(privateBefore,physicalBefore))=
      (simulateQ physical ((simulateQ
        (RegistrationNativeSelectiveHiddenInterpreter.handler setup wire sign seed scalar candidate provider)
        ((simulateQ RegistrationNativeG2Trace.handler work).run trace)).run privateBefore)).run physicalBefore := by
  have same:=RegistrationNativePlatformRecordPartnerSlotTrace.trace_source setup wire sign seed scalar candidate provider physical work
    (slots,trace,(privateBefore,physicalBefore))
  have mapped:=congrArg (Functor.map (fun result : A×(RegistrationNativeG2Trace.State×
      (RegistrationNativeSelectiveHiddenInterpreter.State n KemSK ProviderState×Physical))=>
    (((result.1,result.2.1),result.2.2.1),result.2.2.2))) same
  rw [QueryImpl.Stateful.simulateQ_link_run,RegistrationNativePlatformRecordPartnerSlotInput.closed,
    OracleComp.simulateQ_flattenStateT_run,←QueryImpl.simulateQ_mapStateTBase_run] at mapped
  simp only [Functor.map_map,bind_pure_comp] at mapped
  simpa only [Prod.map_def,id_eq,QueryImpl.Stateful.Frame.prod,
    PFunctor.Lens.State.fst,PFunctor.Lens.State.snd,PFunctor.Lens.State.mk_put,id_map'] using mapped
end BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerJointG2Source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerJointG2Source.source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerJointG2Source.source
