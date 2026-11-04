-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerSlotTrace
/-! The common ordered slot/descriptor observer is the exact persistent closing of the existing public-slot and G2 observers. Only product association changes; dropping the slot observer recovers the original complete G2 execution. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerSlotTrace
open PqxdhServerAuthExperiment (Setup)
open RegistrationNativeHiddenInterpreter (Provider)
open RegistrationNativePublicFrontend (Spec)
variable {n : Nat} {I KemSK ProviderState Physical A : Type} {base : OracleSpec I}
variable (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (sign : beaconcrypt_core.registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret) (provider : Provider KemSK ProviderState)
    (physical : QueryImpl (PqxdhRecordLiftInterface.WorldSpec n) (StateT Physical ProbComp))
local notation "backend" => RegistrationNativePlatformRecordPartnerSlotInput.closed setup wire sign seed scalar candidate provider physical
local notation "actual" => handler setup wire sign seed scalar candidate provider physical

private theorem bind_apply {S X Y : Type} {m : Type → Type} [Monad m]
    (work : StateT S m X) (next : X → StateT S m Y) (before : S) :
    (work >>= next) before=(do let result ← work before; next result.1 result.2) := rfl

/-- The joint observer is exactly the existing two observers closed by the same persistent physical interpreter, retaining every poststate. -/
theorem program_source (work : OracleComp (Spec n KemSK) A) (before : State n KemSK ProviderState Physical) :
    (simulateQ actual work).run before =
      (fun reached=>(reached.1.1.1,(reached.1.2,reached.1.1.2,reached.2))) <$>
        (simulateQ backend (RegistrationNativePlatformPublicRecordSlots.program
          ((simulateQ RegistrationNativeG2Trace.handler work).run before.2.1) before.1)).run before.2.2 := by
  induction work using OracleComp.inductionOn generalizing before with
  | pure value =>
      simp only [simulateQ_pure,StateT.run_pure,RegistrationNativePlatformPublicRecordSlots.program,map_pure]
  | query_bind query next ih =>
      simp only [simulateQ_bind,simulateQ_spec_query,handler,
        RegistrationNativePlatformPublicRecordSlots.program,RegistrationNativePlatformPublicRecordSlots.handler,
        RegistrationNativeG2Trace.handler,StateT.run,bind_apply,map_bind,bind_map_left]
      apply bind_congr
      intro reached
      exact ih reached.1 (RegistrationNativePlatformPublicRecordSlots.step query reached.1 before.1,
        RegistrationNativeG2Trace.finish query reached.1 (RegistrationNativeG2Trace.begin query before.2.1),reached.2)

/-- Erasing only the opaque slot observer gives the exact original G2 trace, native private state and physical state. -/
theorem trace_source (work : OracleComp (Spec n KemSK) A) (before : State n KemSK ProviderState Physical) :
    Prod.map id (fun current=>(current.2.1,current.2.2)) <$> (simulateQ actual work).run before =
      (simulateQ (QueryImpl.Stateful.link RegistrationNativeG2Trace.handler backend) work).run (before.2.1,before.2.2) := by
  rw [program_source setup wire sign seed scalar candidate provider physical]
  have erased := congrArg (fun tree=>(simulateQ backend tree).run before.2.2)
    (RegistrationNativePlatformPublicRecordSlots.program_erase
      ((simulateQ RegistrationNativeG2Trace.handler work).run before.2.1) before.1)
  simp only [simulateQ_map,StateT.run_map] at erased
  rw [QueryImpl.Stateful.simulateQ_link_run]
  rw [←erased]
  simp only [Functor.map_map]
  rfl

end BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerSlotTrace

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerSlotTrace.program_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerSlotTrace.program_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerSlotTrace.trace_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerSlotTrace.trace_source
