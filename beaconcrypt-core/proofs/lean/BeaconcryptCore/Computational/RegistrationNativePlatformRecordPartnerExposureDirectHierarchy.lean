-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureOpenMarginal
import BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureClientHierarchy
import BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureClosedProjection
/-! The normalized proxy's literal Word chronology and its direct open-source physical hierarchy have the same complete result. Only product association changes; no source/private/cache coordinate is omitted. -/
open OracleComp OracleSpec CoreModels
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureDirectHierarchy
open PqxdhServerAuthExperiment (Setup)
open RegistrationNativeSecretWordMessage (Message)
variable {n : Nat} {I KemSK Physical A : Type} {base : OracleSpec I}
variable (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (sign : beaconcrypt_core.registration.MldsaSigningRequest →ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret) (filler : PqxdhServerAuthKeySchedule.Output)
    (selected : Nat) (pairs : List (PqxdhKemIndCca.MlKem768PublicKey ×KemSK))
    (publicKey : PqxdhKemIndCca.MlKem768PublicKey) (challenge : PqxdhKemIndCca.MlKem768Ciphertext)
    (physical : QueryImpl (PqxdhRecordLiftInterface.WorldSpec n) (StateT Physical ProbComp))
local notation "provider"=>RegistrationNativeSecretWordKemEarly.early setup.baseImpl setup.kem selected pairs publicKey challenge
local notation "proxy"=>RegistrationNativePlatformRecordPartnerExposureClosedProjection.proxy setup wire sign seed scalar candidate filler selected pairs publicKey challenge physical
local notation "input"=>RegistrationNativeSecretWordMessage.input setup.joint setup.dh seed scalar
local notation "inside"=>RegistrationNativeSecretWordProtection.inside (setup.joint.staticDh seed (setup.dh.publicKey scalar))
local notation "operand"=>RegistrationNativePlatformRecordPartnerExposureNormalize.message candidate

/-- The actual proxy Word interpreter retains its same chronological return, private frame and physical state on the direct open-source tree. -/
theorem source (work : OracleComp (RegistrationNativeSecretWordInterface.Spec n KemSK) A)
    (trace : RegistrationNativeSecretWordFrontendTrace.State) (before : RegistrationNativeSecretWordInterpreter.State n KemSK)
    (roots : RegistrationNativePlatformRecordPartnerExposureSlots.State n) (physicalBefore : Physical) :
    (simulateQ (RegistrationNativePlatformLorStatefulSupport.trace proxy) work).run (trace,((before,roots),physicalBefore))=
      (fun result=>(result.1.1.1,(result.1.1.2,((result.1.2,result.2.1),result.2.2)))) <$>
        (simulateQ (RegistrationNativePlatformRecordPartnerExposureOpenMarginal.direct setup.source candidate filler physical input inside operand)
          (RegistrationNativePlatformRecordPartnerExposureClientHierarchy.opened setup wire sign seed scalar provider work trace before)).run (roots,physicalBefore) := by
  rw [RegistrationNativePlatformLorStatefulSupport.trace_program,
    RegistrationNativePlatformRecordPartnerExposureOpenMarginal.program_source]
  unfold RegistrationNativePlatformRecordPartnerExposureClosedProjection.proxy
    RegistrationNativePlatformRecordPartnerExposureClientHierarchy.opened
  rw [OracleComp.simulateQ_flattenStateT_run,←QueryImpl.simulateQ_mapStateTBase_run,bind_pure_comp]
  rw [←QueryImpl.simulateQ_mapStateTBase_run]
  unfold RegistrationNativePlatformRecordPartnerExposureClient.lowerWith
  rw [OracleComp.simulateQ_flattenStateT_run,←QueryImpl.simulateQ_mapStateTBase_run,bind_pure_comp]
  simp only [simulateQ_map,StateT.run_map,Functor.map_map]

end BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureDirectHierarchy
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureDirectHierarchy.source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureDirectHierarchy.source
