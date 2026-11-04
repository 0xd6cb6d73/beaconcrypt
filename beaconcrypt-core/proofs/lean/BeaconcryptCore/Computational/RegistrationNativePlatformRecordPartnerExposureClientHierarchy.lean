-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureClientExecution
/-! The candidate-independent client and its root/recovery/physical analysis hierarchy differ only by product association. The complete Word-private state and chronological observer remain joint with all opaque-root, recovery and physical state. -/
open OracleComp OracleSpec CoreModels
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureClientHierarchy
open PqxdhServerAuthExperiment (Setup)
open RegistrationNativeSecretWordMessage (Message)
open RegistrationNativeSecretWord (Cache)
open RegistrationNativePlatformRecordPartnerExposureClient (Shared Roots)
variable {n : Nat} {I KemSK Physical A : Type} {base : OracleSpec I}
variable (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (sign : beaconcrypt_core.registration.MldsaSigningRequest →ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (provider : RegistrationNativeSecretWordInterpreter.Provider KemSK)

noncomputable def opened (work : OracleComp (RegistrationNativeSecretWordInterface.Spec n KemSK) A)
    (trace : RegistrationNativeSecretWordFrontendTrace.State) (before : RegistrationNativeSecretWordInterpreter.State n KemSK) :=
  (simulateQ (RegistrationNativePlatformLorOpenDictionary.handler setup wire sign
    (RegistrationNativeSecretWordMessage.input setup.joint setup.dh seed scalar)
    (RegistrationNativeSecretWordProtection.inside (setup.joint.staticDh seed (setup.dh.publicKey scalar))) provider)
    ((simulateQ RegistrationNativeSecretWordFrontendTrace.handler work).run trace)).run before

noncomputable def staged (operand : Message →Message) (work : OracleComp (RegistrationNativeSecretWordInterface.Spec n KemSK) A)
    (trace : RegistrationNativeSecretWordFrontendTrace.State) (before : RegistrationNativeSecretWordInterpreter.State n KemSK) (roots : Roots n) :=
  (simulateQ (RegistrationNativePlatformRecordPartnerExposureClient.closing setup.source
    (RegistrationNativeSecretWordMessage.input setup.joint setup.dh seed scalar)
    (RegistrationNativeSecretWordProtection.inside (setup.joint.staticDh seed (setup.dh.publicKey scalar))) operand)
    (opened setup wire sign seed scalar provider work trace before)).run roots

/-- The actual full client factors through its identical open dictionary and ambient World tree, retaining all state coordinates. -/
theorem staged_source (physical : QueryImpl (PqxdhRecordLiftInterface.WorldSpec n) (StateT Physical ProbComp))
    (operand : Message →Message) (work : OracleComp (RegistrationNativeSecretWordInterface.Spec n KemSK) A)
    (trace : RegistrationNativeSecretWordFrontendTrace.State) (before : RegistrationNativeSecretWordInterpreter.State n KemSK)
    (roots : Roots n) (physicalBefore : Physical) :
    RegistrationNativePlatformRecordPartnerExposureClient.programWith setup wire sign seed scalar provider physical operand work trace ((before,roots),physicalBefore)=
      (fun result=>(result.1.1.1,((result.1.1.2,result.1.2),result.2))) <$>
        (simulateQ (RegistrationNativePlatformRecordPartnerExposureClient.ambient physical)
          (staged setup wire sign seed scalar provider operand work trace before roots)).run physicalBefore := by
  unfold RegistrationNativePlatformRecordPartnerExposureClient.programWith
    RegistrationNativePlatformRecordPartnerExposureClient.implementationWith
    RegistrationNativePlatformRecordPartnerExposureClient.lowerWith staged opened
  rw [OracleComp.simulateQ_flattenStateT_run,←QueryImpl.simulateQ_mapStateTBase_run,bind_pure_comp]
  rw [OracleComp.simulateQ_flattenStateT_run,←QueryImpl.simulateQ_mapStateTBase_run,bind_pure_comp]
  simp only [simulateQ_map,StateT.run_map,Functor.map_map]
/-- Ordinary recovery closes that exact open tree while retaining its cache jointly with every actual private and physical field. -/
theorem recovery_source (candidate : RegistrationNativeSuffixKeyPrf.Secret)
    (physical : QueryImpl (PqxdhRecordLiftInterface.WorldSpec n) (StateT Physical ProbComp))
    (operand : Message →Message) (work : OracleComp (RegistrationNativeSecretWordInterface.Spec n KemSK) A)
    (trace : RegistrationNativeSecretWordFrontendTrace.State) (before : RegistrationNativeSecretWordInterpreter.State n KemSK)
    (roots : Roots n) (physicalBefore : Physical) (cache : Cache) :
    (simulateQ (RegistrationNativeSecretWordRecoveryCompiler.closed setup.source candidate)
      (RegistrationNativePlatformRecordPartnerExposureClient.programWith setup wire sign seed scalar provider physical operand work trace
        ((before,roots),physicalBefore))).run cache=
      (fun result=>((result.1.1,((result.1.2,result.2.1),result.2.2.2)),result.2.2.1)) <$>
        (simulateQ (RegistrationNativePlatformRecordPartnerExposureFirstHit.closing setup.source candidate physical
          (RegistrationNativeSecretWordMessage.input setup.joint setup.dh seed scalar)
          (RegistrationNativeSecretWordProtection.inside (setup.joint.staticDh seed (setup.dh.publicKey scalar))) operand)
          (opened setup wire sign seed scalar provider work trace before)).run (roots,(cache,physicalBefore)) := by
  rw [staged_source,simulateQ_map,StateT.run_map,
    RegistrationNativePlatformRecordPartnerExposureClientExecution.ambient_program]
  unfold staged
  rw [RegistrationNativePlatformRecordPartnerExposureClientExecution.root_program]
  simp only [Functor.map_map]
end BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureClientHierarchy
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureClientHierarchy.staged_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureClientHierarchy.staged_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureClientHierarchy.recovery_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureClientHierarchy.recovery_source
