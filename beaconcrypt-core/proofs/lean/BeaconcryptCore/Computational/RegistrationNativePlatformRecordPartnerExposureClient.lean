-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureRoot
import BeaconcryptCore.Computational.RegistrationNativePlatformLorOpenDictionary
import BeaconcryptCore.Computational.RegistrationNativeSecretWordKemEarly
import BeaconcryptCore.Computational.RegistrationNativeSecretWordProtection
import BeaconcryptCore.Computational.RegistrationNativeSecretWordRecoveryCompiler
import BeaconcryptCore.Computational.RegistrationNativeSecretWordFrontendTrace
/-! The actual record-service recovery client keeps the source World interpreter and its complete persistent state, while protected material queries log their literal word through the ordinary Combined recovery interface. Its executable client has no candidate argument. Demand-operand normalization is exposed only by the separate analysis programWith parameter. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureClient
open PqxdhServerAuthExperiment (Setup)
open RegistrationNativeSecretWordMessage (Message)
open RegistrationNativeSecretWord (Key)
open RegistrationNativeSecretWordService (Combined)
open PqxdhRecordLiftInterface (WorldSpec)
variable {n : Nat} {I KemSK Physical A : Type} {base : OracleSpec I}
abbrev Roots (n : Nat) := RegistrationNativePlatformRecordPartnerExposureSlots.State n
abbrev Private (n : Nat) (KemSK Physical : Type) := (RegistrationNativeSecretWordInterpreter.State n KemSK ×Roots n) ×Physical
abbrev Shared (n : Nat) := RegistrationNativePlatformRecordPartnerExposureRoot.Spec n

noncomputable def closing (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (input : Message →Option Key) (inside : RegistrationNativeSuffixKeyPrf.Prefix →Bool) (operand : Message →Message) :
    QueryImpl (RegistrationNativePlatformLorOpenDictionary.Spec n) (StateT (Roots n) (OracleComp (Shared n)))
  | .inl query=>StateT.lift ((Shared n).query query)
  | .inr (.inl message)=>RegistrationNativePlatformRecordPartnerExposureRoot.handler source input inside (.inl message)
  | .inr (.inr message)=>RegistrationNativePlatformRecordPartnerExposureRoot.handler source input inside (.inr (operand message))

noncomputable def lowerWith (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest →ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (provider : RegistrationNativeSecretWordInterpreter.Provider KemSK) (operand : Message →Message) :
    QueryImpl (RegistrationNativeSecretWordInterface.Spec n KemSK)
      (StateT (RegistrationNativeSecretWordInterpreter.State n KemSK ×Roots n) (OracleComp (Shared n))) :=
  (QueryImpl.mapStateTBase
    (closing setup.source (RegistrationNativeSecretWordMessage.input setup.joint setup.dh seed scalar)
      (RegistrationNativeSecretWordProtection.inside (setup.joint.staticDh seed (setup.dh.publicKey scalar))) operand)
    (RegistrationNativePlatformLorOpenDictionary.handler setup wire sign
      (RegistrationNativeSecretWordMessage.input setup.joint setup.dh seed scalar)
      (RegistrationNativeSecretWordProtection.inside (setup.joint.staticDh seed (setup.dh.publicKey scalar))) provider)).flattenStateT

noncomputable def ambient (physical : QueryImpl (WorldSpec n) (StateT Physical ProbComp)) :
    QueryImpl (Shared n) (StateT Physical (OracleComp Combined))
  | .inl query=>StateT.lift (Combined.query query)
  | .inr query=>fun before=>simulateQ RegistrationNativeSecretWordService.coins ((physical query).run before)

noncomputable def implementationWith (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest →ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (provider : RegistrationNativeSecretWordInterpreter.Provider KemSK)
    (physical : QueryImpl (WorldSpec n) (StateT Physical ProbComp)) (operand : Message →Message) :
    QueryImpl (RegistrationNativeSecretWordInterface.Spec n KemSK) (StateT (Private n KemSK Physical) (OracleComp Combined)) :=
  (QueryImpl.mapStateTBase (ambient physical) (lowerWith setup wire sign seed scalar provider operand)).flattenStateT

noncomputable def programWith (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest →ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (provider : RegistrationNativeSecretWordInterpreter.Provider KemSK)
    (physical : QueryImpl (WorldSpec n) (StateT Physical ProbComp)) (operand : Message →Message)
    (work : OracleComp (RegistrationNativeSecretWordInterface.Spec n KemSK) A)
    (trace : RegistrationNativeSecretWordFrontendTrace.State) (before : Private n KemSK Physical) :=
  (simulateQ (implementationWith setup wire sign seed scalar provider physical operand)
    ((simulateQ RegistrationNativeSecretWordFrontendTrace.handler work).run trace)).run before

noncomputable def client (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest →ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (provider : RegistrationNativeSecretWordInterpreter.Provider KemSK)
    (physical : QueryImpl (WorldSpec n) (StateT Physical ProbComp))
    (work : OracleComp (RegistrationNativeSecretWordInterface.Spec n KemSK) A)
    (trace : RegistrationNativeSecretWordFrontendTrace.State) (before : Private n KemSK Physical) :=
  programWith setup wire sign seed scalar provider physical id work trace before

/-- The literal physical-service embedding retains its full state and forwards each World probability draw to the ordinary recovery coin surface. -/
theorem ambient_world (physical : QueryImpl (WorldSpec n) (StateT Physical ProbComp)) (work : OracleComp (WorldSpec n) A) (before : Physical) :
    (simulateQ (ambient physical) (simulateQ RegistrationNativePlatformRecordPartnerExposureRoot.world work)).run before=
      simulateQ RegistrationNativeSecretWordService.coins ((simulateQ physical work).run before) := by
  induction work using OracleComp.inductionOn generalizing before with
  | pure value=>simp only [simulateQ_pure,StateT.run_pure]
  | query_bind query next ih=>
    simp only [simulateQ_bind,simulateQ_spec_query,RegistrationNativePlatformRecordPartnerExposureRoot.world,
      ambient,StateT.run_bind,simulateQ_bind]
    exact bind_congr fun result=>ih result.1 result.2

/-- The proxy source dictionary factors through its exact open-controller tree with all source and opaque-cache coordinates retained. -/
theorem lower_run (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest →ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (provider : RegistrationNativeSecretWordInterpreter.Provider KemSK) (operand : Message →Message)
    (query : (RegistrationNativeSecretWordInterface.Spec n KemSK).Domain)
    (before : RegistrationNativeSecretWordInterpreter.State n KemSK ×Roots n) :
    (lowerWith setup wire sign seed scalar provider operand query).run before=
      (fun result=>(result.1.1,(result.1.2,result.2))) <$>
        (simulateQ (closing setup.source (RegistrationNativeSecretWordMessage.input setup.joint setup.dh seed scalar)
          (RegistrationNativeSecretWordProtection.inside (setup.joint.staticDh seed (setup.dh.publicKey scalar))) operand)
          ((RegistrationNativePlatformLorOpenDictionary.handler setup wire sign
            (RegistrationNativeSecretWordMessage.input setup.joint setup.dh seed scalar)
            (RegistrationNativeSecretWordProtection.inside (setup.joint.staticDh seed (setup.dh.publicKey scalar))) provider query).run before.1)).run before.2 :=
  QueryImpl.flattenStateT_mapStateTBase_apply_run _ _ _ _ _

end BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureClient
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureClient.ambient_world' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureClient.ambient_world

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureClient.lower_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureClient.lower_run
