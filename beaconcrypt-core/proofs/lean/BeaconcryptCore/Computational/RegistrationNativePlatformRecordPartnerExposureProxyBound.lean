-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureTraceProbability
import BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureDirectHierarchy
import BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureOpenLogMarginal
/-! The same full normalized physical proxy's installation exposure is bounded by its candidate-independent client's literal recovery hit, with an exact first-hit transition and no extra loss. -/
open OracleComp OracleSpec CoreModels
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureProxyBound
open PqxdhServerAuthExperiment (Setup)
open RegistrationNativeSecretWordMessage (Message)
open RegistrationNativeSuffixKeyPrf (Secret)
variable {n : Nat} {I KemSK Physical A : Type} {base : OracleSpec I}
variable (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (sign : beaconcrypt_core.registration.MldsaSigningRequest →ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (candidate : Secret) (filler : PqxdhServerAuthKeySchedule.Output)
    (selected : Nat) (pairs : List (PqxdhKemIndCca.MlKem768PublicKey ×KemSK))
    (publicKey : PqxdhKemIndCca.MlKem768PublicKey) (challenge : PqxdhKemIndCca.MlKem768Ciphertext)
    (physical : QueryImpl (PqxdhRecordLiftInterface.WorldSpec n) (StateT Physical ProbComp))
local notation "provider"=>RegistrationNativeSecretWordKemEarly.early setup.baseImpl setup.kem selected pairs publicKey challenge
local notation "input"=>RegistrationNativeSecretWordMessage.input setup.joint setup.dh seed scalar
local notation "inside"=>RegistrationNativeSecretWordProtection.inside (setup.joint.staticDh seed (setup.dh.publicKey scalar))
local notation "operand"=>RegistrationNativePlatformRecordPartnerExposureNormalize.message candidate
local notation "proxy"=>RegistrationNativePlatformRecordPartnerExposureClosedProjection.proxy setup wire sign seed scalar candidate filler selected pairs publicKey challenge physical
local notation "literals"=>RegistrationNativePlatformRecordPartnerExposureFirstHit.literals (n:=n) input inside
local notation "traceLiterals"=>RegistrationNativePlatformRecordPartnerExposureQueryLog.traceLiterals (n:=n) input inside
local notation "direct"=>RegistrationNativePlatformRecordPartnerExposureOpenMarginal.direct setup.source candidate filler physical input inside operand
local notation "normalized"=>RegistrationNativePlatformRecordPartnerExposureFirstHit.closing setup.source candidate physical input inside operand
local notation "independent"=>RegistrationNativePlatformRecordPartnerExposureFirstHit.closing setup.source candidate physical input inside id

/-- A protected installation exposure on this exact persistent source proxy is charged to the same complete independent recovery client. -/
theorem fixed (work : OracleComp (RegistrationNativeSecretWordInterface.Spec n KemSK) A)
    (before : RegistrationNativeSecretWordInterpreter.State n KemSK)
    (roots : RegistrationNativePlatformRecordPartnerExposureSlots.State n) (physicalBefore : Physical) :
    Pr{let result←(simulateQ (RegistrationNativePlatformLorStatefulSupport.trace proxy) work).run (RegistrationNativeSecretWordFrontendTrace.initial,((before,roots),physicalBefore))}[
        RegistrationNativeSecretWordAliasExposureBound.Exposure input inside candidate result.2.1]≤
    Pr{let result←(RegistrationNativeSecretWordRecoveryBound.logged setup.source candidate
      (RegistrationNativePlatformRecordPartnerExposureClient.client setup wire sign seed scalar provider physical work
        RegistrationNativeSecretWordFrontendTrace.initial ((before,roots),physicalBefore)))}[candidate∈result.2.2] := by
  rw [RegistrationNativePlatformRecordPartnerExposureDirectHierarchy.source,prEvent_map]
  let opened:=RegistrationNativePlatformRecordPartnerExposureClientHierarchy.opened setup wire sign seed scalar provider
    work RegistrationNativeSecretWordFrontendTrace.initial before
  have allowed : opened.AllQueriesSatisfy RegistrationNativePlatformRecordPartnerExposureDictionarySource.NoAmbient :=
    RegistrationNativePlatformRecordPartnerExposureDictionarySource.program_noAmbient setup wire sign seed scalar provider
      ((simulateQ RegistrationNativeSecretWordFrontendTrace.handler work).run RegistrationNativeSecretWordFrontendTrace.initial) before
  calc
    _ ≤ Pr{let result←(simulateQ direct opened).run (roots,physicalBefore)}[candidate∈traceLiterals result.1.1.2.events] :=
      RegistrationNativePlatformRecordPartnerExposureTraceProbability.exposure_le_demand setup wire sign seed scalar provider
        candidate direct work before (roots,physicalBefore)
    _ = Pr{let result←(simulateQ (RawCtxSelectedQueryTrace.recorded direct literals) opened).run ((roots,physicalBefore),[])}[candidate∈result.2.2] :=
      RegistrationNativePlatformRecordPartnerExposureTraceProbability.open_hit setup wire sign seed scalar provider
        candidate direct work before (roots,physicalBefore)
    _ = Pr{let result←(simulateQ (RawCtxSelectedQueryTrace.recorded normalized literals) opened).run ((roots,(∅,physicalBefore)),[])}[candidate∈result.2.2] :=
      (RegistrationNativePlatformRecordPartnerExposureOpenLogMarginal.hit_probability setup.source candidate filler physical
        input inside operand opened allowed ((roots,(∅,physicalBefore)),[])).symm
    _ = Pr{let result←(simulateQ (RawCtxSelectedQueryTrace.recorded independent literals) opened).run ((roots,(∅,physicalBefore)),[])}[candidate∈result.2.2] :=
      (RegistrationNativePlatformRecordPartnerExposureFirstHit.hit_probability setup seed scalar candidate physical opened
        (roots,(∅,physicalBefore))).symm
    _ = Pr{let result←(simulateQ (RegistrationNativeSecretWordRecoveryCompiler.closed setup.source candidate)
      (RegistrationNativePlatformRecordPartnerExposureClient.client setup wire sign seed scalar provider physical work
        RegistrationNativeSecretWordFrontendTrace.initial ((before,roots),physicalBefore))).run ∅}[
          candidate∈traceLiterals result.1.1.2.events] :=
      RegistrationNativePlatformRecordPartnerExposureTraceProbability.recovery_hit setup wire sign seed scalar provider
        candidate physical work before roots physicalBefore
    _ ≤ _ := RegistrationNativePlatformRecordPartnerExposureTraceProbability.client_logged setup wire sign seed scalar provider
      candidate physical work ((before,roots),physicalBefore)
end BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureProxyBound
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureProxyBound.fixed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureProxyBound.fixed
