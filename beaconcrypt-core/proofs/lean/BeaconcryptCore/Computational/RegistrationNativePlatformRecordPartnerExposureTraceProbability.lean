-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureQueryLog
import BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureClientHierarchy
import BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureClientHistory
import BeaconcryptCore.Computational.RegistrationNativeSecretWordAliasExposureBound
/-! The original chronological demand event, the open input recorder and the executable client's ordinary recovery log remain on the same complete execution. These are fixed-candidate probability laws, without a new security or source-law premise. -/
open OracleComp OracleSpec CoreModels
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureTraceProbability
open PqxdhServerAuthExperiment (Setup)
open RegistrationNativeSecretWordMessage (Message)
open RegistrationNativeSecretWord (Key Cache)
open RegistrationNativeSuffixKeyPrf (Secret)
open RegistrationNativeSecretWordFrontendTrace (Event)
variable {n : Nat} {I KemSK Physical Private A : Type} {base : OracleSpec I}
variable (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (sign : beaconcrypt_core.registration.MldsaSigningRequest →ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (provider : RegistrationNativeSecretWordInterpreter.Provider KemSK)
local notation "input"=>RegistrationNativeSecretWordMessage.input setup.joint setup.dh seed scalar
local notation "inside"=>RegistrationNativeSecretWordProtection.inside (setup.joint.staticDh seed (setup.dh.publicKey scalar))
local notation "opened"=>RegistrationNativePlatformRecordPartnerExposureClientHierarchy.opened setup wire sign seed scalar provider
local notation "literals"=>RegistrationNativePlatformRecordPartnerExposureFirstHit.literals (n:=n) input inside
local notation "traceLiterals"=>RegistrationNativePlatformRecordPartnerExposureQueryLog.traceLiterals (n:=n) input inside

/-- The literal list of the same final Word trace has exactly the open recorder's hit mass. -/
theorem open_hit (candidate : Secret)
    (close : QueryImpl (RegistrationNativePlatformLorOpenDictionary.Spec n) (StateT Private ProbComp))
    (work : OracleComp (RegistrationNativeSecretWordInterface.Spec n KemSK) A)
    (wordBefore : RegistrationNativeSecretWordInterpreter.State n KemSK) (before : Private) :
    Pr{let result←(simulateQ close (opened work RegistrationNativeSecretWordFrontendTrace.initial wordBefore)).run before}[
      candidate∈traceLiterals result.1.1.2.events]=
    Pr{let result←(simulateQ (RawCtxSelectedQueryTrace.recorded close literals)
      (opened work RegistrationNativeSecretWordFrontendTrace.initial wordBefore)).run (before,[])}[candidate∈result.2.2] := by
  rw [←RawCtxSelectedQueryTrace.complete close literals
    (opened work RegistrationNativeSecretWordFrontendTrace.initial wordBefore) (before,[]),prEvent_map]
  apply prEvent_congr_of_support
  intro result supported
  have source := RegistrationNativePlatformRecordPartnerExposureQueryLog.source setup wire sign input inside provider
    close work RegistrationNativeSecretWordFrontendTrace.initial wordBefore (before,[]) []
    (by simp [RegistrationNativeSecretWordFrontendTrace.initial,
      RegistrationNativePlatformRecordPartnerExposureQueryLog.traceLiterals]) result supported
  simpa only [List.nil_append,Prod.map_fst,id_eq] using (congrArg (fun values=>candidate∈values) source.symm).to_iff

/-- A protected literal installation or attempt has its same descriptor in the original demand trace. -/
theorem exposure_le_demand (candidate : Secret)
    (close : QueryImpl (RegistrationNativePlatformLorOpenDictionary.Spec n) (StateT Private ProbComp))
    (work : OracleComp (RegistrationNativeSecretWordInterface.Spec n KemSK) A)
    (wordBefore : RegistrationNativeSecretWordInterpreter.State n KemSK) (before : Private) :
    Pr{let result←(simulateQ close (opened work RegistrationNativeSecretWordFrontendTrace.initial wordBefore)).run before}[
      RegistrationNativeSecretWordAliasExposureBound.Exposure input inside candidate result.1.1.2]≤
    Pr{let result←(simulateQ close (opened work RegistrationNativeSecretWordFrontendTrace.initial wordBefore)).run before}[
      candidate∈traceLiterals result.1.1.2.events] := by
  apply prEvent_mono_of_support
  intro result supported exposed
  have sourceMember : result.1∈support (opened work RegistrationNativeSecretWordFrontendTrace.initial wordBefore) := by
    apply OracleComp.support_simulateQ_run'_subset close _ before
    rw [StateT.run'_eq,support_map]
    exact Set.mem_image_of_mem Prod.fst supported
  have traceMember : result.1.1∈support (RegistrationNativeSecretWordFrontendTrace.program work) := by
    apply OracleComp.support_simulateQ_run'_subset
      (RegistrationNativePlatformLorOpenDictionary.handler setup wire sign input inside provider) _ wordBefore
    rw [StateT.run'_eq,support_map]
    exact Set.mem_image_of_mem Prod.fst sourceMember
  have valid := RegistrationNativeSecretWordAtomTraceDemand.program work RegistrationNativeSecretWordFrontendTrace.initial
    (by simp [RegistrationNativeSecretWordAtomTraceDemand.Holds,RegistrationNativeSecretWordFrontendTrace.initial])
    result.1.1 traceMember
  obtain ⟨role,message,key,member,formed,protectedInput,literal⟩:=exposed
  apply (RegistrationNativePlatformRecordPartnerExposureQueryLog.mem_trace input inside candidate result.1.1.2.events).mpr
  refine ⟨message,key,?_,formed,protectedInput,literal⟩
  rcases member with installed|attempted
  · exact valid.2 (.install role message) installed message (List.mem_singleton_self _)
  · exact valid.2 (.installAttempt role message) attempted message (List.mem_singleton_self _)

/-- The independent open recorder and the executable client retain the same literal-demand hit probability. -/
theorem recovery_hit (candidate : Secret)
    (physical : QueryImpl (PqxdhRecordLiftInterface.WorldSpec n) (StateT Physical ProbComp))
    (work : OracleComp (RegistrationNativeSecretWordInterface.Spec n KemSK) A)
    (wordBefore : RegistrationNativeSecretWordInterpreter.State n KemSK)
    (roots : RegistrationNativePlatformRecordPartnerExposureSlots.State n) (physicalBefore : Physical) :
    Pr{let result←(simulateQ (RawCtxSelectedQueryTrace.recorded
      (RegistrationNativePlatformRecordPartnerExposureFirstHit.closing setup.source candidate physical input inside id) literals)
      (opened work RegistrationNativeSecretWordFrontendTrace.initial wordBefore)).run ((roots,(∅,physicalBefore)),[])}[
      candidate∈result.2.2]=
    Pr{let result←(simulateQ (RegistrationNativeSecretWordRecoveryCompiler.closed setup.source candidate)
      (RegistrationNativePlatformRecordPartnerExposureClient.client setup wire sign seed scalar provider physical work
        RegistrationNativeSecretWordFrontendTrace.initial ((wordBefore,roots),physicalBefore))).run ∅}[
      candidate∈traceLiterals result.1.1.2.events] := by
  rw [←open_hit setup wire sign seed scalar provider candidate]
  unfold RegistrationNativePlatformRecordPartnerExposureClient.client
  rw [RegistrationNativePlatformRecordPartnerExposureClientHierarchy.recovery_source,prEvent_map]

/-- Every actual demand hit in the executable client's output enters its own complete ordinary recovery log. -/
theorem client_logged (candidate : Secret)
    (physical : QueryImpl (PqxdhRecordLiftInterface.WorldSpec n) (StateT Physical ProbComp))
    (work : OracleComp (RegistrationNativeSecretWordInterface.Spec n KemSK) A)
    (before : RegistrationNativePlatformRecordPartnerExposureClient.Private n KemSK Physical) :
    Pr{let result←(simulateQ (RegistrationNativeSecretWordRecoveryCompiler.closed setup.source candidate)
      (RegistrationNativePlatformRecordPartnerExposureClient.client setup wire sign seed scalar provider physical work
        RegistrationNativeSecretWordFrontendTrace.initial before)).run ∅}[
      candidate∈traceLiterals result.1.1.2.events]≤
    Pr{let result←(RegistrationNativeSecretWordRecoveryBound.logged setup.source candidate
      (RegistrationNativePlatformRecordPartnerExposureClient.client setup wire sign seed scalar provider physical work
        RegistrationNativeSecretWordFrontendTrace.initial before))}[candidate∈result.2.2] := by
  rw [←RawCtxSelectedQueryTrace.complete (RegistrationNativeSecretWordRecoveryCompiler.closed setup.source candidate)
    RegistrationNativeSecretWordRecoveryCompiler.literals
    (RegistrationNativePlatformRecordPartnerExposureClient.client setup wire sign seed scalar provider physical work
      RegistrationNativeSecretWordFrontendTrace.initial before) (∅,[]),prEvent_map]
  apply prEvent_mono_of_support
  intro result supported hit
  obtain ⟨message,key,member,formed,protectedInput,literal⟩:=
    (RegistrationNativePlatformRecordPartnerExposureQueryLog.mem_trace input inside candidate result.1.1.2.events).mp hit
  exact RegistrationNativePlatformRecordPartnerExposureClientHistory.demands_logged setup wire sign seed scalar provider physical
    candidate work before result supported message key member formed protectedInput literal

end BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureTraceProbability
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureTraceProbability.open_hit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureTraceProbability.open_hit
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureTraceProbability.exposure_le_demand' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureTraceProbability.exposure_le_demand
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureTraceProbability.client_logged' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureTraceProbability.client_logged

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureTraceProbability.recovery_hit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureTraceProbability.recovery_hit
