-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSelectiveHiddenDictionaryRun
/-! Equal returned opaque slots identify the same complete source input through the actual persistent dictionary. Arbitrary physical World interpretation retains its full poststate; the proof compares neither roots nor material values. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerSlotInput
open PqxdhServerAuthExperiment (Setup)
open RegistrationNativeHiddenInterpreter (Provider)
open RegistrationNativeSelectiveHiddenInterpreter (State handler)
open RegistrationNativeSelectiveHiddenDictionaryRun (Good)
variable {n : Nat} {I KemSK ProviderState Physical Value : Type} {base : OracleSpec I}
variable (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (sign : beaconcrypt_core.registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret) (provider : Provider KemSK ProviderState)
    (physical : QueryImpl (PqxdhRecordLiftInterface.WorldSpec n) (StateT Physical ProbComp))
local notation "actual" => handler setup wire sign seed scalar candidate provider
local notation "PublicSpec" => RegistrationNativePublicFrontend.Spec n KemSK
local notation "Input" => RegistrationNativeRelatedFamily.input setup.joint setup.dh seed scalar
local notation "Selected" => RegistrationNativeSelectiveHiddenService.selected
  (RegistrationNativeKeyFamilyPreparation.inside (setup.joint.staticDh seed (setup.dh.publicKey scalar))) candidate

noncomputable def closed : QueryImpl (RegistrationNativePublicFrontend.Spec n KemSK)
    (StateT (State n KemSK ProviderState × Physical) ProbComp) :=
  (QueryImpl.mapStateTBase physical actual).flattenStateT

private theorem query_support (query : (RegistrationNativePublicFrontend.Spec n KemSK).Domain) (before : State n KemSK ProviderState × Physical)
    (result : (RegistrationNativePublicFrontend.Spec n KemSK).Range query × (State n KemSK ProviderState × Physical))
    (supported : result ∈ support ((closed setup wire sign seed scalar candidate provider physical query).run before)) :
    (result.1,result.2.1) ∈ support ((actual query).run before.1) := by
  rw [closed,QueryImpl.flattenStateT_mapStateTBase_apply_run,support_map] at supported
  obtain ⟨reached,called,equal⟩ := supported
  cases equal
  apply OracleComp.support_simulateQ_run'_subset physical _ before.2
  rw [StateT.run'_eq,support_map]
  exact Set.mem_image_of_mem Prod.fst called

private theorem program_run (work : OracleComp PublicSpec Value) (before : State n KemSK ProviderState × Physical) :
    (simulateQ (closed setup wire sign seed scalar candidate provider physical) work).run before=
      (fun result => (result.1.1,(result.1.2,result.2))) <$>
        (simulateQ physical ((simulateQ actual work).run before.1)).run before.2 := by
  rw [closed,OracleComp.simulateQ_flattenStateT_run,←QueryImpl.simulateQ_mapStateTBase_run]
  rw [bind_pure_comp]

/-- Every actual returned hidden reference records its exact selected full source input, including arbitrary physical-state outcomes. -/
theorem demand_receipt (message : RegistrationNativeRelatedFamily.Message)
    (before after : State n KemSK ProviderState × Physical) (reference : RegistrationNativePairedDemand.Reference n)
    (supported : (some (.hidden reference),after) ∈ support
      ((closed setup wire sign seed scalar candidate provider physical (.inl (.inr (.inl (.inl message))))).run before)) :
    ∃ bytes, Input message=some bytes ∧ Selected bytes=true ∧ after.1.1.keys.slots bytes=some reference.slot :=
  RegistrationNativeSelectiveHiddenDictionaryRun.demand_receipt setup wire sign seed scalar candidate provider message before.1 after.1 reference
    (query_support setup wire sign seed scalar candidate provider physical (.inl (.inr (.inl (.inl message)))) before (some (.hidden reference),after) supported)

/-- The actual persistent continuation retains every previously returned opaque address and allocator injectivity. -/
theorem program_keeps (work : OracleComp PublicSpec Value) (before : State n KemSK ProviderState × Physical)
    (result : Value × (State n KemSK ProviderState × Physical))
    (good : Good before.1)
    (supported : result ∈ support ((simulateQ (closed setup wire sign seed scalar candidate provider physical) work).run before)) :
    Good result.2.1 ∧ ∀ bytes slot, before.1.1.keys.slots bytes=some slot → result.2.1.1.keys.slots bytes=some slot := by
  rw [program_run,support_map] at supported
  obtain ⟨reached,called,equal⟩ := supported
  cases equal
  apply RegistrationNativeSelectiveHiddenDictionaryRun.program setup wire sign seed scalar candidate provider work before.1 reached.1 good
  apply OracleComp.support_simulateQ_run'_subset physical _ before.2
  rw [StateT.run'_eq,support_map]
  exact Set.mem_image_of_mem Prod.fst called

/-- Two actual hidden demands returning the same slot, separated by any persistent continuation, have exactly the same complete 192-byte input. -/
theorem same_slot (firstMessage secondMessage : RegistrationNativeRelatedFamily.Message)
    (firstReference secondReference : RegistrationNativePairedDemand.Reference n)
    (before first middle after : State n KemSK ProviderState × Physical)
    (firstCall : (some (.hidden firstReference),first) ∈ support
      ((closed setup wire sign seed scalar candidate provider physical (.inl (.inr (.inl (.inl firstMessage))))).run before))
    (work : OracleComp PublicSpec Value) (value : Value)
    (between : (value,middle) ∈ support ((simulateQ (closed setup wire sign seed scalar candidate provider physical) work).run first))
    (secondCall : (some (.hidden secondReference),after) ∈ support
      ((closed setup wire sign seed scalar candidate provider physical (.inl (.inr (.inl (.inl secondMessage))))).run middle))
    (good : Good before.1) (same : firstReference.slot=secondReference.slot) :
    ∃ bytes, Input firstMessage=some bytes ∧ Input secondMessage=some bytes ∧ Selected bytes=true ∧
      after.1.1.keys.slots bytes=some firstReference.slot := by
  obtain ⟨firstBytes,firstFormed,firstSelected,firstAssigned⟩ := demand_receipt setup wire sign seed scalar candidate provider physical
    firstMessage before first firstReference firstCall
  have firstGood := RegistrationNativeSelectiveHiddenDictionaryRun.query setup wire sign seed scalar candidate provider
    (.inl (.inr (.inl (.inl firstMessage)))) before.1 (some (.hidden firstReference),first.1) good
    (query_support setup wire sign seed scalar candidate provider physical (.inl (.inr (.inl (.inl firstMessage)))) before (some (.hidden firstReference),first) firstCall)
  have continued := program_keeps setup wire sign seed scalar candidate provider physical work first (value,middle) firstGood.1 between
  have secondGood := RegistrationNativeSelectiveHiddenDictionaryRun.query setup wire sign seed scalar candidate provider
    (.inl (.inr (.inl (.inl secondMessage)))) middle.1 (some (.hidden secondReference),after.1) continued.1
    (query_support setup wire sign seed scalar candidate provider physical (.inl (.inr (.inl (.inl secondMessage)))) middle (some (.hidden secondReference),after) secondCall)
  obtain ⟨secondBytes,secondFormed,_secondSelected,secondAssigned⟩ := demand_receipt setup wire sign seed scalar candidate provider physical
    secondMessage middle after secondReference secondCall
  have retained := secondGood.2 firstBytes firstReference.slot (continued.2 firstBytes firstReference.slot firstAssigned)
  have equal : firstBytes=secondBytes := secondGood.1.2 firstBytes secondBytes secondReference.slot (same ▸ retained) secondAssigned
  exact ⟨firstBytes,firstFormed,equal ▸ secondFormed,firstSelected,retained⟩
end BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerSlotInput

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerSlotInput.demand_receipt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerSlotInput.demand_receipt

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerSlotInput.program_keeps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerSlotInput.program_keeps

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerSlotInput.same_slot' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerSlotInput.same_slot
