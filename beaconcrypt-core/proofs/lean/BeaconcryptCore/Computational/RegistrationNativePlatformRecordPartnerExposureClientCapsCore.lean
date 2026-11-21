-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureClient
import BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureRootCaps
import BeaconcryptCore.Computational.RegistrationNativeSecretWordInterpreterCaps
/-! The actual open source dictionary bills recovery requests only at material demand. Every ambient World, publication and indexed KEM leaf has zero protected-key/suffix cost, and the exact candidate-independent root proxy supplies both remaining bills. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureClientCapsCore
open PqxdhServerAuthExperiment (Setup)
open RegistrationNativeSecretWordMessage (Message)
open RegistrationNativeSecretWord (Key)
open RegistrationNativeSecretWordServiceCaps (Kind)
open RegistrationNativePlatformRecordPartnerExposureRootCaps (Counted)
open RegistrationNativePlatformRecordPartnerExposureClient (Shared Roots closing lowerWith)
variable {n : Nat} {I KemSK A : Type} {base : OracleSpec I}
abbrev OpenSpec (n : Nat) := RegistrationNativePlatformLorOpenDictionary.Spec n

def Charged (kind : Kind) : (OpenSpec n).Domain →Prop
  | .inl query=>Counted kind query
  | .inr (.inl _)=>False
  | .inr (.inr _)=>True
instance (kind : Kind) : DecidablePred (Charged (n := n) kind) := fun query=>by
  rcases query with ambient|(message|message)
  · exact inferInstanceAs (Decidable (Counted kind ambient))
  · exact inferInstanceAs (Decidable False)
  · exact inferInstanceAs (Decidable True)

/-- The literal closing callback charges only an ambient counted request or one material demand. -/
theorem closing_bound (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (input : Message →Option Key)
    (inside : RegistrationNativeSuffixKeyPrf.Prefix →Bool) (operand : Message →Message)
    (query : (OpenSpec n).Domain) (before : Roots n) (kind : Kind) :
    ((closing source input inside operand query).run before).IsQueryBoundP (Counted kind) (if Charged (n := n) kind query then 1 else 0) := by
  rcases query with ambient|(message|message)
  · by_cases counted : Counted (n := n) kind ambient <;>
      simp [closing,StateT.run_lift,bind_pure_comp,isQueryBoundP_map_iff,isQueryBoundP_query_iff,Charged,counted]
  · simp only [closing,RegistrationNativePlatformRecordPartnerExposureRoot.handler,StateT.run_pure,Charged,ite_false,isQueryBoundP_pure]
  · simpa only [closing,Charged,ite_true,RegistrationNativePlatformRecordPartnerExposureRootCaps.IsDemand] using
      RegistrationNativePlatformRecordPartnerExposureRootCaps.handler_bound source input inside (.inr (operand message)) before kind

/-- The open dictionary's actual stateful closing preserves an existing combined request allowance. -/
theorem closing_program_bound (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (input : Message →Option Key)
    (inside : RegistrationNativeSuffixKeyPrf.Prefix →Bool) (operand : Message →Message)
    (work : OracleComp (OpenSpec n) A) (cap : Nat) (kind : Kind) (bounded : work.IsQueryBoundP (Charged kind) cap) (before : Roots n) :
    ((simulateQ (closing source input inside operand) work).run before).IsQueryBoundP (Counted kind) cap := by
  apply bounded.simulateQ_run_of_step
  · intro query counted current
    simpa only [ite_eq_left counted] using closing_bound source input inside operand query current kind
  · intro query free current
    simpa only [ite_eq_right free] using closing_bound source input inside operand query current kind

private theorem embedded_bound (kind : Kind) (work : OracleComp (Shared n) A) (cap : Nat)
    (bounded : work.IsQueryBoundP (Counted kind) cap) :
    (simulateQ RegistrationNativePlatformLorOpenDictionary.embed work).IsQueryBoundP (Charged kind) cap := by
  apply RawCtxSourceOpen.simulate_bound _ (Counted kind) (Charged kind) work cap bounded
  intro query
  by_cases counted : Counted (n := n) kind query <;>
    simp [RegistrationNativePlatformLorOpenDictionary.embed,Charged,counted,isQueryBoundP_query_iff]

private theorem effects_free (kind : Kind) (work : OracleComp (PqxdhRecordLiftInterface.EnvEffects n) A) :
    (simulateQ (fun query=>RegistrationNativePlatformLorWorldDictionary.world (.inr (.inl query))) work).IsQueryBoundP (Counted kind) 0 := by
  apply RawCtxSourceOpen.simulate_bound _ (fun _=>False) _ _ 0 (isQueryBoundP_false work 0)
  intro query
  simp only [RegistrationNativePlatformLorWorldDictionary.world,Counted,isQueryBoundP_query_iff]
  decide

private theorem coins_free (kind : Kind) (work : ProbComp A) :
    (simulateQ (RegistrationNativePlatformLorWorldDictionary.coins (n := n)) work).IsQueryBoundP (Counted kind) 0 := by
  apply RawCtxSourceOpen.simulate_bound _ (fun _=>False) _ _ 0 (isQueryBoundP_false work 0)
  intro query
  simp only [RegistrationNativePlatformLorWorldDictionary.coins,QueryImpl.apply_compose,PqxdhRecordLiftInterface.coinLift,
    RegistrationNativePlatformLorWorldDictionary.world,simulateQ_spec_query,Counted,isQueryBoundP_query_iff]
  decide

private theorem common_free (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest →ProbComp RegistrationSigningShared.SignReply)
    (query : (RegistrationNativePairedServerService.Common n).Domain)
    (before : RegistrationNativeSecretWordInterpreter.State n KemSK) (kind : Kind) :
    ((RegistrationNativePlatformLorWorldDictionary.common setup wire sign query).run before).IsQueryBoundP (Counted kind) 0 := by
  cases query with
  | inl publication=>
    simp only [RegistrationNativePlatformLorWorldDictionary.common,RegistrationNativePlatformLorWorldDictionary.publication,StateT.run,isQueryBoundP_map_iff]
    exact effects_free kind _
  | inr effect=>
    simp only [RegistrationNativePlatformLorWorldDictionary.common,RegistrationNativePlatformLorWorldDictionary.effect,
      StateT.run_lift,bind_pure_comp,isQueryBoundP_map_iff,RegistrationNativePlatformLorWorldDictionary.world,
      Counted,isQueryBoundP_query_iff]
    decide

private theorem routed_free (provider : RegistrationNativeSecretWordInterpreter.Provider KemSK)
    (query : (RegistrationNativeSecretWordKemInterface.Routed KemSK).Domain)
    (before : RegistrationNativeSecretWordInterpreter.State n KemSK) (kind : Kind) :
    ((RegistrationNativePlatformLorWorldDictionary.routed provider query).run before).IsQueryBoundP (Counted kind) 0 := by
  simp only [RegistrationNativePlatformLorWorldDictionary.routed,StateT.run,isQueryBoundP_map_iff]
  exact coins_free kind _

/-- Literal source preparation and ambient calls have zero recovery bill; the actual material leaf has at most one. -/
theorem dictionary_bound (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest →ProbComp RegistrationSigningShared.SignReply)
    (input : Message →Option Key) (inside : RegistrationNativeSuffixKeyPrf.Prefix →Bool)
    (provider : RegistrationNativeSecretWordInterpreter.Provider KemSK)
    (query : (RegistrationNativeSecretWordInterface.Spec n KemSK).Domain)
    (before : RegistrationNativeSecretWordInterpreter.State n KemSK) (kind : Kind) :
    ((RegistrationNativePlatformLorOpenDictionary.handler setup wire sign input inside provider query).run before).IsQueryBoundP (Charged kind)
      (if RegistrationNativeSecretWordInterpreterCaps.IsDemand (n := n) (KemSK := KemSK) query then 1 else 0) := by
  rcases query with (message|(message|common)|kem)|record
  · simp [RegistrationNativePlatformLorOpenDictionary.handler,StateT.run,RegistrationNativePlatformLorOpenDictionary.root,
      RegistrationNativeSecretWordInterpreterCaps.IsDemand,Charged]
  · simp [RegistrationNativePlatformLorOpenDictionary.handler,StateT.run,RegistrationNativePlatformLorOpenDictionary.root,
      RegistrationNativeSecretWordInterpreterCaps.IsDemand,Charged,isQueryBoundP_map_iff,isQueryBoundP_query_iff]
  · simp only [RegistrationNativePlatformLorOpenDictionary.handler,QueryImpl.mapStateTBase,StateT.run_mk,
      RegistrationNativeSecretWordInterpreterCaps.IsDemand,ite_false]
    exact embedded_bound kind _ 0 (common_free setup wire sign common before kind)
  · simp only [RegistrationNativePlatformLorOpenDictionary.handler,QueryImpl.mapStateTBase,StateT.run_mk,
      RegistrationNativeSecretWordInterpreterCaps.IsDemand,ite_false]
    exact embedded_bound kind _ 0 (routed_free provider kem before kind)
  · simp only [RegistrationNativePlatformLorOpenDictionary.handler,QueryImpl.mapStateTBase,StateT.run_mk,
      RegistrationNativeSecretWordInterpreterCaps.IsDemand,ite_false]
    apply embedded_bound kind _ 0
    simp only [RegistrationNativePlatformLorWorldDictionary.handler,StateT.run_lift,bind_pure_comp,isQueryBoundP_map_iff,
      RegistrationNativePlatformLorWorldDictionary.world,Counted,isQueryBoundP_query_iff]
    decide

/-- The actual persistent lower dictionary derives both recovery allowances at its individual Word query. -/
theorem lower_bound (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest →ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (provider : RegistrationNativeSecretWordInterpreter.Provider KemSK) (operand : Message →Message)
    (query : (RegistrationNativeSecretWordInterface.Spec n KemSK).Domain)
    (before : RegistrationNativeSecretWordInterpreter.State n KemSK ×Roots n) (kind : Kind) :
    ((lowerWith setup wire sign seed scalar provider operand query).run before).IsQueryBoundP (Counted kind)
      (if RegistrationNativeSecretWordInterpreterCaps.IsDemand (n := n) (KemSK := KemSK) query then 1 else 0) := by
  rw [RegistrationNativePlatformRecordPartnerExposureClient.lower_run,isQueryBoundP_map_iff]
  exact closing_program_bound setup.source _ _ operand _ _ kind (dictionary_bound setup wire sign _ _ provider query before.1 kind) before.2
end BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureClientCapsCore
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureClientCapsCore.closing_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureClientCapsCore.closing_bound
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureClientCapsCore.closing_program_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureClientCapsCore.closing_program_bound
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureClientCapsCore.dictionary_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureClientCapsCore.dictionary_bound
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureClientCapsCore.lower_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureClientCapsCore.lower_bound
