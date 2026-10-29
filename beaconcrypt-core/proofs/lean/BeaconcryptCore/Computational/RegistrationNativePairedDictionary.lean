-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePairedTrace
import BeaconcryptCore.Computational.RegistrationNativeSelectiveHiddenDictionaryRun

/-! The paired observer's actual current descriptor and returned hidden Choice identify the same selected input in the actual selective service dictionary. The property is derived at each supported demand and retained through all later callbacks, including failed installations and arbitrary KEM/provider replies. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePairedDictionary
open PqxdhServerAuthExperiment (Setup)
open RegistrationNativePublicFrontend (Spec)
open RegistrationNativeHiddenInterpreter (Provider)
open RegistrationNativePairedTrace (step)
variable {n : Nat} {ι KemSK ProviderState Value : Type} {base : OracleSpec ι}

abbrev State (n : Nat) (KemSK ProviderState : Type) := RegistrationNativePairedTrace.State n ×
  RegistrationNativeSelectiveHiddenInterpreter.State n KemSK ProviderState

def Current (input : RegistrationNativeRelatedFamily.Message → Option Pqxdh.Bytes)
    (selected : Pqxdh.Bytes → Bool) (trace : RegistrationNativePairedTrace.State n)
    (keys : RegistrationNativeHiddenService.State n) : Prop :=
  ∀ message reference, trace.trace.current = some message → trace.choice = some (.hidden reference) →
    ∃ bytes, input message = some bytes ∧ selected bytes = true ∧ keys.slots bytes = some reference.slot

noncomputable def handler (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret) (provider : Provider KemSK ProviderState) :
    QueryImpl (Spec n KemSK) (StateT (State n KemSK ProviderState) (OracleComp (PqxdhRecordLiftInterface.WorldSpec n))) := fun query before =>
  (fun reached => (reached.1, (step query reached.1 before.1, reached.2))) <$>
    (RegistrationNativeSelectiveHiddenInterpreter.handler setup wire sign seed scalar candidate provider query).run before.2

variable (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
  (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
  (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
  (candidate : PqxdhKemIndCca.MlKemSharedSecret) (provider : Provider KemSK ProviderState)

local notation "input" => RegistrationNativeRelatedFamily.input setup.joint setup.dh seed scalar
local notation "selected" => RegistrationNativeSelectiveHiddenService.selected
  (RegistrationNativeKeyFamilyPreparation.inside (setup.joint.staticDh seed (setup.dh.publicKey scalar))) candidate

private theorem current_keeps (before after : RegistrationNativePairedTrace.State n)
    (old new : RegistrationNativeHiddenService.State n) (valid : Current input selected before old)
    (current : after.trace.current = before.trace.current) (choice : after.choice = before.choice)
    (keeps : ∀ bytes slot, old.slots bytes = some slot → new.slots bytes = some slot) : Current input selected after new := by
  intro message reference active actualChoice
  obtain ⟨bytes, formed, protectedInput, assigned⟩ := valid message reference (current.symm.trans active) (choice.symm.trans actualChoice)
  exact ⟨bytes, formed, protectedInput, keeps bytes reference.slot assigned⟩

/-- Each literal actual callback preserves the same-demand selected-input receipt in its full current dictionary. -/
theorem query (query : (Spec n KemSK).Domain) (before : State n KemSK ProviderState)
    (valid : RegistrationNativeSelectiveHiddenDictionaryRun.Good before.2 ∧ Current input selected before.1 before.2.1.keys)
    (result : (Spec n KemSK).Range query × State n KemSK ProviderState)
    (supported : result ∈ support ((handler setup wire sign seed scalar candidate provider query).run before)) :
    RegistrationNativeSelectiveHiddenDictionaryRun.Good result.2.2 ∧ Current input selected result.2.1 result.2.2.1.keys := by
  simp only [handler, StateT.run, support_map] at supported
  obtain ⟨reached, actual, rfl⟩ := supported
  have dictionary := RegistrationNativeSelectiveHiddenDictionaryRun.query setup wire sign seed scalar candidate provider query before.2 reached valid.1 actual
  refine ⟨dictionary.1, ?_⟩
  rcases query with (prepare | (demand | (publication | environment)) | kem) | record
  · intro message reference _active impossible
    cases impossible
  · intro message reference active actualChoice
    change some demand = some message at active
    have same := Option.some.inj active
    subst message
    change reached.1 = some (.hidden reference) at actualChoice
    obtain ⟨reply, after⟩ := reached
    dsimp only at actualChoice actual ⊢
    subst reply
    exact RegistrationNativeSelectiveHiddenDictionaryRun.demand_receipt setup wire sign seed scalar candidate provider demand before.2 after reference actual
  · exact current_keeps setup seed scalar candidate _ _ _ _ valid.2 rfl rfl dictionary.2
  · rcases environment with coin | capability
    · exact current_keeps setup seed scalar candidate _ _ _ _ valid.2 rfl rfl dictionary.2
    · cases capability with
      | installServer keyId binding kernel | installBeacon owner shell kernel =>
          intro message reference _active impossible
          cases impossible
      | _ => exact current_keeps setup seed scalar candidate _ _ _ _ valid.2 rfl rfl dictionary.2
  · rcases kem with (other | key) | (pool | key)
    all_goals exact current_keeps setup seed scalar candidate _ _ _ _ valid.2 rfl rfl dictionary.2
  · exact current_keeps setup seed scalar candidate _ _ _ _ valid.2 rfl rfl dictionary.2

/-- The whole adaptive paired execution derives each current descriptor receipt from its actual earlier demand. -/
theorem program (work : OracleComp (Spec n KemSK) Value) (before : State n KemSK ProviderState)
    (valid : RegistrationNativeSelectiveHiddenDictionaryRun.Good before.2 ∧ Current input selected before.1 before.2.1.keys)
    (result : Value × State n KemSK ProviderState)
    (supported : result ∈ support ((simulateQ (handler setup wire sign seed scalar candidate provider) work).run before)) :
    RegistrationNativeSelectiveHiddenDictionaryRun.Good result.2.2 ∧ Current input selected result.2.1 result.2.2.1.keys := by
  induction work using OracleComp.inductionOn generalizing before with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at supported
      cases supported
      exact valid
  | query_bind request next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at supported
      obtain ⟨middle, actual, continued⟩ := supported
      exact ih middle.1 middle.2 (query setup wire sign seed scalar candidate provider request before valid middle actual) continued

end BeaconcryptCore.Computational.RegistrationNativePairedDictionary
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePairedDictionary.query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePairedDictionary.query
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePairedDictionary.program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePairedDictionary.program
