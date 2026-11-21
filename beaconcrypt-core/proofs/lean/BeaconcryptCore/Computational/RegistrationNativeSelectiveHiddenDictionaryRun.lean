-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSelectiveHiddenDictionary
import BeaconcryptCore.Computational.RegistrationNativeHiddenInterpreterInvariant
import BeaconcryptCore.Computational.RegistrationNativeSelectiveHiddenInterpreter

/-! The actual selective native interpreter preserves the full-input slot dictionary through every callback and adaptive continuation. Hidden demand receipts identify the returned descriptor in that same dictionary. The proof retains arbitrary World replies, private KEM provider state and signing receipts and derives allocator injectivity from actual cold startup. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSelectiveHiddenDictionaryRun
open PqxdhServerAuthExperiment (Setup)
open PqxdhRecordLiftInterface (Slot)
open RegistrationNativeHiddenInterpreter (Provider)
open RegistrationNativeSelectiveHiddenInterpreter (State handler onKeys onBase)
open RegistrationNativeHiddenServiceInvariant (Ordered InjectiveSlots)
variable {n : Nat} {ι KemSK ProviderState Value : Type} {base : OracleSpec ι}

def Good (before : State n KemSK ProviderState) : Prop := Ordered before.1.keys ∧ InjectiveSlots before.1.keys

private theorem keys_support (work : StateT (RegistrationNativeSelectiveHiddenService.State n)
    (OracleComp (PqxdhRecordLiftInterface.EnvEffects n)) Value) (before : State n KemSK ProviderState)
    (result : Value × State n KemSK ProviderState) (supported : result ∈ support ((onKeys work).run before)) :
    ∃ inner, inner ∈ support (work.run (before.1.keys, before.2)) ∧
      result.1 = inner.1 ∧ (result.2.1.keys, result.2.2) = inner.2 := by
  simp only [onKeys, StateT.run, support_map] at supported
  obtain ⟨inner, actual, rfl⟩ := supported
  exact ⟨inner, PqxdhDeploymentEnvironment.support_simulateQ_subset _ _ actual, rfl, rfl⟩

variable (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
  (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
  (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
  (candidate : PqxdhKemIndCca.MlKemSharedSecret) (provider : Provider KemSK ProviderState)

/-- Each actual selective demand receipt identifies its selected descriptor input and retained returned slot. -/
theorem demand_receipt (message : RegistrationNativeRelatedFamily.Message)
    (before after : State n KemSK ProviderState) (reference : RegistrationNativePairedDemand.Reference n)
    (supported : (some (.hidden reference), after) ∈ support
      ((handler setup wire sign seed scalar candidate provider (.inl (.inr (.inl (.inl message))))).run before)) :
    ∃ bytes, RegistrationNativeRelatedFamily.input setup.joint setup.dh seed scalar message = some bytes ∧
      RegistrationNativeSelectiveHiddenService.selected
        (RegistrationNativeKeyFamilyPreparation.inside (setup.joint.staticDh seed (setup.dh.publicKey scalar))) candidate bytes = true ∧
      after.1.keys.slots bytes = some reference.slot := by
  obtain ⟨inner, actual, equalReply, equalState⟩ := keys_support
    (RegistrationNativeSelectiveHiddenService.demand setup.source
      (RegistrationNativeRelatedFamily.input setup.joint setup.dh seed scalar)
      (RegistrationNativeKeyFamilyPreparation.inside (setup.joint.staticDh seed (setup.dh.publicKey scalar))) candidate message)
    before (some (RegistrationNativePairedChoice.Choice.hidden reference), after) supported
  rcases inner with ⟨reply, final⟩
  change some (RegistrationNativePairedChoice.Choice.hidden reference) = reply at equalReply
  subst reply
  change (after.1.keys, after.2) = final at equalState
  have receipt := RegistrationNativeSelectiveHiddenDictionary.hidden_receipt setup.source
    (RegistrationNativeRelatedFamily.input setup.joint setup.dh seed scalar)
    (RegistrationNativeKeyFamilyPreparation.inside (setup.joint.staticDh seed (setup.dh.publicKey scalar)))
    candidate message (before.1.keys, before.2) final reference actual
  rw [← equalState] at receipt
  exact receipt

/-- Every actual callback retains all previously assigned full-input addresses and derives the same ordered injective allocator. -/
theorem query (query : (RegistrationNativePublicFrontend.Spec n KemSK).Domain)
    (before : State n KemSK ProviderState)
    (result : (RegistrationNativePublicFrontend.Spec n KemSK).Range query × State n KemSK ProviderState)
    (good : Good before) (supported : result ∈ support ((handler setup wire sign seed scalar candidate provider query).run before)) :
    Good result.2 ∧ ∀ bytes slot, before.1.keys.slots bytes = some slot → result.2.1.keys.slots bytes = some slot := by
  rcases query with (message | (message | common) | kem) | record
  · simp only [handler, onBase, StateT.run, support_map] at supported
    obtain ⟨inner, actual, rfl⟩ := supported
    simp only [RegistrationNativeHiddenInterpreter.handler, RegistrationNativeHiddenInterpreter.onKeys,
      RegistrationNativeHiddenService.prepare, StateT.run, simulateQ_pure, map_pure, mem_support_pure_iff] at actual
    cases actual
    exact ⟨⟨⟨good.1.1, good.1.2⟩, good.2⟩, fun _ _ held => held⟩
  · obtain ⟨inner, actual, _reply, equalState⟩ := keys_support _ before result supported
    have valid := RegistrationNativeSelectiveHiddenServiceInvariant.demand_keeps setup.source
      (RegistrationNativeRelatedFamily.input setup.joint setup.dh seed scalar)
      (RegistrationNativeKeyFamilyPreparation.inside (setup.joint.staticDh seed (setup.dh.publicKey scalar)))
      candidate message (before.1.keys, before.2) inner.2 inner.1 good.1 good.2 actual
    have retained := RegistrationNativeSelectiveHiddenDictionary.demand_retains setup.source
      (RegistrationNativeRelatedFamily.input setup.joint setup.dh seed scalar)
      (RegistrationNativeKeyFamilyPreparation.inside (setup.joint.staticDh seed (setup.dh.publicKey scalar)))
      candidate message (before.1.keys, before.2) inner.2 inner.1
    rw [← equalState] at valid
    refine ⟨valid.2, ?_⟩
    intro bytes slot held
    have keeps := retained bytes slot held actual
    rw [← equalState] at keeps
    exact keeps
  · cases common with
    | inl publication =>
        simp only [handler, onBase, RegistrationNativeHiddenInterpreter.handler,
          RegistrationNativeHiddenInterpreter.publication, StateT.run, support_map] at supported
        obtain ⟨inner, actual, rfl⟩ := supported
        obtain ⟨reached, _possible, rfl⟩ := actual
        exact ⟨good, fun _ _ held => held⟩
    | inr effect =>
        change result ∈ support ((onBase (RegistrationNativeHiddenInterpreter.handler setup wire sign seed scalar provider
          (.inl (.inr (.inl (.inr (.inr effect))))))).run before) at supported
        simp only [onBase, StateT.run, support_map] at supported
        obtain ⟨inner, actual, rfl⟩ := supported
        change inner ∈ support ((RegistrationNativeHiddenInterpreter.handler setup wire sign seed scalar provider
          (.inl (.inr (.inl (.inr (.inr effect)))))).run before.1) at actual
        rw [RegistrationNativeHiddenInterpreter.effect_query setup wire sign seed scalar provider effect before.1] at actual
        simp only [support_map] at actual
        obtain ⟨reached, _possible, rfl⟩ := actual
        exact ⟨good, fun _ _ held => held⟩
  · simp only [handler, onBase, RegistrationNativeHiddenInterpreter.handler,
      RegistrationNativeHiddenInterpreter.routed, StateT.run, support_map] at supported
    obtain ⟨inner, actual, rfl⟩ := supported
    obtain ⟨reached, _possible, rfl⟩ := actual
    exact ⟨good, fun _ _ held => held⟩
  · change result ∈ support ((onBase (RegistrationNativeHiddenInterpreter.handler setup wire sign seed scalar provider (.inr record))).run before) at supported
    simp only [onBase, StateT.run, support_map] at supported
    obtain ⟨inner, actual, rfl⟩ := supported
    change inner ∈ support ((RegistrationNativeHiddenInterpreter.handler setup wire sign seed scalar provider (.inr record)).run before.1) at actual
    rw [RegistrationNativeHiddenInterpreter.record_query setup wire sign seed scalar provider record before.1] at actual
    simp only [support_map] at actual
    obtain ⟨reached, _possible, rfl⟩ := actual
    exact ⟨good, fun _ _ held => held⟩

/-- The same actual complete adaptive continuation retains its original dictionary without a caller-supplied source equation. -/
theorem program (work : OracleComp (RegistrationNativePublicFrontend.Spec n KemSK) Value)
    (before : State n KemSK ProviderState) (result : Value × State n KemSK ProviderState)
    (good : Good before) (supported : result ∈ support ((simulateQ (handler setup wire sign seed scalar candidate provider) work).run before)) :
    Good result.2 ∧ ∀ bytes slot, before.1.keys.slots bytes = some slot → result.2.1.keys.slots bytes = some slot := by
  induction work using OracleComp.inductionOn generalizing before with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at supported
      cases supported
      exact ⟨good, fun _ _ held => held⟩
  | query_bind request next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at supported
      obtain ⟨middle, actual, continued⟩ := supported
      have first := query setup wire sign seed scalar candidate provider request before middle good actual
      have later := ih middle.1 middle.2 first.1 continued
      exact ⟨later.1, fun bytes slot held => later.2 bytes slot (first.2 bytes slot held)⟩

end BeaconcryptCore.Computational.RegistrationNativeSelectiveHiddenDictionaryRun
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSelectiveHiddenDictionaryRun.demand_receipt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSelectiveHiddenDictionaryRun.demand_receipt
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSelectiveHiddenDictionaryRun.query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSelectiveHiddenDictionaryRun.query
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSelectiveHiddenDictionaryRun.program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSelectiveHiddenDictionaryRun.program
