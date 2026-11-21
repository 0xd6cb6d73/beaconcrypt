-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSelectiveHiddenService
import BeaconcryptCore.Computational.RegistrationNativeSecretWordProtection
import BeaconcryptCore.Computational.RegistrationNativeSecretWordCheckedInput

/-! Successful material demand of the selected protected descriptor can only return a hidden reference, with its actual persistent full-input slot. Missing preparation and capacity exhaustion cannot produce a successful known choice. -/
open OracleComp OracleSpec CoreModels
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSelectiveHiddenDemand
open RegistrationNativeRelatedFamily (Message)
open RegistrationNativePairedChoice (Choice)
open RegistrationNativeSelectiveHiddenService (State)
variable {n : Nat}

/-- An actual realized atom descriptor with the proved protected head is selected by the concrete native full-input classifier. -/
theorem selected_descriptor (joint : PqxdhJointIdentity.Primitives) (dh : PqxdhJointGapDh.DhInterface joint)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret) (target : Option PqxdhJointIdentity.DhOutput)
    (message : RegistrationNativeSecretWordMessage.Message) (bytes : Pqxdh.Bytes)
    (atom : message.kem = .atom)
    (protectedHead : ∀ key, RegistrationNativeSecretWordMessage.input joint dh seed scalar message = some key →
      RegistrationNativeSecretWordProtection.inside target key.head = true)
    (native : RegistrationNativeRelatedFamily.input joint dh seed scalar
      (RegistrationNativeSecretWordMessage.eval candidate message) = some bytes) :
    RegistrationNativeSelectiveHiddenService.selected (RegistrationNativeKeyFamilyPreparation.inside target) candidate bytes = true := by
  have mapped := RegistrationNativeSecretWordMessage.input_eval joint dh seed scalar candidate message
  rw [native] at mapped
  cases formed : RegistrationNativeSecretWordMessage.input joint dh seed scalar message with
  | none => simp only [formed, Option.map_none, reduceCtorEq] at mapped
  | some key =>
      simp only [formed, Option.map_some, Option.some.injEq] at mapped
      have word := RegistrationNativeSecretWordCheckedInput.input_word joint dh seed scalar message message.kem
      have unchanged : { message with kem := message.kem } = message := by cases message; rfl
      rw [unchanged, formed, Option.map_some, Option.some.injEq] at word
      have kept : key.word = message.kem := congrArg RegistrationNativeSecretWord.Key.word word
      have suffix : PqxdhJointGapDh.readDh 160 (RegistrationNativeSecretWord.eval candidate key) = some (key.word.eval candidate) := by
        simp [PqxdhJointGapDh.readDh, RegistrationNativeSecretWord.eval]
        apply List.Vector.toList_injective
        exact List.take_of_length_le (by simp)
      simp only [RegistrationNativeSelectiveHiddenService.selected, Bool.and_eq_true, decide_eq_true_eq]
      constructor
      · rw [← mapped, ← RegistrationNativeSecretWordProtection.inside_eval]
        exact protectedHead key formed
      · rw [← mapped, suffix, kept, atom, RegistrationNativeSecretWord.Word.eval]

private theorem hidden_kind (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (input : Message → Option Pqxdh.Bytes) (inside : Pqxdh.Bytes → Bool) (message : Message)
    (bytes : Pqxdh.Bytes) (before after : RegistrationNativeHiddenService.State n) (choice : Choice n)
    (realized : input message = some bytes) (hidden : inside bytes = true)
    (supported : (some choice, after) ∈ support ((RegistrationNativeHiddenService.demand source input inside message).run before)) :
    ∃ reference, choice = .hidden reference := by
  simp only [RegistrationNativeHiddenService.demand, StateT.run] at supported
  split at supported
  · simp only [realized, hidden, ite_true] at supported
    cases allocated : RegistrationNativeHiddenService.reserve bytes { before with demands := before.demands + 1 } with
    | mk selected reached =>
        rw [allocated] at supported
        cases selected with
        | none => simp only [mem_support_pure_iff] at supported; cases supported
        | some slot =>
            rw [support_map] at supported
            obtain ⟨result, _sampled, returned⟩ := supported
            have same : some (.hidden ⟨slot, result.1⟩) = some choice := congrArg Prod.fst returned
            exact ⟨⟨slot, result.1⟩, (Option.some.inj same).symm⟩
  · simp only [mem_support_pure_iff] at supported
    cases supported

/-- Every successful actual selected demand returns a hidden reference at the same full realized input. -/
theorem successful (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (input : Message → Option Pqxdh.Bytes) (inside : Pqxdh.Bytes → Bool)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret) (message : Message) (bytes : Pqxdh.Bytes)
    (before after : State n) (choice : Choice n) (realized : input message = some bytes)
    (selected : RegistrationNativeSelectiveHiddenService.selected inside candidate bytes = true)
    (supported : (some choice, after) ∈ support
      ((RegistrationNativeSelectiveHiddenService.demand source input inside candidate message).run before)) :
    ∃ reference, choice = .hidden reference ∧ after.1.slots bytes = some reference.slot ∧
      after.1.materials reference.slot = some reference.material := by
  by_cases prepared : before.1.prepared message = true
  · rw [RegistrationNativeSelectiveHiddenService.demand_selected source input inside candidate message before bytes prepared realized selected] at supported
    simp only [RegistrationNativeSelectiveHiddenService.onHidden, StateT.run, support_map] at supported
    obtain ⟨result, reached, returned⟩ := supported
    have chosen : result.1 = some choice := congrArg Prod.fst returned
    have state : result.2 = after.1 := congrArg (fun value => value.2.1) returned
    have pairEq : result = (some choice, after.1) := Prod.ext chosen state
    rw [pairEq] at reached
    obtain ⟨reference, same⟩ := hidden_kind source input
      (RegistrationNativeSelectiveHiddenService.selected inside candidate) message bytes before.1 after.1 choice realized selected reached
    subst choice
    obtain ⟨actual, actualAt, _protected, slotAt, materialAt⟩ := RegistrationNativeHiddenServiceDemand.hidden_receipt source input
      (RegistrationNativeSelectiveHiddenService.selected inside candidate) message before.1 after.1 reference reached
    have equal : actual = bytes := Option.some.inj (actualAt.symm.trans realized)
    subst actual
    exact ⟨reference, rfl, slotAt, materialAt⟩
  · simp only [RegistrationNativeSelectiveHiddenService.demand, StateT.run, RegistrationNativeSelectiveHiddenService.onHidden, RegistrationNativeHiddenService.demand,
      ite_eq_right prepared, map_pure, mem_support_pure_iff] at supported
    cases supported

end BeaconcryptCore.Computational.RegistrationNativeSelectiveHiddenDemand

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSelectiveHiddenDemand.successful' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSelectiveHiddenDemand.successful
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSelectiveHiddenDemand.selected_descriptor' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSelectiveHiddenDemand.selected_descriptor
