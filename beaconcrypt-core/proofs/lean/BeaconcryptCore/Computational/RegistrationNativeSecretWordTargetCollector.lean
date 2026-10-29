-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSecretWordServerCollect

/-! A successful actual symbolic Server collector reaches its literal sole KEM getter after the ordered status, reservation, DH admission and ephemeral prefix. The reached getter state and complete suffix state are retained under arbitrary concrete interpreters. The returned word and verified packet metadata come from that same reached getter, rather than an independently supplied root reference. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetCollector
open RegistrationNativeSecretWordServerCollect (Spec Input zero)
open PqxdhServerRootPreparation (Verified Ephemeral registrationId)
open PqxdhRootTableInitialization (rootArray)
open PqxdhBeaconPhase2Preparation (Ciphertext)
open RegistrationNativeSecretWord (Word)
variable {Reader E Shared Auxiliary : Type}

def beforeGetter (verified : Verified Reader) : OracleComp (Spec Reader E Shared) (Option (Ephemeral E)) := OptionT.run do
  let status ← (Spec Reader E Shared).query (.registrationStatus (registrationId verified))
  match status with
  | .Consumed => failure
  | .Fresh => do
      let reserved ← (Spec Reader E Shared).query .reserveRegistration
      if !reserved then failure else do
        let validPrekey ← (Spec Reader E Shared).query (.parseDh (rootArray verified.keys.prekey))
        if !validPrekey then failure else do
          let validOneTime ← (Spec Reader E Shared).query (.parseDh (rootArray verified.keys.oneTime))
          if !validOneTime then failure else do
            let ephemeral ← OptionT.mk ((Spec Reader E Shared).query .generate)
            let validKem ← (Spec Reader E Shared).query (.parseKem verified.keys.pqKey)
            if !validKem then failure else pure ephemeral

def afterGetter (verified : Verified Reader) (ephemeral : Ephemeral E) (pair : Ciphertext × Word) :
    OracleComp (Spec Reader E Shared) (Option (Input Reader E Shared)) := OptionT.run do
  let converted ← OptionT.mk ((Spec Reader E Shared).query (.publicConversion verified.identity))
  let privateConverted ← (Spec Reader E Shared).query .privateConversion
  if !privateConverted then failure else do
    let first ← OptionT.mk ((Spec Reader E Shared).query (.staticDh (rootArray verified.keys.prekey)))
    let second ← OptionT.mk ((Spec Reader E Shared).query (.ephemeralDh ephemeral.secret converted))
    let third ← OptionT.mk ((Spec Reader E Shared).query (.ephemeralDh ephemeral.secret (rootArray verified.keys.prekey)))
    let fourth ← OptionT.mk ((Spec Reader E Shared).query (.ephemeralDh ephemeral.secret (rootArray verified.keys.oneTime)))
    pure ⟨⟨verified, ephemeral, pair.1, converted, first, second, third, fourth, zero⟩, pair.2⟩

/-- The cut is the actual ordered collector AST, with no suspension or simulation premise. -/
theorem collect_factor (verified : Verified Reader) :
    RegistrationNativeSecretWordServerCollect.collect (E := E) (Shared := Shared) verified = (do
      let earlier ← beforeGetter verified
      match earlier with
      | none => pure none
      | some ephemeral => do
          let pair ← (Spec Reader E Shared).query (.encapsulate verified.keys.pqKey)
          match pair with
          | none => pure none
          | some pair => afterGetter verified ephemeral pair) := by
  simp only [RegistrationNativeSecretWordServerCollect.collect, beforeGetter, afterGetter,
    OptionT.run_bind, OptionT.run_monadLift, Option.elimM, bind_map_left, bind_assoc]
  repeat' first
    | rfl
    | (simp only [OptionT.run_bind, OptionT.run_mk, OptionT.run_pure, OptionT.run_monadLift,
        Option.elimM, bind_map_left, bind_assoc, Bool.not_true,
        Bool.false_eq_true, ite_false, Option.elim_some, pure_bind])
    | (congr 1; funext reply; cases reply)

/-- The suffix retains exactly its original verified packet, ciphertext and opaque getter word. -/
theorem after_fields (verified : Verified Reader) (ephemeral : Ephemeral E) (pair : Ciphertext × Word)
    (input : Input Reader E Shared) (supported : some input ∈ support (afterGetter verified ephemeral pair)) :
    input.plain.verified = verified ∧ input.plain.ciphertext = pair.1 ∧ input.kem = pair.2 := by
  simp only [afterGetter, OptionT.run_bind, OptionT.run_monadLift, Option.elimM,
    bind_map_left, mem_support_bind_iff] at supported
  repeat' first
    | (simp only [OptionT.run_bind, OptionT.run_mk, OptionT.run_pure,
        OptionT.run_failure, Option.elimM, Bool.not_true, Bool.not_false,
        Bool.false_eq_true, ite_false, ite_true, Option.elim_none, Option.elim_some,
        mem_support_bind_iff, mem_support_pure_iff, Option.some.injEq, Option.some_ne_none] at supported)
    | (obtain ⟨reply, _, supported⟩ := supported; cases reply)
  all_goals cases supported; exact ⟨rfl, rfl, rfl⟩

/-- Successful concrete collection contains the actual prefix, actual optional getter reply and complete successful suffix at their reached states. -/
theorem collect_receipt
    (implementation : QueryImpl (Spec Reader E Shared) (StateT Auxiliary ProbComp))
    (verified : Verified Reader) (before after : Auxiliary) (input : Input Reader E Shared)
    (supported : (some input, after) ∈ support ((simulateQ implementation
      (RegistrationNativeSecretWordServerCollect.collect verified)).run before)) :
    ∃ ephemeral first second pair,
      (some ephemeral, first) ∈ support ((simulateQ implementation (beforeGetter verified)).run before) ∧
      (some pair, second) ∈ support ((implementation (.encapsulate verified.keys.pqKey)).run first) ∧
      (some input, after) ∈ support ((simulateQ implementation (afterGetter verified ephemeral pair)).run second) ∧
      input.plain.verified = verified ∧ input.plain.ciphertext = pair.1 ∧ input.kem = pair.2 := by
  rw [collect_factor, simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at supported
  obtain ⟨⟨earlier, first⟩, initial, continued⟩ := supported
  cases earlier with
  | none => simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff, Prod.mk.injEq, reduceCtorEq, false_and] at continued
  | some ephemeral =>
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at continued
      obtain ⟨⟨reply, second⟩, called, completed⟩ := continued
      cases reply with
      | none => simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff, Prod.mk.injEq, reduceCtorEq, false_and] at completed
      | some pair =>
          have native : some input ∈ support (afterGetter verified ephemeral pair) := by
            apply OracleComp.support_simulateQ_run'_subset implementation _ second
            rw [StateT.run'_eq, support_map]
            exact Set.mem_image_of_mem Prod.fst completed
          exact ⟨ephemeral, first, second, pair, initial, called, completed, after_fields verified ephemeral pair input native⟩

end BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetCollector
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetCollector.collect_factor' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetCollector.collect_factor
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetCollector.after_fields' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetCollector.after_fields
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetCollector.collect_receipt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetCollector.collect_receipt
