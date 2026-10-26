-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRegistrationJointKemCutSelection

/-! The actual source collector around its encapsulation callback. The split preserves optional exits and the complete continuation; successful resumption keeps the original verified fields and challenger-provided ciphertext/shared-secret pair. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhRegistrationJointKemCollected
open PqxdhServerRootPreparation
open PqxdhBeaconPhase2Preparation (Word32 Ciphertext)
variable {Reader E Shared : Type}

/-- The source suffix after an encapsulation reply, retaining both conversions and all four DH calls in order. A failed reply exits before any of these calls. -/
def afterEncapsulation (verified : Verified Reader) (ephemeral : Ephemeral E)
    (reply : Option (Ciphertext × Word32)) : OracleComp (Spec Reader E Shared)
      (Option (Inputs Reader E Shared)) := OptionT.run do
  let encapsulated ← OptionT.mk (pure reply)
  let converted ← OptionT.mk ((Spec Reader E Shared).query (.publicConversion verified.identity))
  let privateConverted ← (Spec Reader E Shared).query .privateConversion
  if !privateConverted then failure else do
    let prekey := PqxdhRootTableInitialization.rootArray verified.keys.prekey
    let oneTime := PqxdhRootTableInitialization.rootArray verified.keys.oneTime
    let first ← OptionT.mk ((Spec Reader E Shared).query (.staticDh prekey))
    let second ← OptionT.mk ((Spec Reader E Shared).query (.ephemeralDh ephemeral.secret converted))
    let third ← OptionT.mk ((Spec Reader E Shared).query (.ephemeralDh ephemeral.secret prekey))
    let fourth ← OptionT.mk ((Spec Reader E Shared).query (.ephemeralDh ephemeral.secret oneTime))
    pure ⟨verified, ephemeral, encapsulated.1, converted, first, second, third, fourth, encapsulated.2⟩

/-- Successful source suffixes preserve the original verified tuple and ephemeral, and use exactly the supplied encapsulation pair. No independence or successful-DH premise is assumed. -/
theorem after_fields (verified : Verified Reader) (ephemeral : Ephemeral E)
    (reply : Option (Ciphertext × Word32)) (input : Inputs Reader E Shared)
    (reached : some input ∈ support (afterEncapsulation verified ephemeral reply)) :
    input.verified = verified ∧ input.ephemeral = ephemeral ∧
      reply = some (input.ciphertext, input.kem) := by
  cases reply with
  | none => simp [afterEncapsulation] at reached
  | some pair =>
      simp only [afterEncapsulation, OptionT.run_bind, OptionT.run_mk,
        OptionT.run_monadLift, Option.elimM, pure_bind, Option.elim_some, bind_map_left] at reached
      rw [mem_support_bind_iff] at reached
      obtain ⟨converted, _, reached⟩ := reached
      cases converted with
      | none => simp at reached
      | some converted =>
          simp only [Option.elim_some, mem_support_bind_iff] at reached
          obtain ⟨valid, _, reached⟩ := reached
          cases valid <;> simp only [Bool.not_false, Bool.not_true,
            Bool.false_eq_true, ite_true, ite_false, OptionT.run_failure, support_pure,
            Set.mem_singleton_iff, reduceCtorEq] at reached
          simp only [OptionT.run_bind, OptionT.run_mk, OptionT.run_pure, Option.elimM] at reached
          repeat
            rw [mem_support_bind_iff] at reached
            obtain ⟨answer, _, reached⟩ := reached
            cases answer <;> simp only [Option.elim_none, Option.elim_some, support_pure,
              Set.mem_singleton_iff, reduceCtorEq] at reached
          cases Option.some.inj reached
          exact ⟨rfl, rfl, rfl⟩


/-- The literal ordered prefix before encapsulation: freshness, reservation, both point parsers, source ephemeral generation and KEM parsing. -/
def beforeEncapsulation (verified : Verified Reader) :
    OracleComp (Spec Reader E Shared) (Option (Ephemeral E)) := OptionT.run do
  let status ← (Spec Reader E Shared).query (.registrationStatus (registrationId verified))
  match status with
  | .Consumed => failure
  | .Fresh => do
    let reserved ← (Spec Reader E Shared).query .reserveRegistration
    if !reserved then failure else do
      let validPrekey ← (Spec Reader E Shared).query
        (.parseDh (PqxdhRootTableInitialization.rootArray verified.keys.prekey))
      if !validPrekey then failure else do
        let validOneTime ← (Spec Reader E Shared).query
          (.parseDh (PqxdhRootTableInitialization.rootArray verified.keys.oneTime))
        if !validOneTime then failure else do
          let ephemeral ← OptionT.mk ((Spec Reader E Shared).query .generate)
          let validKem ← (Spec Reader E Shared).query (.parseKem verified.keys.pqKey)
          if !validKem then failure else pure ephemeral

/-- Splitting at the source encapsulation operation preserves the complete original collector as an oracle program, with every optional exit and all replies quantified. -/
theorem collect_split (verified : Verified Reader) :
    collectVerified (E := E) (Shared := Shared) verified = (do
      let ephemeral ← beforeEncapsulation verified
      match ephemeral with
      | none => pure none
      | some ephemeral => do
          let reply ← (Spec Reader E Shared).query (.encapsulate verified.keys.pqKey)
          afterEncapsulation verified ephemeral reply) := by
  unfold collectVerified beforeEncapsulation afterEncapsulation
  repeat
    first
    | rfl
    | (fail_if_no_progress simp only [OptionT.run_bind, OptionT.run_mk, OptionT.run_pure,
        OptionT.run_monadLift, Option.elimM, Option.elim_some,
        bind_map_left, bind_assoc, pure_bind, Bool.not_true,
        Bool.false_eq_true, ite_false])
    | (apply bind_congr; intro answer; cases answer)


/-- The field relation holds after any stateful interpretation of the actual suffix. The premise retains the complete incoming and returned state, so local callbacks and their histories are not discarded by this transport. -/
theorem interpreted_fields {ι : Type} {target : OracleSpec ι} {State : Type}
    (impl : QueryImpl (Spec Reader E Shared) (StateT State (OracleComp target)))
    (verified : Verified Reader) (ephemeral : Ephemeral E) (reply : Option (Ciphertext × Word32))
    (before after : State) (input : Inputs Reader E Shared)
    (reached : (some input, after) ∈ support
      ((simulateQ impl (afterEncapsulation verified ephemeral reply)).run before)) :
    input.verified = verified ∧ input.ephemeral = ephemeral ∧
      reply = some (input.ciphertext, input.kem) := by
  apply after_fields verified ephemeral reply input
  apply support_simulateQ_run'_subset impl _ before
  change some input ∈ support (Prod.fst <$> ((simulateQ impl
    (afterEncapsulation verified ephemeral reply)).run before))
  rw [support_map]
  exact Set.mem_image_of_mem _ reached

end BeaconcryptCore.Computational.PqxdhRegistrationJointKemCollected

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemCollected.after_fields' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemCollected.after_fields

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemCollected.collect_split' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemCollected.collect_split

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemCollected.interpreted_fields' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemCollected.interpreted_fields
