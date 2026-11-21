-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeKemCountedRecipientFamily

/-! Every private pool row reached in a bounded reserved execution belongs to the actual finite joint row/cost tape. The conclusion derives from real create control and the syntactic cap, including failed native prefixes; no equality of public-key bytes identifies a private recipient. -/
open OracleComp OracleSpec CoreModels Aeneas ENNReal
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeKemCountedReservedRows
open PqxdhServerAuthExperiment (Setup)
open RegistrationNativeKemCountedProgram (Spec handler)
open RegistrationNativeKemCountedRecipientSample (Draw)
open RegistrationNativeKemCountedReservation (reserved IsCreate)
open PqxdhLiveKemBirth (Pool)
variable {ι KemSK Value : Type} {base : OracleSpec ι}

abbrev Pair (KemSK : Type) := PqxdhKemIndCca.MlKem768PublicKey × KemSK

def Covered (tape : List (Draw KemSK)) (pool : Pool KemSK) : Prop :=
  ∀ pair ∈ pool.keys, pair ∈ tape.map Prod.fst

private theorem draw_keys (setup : Setup base KemSK)
    (query : (RegistrationNativeKemCountedCapability.LeafSpec KemSK).Domain)
    (noncreate : query ≠ .inl .create) (before : Pool KemSK)
    (result : (RegistrationNativeKemCountedCapability.LeafSpec KemSK).Range query × Pool KemSK)
    (supported : result ∈ support ((RegistrationNativeKemCountedCapability.draw setup.baseImpl setup.kem query).run before)) :
    result.2.keys = before.keys := by
  cases query with
  | inr key =>
      simp only [RegistrationNativeKemCountedCapability.draw, StateT.run_lift, bind_pure_comp, support_map] at supported
      obtain ⟨reply, _sampled, returned⟩ := supported
      cases returned
      rfl
  | inl query =>
      cases query with
      | create => exact (noncreate rfl).elim
      | reveal handle =>
          simp only [RegistrationNativeKemCountedCapability.draw, PqxdhLiveKemBirth.poolImpl, StateT.run,
            support_pure, Set.mem_singleton_iff] at supported
          cases supported
          rfl
      | decapsulate handle ciphertext =>
          simp only [RegistrationNativeKemCountedCapability.draw, PqxdhLiveKemBirth.poolImpl, StateT.run] at supported
          split at supported <;> simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at supported
          all_goals obtain ⟨reply, _decapsulated, returned⟩ := supported
          all_goals cases returned
          all_goals rfl

private theorem noncreate_keys (setup : Setup base KemSK) (tape : List (Draw KemSK))
    (query : (Spec KemSK).Domain) (noncreate : ¬ IsCreate query) (before : Pool KemSK)
    (result : (Spec KemSK).Range query × Pool KemSK)
    (supported : result ∈ support ((reserved setup tape query).run before)) : result.2.keys = before.keys := by
  cases query with
  | inl uniform =>
      change result ∈ support ((StateT.lift (unifSpec.query uniform) : StateT (Pool KemSK) ProbComp _).run before) at supported
      simp only [StateT.run_lift, bind_pure_comp, support_map] at supported
      obtain ⟨reply, _sampled, returned⟩ := supported
      cases returned
      rfl
  | inr query =>
      have same : reserved setup tape (.inr query) = handler setup.baseImpl setup.kem (.inr query) := by
        cases query with
        | inr key => rfl
        | inl pool => cases pool with
          | create => exact (noncreate trivial).elim
          | reveal _ => rfl
          | decapsulate _ _ => rfl
      rw [same] at supported
      have prior : (result.1.1, result.2) ∈ support ((RegistrationNativeKemCountedCapability.draw setup.baseImpl setup.kem query).run before) := by
        rw [← RegistrationNativeKemCountedCapability.actual_forget, support_map]
        exact Set.mem_image_of_mem _ supported
      apply draw_keys setup query _ before (result.1.1, result.2) prior
      intro equal
      subst query
      exact noncreate trivial

private theorem query_rows (setup : Setup base KemSK) (tape : List (Draw KemSK))
    (query : (Spec KemSK).Domain) (before : Pool KemSK) (result : (Spec KemSK).Range query × Pool KemSK)
    (supported : result ∈ support ((reserved setup tape query).run before)) (covered : Covered tape before)
    (room : before.keys.length + (if IsCreate query then 1 else 0) ≤ tape.length) :
    Covered tape result.2 ∧ result.2.keys.length ≤ before.keys.length + (if IsCreate query then 1 else 0) := by
  by_cases creates : IsCreate query
  · have selected : query = .inr (.inl .create) := by
      rcases query with uniform | (pool | key)
      · exact creates.elim
      · cases pool <;> simp_all only [IsCreate]
      · exact creates.elim
    subst query
    simp only [IsCreate, ite_true] at room ⊢
    cases found : tape[before.keys.length]? with
    | none =>
        have exhausted := List.getElem?_eq_none_iff.mp found
        omega
    | some drawn =>
        simp only [reserved, StateT.run, found, support_pure, Set.mem_singleton_iff] at supported
        cases supported
        constructor
        · intro pair member
          simp only [PqxdhLiveKemBirth.created, PqxdhLiveKemBirth.record, List.mem_append, List.mem_singleton] at member
          rcases member with older | equal
          · exact covered pair older
          · subst pair
            exact List.mem_map_of_mem (List.mem_of_getElem? found)
        · simp only [PqxdhLiveKemBirth.created, PqxdhLiveKemBirth.record, List.length_append, List.length_singleton, le_refl]
  · have keys := noncreate_keys setup tape query creates before result supported
    constructor
    · intro pair member
      rw [keys] at member
      exact covered pair member
    · simp only [keys, creates, ite_false, Nat.add_zero, le_refl]

/-- Actual bounded adaptive source calls retain only genuine rows from the complete private tape, with enough unused reservation for every remaining call. -/
theorem run (setup : Setup base KemSK) (tape : List (Draw KemSK)) (work : OracleComp (Spec KemSK) Value)
    (cap : Nat) (bounded : work.IsQueryBoundP (IsCreate (KemSK := KemSK)) cap)
    (before : Pool KemSK) (covered : Covered tape before) (room : before.keys.length + cap ≤ tape.length)
    (result : Value × Pool KemSK) (supported : result ∈ support ((simulateQ (reserved setup tape) work).run before)) :
    Covered tape result.2 := by
  induction work using OracleComp.inductionOn generalizing cap before result with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
      cases supported
      exact covered
  | query_bind query next ih =>
      rw [isQueryBoundP_query_bind_iff] at bounded
      simp only [simulateQ_query_bind, StateT.run_bind, mem_support_bind_iff] at supported
      obtain ⟨called, calledSupport, continued⟩ := supported
      have localRoom : before.keys.length + (if IsCreate query then 1 else 0) ≤ tape.length := by
        by_cases creates : IsCreate query
        · have positive : 0 < cap := bounded.1.resolve_left (not_not.mpr creates)
          simp only [creates, ite_true]
          omega
        · simp only [creates, ite_false]
          omega
      obtain ⟨afterCovered, afterLength⟩ := query_rows setup tape query before called calledSupport covered localRoom
      have afterRoom : called.2.keys.length + (if IsCreate query then cap - 1 else cap) ≤ tape.length := by
        by_cases creates : IsCreate query
        · have positive : 0 < cap := bounded.1.resolve_left (not_not.mpr creates)
          simp only [creates, ite_true] at afterLength ⊢
          omega
        · simp only [creates, ite_false] at afterLength ⊢
          omega
      exact ih called.1 _ (bounded.2 called.1) called.2 afterCovered afterRoom result continued

/-- A pool handle in an actual bounded execution names one exact private finite-family row, including public-key aliases. -/
theorem handle (setup : Setup base KemSK) (count : Nat) (rows : Fin count → Draw KemSK)
    (work : OracleComp (Spec KemSK) Value) (bounded : work.IsQueryBoundP (IsCreate (KemSK := KemSK)) count)
    (result : Value × Pool KemSK) (supported : result ∈ support
      ((simulateQ (reserved setup (List.ofFn rows)) work).run PqxdhLiveKemBirth.empty))
    (handle : Nat) (pair : Pair KemSK) (found : result.2.keys[handle]? = some pair) :
    ∃ target, (rows target).1 = pair := by
  have covered := run setup (List.ofFn rows) work count bounded PqxdhLiveKemBirth.empty
    (by intro pair member; exact False.elim (List.not_mem_nil member))
    (by simp only [PqxdhLiveKemBirth.empty, List.length_nil, Nat.zero_add, List.length_ofFn, le_refl]) result supported
  have member := covered pair (List.mem_of_getElem? found)
  obtain ⟨drawn, drawnMember, same⟩ := List.mem_map.mp member
  obtain ⟨target, named⟩ := List.mem_ofFn.mp drawnMember
  exact ⟨target, (congrArg Prod.fst named).trans same⟩
end BeaconcryptCore.Computational.RegistrationNativeKemCountedReservedRows

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemCountedReservedRows.run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemCountedReservedRows.run

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemCountedReservedRows.handle' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemCountedReservedRows.handle
