-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeMldsaEager
import BeaconcryptCore.Computational.RegistrationNativeMldsaTableProgram
import BeaconcryptCore.Computational.PqxdhRecordLiftFlat

/-! Actual private table rows retain the ordinal of their successful named generation attempt. Failed generation still advances that ordinal. Provenance and finite generation caps are derived from the literal interpreter; a live credential's public key then selects an already sampled successful attempt without requiring independent or injective keys. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeMldsaBirthProvenance
open RegistrationNativeMldsa (Source Credential)
open RegistrationNativeMldsaOpaque (Pool handleSource birth record Live)
open RegistrationNativeMldsaEager (IsGenerate)
variable {Value : Type} (source : Source)

structure Provenance (before : Pool source) : Prop where
  aligned : before.keys.length = before.bornAt.length
  earlier : ∀ ordinal ∈ before.bornAt, ordinal < before.attempts

private theorem birth_provenance (before : Pool source) (generated : Option (Credential source) × Nat)
    (good : Provenance source before) : Provenance source (birth source before generated).2 := by
  constructor
  · exact RegistrationNativeMldsaOpaque.birth_aligned source before generated good.aligned
  · intro ordinal member
    rw [RegistrationNativeMldsaOpaque.birth_attempt]
    cases selected : generated.1 with
    | none =>
      simp only [birth, selected] at member
      exact Nat.lt_succ_of_lt (good.earlier ordinal member)
    | some key =>
      simp only [birth, selected, List.mem_append, List.mem_singleton] at member
      rcases member with old | rfl
      · exact Nat.lt_succ_of_lt (good.earlier ordinal old)
      · exact Nat.lt_succ_self _

private theorem record_provenance (before : Pool source) (credential : Credential (handleSource source))
    (request : beaconcrypt_core.registration.MldsaSigningRequest) (reply : RegistrationSigningShared.SignReply)
    (good : Provenance source before) : Provenance source (record source before credential request reply) :=
  ⟨good.aligned, good.earlier⟩

/-- Every named interpreter callback retains actual birth provenance and advances its attempt counter exactly on generation. -/
theorem step (query : (RegistrationNativeMldsaProgram.Spec (handleSource source)).Domain) (before : Pool source)
    (good : Provenance source before)
    (result : (RegistrationNativeMldsaProgram.Spec (handleSource source)).Range query × Pool source)
    (supported : result ∈ support ((RegistrationNativeMldsaTableProgram.handler source query).run before)) :
    Provenance source result.2 ∧ result.2.attempts = before.attempts + (if IsGenerate source query then 1 else 0) := by
  cases query with
  | inl coin =>
    simp only [RegistrationNativeMldsaTableProgram.handler, StateT.run_lift, bind_pure_comp, support_map] at supported
    obtain ⟨reply, _possible, rfl⟩ := supported
    exact ⟨good, by simp [IsGenerate]⟩
  | inr query => cases query with
    | generate =>
      simp only [RegistrationNativeMldsaTableProgram.handler, RegistrationNativeMldsaOpaque.actual, StateT.run, support_map] at supported
      obtain ⟨generated, _possible, rfl⟩ := supported
      exact ⟨birth_provenance source before generated good, by simp [IsGenerate, RegistrationNativeMldsaOpaque.birth_attempt]⟩
    | sign credential request =>
      simp only [RegistrationNativeMldsaTableProgram.handler, RegistrationNativeMldsaOpaque.actual, StateT.run] at supported
      cases selected : before.keys[credential.secret]? with
      | none =>
        simp only [selected, mem_support_pure_iff] at supported
        subst result
        exact ⟨record_provenance source before credential request _ good, by simp [record, IsGenerate]⟩
      | some key =>
        simp only [selected] at supported
        split at supported
        · rw [support_map] at supported
          obtain ⟨signed, _possible, rfl⟩ := supported
          exact ⟨record_provenance source before credential request _ good, by simp [record, IsGenerate]⟩
        · rw [mem_support_pure_iff] at supported
          subst result
          exact ⟨record_provenance source before credential request _ good, by simp [record, IsGenerate]⟩

/-- All actual raw free-program executions from the empty private table derive birth provenance, including all failed attempts. -/
theorem program (work : OracleComp (RegistrationNativeMldsaProgram.Spec (handleSource source)) Value)
    (result : Value × Pool source)
    (supported : result ∈ support (RegistrationNativeMldsaTableProgram.evaluate source work {})) :
    Provenance source result.2 := by
  apply PqxdhRecordLiftFlat.support_keep_oracle (RegistrationNativeMldsaTableProgram.handler source) (Provenance source)
    (fun query before good output reached => (step source query before good output reached).1) work {} _ result supported
  exact ⟨rfl, by simp⟩

/-- A named-generation cap bounds the actual private attempt counter independently of primitive coin counts and success. -/
theorem attempts (work : OracleComp (RegistrationNativeMldsaProgram.Spec (handleSource source)) Value)
    (cap : Nat) (bounded : work.IsQueryBoundP (IsGenerate source) cap)
    (before : Pool source) (good : Provenance source before) (result : Value × Pool source)
    (supported : result ∈ support (RegistrationNativeMldsaTableProgram.evaluate source work before)) :
    result.2.attempts ≤ before.attempts + cap := by
  induction work using OracleComp.inductionOn generalizing cap before with
  | pure value =>
    simp only [RegistrationNativeMldsaTableProgram.evaluate, simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at supported
    subst result
    change before.attempts ≤ before.attempts + cap
    omega
  | query_bind query next ih =>
    rw [isQueryBoundP_query_bind_iff] at bounded
    simp only [RegistrationNativeMldsaTableProgram.evaluate, simulateQ_bind, simulateQ_spec_query, StateT.run_bind,
      mem_support_bind_iff] at supported
    obtain ⟨middle, reached, continued⟩ := supported
    have advanced := step source query before good middle reached
    have suffix := ih middle.1 _ (bounded.2 middle.1) middle.2 advanced.1 continued
    split_ifs at advanced with selected
    · have room : 0 < cap := bounded.1.resolve_left (fun negative => negative selected)
      simp only [selected, ite_true] at suffix
      omega
    · simp only [selected, ite_false] at suffix
      omega

/-- Every live protected native credential has a literal successful generation ordinal and public key at that actual prefix. -/
theorem live (before : Pool source) (good : Provenance source before)
    (credential : Credential (handleSource source)) (key : Credential source) (present : Live source before credential key) :
    ∃ ordinal, before.bornAt[credential.secret]? = some ordinal ∧ ordinal < before.attempts ∧ credential.publicKey = key.publicKey := by
  have keyIndex : credential.secret < before.keys.length := List.getElem?_eq_some_iff.mp present.1 |>.1
  have birthIndex : credential.secret < before.bornAt.length := good.aligned ▸ keyIndex
  refine ⟨before.bornAt[credential.secret], by simp only [List.getElem?_eq_getElem birthIndex], ?_, present.2⟩
  exact good.earlier _ (List.getElem_mem birthIndex)

end BeaconcryptCore.Computational.RegistrationNativeMldsaBirthProvenance
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaBirthProvenance.step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaBirthProvenance.step

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaBirthProvenance.program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaBirthProvenance.program

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaBirthProvenance.attempts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaBirthProvenance.attempts

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaBirthProvenance.live' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaBirthProvenance.live
