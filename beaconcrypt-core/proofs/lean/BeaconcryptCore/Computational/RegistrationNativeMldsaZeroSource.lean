-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeMldsaCountStop
import BeaconcryptCore.Computational.RegistrationNativeMldsaTableProgram

/-! Actual private-table interpretation of a count-normalized ML program has the literal original generate/owned-sign distributions with zero private Nat replies. The table still records every failed attempt and successful birth ordinal. This is primitive-interface simplification after the separately checked protocol count-normalization theorem. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeMldsaZeroSource
open RegistrationNativeMldsa (Source Credential)
open RegistrationNativeMldsaOpaque (Pool handleSource birth record)
variable {Value : Type} (source : Source)

private theorem map_apply {S A B : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (observer : A → B) (work : StateT S m A) (before : S) :
    (observer <$> work) before = Prod.map observer id <$> work before := StateT.run_map observer work before

def zero {query : RegistrationNativeMldsaCapability.Request (handleSource source)}
    (result : (RegistrationNativeMldsaCapability.Spec (handleSource source)).Range query) := (result.1, (0 : Nat))

noncomputable def capability : QueryImpl (RegistrationNativeMldsaCapability.Spec (handleSource source)) (StateT (Pool source) ProbComp) := by
  classical
  exact fun query => match query with
  | .generate => fun before => (fun generated => birth source before (generated, 0)) <$> RegistrationNativeMldsa.generate source
  | .sign handle request => fun before =>
      match before.keys[handle.secret]? with
      | none => pure ((.None, 0), record source before handle request .None)
      | some key => if handle.publicKey = key.publicKey then
          (fun reply => ((reply, 0), record source before handle request reply)) <$> RegistrationNativeMldsa.owned source key request
        else pure ((.None, 0), record source before handle request .None)

noncomputable def handler : QueryImpl (RegistrationNativeMldsaProgram.Spec (handleSource source)) (StateT (Pool source) ProbComp)
  | .inl query => StateT.lift (unifSpec.query query)
  | .inr query => capability source query

noncomputable def evaluate (work : OracleComp (RegistrationNativeMldsaProgram.Spec (handleSource source)) Value) (before : Pool source) :
    ProbComp (Value × Pool source) := (simulateQ (handler source) work).run before

private theorem birth_zero (before : Pool source) (generated : Option (Credential source) × Nat) :
    Prod.map (zero source (query := .generate)) id (birth source before generated) = birth source before (generated.1, 0) := by
  rcases generated with ⟨generated, count⟩
  cases generated <;> rfl

/-- Removing only the primitive accounting reply exposes exactly the original optional generator and owned signer, with the same complete private table update. -/
theorem capability_source (query : RegistrationNativeMldsaCapability.Request (handleSource source)) (before : Pool source) :
    Prod.map (zero source) id <$> (RegistrationNativeMldsaOpaque.actual source query).run before =
      (capability source query).run before := by
  classical
  cases query with
  | generate =>
      rw [RegistrationNativeMldsaOpaque.generate_source]
      simp only [Functor.map_map, birth_zero]
      have same := congrArg (fun work => (fun generated => birth source before (generated, 0)) <$> work)
        (RegistrationNativeMldsaCapability.actual_forget source .generate)
      simp only [Functor.map_map] at same
      exact same
  | sign handle request =>
      simp only [RegistrationNativeMldsaOpaque.actual, capability, StateT.run]
      cases found : before.keys[handle.secret]? with
      | none => simp only [map_pure]; rfl
      | some key =>
          simp only
          split
          · have same := congrArg (fun work => (fun reply => ((reply, (0 : Nat)), record source before handle request reply)) <$> work)
              (RegistrationNativeMldsaCapability.actual_forget source (.sign key request))
            simp only [Functor.map_map, Prod.map, id_eq, zero] at same ⊢
            exact same
          · simp only [map_pure]; rfl

/-- The normalized request interpreter is the actual table interpreter followed by private Nat erasure, without changing any primitive call. -/
theorem translation : RegistrationNativeMldsaTableProgram.handler source ∘ₛ RegistrationNativeMldsaCountMap.translation = handler source := by
  funext query
  cases query with
  | inl coin => simp only [QueryImpl.apply_compose, RegistrationNativeMldsaCountMap.translation,
      simulateQ_spec_query, RegistrationNativeMldsaTableProgram.handler, handler]
  | inr query =>
      funext before
      simp only [QueryImpl.apply_compose, RegistrationNativeMldsaCountMap.translation,
        simulateQ_map, simulateQ_spec_query, RegistrationNativeMldsaTableProgram.handler,
        handler]
      rw [map_apply]
      exact capability_source source query before

/-- Every normalized adaptive native capability program has the exact count-free source primitive semantics with its full private key and signing history. -/
theorem source_program (work : OracleComp (RegistrationNativeMldsaProgram.Spec (handleSource source)) Value) (before : Pool source) :
    RegistrationNativeMldsaTableProgram.evaluate source (RegistrationNativeMldsaCountMap.transform work) before =
      evaluate source work before := by
  simp only [RegistrationNativeMldsaTableProgram.evaluate, RegistrationNativeMldsaCountMap.transform,
    ← QueryImpl.simulateQ_compose, translation, evaluate]
end BeaconcryptCore.Computational.RegistrationNativeMldsaZeroSource

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaZeroSource.capability_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaZeroSource.capability_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaZeroSource.translation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaZeroSource.translation

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaZeroSource.source_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaZeroSource.source_program
