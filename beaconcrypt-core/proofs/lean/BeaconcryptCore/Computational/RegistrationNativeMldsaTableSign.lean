-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeMldsaTableProgram
import BeaconcryptCore.Computational.RegistrationNativeMldsaSignMap

/-! Generation-free programs whose named signing credentials are live interpret through the actual private table as the corresponding real-key signing program. The table's signing history remains private; no source count is replaced or erased. The syntactic valid-query condition is discharged by the actual controller and ownership proofs at use sites. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true
namespace BeaconcryptCore.Computational.RegistrationNativeMldsaTableSign
open RegistrationNativeMldsa (Source Credential)
open RegistrationNativeMldsaOpaque (Pool handleSource restore Live)
open RegistrationNativeMldsaPoolMap (CredentialLive)
open RegistrationNativeMldsaTableProgram (handler evaluate)
variable {Value : Type} (source : Source)

def SignOnly : (RegistrationNativeMldsaProgram.Spec (handleSource source)).Domain → Prop
  | .inr .generate => False
  | _ => True

def Valid (before : Pool source) : (RegistrationNativeMldsaProgram.Spec (handleSource source)).Domain → Prop
  | .inl _ => True
  | .inr (.sign credential _) => CredentialLive source before credential
  | .inr .generate => False

noncomputable def target (fallback : Credential source) (before : Pool source) :=
  RegistrationNativeMldsaProgram.actual (source := source) ∘ₛ
    RegistrationNativeMldsaSignMap.translation (restore source fallback before)

set_option backward.isDefEq.respectTransparency false in
theorem step_keys (query : (RegistrationNativeMldsaProgram.Spec (handleSource source)).Domain)
    (allowed : SignOnly source query) (before : Pool source)
    (result : (RegistrationNativeMldsaProgram.Spec (handleSource source)).Range query × Pool source)
    (supported : result ∈ support ((handler source query).run before)) : result.2.keys = before.keys := by
  cases query with
  | inl coin =>
      simp only [handler, StateT.run_lift, bind_pure_comp, support_map] at supported
      obtain ⟨reply, _reached, rfl⟩ := supported
      rfl
  | inr query => cases query with
    | generate => exact allowed.elim
    | sign credential request =>
        simp only [handler, RegistrationNativeMldsaOpaque.actual, StateT.run] at supported
        cases found : before.keys[credential.secret]? with
        | none =>
            simp only [found, support_pure, Set.mem_singleton_iff] at supported
            cases supported
            rfl
        | some key =>
            simp only [found] at supported
            split at supported
            next =>
              simp only [support_map, Set.mem_image] at supported
              obtain ⟨reply, _reached, rfl⟩ := supported
              rfl
            next =>
              simp only [support_pure, Set.mem_singleton_iff] at supported
              cases supported
              rfl

set_option backward.isDefEq.respectTransparency false in
theorem step_source (fallback : Credential source) (initial before : Pool source) (rows : before.keys = initial.keys)
    (query : (RegistrationNativeMldsaProgram.Spec (handleSource source)).Domain) (allowed : Valid source initial query) :
    Prod.fst <$> (handler source query).run before = target source fallback initial query := by
  cases query with
  | inl coin =>
      simp only [handler, StateT.run_lift, bind_pure_comp, Functor.map_map, target, QueryImpl.apply_compose,
        RegistrationNativeMldsaSignMap.translation, simulateQ_spec_query, RegistrationNativeMldsaProgram.actual]
      exact id_map _
  | inr query => cases query with
    | generate => exact allowed.elim
    | sign credential request =>
        obtain ⟨key, row, publicKey⟩ := allowed
        have current : Live source before credential key := ⟨by rw [rows]; exact row, publicKey⟩
        have leaf := RegistrationNativeMldsaOpaque.sign_source source before credential key current request
        have actualKey := RegistrationNativeMldsaOpaque.restore_live source fallback initial credential key ⟨row, publicKey⟩
        simp only [handler]
        rw [leaf]
        simp only [target, QueryImpl.apply_compose, RegistrationNativeMldsaSignMap.translation,
          simulateQ_spec_query, RegistrationNativeMldsaProgram.actual, Functor.map_map]
        rw [actualKey]
        exact id_map _

/-- Every reached table update in a generation-free program retains the exact private key rows. -/
theorem program_keys (work : OracleComp (RegistrationNativeMldsaProgram.Spec (handleSource source)) Value)
    (allowed : work.AllQueriesSatisfy (SignOnly source)) (before : Pool source)
    (result : Value × Pool source) (supported : result ∈ support (evaluate source work before)) : result.2.keys = before.keys := by
  induction work using OracleComp.inductionOn generalizing before with
  | pure value =>
      simp only [evaluate, simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
      cases supported
      rfl
  | query_bind query next ih =>
      obtain ⟨head, tail⟩ := (allQueriesSatisfy_query_bind_iff _ _ _).mp allowed
      simp only [evaluate, simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at supported
      obtain ⟨middle, reached, continued⟩ := supported
      exact (ih middle.1 (tail middle.1) middle.2 continued).trans (step_keys source query head before middle reached)

set_option maxRecDepth 2048 in
set_option backward.isDefEq.respectTransparency false in
/-- Actual private-table signing evaluates to actual real-key signing, with every optional result and source count retained. -/
theorem program_source (fallback : Credential source) (initial : Pool source)
    (work : OracleComp (RegistrationNativeMldsaProgram.Spec (handleSource source)) Value)
    (allowed : work.AllQueriesSatisfy (Valid source initial)) (before : Pool source) (rows : before.keys = initial.keys) :
    Prod.fst <$> evaluate source work before = simulateQ (target source fallback initial) work := by
  induction work using OracleComp.inductionOn generalizing before with
  | pure value => simp only [evaluate, simulateQ_pure, StateT.run_pure, map_pure]
  | query_bind query next ih =>
      obtain ⟨head, tail⟩ := (allQueriesSatisfy_query_bind_iff _ _ _).mp allowed
      simp only [evaluate, simulateQ_bind, simulateQ_spec_query, StateT.run_bind, map_bind]
      calc
        _ = (handler source query).run before >>= fun middle => simulateQ (target source fallback initial) (next middle.1) := by
          apply bind_congr_of_forall_mem_support
          intro middle reached
          have noGenerate : SignOnly source query := by cases query with
            | inl coin => trivial
            | inr query => cases query with
              | generate => exact head
              | sign _ _ => trivial
          have kept := step_keys source query noGenerate before middle reached
          exact ih middle.1 (tail middle.1) middle.2 (kept.trans rows)
        _ = (Prod.fst <$> (handler source query).run before) >>= fun reply => simulateQ (target source fallback initial) (next reply) := by
          rw [bind_map_left]
        _ = _ := by rw [step_source source fallback initial before rows query head]

end BeaconcryptCore.Computational.RegistrationNativeMldsaTableSign

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaTableSign.step_keys' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaTableSign.step_keys

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaTableSign.step_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaTableSign.step_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaTableSign.program_keys' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaTableSign.program_keys

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaTableSign.program_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaTableSign.program_source
