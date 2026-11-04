-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorCompiler

/-! Before the guessed bundle attempt is armed, the actual censor proxy is precisely the original combined source language with an input recorder. This is a complete adaptive OracleComp equality; selection, placeholder signatures and hidden-address tokens are absent throughout this legal prefix. The recorder's initial known-input list is supplied by the actual startup journal receipt. -/
open OracleComp OracleSpec
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityCensorPrefix
open RegistrationNativeIdentityCensorCompiler (Mode Spec implementation)
open PqxdhEd25519EufCma (Ed25519Signature)
variable {Value : Type}
abbrev SourceSpec := RegistrationNativePlatformIdentityCtxCompiler.Spec

def embed : QueryImpl SourceSpec (OracleComp Spec)
  | .inl query => RegistrationNativeIdentityCensorCompiler.protocol query
  | .inr bytes => Spec.query (.inr ⟨none, some bytes⟩)

def next (before : Mode) : SourceSpec.Domain → Mode
  | .inl _ => before
  | .inr bytes => { before with knownInputs := before.knownInputs ++ [bytes] }

def record : QueryImpl SourceSpec (StateT Mode (OracleComp Spec)) := fun query before => do
  let reply ← embed query
  pure (reply, next before query)

def Unarmed (before : Mode) : Prop := before.armed = false ∧ before.target = none ∧ before.active = false

private theorem next_unarmed (before : Mode) (prior : Unarmed before) (query : SourceSpec.Domain) :
    Unarmed (next before query) := by
  cases query <;> exact prior

/-- Every actual preselection source query is forwarded unchanged, with its literal known input appended once. -/
theorem query (selected : Nat) (placeholder : Ed25519Signature) (request : SourceSpec.Domain)
    (before : Mode) (prior : Unarmed before) :
    (implementation selected placeholder request).run before = (record request).run before := by
  rcases before with ⟨bundles, armed, active, target, inputs⟩
  change armed = false ∧ target = none ∧ active = false at prior
  rcases prior with ⟨rfl, rfl, rfl⟩
  cases request with
  | inr bytes =>
    simp [implementation, RegistrationNativeIdentityCensorCompiler.hashInput, StateT.run, record, embed, next]
  | inl query => cases query with
    | inr report => rfl
    | inl query => cases query with
      | inl coin => rfl
      | inr query => cases query with
        | create | reveal handle => rfl
        | service handle request => cases request with
          | staticDh peer => rfl
          | sign message =>
            change (RegistrationNativeIdentityCensorCompiler.signing selected placeholder handle message).run _ = _
            rw [RegistrationNativeIdentityCensorCompiler.signing, StateT.run_bind]
            have prepared : (RegistrationNativeIdentityCensorCompiler.prepare selected handle message).run
                ⟨bundles, false, false, none, inputs⟩ = pure ((), ⟨bundles, false, false, none, inputs⟩) := by
              by_cases eligible : handle = selected ∧ RegistrationNativeIdentitySigningRole.oneTime message
              · simp [RegistrationNativeIdentityCensorCompiler.prepare, StateT.run, eligible]
              · simp [RegistrationNativeIdentityCensorCompiler.prepare, StateT.run, eligible]
            rw [prepared, pure_bind]
            rw [StateT.run_bind, StateT.run_get, pure_bind]
            have missing : ¬ (none : Option Pqxdh.Bytes) = some message := by intro impossible; cases impossible
            simp only [missing, and_false, ite_false]
            rfl


/-- The complete adaptive legal prefix retains every original reply and source query, including calls for uncreated indices and repeated signatures. -/
theorem program (selected : Nat) (placeholder : Ed25519Signature) (work : OracleComp SourceSpec Value)
    (before : Mode) (prior : Unarmed before) :
    (simulateQ (implementation selected placeholder) work).run before =
      (simulateQ record work).run before := by
  induction work using OracleComp.inductionOn generalizing before with
  | pure value => rfl
  | query_bind request continued ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
    rw [query selected placeholder request before prior]
    simp only [record, StateT.run, bind_assoc, pure_bind]
    exact bind_congr (fun reply => ih reply (next before request) (next_unarmed before prior request))

end BeaconcryptCore.Computational.RegistrationNativeIdentityCensorPrefix
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorPrefix.query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorPrefix.query
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorPrefix.program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorPrefix.program
