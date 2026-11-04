-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeMldsa

/-! An ordinary generated-key, context-aware ML signing oracle. The adversary receives only the actual generated public key. Every matching complete signing request is recorded, including primitive failure; freshness concerns the context and message, so a repeated message with a different signature remains an old message. No native origin or source-profile conclusion occurs in the primitive game. -/
open OracleComp OracleSpec CoreModels Aeneas ENNReal
open Aeneas.Std hiding namespace core alloc
open beaconcrypt_core PqxdhRefinement
set_option autoImplicit false
set_option warningAsError true
namespace BeaconcryptCore.Computational.RegistrationNativeMldsaEuf
open RegistrationNativeMldsa (Source Credential)
open RegistrationSigningShared (SignReply)

abbrev SigningSpec : OracleSpec registration.MldsaSigningRequest := fun _ => SignReply
abbrev Spec := unifSpec + SigningSpec
abbrev PublicKey := Std.Array Std.U8 1952#usize

structure Forgery where
  request : registration.MldsaSigningRequest
  signature : Pqxdh.Bytes

def Fresh (history : List registration.MldsaSigningRequest) (forgery : Forgery) : Prop :=
  ∀ request ∈ history, (request.context, request.input) ≠ (forgery.request.context, forgery.request.input)

def Valid (source : Source) (publicKey : PublicKey) (forgery : Forgery) : Prop :=
  forgery.request.public_key = publicKey ∧ forgery.signature.length = 3309 ∧
    source.verify (absBytes publicKey) (absBytes forgery.request.context) (absBytes forgery.request.input) forgery.signature = true

noncomputable def signing (source : Source) (credential : Credential source) :
    QueryImpl SigningSpec (StateT (List registration.MldsaSigningRequest) ProbComp) := by
  classical
  exact fun request history => if request.public_key = credential.publicKey then
    (fun reply => (reply, history ++ [request])) <$> source.sign credential.secret request
  else pure (.None, history)

noncomputable def handler (source : Source) (credential : Credential source) :
    QueryImpl Spec (StateT (List registration.MldsaSigningRequest) ProbComp)
  | .inl query => StateT.lift (unifSpec.query query)
  | .inr request => signing source credential request

noncomputable def game (source : Source) (adversary : PublicKey → OracleComp Spec (Option Forgery)) : ProbComp Bool := do
  match ← RegistrationNativeMldsa.generate source with
  | none => pure false
  | some credential => do
      let result ← (simulateQ (handler source credential) (adversary credential.publicKey)).run []
      pure (@decide (∃ forgery, result.1 = some forgery ∧ Valid source credential.publicKey forgery ∧ Fresh result.2 forgery) (Classical.propDecidable _))

noncomputable def advantage (source : Source) (adversary : PublicKey → OracleComp Spec (Option Forgery)) : ℝ≥0∞ :=
  𝒟[game source adversary] {true}

/-- A matching oracle request records exactly its complete operands, regardless of its optional reply. -/
theorem signing_match (source : Source) (credential : Credential source) (request : registration.MldsaSigningRequest)
    (history : List registration.MldsaSigningRequest) (matching : request.public_key = credential.publicKey) :
    (signing source credential request).run history =
      (fun reply => (reply, history ++ [request])) <$> source.sign credential.secret request := by
  simp only [signing, StateT.run, ite_eq_left matching]

/-- Requests outside the one supplied public key obtain no signature and make no signing-oracle call. -/
theorem signing_mismatch (source : Source) (credential : Credential source) (request : registration.MldsaSigningRequest)
    (history : List registration.MldsaSigningRequest) (different : request.public_key ≠ credential.publicKey) :
    (signing source credential request).run history = pure (.None, history) := by
  simp only [signing, StateT.run, ite_eq_right different]

/-- Public reply erasure gives the exact original owned signer. -/
theorem signing_owned (source : Source) (credential : Credential source) (request : registration.MldsaSigningRequest)
    (history : List registration.MldsaSigningRequest) :
    Prod.fst <$> (signing source credential request).run history = RegistrationNativeMldsa.owned source credential request := by
  classical
  by_cases matching : request.public_key = credential.publicKey
  · rw [signing_match source credential request history matching, RegistrationNativeMldsa.owned_match source credential request matching,
      Functor.map_map]
    exact id_map _
  · rw [signing_mismatch source credential request history matching, RegistrationNativeMldsa.owned_mismatch source credential request matching, map_pure]

end BeaconcryptCore.Computational.RegistrationNativeMldsaEuf

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaEuf.signing_match' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaEuf.signing_match

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaEuf.signing_mismatch' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaEuf.signing_mismatch

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaEuf.signing_owned' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaEuf.signing_owned
