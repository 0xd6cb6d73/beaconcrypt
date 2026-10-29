-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationWorldSigning

/-! ML key generation and signing are explicit primitive source operations, alongside the existing context-aware verifier. Birth calls the generator and retains its exact returned public/private pair; it does not accept a caller-supplied local key. Owned signing checks that the actual native request names this generated public key and forwards its entire context, role and message to the source signer. These are executable source/ownership receipts, not an EUF assertion about an arbitrary primitive implementation. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open beaconcrypt_core
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RegistrationNativeMldsa
open RegistrationSigningShared (SignReply)

structure Source where
  SigningKey : Type
  generate : ProbComp (Option (Std.Array Std.U8 1952#usize × SigningKey))
  sign : SigningKey → registration.MldsaSigningRequest → ProbComp SignReply
  verify : MldsaTranscriptAuth.Verify

/-- A local credential retains the public/private pair; the actual generator support receipt is proved below. -/
structure Credential (source : Source) where
  publicKey : Std.Array Std.U8 1952#usize
  secret : source.SigningKey

def generate (source : Source) : ProbComp (Option (Credential source)) :=
  Option.map (fun pair => (⟨pair.1, pair.2⟩ : Credential source)) <$> source.generate

/-- The SDK signing identity is selected by ownership; the native request's complete operands are preserved on a matching public key. -/
noncomputable def owned (source : Source) (credential : Credential source)
    (request : registration.MldsaSigningRequest) : ProbComp SignReply := by
  classical
  exact if request.public_key = credential.publicKey then source.sign credential.secret request else pure .None

theorem generated_pair (source : Source) (credential : Credential source)
    (supported : some credential ∈ support (generate source)) :
    some (credential.publicKey, credential.secret) ∈ support source.generate := by
  simp only [generate, support_map] at supported
  obtain ⟨result, generated, equal⟩ := supported
  cases result with
  | none => cases equal
  | some pair =>
    cases pair
    cases equal
    exact generated

theorem owned_match (source : Source) (credential : Credential source)
    (request : registration.MldsaSigningRequest) (matching : request.public_key = credential.publicKey) :
    owned source credential request = source.sign credential.secret request := by
  simp only [owned, matching, ite_true]

theorem owned_mismatch (source : Source) (credential : Credential source)
    (request : registration.MldsaSigningRequest) (different : request.public_key ≠ credential.publicKey) :
    owned source credential request = pure .None := by
  simp only [owned, ite_eq_right different]

/-- The optional primitive failure precedes pin hashing or any later constructor draw. -/
theorem generation_failure (source : Source) (failed : source.generate = pure none) : generate source = pure none := by
  simp only [generate, failed, map_pure, Option.map_none]

/-- The source byte-query costs are inherited from the actual primitive bodies. -/
theorem generation_bound (source : Source) (count : Nat) (bounded : source.generate.IsTotalQueryBound count) :
    (generate source).IsTotalQueryBound count := by
  simpa only [generate, IsTotalQueryBound, isQueryBound_map_iff] using bounded

end BeaconcryptCore.Computational.RegistrationNativeMldsa

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsa.generated_pair' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsa.generated_pair

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsa.owned_match' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsa.owned_match

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsa.owned_mismatch' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsa.owned_mismatch

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsa.generation_failure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsa.generation_failure

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsa.generation_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsa.generation_bound
