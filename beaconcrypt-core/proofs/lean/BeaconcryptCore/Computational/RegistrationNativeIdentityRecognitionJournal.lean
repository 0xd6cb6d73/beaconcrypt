-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxSource
import BeaconcryptCore.Computational.RegistrationNativePlatformCtxProvenance
import BeaconcryptCore.Computational.RegistrationNativeIdentityRecognition

/-! A target chosen after a legal prefix is checked against every actual earlier CTX input. The combined indexed source preserves the physical backend's literal queried-input provenance. Consequently an unrecognized canonical hidden template was not already cached when suppression begins. The executable scan uses only the public target key/message and its finite raw-input journal. -/
open OracleComp OracleSpec CoreModels
set_option autoImplicit false
set_option warningAsError true
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityRecognitionJournal
open PqxdhEd25519EufCma (Ed25519PublicKey Ed25519Signature)
open RegistrationNativePlatformIdentityCtxSource (State implementation)
variable {Value : Type}

def scan (verify : Ed25519PublicKey → Pqxdh.Bytes → Ed25519Signature → Bool)
    (publicKey : Ed25519PublicKey) (message : Pqxdh.Bytes) (journal : List Pqxdh.Bytes) : Option Ed25519Signature :=
  journal.findSome? (RegistrationNativeIdentityRecognition.recognize verify publicKey message)

/-- Every returned candidate is valid, even when it differs from the canonical source signature. -/
theorem valid (verify : Ed25519PublicKey → Pqxdh.Bytes → Ed25519Signature → Bool)
    (publicKey : Ed25519PublicKey) (message : Pqxdh.Bytes) (journal : List Pqxdh.Bytes)
    (signature : Ed25519Signature) (found : scan verify publicKey message journal = some signature) :
    verify publicKey message signature = true := by
  obtain ⟨input, _member, recognized⟩ := List.exists_of_findSome?_eq_some found
  exact RegistrationNativeIdentityRecognition.valid verify publicKey message input signature recognized

private theorem query_provenance (primitives : PqxdhJointIdentity.Primitives)
    (query : RegistrationNativePlatformIdentityCtxCompiler.Spec.Domain) (before : State)
    (prior : RegistrationNativePlatformCtxProvenance.Provenance before.2)
    (after : RegistrationNativePlatformIdentityCtxCompiler.Spec.Range query × State)
    (reached : after ∈ support ((implementation primitives query).run before)) :
    RegistrationNativePlatformCtxProvenance.Provenance after.2.2 := by
  cases query with
  | inl query =>
    simp only [implementation, StateT.run, support_map] at reached
    obtain ⟨reply, _possible, same⟩ := reached
    cases same
    exact prior
  | inr bytes =>
    simp only [implementation, StateT.run, support_map] at reached
    obtain ⟨reply, possible, same⟩ := reached
    cases same
    exact RegistrationNativePlatformCtxProvenance.physical bytes before.2 prior reply possible

/-- The complete actual joint/hash source has no physical cache key outside its own chronological CTX-input journal. -/
theorem complete (primitives : PqxdhJointIdentity.Primitives)
    (work : OracleComp RegistrationNativePlatformIdentityCtxCompiler.Spec Value) (before : State)
    (prior : RegistrationNativePlatformCtxProvenance.Provenance before.2) (after : Value × State)
    (reached : after ∈ support ((simulateQ (implementation primitives) work).run before)) :
    RegistrationNativePlatformCtxProvenance.Provenance after.2.2 := by
  induction work using OracleComp.inductionOn generalizing before after with
  | pure value =>
    simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at reached
    cases reached
    exact prior
  | query_bind query next ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at reached
    obtain ⟨middle, called, continued⟩ := reached
    exact ih middle.1 middle.2 (query_provenance primitives query before prior middle called) after continued

/-- No-recognition of the actual finite history excludes every cache hit on a template containing a genuine target signature. -/
theorem cache_absent (verify : Ed25519PublicKey → Pqxdh.Bytes → Ed25519Signature → Bool)
    (publicKey : Ed25519PublicKey) (message leading trailing : Pqxdh.Bytes) (signature : Ed25519Signature)
    (before : RegistrationNativePlatformCtxBackend.State)
    (prior : RegistrationNativePlatformCtxProvenance.Provenance before)
    (verified : verify publicKey message signature = true)
    (unrecognized : scan verify publicKey message before.2 = none) :
    before.1 ((), leading ++ signature.toList ++ trailing) = none := by
  by_contra present
  have member := prior (leading ++ signature.toList ++ trailing) present
  have missing := List.findSome?_eq_none_iff.mp unrecognized _ member
  have recognized := RegistrationNativeIdentityRecognition.template_recognized verify publicKey message leading trailing signature verified
  rw [missing] at recognized
  contradiction

/-- The cache-exclusion receipt follows directly from an actual complete empty-cache source prefix; queried-input coverage is derived rather than supplied. -/
theorem initialized (primitives : PqxdhJointIdentity.Primitives)
    (work : OracleComp RegistrationNativePlatformIdentityCtxCompiler.Spec Value)
    (pool : PqxdhDynamicIdentityPool.SourceState) (after : Value × State)
    (reached : after ∈ support ((simulateQ (implementation primitives) work).run (pool, (∅, []))))
    (publicKey : Ed25519PublicKey) (message leading trailing : Pqxdh.Bytes) (signature : Ed25519Signature)
    (verified : primitives.verify publicKey message signature = true)
    (unrecognized : scan primitives.verify publicKey message after.2.2.2 = none) :
    after.2.2.1 ((), leading ++ signature.toList ++ trailing) = none :=
  cache_absent primitives.verify publicKey message leading trailing signature after.2.2
    (complete primitives work (pool, (∅, [])) RegistrationNativePlatformCtxProvenance.empty after reached)
    verified unrecognized

end BeaconcryptCore.Computational.RegistrationNativeIdentityRecognitionJournal
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityRecognitionJournal.valid' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityRecognitionJournal.valid
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityRecognitionJournal.complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityRecognitionJournal.complete
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityRecognitionJournal.cache_absent' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityRecognitionJournal.cache_absent
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityRecognitionJournal.initialized' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityRecognitionJournal.initialized
