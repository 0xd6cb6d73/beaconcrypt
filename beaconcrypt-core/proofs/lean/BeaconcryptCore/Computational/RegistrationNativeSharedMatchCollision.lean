-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhDeploymentServerAuthEvent
import BeaconcryptCore.Computational.PqxdhIdentityCollisionReduction

/-! The original public SharedMatch registration predicate, without its old experiment-state wrapper, applies unchanged to the original ledger retained by the actual Native runtime. Its collision implication uses source session-handle uniqueness and published-key provenance. Actual source wrappers must discharge these internal invariants; this module supplies neither an AD inverse nor a new public security premise. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true
namespace BeaconcryptCore.Computational.RegistrationNativeSharedMatchCollision
open PqxdhJointIdentity
open PqxdhServerAuthExperiment (Codec)
open PqxdhDeploymentServerAuthEvent (Reg accepted MatchedAt publishedKeys)
variable {Reader Response : Type}

/-- This is exactly the original SharedMatch predicate on registration entries: two distinct accepted owners, one common matching Server session, and their original public matching tests. -/
def SharedMatch (crypto : Pqxdh.Crypto) (codec : Codec Reader Response) (first second : Nat)
    (regs : List Reg) : Prop :=
  first ≠ second ∧ ∃ session,
    (∃ before raw, accepted first regs = some (before, raw) ∧ MatchedAt crypto codec first session before raw) ∧
    (∃ before raw, accepted second regs = some (before, raw) ∧ MatchedAt crypto codec second session before raw)

/-- The public matching itself fixes one accepted candidate at the unique session handle; original publication provenance then identifies both generated owner keys. No identity is inferred from opaque record AD. -/
theorem shared_collision (joint : Primitives) (crypto : Pqxdh.Crypto) (codec : Codec Reader Response)
    (regs : List Reg) (identities : List IdentitySeed)
    (unique : ∀ raw other session, Reg.accept raw (some session) ∈ regs →
      Reg.accept other (some session) ∈ regs → raw = other)
    (published : ∀ before, before <+: regs → ∀ owner keys, publishedKeys codec before owner = some keys →
      ∃ seed, identities[owner]? = some seed ∧ keys.1 = (joint.publicKeys seed).ed25519)
    (first second : Nat) (shared : SharedMatch crypto codec first second regs) :
    PqxdhDeploymentServerAuthInjective.Collision joint identities := by
  obtain ⟨different, session, ⟨before, raw, acceptedAt, matched⟩,
    ⟨otherBefore, otherRaw, otherAcceptedAt, otherMatched⟩⟩ := shared
  have firstPrefix := PqxdhDeploymentServerAuthEvent.accepted_prefix first regs before raw acceptedAt
  have otherPrefix := PqxdhDeploymentServerAuthEvent.accepted_prefix second regs otherBefore otherRaw otherAcceptedAt
  obtain ⟨acceptRaw, candidate, keys, _payload, _reply, _record, acceptMember, candidateAt, keysAt, publishedAt, _⟩ := matched
  obtain ⟨otherAcceptRaw, otherCandidate, otherKeys, _otherPayload, _otherReply, _otherRecord,
    otherAcceptMember, otherCandidateAt, otherKeysAt, otherPublishedAt, _⟩ := otherMatched
  have rawSame := unique acceptRaw otherAcceptRaw session (firstPrefix.subset acceptMember) (otherPrefix.subset otherAcceptMember)
  subst otherAcceptRaw
  rw [candidateAt, Option.some.injEq] at otherCandidateAt
  subst otherCandidate
  rw [keysAt, Option.some.injEq] at otherKeysAt
  subst otherKeys
  obtain ⟨firstSeed, firstAt, firstKey⟩ := published before firstPrefix first keys publishedAt
  obtain ⟨secondSeed, secondAt, secondKey⟩ := published otherBefore otherPrefix second keys otherPublishedAt
  exact ⟨first, second, different, firstSeed, secondSeed, firstAt, secondAt, firstKey.symm.trans secondKey⟩

end BeaconcryptCore.Computational.RegistrationNativeSharedMatchCollision

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSharedMatchCollision.shared_collision' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSharedMatchCollision.shared_collision
