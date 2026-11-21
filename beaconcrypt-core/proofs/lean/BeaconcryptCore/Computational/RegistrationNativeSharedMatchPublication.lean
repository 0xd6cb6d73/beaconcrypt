-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSharedMatchCollision
import BeaconcryptCore.Computational.RegistrationNativeKemPublicTarget
/-! The original public matching scanner retains an actual successful bundle entry. Lower source publication receipts can therefore identify its generated Ed key without inverting record AD. Actual run wrappers must discharge the receipt invariant from the unchanged publication trace. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true
namespace BeaconcryptCore.Computational.RegistrationNativeSharedMatchPublication
open PqxdhServerAuthExperiment (Codec)
open PqxdhDeploymentServerAuthEvent (Reg bundleOfReg keysOfBundle publishedKeys)
variable {Reader Response : Type}

/-- Every successful public published-key lookup selects a literal earlier bundle and its original raw parser fields. -/
theorem published_bundle (codec : Codec Reader Response) (regs : List Reg) (owner : Nat)
    (keys : PqxdhEd25519EufCma.Ed25519PublicKey × PqxdhEd25519EufCma.Phase1KeyTuple)
    (selected : publishedKeys codec regs owner = some keys) :
    ∃ raw candidate, Reg.bundle owner (some raw) ∈ regs ∧
      PqxdhDeploymentTranscript.candidateOf codec raw = some candidate ∧
      PqxdhEd25519EufCma.parseIdentity candidate.identityKey = some keys.1 := by
  cases bundled : bundleOfReg regs owner with
  | none => simp [publishedKeys, keysOfBundle, bundled] at selected
  | some raw =>
    change (do
      let raw ← bundleOfReg regs owner
      let candidate ← PqxdhDeploymentTranscript.candidateOf codec raw
      let identity ← PqxdhEd25519EufCma.parseIdentity candidate.identityKey
      let tuple ← PqxdhDeploymentPublishedTuple.candidateTuple candidate
      pure (identity, tuple)) = some keys at selected
    rw [bundled] at selected
    change (do
      let candidate ← PqxdhDeploymentTranscript.candidateOf codec raw
      let identity ← PqxdhEd25519EufCma.parseIdentity candidate.identityKey
      let tuple ← PqxdhDeploymentPublishedTuple.candidateTuple candidate
      pure (identity, tuple)) = some keys at selected
    obtain ⟨candidate, parsed, rest⟩ := Option.bind_eq_some_iff.mp selected
    obtain ⟨identity, identityAt, rest⟩ := Option.bind_eq_some_iff.mp rest
    obtain ⟨tuple, _tupleAt, equal⟩ := Option.bind_eq_some_iff.mp rest
    cases equal
    refine ⟨raw, candidate, ?_, parsed, identityAt⟩
    obtain ⟨reg, member, found⟩ := List.exists_of_findSome?_eq_some bundled
    cases reg with
    | bundle index reply =>
      cases reply with
      | none => cases found
      | some encoded =>
        simp only at found
        split at found
        · rename_i same
          simp only [Option.some.injEq] at found
          subst index encoded
          exact member
        · cases found
    | _ => cases found

/-- Internal source receipt shape: each reached original bundle is read as the packet with the same final generated owner's key. The actual run wrapper derives this from its publication trace. -/
def Receipts (joint : PqxdhJointIdentity.Primitives) (wire : RegistrationNativeWire.Wire)
    (regs : List Reg) (identities : List PqxdhJointIdentity.IdentitySeed) : Prop :=
  ∀ owner raw, Reg.bundle owner (some raw) ∈ regs →
    ∃ seed packet, identities[owner]? = some seed ∧ RegistrationNativeWire.readInit wire raw = some packet ∧
      PqxdhEd25519EufCma.parseIdentity (PqxdhRefinement.absBytes packet.identity_key) = some (joint.publicKeys seed).ed25519

/-- A public matching key is the exact generated source key retained by the real packet receipt; no AD identity inverse is used. -/
theorem generated_key (joint : PqxdhJointIdentity.Primitives) (wire : RegistrationNativeWire.Wire)
    (regs : List Reg) (identities : List PqxdhJointIdentity.IdentitySeed) (receipts : Receipts joint wire regs identities)
    (before : List Reg) (earlier : before <+: regs) (owner : Nat)
    (keys : PqxdhEd25519EufCma.Ed25519PublicKey × PqxdhEd25519EufCma.Phase1KeyTuple)
    (selected : publishedKeys (RegistrationNativeWire.ledgerCodec wire) before owner = some keys) :
    ∃ seed, identities[owner]? = some seed ∧ keys.1 = (joint.publicKeys seed).ed25519 := by
  obtain ⟨raw, candidate, bundled, parsed, key⟩ := published_bundle (RegistrationNativeWire.ledgerCodec wire) before owner keys selected
  obtain ⟨seed, packet, stored, read, identity⟩ := receipts owner raw (earlier.subset bundled)
  have actual := RegistrationNativeKemPublicTarget.candidate_read wire raw packet read
  have same : RegistrationRootInput.candidate packet = candidate := Option.some.inj (actual.symm.trans parsed)
  rw [← same] at key
  exact ⟨seed, stored, Option.some.inj (key.symm.trans identity)⟩

end BeaconcryptCore.Computational.RegistrationNativeSharedMatchPublication

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSharedMatchPublication.published_bundle' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSharedMatchPublication.published_bundle

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSharedMatchPublication.generated_key' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSharedMatchPublication.generated_key
