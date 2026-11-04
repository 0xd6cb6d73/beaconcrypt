-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeRegistrationLedgerLog
import BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryFinalOwnerCausalEvents
import BeaconcryptCore.Computational.RegistrationNativeKemPublicTarget
import BeaconcryptCore.Computational.RegistrationNativeParsedTarget
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeRegistrationMarkCausal
open RegistrationNativeRawRegistrationJournal (Mark rawMarks)
open RegistrationNativeRegistrationLedgerLog (marks transcript)

def bundle (owner : Nat) : Mark → Option Pqxdh.Bytes
  | .bundle index reply => if index = owner then reply else none
  | _ => none
def published (wire : RegistrationNativeWire.Wire) (entries : List Mark) (owner : Nat) :
    Option PqxdhEd25519EufCma.Phase1KeyTuple :=
  ((entries.findSome? (bundle owner)).bind (PqxdhDeploymentTranscript.candidateOf (RegistrationNativeWire.ledgerCodec wire))).bind
    PqxdhDeploymentPublishedTuple.candidateTuple

/-- Registration projection preserves the first successful bundle of every public owner, including all failed attempts. -/
theorem bundle_projection (wire : RegistrationNativeWire.Wire) (entries : List RegistrationNativeInterface.Entry) (owner : Nat) :
    (transcript wire entries).findSome? (bundle owner) =
      PqxdhDeploymentTranscript.bundleOf (entries.map RegistrationNativeInterface.Entry.erase) owner := by
  induction entries with
  | nil => rfl
  | cons entry entries ih =>
    rcases entry with ⟨((coin | command) | secrecy), reply⟩
    · simpa only [transcript, List.flatMap_cons, marks, rawMarks, List.nil_append, List.map_cons,
        RegistrationNativeInterface.Entry.erase, PqxdhDeploymentTranscript.bundleOf, List.findSome?_cons, Option.or] using ih
    · cases command
      case bundle index =>
        cases reply <;> by_cases same : index = owner <;>
          simp only [transcript, List.flatMap_cons, marks, rawMarks, List.map_cons,
            RegistrationNativeInterface.Entry.erase, RegistrationNativeInterface.eraseCommand,
            PqxdhDeploymentTranscript.bundleOf, List.findSome?_cons, bundle, same,
            ite_true, ite_false, List.cons_append, List.nil_append] at *
        all_goals exact ih
      case accept raw =>
        cases parsed : RegistrationNativeWire.readInit wire raw <;>
          simpa only [transcript, List.flatMap_cons, marks, rawMarks, parsed, List.nil_append,
            List.map_cons, RegistrationNativeInterface.Entry.erase, RegistrationNativeInterface.eraseCommand,
            PqxdhDeploymentTranscript.bundleOf, List.findSome?_cons, List.cons_append, bundle, Option.or] using ih
      all_goals
        simpa only [transcript, List.flatMap_cons, marks, rawMarks, List.nil_append, List.map_cons,
          RegistrationNativeInterface.Entry.erase, RegistrationNativeInterface.eraseCommand,
          PqxdhDeploymentTranscript.bundleOf, List.findSome?_cons, Option.or] using ih
    · simpa only [transcript, List.flatMap_cons, marks, List.nil_append, List.map_cons,
        RegistrationNativeInterface.Entry.erase, PqxdhDeploymentTranscript.bundleOf, List.findSome?_cons, Option.or] using ih

/-- Publication reads the same original bytes and classical key tuple before and after exact registration projection. -/
theorem published_projection (wire : RegistrationNativeWire.Wire) (entries : List RegistrationNativeInterface.Entry) (owner : Nat) :
    published wire (transcript wire entries) owner = PqxdhDeploymentPublishedTuple.publishedTuple
      (RegistrationNativeWire.ledgerCodec wire) (entries.map RegistrationNativeInterface.Entry.erase) owner := by
  rw [published, bundle_projection]
  rfl

/-- The marker event retains the original successful parsed accept, its exact verified tuple, strict earlier publication and arbitrary final owner roster. -/
def At (crypto : Pqxdh.Crypto) (wire : RegistrationNativeWire.Wire)
    (identities : List PqxdhEd25519EufCma.Ed25519PublicKey) (entries : List Mark) : Prop :=
  ∃ prior packet session identity decoded owner,
    entries = prior ++ [.accept packet (some session)] ∧
    PqxdhDeploymentTranscript.acceptedKeys crypto (RegistrationRootInput.candidate packet) = some (identity, decoded) ∧
    identities[owner]? = some identity ∧ published wire prior owner ≠ some decoded

def Historical (crypto : Pqxdh.Crypto) (wire : RegistrationNativeWire.Wire)
    (identities : List PqxdhEd25519EufCma.Ed25519PublicKey) (entries : List Mark) : Prop :=
  ∃ earlier later, entries = earlier ++ later ∧ At crypto wire identities earlier

/-- Every original successful native causal failure has the same decoded typed acceptance and exact strict earlier publications, against the full final owner eligibility. -/
theorem at_projection (crypto : Pqxdh.Crypto) (wire : RegistrationNativeWire.Wire)
    (identities : List PqxdhEd25519EufCma.Ed25519PublicKey) (entries : List RegistrationNativeInterface.Entry)
    (failed : RegistrationNativePlatformOrdinaryFinalOwnerCausalEvents.At crypto wire identities entries) :
    At crypto wire identities (transcript wire entries) := by
  obtain ⟨prior, raw, session, candidate, identity, decoded, owner, entriesEq, parsed, verified, owned, unpublished⟩ := failed
  obtain ⟨packet, read⟩ := RegistrationNativeParsedTarget.candidate_parsed wire raw candidate parsed
  have original : RegistrationRootInput.candidate packet = candidate :=
    Option.some.inj ((RegistrationNativeKemPublicTarget.candidate_read wire raw packet read).symm.trans parsed)
  refine ⟨transcript wire prior, packet, session, identity, decoded, owner, ?_, ?_, owned, ?_⟩
  · rw [entriesEq, transcript, List.flatMap_append]
    simp only [List.flatMap_cons, List.flatMap_nil, marks, rawMarks, read, List.append_nil]
    rfl
  · simpa only [original] using verified
  · simpa only [published_projection] using unpublished

/-- The original complete causal event transfers without erasing its later callbacks or narrowing future-created owner aliases. -/
theorem historical_projection (crypto : Pqxdh.Crypto) (wire : RegistrationNativeWire.Wire)
    (identities : List PqxdhEd25519EufCma.Ed25519PublicKey) (entries : List RegistrationNativeInterface.Entry)
    (failed : RegistrationNativePlatformOrdinaryFinalOwnerCausalEvents.Historical crypto wire identities entries) :
    Historical crypto wire identities (transcript wire entries) := by
  obtain ⟨earlier, later, split, failed⟩ := failed
  refine ⟨transcript wire earlier, transcript wire later, ?_, at_projection crypto wire identities earlier failed⟩
  rw [split, transcript, List.flatMap_append]
  rfl
end BeaconcryptCore.Computational.RegistrationNativeRegistrationMarkCausal

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeRegistrationMarkCausal.bundle_projection' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeRegistrationMarkCausal.bundle_projection
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeRegistrationMarkCausal.published_projection' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeRegistrationMarkCausal.published_projection
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeRegistrationMarkCausal.at_projection' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeRegistrationMarkCausal.at_projection
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeRegistrationMarkCausal.historical_projection' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeRegistrationMarkCausal.historical_projection
