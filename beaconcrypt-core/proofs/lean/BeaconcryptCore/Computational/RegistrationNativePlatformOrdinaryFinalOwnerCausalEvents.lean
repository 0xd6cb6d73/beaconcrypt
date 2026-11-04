-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryCausalPublication
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryFinalOwnerCausalEvents
variable {n count : Nat} {KemSK Platform : Type} {source : RegistrationNativeMldsa.Source}

/-- The strict earlier-publication failure at one actual successful accept, tested against an arbitrary final owner identity roster. -/
def At (crypto : Pqxdh.Crypto) (wire : RegistrationNativeWire.Wire)
    (identities : List PqxdhEd25519EufCma.Ed25519PublicKey) (transcript : List RegistrationNativeInterface.Entry) : Prop :=
  ∃ prior raw session candidate identity decoded owner,
    transcript = prior ++ [⟨.inl (.inr (.accept raw)), some session⟩] ∧
    PqxdhDeploymentTranscript.candidateOf (RegistrationNativeWire.ledgerCodec wire) raw = some candidate ∧
    PqxdhDeploymentTranscript.acceptedKeys crypto candidate = some (identity, decoded) ∧
    identities[owner]? = some identity ∧
    PqxdhDeploymentPublishedTuple.publishedTuple (RegistrationNativeWire.ledgerCodec wire)
      (prior.map RegistrationNativeInterface.Entry.erase) owner ≠ some decoded

/-- Original final-ledger causal tuple failure retains every subsequent callback and the final complete native owner eligibility. -/
def Historical (crypto : Pqxdh.Crypto) (wire : RegistrationNativeWire.Wire)
    (identities : List PqxdhEd25519EufCma.Ed25519PublicKey) (transcript : List RegistrationNativeInterface.Entry) : Prop :=
  ∃ earlier later, transcript = earlier ++ later ∧ At crypto wire identities earlier

/-- Every final owner remains eligible in each private public-ordinal receipt, including owners created after the receipt. -/
def Captured (crypto : Pqxdh.Crypto) (wire : RegistrationNativeWire.Wire)
    (identities : List PqxdhEd25519EufCma.Ed25519PublicKey)
    (state : PqxdhDeploymentSessionSnapshots.State (Fin count) RegistrationNativeInterface.FullSpec
      (RegistrationNativeLedger.State × (RegistrationNativeExperiment.State n KemSK source × Platform))) : Prop :=
  ∃ ordinal snapshot, state.captured ordinal = some snapshot ∧ At crypto wire identities snapshot.2.1.transcript

/-- The successful accept is not a bundle publication; the final-roster event is the original tuple predicate at that strict prefix. -/
theorem at_published (crypto : Pqxdh.Crypto) (wire : RegistrationNativeWire.Wire)
    (identities : List PqxdhEd25519EufCma.Ed25519PublicKey) (transcript : List RegistrationNativeInterface.Entry)
    (failed : At crypto wire identities transcript) :
    PqxdhDeploymentPublishedTuple.PublishedForgery crypto (RegistrationNativeWire.ledgerCodec wire)
      (transcript.map RegistrationNativeInterface.Entry.erase) identities := by
  obtain ⟨prior, raw, session, candidate, identity, decoded, owner, entries, parsed, verified, owned, unpublished⟩ := failed
  refine ⟨raw, session, ?_, candidate, identity, decoded, owner, parsed, verified, owned, ?_⟩
  · rw [entries, List.map_append, List.map_cons, List.map_nil]
    exact List.mem_append_right _ List.mem_cons_self
  · rw [entries, RegistrationNativePlatformOrdinaryCausalPublication.publication_before_accept]
    exact unpublished

/-- Adding future owner aliases cannot remove an earlier genuine final-roster origin failure. -/
theorem at_owner_extension (crypto : Pqxdh.Crypto) (wire : RegistrationNativeWire.Wire)
    (identities later : List PqxdhEd25519EufCma.Ed25519PublicKey) (transcript : List RegistrationNativeInterface.Entry)
    (failed : At crypto wire identities transcript) : At crypto wire (identities ++ later) transcript := by
  obtain ⟨prior, raw, session, candidate, identity, decoded, owner, entries, parsed, verified, owned, unpublished⟩ := failed
  have below := (List.getElem?_eq_some_iff.mp owned).1
  exact ⟨prior, raw, session, candidate, identity, decoded, owner, entries, parsed, verified,
    by simpa only [List.getElem?_append_left below] using owned, unpublished⟩

/-- Later publications and later owner creation cannot repair a historical failure; only publications strictly before its acceptance count. -/
theorem historical_extend (crypto : Pqxdh.Crypto) (wire : RegistrationNativeWire.Wire)
    (identities laterOwners : List PqxdhEd25519EufCma.Ed25519PublicKey)
    (transcript laterEntries : List RegistrationNativeInterface.Entry)
    (failed : Historical crypto wire identities transcript) :
    Historical crypto wire (identities ++ laterOwners) (transcript ++ laterEntries) := by
  obtain ⟨earlier, later, entries, failed⟩ := failed
  exact ⟨earlier, later ++ laterEntries, by rw [entries, List.append_assoc],
    at_owner_extension crypto wire identities laterOwners earlier failed⟩
end BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryFinalOwnerCausalEvents

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryFinalOwnerCausalEvents.at_published' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryFinalOwnerCausalEvents.at_published

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryFinalOwnerCausalEvents.at_owner_extension' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryFinalOwnerCausalEvents.at_owner_extension

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryFinalOwnerCausalEvents.historical_extend' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryFinalOwnerCausalEvents.historical_extend
