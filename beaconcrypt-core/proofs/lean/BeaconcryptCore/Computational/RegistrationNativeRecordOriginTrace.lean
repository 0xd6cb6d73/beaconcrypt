-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeRecordLedger
import BeaconcryptCore.Computational.CborRawRecordOriginPrefixes

/-! Native ML metadata restoration preserves the exact chronological publication prefix of every actual ordinary raw receive. Later native calls cannot replace this prefix or its failed-writer witness. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true
namespace BeaconcryptCore.Computational.RegistrationNativeRecordOriginTrace
open PqxdhRecordLiftIdeal (CtxPrivate PublishedBefore)
open PqxdhDeploymentInterface (Entry Handle)
open PqxdhRecordFactsOriginPublicationTemporal (AcceptedBefore ReceivedBefore)
open PqxdhRecordFactsOriginPublicationPrefixes (Prefixes)
open RegistrationNativeEntropyTrace (strip stripEntry)
variable {n : Nat} {Reader Response : Type}

/-- Metadata decoding retains every publication with its literal sender, frame and ordering. -/
theorem published_strip (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (transcript : List Entry) (handle : Handle) (frame : PqxdhDeploymentNative.Frame) :
    PublishedBefore codec (strip transcript) handle frame ↔ PublishedBefore codec transcript handle frame := by
  unfold PublishedBefore
  rw [RegistrationNativeEntropyTrace.projection_strip Entry.published (fun _ _ _ => rfl)]

private theorem accepted_strip (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (control : PqxdhRecordLiftProtocol.Control n) (secret : CtxPrivate n) (transcript : List Entry)
    (handle : Handle) (raw : Pqxdh.Bytes) (opened : RawCtxWholeOwner.Decrypted)
    (good : AcceptedBefore codec control secret transcript handle raw opened) :
    AcceptedBefore codec control secret (strip transcript) handle raw opened := by
  rcases good with known | ⟨label, slot, direction, frame, decoded, entry, present, matched, plaintext, sender, owned, outcome⟩
  · exact Or.inl known
  · exact Or.inr ⟨label, slot, direction, frame, decoded, entry, present, matched, plaintext, sender, owned,
      outcome.imp_right ((published_strip codec transcript sender frame).mpr)⟩

private theorem entry_received (original decoded : Entry) (same : stripEntry original = some decoded) :
    original.received = decoded.received := by
  have projected := congrArg List.head? (RegistrationNativeEntropyTrace.projection_strip
    Entry.received (fun _ _ _ => rfl) [original])
  simp only [strip, List.filterMap_cons, same, List.filterMap_nil] at projected
  cases first : original.received <;> cases second : decoded.received
  all_goals simp only [first, second, List.head?_cons, List.head?_nil] at projected ⊢
  all_goals exact projected.symm

/-- Every received native entry keeps exactly the stripped original source prefix, including all optional failure entries before it. -/
theorem strip_prefixes (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (control : PqxdhRecordLiftProtocol.Control n)
    (secret : CtxPrivate n) (transcript : List Entry) (good : Prefixes codec route control secret transcript) :
    Prefixes codec route control secret (strip transcript) := by
  intro before event after split
  obtain ⟨left, rest, full, leftMap, restMap⟩ := List.filterMap_eq_append_iff.mp split
  obtain ⟨skipped, original, tail, restFull, skippedNone, selected, _tailMap⟩ := List.filterMap_eq_cons_iff.mp restMap
  have sourceSplit : transcript = (left ++ skipped) ++ original :: tail := by
    rw [full, restFull, List.append_assoc]
  have empty : strip skipped = [] := List.filterMap_eq_nil_iff.mpr skippedNone
  have beforeMap : strip (left ++ skipped) = before := by
    rw [RegistrationNativeEntropyTrace.strip_append, empty, List.append_nil]
    exact leftMap
  intro receiver raw opened returned
  obtain ⟨handle, routed, accepted⟩ := good (left ++ skipped) original tail sourceSplit receiver raw opened
    ((entry_received original event selected).trans returned)
  exact ⟨handle, routed, beforeMap ▸ accepted_strip codec control secret (left ++ skipped) handle raw opened accepted⟩

end BeaconcryptCore.Computational.RegistrationNativeRecordOriginTrace
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeRecordOriginTrace.published_strip' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeRecordOriginTrace.published_strip

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeRecordOriginTrace.strip_prefixes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeRecordOriginTrace.strip_prefixes
