-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeLorCanonical
import BeaconcryptCore.Computational.RegistrationNativeEntropyDesignation
import BeaconcryptCore.Computational.CborRawRecordLorInitial

/-! The native entropy adapter preserves every admitted test and its literal original bit. Removing HMAC transport metadata changes neither test admission nor the hidden-handle predicate; canonical eligibility factors through a reified native mode-P transcript with no private test bit or fresh message. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeLorTransport
open PqxdhDeploymentInterface (Entry Handle)
open RegistrationNativeEntropyTrace (strip stripEntry)
variable {Value : Type}

theorem firstTest_strip (transcript : List Entry) :
    PqxdhRecordLiftIdeal.firstTest (strip transcript) = PqxdhRecordLiftIdeal.firstTest transcript := by
  unfold PqxdhRecordLiftIdeal.firstTest
  apply RegistrationNativeEntropyTrace.findSome_strip
  intro key message reply
  rfl

theorem admitted_strip (crypto : Pqxdh.Crypto) (wire : RegistrationNativeWire.Wire) (serverKeyId : U64)
    (transcript : List Entry) (handle : Handle) (left right : Pqxdh.Bytes) :
    PqxdhRecordLiftIdeal.AdmittedTest crypto (RegistrationNativeWire.ledgerCodec wire) serverKeyId (strip transcript) handle left right ↔
      PqxdhRecordLiftIdeal.AdmittedTest crypto (RegistrationNativeWire.ledgerCodec wire) serverKeyId transcript handle left right := by
  simp only [PqxdhRecordLiftIdeal.AdmittedTest, firstTest_strip, RegistrationNativeEntropyDesignation.sameSession_strip]

private theorem strip_test (entry : Entry) (handle : Handle) (left right : Pqxdh.Bytes)
    (query : entry.query = .inr (.test handle left right)) : stripEntry entry = some entry := by
  rcases entry with ⟨query, reply⟩
  cases query
  rfl

private theorem original_test (original restored : Entry) (handle : Handle) (left right : Pqxdh.Bytes)
    (stripped : stripEntry original = some restored) (query : restored.query = .inr (.test handle left right)) : original = restored := by
  rcases original with ⟨(coin | command) | secrecy, reply⟩
  · exact Option.some.inj stripped
  · cases command <;> try exact Option.some.inj stripped
    rename_i key message
    simp only [stripEntry] at stripped
    cases decoded : RegistrationNativeEntropyInterface.decode message with
    | none => simp only [decoded] at stripped; cases stripped
    | some transport =>
        cases transport with
        | metadata mlPin => simp only [decoded] at stripped; cases stripped
        | hmac message =>
            simp only [decoded, Option.some.injEq] at stripped
            subst restored
            cases query
  · exact Option.some.inj stripped

/-- The complete admitted-test condition is unchanged by transport stripping in both directions. -/
theorem onTests_strip (crypto : Pqxdh.Crypto) (wire : RegistrationNativeWire.Wire) (serverKeyId : U64)
    (transcript : List Entry) (property : Handle → Prop) :
    RegistrationNativeLorCanonical.OnTests crypto wire serverKeyId (strip transcript) property ↔
      RegistrationNativeLorCanonical.OnTests crypto wire serverKeyId transcript property := by
  constructor
  · intro holds pre entry post handle left right split query admitted
    have preserved := strip_test entry handle left right query
    have actual : strip transcript = strip pre ++ entry :: strip post := by
      rw [split, RegistrationNativeEntropyTrace.strip_append]
      simp only [strip, List.filterMap_cons, preserved]
    exact holds (strip pre) entry (strip post) handle left right actual query
      ((admitted_strip crypto wire serverKeyId pre handle left right).2 admitted)
  · intro holds pre entry post handle left right split query admitted
    have lifted := split
    rw [strip, List.filterMap_eq_append_iff] at lifted
    obtain ⟨leading, rest, actual, leadingEq, restEq⟩ := lifted
    rw [List.filterMap_eq_cons_iff] at restEq
    obtain ⟨skipped, original, suffix, restSplit, skippedNone, restored, suffixEq⟩ := restEq
    have same := original_test original entry handle left right restored query
    subst original
    have skippedEmpty : strip skipped = [] := List.filterMap_eq_nil_iff.mpr skippedNone
    have leadingView : strip (leading ++ skipped) = pre := by
      rw [RegistrationNativeEntropyTrace.strip_append, skippedEmpty, List.append_nil]
      exact leadingEq
    have originalSplit : transcript = (leading ++ skipped) ++ entry :: suffix := by
      rw [actual, restSplit, List.append_assoc]
    exact holds (leading ++ skipped) entry suffix handle left right originalSplit query
      ((admitted_strip crypto wire serverKeyId (leading ++ skipped) handle left right).1 (leadingView ▸ admitted))


noncomputable def representative (transcript : List RegistrationNativeLedgerHiding.PublicEntry) : RegistrationNativeLedger.State :=
  let entries := transcript.map RegistrationNativeCanonicalSelector.reify
  ⟨⟨entries.map RegistrationNativeInterface.Entry.erase, none, []⟩, entries⟩

/-- Eligibility factors through a fixed public representative with no secret test state or fresh messages. -/
theorem j_representative (crypto : Pqxdh.Crypto) (wire : RegistrationNativeWire.Wire) (serverKeyId : U64)
    (budget : PqxdhDeploymentInterface.Budget) (filter : RegistrationNativeLorEvents.Filter Value)
    (target : Fin budget.accept × Fin budget.capacity) (value : Value) (ledger : RegistrationNativeLedger.State)
    (consistent : RegistrationNativeLedger.Consistent ledger) :
    RegistrationNativeLorCanonical.j crypto wire serverKeyId budget filter target (value, ledger) =
      RegistrationNativeLorCanonical.j crypto wire serverKeyId budget filter target
        (value, representative (ledger.transcript.map RegistrationNativeLedgerHiding.view)) := by
  have original : PqxdhDeploymentTranscript.SameView ledger.ledger.transcript
      (representative (ledger.transcript.map RegistrationNativeLedgerHiding.view)).ledger.transcript := by
    rw [consistent]
    simpa only [representative, PqxdhDeploymentTranscript.SameView, List.map_map, Function.comp_def] using (RegistrationNativeCanonicalSelector.erased_transcript ledger.transcript).symm
  apply RegistrationNativeLorCanonical.j_view crypto wire serverKeyId budget filter target value _ _ original
  simp only [representative, List.map_map, Function.comp_def, RegistrationNativeCanonicalSelector.reify_view]

theorem j_restored (crypto : Pqxdh.Crypto) (wire : RegistrationNativeWire.Wire) (serverKeyId : U64)
    (budget : PqxdhDeploymentInterface.Budget) (filter : RegistrationNativeLorEvents.Filter Value)
    (target : Fin budget.accept × Fin budget.capacity) (value : Value) (ledger : PqxdhDeploymentSecrecy.Ledger) :
    RegistrationNativeLorCanonical.j crypto wire serverKeyId budget filter target (value, RegistrationNativeEntropyRestore.ledger ledger) =
      RegistrationNativeLorCanonical.j crypto wire serverKeyId budget filter target
        (value, representative (RegistrationNativePublicObservation.restoreFrom [] (ledger.transcript.map (Entry.view .P))).2) := by
  rw [j_representative crypto wire serverKeyId budget filter target value _ (RegistrationNativeEntropyRestore.ledger_consistent ledger),
    RegistrationNativePublicObservation.ledger_public]

end BeaconcryptCore.Computational.RegistrationNativeLorTransport

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeLorTransport.firstTest_strip' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeLorTransport.firstTest_strip

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeLorTransport.admitted_strip' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeLorTransport.admitted_strip

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeLorTransport.onTests_strip' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeLorTransport.onTests_strip

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeLorTransport.j_representative' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeLorTransport.j_representative

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeLorTransport.j_restored' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeLorTransport.j_restored
