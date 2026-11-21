-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePublicObservation
import BeaconcryptCore.Computational.CborRawRecordWeightedFresh

/-! A canonical APP target is computed from public observations and fresh-handle metadata, never from the private message. The reification of a success-only raw reply uses a fixed dummy plaintext solely to evaluate the already public designation function. Its mode-P projection is exactly the supplied public entry. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true
namespace BeaconcryptCore.Computational.RegistrationNativeCanonicalSelector
open RegistrationNativePublicObservation (firstAccept restoreFrom)
open RegistrationNativeLedgerHiding (view PublicEntry)
open RegistrationNativeInterface (Entry)
open PqxdhDeploymentInterface (Budget Handle)
variable {Value NativeState : Type}

def rawReply (success : Bool) : core.option.Option RawCtxWholeOwner.Decrypted :=
  if success then .Some ⟨[], 0#u64, 0#u64⟩ else .None

/-- A finite public representative; its dummy raw plaintexts never enter designation. -/
def reify : PublicEntry → Entry
  | ⟨.inl (.inl coin), reply⟩ => ⟨.inl (.inl coin), reply⟩
  | ⟨.inl (.inr (.create ed ml keyId)), reply⟩ => ⟨.inl (.inr (.create ed ml keyId)), reply⟩
  | ⟨.inl (.inr (.bundle owner)), reply⟩ => ⟨.inl (.inr (.bundle owner)), reply⟩
  | ⟨.inl (.inr (.accept raw)), reply⟩ => ⟨.inl (.inr (.accept raw)), reply⟩
  | ⟨.inl (.inr (.build session payload)), reply⟩ => ⟨.inl (.inr (.build session payload)), reply⟩
  | ⟨.inl (.inr (.finish owner raw)), reply⟩ => ⟨.inl (.inr (.finish owner raw)), reply⟩
  | ⟨.inl (.inr (.hmac key message)), reply⟩ => ⟨.inl (.inr (.hmac key message)), reply⟩
  | ⟨.inl (.inr (.hash bytes)), reply⟩ => ⟨.inl (.inr (.hash bytes)), reply⟩
  | ⟨.inl (.inr (.serverSend keyId plaintext)), reply⟩ => ⟨.inl (.inr (.serverSend keyId plaintext)), reply⟩
  | ⟨.inl (.inr (.serverRaw raw)), reply⟩ => ⟨.inl (.inr (.serverRaw raw)), rawReply reply⟩
  | ⟨.inl (.inr (.beaconSend owner plaintext)), reply⟩ => ⟨.inl (.inr (.beaconSend owner plaintext)), reply⟩
  | ⟨.inl (.inr (.beaconRaw owner raw)), reply⟩ => ⟨.inl (.inr (.beaconRaw owner raw)), rawReply reply⟩
  | ⟨.inr secrecy, reply⟩ => ⟨.inr secrecy, reply⟩

theorem reify_view (entry : PublicEntry) : view (reify entry) = entry := by
  rcases entry with ⟨(coin | command) | secrecy, reply⟩
  · rfl
  · cases command <;> try rfl
    all_goals cases reply <;> rfl
  · rfl

theorem erased_view (entry : Entry) :
    ((reify (view entry)).erase).view .P = entry.erase.view .P := by
  rcases entry with ⟨(coin | command) | secrecy, reply⟩
  · rfl
  · cases command <;> try rfl
    all_goals cases reply <;> rfl
  · rfl

theorem erased_transcript (transcript : List Entry) :
    PqxdhDeploymentTranscript.SameView
      ((transcript.map view).map fun entry => (reify entry).erase)
      (transcript.map Entry.erase) := by
  simp only [PqxdhDeploymentTranscript.SameView, List.map_map]
  exact List.map_congr_left fun entry _ => erased_view entry

abbrev Target (budget : Budget) := Fin budget.accept × Fin budget.capacity

/-- Both scans use only public data. In particular no supplied guess or private fresh message is read. -/
noncomputable def chooseFrom (crypto : Pqxdh.Crypto) (wire : RegistrationNativeWire.Wire)
    (serverKeyId : U64) (budget : Budget) (index : Option Nat)
    (transcript : List PublicEntry) (freshHandles : List Handle) : Option (Target budget) := do
  let index ← index
  let handle ← freshHandles[index]?
  let selected ← PqxdhDeploymentTranscript.designateIn crypto (RegistrationNativeWire.ledgerCodec wire)
    serverKeyId budget (transcript.map fun entry => (reify entry).erase) handle
  let first ← firstAccept wire selected.1.val transcript
  if bound : first.1 < budget.accept then some (⟨first.1, bound⟩, selected.2) else none

noncomputable def chooseLedger (crypto : Pqxdh.Crypto) (wire : RegistrationNativeWire.Wire)
    (serverKeyId : U64) (budget : Budget) (index : Option Nat) (ledger : RegistrationNativeLedger.State) :
    Option (Target budget) :=
  chooseFrom crypto wire serverKeyId budget index (ledger.transcript.map view)
    (ledger.ledger.fresh.map PqxdhDeploymentSecrecy.FreshEntry.handle)

/-- The public representative computes exactly the original designation on every consistent native ledger. -/
theorem designation (crypto : Pqxdh.Crypto) (wire : RegistrationNativeWire.Wire)
    (serverKeyId : U64) (budget : Budget) (ledger : RegistrationNativeLedger.State)
    (consistent : RegistrationNativeLedger.Consistent ledger) :
    PqxdhDeploymentTranscript.designateIn crypto (RegistrationNativeWire.ledgerCodec wire)
      serverKeyId budget ((ledger.transcript.map view).map fun entry => (reify entry).erase) =
      PqxdhDeploymentTranscript.designateIn crypto (RegistrationNativeWire.ledgerCodec wire)
        serverKeyId budget ledger.ledger.transcript := by
  exact consistent ▸ (PqxdhDeploymentTranscript.designate_view crypto (RegistrationNativeWire.ledgerCodec wire)
    serverKeyId _ _ (erased_transcript ledger.transcript)).2 budget

/-- The implemented selector reads the literal original designation and the actual indexed fresh handle. -/
theorem choose_literal (crypto : Pqxdh.Crypto) (wire : RegistrationNativeWire.Wire)
    (serverKeyId : U64) (budget : Budget) (index : Option Nat) (ledger : RegistrationNativeLedger.State)
    (consistent : RegistrationNativeLedger.Consistent ledger) :
    chooseLedger crypto wire serverKeyId budget index ledger = (do
      let index ← index
      let entry ← ledger.ledger.fresh[index]?
      let selected ← PqxdhDeploymentTranscript.designateIn crypto (RegistrationNativeWire.ledgerCodec wire)
        serverKeyId budget ledger.ledger.transcript entry.handle
      let first ← firstAccept wire selected.1.val (ledger.transcript.map view)
      if bound : first.1 < budget.accept then some (⟨first.1, bound⟩, selected.2) else none) := by
  simp only [chooseLedger, chooseFrom, designation crypto wire serverKeyId budget ledger consistent,
    List.getElem?_map]
  cases index with
  | none => rfl
  | some index => exact Option.bind_map

/-- Equality of native public observations and fresh-handle metadata suffices; no message equality is assumed. -/
theorem choose_public (crypto : Pqxdh.Crypto) (wire : RegistrationNativeWire.Wire)
    (serverKeyId : U64) (budget : Budget) (index : Option Nat)
    (first second : RegistrationNativeLedger.State)
    (transcript : first.transcript.map view = second.transcript.map view)
    (handles : first.ledger.fresh.map PqxdhDeploymentSecrecy.FreshEntry.handle =
      second.ledger.fresh.map PqxdhDeploymentSecrecy.FreshEntry.handle) :
    chooseLedger crypto wire serverKeyId budget index first = chooseLedger crypto wire serverKeyId budget index second := by
  simp only [chooseLedger, transcript, handles]

/-- A source selection event reads the claim's index, never its guessed bytes. -/
noncomputable def selected (crypto : Pqxdh.Crypto) (wire : RegistrationNativeWire.Wire)
    (serverKeyId : U64) (budget : Budget) (claim : Value → Option (Nat × Pqxdh.Bytes))
    (target : Target budget) (value : Value) (ledger : RegistrationNativeLedger.State) : Bool :=
  decide (chooseLedger crypto wire serverKeyId budget ((claim value).map Prod.fst) ledger = some target)

/-- Distinct target events are disjoint in the same real execution. -/
theorem selected_unique (crypto : Pqxdh.Crypto) (wire : RegistrationNativeWire.Wire)
    (serverKeyId : U64) (budget : Budget) (claim : Value → Option (Nat × Pqxdh.Bytes))
    (first second : Target budget) (value : Value) (ledger : RegistrationNativeLedger.State)
    (chosenFirst : selected crypto wire serverKeyId budget claim first value ledger = true)
    (chosenSecond : selected crypto wire serverKeyId budget claim second value ledger = true) : first = second := by
  exact Option.some.inj ((of_decide_eq_true chosenFirst).symm.trans (of_decide_eq_true chosenSecond))

/-- The ideal selector ignores environment, produced frames, counters, slot map, test bit and private messages. -/
noncomputable def analysisSelector {n : Nat} {E : Type}
    (crypto : Pqxdh.Crypto) (wire : RegistrationNativeWire.Wire) (serverKeyId : U64) (budget : Budget)
    (claim : Value → Option (Nat × Pqxdh.Bytes)) (target : Target budget)
    (projection : PqxdhRecordLiftIdeal.PublicHiding n E Value) : Bool :=
  match projection.1 with
  | none => false
  | some observed => decide (chooseFrom crypto wire serverKeyId budget ((claim observed.1).map Prod.fst)
      (restoreFrom [] observed.2.1).2 (observed.2.2.2.1.map Prod.fst) = some target)

theorem restored_fresh (ledger : PqxdhDeploymentSecrecy.Ledger) :
    (RegistrationNativeEntropyRestore.ledger ledger).ledger.fresh = ledger.fresh := rfl

/-- The same selector is an explicit finite function of the record observer's public projection. -/
theorem analysis_exact {n : Nat} {E : Type}
    (crypto : Pqxdh.Crypto) (wire : RegistrationNativeWire.Wire) (serverKeyId : U64) (budget : Budget)
    (claim : Value → Option (Nat × Pqxdh.Bytes)) (target : Target budget) (value : Value)
    (ledger : PqxdhDeploymentSecrecy.Ledger) (environment : E)
    (produced : List (PqxdhDeploymentInterface.FrameTag × PqxdhDeploymentNative.Frame))
    (raw : PqxdhRecordLiftWorld.RawCounters)
    (slots : Handle → Option (PqxdhRecordLiftInterface.Slot n)) :
    analysisSelector crypto wire serverKeyId budget claim target
      (PqxdhRecordLiftIdeal.publicHiding ⟨some (value, ledger, environment), produced, raw, slots⟩) =
      selected crypto wire serverKeyId budget claim target value (RegistrationNativeEntropyRestore.ledger ledger) := by
  simp only [analysisSelector, PqxdhRecordLiftIdeal.publicHiding, Option.map_some, selected]
  apply decide_eq_decide.mpr
  simp only [chooseLedger, restored_fresh, List.map_map, Function.comp_def]
  rw [RegistrationNativePublicObservation.ledger_public ledger]

end BeaconcryptCore.Computational.RegistrationNativeCanonicalSelector

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeCanonicalSelector.reify_view' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeCanonicalSelector.reify_view

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeCanonicalSelector.erased_view' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeCanonicalSelector.erased_view

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeCanonicalSelector.erased_transcript' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeCanonicalSelector.erased_transcript

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeCanonicalSelector.designation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeCanonicalSelector.designation

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeCanonicalSelector.choose_literal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeCanonicalSelector.choose_literal

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeCanonicalSelector.choose_public' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeCanonicalSelector.choose_public

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeCanonicalSelector.selected_unique' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeCanonicalSelector.selected_unique

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeCanonicalSelector.restored_fresh' does not depend on any axioms -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeCanonicalSelector.restored_fresh

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeCanonicalSelector.analysis_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeCanonicalSelector.analysis_exact
