-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePublicObservation

/-! The functional first-accept scanner yields an actual canonical source receipt. It counts every preceding decodable attempt, including failures, and selects the same first successful session input as acceptOf. No session-uniqueness or successful-decoding conclusion is assumed for arbitrary histories. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeCanonicalReceipt
open RegistrationNativePublicObservation (NativePublic acceptPublic parsedPublic firstFrom firstAccept)
open RegistrationNativeLedgerHiding (view)
open RegistrationNativeEvents (parsedAccept parsedAcceptCount)
open RegistrationNativeInterface (Entry)

theorem parsed_view (wire : RegistrationNativeWire.Wire) (entry : Entry) :
    parsedPublic wire (view entry) = parsedAccept wire entry := by
  rcases entry with ⟨(coin | command) | secrecy, reply⟩
  · rfl
  · cases command <;> rfl
  · rfl

theorem parsed_cons (wire : RegistrationNativeWire.Wire) (entry : Entry) (transcript : List Entry) :
    parsedAcceptCount wire (entry :: transcript) =
      parsedAcceptCount wire transcript + if parsedAccept wire entry then 1 else 0 := by
  cases selected : parsedAccept wire entry <;> simp [parsedAcceptCount, selected]

theorem accept_some (session : Nat) (entry : Entry) (raw : Pqxdh.Bytes)
    (found : acceptPublic session (view entry) = some raw) :
    entry = ⟨.inl (.inr (.accept raw)), some session⟩ := by
  rcases entry with ⟨(coin | command) | secrecy, reply⟩
  · cases found
  · cases command <;> try cases found
    cases reply with
    | none => cases found
    | some handle =>
        simp only [acceptPublic, view, RegistrationNativeInterface.project, RegistrationNativeInterface.eraseCommand,
          PqxdhDeploymentInterface.project] at found
        split at found
        all_goals simp_all only [Option.some.injEq, reduceCtorEq]
        subst_vars
        rfl
  · cases found

theorem first_split (wire : RegistrationNativeWire.Wire) (session cursor parsed : Nat)
    (transcript : List Entry) (raw : Pqxdh.Bytes)
    (found : firstFrom wire session cursor (transcript.map view) = some (parsed, raw)) :
    ∃ before after, transcript = before ++ (Entry.mk (.inl (.inr (.accept raw))) (some session)) :: after ∧
      cursor + parsedAcceptCount wire before = parsed := by
  induction transcript generalizing cursor with
  | nil => simp [firstFrom] at found
  | cons entry rest ih =>
      cases accepted : acceptPublic session (view entry) with
      | none =>
          simp only [List.map_cons, firstFrom, accepted] at found
          obtain ⟨before, after, split, counted⟩ := ih _ found
          refine ⟨entry :: before, after, ?_, ?_⟩
          · exact congrArg (List.cons entry) split
          · simpa only [parsed_cons, ← parsed_view, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using counted
      | some incoming =>
          simp only [List.map_cons, firstFrom, accepted, Option.some.injEq, Prod.mk.injEq] at found
          rcases found with ⟨rfl, rfl⟩
          exact ⟨[], rest, congrArg (fun first => first :: rest) (accept_some session entry incoming accepted), Nat.add_zero cursor⟩

/-- A decodable first scanner hit is the actual canonical accepted entry with its exact parsed-call ordinal. -/
theorem first_receipt (wire : RegistrationNativeWire.Wire) (session parsed : Nat)
    (transcript : List Entry) (raw : Pqxdh.Bytes)
    (found : firstAccept wire session (transcript.map view) = some (parsed, raw))
    (decodable : (RegistrationNativeWire.readInit wire raw).isSome) :
    RegistrationNativeParsedTargetCanonical.AcceptedAt wire transcript session parsed := by
  obtain ⟨before, after, split, counted⟩ := first_split wire session 0 parsed transcript raw found
  obtain ⟨packet, decoded⟩ := Option.isSome_iff_exists.mp decodable
  exact ⟨before, raw, packet, after, split, by simpa only [Nat.zero_add] using counted, decoded,
    (RegistrationNativePublicObservation.first_acceptOf wire session transcript).symm.trans
      (congrArg (Option.map Prod.snd) found)⟩

/-- Broad public designation supplies a decodable first scanner hit and its actual canonical receipt, including changed valid packets. -/
theorem designated_scan (crypto : Pqxdh.Crypto) (wire : RegistrationNativeWire.Wire) (serverKeyId : U64)
    (budget : PqxdhDeploymentInterface.Budget) (transcript : List Entry) (handle : PqxdhDeploymentInterface.Handle)
    (target : Fin budget.accept × Fin budget.capacity)
    (designated : PqxdhDeploymentTranscript.designateIn crypto (RegistrationNativeWire.ledgerCodec wire)
      serverKeyId budget (transcript.map Entry.erase) handle = some target) :
    ∃ parsed raw, firstAccept wire target.1.val (transcript.map view) = some (parsed, raw) ∧
      RegistrationNativeParsedTargetCanonical.AcceptedAt wire transcript target.1.val parsed := by
  obtain ⟨_ordinal, _before, raw, packet, _after, _split, _counted, decoded, canonical⟩ :=
    RegistrationNativeParsedTargetCanonical.designated_first crypto wire serverKeyId budget transcript handle target designated
  have payload : (firstAccept wire target.1.val (transcript.map view)).map Prod.snd = some raw :=
    (RegistrationNativePublicObservation.first_acceptOf wire target.1.val transcript).trans canonical
  obtain ⟨⟨parsed, returned⟩, found, same⟩ := Option.map_eq_some_iff.mp payload
  cases same
  exact ⟨parsed, returned, found, first_receipt wire target.1.val parsed transcript returned found
    (Option.isSome_iff_exists.mpr ⟨packet, decoded⟩)⟩

/-- The original raw accept allowance also bounds the canonical parsed ordinal, with no extra session-position sum. -/
theorem designated_scan_bounded (crypto : Pqxdh.Crypto) (wire : RegistrationNativeWire.Wire) (serverKeyId : U64)
    (budget : PqxdhDeploymentInterface.Budget) (transcript : List Entry) (handle : PqxdhDeploymentInterface.Handle)
    (target : Fin budget.accept × Fin budget.capacity)
    (designated : PqxdhDeploymentTranscript.designateIn crypto (RegistrationNativeWire.ledgerCodec wire)
      serverKeyId budget (transcript.map Entry.erase) handle = some target)
    (cap : RegistrationNativeParsedTargetCaps.classCount 3 transcript ≤ budget.accept) :
    ∃ parsed : Fin budget.accept, ∃ raw, firstAccept wire target.1.val (transcript.map view) = some (parsed.val, raw) ∧
      RegistrationNativeParsedTargetCanonical.AcceptedAt wire transcript target.1.val parsed.val := by
  obtain ⟨parsed, raw, found, receipt⟩ := designated_scan crypto wire serverKeyId budget transcript handle target designated
  have room := Nat.lt_of_lt_of_le (RegistrationNativeParsedTargetCaps.accepted_lt wire transcript target.1.val parsed
    (RegistrationNativeParsedTargetCanonical.accepted_original wire transcript target.1.val parsed receipt)) cap
  exact ⟨⟨parsed, room⟩, raw, found, receipt⟩

theorem run_designated_scan {Value NativeState : Type}
    (crypto : Pqxdh.Crypto) (wire : RegistrationNativeWire.Wire) (serverKeyId : U64)
    (bounds : PqxdhDeploymentInterface.FreshBounds)
    (typed : QueryImpl RegistrationNativeRawAdapter.TypedSpec (StateT NativeState ProbComp))
    (mode : PqxdhDeploymentInterface.Mode) (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (budget : PqxdhDeploymentInterface.Budget) (bounded : RegistrationNativeInterface.Respects budget work)
    (before : NativeState) (observed : RegistrationNativeEvents.Observed Value NativeState)
    (supported : observed ∈ support (RegistrationNativeFullCompiler.run crypto wire serverKeyId bounds typed mode work before))
    (handle : PqxdhDeploymentInterface.Handle) (target : Fin budget.accept × Fin budget.capacity)
    (designated : PqxdhDeploymentTranscript.designateIn crypto (RegistrationNativeWire.ledgerCodec wire)
      serverKeyId budget observed.2.1.ledger.transcript handle = some target) :
    ∃ parsed : Fin budget.accept, ∃ raw,
      firstAccept wire target.1.val (observed.2.1.transcript.map view) = some (parsed.val, raw) ∧
      RegistrationNativeParsedTargetCanonical.AcceptedAt wire observed.2.1.transcript target.1.val parsed.val := by
  have consistent := RegistrationNativeFullCompiler.ledger_projection crypto wire serverKeyId bounds typed mode work before observed supported
  rw [consistent] at designated
  exact designated_scan_bounded crypto wire serverKeyId budget observed.2.1.transcript handle target designated
    (RegistrationNativeParsedTargetCaps.run_accepts crypto wire serverKeyId bounds typed mode work budget bounded before observed supported)

/-- Every original broad APP win has a bounded functional canonical target, without requiring unchanged honest bytes. -/
theorem broad_selected {Value NativeState : Type}
    (crypto : Pqxdh.Crypto) (wire : RegistrationNativeWire.Wire) (serverKeyId : U64)
    (bounds : PqxdhDeploymentInterface.FreshBounds)
    (typed : QueryImpl RegistrationNativeRawAdapter.TypedSpec (StateT NativeState ProbComp))
    (mode : PqxdhDeploymentInterface.Mode) (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (budget : PqxdhDeploymentInterface.Budget) (bounded : RegistrationNativeInterface.Respects budget work)
    (before : NativeState) (claim : Value → Option (Nat × Pqxdh.Bytes))
    (observed : RegistrationNativeEvents.Observed Value NativeState)
    (supported : observed ∈ support (RegistrationNativeFullCompiler.run crypto wire serverKeyId bounds typed mode work before))
    (winning : RegistrationNativeEvents.CEAppWin crypto wire serverKeyId budget claim observed) :
    ∃ target : Fin budget.accept × Fin budget.capacity, ∃ raw,
      RegistrationNativeParsedTargetCanonical.CEAppAt crypto wire serverKeyId budget target claim observed ∧
      ∃ index guess entry session,
        claim observed.1 = some (index, guess) ∧ observed.2.1.ledger.fresh[index]? = some entry ∧
        PqxdhDeploymentTranscript.designateIn crypto (RegistrationNativeWire.ledgerCodec wire)
          serverKeyId budget observed.2.1.ledger.transcript entry.handle = some (session, target.2) ∧
        firstAccept wire session.val (observed.2.1.transcript.map view) = some (target.1.val, raw) := by
  rcases winning with ⟨index, guess, entry, claimed, fresh, eligible, guessed⟩
  obtain ⟨original, designated⟩ := Option.isSome_iff_exists.mp eligible
  obtain ⟨parsed, raw, found, receipt⟩ := run_designated_scan crypto wire serverKeyId bounds typed mode work budget bounded
    before observed supported entry.handle original designated
  exact ⟨(parsed, original.2), raw,
    ⟨index, guess, entry, original.1, claimed, fresh, designated, receipt, guessed⟩,
    index, guess, entry, original.1, claimed, fresh, designated, found⟩

end BeaconcryptCore.Computational.RegistrationNativeCanonicalReceipt

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeCanonicalReceipt.parsed_view' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeCanonicalReceipt.parsed_view
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeCanonicalReceipt.parsed_cons' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeCanonicalReceipt.parsed_cons
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeCanonicalReceipt.accept_some' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeCanonicalReceipt.accept_some
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeCanonicalReceipt.first_split' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeCanonicalReceipt.first_split
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeCanonicalReceipt.first_receipt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeCanonicalReceipt.first_receipt
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeCanonicalReceipt.designated_scan' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeCanonicalReceipt.designated_scan
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeCanonicalReceipt.designated_scan_bounded' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeCanonicalReceipt.designated_scan_bounded
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeCanonicalReceipt.run_designated_scan' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeCanonicalReceipt.run_designated_scan
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeCanonicalReceipt.broad_selected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeCanonicalReceipt.broad_selected
