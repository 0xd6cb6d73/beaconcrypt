-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRegistrationJointAcceptCutEuf
import BeaconcryptCore.Computational.PqxdhRegistrationJointNativeKemOrigin

/-! Classify the selected raw accept of the actual source14 program at the cut, and bound the authentication failure there. The target is designated by public handles only: the raw-accept ordinal of the scan and a public KEM creation index. A candidate counts as protected when its attached source verification succeeds under the public identity key of some generated owner in the public owner registry whose public KEM index is the designated one and which is unrevealed at the cut. Protected candidates either carry an issued tuple of that owner, whose PQ key is the owner's native KEM key at the cut, or produce the address-free final-report failure, which the ordinary joint-use weak-EUF family bounds with coefficient one. There is no honest-target premise; attacker-owned, imported, revealed and other candidates are classified, not bounded. -/
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhRegistrationJointAcceptOrigin
open PqxdhJointIdentity PqxdhDynamicIdentityReports PqxdhEd25519EufCma PqxdhServerAuthExperiment
open PqxdhDynamicIdentityRouting
open PqxdhRegistrationJointRevealSchedule (Spec)
open PqxdhRegistrationJointAcceptCut (Cut scan selected)
open PqxdhRegistrationJointAcceptCutReports (mapChoice)
open PqxdhRegistrationJointInitializedReports (ReportResult sourceResult)
open PqxdhRegistrationJointRawSignatures (verified)
open PqxdhRegistrationJointNativeOriginBound (reduction)
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK A Reader Response X : Type}

section CutProtection

/-! Cut-time protection. This section fixes the freshness reading used by this module: the identity freshness of the owner is read in the report state reached immediately before the selected raw accept is issued, and nothing after the cut is inspected. A whole-run reading or a public cut-time observable would be separate predicates with their own theorems; the statements below would not change. -/

/-- Cut-time protection with explicit witnesses. The reached outcome is a pending raw cut whose attached source verification succeeds; `address` locates a generated owner in the public owner registry with public KEM index `kemIndex`; the verified identity equals that owner's public identity key; and the owner's identity is unrevealed at the cut. Only public values are compared. The source key lookup is an analysis projection, as in `NativeKemOrigin.key_or_failure`, and is never evaluated by a reduction. -/
def ProtectedAt (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks) {count : Nat}
    (kemIndex : Fin count) (reached : ReportResult KemSK A (Cut KemSK X) count)
    (encoded : PqxdhRegistrationJointInitializedSchedule.Outcome KemSK (Cut KemSK X))
    (raw : Pqxdh.Bytes) (next : Option Nat → OracleComp (Spec KemSK) X)
    (value : PqxdhServerRootPreparation.Verified Reader) (address : Nat)
    (owner : PqxdhRegistrationJointGeneratedFinish.EncodedEntry) (target : Fin count) (publicKey : PublicIdentity) :
    Prop :=
  (sourceResult reached).1 = some encoded ∧ encoded.2.1 = .pending raw next ∧
    verified setup codec checks raw = some value ∧
    encoded.2.2.owners[address]? = some owner ∧ owner.2.1 = kemIndex.val ∧
    reached.1.2.refs[owner.1]? = some (.generated target.val) ∧
    sourceKeys setup.joint (sourceResult reached).2.1.1.seeds owner.1 = some publicKey ∧
    value.identity = publicKey.ed25519 ∧
    PqxdhRegistrationJointRoutedReveals.revealedAt owner.1 (sourceResult reached).2.1.1.transcript = false

/-- Some public owner address witnesses cut-time protection for KEM index `kemIndex`. -/
def Protected (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks) {count : Nat}
    (kemIndex : Fin count) (reached : ReportResult KemSK A (Cut KemSK X) count) : Prop :=
  ∃ encoded raw next value address owner target publicKey,
    ProtectedAt setup codec checks kemIndex reached encoded raw next value address owner target publicKey

end CutProtection

/-- Protection by a witness whose verified tuple occurs in that owner's chronological signing history: an honest unchanged or honestly re-issued tuple. -/
def HonestTuple (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks) {count : Nat}
    (kemIndex : Fin count) (reached : ReportResult KemSK A (Cut KemSK X) count) : Prop :=
  ∃ encoded raw next value address owner target publicKey,
    ProtectedAt setup codec checks kemIndex reached encoded raw next value address owner target publicKey ∧
    PqxdhRegistrationJointAttemptDecoding.Occurred value.keys
      (PqxdhRegistrationJointSigningTranscript.messagesAt owner.1 (sourceResult reached).2.1.1.transcript)

/-- At the cut, the verified PQ key of the pending candidate is the public key at KEM creation index `kemIndex` of the native KEM pool. -/
def KeyMatchCut (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks) {count : Nat}
    (kemIndex : Fin count) (reached : ReportResult KemSK A (Cut KemSK X) count) : Prop :=
  ∃ encoded raw next value, (sourceResult reached).1 = some encoded ∧ encoded.2.1 = .pending raw next ∧
    verified setup codec checks raw = some value ∧
    ((sourceResult reached).2.1.2.keys[kemIndex.val]?).map Prod.fst = some value.keys.pqKey

/-- The Server constructor failed, or the program completed before its selected raw accept. -/
def CutComplete {count : Nat} (reached : ReportResult KemSK A (Cut KemSK X) count) : Prop :=
  (sourceResult reached).1 = none ∨
    ∃ encoded result, (sourceResult reached).1 = some encoded ∧ encoded.2.1 = .complete result

/-- The selected raw accept is pending and its attached source verification rejects. -/
def VerifyRejected (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks) {count : Nat}
    (reached : ReportResult KemSK A (Cut KemSK X) count) : Prop :=
  ∃ encoded raw next, (sourceResult reached).1 = some encoded ∧ encoded.2.1 = .pending raw next ∧
    verified setup codec checks raw = none

/-- The selected raw accept is pending and its attached source verification succeeds. -/
def VerifiedSome (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks) {count : Nat}
    (reached : ReportResult KemSK A (Cut KemSK X) count) : Prop :=
  ∃ encoded raw next value, (sourceResult reached).1 = some encoded ∧ encoded.2.1 = .pending raw next ∧
    verified setup codec checks raw = some value

/-- Attached-to-detached step: a successful attached source verification of the raw bytes reads the original candidate fields and is accepted by the detached `acceptPhase1Candidate setup.joint.verify` interface with the verified identity and tuple. The step uses the inherited attached-format contract `shortRejects` and `setup.wiring` only. -/
theorem attached_detached (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (shortRejects : ∀ (publicKey : Ed25519PublicKey) bytes, bytes.length < 64 →
      setup.source.crypto.verify publicKey.toList bytes = none)
    (raw : Pqxdh.Bytes) (value : PqxdhServerRootPreparation.Verified Reader)
    (attached : verified setup codec checks raw = some value) :
    PqxdhRegistrationJointRawSignatures.candidate codec raw = some value.candidate ∧
      acceptPhase1Candidate setup.joint.verify value.candidate = some (value.identity, value.keys) :=
  ⟨(PqxdhRegistrationJointRawSignatures.verified_origin setup codec checks raw value attached).1,
    PqxdhRegistrationJointRawSignatures.verified_detached setup codec checks shortRejects raw value attached⟩

/-- A protected cut either carries a tuple issued by the witness owner, whose PQ key is then the native KEM key at the designated index, or is the original-field report failure of that owner's generated position in the reached snapshot. The owner is located at the witness address, not at an address returned by the program. -/
theorem protected_origin (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (shortRejects : ∀ (publicKey : Ed25519PublicKey) bytes, bytes.length < 64 →
      setup.source.crypto.verify publicKey.toList bytes = none)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes) (count : Nat)
    (work : OracleComp (Spec KemSK) X) (index : Nat) (runtime : A)
    (reached : ReportResult KemSK A (Cut KemSK X) count)
    (supported : reached ∈ support (PqxdhJointPhase1Reports.run setup.joint count
      (PqxdhRegistrationJointReportCompiler.initialized setup codec checks ensureInit supplied count
        (scan work index) runtime)))
    (kemIndex : Fin count) (encoded : PqxdhRegistrationJointInitializedSchedule.Outcome KemSK (Cut KemSK X))
    (raw : Pqxdh.Bytes) (next : Option Nat → OracleComp (Spec KemSK) X)
    (value : PqxdhServerRootPreparation.Verified Reader) (address : Nat)
    (owner : PqxdhRegistrationJointGeneratedFinish.EncodedEntry) (target : Fin count) (publicKey : PublicIdentity)
    (protectedAt : ProtectedAt setup codec checks kemIndex reached encoded raw next value address owner target publicKey) :
    (PqxdhRegistrationJointAttemptDecoding.Occurred value.keys
        (PqxdhRegistrationJointSigningTranscript.messagesAt owner.1 (sourceResult reached).2.1.1.transcript) ∧
      KeyMatchCut setup codec checks kemIndex reached) ∨
    PqxdhJointPhase1Reports.FieldOriginFailure setup.joint ⟨target.val, value.candidate⟩ reached.2.1.snapshot := by
  obtain ⟨finished, pending, attached, found, slot, generated, key, identity, fresh⟩ := protectedAt
  have accepted := (attached_detached setup codec checks shortRejects raw value attached).2
  rw [identity] at accepted
  obtain ⟨receipt, fixed, exactHistory, nativeKey, origin⟩ :=
    PqxdhRegistrationJointAttemptReports.owner_origin setup codec checks ensureInit supplied count (scan work index)
      runtime reached supported encoded finished address owner found target generated publicKey value.candidate
      value.keys key accepted fresh
  rcases origin with issued | forged
  · refine Or.inl ⟨?_, encoded, raw, next, value, finished, pending, attached, ?_⟩
    · rw [exactHistory]
      exact (PqxdhRegistrationJointAttemptDecoding.occurred_iff value.keys receipt.attempts).mpr issued
    · rw [← slot]
      exact nativeKey.trans (congrArg some (fixed value.keys issued).2.symm)
  · exact Or.inr forged

/-- The final choice of the mapped selected outcome parses to the verified candidate of the pending raw bytes. -/
theorem chosen_mapped (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (chosenOwner : Nat) (fallback : Pqxdh.Bytes) {count : Nat} (reached : ReportResult KemSK A (Cut KemSK X) count)
    (encoded : PqxdhRegistrationJointInitializedSchedule.Outcome KemSK (Cut KemSK X))
    (raw : Pqxdh.Bytes) (next : Option Nat → OracleComp (Spec KemSK) X)
    (value : PqxdhServerRootPreparation.Verified Reader)
    (finished : (sourceResult reached).1 = some encoded) (pending : encoded.2.1 = .pending raw next)
    (attached : verified setup codec checks raw = some value) :
    PqxdhRegistrationJointFinalCandidate.selected codec (mapChoice chosenOwner fallback reached).1 =
      some value.candidate := by
  rw [PqxdhRegistrationJointNativeKemOrigin.selected_source codec (mapChoice chosenOwner fallback reached)
    (encoded.1, (chosenOwner, raw), encoded.2.2)
    (PqxdhRegistrationJointAcceptCutReports.raw_eq chosenOwner fallback reached encoded raw next finished pending)]
  exact (PqxdhRegistrationJointRawSignatures.verified_origin setup codec checks raw value attached).1

/-- A protected cut whose verified PQ key is not the native KEM key at the designated index is an address-free final-report failure of the mapped selected outcome. -/
theorem protected_report_failure (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (shortRejects : ∀ (publicKey : Ed25519PublicKey) bytes, bytes.length < 64 →
      setup.source.crypto.verify publicKey.toList bytes = none)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes) (count : Nat)
    (work : OracleComp (Spec KemSK) X) (index : Nat) (runtime : A)
    (reached : ReportResult KemSK A (Cut KemSK X) count)
    (supported : reached ∈ support (PqxdhJointPhase1Reports.run setup.joint count
      (PqxdhRegistrationJointReportCompiler.initialized setup codec checks ensureInit supplied count
        (scan work index) runtime)))
    (kemIndex : Fin count) (chosenOwner : Nat) (fallback : Pqxdh.Bytes)
    (protects : Protected setup codec checks kemIndex reached)
    (mismatch : ¬KeyMatchCut setup codec checks kemIndex reached) :
    PqxdhRegistrationJointFinalReportEvent.Failure setup.joint codec (mapChoice chosenOwner fallback reached) := by
  obtain ⟨encoded, raw, next, value, address, owner, target, publicKey, protectedAt⟩ := protects
  rcases protected_origin setup codec checks shortRejects ensureInit supplied count work index runtime reached supported
      kemIndex encoded raw next value address owner target publicKey protectedAt with ⟨_, matched⟩ | forged
  · exact absurd matched mismatch
  · obtain ⟨finished, pending, attached, _⟩ := protectedAt
    exact ⟨target.val, value.candidate,
      chosen_mapped setup codec checks chosenOwner fallback reached encoded raw next value finished pending attached,
      forged⟩

/-- Every reached cut satisfies at least one of five cases. The cases are not exclusive: for example two generated owners with equal identity public keys can make one cut honest through one owner and a report failure through the other. Attacker-owned, imported, revealed, missing and other-index candidates, or a generated owner outside the report range (impossible under capacity), fall in the third case and are only classified. -/
theorem classify (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (shortRejects : ∀ (publicKey : Ed25519PublicKey) bytes, bytes.length < 64 →
      setup.source.crypto.verify publicKey.toList bytes = none)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes) (count : Nat)
    (work : OracleComp (Spec KemSK) X) (index : Nat) (runtime : A)
    (reached : ReportResult KemSK A (Cut KemSK X) count)
    (supported : reached ∈ support (PqxdhJointPhase1Reports.run setup.joint count
      (PqxdhRegistrationJointReportCompiler.initialized setup codec checks ensureInit supplied count
        (scan work index) runtime)))
    (kemIndex : Fin count) (chosenOwner : Nat) (fallback : Pqxdh.Bytes) :
    CutComplete reached ∨
      VerifyRejected setup codec checks reached ∨
      (VerifiedSome setup codec checks reached ∧ ¬Protected setup codec checks kemIndex reached) ∨
      (Protected setup codec checks kemIndex reached ∧ HonestTuple setup codec checks kemIndex reached ∧
        KeyMatchCut setup codec checks kemIndex reached) ∨
      (Protected setup codec checks kemIndex reached ∧
        PqxdhRegistrationJointFinalReportEvent.Failure setup.joint codec (mapChoice chosenOwner fallback reached)) := by
  by_cases protects : Protected setup codec checks kemIndex reached
  · obtain ⟨encoded, raw, next, value, address, owner, target, publicKey, protectedAt⟩ := id protects
    rcases protected_origin setup codec checks shortRejects ensureInit supplied count work index runtime reached supported
        kemIndex encoded raw next value address owner target publicKey protectedAt with ⟨occurred, matched⟩ | forged
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨protects,
        ⟨encoded, raw, next, value, address, owner, target, publicKey, protectedAt, occurred⟩, matched⟩)))
    · obtain ⟨finished, pending, attached, _⟩ := protectedAt
      exact Or.inr (Or.inr (Or.inr (Or.inr ⟨protects, target.val, value.candidate,
        chosen_mapped setup codec checks chosenOwner fallback reached encoded raw next value finished pending attached,
        forged⟩)))
  · cases finished : (sourceResult reached).1 with
    | none => exact Or.inl (Or.inl finished)
    | some encoded =>
      cases cut : encoded.2.1 with
      | complete result => exact Or.inl (Or.inr ⟨encoded, result, finished, cut⟩)
      | pending raw next =>
        cases checked : verified setup codec checks raw with
        | none => exact Or.inr (Or.inl ⟨encoded, raw, next, finished, cut, checked⟩)
        | some value =>
          exact Or.inr (Or.inr (Or.inl ⟨⟨encoded, raw, next, value, finished, cut, checked⟩, protects⟩))

/-- Authentication bound at the cut: the probability, in the report run of the raw-accept scan at `count + 1` positions, that the selected candidate is protected for KEM index `kemIndex` but its verified PQ key is not the native KEM key at that index, is at most the ordinary joint-use weak-EUF family of the selected prefix program, with coefficient one. -/
theorem protected_bound (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (shortRejects : ∀ (publicKey : Ed25519PublicKey) bytes, bytes.length < 64 →
      setup.source.crypto.verify publicKey.toList bytes = none)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes) (count : Nat)
    (work : OracleComp (Spec KemSK) X) (runtime : A) (index : Nat)
    (budget : PqxdhRegistrationJointRevealCosts.SourceKind → Nat)
    (certified : ∀ source, work.IsQueryBoundP
      (fun query => PqxdhRegistrationJointRevealCosts.sourceKind (KemSK := KemSK) query = source) (budget source))
    (capacity : (if supplied.isNone then 1 else 0) + budget (.inl 1) ≤ count + 1)
    (kemIndex : Fin (count + 1)) (chosenOwner : Nat) (fallback : Pqxdh.Bytes)
    (dynamicFallback : DynamicForgery) (ordinaryFallback : Forgery) :
    letI := Classical.propDecidable
    𝒟[(fun reached => decide (Protected setup codec checks kemIndex reached ∧
        ¬KeyMatchCut setup codec checks kemIndex reached)) <$>
      PqxdhJointPhase1Reports.run setup.joint (count + 1)
        (PqxdhRegistrationJointReportCompiler.initialized setup codec checks ensureInit supplied (count + 1)
          (scan work index) runtime)] {true} ≤
      ∑ target : Fin (count + 1), advantage setup.joint
        (reduction setup codec checks ensureInit supplied count (selected work index chosenOwner fallback) runtime
          dynamicFallback ordinaryFallback target) := by
  classical
  refine le_trans ?_ (PqxdhRegistrationJointAcceptCutEuf.selected_report_bound setup codec checks ensureInit supplied
    count work runtime index chosenOwner fallback budget certified capacity dynamicFallback ordinaryFallback)
  rw [PqxdhRegistrationJointAcceptCutReports.selected_run, ← prEvent_eq_evalDist_singleton _ true,
    prEvent_map, ← prEvent_eq_evalDist_singleton _ true, prEvent_map, prEvent_map]
  apply prEvent_mono_of_support
  intro reached supported event
  simp only [decide_eq_true_eq] at event ⊢
  exact protected_report_failure setup codec checks shortRejects ensureInit supplied (count + 1) work index runtime
    reached supported kemIndex chosenOwner fallback event.1 event.2

end BeaconcryptCore.Computational.PqxdhRegistrationJointAcceptOrigin

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointAcceptOrigin.attached_detached' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointAcceptOrigin.attached_detached

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointAcceptOrigin.protected_origin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointAcceptOrigin.protected_origin

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointAcceptOrigin.chosen_mapped' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointAcceptOrigin.chosen_mapped

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointAcceptOrigin.protected_report_failure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointAcceptOrigin.protected_report_failure

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointAcceptOrigin.classify' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointAcceptOrigin.classify

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointAcceptOrigin.protected_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointAcceptOrigin.protected_bound
