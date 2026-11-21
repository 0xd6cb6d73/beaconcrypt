-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeLorEvents
import BeaconcryptCore.Computational.RegistrationNativeCanonicalReceipt
import BeaconcryptCore.Computational.RegistrationNativeCanonicalSelector
import BeaconcryptCore.Computational.RegistrationNativePrekeySplit

/-! The first admitted test chooses a functional parsed-accept by owner target from public native observations. Broad original LR eligibility is retained literally, and a shared first-accept receipt supplies the canonical source attempt for every admitted test handle. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeLorCanonical
open PqxdhDeploymentInterface (Budget FreshBounds Mode Handle)
open RegistrationNativeLedgerHiding (PublicEntry view)
open RegistrationNativePublicObservation (firstAccept)
open RegistrationNativeCanonicalSelector (reify)
open RegistrationNativeLorEvents (EligibleAt)
variable {Value NativeState : Type}

noncomputable def chooseFrom (crypto : Pqxdh.Crypto) (wire : RegistrationNativeWire.Wire)
    (serverKeyId : U64) (budget : Budget) (transcript : List PublicEntry) : Option (Fin budget.accept × Fin budget.capacity) := do
  let original := transcript.map fun entry => (reify entry).erase
  let handle ← PqxdhRecordLiftIdeal.firstTest original
  let target ← PqxdhDeploymentTranscript.designateIn crypto (RegistrationNativeWire.ledgerCodec wire) serverKeyId budget original handle
  let first ← firstAccept wire target.1.val transcript
  if bound : first.1 < budget.accept then some (⟨first.1, bound⟩, target.2) else none

noncomputable def choose (crypto : Pqxdh.Crypto) (wire : RegistrationNativeWire.Wire)
    (serverKeyId : U64) (budget : Budget) (ledger : RegistrationNativeLedger.State) : Option (Fin budget.accept × Fin budget.capacity) :=
  chooseFrom crypto wire serverKeyId budget (ledger.transcript.map view)

/-- The native public scan computes the literal first admitted test and original public designation. -/
theorem choose_literal (crypto : Pqxdh.Crypto) (wire : RegistrationNativeWire.Wire)
    (serverKeyId : U64) (budget : Budget) (ledger : RegistrationNativeLedger.State)
    (consistent : RegistrationNativeLedger.Consistent ledger) :
    choose crypto wire serverKeyId budget ledger = (do
      let handle ← PqxdhRecordLiftIdeal.firstTest ledger.ledger.transcript
      let target ← PqxdhDeploymentTranscript.designateIn crypto (RegistrationNativeWire.ledgerCodec wire) serverKeyId budget ledger.ledger.transcript handle
      let first ← firstAccept wire target.1.val (ledger.transcript.map view)
      if bound : first.1 < budget.accept then some (⟨first.1, bound⟩, target.2) else none) := by
  have first := PqxdhDeploymentHeadlineLor.firstTest_view _ _ (RegistrationNativeCanonicalSelector.erased_transcript ledger.transcript)
  rw [← consistent] at first
  simp only [choose, chooseFrom, first,
    RegistrationNativeCanonicalSelector.designation crypto wire serverKeyId budget ledger consistent]

def CanonicalEligibleAt (crypto : Pqxdh.Crypto) (wire : RegistrationNativeWire.Wire) (serverKeyId : U64)
    (budget : Budget) (filter : RegistrationNativeLorEvents.Filter Value) (target : Fin budget.accept × Fin budget.capacity)
    (result : Value × RegistrationNativeLedger.State) : Prop :=
  ∃ session : Fin budget.accept, ∃ raw, EligibleAt crypto wire serverKeyId budget filter (session, target.2) result ∧
    firstAccept wire session.val (result.2.transcript.map view) = some (target.1.val, raw)

/-- The functional first-test scan names every canonical eligible target. -/
theorem eligible_choose (crypto : Pqxdh.Crypto) (wire : RegistrationNativeWire.Wire) (serverKeyId : U64)
    (budget : Budget) (filter : RegistrationNativeLorEvents.Filter Value) (target : Fin budget.accept × Fin budget.capacity)
    (result : Value × RegistrationNativeLedger.State) (consistent : RegistrationNativeLedger.Consistent result.2)
    (eligible : CanonicalEligibleAt crypto wire serverKeyId budget filter target result) :
    choose crypto wire serverKeyId budget result.2 = some target := by
  obtain ⟨session, raw, eligible, scanned⟩ := eligible
  obtain ⟨first, tested, designated⟩ := eligible.2.1
  rw [choose_literal crypto wire serverKeyId budget result.2 consistent]
  simp only [tested, Option.bind_eq_bind, Option.bind_some, designated, scanned, dite_eq_left target.1.isLt]

/-- Broad original eligibility is covered by the same parsed-accept by owner product on actual bounded native runs. -/
theorem broad_selected (crypto : Pqxdh.Crypto) (wire : RegistrationNativeWire.Wire) (serverKeyId : U64) (bounds : FreshBounds)
    (typed : QueryImpl RegistrationNativeRawAdapter.TypedSpec (StateT NativeState ProbComp)) (mode : Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value) (budget : Budget) (bounded : RegistrationNativeInterface.Respects budget work)
    (before : NativeState) (filter : RegistrationNativeLorEvents.Filter Value) (result : Value × (RegistrationNativeLedger.State × NativeState))
    (supported : result ∈ support (RegistrationNativeFullCompiler.run crypto wire serverKeyId bounds typed mode work before))
    (eligible : RegistrationNativeLorEvents.j crypto wire serverKeyId budget filter (result.1, result.2.1) = true) :
    ∃ target : Fin budget.accept × Fin budget.capacity, CanonicalEligibleAt crypto wire serverKeyId budget filter target (result.1, result.2.1) := by
  classical
  obtain ⟨original, originalEligible⟩ := of_decide_eq_true eligible
  obtain ⟨first, tested, designated⟩ := originalEligible.2.1
  have consistent := RegistrationNativeFullCompiler.ledger_projection crypto wire serverKeyId bounds typed mode work before result supported
  rw [consistent] at designated
  have cap := RegistrationNativeParsedTargetCaps.run_accepts crypto wire serverKeyId bounds typed mode work budget bounded before result supported
  obtain ⟨parsed, raw, scanned, _receipt⟩ := RegistrationNativeCanonicalReceipt.designated_scan_bounded crypto wire serverKeyId budget
    result.2.1.transcript first original designated cap
  exact ⟨(parsed, original.2), original.1, raw, originalEligible, scanned⟩

/-- The canonical receipt is derived from broad designation and the literal first scanner hit. -/
theorem accepted (crypto : Pqxdh.Crypto) (wire : RegistrationNativeWire.Wire) (serverKeyId : U64)
    (budget : Budget) (filter : RegistrationNativeLorEvents.Filter Value) (target : Fin budget.accept × Fin budget.capacity)
    (result : Value × RegistrationNativeLedger.State) (consistent : RegistrationNativeLedger.Consistent result.2)
    (eligible : CanonicalEligibleAt crypto wire serverKeyId budget filter target result) :
    ∃ session : Fin budget.accept, EligibleAt crypto wire serverKeyId budget filter (session, target.2) result ∧
      RegistrationNativeParsedTargetCanonical.AcceptedAt wire result.2.transcript session.val target.1.val := by
  obtain ⟨session, raw, eligible, scanned⟩ := eligible
  obtain ⟨first, tested, designated⟩ := eligible.2.1
  rw [consistent] at designated
  obtain ⟨parsed, returned, found, receipt⟩ := RegistrationNativeCanonicalReceipt.designated_scan crypto wire serverKeyId budget
    result.2.transcript first (session, target.2) designated
  have pair := Option.some.inj (found.symm.trans scanned)
  have sameParsed : parsed = target.1.val := congrArg Prod.fst pair
  rw [sameParsed] at receipt
  exact ⟨session, eligible, receipt⟩

/-- Canonical eligibility shares are disjoint because the first-test selector is functional. -/
theorem unique (crypto : Pqxdh.Crypto) (wire : RegistrationNativeWire.Wire) (serverKeyId : U64)
    (budget : Budget) (filter : RegistrationNativeLorEvents.Filter Value) (result : Value × RegistrationNativeLedger.State)
    (consistent : RegistrationNativeLedger.Consistent result.2) (first second : Fin budget.accept × Fin budget.capacity)
    (left : CanonicalEligibleAt crypto wire serverKeyId budget filter first result)
    (right : CanonicalEligibleAt crypto wire serverKeyId budget filter second result) : first = second := by
  exact Option.some.inj ((eligible_choose crypto wire serverKeyId budget filter first result consistent left).symm.trans
    (eligible_choose crypto wire serverKeyId budget filter second result consistent right))


/-- A property is required only for the handles of actually admitted test commands, including failed sends. -/
def OnTests (crypto : Pqxdh.Crypto) (wire : RegistrationNativeWire.Wire) (serverKeyId : U64)
    (transcript : List PqxdhDeploymentInterface.Entry) (property : Handle → Prop) : Prop :=
  ∀ before entry after handle left right, transcript = before ++ entry :: after →
    entry.query = .inr (.test handle left right) →
    PqxdhRecordLiftIdeal.AdmittedTest crypto (RegistrationNativeWire.ledgerCodec wire) serverKeyId before handle left right → property handle

def GoodAt (crypto : Pqxdh.Crypto) (wire : RegistrationNativeWire.Wire) (serverKeyId : U64)
    (budget : Budget) (filter : RegistrationNativeLorEvents.Filter Value) (target : Fin budget.accept × Fin budget.capacity)
    (result : Value × RegistrationNativeLedger.State) : Prop :=
  CanonicalEligibleAt crypto wire serverKeyId budget filter target result ∧
    OnTests crypto wire serverKeyId result.2.ledger.transcript
      (RegistrationNativePrekeyEvents.Pinned crypto (RegistrationNativeWire.ledgerCodec wire) serverKeyId result.2.ledger.transcript)

/-- The two original observer families retain the same literal hidden test bit. -/
noncomputable def j (crypto : Pqxdh.Crypto) (wire : RegistrationNativeWire.Wire) (serverKeyId : U64)
    (budget : Budget) (filter : RegistrationNativeLorEvents.Filter Value) (target : Fin budget.accept × Fin budget.capacity)
    (result : Value × RegistrationNativeLedger.State) : Bool :=
  @decide (GoodAt crypto wire serverKeyId budget filter target result) (Classical.propDecidable _)

noncomputable def w (crypto : Pqxdh.Crypto) (wire : RegistrationNativeWire.Wire) (serverKeyId : U64)
    (budget : Budget) (filter : RegistrationNativeLorEvents.Filter Value) (guess : Value → Bool)
    (target : Fin budget.accept × Fin budget.capacity) (result : Value × RegistrationNativeLedger.State) : Bool :=
  j crypto wire serverKeyId budget filter target result &&
    decide (result.2.ledger.test.map PqxdhDeploymentSecrecy.TestState.bit = some (guess result.1))

/-- One real changed-prekey origin event covers every failing public pin equality at once. -/
theorem real_pin_tests {n : Nat} {ι KemSK : Type} {base : OracleSpec ι} {source : RegistrationNativeMldsa.Source}
    (setup : PqxdhServerAuthExperiment.Setup base KemSK) (checks : PqxdhServerAuthExperiment.Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (credential : RegistrationNativeMldsa.Credential source)
    (readback : RegistrationNativeWire.InitReadBack wire)
    (shortRejects : ∀ (publicKey : PqxdhEd25519EufCma.Ed25519PublicKey) bytes, bytes.length < 64 → setup.source.crypto.verify publicKey.toList bytes = none)
    (bounds : FreshBounds) (mode : Mode) (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (before : RegistrationNativeExperiment.State n KemSK source)
    (result : RegistrationNativeEvents.Observed Value (RegistrationNativeExperiment.State n KemSK source))
    (supported : result ∈ support (RegistrationNativeExperiment.run setup checks wire route representation created source credential bounds mode work before)) :
    RegistrationNativeIdentityOriginEvents.Changed setup.joint wire result.2.1.transcript result.2.2.beacons ∨
      OnTests setup.source.crypto wire created.server.server.metadata.sender result.2.1.ledger.transcript
        (RegistrationNativePrekeyEvents.Pinned setup.source.crypto (RegistrationNativeWire.ledgerCodec wire)
          created.server.server.metadata.sender result.2.1.ledger.transcript) := by
  classical
  by_cases changed : RegistrationNativeIdentityOriginEvents.Changed setup.joint wire result.2.1.transcript result.2.2.beacons
  · exact Or.inl changed
  · right
    intro pre entry post handle left right split query admitted
    exact (RegistrationNativePrekeySplit.pinned_or_changed setup checks wire route representation created credential readback shortRejects
      bounds mode work before result supported handle).resolve_right changed

/-- Broad real LR eligibility splits once into the original origin event or the canonical public good-target shares. -/
theorem real_eligible_split {n : Nat} {ι KemSK : Type} {base : OracleSpec ι} {source : RegistrationNativeMldsa.Source}
    (setup : PqxdhServerAuthExperiment.Setup base KemSK) (checks : PqxdhServerAuthExperiment.Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (credential : RegistrationNativeMldsa.Credential source)
    (readback : RegistrationNativeWire.InitReadBack wire)
    (shortRejects : ∀ (publicKey : PqxdhEd25519EufCma.Ed25519PublicKey) bytes, bytes.length < 64 → setup.source.crypto.verify publicKey.toList bytes = none)
    (bounds : FreshBounds) (mode : Mode) (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (budget : Budget) (bounded : RegistrationNativeInterface.Respects budget work) (filter : RegistrationNativeLorEvents.Filter Value)
    (before : RegistrationNativeExperiment.State n KemSK source)
    (result : RegistrationNativeEvents.Observed Value (RegistrationNativeExperiment.State n KemSK source))
    (supported : result ∈ support (RegistrationNativeExperiment.run setup checks wire route representation created source credential bounds mode work before))
    (eligible : RegistrationNativeLorEvents.j setup.source.crypto wire created.server.server.metadata.sender budget filter (result.1, result.2.1) = true) :
    RegistrationNativeIdentityOriginEvents.Changed setup.joint wire result.2.1.transcript result.2.2.beacons ∨
      ∃ target : Fin budget.accept × Fin budget.capacity, GoodAt setup.source.crypto wire created.server.server.metadata.sender budget filter target (result.1, result.2.1) := by
  rcases real_pin_tests setup checks wire route representation created credential readback shortRejects bounds mode work before result supported with changed | pinned
  · exact Or.inl changed
  · obtain ⟨target, canonical⟩ := broad_selected setup.source.crypto wire created.server.server.metadata.sender bounds
      (RegistrationNativeExperiment.handler setup checks wire route representation created source credential) mode work budget bounded before filter result supported eligible
    exact Or.inr ⟨target, canonical, pinned⟩


/-- The retained public prekey equality ignores raw receive plaintext replies. -/
theorem pinned_view (crypto : Pqxdh.Crypto) (wire : RegistrationNativeWire.Wire) (serverKeyId : U64)
    (first second : List PqxdhDeploymentInterface.Entry) (same : PqxdhDeploymentTranscript.SameView first second)
    (handle : Handle) :
    RegistrationNativePrekeyEvents.Pinned crypto (RegistrationNativeWire.ledgerCodec wire) serverKeyId first handle ↔
      RegistrationNativePrekeyEvents.Pinned crypto (RegistrationNativeWire.ledgerCodec wire) serverKeyId second handle := by
  have accepts : PqxdhDeploymentTranscript.acceptOf first = PqxdhDeploymentTranscript.acceptOf second := funext fun _ =>
    PqxdhDeploymentTranscript.findSome_view _ (PqxdhDeploymentTranscript.view_respects _ (fun _ _ _ => rfl) (fun _ _ _ _ => rfl)) first second same
  have bundles : PqxdhDeploymentTranscript.bundleOf first = PqxdhDeploymentTranscript.bundleOf second := funext fun _ =>
    PqxdhDeploymentTranscript.findSome_view _ (PqxdhDeploymentTranscript.view_respects _ (fun _ _ _ => rfl) (fun _ _ _ _ => rfl)) first second same
  have designation := (PqxdhDeploymentTranscript.designate_view crypto (RegistrationNativeWire.ledgerCodec wire) serverKeyId first second same).1
  cases handle with
  | owner _ => rfl
  | peer _ => simp only [RegistrationNativePrekeyEvents.Pinned, RegistrationNativePrekeyEvents.acceptedAt,
      RegistrationNativePrekeyEvents.publishedAt, accepts, bundles, designation]

/-- Good canonical LR eligibility depends on public native observations and the terminal adversary output alone. -/
theorem good_view (crypto : Pqxdh.Crypto) (wire : RegistrationNativeWire.Wire) (serverKeyId : U64)
    (budget : Budget) (filter : RegistrationNativeLorEvents.Filter Value) (target : Fin budget.accept × Fin budget.capacity)
    (value : Value) (first second : RegistrationNativeLedger.State)
    (original : PqxdhDeploymentTranscript.SameView first.ledger.transcript second.ledger.transcript)
    (native : first.transcript.map view = second.transcript.map view)
    (good : GoodAt crypto wire serverKeyId budget filter target (value, first)) :
    GoodAt crypto wire serverKeyId budget filter target (value, second) := by
  obtain ⟨⟨session, raw, eligible, scanned⟩, pinned⟩ := good
  refine ⟨⟨session, raw, RegistrationNativeLorEvents.eligible_view crypto wire serverKeyId budget filter (session, target.2) value
    first second original native eligible, ?_⟩, ?_⟩
  · simpa only [native] using scanned
  · exact PqxdhDeploymentHeadlineLor.admitted_view crypto (RegistrationNativeWire.ledgerCodec wire) serverKeyId
      (RegistrationNativePrekeyEvents.Pinned crypto (RegistrationNativeWire.ledgerCodec wire) serverKeyId second.ledger.transcript)
      first.ledger.transcript second.ledger.transcript original
      (fun pre entry post handle left right split query admitted =>
        (pinned_view crypto wire serverKeyId _ _ original handle).mp (pinned pre entry post handle left right split query admitted))

theorem j_view (crypto : Pqxdh.Crypto) (wire : RegistrationNativeWire.Wire) (serverKeyId : U64)
    (budget : Budget) (filter : RegistrationNativeLorEvents.Filter Value) (target : Fin budget.accept × Fin budget.capacity)
    (value : Value) (first second : RegistrationNativeLedger.State)
    (original : PqxdhDeploymentTranscript.SameView first.ledger.transcript second.ledger.transcript)
    (native : first.transcript.map view = second.transcript.map view) :
    j crypto wire serverKeyId budget filter target (value, first) = j crypto wire serverKeyId budget filter target (value, second) := by
  exact decide_eq_decide.mpr ⟨good_view crypto wire serverKeyId budget filter target value first second original native,
    good_view crypto wire serverKeyId budget filter target value second first original.symm native.symm⟩

/-- The winning observer keeps the literal original bit under native ledger hiding. -/
theorem w_related (crypto : Pqxdh.Crypto) (wire : RegistrationNativeWire.Wire) (serverKeyId : U64)
    (budget : Budget) (filter : RegistrationNativeLorEvents.Filter Value) (guess : Value → Bool) (target : Fin budget.accept × Fin budget.capacity)
    (value : Value) (first second : RegistrationNativeLedger.State) (related : RegistrationNativeLedgerHiding.StateRel first second) :
    w crypto wire serverKeyId budget filter guess target (value, first) = w crypto wire serverKeyId budget filter guess target (value, second) := by
  rw [w, w, j_view crypto wire serverKeyId budget filter target value first second related.1.1 related.2, related.1.2.1]

end BeaconcryptCore.Computational.RegistrationNativeLorCanonical

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeLorCanonical.choose_literal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeLorCanonical.choose_literal

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeLorCanonical.eligible_choose' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeLorCanonical.eligible_choose

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeLorCanonical.broad_selected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeLorCanonical.broad_selected

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeLorCanonical.accepted' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeLorCanonical.accepted

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeLorCanonical.unique' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeLorCanonical.unique

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeLorCanonical.real_pin_tests' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeLorCanonical.real_pin_tests

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeLorCanonical.real_eligible_split' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeLorCanonical.real_eligible_split

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeLorCanonical.pinned_view' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeLorCanonical.pinned_view

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeLorCanonical.good_view' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeLorCanonical.good_view

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeLorCanonical.j_view' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeLorCanonical.j_view

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeLorCanonical.w_related' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeLorCanonical.w_related
