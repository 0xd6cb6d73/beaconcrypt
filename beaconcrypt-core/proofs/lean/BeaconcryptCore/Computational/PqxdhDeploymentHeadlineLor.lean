-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhDeploymentHeadlineAnomaly
import BeaconcryptCore.Computational.PqxdhDeploymentHeadlineContain
import BeaconcryptCore.Computational.PqxdhRecordLiftLor

/-!
# CE-LOR: left-or-right secrecy of the single test session (CE-12 P1, design-v2 section 4.5)

The headline CE-LOR in observation mode P (VC rows SSX-b2s, SSX-s2b, SS-b2s, SS-s2b and the record challenges 167, design-v2 section 12), for every public filter `F` on the mode-P transcript view (`F = fun _ => true` gives the plain CE-LOR; the symbolic corollary of unit P2 uses `NoBundleFailure`):

- Eligibility (`PqxdhDeploymentHeadlineEvents.LorElig`): a test session exists, `F` holds, and every admitted test entry's handle designates the target of the first admitted test entry (`PqxdhRecordLiftIdeal.firstTest`, the claim). The win (`LorWin`) adds that the adversary's guess equals the test bit.
- `ce_lor`: the advantage `|Pr_CE[win] - ½ Pr_CE[eligible]|` is at most the sum over the targets `g` in `Fin qAccept × Fin qCreate`, each with coefficient one, of `kemLoss + slotLoss + recLoss_g(dec_g(W) ∧ IS_g)` of the win, half of the same terms of the eligibility, and `½ β_g`; two transfers per target, one per event. `ce_lor_target` is the per-target form.
- `ce_lor_server` and `ce_lor_server_target`: the same for Server-side tests (`PeerTests`), with `ServerSlots` and no `β_g`.

Proof per target (design-v2 section 4.5): both events go two-sidedly along C1-C5 (`PqxdhDeploymentHeadlineChain.chain_close`); on the record lift's view of the all-real chain world the slot differences are combined before splitting, `|(Pr[W] - ½Pr[E]) - (Pr[W ∧ IS] - ½Pr[E ∧ IS])| = |Pr[W ∧ ¬IS] - ½Pr[E ∧ ¬IS]| ≤ ½Pr[E ∧ ¬IS] ≤ ½β_g` (`chance_split`, `view_unslotted`, `anomaly_beta`, `lor_arith`, `lor_bound`); both slotted events go two-sidedly through the record lift (`records_close`); and in `idealRecords` the slotted win has exactly half the probability of the slotted eligibility (`lor_final`): `dec_g(E) ∧ IS_g` depends on a view only through the public hiding projection (`decided_view`, from the mode-P invariance of designation, admission, `firstTest`, `peerOf` and `IdealSlots`: `idealSlots_view`, `lorElig_view`, `lorClaim_view`), implies `TestsHidden` (`PqxdhDeploymentHeadlineContain.lor_hidden`), and the win is the eligibility with the test bit equal to the projected guess (`win_slotted`), so `PqxdhRecordLiftLor.idealRecords_lor` applies with the public eligibility `hidingOf` and the projected guess `decisionHiding`.

Premises: `FunctionalDecapsulation setup.kem`, `Phase1ReadBack`, `Phase2ReadBack`, `SourceFullCorrect setup.source setup.hmac`, `KemBound setup caps`, the total query bound `qInit` of the runtime initializer, and `budget.Respects adversary`; the AEAD forgery fallback is a parameter of the integrity loss. No new assumption or contract.
-/

open OracleComp OracleSpec ENNReal

set_option autoImplicit false

namespace BeaconcryptCore.Computational.PqxdhDeploymentHeadlineLor
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhDeploymentInterface (Handle Entry FreshBounds Mode ModeSpec Budget)
open PqxdhDeploymentKemTransfer (Observed happens designated)
open PqxdhDeploymentIdealParams (Target)
open PqxdhDeploymentIdealTrace (IdealSlots peerOf)
open PqxdhDeploymentTranscript (SameView designateIn)
open PqxdhDeploymentIdealHandoff (decisionOn viewObserved)
open PqxdhRecordLiftIdeal (View PublicHiding publicHiding firstTest AdmittedTest testBit)
open PqxdhRecordLiftInterface (Slot)
open PqxdhDeploymentHeadlineChain (ServerSlots slotted serverSlotted)
open PqxdhDeploymentHeadlineEvents

/-! ### The mode-P view of the transcript -/

section View
variable {Reader Response : Type}

/-- A filter-map of transcript entries by a function that ignores raw-receive replies depends only on the mode P view. -/
theorem filterMap_view {β : Type} (f : Entry → Option β) (respects : ∀ first second : Entry,
    first.view .P = second.view .P → f first = f second) :
    ∀ first second : List Entry, SameView first second → first.filterMap f = second.filterMap f
  | [], [], _ => rfl
  | [], _ :: _, same => by simp [SameView] at same
  | _ :: _, [], same => by simp [SameView] at same
  | entry :: rest, other :: rest', same => by
      simp only [SameView, List.map_cons, List.cons.injEq] at same
      simp only [List.filterMap_cons, respects entry other same.1, filterMap_view f respects rest rest' same.2]

/-- Same view is symmetric. -/
theorem sameView_symm {first second : List Entry} (same : SameView first second) : SameView second first :=
  same.symm

/-- The Server peer of a target's session depends only on the mode P view. -/
theorem peerOf_view {count : ℕ} (t : Target count) (first second : List Entry) (same : SameView first second) :
    peerOf t first = peerOf t second := by
  have replies : PqxdhDeploymentIdealTrace.acceptReplies first = PqxdhDeploymentIdealTrace.acceptReplies second :=
    filterMap_view _ (PqxdhDeploymentTranscript.view_respects _ (fun _ _ _ => rfl) (fun _ _ _ _ => rfl)) first second
      same
  have builds : PqxdhDeploymentTranscript.buildOf first = PqxdhDeploymentTranscript.buildOf second := funext fun _ =>
    PqxdhDeploymentTranscript.findSome_view _
      (PqxdhDeploymentTranscript.view_respects _ (fun _ _ _ => rfl) (fun _ _ _ _ => rfl)) first second same
  simp only [peerOf, PqxdhDeploymentIdealTrace.sessionAt, replies, builds]

/-- `IdealSlots` of a slot map depends on the transcript only through its mode P view. -/
theorem idealSlots_view (crypto : Pqxdh.Crypto) (codec : Codec Reader Response) (serverKid : Aeneas.Std.U64)
    {count : ℕ} (t : Target count) (slots : Handle → Option (Slot 2)) (first second : List Entry)
    (same : SameView first second) :
    IdealSlots crypto codec serverKid t slots first ↔ IdealSlots crypto codec serverKid t slots second := by
  have designated := (PqxdhDeploymentTranscript.designate_view crypto codec serverKid first second same).1
  simp only [IdealSlots, PqxdhDeploymentIdealTrace.BeaconLinked, designated, peerOf_view t first second same]

/-- `ServerSlots` of a slot map depends on the transcript only through its mode P view. -/
theorem serverSlots_view (crypto : Pqxdh.Crypto) (codec : Codec Reader Response) (serverKid : Aeneas.Std.U64)
    {count : ℕ} (t : Target count) (slots : Handle → Option (Slot 2)) (first second : List Entry)
    (same : SameView first second) :
    ServerSlots crypto codec serverKid t slots first ↔ ServerSlots crypto codec serverKid t slots second := by
  have designated := (PqxdhDeploymentTranscript.designate_view crypto codec serverKid first second same).1
  simp only [ServerSlots, designated, peerOf_view t first second same]

/-- The first admitted test of a transcript depends only on its mode P view. -/
theorem firstTest_view (first second : List Entry) (same : SameView first second) :
    firstTest first = firstTest second :=
  PqxdhDeploymentTranscript.findSome_view PqxdhRecordLiftIdeal.admissibleTest
    (PqxdhDeploymentTranscript.view_respects PqxdhRecordLiftIdeal.admissibleTest (fun _ _ _ => rfl)
      (fun _ _ _ _ => rfl)) first second same

/-- A split of a transcript at an entry corresponds to a split of every transcript with the same mode P view, at an entry with the same query and with prefixes of the same mode P view. -/
theorem split_view (first second : List Entry) (same : SameView first second) (before' : List Entry) (entry' : Entry)
    (after' : List Entry) (split : second = before' ++ entry' :: after') :
    ∃ before entry after, first = before ++ entry :: after ∧ SameView before before' ∧ entry.query = entry'.query := by
  unfold SameView at same
  rw [split, List.map_append, List.map_cons, List.map_eq_append_iff] at same
  obtain ⟨before, rest, rfl, beforeSame, restSame⟩ := same
  obtain ⟨entry, after, rfl, entrySame, _⟩ := List.map_eq_cons_iff.mp restSame
  exact ⟨before, entry, after, rfl, beforeSame, congrArg PqxdhDeploymentInterface.PublicEntry.query entrySame⟩

/-- The admitted-test condition of CE-LOR transfers between transcripts with the same mode P view. -/
theorem admitted_view (crypto : Pqxdh.Crypto) (codec : Codec Reader Response) (serverKid : Aeneas.Std.U64)
    (P : Handle → Prop) (first second : List Entry) (same : SameView first second)
    (holds : ∀ before entry after handle left right, first = before ++ entry :: after →
      entry.query = .inr (.test handle left right) → AdmittedTest crypto codec serverKid before handle left right →
        P handle) :
    ∀ before entry after handle left right, second = before ++ entry :: after →
      entry.query = .inr (.test handle left right) → AdmittedTest crypto codec serverKid before handle left right →
        P handle := by
  intro before' entry' after' handle left right split query admitted
  obtain ⟨before, entry, after, firstSplit, beforeSame, querySame⟩ :=
    split_view first second same before' entry' after' split
  exact holds before entry after handle left right firstSplit (querySame.trans query)
    ((PqxdhRecordLiftIdeal.admittedTest_view crypto codec serverKid before before' beforeSame handle left right).2
      admitted)

end View

/-! ### Invariance of the eligibility under the public hiding projection -/

section Invariance
variable {Reader Response X : Type} (crypto : Pqxdh.Crypto) (codec : Codec Reader Response)
  (serverKid : Aeneas.Std.U64) (budget : Budget) (filter : List (PqxdhDeploymentInterface.PublicEntry .P) → Bool)

/-- CE-LOR eligibility for a target transfers between observations whose transcripts have the same mode P view and whose ledgers agree on whether a test session exists. -/
theorem lorElig_view (g : Fin budget.accept × Fin budget.capacity) (observed observed' : Observed X)
    (same : SameView observed.2.1.transcript observed'.2.1.transcript)
    (tested : observed.2.1.test.isSome = observed'.2.1.test.isSome)
    (eligible : LorElig crypto codec serverKid budget filter g observed) :
    LorElig crypto codec serverKid budget filter g observed' := by
  obtain ⟨test, filtered, ⟨first, firstFound, firstDesignated⟩, admitted⟩ := eligible
  have designated := (PqxdhDeploymentTranscript.designate_view crypto codec serverKid _ _ same).2 budget
  refine ⟨tested ▸ test, ?_, ⟨first, ?_, ?_⟩, ?_⟩
  · unfold SameView at same
    rw [← same]
    exact filtered
  · rw [← firstTest_view _ _ same]
    exact firstFound
  · rw [← designated]
    exact firstDesignated
  · exact admitted_view crypto codec serverKid
      (fun handle => designateIn crypto codec serverKid budget observed'.2.1.transcript handle = some g) _ _ same
      (fun before entry after handle left right split query admittedTest => by
        rw [← designated]
        exact admitted before entry after handle left right split query admittedTest)

/-- `PeerTests` transfers between observations whose transcripts have the same mode P view. -/
theorem peerTests_view (observed observed' : Observed X)
    (same : SameView observed.2.1.transcript observed'.2.1.transcript)
    (peers : PeerTests crypto codec serverKid observed) : PeerTests crypto codec serverKid observed' :=
  admitted_view crypto codec serverKid (fun handle => ∃ keyId, handle = .peer keyId) _ _ same peers

open Classical in
/-- The CE-LOR eligibility event depends on an observation only through its transcript's mode P view and whether a test session exists. -/
theorem lorEligEvent_view (observed observed' : Observed X)
    (same : SameView observed.2.1.transcript observed'.2.1.transcript)
    (tested : observed.2.1.test.isSome = observed'.2.1.test.isSome) :
    lorEligEvent crypto codec serverKid budget filter observed =
      lorEligEvent crypto codec serverKid budget filter observed' := by
  unfold lorEligEvent
  rw [Bool.eq_iff_iff, decide_eq_true_iff, decide_eq_true_iff]
  exact ⟨fun ⟨g, eligible⟩ => ⟨g, lorElig_view crypto codec serverKid budget filter g _ _ same tested eligible⟩,
    fun ⟨g, eligible⟩ => ⟨g, lorElig_view crypto codec serverKid budget filter g _ _ (sameView_symm same)
      tested.symm eligible⟩⟩

open Classical in
/-- The Server-side CE-LOR eligibility event depends on an observation only through its transcript's mode P view and whether a test session exists. -/
theorem lorEligPeerEvent_view (observed observed' : Observed X)
    (same : SameView observed.2.1.transcript observed'.2.1.transcript)
    (tested : observed.2.1.test.isSome = observed'.2.1.test.isSome) :
    lorEligPeerEvent crypto codec serverKid budget filter observed =
      lorEligPeerEvent crypto codec serverKid budget filter observed' := by
  unfold lorEligPeerEvent
  rw [Bool.eq_iff_iff, decide_eq_true_iff, decide_eq_true_iff]
  exact ⟨fun ⟨⟨g, eligible⟩, peers⟩ => ⟨⟨g, lorElig_view crypto codec serverKid budget filter g _ _ same tested
      eligible⟩, peerTests_view crypto codec serverKid _ _ same peers⟩,
    fun ⟨⟨g, eligible⟩, peers⟩ => ⟨⟨g, lorElig_view crypto codec serverKid budget filter g _ _ (sameView_symm same)
      tested.symm eligible⟩, peerTests_view crypto codec serverKid _ _ (sameView_symm same) peers⟩⟩

/-- The CE-LOR claim's designation depends on an observation only through its transcript's mode P view. -/
theorem lorClaim_view (observed observed' : Observed X)
    (same : SameView observed.2.1.transcript observed'.2.1.transcript) :
    PqxdhDeploymentKemTransfer.target crypto codec serverKid budget lorClaim observed =
      PqxdhDeploymentKemTransfer.target crypto codec serverKid budget lorClaim observed' := by
  unfold PqxdhDeploymentKemTransfer.target lorClaim
  rw [firstTest_view _ _ same, (PqxdhDeploymentTranscript.designate_view crypto codec serverKid _ _ same).2 budget]

end Invariance

section Decided
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response E X : Type}
  (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (budget : Budget)

open Classical in
/-- A per-target decision conjoined with a slot predicate is invariant under the public hiding projection when the event reads only the transcript's mode P view and the test's presence, the claim's designation reads only the mode P view, and the slot predicate reads the transcript only through its mode P view. -/
theorem decided_view (event : Observed X → Bool) (claim : Observed X → Option Handle)
    (g : Fin budget.accept × Fin budget.capacity)
    (slotted : List Entry → (Handle → Option (Slot 2)) → Prop)
    (eventView : ∀ observed observed' : Observed X, SameView observed.2.1.transcript observed'.2.1.transcript →
      observed.2.1.test.isSome = observed'.2.1.test.isSome → event observed = event observed')
    (claimView : ∀ observed observed' : Observed X, SameView observed.2.1.transcript observed'.2.1.transcript →
      PqxdhDeploymentKemTransfer.target setup.source.crypto codec setup.serverKeyId budget claim observed =
        PqxdhDeploymentKemTransfer.target setup.source.crypto codec setup.serverKeyId budget claim observed')
    (slotsView : ∀ first second slots, SameView first second → (slotted first slots ↔ slotted second slots))
    (view view' : View 2 E X) (same : publicHiding view = publicHiding view') :
    decide ((viewObserved view).any (decisionOn setup codec budget event claim g) = true ∧
        ∀ value, view.result = some value → slotted value.2.1.transcript view.slots) =
      decide ((viewObserved view').any (decisionOn setup codec budget event claim g) = true ∧
        ∀ value, view'.result = some value → slotted value.2.1.transcript view'.slots) := by
  rcases view with ⟨_ | value, produced, raw, slots⟩ <;> rcases view' with ⟨_ | value', produced', raw', slots'⟩
  · simp [viewObserved]
  · simp [publicHiding] at same
  · simp [publicHiding] at same
  · simp only [publicHiding, Option.map_some, Prod.mk.injEq, Option.some.injEq] at same
    obtain ⟨⟨_, transcriptSame, testSame, _, _⟩, _, _, rfl⟩ := same
    have tested : value.2.1.test.isSome = value'.2.1.test.isSome := by
      rw [← Option.isSome_map (f := fun test => (test.first, test.count)), testSame, Option.isSome_map]
    have eventSame := eventView (value.1, value.2.1, produced) (value'.1, value'.2.1, produced') transcriptSame tested
    have claimSame := claimView (value.1, value.2.1, produced) (value'.1, value'.2.1, produced') transcriptSame
    have slotsSame := slotsView value.2.1.transcript value'.2.1.transcript slots transcriptSame
    simp only [viewObserved, Option.map_some, Option.any_some, decisionOn, eventSame, Option.some.injEq,
      forall_eq', slotsSame]
    rw [claimSame]

end Decided

/-! ### The final world: factoring through the public hiding projection -/

section Hiding
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response E X : Type}

/-- The public eligibility of a view predicate that factors through the public hiding projection: some view with that projection satisfies it. -/
noncomputable def hidingOf {n : ℕ} (predicate : View n E X → Bool) (projection : PublicHiding n E X) : Bool :=
  @decide (∃ view, publicHiding view = projection ∧ predicate view = true) (Classical.propDecidable _)

/-- A view predicate that is invariant under the public hiding projection is its public eligibility read off the projection. -/
theorem hidingOf_eq {n : ℕ} (predicate : View n E X → Bool)
    (invariant : ∀ view view', publicHiding view = publicHiding view' → predicate view = predicate view')
    (view : View n E X) : hidingOf predicate (publicHiding view) = predicate view := by
  unfold hidingOf
  rw [Bool.eq_iff_iff]
  simp only [decide_eq_true_eq]
  exact ⟨fun ⟨other, same, holds⟩ => by rw [← invariant other view same]; exact holds,
    fun holds => ⟨view, rfl, holds⟩⟩

/-- The adversary's guess read off the public hiding projection: the guess of its output, false when no Server was constructed. -/
def decisionHiding {n : ℕ} (guess : X → Bool) (projection : PublicHiding n E X) : Bool :=
  match projection.1 with
  | some value => guess value.1
  | none => false

variable (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)

/-- `lorEligible` of the public eligibility of an invariant view predicate that implies `TestsHidden` is the predicate. -/
theorem eligible_hiding {n : ℕ} (predicate : View n E X → Bool)
    (invariant : ∀ view view', publicHiding view = publicHiding view' → predicate view = predicate view')
    (hidden : ∀ view, predicate view = true →
      PqxdhRecordLiftIdeal.TestsHidden setup.source.crypto codec setup.serverKeyId view)
    (view : View n E X) :
    PqxdhRecordLiftIdeal.lorEligible setup.source.crypto codec setup.serverKeyId (hidingOf predicate) view =
      predicate view := by
  classical
  unfold PqxdhRecordLiftIdeal.lorEligible
  rw [hidingOf_eq predicate invariant view, Bool.eq_iff_iff, decide_eq_true_iff]
  exact ⟨And.left, fun holds => ⟨holds, hidden view holds⟩⟩

/-- `lorGuess` of the projected guess and the public eligibility of an invariant view predicate that implies `TestsHidden` is the predicate together with the test bit equal to the guess. -/
theorem guess_hiding {n : ℕ} (guess : X → Bool) (predicate : View n E X → Bool)
    (invariant : ∀ view view', publicHiding view = publicHiding view' → predicate view = predicate view')
    (hidden : ∀ view, predicate view = true →
      PqxdhRecordLiftIdeal.TestsHidden setup.source.crypto codec setup.serverKeyId view)
    (view : View n E X) :
    PqxdhRecordLiftIdeal.lorGuess setup.source.crypto codec setup.serverKeyId (decisionHiding guess)
        (hidingOf predicate) view =
      (predicate view && decide (testBit view = some (decisionHiding guess (publicHiding view)))) := by
  classical
  unfold PqxdhRecordLiftIdeal.lorGuess
  rw [hidingOf_eq predicate invariant view, Bool.eq_iff_iff, decide_eq_true_iff, Bool.and_eq_true,
    decide_eq_true_iff]
  exact ⟨fun ⟨holds, _, bit⟩ => ⟨holds, bit⟩, fun ⟨holds, bit⟩ => ⟨holds, hidden view holds, bit⟩⟩

end Hiding

section Win
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response E X : Type}
  (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (budget : Budget) (guess : X → Bool)
  (filter : List (PqxdhDeploymentInterface.PublicEntry .P) → Bool)

open Classical in
/-- The CE-LOR win event is the eligibility event with the test bit equal to the adversary's guess. -/
theorem lorWin_iff (observed : Observed X) :
    lorWinEvent setup.source.crypto codec setup.serverKeyId budget guess filter observed = true ↔
      lorEligEvent setup.source.crypto codec setup.serverKeyId budget filter observed = true ∧
        observed.2.1.test.map PqxdhDeploymentSecrecy.TestState.bit = some (guess observed.1) := by
  unfold lorWinEvent lorEligEvent
  simp only [decide_eq_true_eq]
  exact ⟨fun ⟨g, eligible, bit⟩ => ⟨⟨g, eligible⟩, bit⟩, fun ⟨⟨g, eligible⟩, bit⟩ => ⟨g, eligible, bit⟩⟩

open Classical in
/-- The Server-side CE-LOR win event is the Server-side eligibility event with the test bit equal to the adversary's guess. -/
theorem lorWinPeer_iff (observed : Observed X) :
    lorWinPeerEvent setup.source.crypto codec setup.serverKeyId budget guess filter observed = true ↔
      lorEligPeerEvent setup.source.crypto codec setup.serverKeyId budget filter observed = true ∧
        observed.2.1.test.map PqxdhDeploymentSecrecy.TestState.bit = some (guess observed.1) := by
  unfold lorWinPeerEvent lorEligPeerEvent
  simp only [decide_eq_true_eq]
  exact ⟨fun ⟨⟨g, eligible, bit⟩, peers⟩ => ⟨⟨⟨g, eligible⟩, peers⟩, bit⟩,
    fun ⟨⟨⟨g, eligible⟩, peers⟩, bit⟩ => ⟨⟨g, eligible, bit⟩, peers⟩⟩

open Classical in
/-- The CE-LOR win with its slots is the eligibility with its slots and the test bit equal to the projected guess. -/
theorem win_slotted (g : Fin budget.accept × Fin budget.capacity) (view : View 2 E X) :
    slotted setup codec budget (lorWinEvent setup.source.crypto codec setup.serverKeyId budget guess filter) lorClaim
        g view =
      (slotted setup codec budget (lorEligEvent setup.source.crypto codec setup.serverKeyId budget filter) lorClaim g
          view &&
        decide (testBit view = some (decisionHiding guess (publicHiding view)))) := by
  rcases view with ⟨_ | value, produced, raw, slots⟩
  · simp [slotted, viewObserved]
  · rw [Bool.eq_iff_iff, Bool.and_eq_true]
    unfold slotted
    simp only [decide_eq_true_eq, viewObserved, Option.map_some, Option.any_some, decisionOn, Bool.and_eq_true,
      lorWin_iff setup codec budget guess filter, testBit, publicHiding, decisionHiding, Option.bind_some]
    constructor
    · rintro ⟨⟨⟨eligible, bit⟩, target⟩, ideal⟩
      exact ⟨⟨⟨eligible, target⟩, ideal⟩, decide_eq_true bit⟩
    · rintro ⟨⟨⟨eligible, target⟩, ideal⟩, bit⟩
      exact ⟨⟨⟨eligible, of_decide_eq_true bit⟩, target⟩, ideal⟩

open Classical in
/-- The Server-side CE-LOR win with its Server-side slots is the Server-side eligibility with its slots and the test bit equal to the projected guess. -/
theorem win_peer_slotted (g : Fin budget.accept × Fin budget.capacity) (view : View 2 E X) :
    serverSlotted setup codec budget (lorWinPeerEvent setup.source.crypto codec setup.serverKeyId budget guess filter)
        lorClaim g view =
      (serverSlotted setup codec budget (lorEligPeerEvent setup.source.crypto codec setup.serverKeyId budget filter)
          lorClaim g view &&
        decide (testBit view = some (decisionHiding guess (publicHiding view)))) := by
  rcases view with ⟨_ | value, produced, raw, slots⟩
  · simp [serverSlotted, viewObserved]
  · rw [Bool.eq_iff_iff, Bool.and_eq_true]
    unfold serverSlotted
    simp only [decide_eq_true_eq, viewObserved, Option.map_some, Option.any_some, decisionOn, Bool.and_eq_true,
      lorWinPeer_iff setup codec budget guess filter, testBit, publicHiding, decisionHiding, Option.bind_some]
    constructor
    · rintro ⟨⟨⟨eligible, bit⟩, target⟩, ideal⟩
      exact ⟨⟨⟨eligible, target⟩, ideal⟩, decide_eq_true bit⟩
    · rintro ⟨⟨⟨eligible, target⟩, ideal⟩, bit⟩
      exact ⟨⟨⟨eligible, of_decide_eq_true bit⟩, target⟩, ideal⟩

end Win

/-! ### The final world -/

section Final
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response A X : Type}
open PqxdhRecordLiftIdeal (ctxView idealRecords)
open PqxdhDeploymentHeadlineChain (EnvG)

/-- C8 for CE-LOR (design-v2 section 4.5): on the record lift's view of `idealRecords` (mode P) with the ideal environment of the target of `g`, the win with `IdealSlots` has exactly half the probability of the eligibility with `IdealSlots` (`PqxdhRecordLiftLor.idealRecords_lor` with the projected guess and the public eligibility of `dec_g(E) ∧ IS_g`, which factors through the public hiding projection and implies `TestsHidden`). -/
theorem lor_final (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (ensureInit : StateT A ProbComp Bool) (bounds : FreshBounds)
    (adversary : OracleComp (ModeSpec .P) X) (budget : Budget) (g : Fin budget.accept × Fin budget.capacity)
    (runtime : A) (guess : X → Bool) (filter : List (PqxdhDeploymentInterface.PublicEntry .P) → Bool) :
    𝒟[slotted setup codec budget (lorWinEvent setup.source.crypto codec setup.serverKeyId budget guess filter)
        lorClaim g <$> (ctxView <$> idealRecords setup codec route
          (PqxdhDeploymentIdealEnv.envGD setup codec checks (Target.ofCE budget g) ensureInit 0 runtime)
          setup.serverKeyId bounds .P adversary)] {true} =
      2⁻¹ * 𝒟[slotted setup codec budget (lorEligEvent setup.source.crypto codec setup.serverKeyId budget filter)
        lorClaim g <$> (ctxView <$> idealRecords setup codec route
          (PqxdhDeploymentIdealEnv.envGD setup codec checks (Target.ofCE budget g) ensureInit 0 runtime)
          setup.serverKeyId bounds .P adversary)] {true} := by
  have invariant : ∀ view view' : View 2 (EnvG KemSK budget) X, publicHiding view = publicHiding view' →
      slotted setup codec budget (lorEligEvent setup.source.crypto codec setup.serverKeyId budget filter) lorClaim g
        view =
      slotted setup codec budget (lorEligEvent setup.source.crypto codec setup.serverKeyId budget filter) lorClaim g
        view' := fun view view' same =>
    decided_view setup codec budget _ lorClaim g
      (fun transcript slots => IdealSlots setup.source.crypto codec setup.serverKeyId (Target.ofCE budget g) slots
        transcript)
      (lorEligEvent_view setup.source.crypto codec setup.serverKeyId budget filter)
      (lorClaim_view setup.source.crypto codec setup.serverKeyId budget)
      (fun first second slots same => idealSlots_view setup.source.crypto codec setup.serverKeyId _ slots first second
        same) view view' same
  have hidden : ∀ view : View 2 (EnvG KemSK budget) X,
      slotted setup codec budget (lorEligEvent setup.source.crypto codec setup.serverKeyId budget filter) lorClaim g
        view = true → PqxdhRecordLiftIdeal.TestsHidden setup.source.crypto codec setup.serverKeyId view :=
    fun view held => PqxdhDeploymentHeadlineContain.lor_hidden setup codec budget filter g view held
  have win : slotted (E := EnvG KemSK budget) setup codec budget
      (lorWinEvent setup.source.crypto codec setup.serverKeyId budget guess filter) lorClaim g =
      fun view => PqxdhRecordLiftIdeal.lorGuess setup.source.crypto codec setup.serverKeyId (decisionHiding guess)
        (hidingOf (slotted setup codec budget (lorEligEvent setup.source.crypto codec setup.serverKeyId budget filter)
          lorClaim g)) view := funext fun view => by
    rw [guess_hiding setup codec guess _ invariant hidden view, win_slotted]
  have eligible : slotted (E := EnvG KemSK budget) setup codec budget
      (lorEligEvent setup.source.crypto codec setup.serverKeyId budget filter) lorClaim g =
      fun view => PqxdhRecordLiftIdeal.lorEligible setup.source.crypto codec setup.serverKeyId
        (hidingOf (slotted setup codec budget (lorEligEvent setup.source.crypto codec setup.serverKeyId budget filter)
          lorClaim g)) view := funext fun view => (eligible_hiding setup codec _ invariant hidden view).symm
  conv_lhs => rw [win, Functor.map_map]
  conv_rhs => rw [eligible, Functor.map_map]
  exact PqxdhRecordLiftLor.idealRecords_lor setup codec route setup.serverKeyId bounds 2 _ adversary
    (decisionHiding guess) _

/-- C8 for the Server-side CE-LOR (design-v2 section 4.5, `ce_lor_server`): on the record lift's view of `idealRecords` (mode P) with the ideal environment of the target of `g`, the Server-side win with `ServerSlots` has exactly half the probability of the Server-side eligibility with `ServerSlots`. -/
theorem lor_peer_final (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (ensureInit : StateT A ProbComp Bool) (bounds : FreshBounds)
    (adversary : OracleComp (ModeSpec .P) X) (budget : Budget) (g : Fin budget.accept × Fin budget.capacity)
    (runtime : A) (guess : X → Bool) (filter : List (PqxdhDeploymentInterface.PublicEntry .P) → Bool) :
    𝒟[serverSlotted setup codec budget (lorWinPeerEvent setup.source.crypto codec setup.serverKeyId budget guess filter)
        lorClaim g <$> (ctxView <$> idealRecords setup codec route
          (PqxdhDeploymentIdealEnv.envGD setup codec checks (Target.ofCE budget g) ensureInit 0 runtime)
          setup.serverKeyId bounds .P adversary)] {true} =
      2⁻¹ * 𝒟[serverSlotted setup codec budget
        (lorEligPeerEvent setup.source.crypto codec setup.serverKeyId budget filter) lorClaim g <$>
          (ctxView <$> idealRecords setup codec route
            (PqxdhDeploymentIdealEnv.envGD setup codec checks (Target.ofCE budget g) ensureInit 0 runtime)
            setup.serverKeyId bounds .P adversary)] {true} := by
  have invariant : ∀ view view' : View 2 (EnvG KemSK budget) X, publicHiding view = publicHiding view' →
      serverSlotted setup codec budget (lorEligPeerEvent setup.source.crypto codec setup.serverKeyId budget filter)
        lorClaim g view =
      serverSlotted setup codec budget (lorEligPeerEvent setup.source.crypto codec setup.serverKeyId budget filter)
        lorClaim g view' := fun view view' same =>
    decided_view setup codec budget _ lorClaim g
      (fun transcript slots => ServerSlots setup.source.crypto codec setup.serverKeyId (Target.ofCE budget g) slots
        transcript)
      (lorEligPeerEvent_view setup.source.crypto codec setup.serverKeyId budget filter)
      (lorClaim_view setup.source.crypto codec setup.serverKeyId budget)
      (fun first second slots same => serverSlots_view setup.source.crypto codec setup.serverKeyId _ slots first second
        same) view view' same
  have hidden : ∀ view : View 2 (EnvG KemSK budget) X,
      serverSlotted setup codec budget (lorEligPeerEvent setup.source.crypto codec setup.serverKeyId budget filter)
        lorClaim g view = true → PqxdhRecordLiftIdeal.TestsHidden setup.source.crypto codec setup.serverKeyId view :=
    fun view held => PqxdhDeploymentHeadlineContain.lor_peer_hidden setup codec budget filter g view held
  have win : serverSlotted (E := EnvG KemSK budget) setup codec budget
      (lorWinPeerEvent setup.source.crypto codec setup.serverKeyId budget guess filter) lorClaim g =
      fun view => PqxdhRecordLiftIdeal.lorGuess setup.source.crypto codec setup.serverKeyId (decisionHiding guess)
        (hidingOf (serverSlotted setup codec budget
          (lorEligPeerEvent setup.source.crypto codec setup.serverKeyId budget filter) lorClaim g)) view :=
    funext fun view => by rw [guess_hiding setup codec guess _ invariant hidden view, win_peer_slotted]
  have eligible : serverSlotted (E := EnvG KemSK budget) setup codec budget
      (lorEligPeerEvent setup.source.crypto codec setup.serverKeyId budget filter) lorClaim g =
      fun view => PqxdhRecordLiftIdeal.lorEligible setup.source.crypto codec setup.serverKeyId
        (hidingOf (serverSlotted setup codec budget
          (lorEligPeerEvent setup.source.crypto codec setup.serverKeyId budget filter) lorClaim g)) view :=
    funext fun view => (eligible_hiding setup codec _ invariant hidden view).symm
  conv_lhs => rw [win, Functor.map_map]
  conv_rhs => rw [eligible, Functor.map_map]
  exact PqxdhRecordLiftLor.idealRecords_lor setup codec route setup.serverKeyId bounds 2 _ adversary
    (decisionHiding guess) _

end Final

/-! ### Probability helpers -/

section Helpers

/-- Splitting a Boolean observation by a further predicate: its probability is that of its conjunction with the predicate plus that of its conjunction with the negation. -/
theorem chance_split {α : Type} (run : ProbComp α) (first : α → Bool) (second : α → Prop) [DecidablePred second] :
    𝒟[first <$> run] {true} = 𝒟[(fun a => decide (first a = true ∧ second a)) <$> run] {true} +
      𝒟[(fun a => decide (first a = true ∧ ¬second a)) <$> run] {true} := by
  have each : ∀ observation : α → Bool, 𝒟[observation <$> run] {true} = Pr{let a ← run}[observation a = true] :=
    fun observation => by
      rw [← prEvent_eq_evalDist_singleton _ true, prEvent_map]
  rw [each, each, each, OracleComp.prEvent_eq_tsum_ite, OracleComp.prEvent_eq_tsum_ite, OracleComp.prEvent_eq_tsum_ite, ← ENNReal.tsum_add]
  refine tsum_congr fun a => ?_
  generalize Pr{let y ← run}[y = a] = mass
  by_cases held : first a = true <;> by_cases other : second a <;> simp [held, other]

/-- The non-negative real `½ · x` as an extended non-negative real is half of `x`. -/
theorem ofReal_half (x : ℝ) : ENNReal.ofReal ((1 / 2) * x) = 2⁻¹ * ENNReal.ofReal x := by
  rw [ENNReal.ofReal_mul (by norm_num), one_div, ENNReal.ofReal_inv_of_pos two_pos, ENNReal.ofReal_ofNat]

/-- The real arithmetic of the CE-LOR composition: if `vw = sw + xw`, `ve = se + xe`, `rw = re / 2` and `0 ≤ xw ≤ xe`, then `|a - b/2|` is at most `|a - vw| + |b - ve|/2 + |sw - rw| + |se - re|/2 + xe/2`. -/
theorem lor_arith (a b vw ve sw se xw xe rw re : ℝ) (splitW : vw = sw + xw) (splitE : ve = se + xe)
    (final : rw = (1 / 2) * re) (nonneg : 0 ≤ xw) (below : xw ≤ xe) :
    |a - (1 / 2) * b| ≤ |a - vw| + (1 / 2) * |b - ve| + |sw - rw| + (1 / 2) * |se - re| + (1 / 2) * xe := by
  rw [abs_le]
  constructor <;> nlinarith [le_abs_self (a - vw), neg_abs_le (a - vw), le_abs_self (b - ve), neg_abs_le (b - ve),
    le_abs_self (sw - rw), neg_abs_le (sw - rw), le_abs_self (se - re), neg_abs_le (se - re)]

/-- The extended non-negative form of the CE-LOR composition: with `vw = sw + xw`, `ve = se + xe`, `rw = re/2`, `xw ≤ xe ≤ β`, the chain bounds `kW`, `kE` and the record-lift bounds `rW`, `rE`, the advantage `|a - b/2|` is at most `kW + rW + (kE + rE)/2 + β/2`. -/
theorem lor_bound (a b vw ve sw se xw xe rw re : ℝ≥0∞) (finiteSW : sw ≠ ⊤) (finiteSE : se ≠ ⊤)
    (finiteXW : xw ≠ ⊤) (finiteXE : xe ≠ ⊤)
    (splitW : vw = sw + xw) (splitE : ve = se + xe) (final : rw = 2⁻¹ * re) (below : xw ≤ xe)
    (kW kE : ℝ) (chainW : |a.toReal - vw.toReal| ≤ kW) (chainE : |b.toReal - ve.toReal| ≤ kE)
    (rW rE : ℝ≥0∞) (liftW : ENNReal.ofReal |sw.toReal - rw.toReal| ≤ rW)
    (liftE : ENNReal.ofReal |se.toReal - re.toReal| ≤ rE) (β : ℝ≥0∞) (anomaly : xe ≤ β) :
    ENNReal.ofReal |a.toReal - (1 / 2) * b.toReal| ≤
      ENNReal.ofReal kW + rW + 2⁻¹ * (ENNReal.ofReal kE + rE) + 2⁻¹ * β := by
  have real := lor_arith a.toReal b.toReal vw.toReal ve.toReal sw.toReal se.toReal xw.toReal xe.toReal rw.toReal
    re.toReal (by rw [splitW, ENNReal.toReal_add finiteSW finiteXW])
    (by rw [splitE, ENNReal.toReal_add finiteSE finiteXE])
    (by rw [final, ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_ofNat]; ring)
    ENNReal.toReal_nonneg (ENNReal.toReal_mono finiteXE below)
  calc ENNReal.ofReal |a.toReal - (1 / 2) * b.toReal|
      ≤ ENNReal.ofReal (|a.toReal - vw.toReal| + (1 / 2) * |b.toReal - ve.toReal| + |sw.toReal - rw.toReal| +
          (1 / 2) * |se.toReal - re.toReal| + (1 / 2) * xe.toReal) := ENNReal.ofReal_le_ofReal real
    _ = ENNReal.ofReal |a.toReal - vw.toReal| + ENNReal.ofReal ((1 / 2) * |b.toReal - ve.toReal|) +
          ENNReal.ofReal |sw.toReal - rw.toReal| + ENNReal.ofReal ((1 / 2) * |se.toReal - re.toReal|) +
          ENNReal.ofReal ((1 / 2) * xe.toReal) := by
        rw [ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_add (by positivity) (by positivity),
          ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_add (by positivity) (by positivity)]
    _ ≤ ENNReal.ofReal kW + 2⁻¹ * ENNReal.ofReal kE + rW + 2⁻¹ * rE + 2⁻¹ * β := by
        rw [ofReal_half, ofReal_half, ofReal_half, ENNReal.ofReal_toReal finiteXE]
        gcongr
    _ = _ := by ring

/-- The Server-side form of `lor_bound`, with no unslotted remainder: with `vw = sw`, `ve = se` and `rw = re/2`, the advantage `|a - b/2|` is at most `kW + rW + (kE + rE)/2`. -/
theorem lor_bound_server (a b vw ve sw se rw re : ℝ≥0∞) (finiteSW : sw ≠ ⊤) (finiteSE : se ≠ ⊤)
    (splitW : vw = sw) (splitE : ve = se) (final : rw = 2⁻¹ * re)
    (kW kE : ℝ) (chainW : |a.toReal - vw.toReal| ≤ kW) (chainE : |b.toReal - ve.toReal| ≤ kE)
    (rW rE : ℝ≥0∞) (liftW : ENNReal.ofReal |sw.toReal - rw.toReal| ≤ rW)
    (liftE : ENNReal.ofReal |se.toReal - re.toReal| ≤ rE) :
    ENNReal.ofReal |a.toReal - (1 / 2) * b.toReal| ≤ ENNReal.ofReal kW + rW + 2⁻¹ * (ENNReal.ofReal kE + rE) := by
  have bound := lor_bound a b vw ve sw se 0 0 rw re finiteSW finiteSE ENNReal.zero_ne_top ENNReal.zero_ne_top
    (by rw [splitW, add_zero]) (by rw [splitE, add_zero]) final le_rfl kW kE chainW chainE
    rW rE liftW liftE 0 le_rfl
  simpa using bound

end Helpers

/-! ### CE-LOR -/

section Headline
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response A X : Type}
open PqxdhRecordLiftIdeal (chainView ctxView realChains idealRecords)
open PqxdhServerAuthSourceCosts (KemCaps KemBound)
open PqxdhDeploymentHeadlineChain (EnvG kemLoss slotLoss recLoss chance_ne_top)
open PqxdhDeploymentHeadlineAnomaly (beta)

/-- The CE-LOR win names a designated claim: the first admitted test's handle designates its target. -/
theorem lorWin_named (crypto : Pqxdh.Crypto) (codec : Codec Reader Response) (serverKid : Aeneas.Std.U64)
    (budget : Budget) (guess : X → Bool) (filter : List (PqxdhDeploymentInterface.PublicEntry .P) → Bool)
    (observed : Observed X) (won : lorWinEvent crypto codec serverKid budget guess filter observed = true) :
    (PqxdhDeploymentKemTransfer.target crypto codec serverKid budget lorClaim observed).isSome := by
  classical
  unfold lorWinEvent at won
  obtain ⟨g, eligible, _⟩ := of_decide_eq_true won
  rw [lorElig_target crypto codec serverKid budget filter g observed eligible]
  rfl

/-- The CE-LOR eligibility names a designated claim. -/
theorem lorElig_named (crypto : Pqxdh.Crypto) (codec : Codec Reader Response) (serverKid : Aeneas.Std.U64)
    (budget : Budget) (filter : List (PqxdhDeploymentInterface.PublicEntry .P) → Bool) (observed : Observed X)
    (eligible : lorEligEvent crypto codec serverKid budget filter observed = true) :
    (PqxdhDeploymentKemTransfer.target crypto codec serverKid budget lorClaim observed).isSome := by
  classical
  unfold lorEligEvent at eligible
  obtain ⟨g, holds⟩ := of_decide_eq_true eligible
  rw [lorElig_target crypto codec serverKid budget filter g observed holds]
  rfl

/-- The Server-side CE-LOR win names a designated claim. -/
theorem lorWinPeer_named (crypto : Pqxdh.Crypto) (codec : Codec Reader Response) (serverKid : Aeneas.Std.U64)
    (budget : Budget) (guess : X → Bool) (filter : List (PqxdhDeploymentInterface.PublicEntry .P) → Bool)
    (observed : Observed X) (won : lorWinPeerEvent crypto codec serverKid budget guess filter observed = true) :
    (PqxdhDeploymentKemTransfer.target crypto codec serverKid budget lorClaim observed).isSome := by
  classical
  unfold lorWinPeerEvent at won
  obtain ⟨⟨g, eligible, _⟩, _⟩ := of_decide_eq_true won
  rw [lorElig_target crypto codec serverKid budget filter g observed eligible]
  rfl

/-- The Server-side CE-LOR eligibility names a designated claim. -/
theorem lorEligPeer_named (crypto : Pqxdh.Crypto) (codec : Codec Reader Response) (serverKid : Aeneas.Std.U64)
    (budget : Budget) (filter : List (PqxdhDeploymentInterface.PublicEntry .P) → Bool) (observed : Observed X)
    (eligible : lorEligPeerEvent crypto codec serverKid budget filter observed = true) :
    (PqxdhDeploymentKemTransfer.target crypto codec serverKid budget lorClaim observed).isSome := by
  classical
  unfold lorEligPeerEvent at eligible
  obtain ⟨⟨g, holds⟩, _⟩ := of_decide_eq_true eligible
  rw [lorElig_target crypto codec serverKid budget filter g observed holds]
  rfl

open Classical in
/-- On the record lift's view of the all-real chain world with the ideal environment of a target, under `Phase1ReadBack`, a per-target decision has the probability of the decision with `ServerSlots` (`PqxdhDeploymentHeadlineChain.real_slots_server`). -/
theorem server_view (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (ensureInit : StateT A ProbComp Bool) (bounds : FreshBounds) (mode : Mode) (adversary : OracleComp (ModeSpec mode) X)
    (budget : Budget) (event : Observed X → Bool) (claim : Observed X → Option Handle)
    (g : Fin budget.accept × Fin budget.capacity) (runtime : A) :
    𝒟[(fun view => (viewObserved view).any (decisionOn setup codec budget event claim g)) <$>
        (chainView <$> realChains setup codec route
          (PqxdhDeploymentIdealEnv.envGD setup codec checks (Target.ofCE budget g) ensureInit 0 runtime)
          setup.serverKeyId bounds mode adversary)] {true} =
      𝒟[serverSlotted setup codec budget event claim g <$>
        (chainView <$> realChains setup codec route
          (PqxdhDeploymentIdealEnv.envGD setup codec checks (Target.ofCE budget g) ensureInit 0 runtime)
          setup.serverKeyId bounds mode adversary)] {true} := by
  congr 2
  rw [Functor.map_map, Functor.map_map]
  refine PqxdhDeploymentKemTransfer.map_support_congr _ _ _ fun result member => ?_
  simp only [serverSlotted]
  rw [Bool.eq_iff_iff, decide_eq_true_iff]
  exact ⟨fun held => ⟨held, PqxdhDeploymentHeadlineChain.real_slots_server setup codec checks route phase1
    (Target.ofCE budget g) ensureInit 0 runtime bounds mode adversary result member⟩, And.left⟩

open Classical in
/-- **CE-LOR, per target** (design-v2 section 4.5): in mode P, for the target `g`, the left-or-right advantage of the deployment experiment at `g` (the probability of the win with the first admitted test designating `g`, minus half the probability of the eligibility with it) is, in absolute value, at most `kemLoss + slotLoss + recLoss_g(dec_g(W) ∧ IS_g)` of the win, plus half of `kemLoss + slotLoss + recLoss_g(dec_g(E) ∧ IS_g)` of the eligibility, plus `β_g / 2`. -/
theorem ce_lor_target (setup : Setup baseSpec KemSK)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem)
    (codec : Codec Reader Response) (checks : Checks) (route : RawCtxServerRouting.SenderDecoder)
    (ensureInit : StateT A ProbComp Bool) (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec)
    (correct : PqxdhFullSecretInputKdf.SourceFullCorrect setup.source setup.hmac) (caps : KemCaps)
    (bounded : KemBound setup caps) (qInit : ℕ) (initBound : ∀ state, (ensureInit.run state).IsTotalQueryBound qInit)
    (bounds : FreshBounds) (adversary : OracleComp (ModeSpec .P) X) (budget : Budget)
    (respects : budget.Respects adversary) (runtime : A) (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery)
    (guess : X → Bool) (filter : List (PqxdhDeploymentInterface.PublicEntry .P) → Bool)
    (g : Fin budget.accept × Fin budget.capacity) :
    ENNReal.ofReal |(𝒟[(fun outcome => decide (happens (lorWinEvent setup.source.crypto codec setup.serverKeyId budget
          guess filter) outcome = true ∧
          designated setup.source.crypto codec setup.serverKeyId budget lorClaim outcome = some g)) <$>
        (PqxdhDeploymentSecrecy.game setup codec checks route ensureInit 0 bounds .P adversary).run runtime]
          {true}).toReal -
        (1 / 2) * (𝒟[(fun outcome => decide (happens (lorEligEvent setup.source.crypto codec setup.serverKeyId budget
          filter) outcome = true ∧
          designated setup.source.crypto codec setup.serverKeyId budget lorClaim outcome = some g)) <$>
        (PqxdhDeploymentSecrecy.game setup codec checks route ensureInit 0 bounds .P adversary).run runtime]
          {true}).toReal| ≤
      ENNReal.ofReal (kemLoss setup codec checks route ensureInit bounds .P adversary budget
        (lorWinEvent setup.source.crypto codec setup.serverKeyId budget guess filter) lorClaim g runtime) +
      ENNReal.ofReal (slotLoss setup codec checks route ensureInit bounds .P adversary budget
        (lorWinEvent setup.source.crypto codec setup.serverKeyId budget guess filter) lorClaim g runtime) +
      recLoss setup codec checks route ensureInit bounds .P adversary budget g runtime fallback caps qInit
        (slotted setup codec budget (lorWinEvent setup.source.crypto codec setup.serverKeyId budget guess filter)
          lorClaim g) +
      2⁻¹ * (ENNReal.ofReal (kemLoss setup codec checks route ensureInit bounds .P adversary budget
          (lorEligEvent setup.source.crypto codec setup.serverKeyId budget filter) lorClaim g runtime) +
        ENNReal.ofReal (slotLoss setup codec checks route ensureInit bounds .P adversary budget
          (lorEligEvent setup.source.crypto codec setup.serverKeyId budget filter) lorClaim g runtime) +
        recLoss setup codec checks route ensureInit bounds .P adversary budget g runtime fallback caps qInit
          (slotted setup codec budget (lorEligEvent setup.source.crypto codec setup.serverKeyId budget filter)
            lorClaim g)) +
      2⁻¹ * beta setup codec route checks ensureInit bounds .P adversary budget g runtime := by
  set realView := chainView <$> realChains setup codec route
    (PqxdhDeploymentIdealEnv.envGD setup codec checks (Target.ofCE budget g) ensureInit 0 runtime)
    setup.serverKeyId bounds .P adversary with hrealView
  set idealView := ctxView <$> idealRecords setup codec route
    (PqxdhDeploymentIdealEnv.envGD setup codec checks (Target.ofCE budget g) ensureInit 0 runtime)
    setup.serverKeyId bounds .P adversary with hidealView
  set win := lorWinEvent setup.source.crypto codec setup.serverKeyId budget guess filter with hwin
  set elig := lorEligEvent setup.source.crypto codec setup.serverKeyId budget filter with helig
  set ideal : View 2 (EnvG KemSK budget) X → Prop := fun view => ∀ value, view.result = some value →
    IdealSlots setup.source.crypto codec setup.serverKeyId (Target.ofCE budget g) view.slots value.2.1.transcript
    with hideal
  have winElig : ∀ view : View 2 (EnvG KemSK budget) X,
      (viewObserved view).any (decisionOn setup codec budget win lorClaim g) = true →
        (viewObserved view).any (decisionOn setup codec budget elig lorClaim g) = true := by
    intro view held
    rcases view with ⟨_ | value, produced, raw, slots⟩
    · simp [viewObserved] at held
    · simp only [viewObserved, Option.map_some, Option.any_some, decisionOn, Bool.and_eq_true] at held ⊢
      exact ⟨((lorWin_iff setup codec budget guess filter _).mp held.1).1, held.2⟩
  have splitW := chance_split realView (fun view => (viewObserved view).any (decisionOn setup codec budget win lorClaim g))
    ideal
  have splitE := chance_split realView (fun view => (viewObserved view).any
    (decisionOn setup codec budget elig lorClaim g)) ideal
  have below := PqxdhDeploymentHeadlineContain.chance_mono realView
    (fun view => decide ((viewObserved view).any (decisionOn setup codec budget win lorClaim g) = true ∧ ¬ideal view))
    (fun view => decide ((viewObserved view).any (decisionOn setup codec budget elig lorClaim g) = true ∧ ¬ideal view))
    (fun view held => by
      rw [decide_eq_true_iff] at held ⊢
      exact ⟨winElig view held.1, held.2⟩)
  have anomaly := (PqxdhDeploymentHeadlineChain.view_unslotted setup codec checks route phase1 phase2
    (Target.ofCE budget g) ensureInit 0 runtime bounds .P adversary
    (fun view => (viewObserved view).any (decisionOn setup codec budget elig lorClaim g))).trans
      (PqxdhDeploymentHeadlineAnomaly.anomaly_beta setup functional codec checks route ensureInit phase1 phase2 bounds .P
        adversary budget g runtime)
  have final := lor_final setup codec checks route ensureInit bounds adversary budget g runtime guess filter
  have chainW := PqxdhDeploymentHeadlineChain.chain_close setup functional codec checks route ensureInit phase1 phase2
    correct bounds .P adversary budget respects win lorClaim g runtime
  have chainE := PqxdhDeploymentHeadlineChain.chain_close setup functional codec checks route ensureInit phase1 phase2
    correct bounds .P adversary budget respects elig lorClaim g runtime
  have liftW := PqxdhDeploymentHeadlineChain.records_close setup codec checks route correct caps bounded ensureInit qInit
    initBound bounds .P adversary budget respects g runtime fallback (slotted setup codec budget win lorClaim g)
  have liftE := PqxdhDeploymentHeadlineChain.records_close setup codec checks route correct caps bounded ensureInit qInit
    initBound bounds .P adversary budget respects g runtime fallback (slotted setup codec budget elig lorClaim g)
  have bound := lor_bound _ _ _ _ _ _ _ _ _ _ (chance_ne_top _ _) (chance_ne_top _ _) (chance_ne_top _ _)
    (chance_ne_top _ _) splitW splitE final below _ _ chainW chainE _ _ liftW liftE _ anomaly
  refine bound.trans ?_
  gcongr ?_ + _ + 2⁻¹ * (?_ + _) + _ <;> exact ENNReal.ofReal_add_le

open Classical in
/-- **CE-LOR** (design-v2 section 4.5, `ce_lor`): in mode P, for every public filter `F` on the mode-P transcript view, the left-or-right advantage of the deployment experiment, the probability that the run is eligible (a test session exists, `F` holds, and every admitted test designates the target of the first admitted test) and the adversary's guess equals the test bit, minus half the probability that it is eligible, is, in absolute value, at most the sum over `g` in `Fin qAccept × Fin qCreate` (with `k` read in `Fin (qCreate + 1)`) of `kemLoss + slotLoss + recLoss_g(dec_g(W) ∧ IS_g)` of the win, plus half of the same terms of the eligibility, plus `β_g / 2`, each with coefficient one. -/
theorem ce_lor (setup : Setup baseSpec KemSK)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem)
    (codec : Codec Reader Response) (checks : Checks) (route : RawCtxServerRouting.SenderDecoder)
    (ensureInit : StateT A ProbComp Bool) (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec)
    (correct : PqxdhFullSecretInputKdf.SourceFullCorrect setup.source setup.hmac) (caps : KemCaps)
    (bounded : KemBound setup caps) (qInit : ℕ) (initBound : ∀ state, (ensureInit.run state).IsTotalQueryBound qInit)
    (bounds : FreshBounds) (adversary : OracleComp (ModeSpec .P) X) (budget : Budget)
    (respects : budget.Respects adversary) (runtime : A) (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery)
    (guess : X → Bool) (filter : List (PqxdhDeploymentInterface.PublicEntry .P) → Bool) :
    ENNReal.ofReal |(𝒟[(fun outcome => happens (lorWinEvent setup.source.crypto codec setup.serverKeyId budget guess
          filter) outcome) <$>
        (PqxdhDeploymentSecrecy.game setup codec checks route ensureInit 0 bounds .P adversary).run runtime]
          {true}).toReal -
        (1 / 2) * (𝒟[(fun outcome => happens (lorEligEvent setup.source.crypto codec setup.serverKeyId budget filter)
          outcome) <$>
        (PqxdhDeploymentSecrecy.game setup codec checks route ensureInit 0 bounds .P adversary).run runtime]
          {true}).toReal| ≤
      ∑ g : Fin budget.accept × Fin budget.create,
        (ENNReal.ofReal (kemLoss setup codec checks route ensureInit bounds .P adversary budget
            (lorWinEvent setup.source.crypto codec setup.serverKeyId budget guess filter) lorClaim (g.1, g.2.castSucc)
            runtime) +
          ENNReal.ofReal (slotLoss setup codec checks route ensureInit bounds .P adversary budget
            (lorWinEvent setup.source.crypto codec setup.serverKeyId budget guess filter) lorClaim (g.1, g.2.castSucc)
            runtime) +
          recLoss setup codec checks route ensureInit bounds .P adversary budget (g.1, g.2.castSucc) runtime fallback
            caps qInit (slotted setup codec budget
              (lorWinEvent setup.source.crypto codec setup.serverKeyId budget guess filter) lorClaim
              (g.1, g.2.castSucc)) +
          2⁻¹ * (ENNReal.ofReal (kemLoss setup codec checks route ensureInit bounds .P adversary budget
              (lorEligEvent setup.source.crypto codec setup.serverKeyId budget filter) lorClaim (g.1, g.2.castSucc)
              runtime) +
            ENNReal.ofReal (slotLoss setup codec checks route ensureInit bounds .P adversary budget
              (lorEligEvent setup.source.crypto codec setup.serverKeyId budget filter) lorClaim (g.1, g.2.castSucc)
              runtime) +
            recLoss setup codec checks route ensureInit bounds .P adversary budget (g.1, g.2.castSucc) runtime fallback
              caps qInit (slotted setup codec budget
                (lorEligEvent setup.source.crypto codec setup.serverKeyId budget filter) lorClaim
                (g.1, g.2.castSucc))) +
          2⁻¹ * beta setup codec route checks ensureInit bounds .P adversary budget (g.1, g.2.castSucc) runtime) := by
  rw [PqxdhDeploymentHeadlineChain.split_named setup codec checks route ensureInit phase1 phase2 bounds .P adversary
      budget respects _ lorClaim runtime (lorWin_named setup.source.crypto codec setup.serverKeyId budget guess filter),
    PqxdhDeploymentHeadlineChain.split_named setup codec checks route ensureInit phase1 phase2 bounds .P adversary
      budget respects _ lorClaim runtime (lorElig_named setup.source.crypto codec setup.serverKeyId budget filter),
    ENNReal.toReal_sum (fun _ _ => chance_ne_top _ _), ENNReal.toReal_sum (fun _ _ => chance_ne_top _ _),
    Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine (ENNReal.ofReal_le_ofReal (Finset.abs_sum_le_sum_abs _ _)).trans ?_
  rw [ENNReal.ofReal_sum_of_nonneg (fun _ _ => abs_nonneg _)]
  exact Finset.sum_le_sum fun g _ => ce_lor_target setup functional codec checks route ensureInit phase1 phase2 correct
    caps bounded qInit initBound bounds adversary budget respects runtime fallback guess filter (g.1, g.2.castSucc)

open Classical in
/-- **CE-LOR on Server peers, per target** (design-v2 section 4.5, `ce_lor_server`): the per-target bound of `ce_lor_target` for the Server-side events (every admitted test handle a Server peer), with `ServerSlots` in place of `IdealSlots` and no anomaly term. -/
theorem ce_lor_server_target (setup : Setup baseSpec KemSK)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem)
    (codec : Codec Reader Response) (checks : Checks) (route : RawCtxServerRouting.SenderDecoder)
    (ensureInit : StateT A ProbComp Bool) (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec)
    (correct : PqxdhFullSecretInputKdf.SourceFullCorrect setup.source setup.hmac) (caps : KemCaps)
    (bounded : KemBound setup caps) (qInit : ℕ) (initBound : ∀ state, (ensureInit.run state).IsTotalQueryBound qInit)
    (bounds : FreshBounds) (adversary : OracleComp (ModeSpec .P) X) (budget : Budget)
    (respects : budget.Respects adversary) (runtime : A) (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery)
    (guess : X → Bool) (filter : List (PqxdhDeploymentInterface.PublicEntry .P) → Bool)
    (g : Fin budget.accept × Fin budget.capacity) :
    ENNReal.ofReal |(𝒟[(fun outcome => decide (happens (lorWinPeerEvent setup.source.crypto codec setup.serverKeyId
          budget guess filter) outcome = true ∧
          designated setup.source.crypto codec setup.serverKeyId budget lorClaim outcome = some g)) <$>
        (PqxdhDeploymentSecrecy.game setup codec checks route ensureInit 0 bounds .P adversary).run runtime]
          {true}).toReal -
        (1 / 2) * (𝒟[(fun outcome => decide (happens (lorEligPeerEvent setup.source.crypto codec setup.serverKeyId
          budget filter) outcome = true ∧
          designated setup.source.crypto codec setup.serverKeyId budget lorClaim outcome = some g)) <$>
        (PqxdhDeploymentSecrecy.game setup codec checks route ensureInit 0 bounds .P adversary).run runtime]
          {true}).toReal| ≤
      ENNReal.ofReal (kemLoss setup codec checks route ensureInit bounds .P adversary budget
        (lorWinPeerEvent setup.source.crypto codec setup.serverKeyId budget guess filter) lorClaim g runtime) +
      ENNReal.ofReal (slotLoss setup codec checks route ensureInit bounds .P adversary budget
        (lorWinPeerEvent setup.source.crypto codec setup.serverKeyId budget guess filter) lorClaim g runtime) +
      recLoss setup codec checks route ensureInit bounds .P adversary budget g runtime fallback caps qInit
        (serverSlotted setup codec budget
          (lorWinPeerEvent setup.source.crypto codec setup.serverKeyId budget guess filter) lorClaim g) +
      2⁻¹ * (ENNReal.ofReal (kemLoss setup codec checks route ensureInit bounds .P adversary budget
          (lorEligPeerEvent setup.source.crypto codec setup.serverKeyId budget filter) lorClaim g runtime) +
        ENNReal.ofReal (slotLoss setup codec checks route ensureInit bounds .P adversary budget
          (lorEligPeerEvent setup.source.crypto codec setup.serverKeyId budget filter) lorClaim g runtime) +
        recLoss setup codec checks route ensureInit bounds .P adversary budget g runtime fallback caps qInit
          (serverSlotted setup codec budget
            (lorEligPeerEvent setup.source.crypto codec setup.serverKeyId budget filter) lorClaim g)) := by
  have viewW := server_view setup codec checks route phase1 ensureInit bounds .P adversary budget
    (lorWinPeerEvent setup.source.crypto codec setup.serverKeyId budget guess filter) lorClaim g runtime
  have viewE := server_view setup codec checks route phase1 ensureInit bounds .P adversary budget
    (lorEligPeerEvent setup.source.crypto codec setup.serverKeyId budget filter) lorClaim g runtime
  have final := lor_peer_final setup codec checks route ensureInit bounds adversary budget g runtime guess filter
  have chainW := PqxdhDeploymentHeadlineChain.chain_close setup functional codec checks route ensureInit phase1 phase2
    correct bounds .P adversary budget respects
    (lorWinPeerEvent setup.source.crypto codec setup.serverKeyId budget guess filter) lorClaim g runtime
  have chainE := PqxdhDeploymentHeadlineChain.chain_close setup functional codec checks route ensureInit phase1 phase2
    correct bounds .P adversary budget respects
    (lorEligPeerEvent setup.source.crypto codec setup.serverKeyId budget filter) lorClaim g runtime
  have liftW := PqxdhDeploymentHeadlineChain.records_close setup codec checks route correct caps bounded ensureInit qInit
    initBound bounds .P adversary budget respects g runtime fallback (serverSlotted setup codec budget
      (lorWinPeerEvent setup.source.crypto codec setup.serverKeyId budget guess filter) lorClaim g)
  have liftE := PqxdhDeploymentHeadlineChain.records_close setup codec checks route correct caps bounded ensureInit qInit
    initBound bounds .P adversary budget respects g runtime fallback (serverSlotted setup codec budget
      (lorEligPeerEvent setup.source.crypto codec setup.serverKeyId budget filter) lorClaim g)
  have bound := lor_bound_server _ _ _ _ _ _ _ _ (chance_ne_top _ _) (chance_ne_top _ _) viewW viewE final _ _ chainW
    chainE _ _ liftW liftE
  refine bound.trans ?_
  gcongr ?_ + _ + 2⁻¹ * (?_ + _) <;> exact ENNReal.ofReal_add_le

open Classical in
/-- **CE-LOR on Server peers** (design-v2 section 4.5, `ce_lor_server`): `ce_lor` for the Server-side events (every admitted test handle a Server peer, `PeerTests`), with `ServerSlots` and no anomaly term, summed over `g` in `Fin qAccept × Fin qCreate` with coefficient one. -/
theorem ce_lor_server (setup : Setup baseSpec KemSK)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem)
    (codec : Codec Reader Response) (checks : Checks) (route : RawCtxServerRouting.SenderDecoder)
    (ensureInit : StateT A ProbComp Bool) (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec)
    (correct : PqxdhFullSecretInputKdf.SourceFullCorrect setup.source setup.hmac) (caps : KemCaps)
    (bounded : KemBound setup caps) (qInit : ℕ) (initBound : ∀ state, (ensureInit.run state).IsTotalQueryBound qInit)
    (bounds : FreshBounds) (adversary : OracleComp (ModeSpec .P) X) (budget : Budget)
    (respects : budget.Respects adversary) (runtime : A) (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery)
    (guess : X → Bool) (filter : List (PqxdhDeploymentInterface.PublicEntry .P) → Bool) :
    ENNReal.ofReal |(𝒟[(fun outcome => happens (lorWinPeerEvent setup.source.crypto codec setup.serverKeyId budget guess
          filter) outcome) <$>
        (PqxdhDeploymentSecrecy.game setup codec checks route ensureInit 0 bounds .P adversary).run runtime]
          {true}).toReal -
        (1 / 2) * (𝒟[(fun outcome => happens (lorEligPeerEvent setup.source.crypto codec setup.serverKeyId budget
          filter) outcome) <$>
        (PqxdhDeploymentSecrecy.game setup codec checks route ensureInit 0 bounds .P adversary).run runtime]
          {true}).toReal| ≤
      ∑ g : Fin budget.accept × Fin budget.create,
        (ENNReal.ofReal (kemLoss setup codec checks route ensureInit bounds .P adversary budget
            (lorWinPeerEvent setup.source.crypto codec setup.serverKeyId budget guess filter) lorClaim
            (g.1, g.2.castSucc) runtime) +
          ENNReal.ofReal (slotLoss setup codec checks route ensureInit bounds .P adversary budget
            (lorWinPeerEvent setup.source.crypto codec setup.serverKeyId budget guess filter) lorClaim
            (g.1, g.2.castSucc) runtime) +
          recLoss setup codec checks route ensureInit bounds .P adversary budget (g.1, g.2.castSucc) runtime fallback
            caps qInit (serverSlotted setup codec budget
              (lorWinPeerEvent setup.source.crypto codec setup.serverKeyId budget guess filter) lorClaim
              (g.1, g.2.castSucc)) +
          2⁻¹ * (ENNReal.ofReal (kemLoss setup codec checks route ensureInit bounds .P adversary budget
              (lorEligPeerEvent setup.source.crypto codec setup.serverKeyId budget filter) lorClaim
              (g.1, g.2.castSucc) runtime) +
            ENNReal.ofReal (slotLoss setup codec checks route ensureInit bounds .P adversary budget
              (lorEligPeerEvent setup.source.crypto codec setup.serverKeyId budget filter) lorClaim
              (g.1, g.2.castSucc) runtime) +
            recLoss setup codec checks route ensureInit bounds .P adversary budget (g.1, g.2.castSucc) runtime fallback
              caps qInit (serverSlotted setup codec budget
                (lorEligPeerEvent setup.source.crypto codec setup.serverKeyId budget filter) lorClaim
                (g.1, g.2.castSucc)))) := by
  rw [PqxdhDeploymentHeadlineChain.split_named setup codec checks route ensureInit phase1 phase2 bounds .P adversary
      budget respects _ lorClaim runtime
      (lorWinPeer_named setup.source.crypto codec setup.serverKeyId budget guess filter),
    PqxdhDeploymentHeadlineChain.split_named setup codec checks route ensureInit phase1 phase2 bounds .P adversary
      budget respects _ lorClaim runtime (lorEligPeer_named setup.source.crypto codec setup.serverKeyId budget filter),
    ENNReal.toReal_sum (fun _ _ => chance_ne_top _ _), ENNReal.toReal_sum (fun _ _ => chance_ne_top _ _),
    Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine (ENNReal.ofReal_le_ofReal (Finset.abs_sum_le_sum_abs _ _)).trans ?_
  rw [ENNReal.ofReal_sum_of_nonneg (fun _ _ => abs_nonneg _)]
  exact Finset.sum_le_sum fun g _ => ce_lor_server_target setup functional codec checks route ensureInit phase1 phase2
    correct caps bounded qInit initBound bounds adversary budget respects runtime fallback guess filter
    (g.1, g.2.castSucc)

end Headline

end BeaconcryptCore.Computational.PqxdhDeploymentHeadlineLor

-- Axiom guards (generated)

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineLor.filterMap_view' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineLor.filterMap_view

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineLor.sameView_symm' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineLor.sameView_symm

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineLor.peerOf_view' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineLor.peerOf_view

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineLor.idealSlots_view' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineLor.idealSlots_view

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineLor.serverSlots_view' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineLor.serverSlots_view

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineLor.firstTest_view' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineLor.firstTest_view

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineLor.split_view' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineLor.split_view

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineLor.admitted_view' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineLor.admitted_view

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineLor.lorElig_view' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineLor.lorElig_view

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineLor.peerTests_view' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineLor.peerTests_view

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineLor.lorEligEvent_view' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineLor.lorEligEvent_view

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineLor.lorEligPeerEvent_view' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineLor.lorEligPeerEvent_view

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineLor.lorClaim_view' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineLor.lorClaim_view

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineLor.decided_view' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineLor.decided_view

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineLor.hidingOf_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineLor.hidingOf_eq

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineLor.eligible_hiding' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineLor.eligible_hiding

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineLor.guess_hiding' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineLor.guess_hiding

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineLor.lorWin_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineLor.lorWin_iff

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineLor.lorWinPeer_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineLor.lorWinPeer_iff

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineLor.win_slotted' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineLor.win_slotted

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineLor.win_peer_slotted' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineLor.win_peer_slotted

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineLor.lor_final' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineLor.lor_final

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineLor.lor_peer_final' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineLor.lor_peer_final

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineLor.chance_split' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineLor.chance_split

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineLor.ofReal_half' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineLor.ofReal_half

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineLor.lor_arith' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineLor.lor_arith

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineLor.lor_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineLor.lor_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineLor.lor_bound_server' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineLor.lor_bound_server

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineLor.lorWin_named' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineLor.lorWin_named

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineLor.lorElig_named' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineLor.lorElig_named

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineLor.lorWinPeer_named' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineLor.lorWinPeer_named

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineLor.lorEligPeer_named' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineLor.lorEligPeer_named

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineLor.server_view' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineLor.server_view

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineLor.ce_lor_target' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineLor.ce_lor_target

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineLor.ce_lor' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineLor.ce_lor

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineLor.ce_lor_server_target' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineLor.ce_lor_server_target

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineLor.ce_lor_server' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineLor.ce_lor_server
