-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeEvents
import BeaconcryptCore.Computational.PqxdhRecordLiftHiding

/-! Mode P hides raw receive plaintexts while the native experiment retains its complete original Mode O ledger privately. This coupling preserves the original test bit, fresh messages, original transcript's public view and the full native transcript's ML-pin-aware public view. The native APP observation is proved invariant directly, without an arbitrary event-correspondence premise. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeLedgerHiding
open RegistrationNativeInterface (Spec FullSpec ModeSpec Entry eraseCore eraseQuery project asModeO)
open RegistrationNativeLedger (State)
open PqxdhRecordLiftHiding (Coupled LedgerRel EqRel eqRel_eq)
open PqxdhServerAuthExperiment (Codec)
open PqxdhDeploymentInterface (FreshBounds)
variable {Reader Response Value First Second NativeState : Type}

def eraseCoreReply : (query : Spec.Domain) → Spec.Range query →
    PqxdhDeploymentInterface.Spec.Range (eraseCore query)
  | .inl _, reply => reply
  | .inr _, reply => reply

def eraseReply : (query : FullSpec.Domain) → FullSpec.Range query →
    PqxdhDeploymentInterface.FullSpec.Range (eraseQuery query)
  | .inl core, reply => eraseCoreReply core reply
  | .inr _, reply => reply

def CoreRel (query : Spec.Domain) (first second : Spec.Range query) : Prop :=
  PqxdhRecordLiftHiding.SpecRel (eraseCore query) (eraseCoreReply query first) (eraseCoreReply query second)

def FullRel (query : FullSpec.Domain) (first second : FullSpec.Range query) : Prop :=
  PqxdhRecordLiftHiding.FullRel (eraseQuery query) (eraseReply query first) (eraseReply query second)

abbrev PublicEntry := Σ query : RegistrationNativeInterface.Query, (ModeSpec .P).Range query

def view (entry : Entry) : PublicEntry := ⟨entry.query, project .P entry.query entry.reply⟩

def StateRel (first second : State) : Prop :=
  LedgerRel first.ledger second.ledger ∧ first.transcript.map view = second.transcript.map view

private theorem project_equal (query : FullSpec.Domain) (first second : FullSpec.Range query)
    (related : FullRel query first second) : project .P query first = project .P query second := by
  rcases query with (coin | command) | secrecy
  · cases (show first = second from related)
    rfl
  · cases command
    case serverRaw raw => exact related
    case beaconRaw owner raw => exact related
    all_goals cases (show first = second from related); rfl
  · cases (show first = second from related)
    rfl

/-- Coupled replies keep every native public field, including both creation pins, and hide only actual raw plaintext replies. -/
theorem view_equal (query : FullSpec.Domain) (first second : FullSpec.Range query)
    (related : FullRel query first second) : view ⟨query, first⟩ = view ⟨query, second⟩ := by
  unfold view
  rw [project_equal query first second related]

private theorem erase_value (query : FullSpec.Domain) (reply : FullSpec.Range query) :
    (Entry.mk query reply).erase = ⟨eraseQuery query, eraseReply query reply⟩ := by
  rcases query with (coin | command) | secrecy <;> rfl

private theorem original_view (query : FullSpec.Domain) (first second : FullSpec.Range query)
    (related : FullRel query first second) :
    PqxdhDeploymentInterface.Entry.view .P ⟨eraseQuery query, eraseReply query first⟩ =
      PqxdhDeploymentInterface.Entry.view .P ⟨eraseQuery query, eraseReply query second⟩ := by
  cases query with
  | inl core =>
      exact PqxdhRecordLiftHiding.view_spec (eraseCore core)
        (eraseCoreReply core first) (eraseCoreReply core second) related
  | inr secrecy => cases (show first = second from related); rfl

/-- Appending an actual ordinary query preserves the private original ledger and complete native public-view relation. -/
theorem record_related (first second : State) (related : StateRel first second)
    (query : FullSpec.Domain) (reply₁ reply₂ : FullSpec.Range query) (replies : FullRel query reply₁ reply₂) :
    StateRel (RegistrationNativeLedger.record first ⟨query, reply₁⟩)
      (RegistrationNativeLedger.record second ⟨query, reply₂⟩) := by
  constructor
  · have recorded := PqxdhRecordLiftHiding.ledgerRel_record first.ledger second.ledger related.1
      (eraseQuery query) (eraseReply query reply₁) (eraseReply query reply₂)
      (original_view query reply₁ reply₂ replies)
    simpa only [RegistrationNativeLedger.record, PqxdhDeploymentSecrecy.Ledger.record,
      erase_value] using recorded
  · have same := view_equal query reply₁ reply₂ replies
    simp only [RegistrationNativeLedger.record, List.map_append, List.map_cons,
      List.map_nil, related.2, same]

/-- The literal old secrecy callbacks embed into the native API with unchanged coupled replies; their unused creation branch asserts no native membership. -/
theorem legacy_couple {Related : First → Second → Prop}
    {first : OracleComp PqxdhDeploymentInterface.Spec First}
    {second : OracleComp PqxdhDeploymentInterface.Spec Second}
    (coupled : Coupled PqxdhRecordLiftHiding.SpecRel Related first second) :
    Coupled CoreRel Related (simulateQ RegistrationNativeLedger.legacyLift first)
      (simulateQ RegistrationNativeLedger.legacyLift second) := by
  apply Coupled.simulateQ _ _ ?_ coupled
  intro query
  cases query with
  | inl coin => exact Coupled.query (Rr := CoreRel) (.inl coin)
  | inr command =>
      cases command with
      | create pin keyId => exact Coupled.query (Rr := CoreRel) (.inr (.create pin [] keyId))
      | bundle owner => exact Coupled.query (Rr := CoreRel) (.inr (.bundle owner))
      | accept raw => exact Coupled.query (Rr := CoreRel) (.inr (.accept raw))
      | build session payload => exact Coupled.query (Rr := CoreRel) (.inr (.build session payload))
      | finish owner raw => exact Coupled.query (Rr := CoreRel) (.inr (.finish owner raw))
      | hmac key message => exact Coupled.query (Rr := CoreRel) (.inr (.hmac key message))
      | hash bytes => exact Coupled.query (Rr := CoreRel) (.inr (.hash bytes))
      | serverSend keyId plaintext => exact Coupled.query (Rr := CoreRel) (.inr (.serverSend keyId plaintext))
      | serverRaw raw => exact Coupled.query (Rr := CoreRel) (.inr (.serverRaw raw))
      | beaconSend owner plaintext => exact Coupled.query (Rr := CoreRel) (.inr (.beaconSend owner plaintext))
      | beaconRaw owner raw => exact Coupled.query (Rr := CoreRel) (.inr (.beaconRaw owner raw))

/-- Native ledger callbacks retain their real test/fresh draws and both transcripts under success-only raw replies. -/
theorem handler_couple (crypto : Pqxdh.Crypto) (codec : Codec Reader Response) (serverKid : U64)
    (bounds : FreshBounds) (query : FullSpec.Domain) (first second : State) (related : StateRel first second) :
    Coupled CoreRel (fun left right => FullRel query left.1 right.1 ∧ StateRel left.2 right.2)
      ((RegistrationNativeLedger.handler crypto codec serverKid bounds query).run first)
      ((RegistrationNativeLedger.handler crypto codec serverKid bounds query).run second) := by
  cases query with
  | inl core =>
      simp only [RegistrationNativeLedger.query_forward]
      exact (Coupled.query (Rr := CoreRel) core).map fun reply₁ reply₂ replies =>
        ⟨replies, record_related first second related (.inl core) reply₁ reply₂ replies⟩
  | inr secrecy =>
      simp only [RegistrationNativeLedger.query_secrecy]
      exact (legacy_couple (PqxdhRecordLiftHiding.ledger_couple crypto codec serverKid bounds
        (.inr secrecy) first.ledger second.ledger related.1)).map fun left right replies => by
          refine ⟨replies.1, replies.2, ?_⟩
          have equal : left.1 = right.1 := replies.1
          simp only [List.map_append, List.map_cons, List.map_nil, related.2, equal]

private theorem observe_couple (query : (ModeSpec .P).Domain) :
    Coupled FullRel (EqRel query) (RegistrationNativeInterface.observeFull query)
      (RegistrationNativeInterface.observeFull query) := by
  simp only [RegistrationNativeInterface.observe_project]
  exact (Coupled.query (Rr := FullRel) query).map fun first second related =>
    project_equal query first second related

/-- The actual native Mode P adversary receives equal observations while all raw plaintexts remain in the private analysis ledger. -/
theorem adversary_couple (work : OracleComp (ModeSpec .P) Value) :
    Coupled FullRel Eq (asModeO .P work) (asModeO .P work) :=
  Coupled.simulateQ (Rr := EqRel) _ _ observe_couple (Coupled.refl work eqRel_eq fun _ => rfl)

/-- Arbitrary adaptive native secrecy programs preserve their original ledger and complete public transcript relation. -/
theorem wrap_couple (crypto : Pqxdh.Crypto) (codec : Codec Reader Response) (serverKid : U64)
    (bounds : FreshBounds) (work : OracleComp (ModeSpec .P) Value) :
    Coupled CoreRel (fun first second => first.1 = second.1 ∧ StateRel first.2 second.2)
      (RegistrationNativeLedger.wrap crypto codec serverKid bounds (asModeO .P work))
      (RegistrationNativeLedger.wrap crypto codec serverKid bounds (asModeO .P work)) :=
  Coupled.simulateQ_run _ _ StateRel (handler_couple crypto codec serverKid bounds)
    (adversary_couple work) _ _ ⟨⟨rfl, rfl, rfl⟩, rfl⟩

/-- The full original native APP event ignores the hidden raw plaintexts, with its broad verified-key designation unchanged. -/
theorem app_event (crypto : Pqxdh.Crypto) (wire : RegistrationNativeWire.Wire) (serverKid : U64)
    (budget : PqxdhDeploymentInterface.Budget) (claim : Value → Option (Nat × Pqxdh.Bytes)) (value : Value)
    (first second : State) (related : StateRel first second) (native₁ native₂ : NativeState) :
    RegistrationNativeEvents.ceAppEvent crypto wire serverKid budget claim (value, (first, native₁)) =
      RegistrationNativeEvents.ceAppEvent crypto wire serverKid budget claim (value, (second, native₂)) := by
  unfold RegistrationNativeEvents.ceAppEvent RegistrationNativeEvents.CEAppWin
  rw [related.1.2.2,
    (PqxdhDeploymentTranscript.designate_view crypto (RegistrationNativeWire.ledgerCodec wire)
      serverKid first.ledger.transcript second.ledger.transcript related.1.1).2 budget]

end BeaconcryptCore.Computational.RegistrationNativeLedgerHiding

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeLedgerHiding.view_equal' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeLedgerHiding.view_equal
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeLedgerHiding.record_related' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeLedgerHiding.record_related
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeLedgerHiding.legacy_couple' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeLedgerHiding.legacy_couple
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeLedgerHiding.handler_couple' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeLedgerHiding.handler_couple
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeLedgerHiding.adversary_couple' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeLedgerHiding.adversary_couple
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeLedgerHiding.wrap_couple' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeLedgerHiding.wrap_couple
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeLedgerHiding.app_event' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeLedgerHiding.app_event
