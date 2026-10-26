import BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality

/-! The existing left-or-right interface at a reached record position in either sending direction. Every protocol request still uses the original Post interface; the wrapper tracks actual returned publications rather than assuming a private counter or selected-key condition. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhRecordConfidentialityChallenge
open PqxdhFirstRecordConfidentiality (ConfPostSpec AdvSpec)
open RawCtxProtocolReveals (Owner)
variable {ι : Type} {extra : OracleSpec ι} {S B : Nat}

/-- The literal existing send request, retaining the requested Server peer or Beacon object. -/
def sendRequest (owner : Owner S B) (plaintext : Pqxdh.Bytes) : (ConfPostSpec extra S B).Domain :=
  match owner with
  | .server index peer => .inl (.inl (.inl (.inl ⟨index, .inl (plaintext, peer)⟩)))
  | .beacon index => .inl (.inl (.inl (.inr (.inl ⟨index, .inl plaintext⟩))))

/-- Both send variants return the unchanged optional source encrypted record. -/
def send (owner : Owner S B) (plaintext : Pqxdh.Bytes) :
    OracleComp (ConfPostSpec extra S B) (Option RawCtxSourceSend.Encrypted) :=
  match owner with
  | .server index peer => (ConfPostSpec extra S B).query (sendRequest (.server index peer) plaintext)
  | .beacon index => (ConfPostSpec extra S B).query (sendRequest (.beacon index) plaintext)

/-- Public challenge bookkeeping; it contains neither a chain value nor a selected record key. -/
structure State where
  pair : Option (Pqxdh.Bytes × Pqxdh.Bytes)
  reply : Option (Option RawCtxSourceSend.Encrypted)
  otherTarget : Bool

def initial : State := ⟨none, none, false⟩

/-- Only actual successful send API replies contribute a publication; selectors, reveals and finish replies are unchanged. -/
def publications : (request : (ConfPostSpec extra S B).Domain) →
    (ConfPostSpec extra S B).Range request → List (RawCtxPublishedRecords.Publication S B)
  | .inl (.inl request), reply => RawCtxPublishedRecords.record request reply
  | _, _ => []

noncomputable def observe (owner : Owner S B) (number : Std.U64) (state : State)
    (request : (ConfPostSpec extra S B).Domain) (reply : (ConfPostSpec extra S B).Range request) : State :=
  { state with otherTarget := state.otherTarget || decide ((owner, number) ∈ publications request reply) }

/-- The same explicit raw-reply restriction as the first-record experiment; optional Beacon finish replies are still returned unchanged. -/
def screen (state : State) (request : (ConfPostSpec extra S B).Domain)
    (reply : (ConfPostSpec extra S B).Range request) : (ConfPostSpec extra S B).Range request :=
  PqxdhFirstRecordConfidentiality.screen { PqxdhFirstRecordConfidentiality.confInitial with pair := state.pair } request reply

/-- A single equal-length challenge may be requested after any earlier source work. No source send is suppressed based on a private counter or selected-material label. -/
noncomputable def handler (owner : Owner S B) (number : Std.U64) (bit : Bool) :
    QueryImpl (AdvSpec extra S B) (StateT State (OracleComp (ConfPostSpec extra S B))) :=
  fun query state => match query with
  | .inl request => do
      let reply ← (ConfPostSpec extra S B).query request
      pure (screen state request reply, observe owner number state request reply)
  | .inr (left, right) =>
      if state.pair.isSome ∨ left.length ≠ right.length then pure (none, state)
      else do
        let reply ← send owner (if bit then right else left)
        pure (reply, { state with pair := some (left, right), reply := some reply })

/-- The challenge itself returned the target sequence, and no ordinary send returned that owner/sequence. Source lineage freshness remains the separate unchanged protocol event. -/
def Target (number : Std.U64) (state : State) : Prop :=
  state.pair.isSome ∧ (∃ sent, state.reply = some (some sent) ∧ sent.sequence = number) ∧ state.otherTarget = false

noncomputable def output (number : Std.U64) (result : Bool × State) : Bool :=
  by classical exact result.1 && decide (Target number result.2)

noncomputable def post {Selection : Type}
    (adversary : Selection → RustM (Option PqxdhServerRegistrationPublication.Response) → OracleComp (AdvSpec extra S B) Bool)
    (owner : Owner S B) (number : Std.U64) (bit : Bool) :
    Selection → RustM (Option PqxdhServerRegistrationPublication.Response) → OracleComp (ConfPostSpec extra S B) Bool :=
  fun selection reply => output number <$> (simulateQ (handler owner number bit) (adversary selection reply)).run initial

/-- Each challenge is charged to whichever of its two literal sends the source predicate counts. -/
def liftPred (owner : Owner S B) (predicate : (ConfPostSpec extra S B).Domain → Prop) : (AdvSpec extra S B).Domain → Prop
  | .inl query => predicate query
  | .inr (left, right) => predicate (sendRequest owner left) ∨ predicate (sendRequest owner right)

noncomputable instance (owner : Owner S B) (predicate : (ConfPostSpec extra S B).Domain → Prop) :
    DecidablePred (liftPred owner predicate) := fun _ => Classical.propDecidable _

set_option backward.isDefEq.respectTransparency false in
/-- The original send retains its exact source-query classification in either direction. -/
theorem send_bound (owner : Owner S B) (plaintext : Pqxdh.Bytes)
    (predicate : (ConfPostSpec extra S B).Domain → Prop) [DecidablePred predicate] :
    (send (extra := extra) owner plaintext).IsQueryBoundP predicate (if predicate (sendRequest owner plaintext) then 1 else 0) := by
  cases owner <;> simp only [send, sendRequest]
  all_goals rw [isQueryBoundP_query_iff]
  all_goals intro counted; simp only [counted, ite_true, Nat.zero_lt_succ]

/-- Every adversarial Post query retains its original allowance; each attempted challenge contributes at most its one literal send, in either direction and at any reached sequence. -/
theorem query_bound {Result : Type} (owner : Owner S B) (number : Std.U64) (bit : Bool)
    (predicate : (ConfPostSpec extra S B).Domain → Prop) [DecidablePred predicate]
    (adversary : OracleComp (AdvSpec extra S B) Result) (budget : Nat)
    (bounded : adversary.IsQueryBoundP (liftPred owner predicate) budget) (state : State) :
    ((simulateQ (handler owner number bit) adversary).run state).IsQueryBoundP predicate budget := by
  classical
  refine IsQueryBoundP.simulateQ_run_StateT_of_step bounded ?_ state
  intro query current
  rcases query with request | ⟨left, right⟩
  · simp only [handler, liftPred, StateT.run]
    rw [isQueryBoundP_query_bind_iff]
    by_cases counted : predicate request <;> simp [counted]
  · simp only [handler, StateT.run]
    split
    · trivial
    · simp only [bind_pure_comp, isQueryBoundP_map_iff]
      apply (send_bound owner (if bit then right else left) predicate).mono
      cases bit <;> simp only [Bool.false_eq_true, ite_false, ite_true, liftPred] <;> split_ifs <;> simp_all

/-- The complete post wrapper pays the same all-reply predicate allowance, including earlier traffic, refused challenges and unsuccessful sends. -/
theorem post_bound {Selection : Type}
    (adversary : Selection → RustM (Option PqxdhServerRegistrationPublication.Response) → OracleComp (AdvSpec extra S B) Bool)
    (owner : Owner S B) (number : Std.U64) (bit : Bool)
    (predicate : (ConfPostSpec extra S B).Domain → Prop) [DecidablePred predicate] (budget : Nat)
    (bounded : ∀ selection reply, (adversary selection reply).IsQueryBoundP (liftPred owner predicate) budget)
    (selection : Selection) (reply : RustM (Option PqxdhServerRegistrationPublication.Response)) :
    (post adversary owner number bit selection reply).IsQueryBoundP predicate budget := by
  simpa only [post, isQueryBoundP_map_iff] using
    query_bound owner number bit predicate (adversary selection reply) budget (bounded selection reply) initial

/-- At any reached wrapper state before its accepted challenge, equal-length alternatives run the literal source send and retain its exact optional reply and previous publication flag. -/
theorem challenge_step (owner : Owner S B) (number : Std.U64) (bit : Bool)
    (left right : Pqxdh.Bytes) (equal : left.length = right.length) (state : State) (unused : state.pair = none) :
    ((handler (extra := extra) owner number bit (.inr (left, right))).run state) =
      (fun reply => (reply, { state with pair := some (left, right), reply := some reply })) <$>
        send owner (if bit then right else left) := by
  simp only [handler, StateT.run, unused, Option.isSome_none, Bool.false_eq_true, equal, ne_eq, not_true_eq_false,
    or_self, ite_false, bind_pure_comp]

/-- The public competing-publication flag is exact and sticky; no selected owner/sequence returned by an ordinary send can survive the wrapper's final target event. -/
theorem observe_target (owner : Owner S B) (number : Std.U64) (state : State)
    (query : (ConfPostSpec extra S B).Domain) (reply : (ConfPostSpec extra S B).Range query) :
    (observe owner number state query reply).otherTarget = false ↔
      state.otherTarget = false ∧ (owner, number) ∉ publications query reply := by
  classical
  simp only [observe, Bool.or_eq_false_iff, decide_eq_false_iff_not]

/-- Once chosen, the challenge pair and its actual optional reply cannot be overwritten. Competing-publication exclusion is preserved backwards. -/
def Kept (before after : State) : Prop :=
  (before.pair.isSome → after.pair = before.pair ∧ after.reply = before.reply) ∧
    (after.otherTarget = false → before.otherTarget = false)

/-- The exact challenge and publication properties compose through any number of source operations. -/
theorem Kept.trans {first middle last : State} (left : Kept first middle) (right : Kept middle last) :
    Kept first last := by
  refine ⟨fun chosen => ?_, fun clear => left.2 (right.2 clear)⟩
  have a := left.1 chosen
  have b := right.1 (by simpa only [a.1] using chosen)
  exact ⟨b.1.trans a.1, b.2.trans a.2⟩

/-- Each original wrapper request preserves the challenge record and the sticky publication flag, on every possible source reply. -/
theorem query_kept (owner : Owner S B) (number : Std.U64) (bit : Bool)
    (query : (AdvSpec extra S B).Domain) (before : State)
    (result : (AdvSpec extra S B).Range query × State)
    (supported : result ∈ support ((handler owner number bit query).run before)) :
    Kept before result.2 := by
  rcases query with request | ⟨left, right⟩
  · simp only [handler, StateT.run, bind_pure_comp, support_map, Set.mem_image] at supported
    obtain ⟨reply, _, rfl⟩ := supported
    exact ⟨fun _ => ⟨rfl, rfl⟩, fun clear => ((observe_target owner number before request reply).mp clear).1⟩
  · simp only [handler, StateT.run] at supported
    split at supported
    · simp only [mem_support_pure_iff] at supported
      subst result
      exact ⟨fun _ => ⟨rfl, rfl⟩, id⟩
    · rename_i accepted
      simp only [bind_pure_comp, support_map, Set.mem_image] at supported
      obtain ⟨reply, _, rfl⟩ := supported
      exact ⟨fun earlier => False.elim (accepted (Or.inl earlier)), id⟩

/-- The full adaptive source-query syntax preserves write-once challenge information and every earlier competing-publication flag on all reply paths. -/
theorem run_kept {Result : Type} (owner : Owner S B) (number : Std.U64) (bit : Bool)
    (adversary : OracleComp (AdvSpec extra S B) Result) (before : State) (result : Result × State)
    (supported : result ∈ support ((simulateQ (handler owner number bit) adversary).run before)) :
    Kept before result.2 := by
  induction adversary using OracleComp.inductionOn generalizing before with
  | pure value =>
    simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at supported
    subst result
    exact ⟨fun _ => ⟨rfl, rfl⟩, id⟩
  | query_bind query next ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at supported
    obtain ⟨step, actual, later⟩ := supported
    exact (query_kept owner number bit query before step actual).trans (ih step.1 step.2 later)

/-- Test the sequence of an actually returned typed record, retaining ordinary writer failure. -/
def atNumber (number : Std.U64) (reply : Option RawCtxSourceSend.Encrypted) : Bool :=
  match reply with | none => false | some record => decide (record.sequence = number)

set_option backward.isDefEq.respectTransparency false in
/-- The wrapper admits the literal single challenge in either direction; the final predicate is precisely the returned sequence test and the adversary's guess. -/
theorem single_output (owner : Owner S B) (number : Std.U64) (bit : Bool)
    (left right : Pqxdh.Bytes) (equal : left.length = right.length)
    (guess : Option RawCtxSourceSend.Encrypted → Bool) :
    output number <$> (simulateQ (handler owner number bit)
      (PqxdhFirstRecordConfidentiality.singleChallenge (extra := extra) (S := S) (B := B) left right guess)).run initial =
      (fun reply => guess reply && atNumber number reply) <$> send owner (if bit then right else left) := by
  simp only [PqxdhFirstRecordConfidentiality.singleChallenge, simulateQ_map, StateT.run_map, Functor.map_map, simulateQ_query]
  change (fun value => output number (guess value.1, value.2)) <$>
    (handler (extra := extra) owner number bit (.inr (left, right))).run initial = _
  rw [challenge_step owner number bit left right equal initial rfl]
  simp only [Functor.map_map]
  congr 1
  funext reply
  cases reply <;> simp [output, Target, atNumber, initial]

section SourceBudgets
open PqxdhPhase2GeneratedDriver PqxdhPrivateKemSource PqxdhStatefulPhase1EufCma PqxdhKemIndCca
variable {κ M P I K X Response A KemSK : Type} {baseSpec : OracleSpec κ} {T N : Nat}
variable {setup : StatefulPhase1Setup baseSpec}
    (env : PqxdhAuthenticatedRootExperiment.Environment setup M P I K X Response A T N)
    (baseImpl : QueryImpl baseSpec ProbComp) (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (program : Program baseSpec setup.Context T (N + 1))

/-- The adversary pays the original scheduler's complete per-kind budget. A challenge is counted as its literal Server or Beacon send; this does not grant signing, creation or other capabilities absent from the original enclosing experiment. -/
def AdvBounded (owner : Owner T (N + 1))
    (adversary : program.Selection → RustM (Option PqxdhServerRegistrationPublication.Response) →
      OracleComp (AdvSpec (SelectorSpec baseSpec) T (N + 1)) Bool)
    (budget : PqxdhPhase2SourceSchedulerBounds.Budget) : Prop :=
  ∀ selection reply kind, (adversary selection reply).IsQueryBoundP
    (liftPred owner (fun query => PqxdhPhase2SourceSchedulerBounds.classify (baseSpec := baseSpec) query = kind)) (budget kind)

/-- Both literal challenge worlds discharge every original Post budget coordinate from the adversary's own all-reply query caps, with no source-state or successful-target premise. -/
theorem post_bounded (owner : Owner T (N + 1)) (number : Std.U64)
    (adversary : program.Selection → RustM (Option PqxdhServerRegistrationPublication.Response) →
      OracleComp (AdvSpec (SelectorSpec baseSpec) T (N + 1)) Bool)
    (budget : PqxdhPhase2SourceSchedulerBounds.Budget) (bounded : AdvBounded program owner adversary budget) (bit : Bool)
    (selection : program.Selection) (reply : RustM (Option PqxdhServerRegistrationPublication.Response)) :
    PqxdhPhase2SourceSchedulerBounds.Bounded (post adversary owner number bit selection reply) budget := by
  intro kind
  exact post_bound adversary owner number bit _ (budget kind) (fun choice response => bounded choice response kind) selection reply

/-- The enclosing source resource certificate is preserved literally, replacing only its Post with the proven challenge wrapper and its actual per-kind adversary budget. Existing no-sign/no-create prefix restrictions remain unchanged. -/
def certificate {original : PqxdhAuthenticatedRootExperiment.Post (baseSpec := baseSpec) program.Selection T (N + 1)}
    (c : PqxdhAuthenticatedRootBudgets.Certificate env baseImpl kem program original)
    (owner : Owner T (N + 1)) (number : Std.U64)
    (adversary : program.Selection → RustM (Option PqxdhServerRegistrationPublication.Response) →
      OracleComp (AdvSpec (SelectorSpec baseSpec) T (N + 1)) Bool)
    (budget : PqxdhPhase2SourceSchedulerBounds.Budget) (bounded : AdvBounded program owner adversary budget) (bit : Bool) :
    PqxdhAuthenticatedRootBudgets.Certificate env baseImpl kem program (post adversary owner number bit) :=
  { c with postBudget := budget, postBound := post_bounded program owner number adversary budget bounded bit }

end SourceBudgets
end BeaconcryptCore.Computational.PqxdhRecordConfidentialityChallenge

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordConfidentialityChallenge.send_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordConfidentialityChallenge.send_bound
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordConfidentialityChallenge.query_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordConfidentialityChallenge.query_bound
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordConfidentialityChallenge.post_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordConfidentialityChallenge.post_bound
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordConfidentialityChallenge.challenge_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordConfidentialityChallenge.challenge_step
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordConfidentialityChallenge.observe_target' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordConfidentialityChallenge.observe_target
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordConfidentialityChallenge.Kept.trans' does not depend on any axioms -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordConfidentialityChallenge.Kept.trans
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordConfidentialityChallenge.query_kept' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordConfidentialityChallenge.query_kept
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordConfidentialityChallenge.run_kept' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordConfidentialityChallenge.run_kept
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordConfidentialityChallenge.single_output' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordConfidentialityChallenge.single_output
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordConfidentialityChallenge.post_bounded' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordConfidentialityChallenge.post_bounded
