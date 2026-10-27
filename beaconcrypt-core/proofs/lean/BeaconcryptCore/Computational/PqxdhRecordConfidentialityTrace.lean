import BeaconcryptCore.Computational.PqxdhRecordConfidentialityChallenge

/-! Actual request and reply provenance for the later-record challenge wrapper. This is an inductive observation of the unchanged interpreted program, retaining the full source state at every request; it introduces no alternate source scheduler. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhRecordConfidentialityTrace
open PqxdhFirstRecordConfidentiality (ConfPostSpec AdvSpec)
open PqxdhRecordConfidentialityChallenge
open RawCtxProtocolReveals (Owner)
variable {ι A Result : Type} {extra : OracleSpec ι} {S B : Nat}

/-- Every node is the literal wrapper request evaluated by the original source interpreter, before its actual adaptive continuation. -/
inductive Trace (impl : QueryImpl (ConfPostSpec extra S B) (StateT A ProbComp))
    (owner : Owner S B) (number : Std.U64) (bit : Bool) :
    OracleComp (AdvSpec extra S B) Result → State → A → ((Result × State) × A) → Prop where
  | pure (value : Result) (before : State) (ambient : A) :
      Trace impl owner number bit (pure value) before ambient ((value, before), ambient)
  | query (query : (AdvSpec extra S B).Domain)
      (next : (AdvSpec extra S B).Range query → OracleComp (AdvSpec extra S B) Result)
      (before : State) (ambient : A) (step : ((AdvSpec extra S B).Range query × State) × A)
      (result : (Result × State) × A)
      (actual : step ∈ support ((simulateQ impl ((handler owner number bit query).run before)).run ambient))
      (tail : Trace impl owner number bit (next step.1.1) step.1.2 step.2 result) :
      Trace impl owner number bit ((AdvSpec extra S B).query query >>= next) before ambient result

/-- Every supported complete interpreted wrapper run has this exact source-state trace, including rejected and failed sends. -/
theorem run_trace (impl : QueryImpl (ConfPostSpec extra S B) (StateT A ProbComp))
    (owner : Owner S B) (number : Std.U64) (bit : Bool) (client : OracleComp (AdvSpec extra S B) Result)
    (before : State) (ambient : A) (result : (Result × State) × A)
    (supported : result ∈ support ((simulateQ impl ((simulateQ (handler owner number bit) client).run before)).run ambient)) :
    Trace impl owner number bit client before ambient result := by
  induction client using OracleComp.inductionOn generalizing before ambient with
  | pure value =>
    simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at supported
    subst result
    exact .pure value before ambient
  | query_bind query next ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at supported
    obtain ⟨step, actual, later⟩ := supported
    exact .query query next before ambient step result actual (ih step.1.1 step.1.2 step.2 later)

/-- Interpreting source requests preserves the all-reply wrapper footprint; complete source state is retained independently of this public bookkeeping. -/
theorem interpreted_kept (impl : QueryImpl (ConfPostSpec extra S B) (StateT A ProbComp))
    (owner : Owner S B) (number : Std.U64) (bit : Bool) (query : (AdvSpec extra S B).Domain)
    (before : State) (ambient : A) (result : ((AdvSpec extra S B).Range query × State) × A)
    (supported : result ∈ support ((simulateQ impl ((handler owner number bit query).run before)).run ambient)) :
    Kept before result.1.2 := by
  apply query_kept owner number bit query before result.1
  apply support_simulateQ_run'_subset impl ((handler owner number bit query).run before) ambient
  simp only [StateT.run'_eq, support_map, Set.mem_image]
  exact ⟨result, supported, rfl⟩

/-- The exact full source trace retains the chosen challenge and cannot clear an earlier competing publication. -/
theorem Trace.kept {impl : QueryImpl (ConfPostSpec extra S B) (StateT A ProbComp)}
    {owner : Owner S B} {number : Std.U64} {bit : Bool} {client : OracleComp (AdvSpec extra S B) Result}
    {before : State} {ambient : A} {result : (Result × State) × A}
    (traced : Trace impl owner number bit client before ambient result) : Kept before result.1.2 := by
  induction traced with
  | pure value before ambient => exact ⟨fun _ => ⟨rfl, rfl⟩, id⟩
  | query query next before ambient step result actual tail ih =>
    exact (interpreted_kept impl owner number bit query before ambient step actual).trans ih

/-- An actual finite prefix of the same adaptive client, retaining the entire next program and both wrapper and source states. -/
inductive Reaches (impl : QueryImpl (ConfPostSpec extra S B) (StateT A ProbComp))
    (owner : Owner S B) (number : Std.U64) (bit : Bool) :
    OracleComp (AdvSpec extra S B) Result → State → A → OracleComp (AdvSpec extra S B) Result → State → A → Prop where
  | here (client : OracleComp (AdvSpec extra S B) Result) (before : State) (ambient : A) :
      Reaches impl owner number bit client before ambient client before ambient
  | later (query : (AdvSpec extra S B).Domain)
      (next : (AdvSpec extra S B).Range query → OracleComp (AdvSpec extra S B) Result)
      (before : State) (ambient : A) (step : ((AdvSpec extra S B).Range query × State) × A)
      (rest : OracleComp (AdvSpec extra S B) Result) (current : State) (source : A)
      (actual : step ∈ support ((simulateQ impl ((handler owner number bit query).run before)).run ambient))
      (tail : Reaches impl owner number bit (next step.1.1) step.1.2 step.2 rest current source) :
      Reaches impl owner number bit ((AdvSpec extra S B).query query >>= next) before ambient rest current source

/-- The actual source send and complete adaptive suffix at the accepted challenge. Neither a query from another execution nor a reconstructed ciphertext can supply this witness. -/
def Origin (impl : QueryImpl (ConfPostSpec extra S B) (StateT A ProbComp))
    (owner : Owner S B) (number : Std.U64) (bit : Bool)
    (client : OracleComp (AdvSpec extra S B) Result) (before : State) (ambient : A) (result : (Result × State) × A) : Prop :=
  ∃ (left right : Pqxdh.Bytes) (next : Option RawCtxSourceSend.Encrypted → OracleComp (AdvSpec extra S B) Result)
      (current : State) (source after : A) (record : RawCtxSourceSend.Encrypted),
    Reaches impl owner number bit client before ambient ((AdvSpec extra S B).query (.inr (left, right)) >>= next) current source ∧
      current.pair = none ∧ left.length = right.length ∧ current.otherTarget = false ∧
      (some record, after) ∈ support ((simulateQ impl (send owner (if bit then right else left))).run source) ∧
      Trace impl owner number bit (next (some record))
        { current with pair := some (left, right), reply := some (some record) } after result ∧
      record.sequence = number

/-- A true final target event after starting without a challenge has an actual reached challenge send and its unchanged complete source continuation. -/
theorem Trace.origin {impl : QueryImpl (ConfPostSpec extra S B) (StateT A ProbComp)}
    {owner : Owner S B} {number : Std.U64} {bit : Bool} {client : OracleComp (AdvSpec extra S B) Result}
    {before : State} {ambient : A} {result : (Result × State) × A}
    (traced : Trace impl owner number bit client before ambient result)
    (unused : before.pair = none) (target : Target number result.1.2) :
    Origin impl owner number bit client before ambient result := by
  induction traced with
  | pure value before ambient =>
    simp only [Target, unused, Option.isSome_none, Bool.false_eq_true, false_and] at target
  | query query next before ambient step result actual tail ih =>
    have extend : Origin impl owner number bit (next step.1.1) step.1.2 step.2 result →
        Origin impl owner number bit ((AdvSpec extra S B).query query >>= next) before ambient result := by
      rintro ⟨left, right, continuation, current, source, after, record, reached, remaining⟩
      exact ⟨left, right, continuation, current, source, after, record,
        .later query next before ambient step _ current source actual reached, remaining⟩
    rcases query with request | ⟨left, right⟩
    · apply extend
      apply ih _ target
      have forwarded : (handler (extra := extra) owner number bit (.inl request)).run before =
          (fun reply => (screen before request reply, observe owner number before request reply)) <$>
            ((ConfPostSpec extra S B).query request : OracleComp (ConfPostSpec extra S B) _) := by
        simp only [handler, StateT.run, bind_pure_comp]
      rw [forwarded, simulateQ_map, StateT.run_map, support_map] at actual
      obtain ⟨reply, _, rfl⟩ := actual
      exact unused
    · by_cases equal : left.length = right.length
      · rw [challenge_step owner number bit left right equal before unused] at actual
        simp only [simulateQ_map, StateT.run_map, support_map, Set.mem_image] at actual
        obtain ⟨⟨reply, after⟩, sent, rfl⟩ := actual
        have kept := tail.kept.1 (by rfl)
        obtain ⟨record, returned, sequence⟩ := target.2.1
        rw [kept.2] at returned
        have same : reply = some record := Option.some.inj returned
        subst reply
        exact ⟨left, right, next, before, ambient, after, record, .here _ before ambient,
          unused, equal, tail.kept.2 target.2.2, sent, tail, sequence⟩
      · have refused : (handler (extra := extra) owner number bit (.inr (left, right))).run before =
            Pure.pure ((none : Option RawCtxSourceSend.Encrypted), before) := by
          simp only [handler, StateT.run, equal, ne_eq, not_false_eq_true, or_true, ite_true]
        rw [refused, simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at actual
        subst step
        exact extend (ih unused target)

/-- At every ordinary forwarded request whose exact continuation reaches the target event, its actual source reply did not publish the selected owner/sequence. Raw reply screening is retained separately from the source reply used for this check. -/
theorem forwarded_excluded (impl : QueryImpl (ConfPostSpec extra S B) (StateT A ProbComp))
    (owner : Owner S B) (number : Std.U64) (bit : Bool) (query : (ConfPostSpec extra S B).Domain)
    (next : (ConfPostSpec extra S B).Range query → OracleComp (AdvSpec extra S B) Result)
    (before : State) (ambient : A) (step : ((ConfPostSpec extra S B).Range query × State) × A)
    (result : (Result × State) × A)
    (actual : step ∈ support ((simulateQ impl ((handler owner number bit (.inl query)).run before)).run ambient))
    (tail : Trace impl owner number bit (next step.1.1) step.1.2 step.2 result)
    (target : Target number result.1.2) :
    ∃ reply, (reply, step.2) ∈ support ((impl query).run ambient) ∧
      step.1 = (screen before query reply, observe owner number before query reply) ∧
      (owner, number) ∉ publications query reply := by
  have forwarded : (handler (extra := extra) owner number bit (.inl query)).run before =
      (fun reply => (screen before query reply, observe owner number before query reply)) <$>
        ((ConfPostSpec extra S B).query query : OracleComp (ConfPostSpec extra S B) _) := by
    simp only [handler, StateT.run, bind_pure_comp]
  rw [forwarded, simulateQ_map, simulateQ_spec_query, StateT.run_map, support_map] at actual
  obtain ⟨⟨reply, after⟩, returned, rfl⟩ := actual
  exact ⟨reply, returned, rfl, ((observe_target owner number before query reply).mp (tail.kept.2 target.2.2)).2⟩

/-- The literal initial wrapper and any actually supported final target run supply the complete original challenge provenance, with no origin or source-success premise. -/
theorem run_origin (impl : QueryImpl (ConfPostSpec extra S B) (StateT A ProbComp))
    (owner : Owner S B) (number : Std.U64) (bit : Bool) (client : OracleComp (AdvSpec extra S B) Result)
    (ambient : A) (result : (Result × State) × A)
    (supported : result ∈ support ((simulateQ impl ((simulateQ (handler owner number bit) client).run initial)).run ambient))
    (target : Target number result.1.2) : Origin impl owner number bit client initial ambient result := by
  exact (run_trace impl owner number bit client initial ambient result supported).origin rfl target

/-- Even after the wrapper returns only its original Boolean, every true source result retains a witness of the actual challenge send and full suffix with the same final source state. -/
theorem post_origin {Selection : Type} (impl : QueryImpl (ConfPostSpec extra S B) (StateT A ProbComp))
    (adversary : Selection → RustM (Option PqxdhServerRegistrationPublication.Response) → OracleComp (AdvSpec extra S B) Bool)
    (owner : Owner S B) (number : Std.U64) (bit : Bool) (selection : Selection)
    (reply : RustM (Option PqxdhServerRegistrationPublication.Response)) (ambient : A) (result : Bool × A)
    (supported : result ∈ support ((simulateQ impl (post adversary owner number bit selection reply)).run ambient))
    (accepted : result.1 = true) :
    ∃ current, Origin impl owner number bit (adversary selection reply) initial ambient ((true, current), result.2) ∧
      Target number current := by
  simp only [post, simulateQ_map, StateT.run_map, support_map, Set.mem_image] at supported
  obtain ⟨⟨⟨guess, current⟩, after⟩, reached, rfl⟩ := supported
  have facts : guess = true ∧ Target number current := by
    simpa only [output, Bool.and_eq_true, decide_eq_true_eq] using accepted
  rcases facts with ⟨rfl, target⟩
  exact ⟨current, run_origin impl owner number bit (adversary selection reply) ambient ((true, current), after) reached target, target⟩

end BeaconcryptCore.Computational.PqxdhRecordConfidentialityTrace

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordConfidentialityTrace.run_trace' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordConfidentialityTrace.run_trace
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordConfidentialityTrace.interpreted_kept' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordConfidentialityTrace.interpreted_kept
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordConfidentialityTrace.Trace.kept' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordConfidentialityTrace.Trace.kept
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordConfidentialityTrace.Trace.origin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordConfidentialityTrace.Trace.origin
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordConfidentialityTrace.forwarded_excluded' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordConfidentialityTrace.forwarded_excluded
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordConfidentialityTrace.run_origin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordConfidentialityTrace.run_origin
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordConfidentialityTrace.post_origin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordConfidentialityTrace.post_origin
