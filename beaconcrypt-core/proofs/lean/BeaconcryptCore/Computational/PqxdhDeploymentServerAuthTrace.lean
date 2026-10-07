-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhDeploymentServerAuthFreeze
import BeaconcryptCore.Computational.PqxdhDeploymentTargetRange

/-! The registration view of the deployment transcript is the registration view of the compiled program's source14 journal (CE-8). The compiler forwards every create whose pin parses, bundle, accept, build and finish to exactly one source14 query of the same kind with the same reply, answers a create with a pin of the wrong width without a query, and issues no create, bundle, accept, build or finish for any other command (`step_regs`, from the existing per-step cost lemmas). Hence, for every reply, the registration view of the final transcript of the compiled program equals the registration view of its full source14 journal (`compiled_regs`); this is a fact of the program alone. No security claim is made here. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhDeploymentServerAuthTrace
open PqxdhServerAuthExperiment
open PqxdhRegistrationJointRevealSchedule (Spec)
open PqxdhDeploymentInterface (Entry FullSpec ModeSpec Mode FreshBounds queryClass asModeO parsePin)
open PqxdhDeploymentSecrecy (Ledger ledgerImpl)
open PqxdhDeploymentCompile (Local compileImpl)
open PqxdhDeploymentCompileSecrecy (compileFull wrapCost)
open PqxdhDeploymentCompileBudget (commandKind cost unit)
open PqxdhRegistrationJointRevealCosts (SourceKind sourceKind)
open PqxdhDeploymentServerAuthEvent (SourceEntry Reg regOfEntry regsOf regOfSource regsOfSource)
open PqxdhDeploymentServerAuthEmbed (freezeImpl dflt)
open PqxdhDeploymentServerAuthFreeze (journal)
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response A X Result : Type}

/-- The full source14 journal from a starting journal. -/
def journalFrom (program : OracleComp (Spec KemSK) Result) (start : List (SourceEntry KemSK)) :
    OracleComp (Spec KemSK) (Result × List (SourceEntry KemSK)) :=
  (simulateQ (freezeImpl dflt (fun _ => False)) program).run start

/-- A journaled query followed by a journaled continuation. -/
theorem journalFrom_query_bind (query : (Spec KemSK).Domain) (next : (Spec KemSK).Range query → OracleComp (Spec KemSK) Result)
    (start : List (SourceEntry KemSK)) :
    journalFrom (((Spec KemSK).query query : OracleComp (Spec KemSK) _) >>= next) start =
      ((Spec KemSK).query query : OracleComp (Spec KemSK) _) >>= fun reply =>
        journalFrom (next reply) (start ++ [⟨query, reply⟩]) := by
  simp only [journalFrom, simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, id_map,
    StateT.run_bind, PqxdhDeploymentServerAuthLocalize.freezeImpl_run, ite_false, bind_map_left]

/-- A journaled bind is the journaled first program followed by the journaled continuation from the reached journal. -/
theorem journalFrom_bind {Next : Type} (program : OracleComp (Spec KemSK) Result) (next : Result → OracleComp (Spec KemSK) Next)
    (start : List (SourceEntry KemSK)) :
    journalFrom (program >>= next) start = journalFrom program start >>= fun reached => journalFrom (next reached.1) reached.2 := by
  simp only [journalFrom, simulateQ_bind, StateT.run_bind]

/-- A journaled map. -/
theorem journalFrom_map {Next : Type} (f : Result → Next) (program : OracleComp (Spec KemSK) Result)
    (start : List (SourceEntry KemSK)) :
    journalFrom (f <$> program) start = (fun outcome => (f outcome.1, outcome.2)) <$> journalFrom program start := by
  simp only [journalFrom, simulateQ_map, StateT.run_map]

/-- A journaled single query. -/
theorem journalFrom_query (query : (Spec KemSK).Domain) (start : List (SourceEntry KemSK)) :
    journalFrom ((Spec KemSK).query query : OracleComp (Spec KemSK) _) start =
      (fun reply => (reply, start ++ [⟨query, reply⟩])) <$> ((Spec KemSK).query query : OracleComp (Spec KemSK) _) := by
  have single := journalFrom_query_bind query (fun reply => (pure reply : OracleComp (Spec KemSK) _)) start
  simp only [bind_pure] at single
  rw [single]
  simp only [journalFrom, simulateQ_pure, StateT.run_pure, bind_pure_comp]

/-- A source14 query of none of the five registration kinds adds no registration entry. -/
theorem regOfSource_other (query : (Spec KemSK).Domain) (reply : (Spec KemSK).Range query)
    (other : ∀ kind : Fin 9, sourceKind (KemSK := KemSK) query = .inl kind → kind ≠ 1 ∧ kind ≠ 2 ∧ kind ≠ 3 ∧ kind ≠ 4 ∧ kind ≠ 5) :
    regOfSource (⟨query, reply⟩ : SourceEntry KemSK) = none := by
  rcases query with (coin | request) | request
  · rfl
  · cases request with
    | create pin keyId => exact absurd rfl (other 1 rfl).1
    | bundle owner => exact absurd rfl (other 2 rfl).2.1
    | accept raw => exact absurd rfl (other 3 rfl).2.2.1
    | build session payload => exact absurd rfl (other 4 rfl).2.2.2.1
    | finish owner raw => exact absurd rfl (other 5 rfl).2.2.2.2
    | hmac key message => rfl
    | hash bytes => rfl
    | reveal keyId => rfl
  · rfl

/-- A program that issues none of the five registration kinds keeps the registration view of its journal. -/
theorem journal_quiet (program : OracleComp (Spec KemSK) Result)
    (quiet : ∀ kind : Fin 9, (kind = 1 ∨ kind = 2 ∨ kind = 3 ∨ kind = 4 ∨ kind = 5) →
      program.IsQueryBoundP (fun query => sourceKind (KemSK := KemSK) query = .inl kind) 0)
    (start : List (SourceEntry KemSK)) (outcome : Result × List (SourceEntry KemSK))
    (reached : outcome ∈ support (journalFrom program start)) : regsOfSource outcome.2 = regsOfSource start := by
  induction program using OracleComp.inductionOn generalizing start with
  | pure value =>
      simp only [journalFrom, simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at reached
      subst reached
      rfl
  | query_bind query next ih =>
      have noKind : ∀ kind : Fin 9, (kind = 1 ∨ kind = 2 ∨ kind = 3 ∨ kind = 4 ∨ kind = 5) →
          sourceKind (KemSK := KemSK) query ≠ .inl kind := fun kind registration found => by
        have bound := quiet kind registration
        rw [isQueryBoundP_query_bind_iff] at bound
        rcases bound.1 with free | impossible
        · exact free found
        · omega
      have allowed : ∀ kind : Fin 9, sourceKind (KemSK := KemSK) query = .inl kind →
          kind ≠ 1 ∧ kind ≠ 2 ∧ kind ≠ 3 ∧ kind ≠ 4 ∧ kind ≠ 5 := fun kind found =>
        ⟨fun same => noKind kind (Or.inl same) found, fun same => noKind kind (Or.inr (Or.inl same)) found,
          fun same => noKind kind (Or.inr (Or.inr (Or.inl same))) found,
          fun same => noKind kind (Or.inr (Or.inr (Or.inr (Or.inl same)))) found,
          fun same => noKind kind (Or.inr (Or.inr (Or.inr (Or.inr same)))) found⟩
      rw [journalFrom_query_bind, mem_support_bind_iff] at reached
      obtain ⟨reply, _, reached⟩ := reached
      have rest : ∀ kind : Fin 9, (kind = 1 ∨ kind = 2 ∨ kind = 3 ∨ kind = 4 ∨ kind = 5) →
          (next reply).IsQueryBoundP (fun query => sourceKind (KemSK := KemSK) query = .inl kind) 0 := by
        intro kind registration
        have bound := quiet kind registration
        rw [isQueryBoundP_query_bind_iff] at bound
        have notThis : ¬ sourceKind (KemSK := KemSK) query = .inl kind := by
          intro found
          obtain ⟨one, two, three, four, five⟩ := allowed kind found
          rcases registration with rfl | rfl | rfl | rfl | rfl <;> contradiction
        simpa [notThis] using bound.2 reply
      rw [ih reply rest _ reached, PqxdhDeploymentServerAuthEvent.regsOfSource_append,
        regOfSource_other query reply allowed, Option.toList_none, List.append_nil]

/-- A journaled outcome is an outcome of the program. -/
theorem journalFrom_support (program : OracleComp (Spec KemSK) Result) (start : List (SourceEntry KemSK))
    (outcome : Result × List (SourceEntry KemSK)) (reached : outcome ∈ support (journalFrom program start)) :
    outcome.1 ∈ support program := by
  rw [← PqxdhDeploymentServerAuthFreeze.journal_erase_from dflt program start, support_map]
  exact Set.mem_image_of_mem _ reached

/-- A compiled secrecy-layer step of a command outside the five registration classes issues no registration query. -/
theorem reg_cost (bounds : FreshBounds) (kind : Fin 9) (registration : kind = 1 ∨ kind = 2 ∨ kind = 3 ∨ kind = 4 ∨ kind = 5)
    (full : Fin 14) (other : full ≠ 1 ∧ full ≠ 2 ∧ full ≠ 3 ∧ full ≠ 4 ∧ full ≠ 5) :
    (∑ core, cost (.inl kind) core * wrapCost bounds core full) = 0 := by
  obtain ⟨one, two, three, four, five⟩ := other
  rcases registration with rfl | rfl | rfl | rfl | rfl <;> fin_cases full <;>
    simp_all [Fin.sum_univ_succ, cost, unit, wrapCost]

/-- A forwarded registration command adds one journal entry with its reply. -/
theorem forward_journal (request : PqxdhRegistrationSchedule.Request) (command : PqxdhDeploymentInterface.Command)
    (reply : PqxdhRegistrationSchedule.QuerySpec request → PqxdhDeploymentInterface.CommandSpec command) (copies : Local)
    (start : List (SourceEntry KemSK))
    (outcome : (PqxdhDeploymentInterface.CommandSpec command × Local) × List (SourceEntry KemSK))
    (reached : outcome ∈ support (journalFrom ((PqxdhDeploymentCompile.forwardLogged (KemSK := KemSK) request command
      reply).run copies) start)) :
    ∃ answer, outcome.1.1 = reply answer ∧ outcome.2 = start ++ [⟨.inl (.inr request), answer⟩] := by
  rw [PqxdhDeploymentKemTransfer.forwardLogged_run, PqxdhDeploymentCompile.forward, journalFrom_map, journalFrom_query,
    Functor.map_map, support_map] at reached
  obtain ⟨answer, _, rfl⟩ := reached
  exact ⟨answer, rfl, rfl⟩

/-- One complete-interface query of none of the five registration classes, through the secrecy layer and the compiler, keeps the registration view of the journal. -/
theorem step_quiet (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (bounds : FreshBounds) (query : PqxdhDeploymentInterface.Query)
    (other : queryClass query ≠ 1 ∧ queryClass query ≠ 2 ∧ queryClass query ≠ 3 ∧ queryClass query ≠ 4 ∧
      queryClass query ≠ 5)
    (ledger : Ledger) (copies : Local) (start : List (SourceEntry KemSK))
    (outcome : ((FullSpec.Range query × Ledger) × Local) × List (SourceEntry KemSK))
    (reached : outcome ∈ support (journalFrom ((simulateQ (compileImpl setup codec route)
      ((ledgerImpl setup.source.crypto codec setup.serverKeyId bounds query).run ledger)).run copies) start)) :
    regsOfSource outcome.2 = regsOfSource start := by
  refine journal_quiet _ (fun kind registration => ?_) start outcome reached
  have bound := FinitePartitionQueryBounds.weighted_bound commandKind (cost (.inl kind))
    (fun core => wrapCost bounds core (queryClass query)) (compileImpl setup codec route)
    (fun request => sourceKind (KemSK := KemSK) request = .inl kind)
    ((ledgerImpl setup.source.crypto codec setup.serverKeyId bounds query).run ledger)
    (fun core => PqxdhDeploymentCompileSecrecy.wrap_step setup.source.crypto codec setup.serverKeyId bounds core query
      ledger)
    (fun request state => PqxdhDeploymentCompileBudget.step_bound setup codec route (.inl kind) request state) copies
  rwa [reg_cost bounds kind registration (queryClass query) other] at bound

/-- One complete-interface query through the secrecy layer and the compiler, journaled: the transcript gains exactly the query with its reply, and the registration view of the journal gains exactly that entry's registration entry. -/
theorem step_regs (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (bounds : FreshBounds) (query : PqxdhDeploymentInterface.Query)
    (ledger : Ledger) (copies : Local) (start : List (SourceEntry KemSK))
    (outcome : ((FullSpec.Range query × Ledger) × Local) × List (SourceEntry KemSK))
    (reached : outcome ∈ support (journalFrom ((simulateQ (compileImpl setup codec route)
      ((ledgerImpl setup.source.crypto codec setup.serverKeyId bounds query).run ledger)).run copies) start)) :
    outcome.1.1.2.transcript = ledger.transcript ++ [⟨query, outcome.1.1.1⟩] ∧
      regsOfSource outcome.2 = regsOfSource start ++ (regOfEntry ⟨query, outcome.1.1.1⟩).toList := by
  have compiled := journalFrom_support _ start outcome reached
  have layered : outcome.1.1 ∈ support ((ledgerImpl setup.source.crypto codec setup.serverKeyId bounds query).run ledger) := by
    apply support_simulateQ_run'_subset (compileImpl setup codec route) _ copies
    rw [StateT.run'_eq, support_map]
    exact Set.mem_image_of_mem _ compiled
  have transcript : outcome.1.1.2.transcript = ledger.transcript ++ [⟨query, outcome.1.1.1⟩] := by
    rcases query with request | secrecy
    · rw [PqxdhDeploymentSecrecy.ledgerImpl_forward, support_map] at layered
      obtain ⟨reply, _, same⟩ := layered
      rw [← same]
      rfl
    · exact PqxdhDeploymentEligibility.ledger_secrecy setup.source.crypto codec setup.serverKeyId bounds secrecy ledger
        outcome.1.1 layered
  refine ⟨transcript, ?_⟩
  have quiet := fun other => step_quiet setup codec route bounds query other ledger copies start outcome reached
  rcases query with (coin | command) | secrecy
  · rw [quiet (by simp [queryClass])]
    simp [regOfEntry]
  · cases command with
    | create pin keyId =>
        rw [PqxdhDeploymentSecrecy.ledgerImpl_forward] at reached
        simp only [simulateQ_map, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, id_map,
          StateT.run_map, journalFrom_map, support_map, Set.mem_image] at reached
        obtain ⟨answer, member, rfl⟩ := reached
        cases parsed : parsePin pin with
        | none =>
            simp only [PqxdhDeploymentCompile.compileImpl, parsed, StateT.run, journalFrom, simulateQ_pure] at member
            subst member
            simp [regOfEntry]
        | some word =>
            simp only [PqxdhDeploymentCompile.compileImpl, parsed, StateT.run, bind_pure_comp,
              journalFrom_map, support_map, Set.mem_image] at member
            obtain ⟨index, indexMember, rfl⟩ := member
            rw [PqxdhDeploymentCompile.forward, journalFrom_query, support_map] at indexMember
            obtain ⟨reply, _, rfl⟩ := indexMember
            simp [regOfEntry, parsed, PqxdhDeploymentServerAuthEvent.regsOfSource_append, regOfSource]
    | bundle owner =>
        rw [PqxdhDeploymentSecrecy.ledgerImpl_forward] at reached
        simp only [simulateQ_map, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, id_map,
          StateT.run_map, journalFrom_map, support_map, Set.mem_image] at reached
        obtain ⟨answer, member, rfl⟩ := reached
        obtain ⟨reply, same, journaled⟩ := forward_journal (.bundle owner) (.bundle owner) id copies start answer member
        rw [journaled, PqxdhDeploymentServerAuthEvent.regsOfSource_append]
        simp only [same]
        rfl
    | accept raw =>
        rw [PqxdhDeploymentSecrecy.ledgerImpl_forward] at reached
        simp only [simulateQ_map, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, id_map,
          StateT.run_map, journalFrom_map, support_map, Set.mem_image] at reached
        obtain ⟨answer, member, rfl⟩ := reached
        obtain ⟨reply, same, journaled⟩ := forward_journal (.accept raw) (.accept raw) id copies start answer member
        rw [journaled, PqxdhDeploymentServerAuthEvent.regsOfSource_append]
        simp only [same]
        rfl
    | build session payload =>
        rw [PqxdhDeploymentSecrecy.ledgerImpl_forward] at reached
        simp only [simulateQ_map, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, id_map,
          StateT.run_map, journalFrom_map, support_map, Set.mem_image] at reached
        obtain ⟨answer, member, rfl⟩ := reached
        obtain ⟨reply, same, journaled⟩ := forward_journal (.build session payload) (.build session payload) id copies start answer member
        rw [journaled, PqxdhDeploymentServerAuthEvent.regsOfSource_append]
        simp only [same]
        rfl
    | finish owner raw =>
        rw [PqxdhDeploymentSecrecy.ledgerImpl_forward] at reached
        simp only [simulateQ_map, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, id_map,
          StateT.run_map, journalFrom_map, support_map, Set.mem_image] at reached
        obtain ⟨answer, member, rfl⟩ := reached
        obtain ⟨reply, same, journaled⟩ := forward_journal (.finish owner raw) (.finish owner raw) id copies start answer member
        rw [journaled, PqxdhDeploymentServerAuthEvent.regsOfSource_append]
        simp only [same]
        rfl
    | hmac key message =>
        rw [quiet (by simp [queryClass])]
        simp [regOfEntry]
    | hash bytes =>
        rw [quiet (by simp [queryClass])]
        simp [regOfEntry]
    | serverSend keyId plaintext =>
        rw [quiet (by simp [queryClass])]
        simp [regOfEntry]
    | serverRaw raw =>
        rw [quiet (by simp [queryClass])]
        simp [regOfEntry]
    | beaconSend owner plaintext =>
        rw [quiet (by simp [queryClass])]
        simp [regOfEntry]
    | beaconRaw owner raw =>
        rw [quiet (by simp [queryClass])]
        simp [regOfEntry]
  · rw [quiet (by rcases secrecy with ⟨_, _, _⟩ | ⟨_, _⟩ <;> simp [queryClass])]
    simp [regOfEntry]

/-- The registration view of a transcript extended by one entry. -/
theorem regsOf_append (transcript : List Entry) (entry : Entry) :
    regsOf (transcript ++ [entry]) = regsOf transcript ++ (regOfEntry entry).toList := by
  simp only [regsOf, List.filterMap_append, List.filterMap_cons, List.filterMap_nil]
  cases regOfEntry entry <;> rfl

/-- In every outcome of the journaled compiled secrecy-layer run of a complete-interface program, started from a journal whose registration view is that of the starting transcript, the registration view of the final journal is that of the final transcript. -/
theorem compiled_regs_from (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (bounds : FreshBounds) (program : OracleComp FullSpec Result)
    (ledger : Ledger) (copies : Local) (start : List (SourceEntry KemSK))
    (synced : regsOfSource start = regsOf ledger.transcript)
    (outcome : ((Result × Ledger) × Local) × List (SourceEntry KemSK))
    (reached : outcome ∈ support (journalFrom ((simulateQ (compileImpl setup codec route)
      ((simulateQ (ledgerImpl setup.source.crypto codec setup.serverKeyId bounds) program).run ledger)).run copies) start)) :
    regsOfSource outcome.2 = regsOf outcome.1.1.2.transcript := by
  induction program using OracleComp.inductionOn generalizing ledger copies start with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, journalFrom, support_pure, Set.mem_singleton_iff] at reached
      subst reached
      exact synced
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, id_map,
        StateT.run_bind, journalFrom_bind, mem_support_bind_iff] at reached
      obtain ⟨middle, first, second⟩ := reached
      obtain ⟨transcript, logged⟩ := step_regs setup codec route bounds query ledger copies start middle first
      exact ih middle.1.1.1 middle.1.1.2 middle.1.2 middle.2
        (by rw [logged, transcript, regsOf_append, synced]) second

/-- The registration view of the full source14 journal of the compiled program of a complete-interface adversary is the registration view of its final transcript, for every reply. -/
theorem compiled_regs (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) (outcome : ((X × Ledger) × Local) × List (SourceEntry KemSK))
    (reached : outcome ∈ support (journal dflt (compileFull setup codec route bounds mode adversary))) :
    regsOfSource outcome.2 = regsOf outcome.1.1.2.transcript :=
  compiled_regs_from setup codec route bounds (asModeO mode adversary) PqxdhDeploymentSecrecy.Ledger.empty
    PqxdhDeploymentCompile.Local.empty [] rfl outcome reached

end BeaconcryptCore.Computational.PqxdhDeploymentServerAuthTrace

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentServerAuthTrace.journalFrom_query_bind' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentServerAuthTrace.journalFrom_query_bind

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentServerAuthTrace.journalFrom_bind' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentServerAuthTrace.journalFrom_bind

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentServerAuthTrace.journalFrom_map' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentServerAuthTrace.journalFrom_map

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentServerAuthTrace.journalFrom_query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentServerAuthTrace.journalFrom_query

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentServerAuthTrace.regOfSource_other' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentServerAuthTrace.regOfSource_other

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentServerAuthTrace.journal_quiet' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentServerAuthTrace.journal_quiet

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentServerAuthTrace.journalFrom_support' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentServerAuthTrace.journalFrom_support

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentServerAuthTrace.reg_cost' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentServerAuthTrace.reg_cost

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentServerAuthTrace.forward_journal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentServerAuthTrace.forward_journal

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentServerAuthTrace.step_quiet' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentServerAuthTrace.step_quiet

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentServerAuthTrace.step_regs' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentServerAuthTrace.step_regs

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentServerAuthTrace.regsOf_append' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentServerAuthTrace.regsOf_append

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentServerAuthTrace.compiled_regs_from' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentServerAuthTrace.compiled_regs_from

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentServerAuthTrace.compiled_regs' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentServerAuthTrace.compiled_regs
