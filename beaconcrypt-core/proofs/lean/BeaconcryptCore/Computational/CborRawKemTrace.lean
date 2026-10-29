-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.CborRawCompileCaps
import BeaconcryptCore.Computational.PqxdhDeploymentKemTransfer

/-! The raw-CBOR compiler forwards registration accepts and bundles verbatim. Its trace therefore records the registration entries of the actual wire ledger, while admission checks, public sender-prefix removal and ordinary fallible record operations remain quiet for that registration log. -/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false

namespace BeaconcryptCore.Computational.CborRawKemTrace

open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhDeploymentInterface (Entry FullSpec Mode ModeSpec FreshBounds asModeO queryClass)
open PqxdhDeploymentSecrecy (Ledger ledgerImpl)
open PqxdhDeploymentRegistrationTrace (Logged traceFrom)
open PqxdhDeploymentKemTransfer (regOf registrations traceFrom_quiet traceFrom_map traceFrom_query
  traceFrom_bind forwardLogged_run bundle_cost accept_cost registrations_append)
open CborAdmissionCompiler (Local)
open CborTaggedSimulation (boundaryWire)
open PqxdhRegistrationJointRevealCosts (sourceKind)
open PqxdhDeploymentCompileBudget (commandKind cost)
open PqxdhDeploymentCompileSecrecy (wrapCost)
variable {ι KemSK Reader Response X Result : Type} {baseSpec : OracleSpec ι}

theorem accept_run (setup : Setup baseSpec KemSK) (wire : Codec Reader Response)
    (parse : Pqxdh.Bytes → Option CborProductionBoundary.NativeFrame) (raw : Pqxdh.Bytes) (memory : Local) :
    (CborRawCompile.compileImpl setup wire parse (.inr (.accept raw))).run memory =
      (fun answer => (answer, { memory with copies :=
        { memory.copies with log := PqxdhDeploymentCompile.logReply memory.copies.log (.accept raw) answer } })) <$>
        PqxdhDeploymentCompile.forward (KemSK := KemSK) (.accept raw) := by
  simp only [CborRawCompile.compileImpl, CborSplitCompiler.compileImpl, CborAdmissionCompiler.compileImpl,
    CborAdmissionCompiler.liftExisting, StateT.run, PqxdhDeploymentCompile.compileImpl,
    PqxdhDeploymentCompile.forwardLogged, bind_pure_comp, Functor.map_map, id_eq]

theorem bundle_run (setup : Setup baseSpec KemSK) (wire : Codec Reader Response)
    (parse : Pqxdh.Bytes → Option CborProductionBoundary.NativeFrame) (owner : Nat) (memory : Local) :
    (CborRawCompile.compileImpl setup wire parse (.inr (.bundle owner))).run memory =
      (fun answer => (answer, { memory with copies :=
        { memory.copies with log := PqxdhDeploymentCompile.logReply memory.copies.log (.bundle owner) answer } })) <$>
        PqxdhDeploymentCompile.forward (KemSK := KemSK) (.bundle owner) := by
  simp only [CborRawCompile.compileImpl, CborSplitCompiler.compileImpl, CborAdmissionCompiler.compileImpl,
    CborAdmissionCompiler.liftExisting, StateT.run, PqxdhDeploymentCompile.compileImpl,
    PqxdhDeploymentCompile.forwardLogged, bind_pure_comp, Functor.map_map, id_eq]

theorem step_trace (setup : Setup baseSpec KemSK) (wire : Codec Reader Response)
    (parse : Pqxdh.Bytes → Option CborProductionBoundary.NativeFrame) (bounds : FreshBounds) (query : PqxdhDeploymentInterface.Query)
    (ledger : Ledger) (copies : Local) (log : List Logged)
    (outcome : ((FullSpec.Range query × Ledger) × Local) × List Logged)
    (reached : outcome ∈ support (traceFrom ((simulateQ (CborRawCompile.compileImpl setup wire parse)
      ((ledgerImpl setup.source.crypto (boundaryWire wire parse) setup.serverKeyId bounds query).run ledger)).run copies) log)) :
    outcome.1.1.2.transcript = ledger.transcript ++ [⟨query, outcome.1.1.1⟩] ∧
      outcome.2 = log ++ (regOf ⟨query, outcome.1.1.1⟩).toList := by
  have compiled := PqxdhDeploymentRegistrationTrace.traceFrom_support _ log outcome reached
  have layered : outcome.1.1 ∈ support ((ledgerImpl setup.source.crypto (boundaryWire wire parse) setup.serverKeyId bounds query).run ledger) := by
    apply support_simulateQ_run'_subset (CborRawCompile.compileImpl setup wire parse) _ copies
    rw [StateT.run'_eq, support_map]
    exact Set.mem_image_of_mem _ compiled
  have transcript : outcome.1.1.2.transcript = ledger.transcript ++ [⟨query, outcome.1.1.1⟩] := by
    rcases query with request | secrecy
    · rw [PqxdhDeploymentSecrecy.ledgerImpl_forward, support_map] at layered
      obtain ⟨reply, _, same⟩ := layered
      rw [← same]
      rfl
    · exact PqxdhDeploymentEligibility.ledger_secrecy setup.source.crypto (boundaryWire wire parse) setup.serverKeyId bounds secrecy ledger
        outcome.1.1 layered
  refine ⟨transcript, ?_⟩
  by_cases accept : ∃ raw, query = .inl (.inr (.accept raw))
  · obtain ⟨raw, rfl⟩ := accept
    rw [PqxdhDeploymentSecrecy.ledgerImpl_forward] at reached
    simp only [simulateQ_map, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, id_map,
      StateT.run_map, traceFrom_map, support_map, Set.mem_image] at reached
    obtain ⟨answer, member, rfl⟩ := reached
    rw [accept_run, PqxdhDeploymentCompile.forward, traceFrom_map, traceFrom_query, Functor.map_map,
      support_map] at member
    obtain ⟨reply, _, rfl⟩ := member
    rfl
  · by_cases bundle : ∃ owner, query = .inl (.inr (.bundle owner))
    · obtain ⟨owner, rfl⟩ := bundle
      rw [PqxdhDeploymentSecrecy.ledgerImpl_forward] at reached
      simp only [simulateQ_map, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, id_map,
        StateT.run_map, traceFrom_map, support_map, Set.mem_image] at reached
      obtain ⟨answer, member, rfl⟩ := reached
      rw [bundle_run, PqxdhDeploymentCompile.forward, traceFrom_map, traceFrom_query, Functor.map_map,
        support_map] at member
      obtain ⟨reply, _, rfl⟩ := member
      rfl
    · have notAccept : queryClass query ≠ 3 := by
        intro same
        rcases query with ((coin | command) | secrecy)
        · cases same
        · cases command <;> first | exact accept ⟨_, rfl⟩ | cases same
        · rcases secrecy with ⟨_, _, _⟩ | ⟨_, _⟩ <;> cases same
      have notBundle : queryClass query ≠ 2 := by
        intro same
        rcases query with ((coin | command) | secrecy)
        · cases same
        · cases command <;> first | exact bundle ⟨_, rfl⟩ | cases same
        · rcases secrecy with ⟨_, _, _⟩ | ⟨_, _⟩ <;> cases same
      have quietBundle := FinitePartitionQueryBounds.weighted_bound commandKind (cost (.inl 2))
        (fun core => wrapCost bounds core (queryClass query)) (CborRawCompile.compileImpl setup wire parse)
        (fun request => sourceKind (KemSK := KemSK) request = .inl 2)
        ((ledgerImpl setup.source.crypto (boundaryWire wire parse) setup.serverKeyId bounds query).run ledger)
        (fun core => PqxdhDeploymentCompileSecrecy.wrap_step setup.source.crypto (boundaryWire wire parse) setup.serverKeyId bounds core query
          ledger)
        (fun request state => CborRawCompile.step_bound setup wire parse (.inl 2) request state) copies
      have quietAccept := FinitePartitionQueryBounds.weighted_bound commandKind (cost (.inl 3))
        (fun core => wrapCost bounds core (queryClass query)) (CborRawCompile.compileImpl setup wire parse)
        (fun request => sourceKind (KemSK := KemSK) request = .inl 3)
        ((ledgerImpl setup.source.crypto (boundaryWire wire parse) setup.serverKeyId bounds query).run ledger)
        (fun core => PqxdhDeploymentCompileSecrecy.wrap_step setup.source.crypto (boundaryWire wire parse) setup.serverKeyId bounds core query
          ledger)
        (fun request state => CborRawCompile.step_bound setup wire parse (.inl 3) request state) copies
      rw [bundle_cost bounds _ notBundle] at quietBundle
      rw [accept_cost bounds _ notAccept] at quietAccept
      have kept := traceFrom_quiet _ quietBundle quietAccept log outcome reached
      have none : regOf ⟨query, outcome.1.1.1⟩ = none := by
        rcases query with ((coin | command) | secrecy)
        · rfl
        · cases command with
          | accept raw => exact absurd ⟨raw, rfl⟩ accept
          | bundle owner => exact absurd ⟨owner, rfl⟩ bundle
          | _ => rfl
        · rfl
      rw [kept, none, Option.toList_none, List.append_nil]



theorem compiled_traceFrom (setup : Setup baseSpec KemSK) (wire : Codec Reader Response)
    (parse : Pqxdh.Bytes → Option CborProductionBoundary.NativeFrame) (bounds : FreshBounds) (program : OracleComp FullSpec Result)
    (ledger : Ledger) (copies : Local) (log : List Logged) (synced : log = registrations ledger.transcript)
    (outcome : ((Result × Ledger) × Local) × List Logged)
    (reached : outcome ∈ support (traceFrom ((simulateQ (CborRawCompile.compileImpl setup wire parse)
      ((simulateQ (ledgerImpl setup.source.crypto (boundaryWire wire parse) setup.serverKeyId bounds) program).run ledger)).run copies) log)) :
    outcome.2 = registrations outcome.1.1.2.transcript := by
  induction program using OracleComp.inductionOn generalizing ledger copies log with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, traceFrom, support_pure, Set.mem_singleton_iff] at reached
      subst reached
      exact synced
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, id_map,
        StateT.run_bind, traceFrom_bind, mem_support_bind_iff] at reached
      obtain ⟨middle, first, second⟩ := reached
      obtain ⟨transcript, logged⟩ := step_trace setup wire parse bounds query ledger copies log middle first
      exact ih middle.1.1.1 middle.1.1.2 middle.1.2 middle.2
        (by rw [logged, transcript, registrations_append, synced]) second

/-- The log of the traced compiled program of a complete-interface adversary is the registrations of its final transcript. -/
theorem compiled_trace (setup : Setup baseSpec KemSK) (wire : Codec Reader Response)
    (parse : Pqxdh.Bytes → Option CborProductionBoundary.NativeFrame) (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) (outcome : ((X × Ledger) × Local) × List Logged)
    (reached : outcome ∈ support (traceFrom (CborRawCompileSecrecy.compileFull setup wire parse bounds mode adversary) [])) :
    outcome.2 = registrations outcome.1.1.2.transcript :=
  compiled_traceFrom setup wire parse bounds (asModeO mode adversary) Ledger.empty (Local.empty setup.serverKeyId) [] rfl outcome reached



end BeaconcryptCore.Computational.CborRawKemTrace

/-- info: 'BeaconcryptCore.Computational.CborRawKemTrace.accept_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawKemTrace.accept_run
/-- info: 'BeaconcryptCore.Computational.CborRawKemTrace.bundle_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawKemTrace.bundle_run

/-- info: 'BeaconcryptCore.Computational.CborRawKemTrace.step_trace' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawKemTrace.step_trace

/-- info: 'BeaconcryptCore.Computational.CborRawKemTrace.compiled_traceFrom' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawKemTrace.compiled_traceFrom

/-- info: 'BeaconcryptCore.Computational.CborRawKemTrace.compiled_trace' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawKemTrace.compiled_trace
