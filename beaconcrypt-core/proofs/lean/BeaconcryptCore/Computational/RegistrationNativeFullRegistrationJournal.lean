-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeRegistrationJournalCoverage
/-! The original full raw compiler ledger and the complete typed source journal are linked internally. Every successful parsed acceptance and strict earlier bundle publication therefore has bounded all-attempt ordinals and an exact source path, preserving the full final state, original test bit, fresh ledger and native transcript. No caller journal/path invariant or prefix-roster identity is assumed. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeFullRegistrationJournal
open RegistrationNativeStageTrace (Call Path)
open RegistrationNativeRawAdapter (TypedSpec)
open RegistrationNativeRawRegistrationJournal (Mark logging typedMark)
open RegistrationNativeRegistrationJournalProjection (project)
open RegistrationNativeRegistrationJournalCoverage (count IsAccept IsBundle)
variable {S A : Type}
variable (crypto : Pqxdh.Crypto) (wire : RegistrationNativeWire.Wire) (serverKeyId : Std.U64)
    (bounds : PqxdhDeploymentInterface.FreshBounds) (implementation : QueryImpl TypedSpec (StateT S ProbComp))
    (mode : PqxdhDeploymentInterface.Mode) (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) A) (before : S)

/-- Erasing only callback analysis records restores the complete original full-compiler run and its private secrecy ledger. -/
theorem erase :
    Prod.map id (Prod.map id Prod.fst) <$>
      RegistrationNativeFullCompiler.run crypto wire serverKeyId bounds (RegistrationNativeStageTrace.handler implementation) mode work (before, []) =
      RegistrationNativeFullCompiler.run crypto wire serverKeyId bounds implementation mode work before := by
  have original := congrArg (Functor.map (fun result => (result.1.1, (result.1.2, result.2))))
    (RegistrationNativeStageTrace.erase implementation (RegistrationNativeFullCompiler.compile crypto wire serverKeyId bounds mode work) (before, []))
  simpa only [RegistrationNativeFullCompiler.compile_run, Functor.map_map, Prod.map_def, id_eq] using original

/-- The same fully continued source journal projects to the exact typed registration log, preserving the complete final source and original ledger. -/
theorem projection :
    Prod.map id (Prod.map id project) <$>
      RegistrationNativeFullCompiler.run crypto wire serverKeyId bounds (RegistrationNativeStageTrace.handler implementation) mode work (before, []) =
      RegistrationNativeFullCompiler.run crypto wire serverKeyId bounds (logging implementation) mode work (before, []) := by
  have original := congrArg (Functor.map (fun result => (result.1.1, (result.1.2, result.2))))
    (RegistrationNativeRegistrationJournalProjection.typed implementation (RegistrationNativeFullCompiler.compile crypto wire serverKeyId bounds mode work) (before, []))
  simpa only [RegistrationNativeFullCompiler.compile_run, Functor.map_map, Prod.map_def, id_eq, project, List.filterMap_nil] using original

/-- Every supported complete compiled journal derives its same-run path with the actual earlier private source states. -/
theorem path (result : A × (RegistrationNativeLedger.State × (S × List (Call TypedSpec S))))
    (supported : result ∈ support (RegistrationNativeFullCompiler.run crypto wire serverKeyId bounds (RegistrationNativeStageTrace.handler implementation) mode work (before, []))) :
    Path implementation before result.2.2.2 result.2.2.1 := by
  rw [RegistrationNativeFullCompiler.compile_run, support_map] at supported
  obtain ⟨returned, reached, rfl⟩ := supported
  exact RegistrationNativeStageTrace.path implementation (RegistrationNativeFullCompiler.compile crypto wire serverKeyId bounds mode work) before returned reached

/-- The complete native transcript and its exact typed callback chronology are linked internally, including failed parsed accepts and all failed bundle attempts. -/
theorem ledger (result : A × (RegistrationNativeLedger.State × (S × List (Call TypedSpec S))))
    (supported : result ∈ support (RegistrationNativeFullCompiler.run crypto wire serverKeyId bounds (RegistrationNativeStageTrace.handler implementation) mode work (before, []))) :
    RegistrationNativeRegistrationLedgerLog.transcript wire result.2.1.transcript =
      result.2.2.2.filterMap (fun call => typedMark call.query call.reply) := by
  have projected : Prod.map id (Prod.map id project) result ∈ support
      (Prod.map id (Prod.map id project) <$> RegistrationNativeFullCompiler.run crypto wire serverKeyId bounds
        (RegistrationNativeStageTrace.handler implementation) mode work (before, [])) := by
    rw [support_map]
    exact Set.mem_image_of_mem _ supported
  rw [projection] at projected
  exact RegistrationNativeRegistrationLedgerLog.initialized wire implementation crypto (RegistrationNativeWire.ledgerCodec wire) serverKeyId bounds
    (RegistrationNativeInterface.asModeO mode work) before _ projected

attribute [local irreducible] RegistrationNativeFullCompiler.compile

/-- Original raw accept allowance bounds every attempted typed parsed acceptance, regardless of its actual optional reply. -/
theorem accept_bound (budget : PqxdhDeploymentInterface.Budget) (bounded : RegistrationNativeInterface.Respects budget work) :
    (RegistrationNativeFullCompiler.compile crypto wire serverKeyId bounds mode work).IsQueryBoundP IsAccept budget.accept := by
  have bill := RegistrationNativeFullCompiler.compile_bound crypto wire serverKeyId bounds mode work budget bounded 3
  simp [Fin.sum_univ_succ, PqxdhDeploymentCompileSecrecy.wrapCost] at bill
  apply bill.of_imp
  intro query selected
  cases query with
  | inl coin => exact selected.elim
  | inr command => cases command <;> first | rfl | exact selected.elim

/-- Original raw bundle allowance counts all attempted public bundle callbacks, including failed handles and stateful writers. -/
theorem bundle_bound (budget : PqxdhDeploymentInterface.Budget) (bounded : RegistrationNativeInterface.Respects budget work) :
    (RegistrationNativeFullCompiler.compile crypto wire serverKeyId bounds mode work).IsQueryBoundP IsBundle budget.bundle := by
  have bill := RegistrationNativeFullCompiler.compile_bound crypto wire serverKeyId bounds mode work budget bounded 2
  simp [Fin.sum_univ_succ, PqxdhDeploymentCompileSecrecy.wrapCost] at bill
  apply bill.of_imp
  intro query selected
  cases query with
  | inl coin => exact selected.elim
  | inr command => cases command <;> first | rfl | exact selected.elim
/-- Every successful decoded acceptance in the original full ledger has its bounded actual typed source occurrence and exact same-run private prefix/suffix. -/
theorem acceptance (budget : PqxdhDeploymentInterface.Budget) (bounded : RegistrationNativeInterface.Respects budget work)
    (result : A × (RegistrationNativeLedger.State × (S × List (Call TypedSpec S))))
    (supported : result ∈ support (RegistrationNativeFullCompiler.run crypto wire serverKeyId bounds (RegistrationNativeStageTrace.handler implementation) mode work (before, [])))
    (leading trailing : List Mark) (packet : beaconcrypt_core.registration.InitPacket) (session : Nat)
    (marked : RegistrationNativeRegistrationLedgerLog.transcript wire result.2.1.transcript = leading ++ .accept packet (some session) :: trailing) :
    ∃ earlier call later, result.2.2.2 = earlier ++ call :: later ∧
      earlier.filterMap (fun call => typedMark call.query call.reply) = leading ∧
      typedMark call.query call.reply = some (.accept packet (some session)) ∧
      count IsAccept earlier < budget.accept ∧ Path implementation before earlier call.before ∧
      RegistrationNativeStageTrace.Executed implementation call ∧ Path implementation call.after later result.2.2.1 := by
  have exactLog := (ledger crypto wire serverKeyId bounds implementation mode work before result supported).symm.trans marked
  rw [RegistrationNativeFullCompiler.compile_run, support_map] at supported
  obtain ⟨returned, reached, rfl⟩ := supported
  exact RegistrationNativeRegistrationJournalCoverage.acceptance implementation (RegistrationNativeFullCompiler.compile crypto wire serverKeyId bounds mode work)
    budget.accept (accept_bound crypto wire serverKeyId bounds mode work budget bounded) before returned reached leading trailing packet session exactLog

/-- The original complete raw ledger gives finite all-attempt bundle/accept ordinals and literal strict source chronology, with no journal or path invariant supplied by a caller. -/
theorem earlier_bundle (budget : PqxdhDeploymentInterface.Budget) (bounded : RegistrationNativeInterface.Respects budget work)
    (result : A × (RegistrationNativeLedger.State × (S × List (Call TypedSpec S))))
    (supported : result ∈ support (RegistrationNativeFullCompiler.run crypto wire serverKeyId bounds (RegistrationNativeStageTrace.handler implementation) mode work (before, [])))
    (leading trailing : List Mark) (packet : beaconcrypt_core.registration.InitPacket) (session owner : Nat) (bytes : Pqxdh.Bytes)
    (marked : RegistrationNativeRegistrationLedgerLog.transcript wire result.2.1.transcript = leading ++ .accept packet (some session) :: trailing)
    (published : .bundle owner (some bytes) ∈ leading) :
    ∃ firstCalls bundle middle accepted suffix,
      result.2.2.2 = firstCalls ++ bundle :: middle ++ accepted :: suffix ∧
      typedMark bundle.query bundle.reply = some (.bundle owner (some bytes)) ∧
      typedMark accepted.query accepted.reply = some (.accept packet (some session)) ∧
      count IsBundle firstCalls < budget.bundle ∧ count IsAccept (firstCalls ++ bundle :: middle) < budget.accept ∧
      Path implementation before firstCalls bundle.before ∧ RegistrationNativeStageTrace.Executed implementation bundle ∧
      Path implementation bundle.after middle accepted.before ∧ RegistrationNativeStageTrace.Executed implementation accepted ∧
      Path implementation accepted.after suffix result.2.2.1 := by
  have exactLog := (ledger crypto wire serverKeyId bounds implementation mode work before result supported).symm.trans marked
  rw [RegistrationNativeFullCompiler.compile_run, support_map] at supported
  obtain ⟨returned, reached, rfl⟩ := supported
  exact RegistrationNativeRegistrationJournalCoverage.earlier_bundle implementation (RegistrationNativeFullCompiler.compile crypto wire serverKeyId bounds mode work)
    budget.accept budget.bundle (accept_bound crypto wire serverKeyId bounds mode work budget bounded)
    (bundle_bound crypto wire serverKeyId bounds mode work budget bounded) before returned reached leading trailing packet session owner bytes exactLog published

end BeaconcryptCore.Computational.RegistrationNativeFullRegistrationJournal


/-- info: 'BeaconcryptCore.Computational.RegistrationNativeFullRegistrationJournal.erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeFullRegistrationJournal.erase

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeFullRegistrationJournal.projection' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeFullRegistrationJournal.projection

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeFullRegistrationJournal.path' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeFullRegistrationJournal.path

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeFullRegistrationJournal.ledger' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeFullRegistrationJournal.ledger

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeFullRegistrationJournal.accept_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeFullRegistrationJournal.accept_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeFullRegistrationJournal.bundle_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeFullRegistrationJournal.bundle_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeFullRegistrationJournal.acceptance' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeFullRegistrationJournal.acceptance

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeFullRegistrationJournal.earlier_bundle' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeFullRegistrationJournal.earlier_bundle
