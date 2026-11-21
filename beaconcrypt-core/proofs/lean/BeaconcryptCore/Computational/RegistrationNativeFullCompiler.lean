-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeRawAdapter

/-! The ML-pin-aware raw API and the literal original secrecy ledger compile together into the typed native frontend. Complete outcomes retain the original hidden bit/fresh messages, full native public transcript and entire typed poststate. Exact original classwise secrecy bills transfer before cryptographic source reductions. These are operational compiler laws; actual native role orchestration and security reductions instantiate the typed frontend separately. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RegistrationNativeFullCompiler
open RegistrationNativeWire (Wire ledgerCodec)
open RegistrationNativeInterface (ModeSpec asModeO Respects Entry)
open RegistrationNativeRawAdapter (TypedSpec)
open PqxdhDeploymentInterface (Mode Budget FreshBounds)
variable {Value NativeState : Type}

noncomputable def compile (crypto : Pqxdh.Crypto) (wire : Wire) (serverKid : Std.U64)
    (bounds : FreshBounds) (mode : Mode) (work : OracleComp (ModeSpec mode) Value) :
    OracleComp TypedSpec (Value × RegistrationNativeLedger.State) :=
  RegistrationNativeRawAdapter.compile wire
    (RegistrationNativeLedger.wrap crypto (ledgerCodec wire) serverKid bounds (asModeO mode work))

noncomputable def handler (crypto : Pqxdh.Crypto) (wire : Wire) (serverKid : Std.U64) (bounds : FreshBounds)
    (typed : QueryImpl TypedSpec (StateT NativeState ProbComp)) :
    QueryImpl RegistrationNativeInterface.FullSpec (StateT (RegistrationNativeLedger.State × NativeState) ProbComp) :=
  RegistrationNativeLedger.interpreted (RegistrationNativeRawAdapter.handler wire typed)
    crypto (ledgerCodec wire) serverKid bounds

noncomputable def run (crypto : Pqxdh.Crypto) (wire : Wire) (serverKid : Std.U64) (bounds : FreshBounds)
    (typed : QueryImpl TypedSpec (StateT NativeState ProbComp)) (mode : Mode)
    (work : OracleComp (ModeSpec mode) Value) (before : NativeState) :
    ProbComp (Value × (RegistrationNativeLedger.State × NativeState)) :=
  (simulateQ (handler crypto wire serverKid bounds typed) (asModeO mode work)).run
    (RegistrationNativeLedger.empty, before)

/-- The actual full raw execution and compiled typed execution have the same complete outcome, including every failed native poststate. -/
theorem compile_run (crypto : Pqxdh.Crypto) (wire : Wire) (serverKid : Std.U64) (bounds : FreshBounds)
    (typed : QueryImpl TypedSpec (StateT NativeState ProbComp)) (mode : Mode)
    (work : OracleComp (ModeSpec mode) Value) (before : NativeState) :
    run crypto wire serverKid bounds typed mode work before =
      (fun result => (result.1.1, (result.1.2, result.2))) <$>
        (simulateQ typed (compile crypto wire serverKid bounds mode work)).run before := by
  rw [run, handler, RegistrationNativeLedger.run_wrap, RegistrationNativeRawAdapter.program_native]
  rfl

/-- Every full native public or private analysis observation transfers by the derived outcome equality. -/
theorem observe_run {Observed : Type} (crypto : Pqxdh.Crypto) (wire : Wire) (serverKid : Std.U64)
    (bounds : FreshBounds) (typed : QueryImpl TypedSpec (StateT NativeState ProbComp)) (mode : Mode)
    (work : OracleComp (ModeSpec mode) Value) (before : NativeState)
    (observe : (Value × (RegistrationNativeLedger.State × NativeState)) → Observed) :
    observe <$> run crypto wire serverKid bounds typed mode work before =
      (fun result => observe (result.1.1, (result.1.2, result.2))) <$>
        (simulateQ typed (compile crypto wire serverKid bounds mode work)).run before := by
  rw [compile_run, Functor.map_map]

/-- Named events may read the original CE ledger and complete native transcript directly, without an event-correspondence premise. -/
theorem event_probability (crypto : Pqxdh.Crypto) (wire : Wire) (serverKid : Std.U64) (bounds : FreshBounds)
    (typed : QueryImpl TypedSpec (StateT NativeState ProbComp)) (mode : Mode)
    (work : OracleComp (ModeSpec mode) Value) (before : NativeState)
    (event : (Value × (RegistrationNativeLedger.State × NativeState)) → Bool) :
    𝒟[event <$> run crypto wire serverKid bounds typed mode work before] {true} =
      𝒟[(fun result => event (result.1.1, (result.1.2, result.2))) <$>
        (simulateQ typed (compile crypto wire serverKid bounds mode work)).run before] {true} := by
  rw [observe_run]

/-- Every actual full native execution derives the original ledger transcript by dropping only the extra create ML pin. -/
theorem ledger_projection (crypto : Pqxdh.Crypto) (wire : Wire) (serverKid : Std.U64) (bounds : FreshBounds)
    (typed : QueryImpl TypedSpec (StateT NativeState ProbComp)) (mode : Mode)
    (work : OracleComp (ModeSpec mode) Value) (before : NativeState)
    (result : Value × (RegistrationNativeLedger.State × NativeState))
    (supported : result ∈ support (run crypto wire serverKid bounds typed mode work before)) :
    result.2.1.ledger.transcript = result.2.1.transcript.map Entry.erase := by
  rw [run, handler, RegistrationNativeLedger.run_wrap, support_map] at supported
  obtain ⟨inner, reached, rfl⟩ := supported
  apply RegistrationNativeLedger.wrap_consistent crypto (ledgerCodec wire) serverKid bounds (asModeO mode work) inner.1
  apply OracleComp.support_simulateQ_run'_subset (RegistrationNativeRawAdapter.handler wire typed) _ before
  rw [StateT.run'_eq, support_map]
  exact Set.mem_image_of_mem Prod.fst reached

/-- Parsing, the extra ML public pin, observation projection and unchanged secrecy draws preserve the original tight command and fresh-byte allowances. -/
theorem compile_bound (crypto : Pqxdh.Crypto) (wire : Wire) (serverKid : Std.U64) (bounds : FreshBounds)
    (mode : Mode) (work : OracleComp (ModeSpec mode) Value) (budget : Budget) (bounded : Respects budget work)
    (kind : Fin 12) :
    (compile crypto wire serverKid bounds mode work).IsQueryBoundP
      (fun query => RegistrationNativeRawAdapter.kind query = kind)
      (∑ full, PqxdhDeploymentCompileSecrecy.wrapCost bounds kind full * budget.cap full) :=
  RegistrationNativeRawAdapter.compile_bound wire _ kind _
    (RegistrationNativeLedgerCaps.wrap_bound crypto (ledgerCodec wire) serverKid bounds mode work budget bounded kind)

end BeaconcryptCore.Computational.RegistrationNativeFullCompiler

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeFullCompiler.compile_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeFullCompiler.compile_run
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeFullCompiler.observe_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeFullCompiler.observe_run
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeFullCompiler.event_probability' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeFullCompiler.event_probability
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeFullCompiler.ledger_projection' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeFullCompiler.ledger_projection
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeFullCompiler.compile_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeFullCompiler.compile_bound
