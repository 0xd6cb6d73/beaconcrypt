-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePublicFreshHandles

/-! The actual native ledger's first admissible public test always has its original private test state. The proof follows every literal query and then the unchanged wrapped native execution in every mode, including malformed tests and failed sends. No eligible-event premise or test-state conclusion is supplied to the invariant. -/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true
namespace BeaconcryptCore.Computational.RegistrationNativeLedgerTestInvariant
open RegistrationNativeInterface (FullSpec)
open PqxdhDeploymentInterface (FreshBounds)
open PqxdhRecordLiftFlat (LedgerInv)
variable {Reader Response Value NativeState : Type}

private theorem simulate_support {SourceIndex TargetIndex Result : Type}
    {source : OracleSpec SourceIndex} {target : OracleSpec TargetIndex}
    (implementation : QueryImpl source (OracleComp target)) (work : OracleComp source Result) (result : Result)
    (supported : result ∈ support (simulateQ implementation work)) : result ∈ support work := by
  induction work using OracleComp.inductionOn with
  | pure value => simpa only [simulateQ_pure, mem_support_pure_iff] using supported
  | query_bind query next ih =>
      rw [simulateQ_bind, simulateQ_spec_query, mem_support_bind_iff] at supported
      obtain ⟨reply, _reached, tail⟩ := supported
      rw [mem_support_bind_iff]
      exact ⟨reply, mem_support_query query reply, ih reply tail⟩

/-- Every actual native callback preserves the original first-admissible-test invariant. -/
theorem query (crypto : Pqxdh.Crypto) (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (serverKeyId : U64) (bounds : FreshBounds) (request : FullSpec.Domain) (before : RegistrationNativeLedger.State)
    (invariant : LedgerInv before.ledger) (result : FullSpec.Range request × RegistrationNativeLedger.State)
    (supported : result ∈ support ((RegistrationNativeLedger.handler crypto codec serverKeyId bounds request).run before)) :
    LedgerInv result.2.ledger := by
  cases request with
  | inl core =>
      rw [RegistrationNativeLedger.query_forward, support_map] at supported
      obtain ⟨reply, _reached, rfl⟩ := supported
      cases core <;> simpa only [LedgerInv, RegistrationNativeLedger.record,
        PqxdhRecordLiftFlat.firstTest_append, RegistrationNativeInterface.Entry.erase,
        PqxdhRecordLiftFlat.admissibleTest_forward, Option.or_none] using invariant
  | inr secrecy =>
      rw [RegistrationNativeLedger.query_secrecy, support_map] at supported
      obtain ⟨inner, reached, rfl⟩ := supported
      exact PqxdhRecordLiftFlat.ledger_inv crypto codec serverKeyId bounds (.inr secrecy) before.ledger invariant inner
        (simulate_support RegistrationNativeLedger.legacyLift _ inner reached)

/-- Every adaptive native client retains the same private test-origin invariant. -/
theorem program (crypto : Pqxdh.Crypto) (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (serverKeyId : U64) (bounds : FreshBounds) (work : OracleComp FullSpec Value) (before : RegistrationNativeLedger.State)
    (invariant : LedgerInv before.ledger) (result : Value × RegistrationNativeLedger.State)
    (supported : result ∈ support ((simulateQ (RegistrationNativeLedger.handler crypto codec serverKeyId bounds) work).run before)) :
    LedgerInv result.2.ledger := by
  induction work using OracleComp.inductionOn generalizing before result with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at supported
      subst result
      exact invariant
  | query_bind request next ih =>
      rw [simulateQ_bind, StateT.run_bind, simulateQ_spec_query, mem_support_bind_iff] at supported
      obtain ⟨inner, reached, tail⟩ := supported
      exact ih inner.1 inner.2 (query crypto codec serverKeyId bounds request before invariant inner reached) result tail

/-- The real wrapper initializes the invariant from its literal empty test state. -/
theorem wrap (crypto : Pqxdh.Crypto) (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (serverKeyId : U64) (bounds : FreshBounds) (work : OracleComp FullSpec Value) (result : Value × RegistrationNativeLedger.State)
    (supported : result ∈ support (RegistrationNativeLedger.wrap crypto codec serverKeyId bounds work)) :
    LedgerInv result.2.ledger :=
  program crypto codec serverKeyId bounds work RegistrationNativeLedger.empty PqxdhRecordLiftFlat.ledgerInv_empty result supported

/-- Every supported full native execution, in any original observation mode and under any typed handler, retains the exact ledger test invariant. -/
theorem run (crypto : Pqxdh.Crypto) (wire : RegistrationNativeWire.Wire) (serverKeyId : U64) (bounds : FreshBounds)
    (typed : QueryImpl RegistrationNativeRawAdapter.TypedSpec (StateT NativeState ProbComp))
    (mode : PqxdhDeploymentInterface.Mode) (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (before : NativeState) (result : Value × (RegistrationNativeLedger.State × NativeState))
    (supported : result ∈ support (RegistrationNativeFullCompiler.run crypto wire serverKeyId bounds typed mode work before)) :
    LedgerInv result.2.1.ledger := by
  rw [RegistrationNativeFullCompiler.run, RegistrationNativeFullCompiler.handler, RegistrationNativeLedger.run_wrap, support_map] at supported
  obtain ⟨inner, reached, rfl⟩ := supported
  apply wrap crypto (RegistrationNativeWire.ledgerCodec wire) serverKeyId bounds (RegistrationNativeInterface.asModeO mode work) inner.1
  apply OracleComp.support_simulateQ_run'_subset (RegistrationNativeRawAdapter.handler wire typed) _ before
  rw [StateT.run'_eq, support_map]
  exact Set.mem_image_of_mem Prod.fst reached

/-- A public transcript's actual first admissible test has an allocated private native test state. -/
theorem run_test_exists (crypto : Pqxdh.Crypto) (wire : RegistrationNativeWire.Wire) (serverKeyId : U64) (bounds : FreshBounds)
    (typed : QueryImpl RegistrationNativeRawAdapter.TypedSpec (StateT NativeState ProbComp))
    (mode : PqxdhDeploymentInterface.Mode) (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (before : NativeState) (result : Value × (RegistrationNativeLedger.State × NativeState))
    (supported : result ∈ support (RegistrationNativeFullCompiler.run crypto wire serverKeyId bounds typed mode work before)) :
    (PqxdhRecordLiftIdeal.firstTest result.2.1.ledger.transcript).isSome = true → result.2.1.ledger.test.isSome = true := by
  have actual := run crypto wire serverKeyId bounds typed mode work before result supported
  rw [← actual]
  simp only [Option.isSome_map]
  exact id

end BeaconcryptCore.Computational.RegistrationNativeLedgerTestInvariant

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeLedgerTestInvariant.query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeLedgerTestInvariant.query

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeLedgerTestInvariant.program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeLedgerTestInvariant.program

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeLedgerTestInvariant.wrap' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeLedgerTestInvariant.wrap

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeLedgerTestInvariant.run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeLedgerTestInvariant.run

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeLedgerTestInvariant.run_test_exists' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeLedgerTestInvariant.run_test_exists
