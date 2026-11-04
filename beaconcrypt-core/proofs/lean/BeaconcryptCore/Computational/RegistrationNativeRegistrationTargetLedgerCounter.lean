-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeRegistrationTargetRawCounter

/-! Any source-derived parsed-attempt counter agrees with the complete original public ledger. The compiler retains hidden-bit and fresh draws, refused sends and failure poststates. Current source callbacks instantiate the local counter law separately. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeRegistrationTargetLedgerCounter
open RegistrationNativeWire (Wire)
open PqxdhDeploymentInterface (FreshBounds Mode)
open RegistrationNativeEvents (parsedAcceptCount parsedAccept)
variable {S Value : Type} (crypto : Pqxdh.Crypto) (wire : Wire)
    (typed : QueryImpl RegistrationNativeRawAdapter.TypedSpec (StateT S ProbComp)) (counter : S → Nat)
    (step : ∀ (query : RegistrationNativeRawAdapter.TypedSpec.Domain) (before : S)
      (result : RegistrationNativeRawAdapter.TypedSpec.Range query × S),
      result ∈ support ((typed query).run before) →
      counter result.2 = counter before + (RegistrationNativeSecretWordTargetCounter.isAccept query).toNat)
    (serverKeyId : U64)

noncomputable abbrev native : QueryImpl RegistrationNativeInterface.Spec (StateT (S) ProbComp) :=
  RegistrationNativeRawAdapter.handler wire typed

private theorem send_increment (wire : Wire) (query : RegistrationNativeInterface.Spec.Domain)
    (restricted : PqxdhDeploymentSecrecy.coinOrSend (RegistrationNativeInterface.eraseCore query) ≠ false) :
    RegistrationNativeRegistrationTargetRawCounter.increment wire query = 0 := by
  cases query with
  | inl coin => rfl
  | inr command =>
      cases command <;> simp_all [RegistrationNativeRegistrationTargetRawCounter.increment,
        PqxdhDeploymentSecrecy.coinOrSend, RegistrationNativeInterface.eraseCore,
        RegistrationNativeInterface.eraseCommand]

include step in
/-- The actual source interpretation of any coins-and-sends AST keeps the parsed-call counter. -/
theorem restricted_counter (work : OracleComp RegistrationNativeInterface.Spec Value)
    (bounded : work.IsQueryBoundP
      (fun query => PqxdhDeploymentSecrecy.coinOrSend (RegistrationNativeInterface.eraseCore query) = false) 0)
    (before : S) (result : Value × S)
    (reached : result ∈ support ((simulateQ (native wire typed) work).run before)) :
    counter result.2 = counter before := by
  induction work using OracleComp.inductionOn generalizing before result with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at reached
      subst result
      rfl
  | query_bind query next ih =>
      rw [isQueryBoundP_query_bind_iff] at bounded
      obtain ⟨allowed, rest⟩ := bounded
      have restricted := allowed.resolve_right (by omega)
      rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at reached
      obtain ⟨middle, first, tail⟩ := reached
      have stepped := RegistrationNativeRegistrationTargetRawCounter.raw_counter wire typed counter step query before middle first
      rw [send_increment wire query restricted, Nat.add_zero] at stepped
      exact (ih middle.1 (by simpa using rest middle.1) middle.2 result tail).trans stepped

private theorem ledger_trace (crypto : Pqxdh.Crypto) (wire : Wire) (serverKeyId : U64) (bounds : FreshBounds)
    (query : RegistrationNativeInterface.FullSpec.Domain) (before : RegistrationNativeLedger.State)
    (result : RegistrationNativeInterface.FullSpec.Range query × RegistrationNativeLedger.State)
    (supported : result ∈ support ((RegistrationNativeLedger.handler crypto (RegistrationNativeWire.ledgerCodec wire)
      serverKeyId bounds query).run before)) :
    result.2.transcript = before.transcript ++ [⟨query, result.1⟩] := by
  cases query with
  | inl query =>
      rw [RegistrationNativeLedger.query_forward, support_map] at supported
      obtain ⟨reply, _reached, rfl⟩ := supported
      rfl
  | inr query =>
      rw [RegistrationNativeLedger.query_secrecy, support_map] at supported
      obtain ⟨reply, _reached, rfl⟩ := supported
      rfl

include step in
/-- The literal original secrecy step never advances the parsed-call counter, even when its eventual send is refused. -/
theorem secrecy_counter (bounds : FreshBounds) (query : PqxdhDeploymentInterface.Secrecy)
    (before : RegistrationNativeLedger.State × S)
    (result : Option RawCtxSourceSend.Encrypted × (RegistrationNativeLedger.State × S))
    (reached : result ∈ support ((RegistrationNativeFullCompiler.handler crypto wire
      serverKeyId bounds
      (typed)
      (.inr query)).run before)) : counter result.2.2 = counter before.2 := by
  rw [RegistrationNativeFullCompiler.handler, RegistrationNativeLedger.interpreted,
    QueryImpl.flattenStateT_mapStateTBase_apply_run, support_map] at reached
  obtain ⟨inner, supported, rfl⟩ := reached
  exact restricted_counter wire typed counter step _
    (RegistrationNativeLedger.secrecy_frame crypto (RegistrationNativeWire.ledgerCodec wire)
      serverKeyId bounds query before.1) before.2 inner supported

include step in
/-- Each complete original full-interface step preserves the counter-to-public-prefix equation. -/
theorem step_counter (bounds : FreshBounds) (query : RegistrationNativeInterface.FullSpec.Domain) (offset : Nat)
    (before : RegistrationNativeLedger.State × S)
    (prior : counter before.2 = offset + parsedAcceptCount wire before.1.transcript)
    (result : RegistrationNativeInterface.FullSpec.Range query × (RegistrationNativeLedger.State × S))
    (reached : result ∈ support ((RegistrationNativeFullCompiler.handler crypto wire
      serverKeyId bounds
      (typed) query).run before)) :
    counter result.2.2 = offset + parsedAcceptCount wire result.2.1.transcript := by
  cases query with
  | inl query =>
      rw [RegistrationNativeFullCompiler.handler, RegistrationNativeLedger.interpreted,
        QueryImpl.flattenStateT_mapStateTBase_apply_run] at reached
      simp only [RegistrationNativeLedger.query_forward, simulateQ_map, simulateQ_spec_query,
        StateT.run_map, Functor.map_map, support_map] at reached
      obtain ⟨inner, supported, rfl⟩ := reached
      have counted := RegistrationNativeRegistrationTargetRawCounter.raw_counter wire typed counter step query before.2 inner supported
      rw [RegistrationNativeRegistrationTargetRawCounter.entry_increment wire query inner.1, prior] at counted
      cases chosen : parsedAccept wire ⟨.inl query, inner.1⟩ <;>
        simpa [RegistrationNativeLedger.record, parsedAcceptCount, List.filter_append,
          chosen, Bool.toNat, Nat.add_assoc] using counted
  | inr query =>
      have unchanged := secrecy_counter crypto wire typed counter step serverKeyId bounds query before result reached
      rw [RegistrationNativeFullCompiler.handler, RegistrationNativeLedger.interpreted,
        QueryImpl.flattenStateT_mapStateTBase_apply_run, support_map] at reached
      obtain ⟨inner, supported, equal⟩ := reached
      have localSupport := OracleComp.support_simulateQ_run'_subset
        (native wire typed)
        ((RegistrationNativeLedger.handler crypto (RegistrationNativeWire.ledgerCodec wire)
          serverKeyId bounds (.inr query)).run before.1) before.2
      have original : inner.1 ∈ support ((RegistrationNativeLedger.handler crypto
          (RegistrationNativeWire.ledgerCodec wire) serverKeyId bounds (.inr query)).run before.1) := by
        apply localSupport
        rw [StateT.run'_eq, support_map]
        exact Set.mem_image_of_mem Prod.fst supported
      have appended := ledger_trace crypto wire serverKeyId bounds (.inr query) before.1 inner.1 original
      cases equal
      simpa only [appended, parsedAcceptCount, List.filter_append, parsedAccept, List.filter_cons,
        List.filter_nil, Bool.false_eq_true, ite_false, List.append_nil] using unchanged.trans prior

/-- Ordinary raw entries are logged outside their actual native callback, retaining its full poststate. -/
theorem core_run (bounds : FreshBounds) (query : RegistrationNativeInterface.Spec.Domain)
    (before : RegistrationNativeLedger.State × S) :
    (RegistrationNativeFullCompiler.handler crypto wire serverKeyId bounds
      (typed)
      (.inl query)).run before =
      (fun result => (result.1, (RegistrationNativeLedger.record before.1 ⟨.inl query, result.1⟩, result.2))) <$>
        (native wire typed query).run before.2 := by
  rcases before with ⟨ledger, sourceBefore⟩
  simp only [RegistrationNativeFullCompiler.handler, RegistrationNativeLedger.interpreted,
    QueryImpl.flattenStateT_mapStateTBase_apply_run, RegistrationNativeLedger.query_forward,
    simulateQ_map, simulateQ_spec_query, StateT.run_map, Functor.map_map]
  rfl

/-- Every supported full step appends exactly its original native query and reply. -/
theorem step_trace (bounds : FreshBounds) (query : RegistrationNativeInterface.FullSpec.Domain)
    (before : RegistrationNativeLedger.State × S)
    (result : RegistrationNativeInterface.FullSpec.Range query × (RegistrationNativeLedger.State × S))
    (reached : result ∈ support ((RegistrationNativeFullCompiler.handler crypto wire
      serverKeyId bounds
      (typed) query).run before)) :
    result.2.1.transcript = before.1.transcript ++ [⟨query, result.1⟩] := by
  rw [RegistrationNativeFullCompiler.handler, RegistrationNativeLedger.interpreted,
    QueryImpl.flattenStateT_mapStateTBase_apply_run, support_map] at reached
  obtain ⟨inner, supported, rfl⟩ := reached
  apply ledger_trace crypto wire serverKeyId bounds query before.1 inner.1
  apply OracleComp.support_simulateQ_run'_subset
    (native wire typed) _ before.2
  rw [StateT.run'_eq, support_map]
  exact Set.mem_image_of_mem Prod.fst supported

end BeaconcryptCore.Computational.RegistrationNativeRegistrationTargetLedgerCounter

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeRegistrationTargetLedgerCounter.restricted_counter' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeRegistrationTargetLedgerCounter.restricted_counter

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeRegistrationTargetLedgerCounter.secrecy_counter' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeRegistrationTargetLedgerCounter.secrecy_counter

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeRegistrationTargetLedgerCounter.step_counter' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeRegistrationTargetLedgerCounter.step_counter

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeRegistrationTargetLedgerCounter.core_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeRegistrationTargetLedgerCounter.core_run

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeRegistrationTargetLedgerCounter.step_trace' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeRegistrationTargetLedgerCounter.step_trace
