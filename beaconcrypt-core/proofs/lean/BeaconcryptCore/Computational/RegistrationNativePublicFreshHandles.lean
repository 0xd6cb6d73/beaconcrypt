-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeCanonicalSelector

/-! Fresh-handle metadata is reconstructed from the public request transcript and the public bounds. Admission depends only on the requested length, including when the corresponding native send fails. Every supported wrapped native execution therefore computes the canonical selector from native mode-P observations alone. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePublicFreshHandles
open RegistrationNativeInterface (Entry FullSpec)
open RegistrationNativeLedgerHiding (PublicEntry view)
open PqxdhDeploymentInterface (FreshBounds Secrecy Handle)
variable {Reader Response Value NativeState : Type}

def entryHandle (bounds : FreshBounds) : PublicEntry → Option Handle
  | ⟨.inr (.fresh handle length), _⟩ => if bounds.min ≤ length ∧ length ≤ bounds.max then some handle else none
  | _ => none

def handles (bounds : FreshBounds) (transcript : List PublicEntry) : List Handle := transcript.filterMap (entryHandle bounds)

def Consistent (bounds : FreshBounds) (ledger : RegistrationNativeLedger.State) : Prop :=
  ledger.ledger.fresh.map PqxdhDeploymentSecrecy.FreshEntry.handle = handles bounds (ledger.transcript.map view)

private theorem simulate_support {SourceIndex TargetIndex Result : Type}
    {sourceSpec : OracleSpec SourceIndex} {targetSpec : OracleSpec TargetIndex}
    (implementation : QueryImpl sourceSpec (OracleComp targetSpec)) (work : OracleComp sourceSpec Result) (result : Result)
    (supported : result ∈ support (simulateQ implementation work)) : result ∈ support work := by
  induction work using OracleComp.inductionOn with
  | pure value => simpa only [simulateQ_pure, mem_support_pure_iff] using supported
  | query_bind query next ih =>
      rw [simulateQ_bind, simulateQ_spec_query, mem_support_bind_iff] at supported
      obtain ⟨reply, reached, tail⟩ := supported
      rw [mem_support_bind_iff]
      exact ⟨reply, mem_support_query query reply, ih reply tail⟩

/-- The original callback admits exactly the length-bounded requests; send failure does not remove the fresh entry. -/
theorem original (crypto : Pqxdh.Crypto) (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (serverKid : U64) (bounds : FreshBounds) (secrecy : Secrecy) (before : PqxdhDeploymentSecrecy.Ledger)
    (result : Option RawCtxSourceSend.Encrypted × PqxdhDeploymentSecrecy.Ledger)
    (supported : result ∈ support ((PqxdhDeploymentSecrecy.ledgerImpl crypto codec serverKid bounds (.inr secrecy)).run before)) :
    result.2.fresh.map PqxdhDeploymentSecrecy.FreshEntry.handle =
      before.fresh.map PqxdhDeploymentSecrecy.FreshEntry.handle ++ (entryHandle bounds (view ⟨.inr secrecy, result.1⟩)).toList := by
  classical
  cases secrecy with
  | test handle left right =>
      simp only [PqxdhDeploymentSecrecy.ledgerImpl, StateT.run] at supported
      split at supported
      · cases chosen : before.test with
        | none =>
            simp only [chosen, mem_support_bind_iff, mem_support_pure_iff] at supported
            obtain ⟨bit, _bit, reply, _reply, equal⟩ := supported
            cases equal
            simp only [view, entryHandle, Option.toList_none, List.append_nil, PqxdhDeploymentSecrecy.Ledger.record]
        | some session =>
            simp only [chosen] at supported
            split at supported
            · simp only [mem_support_bind_iff, mem_support_pure_iff] at supported
              obtain ⟨reply, _reply, equal⟩ := supported
              cases equal
              simp only [view, entryHandle, Option.toList_none, List.append_nil, PqxdhDeploymentSecrecy.Ledger.record]
            · simp only [mem_support_pure_iff] at supported
              cases supported
              simp only [view, entryHandle, Option.toList_none, List.append_nil, PqxdhDeploymentSecrecy.Ledger.record]
      · simp only [mem_support_pure_iff] at supported
        cases supported
        simp only [view, entryHandle, Option.toList_none, List.append_nil, PqxdhDeploymentSecrecy.Ledger.record]
  | fresh handle length =>
      simp only [PqxdhDeploymentSecrecy.ledgerImpl, StateT.run] at supported
      split at supported
      · rename_i admitted
        simp only [mem_support_bind_iff, mem_support_pure_iff] at supported
        obtain ⟨message, _message, reply, _reply, equal⟩ := supported
        cases equal
        simp only [view, entryHandle]
        rw [ite_eq_left admitted]
        simp only [List.map_append, List.map_cons, List.map_nil, Option.toList_some]
      · rename_i rejected
        simp only [mem_support_pure_iff] at supported
        cases supported
        simp only [view, entryHandle, ite_eq_right rejected, Option.toList_none, List.append_nil, PqxdhDeploymentSecrecy.Ledger.record]

/-- Public requests preserve reconstruction under arbitrary replies, including failed native sends. -/
theorem query (crypto : Pqxdh.Crypto) (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (serverKid : U64) (bounds : FreshBounds) (request : FullSpec.Domain) (before : RegistrationNativeLedger.State)
    (consistent : Consistent bounds before) (result : FullSpec.Range request × RegistrationNativeLedger.State)
    (supported : result ∈ support ((RegistrationNativeLedger.handler crypto codec serverKid bounds request).run before)) :
    Consistent bounds result.2 := by
  cases request with
  | inl core =>
      rw [RegistrationNativeLedger.query_forward, support_map] at supported
      obtain ⟨reply, _reached, rfl⟩ := supported
      simp only [Consistent, RegistrationNativeLedger.record, List.map_append, List.map_cons, List.map_nil,
        handles, List.filterMap_append, List.filterMap_cons, List.filterMap_nil, view, entryHandle,
        List.append_nil] at consistent ⊢
      exact consistent
  | inr secrecy =>
      rw [RegistrationNativeLedger.query_secrecy, support_map] at supported
      obtain ⟨inner, reached, rfl⟩ := supported
      have recorded := original crypto codec serverKid bounds secrecy before.ledger inner
        (simulate_support RegistrationNativeLedger.legacyLift _ inner reached)
      simp only [Consistent, List.map_append, List.map_cons, List.map_nil, handles, List.filterMap_append,
        List.filterMap_cons, List.filterMap_nil, recorded]
      exact congrArg (fun previous => previous ++ (entryHandle bounds (view ⟨.inr secrecy, inner.1⟩)).toList) consistent

/-- Arbitrary adaptive wrapped clients retain exactly the public admitted-handle list. -/
theorem program (crypto : Pqxdh.Crypto) (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (serverKid : U64) (bounds : FreshBounds) (work : OracleComp FullSpec Value) (before : RegistrationNativeLedger.State)
    (consistent : Consistent bounds before) (result : Value × RegistrationNativeLedger.State)
    (supported : result ∈ support ((simulateQ (RegistrationNativeLedger.handler crypto codec serverKid bounds) work).run before)) :
    Consistent bounds result.2 := by
  induction work using OracleComp.inductionOn generalizing before result with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at supported
      subst result
      exact consistent
  | query_bind request next ih =>
      rw [simulateQ_bind, StateT.run_bind, simulateQ_spec_query, mem_support_bind_iff] at supported
      obtain ⟨inner, reached, tail⟩ := supported
      exact ih inner.1 inner.2 (query crypto codec serverKid bounds request before consistent inner reached) result tail

theorem wrap (crypto : Pqxdh.Crypto) (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (serverKid : U64) (bounds : FreshBounds) (work : OracleComp FullSpec Value) (result : Value × RegistrationNativeLedger.State)
    (supported : result ∈ support (RegistrationNativeLedger.wrap crypto codec serverKid bounds work)) :
    Consistent bounds result.2 :=
  program crypto codec serverKid bounds work RegistrationNativeLedger.empty rfl result supported

/-- The claim's indexed handle is reconstructed solely from native mode-P observations in every supported actual execution. -/
theorem run (crypto : Pqxdh.Crypto) (wire : RegistrationNativeWire.Wire) (serverKid : U64) (bounds : FreshBounds)
    (typed : QueryImpl RegistrationNativeRawAdapter.TypedSpec (StateT NativeState ProbComp)) (mode : PqxdhDeploymentInterface.Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value) (before : NativeState)
    (result : Value × (RegistrationNativeLedger.State × NativeState))
    (supported : result ∈ support (RegistrationNativeFullCompiler.run crypto wire serverKid bounds typed mode work before)) :
    Consistent bounds result.2.1 := by
  rw [RegistrationNativeFullCompiler.run, RegistrationNativeFullCompiler.handler, RegistrationNativeLedger.run_wrap, support_map] at supported
  obtain ⟨inner, reached, rfl⟩ := supported
  apply wrap crypto (RegistrationNativeWire.ledgerCodec wire) serverKid bounds (RegistrationNativeInterface.asModeO mode work) inner.1
  apply OracleComp.support_simulateQ_run'_subset (RegistrationNativeRawAdapter.handler wire typed) _ before
  rw [StateT.run'_eq, support_map]
  exact Set.mem_image_of_mem Prod.fst reached


noncomputable def choose (crypto : Pqxdh.Crypto) (wire : RegistrationNativeWire.Wire) (serverKid : U64)
    (bounds : FreshBounds) (budget : PqxdhDeploymentInterface.Budget) (index : Option Nat) (transcript : List PublicEntry) :
    Option (Fin budget.accept × Fin budget.capacity) :=
  RegistrationNativeCanonicalSelector.chooseFrom crypto wire serverKid budget index transcript (handles bounds transcript)

/-- On every supported run, no private ledger metadata is needed to compute the canonical target. -/
theorem choose_run (crypto : Pqxdh.Crypto) (wire : RegistrationNativeWire.Wire) (serverKid : U64) (bounds : FreshBounds)
    (typed : QueryImpl RegistrationNativeRawAdapter.TypedSpec (StateT NativeState ProbComp)) (mode : PqxdhDeploymentInterface.Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value) (before : NativeState)
    (result : Value × (RegistrationNativeLedger.State × NativeState))
    (supported : result ∈ support (RegistrationNativeFullCompiler.run crypto wire serverKid bounds typed mode work before))
    (budget : PqxdhDeploymentInterface.Budget) (index : Option Nat) :
    RegistrationNativeCanonicalSelector.chooseLedger crypto wire serverKid budget index result.2.1 =
      choose crypto wire serverKid bounds budget index (result.2.1.transcript.map view) := by
  have reconstructed := run crypto wire serverKid bounds typed mode work before result supported
  unfold RegistrationNativeCanonicalSelector.chooseLedger choose
  rw [reconstructed]

/-- The actual native selector is a function of the claim index and native mode-P transcript alone. The private fresh bytes and raw plaintext replies are absent. -/
theorem selected_run (crypto : Pqxdh.Crypto) (wire : RegistrationNativeWire.Wire) (serverKid : U64) (bounds : FreshBounds)
    (typed : QueryImpl RegistrationNativeRawAdapter.TypedSpec (StateT NativeState ProbComp)) (mode : PqxdhDeploymentInterface.Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value) (before : NativeState)
    (result : Value × (RegistrationNativeLedger.State × NativeState))
    (supported : result ∈ support (RegistrationNativeFullCompiler.run crypto wire serverKid bounds typed mode work before))
    (budget : PqxdhDeploymentInterface.Budget) (claim : Value → Option (Nat × Pqxdh.Bytes))
    (target : Fin budget.accept × Fin budget.capacity) :
    RegistrationNativeCanonicalSelector.selected crypto wire serverKid budget claim target result.1 result.2.1 =
      decide (choose crypto wire serverKid bounds budget ((claim result.1).map Prod.fst)
        (result.2.1.transcript.map view) = some target) := by
  unfold RegistrationNativeCanonicalSelector.selected
  rw [choose_run crypto wire serverKid bounds typed mode work before result supported budget ((claim result.1).map Prod.fst)]

end BeaconcryptCore.Computational.RegistrationNativePublicFreshHandles

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePublicFreshHandles.original' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePublicFreshHandles.original

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePublicFreshHandles.query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePublicFreshHandles.query

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePublicFreshHandles.program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePublicFreshHandles.program

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePublicFreshHandles.wrap' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePublicFreshHandles.wrap

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePublicFreshHandles.run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePublicFreshHandles.run

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePublicFreshHandles.choose_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePublicFreshHandles.choose_run

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePublicFreshHandles.selected_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePublicFreshHandles.selected_run
