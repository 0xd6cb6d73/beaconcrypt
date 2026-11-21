-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeParsedTarget
import BeaconcryptCore.Computational.RegistrationNativeFullCompiler

/-! The parsed target is bounded by the original raw accept allowance. This counts the original ledger entries, including malformed inputs and failed authentication, and derives the bound through the literal secrecy wrapper before any native reduction. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RegistrationNativeParsedTargetCaps
open RegistrationNativeInterface (Entry FullSpec queryClass ModeSpec asModeO Respects)
open RegistrationNativeEvents (parsedAccept parsedAcceptCount)
open RegistrationNativeWire (Wire)
open PqxdhDeploymentInterface (FreshBounds Mode Budget)
variable {Value NativeState Reader Response : Type}

def classCount (kind : Fin 14) (transcript : List Entry) : Nat :=
  transcript.countP fun entry => decide (queryClass entry.query = kind)

/-- A parsed accept is one original raw accept, independently of its success reply. -/
theorem parsed_le_accept (wire : Wire) (transcript : List Entry) :
    parsedAcceptCount wire transcript ≤ classCount 3 transcript := by
  induction transcript with
  | nil => exact Nat.le_refl 0
  | cons entry rest ih =>
      rcases entry with ⟨((coin | command) | secrecy), reply⟩
      · simpa [parsedAcceptCount, parsedAccept, classCount, queryClass,
          RegistrationNativeInterface.eraseQuery, RegistrationNativeInterface.eraseCore,
          PqxdhDeploymentInterface.queryClass] using ih
      · cases command <;>
          simp only [parsedAcceptCount, parsedAccept, List.filter_cons, classCount, List.countP_cons,
            queryClass, RegistrationNativeInterface.eraseQuery, RegistrationNativeInterface.eraseCore,
            RegistrationNativeInterface.eraseCommand, PqxdhDeploymentInterface.queryClass] at ih ⊢
        all_goals split_ifs <;> simp_all
        all_goals omega
      · cases secrecy <;>
          simpa [parsedAcceptCount, parsedAccept, classCount, queryClass,
            RegistrationNativeInterface.eraseQuery, PqxdhDeploymentInterface.queryClass] using ih

/-- The exact successful entry contributes one further raw accept after its parsed prefix. -/
theorem accepted_lt (wire : Wire) (transcript : List Entry) (session parsed : Nat)
    (accepted : RegistrationNativeParsedTarget.AcceptedAt wire transcript session parsed) :
    parsed < classCount 3 transcript := by
  obtain ⟨before, raw, packet, after, rfl, count, _read⟩ := accepted
  have bounded := parsed_le_accept wire before
  simp only [classCount, List.countP_append, List.countP_cons, queryClass,
    RegistrationNativeInterface.eraseQuery, RegistrationNativeInterface.eraseCore,
    RegistrationNativeInterface.eraseCommand, PqxdhDeploymentInterface.queryClass, decide_true,
    ite_true] at bounded ⊢
  omega

private theorem ledger_step (crypto : Pqxdh.Crypto) (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (serverKeyId : U64) (bounds : FreshBounds) (query : FullSpec.Domain)
    (before : RegistrationNativeLedger.State) (result : FullSpec.Range query × RegistrationNativeLedger.State)
    (reached : result ∈ support ((RegistrationNativeLedger.handler crypto codec serverKeyId bounds query).run before)) :
    result.2.transcript = before.transcript ++ [⟨query, result.1⟩] := by
  cases query with
  | inl core =>
      rw [RegistrationNativeLedger.query_forward, support_map] at reached
      obtain ⟨reply, _supported, rfl⟩ := reached
      rfl
  | inr secrecy =>
      rw [RegistrationNativeLedger.query_secrecy, support_map] at reached
      obtain ⟨reply, _supported, rfl⟩ := reached
      rfl

/-- Every class allowance bounds the original native transcript through the unchanged hidden-bit and fresh-message controllers. -/
theorem ledger_count (crypto : Pqxdh.Crypto) (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (serverKeyId : U64) (bounds : FreshBounds) (kind : Fin 14) (work : OracleComp FullSpec Value)
    (cap : Nat) (bounded : work.IsQueryBoundP (fun query => queryClass query = kind) cap)
    (before : RegistrationNativeLedger.State) (result : Value × RegistrationNativeLedger.State)
    (reached : result ∈ support ((simulateQ (RegistrationNativeLedger.handler crypto codec serverKeyId bounds) work).run before)) :
    classCount kind result.2.transcript ≤ classCount kind before.transcript + cap := by
  induction work using OracleComp.inductionOn generalizing cap before with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at reached
      subst reached
      exact Nat.le_add_right _ _
  | query_bind query next ih =>
      rw [isQueryBoundP_query_bind_iff] at bounded
      obtain ⟨allowed, rest⟩ := bounded
      rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at reached
      obtain ⟨middle, first, second⟩ := reached
      have appended := ledger_step crypto codec serverKeyId bounds query before middle first
      have later := ih middle.1 _ (rest middle.1) middle.2 second
      rw [appended] at later
      simp only [classCount, List.countP_append, List.countP_singleton] at later ⊢
      by_cases same : queryClass query = kind
      · have positive := allowed.resolve_left (fun absurd => absurd same)
        simp only [same, decide_true, ite_true] at later
        omega
      · simp only [same, decide_false, Bool.false_eq_true, ite_false] at later
        omega

/-- The actual full raw native execution has at most the adversary's original raw accept cap. -/
theorem run_accepts (crypto : Pqxdh.Crypto) (wire : Wire) (serverKeyId : U64) (bounds : FreshBounds)
    (typed : QueryImpl RegistrationNativeRawAdapter.TypedSpec (StateT NativeState ProbComp))
    (mode : Mode) (work : OracleComp (ModeSpec mode) Value) (budget : Budget) (bounded : Respects budget work)
    (before : NativeState) (result : Value × (RegistrationNativeLedger.State × NativeState))
    (supported : result ∈ support (RegistrationNativeFullCompiler.run crypto wire serverKeyId bounds typed mode work before)) :
    classCount 3 result.2.1.transcript ≤ budget.accept := by
  rw [RegistrationNativeFullCompiler.run, RegistrationNativeFullCompiler.handler,
    RegistrationNativeLedger.run_wrap, support_map] at supported
  obtain ⟨inner, reached, rfl⟩ := supported
  have wrapped : inner.1 ∈ support (RegistrationNativeLedger.wrap crypto (RegistrationNativeWire.ledgerCodec wire)
      serverKeyId bounds (asModeO mode work)) := by
    apply OracleComp.support_simulateQ_run'_subset (RegistrationNativeRawAdapter.handler wire typed) _ before
    rw [StateT.run'_eq, support_map]
    exact Set.mem_image_of_mem Prod.fst reached
  have counted := ledger_count crypto (RegistrationNativeWire.ledgerCodec wire) serverKeyId bounds 3
    (asModeO mode work) (budget.cap 3) (RegistrationNativeInterface.asModeO_bound budget work bounded 3)
    RegistrationNativeLedger.empty inner.1 wrapped
  simpa [classCount, RegistrationNativeLedger.empty, PqxdhDeploymentInterface.Budget.cap] using counted

end BeaconcryptCore.Computational.RegistrationNativeParsedTargetCaps

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeParsedTargetCaps.parsed_le_accept' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeParsedTargetCaps.parsed_le_accept
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeParsedTargetCaps.accepted_lt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeParsedTargetCaps.accepted_lt
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeParsedTargetCaps.ledger_count' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeParsedTargetCaps.ledger_count
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeParsedTargetCaps.run_accepts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeParsedTargetCaps.run_accepts
