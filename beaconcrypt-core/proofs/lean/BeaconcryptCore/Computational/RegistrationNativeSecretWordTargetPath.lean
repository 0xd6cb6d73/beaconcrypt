-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetLedger

/-! A supported original full-ledger execution supplies a chronological path of its actual complete step states. Cuts retain both source states and the same supported suffix; acceptance and later build receipts can therefore be related in one execution. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetPath
open RegistrationNativeInterface (Entry FullSpec)
variable {NativeState Value : Type}

inductive Path (implementation : QueryImpl FullSpec (StateT NativeState ProbComp)) :
    NativeState → List Entry → NativeState → Prop
  | nil (before : NativeState) : Path implementation before [] before
  | cons (query : FullSpec.Domain) (reply : FullSpec.Range query) (before middle after : NativeState)
      (tail : List Entry) (called : (reply, middle) ∈ support ((implementation query).run before))
      (later : Path implementation middle tail after) :
      Path implementation before (⟨query, reply⟩ :: tail) after

/-- Every supported complete adaptive execution has a path of its literal supported calls. -/
theorem program (implementation : QueryImpl FullSpec (StateT NativeState ProbComp))
    (work : OracleComp FullSpec Value) (before : NativeState) (result : Value × NativeState)
    (supported : result ∈ support ((simulateQ implementation work).run before)) :
    ∃ entries, Path implementation before entries result.2 := by
  induction work using OracleComp.inductionOn generalizing before result with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at supported
      cases supported
      exact ⟨[], .nil before⟩
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at supported
      obtain ⟨⟨reply, middle⟩, called, later⟩ := supported
      obtain ⟨tail, path⟩ := ih reply middle result later
      exact ⟨⟨query, reply⟩ :: tail, .cons query reply before middle result.2 tail called path⟩

/-- A local invariant may be transported along the same actual path, including its intermediate cut states. -/
theorem preserves (implementation : QueryImpl FullSpec (StateT NativeState ProbComp))
    (valid : NativeState → Prop)
    (step : ∀ query before result, valid before →
      result ∈ support ((implementation query).run before) → valid result.2)
    {before after : NativeState} {entries : List Entry}
    (path : Path implementation before entries after) (initial : valid before) : valid after := by
  induction path with
  | nil before => exact initial
  | cons query reply before middle after tail called later ih => exact ih (step query before (reply, middle) initial called)

/-- The path records exactly the original ordered transcript when each complete call appends its own literal entry. -/
theorem records (implementation : QueryImpl FullSpec (StateT NativeState ProbComp))
    (transcript : NativeState → List Entry)
    (step : ∀ query before result, result ∈ support ((implementation query).run before) →
      transcript result.2 = transcript before ++ [⟨query, result.1⟩])
    {before after : NativeState} {entries : List Entry} (path : Path implementation before entries after) :
    transcript after = transcript before ++ entries := by
  induction path with
  | nil before => exact (List.append_nil _).symm
  | cons query reply before middle after tail called later ih =>
      rw [ih, step query before (reply, middle) called, List.append_assoc]
      rfl

/-- Every chosen transcript position has the same actual prefix state, single call and supported suffix. -/
theorem split (implementation : QueryImpl FullSpec (StateT NativeState ProbComp))
    {before after : NativeState} {entries : List Entry}
    (path : Path implementation before entries after) (pre : List Entry) (entry : Entry) (post : List Entry)
    (recorded : entries = pre ++ entry :: post) :
    ∃ first last, Path implementation before pre first ∧
      (entry.reply, last) ∈ support ((implementation entry.query).run first) ∧
      Path implementation last post after := by
  induction pre generalizing before entries with
  | nil =>
      cases path with
      | nil before => simp at recorded
      | cons query reply before middle after tail called later =>
          simp only [List.nil_append, List.cons.injEq] at recorded
          cases recorded.1
          cases recorded.2
          exact ⟨before, middle, .nil before, called, later⟩
  | cons head rest ih =>
      cases path with
      | nil before => simp at recorded
      | cons query reply before middle after tail called later =>
          simp only [List.cons_append, List.cons.injEq] at recorded
          obtain ⟨rfl, recorded⟩ := recorded
          obtain ⟨first, last, priorPath, selected, suffix⟩ := ih later recorded
          exact ⟨first, last, .cons query reply before middle first rest called priorPath, selected, suffix⟩
end BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetPath
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetPath.program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetPath.program
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetPath.preserves' does not depend on any axioms -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetPath.preserves
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetPath.split' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetPath.split

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetPath.records' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetPath.records
