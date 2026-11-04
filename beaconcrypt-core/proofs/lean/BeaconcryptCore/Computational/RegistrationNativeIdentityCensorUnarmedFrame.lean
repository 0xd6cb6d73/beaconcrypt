-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorUnarmedMain

/-! Before the fixed public bundle is armed, source interpretation preserves the complete public control and private selection metadata. Physical cache, chronological inputs and ordinary source rows remain actual mutable state. -/
open OracleComp OracleSpec
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityCensorUnarmedFrame
open RegistrationNativeIdentityCensorCompiler (Mode)
open RegistrationNativeIdentityCensorPrefix (SourceSpec Unarmed)
open PqxdhEd25519EufCma (Ed25519Signature)
abbrev Private := RegistrationNativeIdentityCensorSource.State
variable {A : Type}

noncomputable def closed (joint : PqxdhJointIdentity.Primitives) (selected : Nat) (placeholder : Ed25519Signature) (masked : Bool) :
    QueryImpl SourceSpec (StateT (Mode × Private) ProbComp) :=
  QueryImpl.Stateful.link (RegistrationNativeIdentityCensorOperational.implementation selected placeholder)
    (if masked then RegistrationNativeIdentityCensorSource.censored joint selected placeholder
      else RegistrationNativeIdentityCensorSource.implementation joint selected)

def snapshot (before : Mode × Private) :=
  ({before.1 with knownInputs := []}, (before.2.target, before.2.canonical, before.2.framing))

private def restore (before : Mode × Private) (query : SourceSpec.Domain)
    (after : RegistrationNativePlatformIdentityCtxSource.State) : Mode × Private :=
  (RegistrationNativeIdentityCensorPrefix.next before.1 query, {before.2 with pool := after.1, hash := after.2})

private theorem map_apply {State X Y : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (change : X → Y) (work : StateT State m X) (before : State) :
    (change <$> work) before = Prod.map change id <$> work before := StateT.run_map change work before

private theorem query_run (joint : PqxdhJointIdentity.Primitives) (selected : Nat) (placeholder : Ed25519Signature)
    (masked : Bool) (query : SourceSpec.Domain) (before : Mode × Private) (prior : Unarmed before.1) :
    (closed joint selected placeholder masked query).run before =
      (fun result => (result.1, restore before query result.2)) <$>
        (RegistrationNativePlatformIdentityCtxSource.implementation joint query).run (before.2.pool, before.2.hash) := by
  rw [closed, QueryImpl.Stateful.link_impl_apply_run,
    RegistrationNativeIdentityCensorOperationalPrefix.query selected placeholder query before.1 prior]
  cases query with
  | inl query =>
    cases masked <;>
      simp only [RegistrationNativeIdentityCensorOperational.embed, RegistrationNativeIdentityCensorPrefix.record,
        RegistrationNativeIdentityCensorPrefix.embed, RegistrationNativeIdentityCensorCompiler.protocol,
        simulateQ_spec_query, simulateQ_map, StateT.run, map_apply,
        Bool.false_eq_true, ite_false, ite_true,
        RegistrationNativeIdentityCensorSource.censored, RegistrationNativeIdentityCensorSource.implementation,
        RegistrationNativeIdentityCensorSource.protocol, RegistrationNativePlatformIdentityCtxSource.implementation,
        bind_pure_comp, Functor.map_map, restore] <;> rfl
  | inr bytes =>
    cases masked <;>
      simp only [RegistrationNativeIdentityCensorOperational.embed, RegistrationNativeIdentityCensorPrefix.record,
        RegistrationNativeIdentityCensorPrefix.embed, simulateQ_spec_query, simulateQ_map, StateT.run, map_apply,
        Bool.false_eq_true, ite_false, ite_true,
        RegistrationNativeIdentityCensorSource.censored, RegistrationNativeIdentityCensorSource.implementation,
        RegistrationNativeIdentityCensorSource.physical, RegistrationNativePlatformIdentityCtxSource.implementation,
        bind_pure_comp, Functor.map_map, restore] <;> rfl

/-- One unarmed source operation preserves all selection/control fields while retaining its actual physical and ordinary source updates. -/
theorem query (joint : PqxdhJointIdentity.Primitives) (selected : Nat) (placeholder : Ed25519Signature)
    (masked : Bool) (request : SourceSpec.Domain) (before : Mode × Private) (prior : Unarmed before.1)
    (result : SourceSpec.Range request × (Mode × Private))
    (reached : result ∈ support ((closed joint selected placeholder masked request).run before)) :
    snapshot result.2 = snapshot before ∧ Unarmed result.2.1 := by
  rw [query_run joint selected placeholder masked request before prior, support_map] at reached
  obtain ⟨actual, _called, rfl⟩ := reached
  cases request <;> exact ⟨rfl, prior⟩

/-- The entire adaptive preselection tree preserves the same unarmed control and private target/canonical/framing fields. -/
theorem program (joint : PqxdhJointIdentity.Primitives) (selected : Nat) (placeholder : Ed25519Signature)
    (masked : Bool) (work : OracleComp SourceSpec A) (before : Mode × Private) (prior : Unarmed before.1)
    (result : A × (Mode × Private))
    (reached : result ∈ support ((simulateQ (closed joint selected placeholder masked) work).run before)) :
    snapshot result.2 = snapshot before ∧ Unarmed result.2.1 := by
  induction work using OracleComp.inductionOn generalizing before result with
  | pure value =>
    simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at reached
    cases reached
    exact ⟨rfl, prior⟩
  | query_bind request next ih =>
    rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at reached
    obtain ⟨middle, first, rest⟩ := reached
    have frame := query joint selected placeholder masked request before prior middle first
    have later := ih middle.1 middle.2 frame.2 result rest
    exact ⟨later.1.trans frame.1, later.2⟩

private theorem lower_program (joint : PqxdhJointIdentity.Primitives) (selected : Nat) (placeholder : Ed25519Signature)
    (masked : Bool) (work : OracleComp SourceSpec A) (mode : Mode) (before : Private) (prior : Unarmed mode)
    (result : (A × Mode) × Private)
    (reached : result ∈ support ((simulateQ (if masked then RegistrationNativeIdentityCensorSource.censored joint selected placeholder
      else RegistrationNativeIdentityCensorSource.implementation joint selected)
      ((simulateQ (RegistrationNativeIdentityCensorOperational.implementation selected placeholder) work).run mode)).run before)) :
    snapshot (result.1.2, result.2) = snapshot (mode, before) ∧ Unarmed result.1.2 := by
  have supported : (result.1.1, (result.1.2, result.2)) ∈ support
      ((simulateQ (closed joint selected placeholder masked) work).run (mode, before)) := by
    rw [closed, QueryImpl.Stateful.simulateQ_link_run, support_map]
    exact ⟨result, reached, rfl⟩
  exact program joint selected placeholder masked work (mode, before) prior (result.1.1, (result.1.2, result.2)) supported

section Main
open RegistrationNativeIdentityCensorEdOutgoingSource (Full interpret)
variable {n : Nat} {KemSK Platform : Type} {mlSource : RegistrationNativeMldsa.Source}

/-- Arbitrary actual Main/P computation before arming retains all public controls and private selection metadata, while physical state and ordinary source transcripts may advance. -/
theorem main (joint : PqxdhJointIdentity.Primitives) (selected : Nat) (placeholder : Ed25519Signature)
    (masked : Bool) (work : RegistrationNativePlatformIdentityCtxMain.M n KemSK Platform mlSource A)
    (before : Full (n := n) (KemSK := KemSK) (Platform := Platform) (mlSource := mlSource)) (prior : Unarmed before.1.2)
    (result : A × Full (n := n) (KemSK := KemSK) (Platform := Platform) (mlSource := mlSource))
    (reached : result ∈ support ((interpret joint selected placeholder masked work).run before)) :
    snapshot (result.2.1.2, result.2.2) = snapshot (before.1.2, before.2) ∧ Unarmed result.2.1.2 := by
  simp only [interpret, StateT.run, bind_pure_comp, support_map] at reached
  obtain ⟨actual, called, rfl⟩ := reached
  exact lower_program joint selected placeholder masked (work.run before.1.1) before.1.2 before.2 prior actual called
end Main

end BeaconcryptCore.Computational.RegistrationNativeIdentityCensorUnarmedFrame

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorUnarmedFrame.query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorUnarmedFrame.query

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorUnarmedFrame.program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorUnarmedFrame.program

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorUnarmedFrame.main' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorUnarmedFrame.main
