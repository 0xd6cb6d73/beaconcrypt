-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorPrefix
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorSource
import BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxSource

/-! The operational marker program has no omitted-signature or template marker before the public bundle position is armed. It is literally the original indexed source language with the checked known-input recorder. All source replies, including missing keys and failed signing calls, remain unchanged. -/
open OracleComp OracleSpec
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityCensorOperationalPrefix
open RegistrationNativeIdentityCensorCompiler (Mode)
open RegistrationNativeIdentityCensorPrefix (SourceSpec Unarmed record next)
open PqxdhEd25519EufCma (Ed25519Signature)
variable {A : Type}

private theorem hash_run (selected : Nat) (placeholder : Ed25519Signature) (bytes : Pqxdh.Bytes) (before : Mode) :
    (RegistrationNativeIdentityCensorOperational.implementation selected placeholder (.inr bytes)).run before =
      (match (RegistrationNativeIdentityCensorCompiler.hashInput before bytes).input with
      | some _ => (RegistrationNativeIdentityCensorOperational.promote
          (RegistrationNativeIdentityCensorCompiler.implementation selected placeholder (.inr bytes))).run before
      | none => do
          let reply ← (RegistrationNativeIdentityCensorOperational.Spec.query (.inr (.template selected before.target
            (RegistrationNativeIdentityCensorOperational.parts bytes).1 (RegistrationNativeIdentityCensorOperational.parts bytes).2)) :
            OracleComp RegistrationNativeIdentityCensorOperational.Spec (CtxRomAuth.CtxDigest × Nat))
          pure (reply, before)) := rfl

private theorem promote_run (work : StateT Mode (OracleComp RegistrationNativeIdentityCensorCompiler.Spec) A) (before : Mode) :
    (RegistrationNativeIdentityCensorOperational.promote work).run before =
      simulateQ RegistrationNativeIdentityCensorOperational.embed (work.run before) := rfl

private theorem promoted (selected : Nat) (placeholder : Ed25519Signature) (query : SourceSpec.Domain)
    (before : Mode) (prior : Unarmed before) :
    (RegistrationNativeIdentityCensorOperational.implementation selected placeholder query).run before =
      simulateQ RegistrationNativeIdentityCensorOperational.embed
        ((RegistrationNativeIdentityCensorCompiler.implementation selected placeholder query).run before) := by
  cases query with
  | inr bytes =>
    rw [hash_run]
    simp only [RegistrationNativeIdentityCensorCompiler.hashInput, prior.2.2, Bool.false_eq_true, ite_false]
    rfl
  | inl query => cases query with
    | inr report => rfl
    | inl query => cases query with
      | inl coin => rfl
      | inr query => cases query with
        | create | reveal handle => rfl
        | service handle request => cases request with
          | staticDh peer => rfl
          | sign message =>
            rcases before with ⟨bundles, armed, active, target, inputs⟩
            change armed = false ∧ target = none ∧ active = false at prior
            rcases prior with ⟨rfl, rfl, rfl⟩
            have prepared : (RegistrationNativeIdentityCensorCompiler.prepare selected handle message).run
                ⟨bundles, false, false, none, inputs⟩ = pure ((), ⟨bundles, false, false, none, inputs⟩) := by
              by_cases eligible : handle = selected ∧ RegistrationNativeIdentitySigningRole.oneTime message
              · simp [RegistrationNativeIdentityCensorCompiler.prepare, StateT.run, eligible]
              · simp [RegistrationNativeIdentityCensorCompiler.prepare, StateT.run, eligible]
            have missing : ¬ (none : Option Pqxdh.Bytes) = some message := by intro impossible; cases impossible
            change (RegistrationNativeIdentityCensorOperational.signing selected handle message).run _ =
              simulateQ RegistrationNativeIdentityCensorOperational.embed
                ((RegistrationNativeIdentityCensorCompiler.signing selected placeholder handle message).run _)
            simp only [RegistrationNativeIdentityCensorOperational.signing,
              RegistrationNativeIdentityCensorCompiler.signing,
              StateT.run_bind, promote_run,
              prepared, simulateQ_pure, pure_bind, StateT.run_get]
            simp only [missing, and_false, ite_false]
            rfl

/-- Every actual unarmed indexed query has the original literal known-input recorder tree, with no source-secret marker. -/
theorem query (selected : Nat) (placeholder : Ed25519Signature) (request : SourceSpec.Domain)
    (before : Mode) (prior : Unarmed before) :
    (RegistrationNativeIdentityCensorOperational.implementation selected placeholder request).run before =
      simulateQ RegistrationNativeIdentityCensorOperational.embed ((record request).run before) := by
  rw [promoted selected placeholder request before prior,
    RegistrationNativeIdentityCensorPrefix.query selected placeholder request before prior]

private theorem next_unarmed (before : Mode) (prior : Unarmed before) (request : SourceSpec.Domain) : Unarmed (next before request) := by
  cases request <;> exact prior

/-- The complete adaptive unarmed prefix retains every literal original source query and reply under marker embedding. -/
theorem program (selected : Nat) (placeholder : Ed25519Signature) (work : OracleComp SourceSpec A)
    (before : Mode) (prior : Unarmed before) :
    (simulateQ (RegistrationNativeIdentityCensorOperational.implementation selected placeholder) work).run before =
      simulateQ RegistrationNativeIdentityCensorOperational.embed ((simulateQ record work).run before) := by
  induction work using OracleComp.inductionOn generalizing before with
  | pure value => rfl
  | query_bind request continued ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
    rw [query selected placeholder request before prior]
    simp only [record, StateT.run, simulateQ_bind, bind_assoc, pure_bind, simulateQ_pure]
    exact bind_congr (fun reply => ih reply (next before request) (next_unarmed before prior request))


private def recorder : QueryImpl SourceSpec (StateT Mode (OracleComp RegistrationNativeIdentityCensorOperational.Spec)) :=
  fun request before => simulateQ RegistrationNativeIdentityCensorOperational.embed ((record request).run before)

private theorem recorder_run (request : SourceSpec.Domain) (before : Mode) :
    (recorder request).run before = simulateQ RegistrationNativeIdentityCensorOperational.embed ((record request).run before) := rfl

private theorem recorder_program (work : OracleComp SourceSpec A) (before : Mode) :
    (simulateQ recorder work).run before =
      simulateQ RegistrationNativeIdentityCensorOperational.embed ((simulateQ record work).run before) := by
  induction work using OracleComp.inductionOn generalizing before with
  | pure value => rfl
  | query_bind request next ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
    rw [recorder_run]
    simp only [record, StateT.run, simulateQ_bind, bind_assoc, pure_bind, simulateQ_pure]
    exact bind_congr (fun reply => ih reply _)

private noncomputable def closed (joint : PqxdhJointIdentity.Primitives) (selected : Nat)
    (placeholder : Ed25519Signature) (censored : Bool) :
    QueryImpl SourceSpec (StateT (Mode × RegistrationNativeIdentityCensorSource.State) ProbComp) :=
  QueryImpl.Stateful.link recorder
    (if censored then RegistrationNativeIdentityCensorSource.censored joint selected placeholder
      else RegistrationNativeIdentityCensorSource.implementation joint selected)

def project (before : Mode × RegistrationNativeIdentityCensorSource.State) : RegistrationNativePlatformIdentityCtxSource.State :=
  (before.2.pool, before.2.hash)

private theorem map_apply {S X Y : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (change : X → Y) (work : StateT S m X) (before : S) :
    (change <$> work) before = Prod.map change id <$> work before := StateT.run_map change work before

private theorem source_query (joint : PqxdhJointIdentity.Primitives) (selected : Nat)
    (placeholder : Ed25519Signature) (censored : Bool) (request : SourceSpec.Domain)
    (before : Mode × RegistrationNativeIdentityCensorSource.State) :
    Prod.map id project <$> (closed joint selected placeholder censored request).run before =
      (RegistrationNativePlatformIdentityCtxSource.implementation joint request).run (project before) := by
  rw [closed, QueryImpl.Stateful.link_impl_apply_run]
  cases request with
  | inl query => cases censored <;>
    simp only [recorder, record, StateT.run, bind_pure_comp, simulateQ_map, Bool.false_eq_true, ite_false, ite_true,
      RegistrationNativeIdentityCensorPrefix.embed, RegistrationNativeIdentityCensorCompiler.protocol,
      simulateQ_spec_query, RegistrationNativeIdentityCensorOperational.embed,
      RegistrationNativeIdentityCensorSource.censored, RegistrationNativeIdentityCensorSource.implementation,
      RegistrationNativeIdentityCensorSource.protocol,
      RegistrationNativePlatformIdentityCtxSource.implementation,
      map_apply, Functor.map_map, Prod.map_def, id_eq, project] <;> rfl
  | inr bytes => cases censored <;>
    simp only [recorder, record, StateT.run, bind_pure_comp, simulateQ_map, Bool.false_eq_true, ite_false, ite_true,
      RegistrationNativeIdentityCensorPrefix.embed, simulateQ_spec_query, RegistrationNativeIdentityCensorOperational.embed,
      RegistrationNativeIdentityCensorSource.censored, RegistrationNativeIdentityCensorSource.implementation,
      RegistrationNativeIdentityCensorSource.physical,
      RegistrationNativePlatformIdentityCtxSource.implementation,
      map_apply, Functor.map_map, Prod.map_def, id_eq, project] <;> rfl

/-- Closing the entire legal unarmed prefix erases only recorder/marker ghost fields and recovers the literal original native source pool, physical cache/journal and replies. -/
theorem source (joint : PqxdhJointIdentity.Primitives) (selected : Nat) (placeholder : Ed25519Signature)
    (censored : Bool) (work : OracleComp SourceSpec A) (before : Mode × RegistrationNativeIdentityCensorSource.State)
    (prior : Unarmed before.1) :
    Prod.map id project <$>
      (simulateQ (QueryImpl.Stateful.link (RegistrationNativeIdentityCensorOperational.implementation selected placeholder)
        (if censored then RegistrationNativeIdentityCensorSource.censored joint selected placeholder
          else RegistrationNativeIdentityCensorSource.implementation joint selected)) work).run before =
      (simulateQ (RegistrationNativePlatformIdentityCtxSource.implementation joint) work).run (project before) := by
  have actual := QueryImpl.Stateful.simulateQ_link_run
    (RegistrationNativeIdentityCensorOperational.implementation selected placeholder)
    (if censored then RegistrationNativeIdentityCensorSource.censored joint selected placeholder
      else RegistrationNativeIdentityCensorSource.implementation joint selected) work before.1 before.2
  have recorded := QueryImpl.Stateful.simulateQ_link_run recorder
    (if censored then RegistrationNativeIdentityCensorSource.censored joint selected placeholder
      else RegistrationNativeIdentityCensorSource.implementation joint selected) work before.1 before.2
  rw [program selected placeholder work before.1 prior] at actual
  rw [recorder_program] at recorded
  rw [actual, ← recorded]
  exact OracleComp.map_run_simulateQ_eq_of_query_map_eq _ _ project
    (source_query joint selected placeholder censored) work before

end BeaconcryptCore.Computational.RegistrationNativeIdentityCensorOperationalPrefix

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorOperationalPrefix.query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorOperationalPrefix.query

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorOperationalPrefix.program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorOperationalPrefix.program

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorOperationalPrefix.source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorOperationalPrefix.source
