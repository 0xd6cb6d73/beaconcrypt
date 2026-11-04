-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorTargetSync
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorRealSigning
import BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxOneTimeMessageHistory

/-! Within an armed source body, the selected wanted one-time message remains fresh while no target exists. Its actual signing request must select a target before any optional signature reply. -/
open OracleComp OracleSpec
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityCensorArmedFresh
open RegistrationNativeIdentityCensorCompiler (Mode)
open RegistrationNativeIdentityCensorSource (State)
open RegistrationNativeIdentityCensorOperational (Spec)
open RegistrationNativeIdentityCensorRealSigning (closed project)
open RegistrationNativePlatformIdentityCtxSigningHistoryFrame (poolMessages)
open PqxdhEd25519EufCma (Ed25519Signature)
variable {A : Type}
abbrev SourceSpec := RegistrationNativePlatformIdentityCtxCompiler.Spec

def Holds (selected : Nat) (wanted : Pqxdh.Bytes) (before : Mode × State) : Prop :=
  before.1.armed=true ∧ before.1.target=before.2.target ∧
    (before.2.target=none → wanted∉poolMessages selected before.2.pool)

private theorem source_none (joint : PqxdhJointIdentity.Primitives) (selected : Nat) (request : Spec.Domain)
    (before : State) (result : Spec.Range request × State)
    (supported : result ∈ support ((RegistrationNativeIdentityCensorSource.implementation joint selected request).run before))
    (missing : result.2.target=none) : before.target=none := by
  rw [RegistrationNativeIdentityCensorTargetSync.source_step joint selected request before result supported] at missing
  rcases request with (((protocol|message)|scanned)|hash)|marker
  · exact missing
  · cases chosen : result.1 <;> simp_all [RegistrationNativeIdentityCensorTargetSync.targetAfter]
  · exact missing
  · exact missing
  · exact missing

private theorem source_program_none (joint : PqxdhJointIdentity.Primitives) (selected : Nat)
    (work : OracleComp Spec A) (before : State) (result : A × State)
    (supported : result ∈ support ((simulateQ (RegistrationNativeIdentityCensorSource.implementation joint selected) work).run before))
    (missing : result.2.target=none) : before.target=none := by
  induction work using OracleComp.inductionOn generalizing before result with
  | pure value =>
      simp only [simulateQ_pure,StateT.run_pure,mem_support_pure_iff] at supported
      cases supported
      exact missing
  | query_bind request next ih =>
      simp only [simulateQ_bind,simulateQ_spec_query,StateT.run_bind,mem_support_bind_iff] at supported
      obtain ⟨middle,called,continued⟩ := supported
      exact source_none joint selected request before middle called (ih middle.1 middle.2 result continued missing)

private theorem promote_run (work : StateT Mode (OracleComp RegistrationNativeIdentityCensorCompiler.Spec) A) (before : Mode) :
    (RegistrationNativeIdentityCensorOperational.promote work).run before =
      simulateQ RegistrationNativeIdentityCensorOperational.embed (work.run before) := rfl
private theorem bind_apply {S X Y : Type} {m : Type → Type} [Monad m]
    (work : StateT S m X) (next : X → StateT S m Y) (before : S) :
    (work >>= next) before = (do let result ← work before; next result.1 result.2) := rfl
private theorem pure_apply {S X : Type} {m : Type → Type} [Monad m] (value : X) (before : S) :
    (pure value : StateT S m X) before = pure (value,before) := rfl

private theorem prepare_facts (joint : PqxdhJointIdentity.Primitives) (selected handle : Nat) (message : Pqxdh.Bytes)
    (mode : Mode) (before : State) :
    ∃ afterMode afterPrivate,
      (simulateQ (RegistrationNativeIdentityCensorSource.implementation joint selected)
        ((RegistrationNativeIdentityCensorOperational.promote
          (RegistrationNativeIdentityCensorCompiler.prepare selected handle message)).run mode)).run before =
        pure (((),afterMode),afterPrivate) ∧ afterPrivate.pool=before.pool ∧ afterMode.armed=mode.armed := by
  rw [promote_run]
  unfold RegistrationNativeIdentityCensorCompiler.prepare
  simp only [StateT.run]
  split
  · split
    · simp only [RegistrationNativeIdentityCensorCompiler.select,RegistrationNativeIdentityCensorCompiler.inspect,
        simulateQ_bind,simulateQ_spec_query,RegistrationNativeIdentityCensorOperational.embed,
        RegistrationNativeIdentityCensorSource.implementation]
      unfold RegistrationNativeIdentityCensorSource.select
      simp only [bind_apply]
      split
      · simp only [pure_bind,ite_true]
        exact ⟨_,_,rfl,rfl,rfl⟩
      · simp only [pure_bind,Bool.false_eq_true,ite_false,simulateQ_pure]
        exact ⟨_,_,rfl,rfl,rfl⟩
    · simp only [simulateQ_pure,pure_bind,Bool.false_eq_true,ite_false]
      exact ⟨_,_,rfl,rfl,rfl⟩
  · simp only [simulateQ_pure]
    exact ⟨_,_,rfl,rfl,rfl⟩

/-- Fresh selection happens before the optional primitive signing reply and needs no generated-key-row premise. -/
theorem prepare_wanted (joint : PqxdhJointIdentity.Primitives) (selected : Nat) (wanted : Pqxdh.Bytes)
    (mode : Mode) (before : State) (armed : mode.armed=true) (synced : mode.target=before.target)
    (missing : before.target=none) (fresh : wanted∉poolMessages selected before.pool)
    (role : RegistrationNativeIdentitySigningRole.oneTime wanted=true) :
    (simulateQ (RegistrationNativeIdentityCensorSource.implementation joint selected)
      ((RegistrationNativeIdentityCensorOperational.promote
        (RegistrationNativeIdentityCensorCompiler.prepare selected selected wanted)).run mode)).run before =
      pure (((),{mode with target:=some wanted,active:=true}),
        {before with target:=some wanted,canonical:=none,framing:=none}) := by
  have privateSelect : RegistrationNativeIdentityCensorSource.select selected wanted before =
      pure (true,{before with target:=some wanted,canonical:=none,framing:=none}) := by
    exact ite_eq_left_iff.mpr (fun _ => by simp_all [poolMessages])
  rw [promote_run]
  simp only [RegistrationNativeIdentityCensorCompiler.prepare,StateT.run,role,and_self,ite_true,
    armed,synced,missing,RegistrationNativeIdentityCensorCompiler.select,RegistrationNativeIdentityCensorCompiler.inspect,
    simulateQ_bind,simulateQ_spec_query,RegistrationNativeIdentityCensorOperational.embed,
    RegistrationNativeIdentityCensorSource.implementation,bind_apply]
  rw [privateSelect]
  simp only [pure_bind,ite_true,beq_self_eq_true,simulateQ_bind,simulateQ_spec_query,
    RegistrationNativeIdentityCensorOperational.embed,RegistrationNativeIdentityCensorSource.implementation,
    simulateQ_pure,pure_apply]

/-- The selected fresh wanted-sign request cannot finish with an absent target, even if the genuine key or signature reply is absent. -/
theorem signing_target (joint : PqxdhJointIdentity.Primitives) (selected : Nat) (wanted : Pqxdh.Bytes)
    (mode : Mode) (before : State) (armed : mode.armed=true) (synced : mode.target=before.target)
    (missing : before.target=none) (fresh : wanted∉poolMessages selected before.pool)
    (role : RegistrationNativeIdentitySigningRole.oneTime wanted=true)
    (result : (Option Ed25519Signature × Mode) × State)
    (supported : result ∈ support ((simulateQ (RegistrationNativeIdentityCensorSource.implementation joint selected)
      ((RegistrationNativeIdentityCensorOperational.signing selected selected wanted).run mode)).run before)) :
    result.2.target≠none := by
  simp only [RegistrationNativeIdentityCensorOperational.signing,StateT.run_bind,simulateQ_bind,
    mem_support_bind_iff] at supported
  obtain ⟨prepared,called,rest⟩ := supported
  rw [prepare_wanted joint selected wanted mode before armed synced missing fresh role,mem_support_pure_iff] at called
  cases called
  simp only [StateT.run_get,simulateQ_pure,StateT.run_pure,mem_support_pure_iff,exists_eq_left] at rest
  intro absent
  have noTarget := source_program_none joint selected _ _ result rest absent
  change some wanted=none at noTarget
  cases noTarget

private theorem constant_armed (joint : PqxdhJointIdentity.Primitives) (selected : Nat)
    (query : Spec.Domain) (mode : Mode) (before : State) (result : (Spec.Range query × Mode) × State)
    (supported : result ∈ support ((simulateQ (RegistrationNativeIdentityCensorSource.implementation joint selected)
      (do let answer ← (Spec.query query : OracleComp Spec _); pure (answer,mode))).run before)) :
    result.1.2.armed=mode.armed := by
  simp only [simulateQ_bind,simulateQ_spec_query,simulateQ_pure,StateT.run_bind,StateT.run_pure,
    mem_support_bind_iff] at supported
  obtain ⟨called,_queried,returned⟩ := supported
  obtain rfl := eq_of_mem_support_pure _ returned
  rfl

private theorem signing_armed (joint : PqxdhJointIdentity.Primitives) (selected handle : Nat)
    (message : Pqxdh.Bytes) (mode : Mode) (before : State) (result : (Option Ed25519Signature × Mode) × State)
    (supported : result ∈ support ((simulateQ (RegistrationNativeIdentityCensorSource.implementation joint selected)
      ((RegistrationNativeIdentityCensorOperational.signing selected handle message).run mode)).run before)) :
    result.1.2.armed=mode.armed := by
  obtain ⟨afterMode,afterPrivate,prepared,_pool,armed⟩ := prepare_facts joint selected handle message mode before
  simp only [RegistrationNativeIdentityCensorOperational.signing,StateT.run_bind,simulateQ_bind,
    mem_support_bind_iff] at supported
  obtain ⟨middle,called,rest⟩ := supported
  rw [prepared,mem_support_pure_iff] at called
  cases called
  simp only [StateT.run_get,simulateQ_pure,StateT.run_pure,mem_support_pure_iff,exists_eq_left] at rest
  split at rest
  · exact (constant_armed joint selected (.inr (.omitted handle message)) afterMode afterPrivate result rest).trans armed
  · exact (constant_armed joint selected (.inl (.inl (.inl (.inl (.inl (.inr (.service handle (.sign message))))))))
      afterMode afterPrivate result rest).trans armed

private theorem lower_query_armed (joint : PqxdhJointIdentity.Primitives) (selected : Nat) (placeholder : Ed25519Signature)
    (query : SourceSpec.Domain) (mode : Mode) (before : State) (result : (SourceSpec.Range query × Mode) × State)
    (supported : result ∈ support ((simulateQ (RegistrationNativeIdentityCensorSource.implementation joint selected)
      ((RegistrationNativeIdentityCensorOperational.implementation selected placeholder query).run mode)).run before)) :
    result.1.2.armed=mode.armed := by
  rcases query with ((coin|request)|report)|bytes
  · exact constant_armed joint selected (.inl (.inl (.inl (.inl (.inl (.inl coin)))))) mode before result supported
  · cases request with
    | create => exact constant_armed joint selected (.inl (.inl (.inl (.inl (.inl (.inr .create)))))) mode before result supported
    | reveal handle => exact constant_armed joint selected (.inl (.inl (.inl (.inl (.inl (.inr (.reveal handle))))))) mode before result supported
    | service handle request => cases request with
      | staticDh peer => exact constant_armed joint selected (.inl (.inl (.inl (.inl (.inl (.inr (.service handle (.staticDh peer)))))))) mode before result supported
      | sign message => exact signing_armed joint selected handle message mode before result supported
  · exact constant_armed joint selected (.inl (.inl (.inl (.inl (.inr report))))) mode before result supported
  · change result ∈ support ((simulateQ (RegistrationNativeIdentityCensorSource.implementation joint selected)
      (match (RegistrationNativeIdentityCensorCompiler.hashInput mode bytes).input with
      | some _ => (RegistrationNativeIdentityCensorOperational.promote
          (RegistrationNativeIdentityCensorCompiler.implementation selected placeholder (.inr bytes))).run mode
      | none => do
          let reply ← (Spec.query (.inr (.template selected mode.target
            (RegistrationNativeIdentityCensorOperational.parts bytes).1 (RegistrationNativeIdentityCensorOperational.parts bytes).2)) : OracleComp Spec _)
          pure (reply,mode))).run before) at supported
    split at supported
    · exact constant_armed joint selected (.inl (.inr (RegistrationNativeIdentityCensorCompiler.hashInput mode bytes)))
        {mode with knownInputs:=match (RegistrationNativeIdentityCensorCompiler.hashInput mode bytes).input with
          | none => mode.knownInputs | some input => mode.knownInputs++[input]} before result supported
    · exact constant_armed joint selected (.inr (.template selected mode.target
        (RegistrationNativeIdentityCensorOperational.parts bytes).1 (RegistrationNativeIdentityCensorOperational.parts bytes).2))
        mode before result supported

private theorem original_fresh (joint : PqxdhJointIdentity.Primitives) (selected : Nat) (wanted : Pqxdh.Bytes)
    (query : SourceSpec.Domain)
    (other : query≠.inl (.inl (.inr (.service selected (.sign wanted)))))
    (before : RegistrationNativePlatformIdentityCtxSource.State) (result : SourceSpec.Range query × RegistrationNativePlatformIdentityCtxSource.State)
    (supported : result ∈ support ((RegistrationNativePlatformIdentityCtxSource.implementation joint query).run before))
    (fresh : wanted∉RegistrationNativePlatformIdentityCtxSigningHistoryFrame.messages selected before)
    (role : RegistrationNativeIdentitySigningRole.oneTime wanted=true) :
    wanted∉RegistrationNativePlatformIdentityCtxSigningHistoryFrame.messages selected result.2 := by
  intro member
  by_cases quiet : RegistrationNativePlatformIdentityCtxSigningHistoryFrame.NoSignFor selected query
  · have same := RegistrationNativePlatformIdentityCtxSigningHistoryFrame.query joint selected query quiet before result supported
    exact fresh (same ▸ member)
  · rcases query with ((coin|request)|report)|bytes
    · exact quiet trivial
    · cases request with
      | create | reveal handle => exact quiet trivial
      | service handle request => cases request with
        | staticDh peer => exact quiet trivial
        | sign message =>
            have same : handle=selected := by
              by_contra different
              exact quiet different
            subst handle
            have unequal : message≠wanted := fun equal => other (by cases equal; rfl)
            have crossed := RegistrationNativePlatformIdentityCtxOneTimeMessageHistory.query joint selected message
              (.inl (.inl (.inr (.service selected (.sign message))))) (fun _ => rfl) before result supported wanted member role
            exact crossed.elim fresh (fun equal => unequal equal.symm)
    · exact quiet trivial
    · exact quiet trivial

private theorem hash_pool (joint : PqxdhJointIdentity.Primitives) (selected : Nat) (placeholder : Ed25519Signature)
    (bytes : Pqxdh.Bytes) (mode : Mode) (before : State) (result : (SourceSpec.Range (.inr bytes) × Mode) × State)
    (supported : result ∈ support ((simulateQ (RegistrationNativeIdentityCensorSource.implementation joint selected)
      ((RegistrationNativeIdentityCensorOperational.implementation selected placeholder (.inr bytes)).run mode)).run before)) :
    result.2.pool=before.pool := by
  change result ∈ support ((simulateQ (RegistrationNativeIdentityCensorSource.implementation joint selected)
    (match (RegistrationNativeIdentityCensorCompiler.hashInput mode bytes).input with
    | some _ => (RegistrationNativeIdentityCensorOperational.promote
        (RegistrationNativeIdentityCensorCompiler.implementation selected placeholder (.inr bytes))).run mode
    | none => do
        let reply ← (Spec.query (.inr (.template selected mode.target
          (RegistrationNativeIdentityCensorOperational.parts bytes).1 (RegistrationNativeIdentityCensorOperational.parts bytes).2)) : OracleComp Spec _)
        pure (reply,mode))).run before) at supported
  split at supported
  · change result ∈ support ((simulateQ (RegistrationNativeIdentityCensorSource.implementation joint selected)
      (do let reply ← (Spec.query (.inl (.inr (RegistrationNativeIdentityCensorCompiler.hashInput mode bytes))) : OracleComp Spec _)
          pure (reply,{mode with knownInputs:=match (RegistrationNativeIdentityCensorCompiler.hashInput mode bytes).input with
            | none => mode.knownInputs | some input => mode.knownInputs++[input]}))).run before) at supported
    simp only [simulateQ_bind,simulateQ_spec_query,simulateQ_pure,StateT.run_bind,StateT.run_pure,
      mem_support_bind_iff] at supported
    obtain ⟨called,queried,returned⟩ := supported
    obtain rfl := eq_of_mem_support_pure _ returned
    simp only [RegistrationNativeIdentityCensorSource.implementation,RegistrationNativeIdentityCensorSource.physical,
      StateT.run,support_map] at queried
    obtain ⟨inner,_physical,rfl⟩ := queried
    rfl
  · simp only [simulateQ_bind,simulateQ_spec_query,simulateQ_pure,StateT.run_bind,StateT.run_pure,
      mem_support_bind_iff] at supported
    obtain ⟨called,queried,returned⟩ := supported
    obtain rfl := eq_of_mem_support_pure _ returned
    simp only [RegistrationNativeIdentityCensorSource.implementation,RegistrationNativeIdentityCensorSource.template,
      RegistrationNativeIdentityCensorSource.physical,StateT.run,Functor.map_map,support_map] at queried
    obtain ⟨inner,_physical,rfl⟩ := queried
    rfl

/-- Every literal canonical lower source leaf preserves armedness, target synchronization, and wanted freshness for as long as no target has been selected. -/
theorem query (joint : PqxdhJointIdentity.Primitives) (selected : Nat) (placeholder : Ed25519Signature)
    (wanted : Pqxdh.Bytes) (role : RegistrationNativeIdentitySigningRole.oneTime wanted=true)
    (request : SourceSpec.Domain) (before : Mode × State) (prior : Holds selected wanted before)
    (result : SourceSpec.Range request × (Mode × State))
    (supported : result ∈ support ((closed joint selected placeholder request).run before)) :
    Holds selected wanted result.2 := by
  have original := supported
  rw [closed,QueryImpl.Stateful.link_impl_apply_run,support_map] at supported
  obtain ⟨lower,called,rfl⟩ := supported
  change Holds selected wanted (lower.1.2,lower.2)
  have armed := lower_query_armed joint selected placeholder request before.1 before.2 lower called
  have synced := RegistrationNativeIdentityCensorTargetSync.lower_query joint selected placeholder false
    request before.1 before.2 prior.2.1 lower called
  refine ⟨armed.trans prior.1,synced,?_⟩
  intro absent member
  have missing := source_program_none joint selected _ before.2 lower called absent
  have fresh := prior.2.2 missing
  cases request with
  | inl protocol =>
      by_cases actualWanted : protocol=.inl (.inr (.service selected (.sign wanted)))
      · subst protocol
        exact signing_target joint selected wanted before.1 before.2 prior.1 prior.2.1 missing fresh role lower called absent
      · have mapped := RegistrationNativeIdentityCensorRealSigning.protocol joint selected placeholder protocol before
        ▸ (show (lower.1.1,project (lower.1.2,lower.2)) ∈ support
            (Prod.map id project <$> (closed joint selected placeholder (.inl protocol)).run before) from by
          rw [support_map]
          exact ⟨(lower.1.1,(lower.1.2,lower.2)),original,rfl⟩)
        exact original_fresh joint selected wanted (.inl protocol) (fun same => actualWanted (Sum.inl.inj same))
          (project before) (lower.1.1,project (lower.1.2,lower.2)) mapped fresh role member
  | inr bytes =>
      have same := hash_pool joint selected placeholder bytes before.1 before.2 lower called
      exact fresh (same ▸ member)

/-- Every adaptive lower source program retains the exact armed-and-fresh invariant through all optional replies and hash branches. -/
theorem program (joint : PqxdhJointIdentity.Primitives) (selected : Nat) (placeholder : Ed25519Signature)
    (wanted : Pqxdh.Bytes) (role : RegistrationNativeIdentitySigningRole.oneTime wanted=true)
    (work : OracleComp SourceSpec A) (before : Mode × State) (prior : Holds selected wanted before)
    (result : A × (Mode × State))
    (supported : result ∈ support ((simulateQ (closed joint selected placeholder) work).run before)) :
    Holds selected wanted result.2 := by
  induction work using OracleComp.inductionOn generalizing before result with
  | pure value =>
      simp only [simulateQ_pure,StateT.run_pure,mem_support_pure_iff] at supported
      cases supported
      exact prior
  | query_bind request next ih =>
      simp only [simulateQ_bind,simulateQ_spec_query,StateT.run_bind,mem_support_bind_iff] at supported
      obtain ⟨middle,called,continued⟩ := supported
      exact ih middle.1 middle.2 (query joint selected placeholder wanted role request before prior middle called) result continued

/-- Once the actual wanted message has appeared in its selected successful signing history, a target must already exist on that same source run. -/
theorem crossing (joint : PqxdhJointIdentity.Primitives) (selected : Nat) (placeholder : Ed25519Signature)
    (wanted : Pqxdh.Bytes) (role : RegistrationNativeIdentitySigningRole.oneTime wanted=true)
    (work : OracleComp SourceSpec A) (before : Mode × State) (prior : Holds selected wanted before)
    (result : A × (Mode × State))
    (supported : result ∈ support ((simulateQ (closed joint selected placeholder) work).run before))
    (member : wanted∈poolMessages selected result.2.2.pool) : result.2.2.target≠none := by
  have held := program joint selected placeholder wanted role work before prior result supported
  exact fun absent => held.2.2 absent member

/-- The invariant applies directly to the genuine nested source interpretation, retaining both complete poststates. -/
theorem lower_program (joint : PqxdhJointIdentity.Primitives) (selected : Nat) (placeholder : Ed25519Signature)
    (wanted : Pqxdh.Bytes) (role : RegistrationNativeIdentitySigningRole.oneTime wanted=true)
    (work : OracleComp SourceSpec A) (mode : Mode) (before : State) (prior : Holds selected wanted (mode,before))
    (result : (A × Mode) × State)
    (supported : result ∈ support ((simulateQ (RegistrationNativeIdentityCensorSource.implementation joint selected)
      ((simulateQ (RegistrationNativeIdentityCensorOperational.implementation selected placeholder) work).run mode)).run before)) :
    Holds selected wanted (result.1.2,result.2) := by
  have closedSupport : (result.1.1,(result.1.2,result.2)) ∈ support
      ((simulateQ (closed joint selected placeholder) work).run (mode,before)) := by
    rw [closed,QueryImpl.Stateful.simulateQ_link_run,support_map]
    exact ⟨result,supported,rfl⟩
  exact program joint selected placeholder wanted role work (mode,before) prior (result.1.1,(result.1.2,result.2)) closedSupport

private theorem scoped_fresh_query (joint : PqxdhJointIdentity.Primitives) (selected : Nat) (placeholder : Ed25519Signature)
    (fixed wanted : Pqxdh.Bytes) (different : wanted≠fixed) (role : RegistrationNativeIdentitySigningRole.oneTime wanted=true)
    (request : SourceSpec.Domain) (allowed : RegistrationNativePlatformIdentityCtxBundleMessageScope.UsesSourceMessage fixed request)
    (before : Mode × State) (fresh : wanted∉poolMessages selected before.2.pool)
    (result : SourceSpec.Range request × (Mode × State))
    (supported : result ∈ support ((closed joint selected placeholder request).run before)) :
    wanted∉poolMessages selected result.2.2.pool := by
  have original := supported
  have other : request≠.inl (.inl (.inr (.service selected (.sign wanted)))) := by
    intro same
    subst request
    exact different (allowed role)
  rw [closed,QueryImpl.Stateful.link_impl_apply_run,support_map] at supported
  obtain ⟨lower,called,rfl⟩ := supported
  cases request with
  | inl protocol =>
      have mapped := RegistrationNativeIdentityCensorRealSigning.protocol joint selected placeholder protocol before
        ▸ (show (lower.1.1,project (lower.1.2,lower.2)) ∈ support
            (Prod.map id project <$> (closed joint selected placeholder (.inl protocol)).run before) from by
          rw [support_map]
          exact ⟨(lower.1.1,(lower.1.2,lower.2)),original,rfl⟩)
      exact original_fresh joint selected wanted (.inl protocol) other
        (project before) (lower.1.1,project (lower.1.2,lower.2)) mapped fresh role
  | inr bytes =>
      have same := hash_pool joint selected placeholder bytes before.1 before.2 lower called
      exact fun member => fresh (same ▸ member)

private theorem scoped_fresh_program (joint : PqxdhJointIdentity.Primitives) (selected : Nat) (placeholder : Ed25519Signature)
    (fixed wanted : Pqxdh.Bytes) (different : wanted≠fixed) (role : RegistrationNativeIdentitySigningRole.oneTime wanted=true)
    (work : OracleComp SourceSpec A) (allowed : work.AllQueriesSatisfy (RegistrationNativePlatformIdentityCtxBundleMessageScope.UsesSourceMessage fixed))
    (before : Mode × State) (fresh : wanted∉poolMessages selected before.2.pool)
    (result : A × (Mode × State))
    (supported : result ∈ support ((simulateQ (closed joint selected placeholder) work).run before)) :
    wanted∉poolMessages selected result.2.2.pool := by
  induction work using OracleComp.inductionOn generalizing before result with
  | pure value =>
      simp only [simulateQ_pure,StateT.run_pure,mem_support_pure_iff] at supported
      cases supported
      exact fresh
  | query_bind request next ih =>
      rw [allQueriesSatisfy_query_bind_iff] at allowed
      simp only [simulateQ_bind,simulateQ_spec_query,StateT.run_bind,mem_support_bind_iff] at supported
      obtain ⟨middle,called,continued⟩ := supported
      exact ih middle.1 (allowed.2 middle.1) middle.2
        (scoped_fresh_query joint selected placeholder fixed wanted different role request allowed.1 before fresh middle called)
        result continued

section Main
open RegistrationNativeIdentityCensorEdOutgoingSource (Full interpret)
variable {n : Nat} {KemSK Platform : Type} {mlSource : RegistrationNativeMldsa.Source}

/-- The actual complete Main/platform transformer retains armedness and freshness through every source reply, writer and reservation failure. -/
theorem main (joint : PqxdhJointIdentity.Primitives) (selected : Nat) (placeholder : Ed25519Signature)
    (wanted : Pqxdh.Bytes) (role : RegistrationNativeIdentitySigningRole.oneTime wanted=true)
    (work : RegistrationNativePlatformIdentityCtxMain.M n KemSK Platform mlSource A)
    (before : Full (n := n) (KemSK := KemSK) (Platform := Platform) (mlSource := mlSource))
    (prior : Holds selected wanted (before.1.2,before.2))
    (result : A × Full (n := n) (KemSK := KemSK) (Platform := Platform) (mlSource := mlSource))
    (supported : result ∈ support ((interpret joint selected placeholder false work).run before)) :
    Holds selected wanted (result.2.1.2,result.2.2) := by
  simp only [interpret,StateT.run,Bool.false_eq_true,ite_false,bind_pure_comp,support_map] at supported
  obtain ⟨lower,called,rfl⟩ := supported
  exact lower_program joint selected placeholder wanted role (work.run before.1.1) before.1.2 before.2 prior lower called

/-- A newly reached successful wanted-sign history implies synchronized present targets in the exact original Main/platform/private result. -/
theorem main_target (joint : PqxdhJointIdentity.Primitives) (selected : Nat) (placeholder : Ed25519Signature)
    (wanted : Pqxdh.Bytes) (role : RegistrationNativeIdentitySigningRole.oneTime wanted=true)
    (work : RegistrationNativePlatformIdentityCtxMain.M n KemSK Platform mlSource A)
    (before : Full (n := n) (KemSK := KemSK) (Platform := Platform) (mlSource := mlSource))
    (prior : Holds selected wanted (before.1.2,before.2))
    (result : A × Full (n := n) (KemSK := KemSK) (Platform := Platform) (mlSource := mlSource))
    (supported : result ∈ support ((interpret joint selected placeholder false work).run before))
    (member : wanted∈poolMessages selected result.2.2.pool) :
    ∃ message,result.2.1.2.target=some message ∧ result.2.2.target=some message := by
  have held := main joint selected placeholder wanted role work before prior result supported
  cases chosen : result.2.2.target with
  | none => exact False.elim (held.2.2 chosen member)
  | some message => exact ⟨message,held.2.1.trans chosen,rfl⟩
/-- A genuine canonical successful-history crossing identifies the body's original one-time operand without any scalar, armedness or target-equality premise. -/
theorem message_crossing (joint : PqxdhJointIdentity.Primitives) (selected : Nat) (placeholder : Ed25519Signature)
    (fixed wanted : Pqxdh.Bytes) (role : RegistrationNativeIdentitySigningRole.oneTime wanted=true)
    (work : RegistrationNativePlatformIdentityCtxMain.M n KemSK Platform mlSource A)
    (before : Full (n := n) (KemSK := KemSK) (Platform := Platform) (mlSource := mlSource))
    (allowed : (work.run before.1.1).AllQueriesSatisfy (RegistrationNativePlatformIdentityCtxBundleMessageScope.UsesSourceMessage fixed))
    (fresh : wanted∉poolMessages selected before.2.pool)
    (result : A × Full (n := n) (KemSK := KemSK) (Platform := Platform) (mlSource := mlSource))
    (supported : result ∈ support ((interpret joint selected placeholder false work).run before))
    (member : wanted∈poolMessages selected result.2.2.pool) : wanted=fixed := by
  by_contra different
  simp only [interpret,StateT.run,Bool.false_eq_true,ite_false,bind_pure_comp,support_map] at supported
  obtain ⟨lower,called,rfl⟩ := supported
  have closedSupport : (lower.1.1,(lower.1.2,lower.2)) ∈ support
      ((simulateQ (closed joint selected placeholder) (work.run before.1.1)).run (before.1.2,before.2)) := by
    rw [closed,QueryImpl.Stateful.simulateQ_link_run,support_map]
    exact ⟨lower,called,rfl⟩
  exact scoped_fresh_program joint selected placeholder fixed wanted different role (work.run before.1.1)
    allowed (before.1.2,before.2) fresh (lower.1.1,(lower.1.2,lower.2)) closedSupport member
end Main

end BeaconcryptCore.Computational.RegistrationNativeIdentityCensorArmedFresh

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorArmedFresh.prepare_wanted' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorArmedFresh.prepare_wanted

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorArmedFresh.signing_target' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorArmedFresh.signing_target

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorArmedFresh.query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorArmedFresh.query

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorArmedFresh.program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorArmedFresh.program

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorArmedFresh.crossing' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorArmedFresh.crossing

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorArmedFresh.lower_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorArmedFresh.lower_program

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorArmedFresh.main' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorArmedFresh.main

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorArmedFresh.main_target' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorArmedFresh.main_target

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorArmedFresh.message_crossing' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorArmedFresh.message_crossing
