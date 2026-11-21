-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorOperationalPrefix
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorEdOutgoingSource
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorActualHashSource

/-! Erasing only the censor's private selection metadata recovers the actual ordinary indexed signing call. Selection and scanning are ghost operations in the canonical source; every genuine optional reply and every attempted service receipt remain in the original pool. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityCensorRealSigning
open RegistrationNativeIdentityCensorCompiler (Mode)
open PqxdhEd25519EufCma (Ed25519Signature)
abbrev Private := RegistrationNativeIdentityCensorSource.State
variable {A : Type}

def project (before : Mode × Private) : RegistrationNativePlatformIdentityCtxSource.State :=
  (before.2.pool, before.2.hash)

private theorem promote_run (work : StateT Mode (OracleComp RegistrationNativeIdentityCensorCompiler.Spec) A) (before : Mode) :
    (RegistrationNativeIdentityCensorOperational.promote work).run before =
      simulateQ RegistrationNativeIdentityCensorOperational.embed (work.run before) := rfl

private theorem bind_apply {S X Y : Type} {m : Type → Type} [Monad m]
    (work : StateT S m X) (next : X → StateT S m Y) (before : S) :
    (work >>= next) before = (do let result ← work before; next result.1 result.2) := rfl

private theorem prepare (joint : PqxdhJointIdentity.Primitives) (selected handle : Nat) (message : Pqxdh.Bytes)
    (mode : Mode) (before : Private) :
    ∃ afterMode afterPrivate,
      (simulateQ (RegistrationNativeIdentityCensorSource.implementation joint selected)
        ((RegistrationNativeIdentityCensorOperational.promote
          (RegistrationNativeIdentityCensorCompiler.prepare selected handle message)).run mode)).run before =
        pure (((), afterMode), afterPrivate) ∧ afterPrivate.pool = before.pool ∧ afterPrivate.hash = before.hash := by
  rw [promote_run]
  unfold RegistrationNativeIdentityCensorCompiler.prepare
  simp only [StateT.run]
  split
  · split
    · simp only [RegistrationNativeIdentityCensorCompiler.select, RegistrationNativeIdentityCensorCompiler.inspect,
        simulateQ_bind, simulateQ_spec_query, RegistrationNativeIdentityCensorOperational.embed,
        RegistrationNativeIdentityCensorSource.implementation]
      unfold RegistrationNativeIdentityCensorSource.select
      simp only [bind_apply]
      split
      · simp only [pure_bind, ite_true]
        exact ⟨_, _, rfl, rfl, rfl⟩
      · simp only [pure_bind, Bool.false_eq_true, ite_false, simulateQ_pure]
        exact ⟨_, _, rfl, rfl, rfl⟩
    · simp only [simulateQ_pure, pure_bind, Bool.false_eq_true, ite_false]
      exact ⟨_, _, rfl, rfl, rfl⟩
  · simp only [simulateQ_pure]
    exact ⟨_, _, rfl, rfl, rfl⟩

private theorem lift_apply {S X : Type} {m : Type → Type} [Monad m]
    (work : m X) (before : S) :
    (StateT.lift work : StateT S m X) before = (do let value ← work; pure (value, before)) := rfl
private theorem map_apply {S X Y : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (change : X → Y) (work : StateT S m X) (before : S) :
    (change <$> work) before = Prod.map change id <$> work before := StateT.run_map change work before

/-- The canonical source records the exact genuine optional service even when its frontend request is marked for suppression. Private selection metadata alone is erased. -/
theorem signing (joint : PqxdhJointIdentity.Primitives) (selected handle : Nat) (message : Pqxdh.Bytes)
    (mode : Mode) (before : Private) :
    (fun result => (result.1.1, project (result.1.2, result.2))) <$>
      (simulateQ (RegistrationNativeIdentityCensorSource.implementation joint selected)
        ((RegistrationNativeIdentityCensorOperational.signing selected handle message).run mode)).run before =
      (RegistrationNativePlatformIdentityCtxSource.implementation joint
        (.inl (.inl (.inr (.service handle (.sign message)))))).run (project (mode, before)) := by
  obtain ⟨afterMode, afterPrivate, prepared, pool, hash⟩ := prepare joint selected handle message mode before
  rw [RegistrationNativeIdentityCensorOperational.signing, StateT.run_bind]
  simp only [simulateQ_bind, StateT.run_bind, prepared, pure_bind, StateT.run_get]
  split
  · simp only [lift_apply, bind_pure_comp, simulateQ_map, simulateQ_spec_query,
      RegistrationNativeIdentityCensorSource.implementation, RegistrationNativeIdentityCensorSource.omitted,
      RegistrationNativeIdentityMainSource.implementation, PqxdhDynamicIdentityPool.lazyImpl,
      PqxdhDynamicIdentityPool.poolImpl, PqxdhJointIdentity.primitiveReply,
      RegistrationNativePlatformIdentityCtxSource.implementation, map_apply, StateT.run,
      map_pure, project, pool, hash]
    rfl
  · simp only [lift_apply, bind_pure_comp, simulateQ_map, simulateQ_spec_query,
      RegistrationNativeIdentityCensorOperational.embed, RegistrationNativeIdentityCensorSource.implementation,
      RegistrationNativeIdentityCensorSource.protocol,
      RegistrationNativeIdentityMainSource.implementation, PqxdhDynamicIdentityPool.lazyImpl,
      PqxdhDynamicIdentityPool.poolImpl, PqxdhJointIdentity.primitiveReply,
      RegistrationNativePlatformIdentityCtxSource.implementation, map_apply, StateT.run,
      map_pure, project, pool, hash]
    rfl

abbrev Spec := RegistrationNativePlatformIdentityCtxCompiler.Spec

noncomputable def closed (joint : PqxdhJointIdentity.Primitives) (selected : Nat) (placeholder : Ed25519Signature) :
    QueryImpl Spec (StateT (Mode × Private) ProbComp) :=
  QueryImpl.Stateful.link (RegistrationNativeIdentityCensorOperational.implementation selected placeholder)
    (RegistrationNativeIdentityCensorSource.implementation joint selected)

private def forwarded (request : PqxdhJointPhase1Reports.ProtocolSpec.Domain) (before : Mode) :
    OracleComp RegistrationNativeIdentityCensorOperational.Spec (PqxdhJointPhase1Reports.ProtocolSpec.Range request × Mode) := do
  let answer ← RegistrationNativeIdentityCensorOperational.Spec.query (.inl (.inl (.inl (.inl request))))
  pure (answer, before)

private theorem pure_apply {S X : Type} {m : Type → Type} [Monad m] (value : X) (before : S) :
    (pure value : StateT S m X) before = pure (value, before) := rfl

private theorem forwarded_source (joint : PqxdhJointIdentity.Primitives) (selected : Nat)
    (request : PqxdhJointPhase1Reports.ProtocolSpec.Domain) (before : Mode × Private) :
    (fun result => (result.1.1, project (result.1.2, result.2))) <$>
      (simulateQ (RegistrationNativeIdentityCensorSource.implementation joint selected)
        (forwarded request before.1)).run before.2 =
      (RegistrationNativePlatformIdentityCtxSource.implementation joint (.inl request)).run (project before) := by
  simp only [forwarded, simulateQ_bind, simulateQ_spec_query, RegistrationNativeIdentityCensorSource.implementation,
    simulateQ_pure, StateT.run, bind_apply, RegistrationNativeIdentityCensorSource.protocol,
    RegistrationNativePlatformIdentityCtxSource.implementation, map_bind, bind_map_left, pure_apply, map_pure, project]
  rw [bind_pure_comp]

/-- Every protocol leaf, including every optional genuine signing attempt, has its literal original private-source marginal. -/
theorem protocol (joint : PqxdhJointIdentity.Primitives) (selected : Nat) (placeholder : Ed25519Signature)
    (request : PqxdhJointPhase1Reports.ProtocolSpec.Domain) (before : Mode × Private) :
    Prod.map id project <$> (closed joint selected placeholder (.inl request)).run before =
      (RegistrationNativePlatformIdentityCtxSource.implementation joint (.inl request)).run (project before) := by
  rw [closed, QueryImpl.Stateful.link_impl_apply_run, Functor.map_map]
  change (fun result : (Spec.Range (.inl request) × Mode) × Private =>
    (result.1.1, project (result.1.2, result.2))) <$>
      (simulateQ (RegistrationNativeIdentityCensorSource.implementation joint selected)
        ((RegistrationNativeIdentityCensorOperational.implementation selected placeholder (.inl request)).run before.1)).run before.2 = _
  rcases request with (coin | request) | report
  · have tree : (RegistrationNativeIdentityCensorOperational.implementation selected placeholder (.inl (.inl (.inl coin)))).run before.1 =
        forwarded (.inl (.inl coin)) before.1 := rfl
    rw [tree]
    exact forwarded_source joint selected (.inl (.inl coin)) before
  · cases request with
    | service handle request => cases request with
      | sign message =>
        exact signing joint selected handle message before.1 before.2
      | staticDh peer =>
        have tree : (RegistrationNativeIdentityCensorOperational.implementation selected placeholder (.inl (.inl (.inr (.service handle (.staticDh peer)))))).run before.1 =
            forwarded (.inl (.inr (.service handle (.staticDh peer)))) before.1 := rfl
        rw [tree]
        exact forwarded_source joint selected (.inl (.inr (.service handle (.staticDh peer)))) before
    | create =>
      have tree : (RegistrationNativeIdentityCensorOperational.implementation selected placeholder (.inl (.inl (.inr .create)))).run before.1 =
          forwarded (.inl (.inr .create)) before.1 := rfl
      rw [tree]
      exact forwarded_source joint selected (.inl (.inr .create)) before
    | reveal handle =>
      have tree : (RegistrationNativeIdentityCensorOperational.implementation selected placeholder (.inl (.inl (.inr (.reveal handle))))).run before.1 =
          forwarded (.inl (.inr (.reveal handle))) before.1 := rfl
      rw [tree]
      exact forwarded_source joint selected (.inl (.inr (.reveal handle))) before
  · have tree : (RegistrationNativeIdentityCensorOperational.implementation selected placeholder (.inl (.inr report))).run before.1 =
        forwarded (.inr report) before.1 := rfl
    rw [tree]
    exact forwarded_source joint selected (.inr report) before

def NoHash : Spec.Domain → Prop
  | .inl _ => True
  | .inr _ => False

/-- Adaptive protocol-only source work erases its private selection metadata without changing a service request, optional signature, generated row, transcript or physical cache. -/
theorem program (joint : PqxdhJointIdentity.Primitives) (selected : Nat) (placeholder : Ed25519Signature)
    (work : OracleComp Spec A) (allowed : work.AllQueriesSatisfy NoHash) (before : Mode × Private) :
    Prod.map id project <$> (simulateQ (closed joint selected placeholder) work).run before =
      (simulateQ (RegistrationNativePlatformIdentityCtxSource.implementation joint) work).run (project before) := by
  induction work using OracleComp.inductionOn generalizing before with
  | pure value => simp only [simulateQ_pure, StateT.run_pure, map_pure, Prod.map_apply, id_eq]
  | query_bind request next ih =>
    rw [allQueriesSatisfy_query_bind_iff] at allowed
    cases request with
    | inr bytes => exact False.elim allowed.1
    | inl request =>
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, map_bind]
      have later : (fun result : Spec.Range (.inl request) × (Mode × Private) => Prod.map id project <$>
          (simulateQ (closed joint selected placeholder) (next result.1)).run result.2) =
          (fun result : Spec.Range (.inl request) × (Mode × Private) => (simulateQ (RegistrationNativePlatformIdentityCtxSource.implementation joint) (next result.1)).run (project result.2)) := by
        funext result
        exact ih result.1 (allowed.2 result.1) result.2
      rw [later]
      change _ = (do let result ← (RegistrationNativePlatformIdentityCtxSource.implementation joint (.inl request)).run (project before)
                     (simulateQ (RegistrationNativePlatformIdentityCtxSource.implementation joint) (next result.1)).run result.2)
      rw [← protocol joint selected placeholder request before, bind_map_left]
      rfl

section Main
open RegistrationNativeIdentityCensorEdOutgoingSource (Full interpret)
variable {n : Nat} {I KemSK Platform : Type} {base : OracleSpec I} {mlSource : RegistrationNativeMldsa.Source}

/-- The same source erasure lifts through the actual Main state transformer, retaining the entire Main/P result and physical pool/cache/journal. -/
theorem main (joint : PqxdhJointIdentity.Primitives) (selected : Nat) (placeholder : Ed25519Signature)
    (work : RegistrationNativePlatformIdentityCtxMain.M n KemSK Platform mlSource A)
    (before : Full (n := n) (KemSK := KemSK) (Platform := Platform) (mlSource := mlSource))
    (allowed : (work.run before.1.1).AllQueriesSatisfy NoHash) :
    Prod.map id RegistrationNativeIdentityCensorActualHashSource.project <$>
      (interpret joint selected placeholder false work).run before =
      (RegistrationNativePlatformIdentityCtxMain.interpret joint work).run
        (RegistrationNativeIdentityCensorActualHashSource.project before) := by
  have law := program joint selected placeholder (work.run before.1.1) allowed (before.1.2, before.2)
  rw [closed, QueryImpl.Stateful.simulateQ_link_run, Functor.map_map] at law
  change (fun result : ((A × (RegistrationNativeIdentityMain.State n KemSK mlSource × Platform)) × Mode) × Private =>
      (result.1.1, (result.2.pool, result.2.hash))) <$>
    (simulateQ (RegistrationNativeIdentityCensorSource.implementation joint selected)
      ((simulateQ (RegistrationNativeIdentityCensorOperational.implementation selected placeholder) (work.run before.1.1)).run before.1.2)).run before.2 = _ at law
  have result := congrArg (fun distribution =>
    (fun value : (A × (RegistrationNativeIdentityMain.State n KemSK mlSource × Platform)) × RegistrationNativePlatformIdentityCtxSource.State =>
      (value.1.1, (value.1.2, value.2))) <$> distribution) law
  simpa only [interpret, RegistrationNativePlatformIdentityCtxMain.interpret, StateT.run, Bool.false_eq_true,
    ite_false, bind_pure_comp, Functor.map_map, RegistrationNativeIdentityCensorActualHashSource.project, project,
    Prod.map_def, id_eq] using result

/-- The actual outgoing Ed callback has its literal ordinary source marginal for every target/mode, key-row absence, public-key rejection and optional signing outcome. -/
theorem outgoing (setup : PqxdhServerAuthExperiment.Setup base KemSK) (checks : PqxdhServerAuthExperiment.Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (selected index : Nat) (owner : RegistrationNativeIdentityFrontend.Owner mlSource) (request : registration.Ed25519SigningRequest)
    (placeholder : Ed25519Signature) (before : Full (n := n) (KemSK := KemSK) (Platform := Platform) (mlSource := mlSource)) :
    let action := RegistrationNativePlatformIdentityCtxMain.beacon setup checks representation created
      (RegistrationNativePlatformIdentityProgram.native
        (RegistrationNativeIdentityFrontend.outgoing (n := n) (Auxiliary := RegistrationServerRoleBackend.State) setup mlSource index owner (.inr request)))
    Prod.map id RegistrationNativeIdentityCensorActualHashSource.project <$>
      (interpret setup.joint selected placeholder false action).run before =
      (RegistrationNativePlatformIdentityCtxMain.interpret setup.joint action).run
        (RegistrationNativeIdentityCensorActualHashSource.project before) := by
  dsimp only
  apply main
  rw [RegistrationNativePlatformIdentityCtxEdOutgoing.outgoing]
  unfold RegistrationNativePlatformIdentityCtxEdOutgoing.expected
  split
  · exact (allQueriesSatisfy_query_bind_iff _ _ _).mpr ⟨trivial, fun _ => trivial⟩
  · trivial
end Main

end BeaconcryptCore.Computational.RegistrationNativeIdentityCensorRealSigning

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorRealSigning.signing' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorRealSigning.signing

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorRealSigning.protocol' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorRealSigning.protocol

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorRealSigning.program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorRealSigning.program

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorRealSigning.main' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorRealSigning.main

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorRealSigning.outgoing' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorRealSigning.outgoing
