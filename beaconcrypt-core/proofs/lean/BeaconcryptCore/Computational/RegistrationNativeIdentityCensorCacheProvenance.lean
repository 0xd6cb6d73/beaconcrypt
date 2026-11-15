-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateFirstOmitted
import BeaconcryptCore.Computational.RegistrationNativeIdentityStartupJournal
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorPublicSource

/-! Every cached physical address remains in the same actual chronological source journal. The invariant threads through canonical omitted attempts, optional source services and every public/template hash, beginning with the actual empty startup journal. -/
open OracleComp OracleSpec
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityCensorCacheProvenance
open RegistrationNativeIdentityCensorSource (State)
open RegistrationNativeIdentityCensorOperational (Spec)
open RegistrationNativePlatformCtxProvenance (Provenance)
open PqxdhEd25519EufCma (Ed25519Signature)
variable {Value I KemSK : Type} {base : OracleSpec I}

def Known (before : State) : Prop := Provenance before.hash

private theorem bind_apply {S A B : Type} {m : Type → Type} [Monad m]
    (work : StateT S m A) (next : A → StateT S m B) (before : S) :
    (work >>= next) before = (do let result ← work before; next result.1 result.2) := rfl

private theorem pure_apply {S A : Type} {m : Type → Type} [Monad m] (value : A) (before : S) :
    (pure value : StateT S m A) before = pure (value, before) := rfl

/-- The literal private-censored source leaf keeps actual cache provenance on every reached result. -/
theorem query (joint : PqxdhJointIdentity.Primitives) (selected : Nat) (placeholder : Ed25519Signature)
    (request : Spec.Domain) (before : State) (prior : Known before) (result : Spec.Range request × State)
    (supported : result ∈ support ((RegistrationNativeIdentityCensorSource.censored joint selected placeholder request).run before)) :
    Known result.2 := by
  rcases request with (((protocol | message) | scan) | described) | marker
  · simp only [RegistrationNativeIdentityCensorSource.censored, RegistrationNativeIdentityCensorSource.implementation,
      RegistrationNativeIdentityCensorSource.protocol, StateT.run, support_map] at supported
    obtain ⟨actual, _called, rfl⟩ := supported
    exact prior
  · simp only [RegistrationNativeIdentityCensorSource.censored, RegistrationNativeIdentityCensorSource.implementation,
      RegistrationNativeIdentityCensorSource.select, StateT.run] at supported
    split at supported <;> simp only [mem_support_pure_iff] at supported <;> cases supported <;> exact prior
  · simp only [RegistrationNativeIdentityCensorSource.censored, RegistrationNativeIdentityCensorSource.implementation,
      StateT.run_pure, mem_support_pure_iff] at supported
    cases supported
    exact prior
  · simp only [RegistrationNativeIdentityCensorSource.censored, RegistrationNativeIdentityCensorSource.implementation,
      RegistrationNativeIdentityCensorSource.physical, StateT.run, support_map] at supported
    obtain ⟨actual, called, rfl⟩ := supported
    exact RegistrationNativePlatformCtxProvenance.physical _ before.hash prior actual called
  · cases marker with
    | template handle message leading trailing =>
      simp only [RegistrationNativeIdentityCensorSource.censored, RegistrationNativeIdentityCensorSource.implementation,
        RegistrationNativeIdentityCensorSource.template, RegistrationNativeIdentityCensorSource.physical,
        StateT.run, Functor.map_map, support_map] at supported
      obtain ⟨actual, called, rfl⟩ := supported
      exact RegistrationNativePlatformCtxProvenance.physical _ before.hash prior actual called
    | omitted handle message =>
      simp only [RegistrationNativeIdentityCensorSource.censored, bind_apply, RegistrationNativeIdentityCensorSource.omitted,
        StateT.run, pure_apply, bind_pure_comp, Functor.map_map, support_map] at supported
      obtain ⟨actual, _called, rfl⟩ := supported
      exact prior

/-- Arbitrary adaptive operational source work retains the entire inherited-cache provenance invariant. -/
theorem program (joint : PqxdhJointIdentity.Primitives) (selected : Nat) (placeholder : Ed25519Signature)
    (work : OracleComp Spec Value) (before : State) (prior : Known before) (result : Value × State)
    (supported : result ∈ support ((simulateQ (RegistrationNativeIdentityCensorSource.censored joint selected placeholder) work).run before)) :
    Known result.2 := by
  induction work using OracleComp.inductionOn generalizing before result with
  | pure value =>
    simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at supported
    cases supported
    exact prior
  | query_bind request next ih =>
    rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at supported
    obtain ⟨middle, called, continued⟩ := supported
    exact ih middle.1 middle.2 (query joint selected placeholder request before prior middle called) result continued

/-- Actual initialized source state has the unchanged initial CTX cache and empty journal; pure pin selection creates no hash address. -/
theorem initialized {n : Nat} {source : RegistrationNativeMldsa.Source}
    (setup : PqxdhServerAuthExperiment.Setup base KemSK) (ensureInit : StateT Unit ProbComp Bool)
    (identityIndex : Nat) (serverKeyId : Aeneas.Std.U64) (initial : RegistrationNativeExperiment.Initial n KemSK source)
    (reached : some initial ∈ support (RegistrationNativeExperiment.start setup source ensureInit identityIndex serverKeyId)) :
    Known ⟨PqxdhDynamicIdentityPool.initialState,
      (RegistrationNativeWorldCache.cache initial.state, []), none, none, none⟩ :=
  RegistrationNativeIdentityStartupJournal.start setup ensureInit identityIndex serverKeyId initial reached

section Main
open RegistrationNativeIdentityCensorEdOutgoingSource (Full interpret)
open RegistrationNativeRawAdapter (TypedSpec)
variable {n : Nat} {Platform : Type} {source : RegistrationNativeMldsa.Source}

/-- Main reassociation preserves the same complete private physical cache and journal invariant. -/
theorem main (joint : PqxdhJointIdentity.Primitives) (selected : Nat) (placeholder : Ed25519Signature)
    (work : RegistrationNativePlatformIdentityCtxMain.M n KemSK Platform source Value)
    (before : Full (n := n) (KemSK := KemSK) (Platform := Platform) (mlSource := source)) (prior : Known before.2)
    (result : Value × Full (n := n) (KemSK := KemSK) (Platform := Platform) (mlSource := source))
    (supported : result ∈ support ((interpret joint selected placeholder true work).run before)) : Known result.2.2 := by
  simp only [interpret, StateT.run, ite_true, mem_support_bind_iff] at supported
  obtain ⟨returned, called, completed⟩ := supported
  obtain rfl := eq_of_mem_support_pure _ completed
  exact program joint selected placeholder _ before.2 prior returned called

/-- The literal entered typed callback counts every attempt without resetting or hiding any source cache key. -/
theorem callback (joint : PqxdhJointIdentity.Primitives) (selected position : Nat) (placeholder : Ed25519Signature)
    (frontend : QueryImpl TypedSpec (RegistrationNativePlatformIdentityCtxMain.M n KemSK Platform source)) (query : TypedSpec.Domain)
    (before : Full (n := n) (KemSK := KemSK) (Platform := Platform) (mlSource := source)) (prior : Known before.2)
    (result : TypedSpec.Range query × Full (n := n) (KemSK := KemSK) (Platform := Platform) (mlSource := source))
    (supported : result ∈ support ((RegistrationNativeIdentityCensorPublicSource.callback
      (RegistrationNativeIdentityCensorSource.censored joint selected placeholder)
      (RegistrationNativeIdentityCensorPublicClient.callback selected position placeholder frontend) query).run before)) : Known result.2.2 := by
  have law := RegistrationNativeIdentityCensorPublicSource.current joint selected position placeholder true frontend query before
  simp only [ite_true] at law
  rw [law] at supported
  exact main joint selected placeholder (frontend query)
    ((before.1.1, RegistrationNativeIdentityCensorCompiler.enter position query before.1.2), before.2) prior result supported

/-- Every reached actual adaptive callback prefix retains the inherited cache's source-derived provenance. -/
theorem adaptive (joint : PqxdhJointIdentity.Primitives) (selected position : Nat) (placeholder : Ed25519Signature)
    (frontend : QueryImpl TypedSpec (RegistrationNativePlatformIdentityCtxMain.M n KemSK Platform source)) (work : OracleComp TypedSpec Value)
    (before : Full (n := n) (KemSK := KemSK) (Platform := Platform) (mlSource := source)) (prior : Known before.2)
    (result : Value × Full (n := n) (KemSK := KemSK) (Platform := Platform) (mlSource := source))
    (supported : result ∈ support ((simulateQ (RegistrationNativeIdentityCensorPublicSource.callback
      (RegistrationNativeIdentityCensorSource.censored joint selected placeholder)
      (RegistrationNativeIdentityCensorPublicClient.callback selected position placeholder frontend)) work).run before)) : Known result.2.2 := by
  apply OracleComp.simulateQ_run_preserves_inv_of_query _ (fun current => Known current.2) _ work before prior result supported
  intro query current held returned called
  exact callback joint selected position placeholder frontend query current held returned called
end Main

end BeaconcryptCore.Computational.RegistrationNativeIdentityCensorCacheProvenance

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorCacheProvenance.query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorCacheProvenance.query
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorCacheProvenance.program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorCacheProvenance.program
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorCacheProvenance.initialized' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorCacheProvenance.initialized

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorCacheProvenance.main' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorCacheProvenance.main

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorCacheProvenance.callback' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorCacheProvenance.callback

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorCacheProvenance.adaptive' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorCacheProvenance.adaptive
