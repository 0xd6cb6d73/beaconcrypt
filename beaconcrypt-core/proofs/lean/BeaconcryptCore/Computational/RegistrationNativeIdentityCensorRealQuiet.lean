-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorRealSigning
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorQuietSource

/-! Every actual nonsigning callback starts with its public token inactive. Its complete canonical source run therefore has the literal original private-source marginal, even after a target has been selected. The proof retains every current reply, generated table, warm cache and physical journal; only censor metadata is erased. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityCensorRealQuiet
open PqxdhEd25519EufCma (Ed25519Signature)
open RegistrationNativeIdentityCensorCompiler (Mode)
open RegistrationNativeIdentityCensorRealSigning (Spec Private closed project)
open RegistrationNativePlatformIdentityCtxSignScope (Allowed)
variable {A : Type}

private theorem bind_apply {S X Y : Type} {m : Type → Type} [Monad m]
    (work : StateT S m X) (next : X → StateT S m Y) (before : S) :
    (work >>= next) before = (do let result ← work before; next result.1 result.2) := rfl
private theorem pure_apply {S X : Type} {m : Type → Type} [Monad m] (value : X) (before : S) :
    (pure value : StateT S m X) before = pure (value, before) := rfl

private def plain : (request : Spec.Domain) → Mode →
    OracleComp RegistrationNativeIdentityCensorOperational.Spec (Spec.Range request × Mode)
  | .inl query, before => do
      let reply ← (RegistrationNativeIdentityCensorOperational.Spec.query (.inl (.inl (.inl (.inl query)))) :
        OracleComp RegistrationNativeIdentityCensorOperational.Spec (PqxdhJointPhase1Reports.ProtocolSpec.Range query))
      pure (reply, before)
  | .inr bytes, before => do
      let reply ← (RegistrationNativeIdentityCensorOperational.Spec.query (.inl (.inr ⟨before.target, some bytes⟩)) :
        OracleComp RegistrationNativeIdentityCensorOperational.Spec (CtxRomAuth.CtxDigest × Nat))
      pure (reply, {before with knownInputs := before.knownInputs ++ [bytes]})

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

private theorem query_plain (selected : Nat) (placeholder : Ed25519Signature) (request : Spec.Domain)
    (allowed : Allowed request) (before : Mode) (inactive : before.active = false) :
    (RegistrationNativeIdentityCensorOperational.implementation selected placeholder request).run before = plain request before := by
  rcases request with ((coin | request) | report) | bytes
  · rfl
  · cases request with
    | create | reveal handle => rfl
    | service handle request => cases request with
      | staticDh peer => rfl
      | sign message => exact False.elim (allowed True.intro)
  · rfl
  · rw [hash_run]
    simp only [RegistrationNativeIdentityCensorCompiler.hashInput, inactive, Bool.false_eq_true, ite_false]
    simp only [RegistrationNativeIdentityCensorOperational.promote, RegistrationNativeIdentityCensorCompiler.implementation,
      RegistrationNativeIdentityCensorCompiler.hashInput, inactive, Bool.false_eq_true, ite_false, StateT.run,
      simulateQ_bind, simulateQ_spec_query, RegistrationNativeIdentityCensorOperational.embed, simulateQ_pure, plain]
    rw [inactive]
    rfl

private def restore (before : Mode × Private) (request : Spec.Domain)
    (after : RegistrationNativePlatformIdentityCtxSource.State) : Mode × Private :=
  (RegistrationNativeIdentityCensorPrefix.next before.1 request, {before.2 with pool := after.1, hash := after.2})

private theorem plain_source (joint : PqxdhJointIdentity.Primitives) (selected : Nat) (request : Spec.Domain)
    (before : Mode × Private) :
    (fun result => (result.1.1, (result.1.2, result.2))) <$>
      (simulateQ (RegistrationNativeIdentityCensorSource.implementation joint selected) (plain request before.1)).run before.2 =
      (fun result => (result.1, restore before request result.2)) <$>
        (RegistrationNativePlatformIdentityCtxSource.implementation joint request).run (project before) := by
  cases request with
  | inl query =>
    simp only [plain, simulateQ_bind, simulateQ_spec_query, RegistrationNativeIdentityCensorSource.implementation,
      simulateQ_pure, StateT.run, bind_apply, RegistrationNativeIdentityCensorSource.protocol,
      pure_apply, RegistrationNativePlatformIdentityCtxSource.implementation, map_bind, bind_map_left,
      map_pure, Functor.map_map, restore, project]
    rw [bind_pure_comp]
    rfl
  | inr bytes =>
    simp only [plain, simulateQ_bind, simulateQ_spec_query, RegistrationNativeIdentityCensorSource.implementation,
      simulateQ_pure, StateT.run, bind_apply, RegistrationNativeIdentityCensorSource.physical,
      pure_apply, RegistrationNativePlatformIdentityCtxSource.implementation, map_bind, bind_map_left,
      map_pure, Functor.map_map, restore, project]
    rw [bind_pure_comp]
    rfl

private theorem query (joint : PqxdhJointIdentity.Primitives) (selected : Nat) (placeholder : Ed25519Signature)
    (request : Spec.Domain) (allowed : Allowed request) (before : Mode × Private) (inactive : before.1.active = false) :
    (closed joint selected placeholder request).run before =
      (fun result => (result.1, restore before request result.2)) <$>
        (RegistrationNativePlatformIdentityCtxSource.implementation joint request).run (project before) := by
  rw [closed, QueryImpl.Stateful.link_impl_apply_run, query_plain selected placeholder request allowed before.1 inactive]
  change (fun result => (result.1.1, (result.1.2, result.2))) <$>
      (simulateQ (RegistrationNativeIdentityCensorSource.implementation joint selected) (plain request before.1)).run before.2 = _
  exact plain_source joint selected request before

private theorem restore_inactive (before : Mode × Private) (inactive : before.1.active = false)
    (request : Spec.Domain) (after : RegistrationNativePlatformIdentityCtxSource.State) :
    (restore before request after).1.active = false := by
  cases request <;> exact inactive

/-- Inactive nonsigning adaptive source work has exactly its original full private-source marginal. No source row, acceptance or prior-history premise is required. -/
theorem program (joint : PqxdhJointIdentity.Primitives) (selected : Nat) (placeholder : Ed25519Signature)
    (work : OracleComp Spec A) (allowed : work.AllQueriesSatisfy Allowed) (before : Mode × Private)
    (inactive : before.1.active = false) :
    Prod.map id project <$> (simulateQ (closed joint selected placeholder) work).run before =
      (simulateQ (RegistrationNativePlatformIdentityCtxSource.implementation joint) work).run (project before) := by
  induction work using OracleComp.inductionOn generalizing before with
  | pure value => simp only [simulateQ_pure, StateT.run_pure, map_pure, Prod.map_apply, id_eq]
  | query_bind request next ih =>
    rw [allQueriesSatisfy_query_bind_iff] at allowed
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, map_bind]
    rw [query joint selected placeholder request allowed.1 before inactive, bind_map_left]
    apply bind_congr
    intro result
    exact ih result.1 (allowed.2 result.1) (restore before request result.2)
      (restore_inactive before inactive request result.2)

section Main
open RegistrationNativeIdentityCensorEdOutgoingSource (Full interpret)
variable {n : Nat} {I KemSK Platform : Type} {base : OracleSpec I} {mlSource : RegistrationNativeMldsa.Source}

/-- The inactive nonsigning source marginal retains the complete actual Main/P transformer, pool and physical CTX journal. -/
theorem main (joint : PqxdhJointIdentity.Primitives) (selected : Nat) (placeholder : Ed25519Signature)
    (work : RegistrationNativePlatformIdentityCtxMain.M n KemSK Platform mlSource A)
    (before : Full (n := n) (KemSK := KemSK) (Platform := Platform) (mlSource := mlSource))
    (allowed : (work.run before.1.1).AllQueriesSatisfy Allowed) (inactive : before.1.2.active = false) :
    Prod.map id RegistrationNativeIdentityCensorActualHashSource.project <$>
      (interpret joint selected placeholder false work).run before =
      (RegistrationNativePlatformIdentityCtxMain.interpret joint work).run
        (RegistrationNativeIdentityCensorActualHashSource.project before) := by
  have law := program joint selected placeholder (work.run before.1.1) allowed (before.1.2, before.2) inactive
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

variable {E : Type} [primitive : BeaconcryptCore.Refinement.AdapterSealPrimitive.Operations]
variable (setup : PqxdhServerAuthExperiment.Setup base KemSK) (checks : PqxdhServerAuthExperiment.Checks)
variable (wire : RegistrationNativeWire.Wire) (route : RawCtxServerRouting.SenderDecoder)
variable (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
variable (credential : RegistrationNativeMldsa.Credential mlSource) (keys : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
variable (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
variable (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
variable (reserveFrame : Nat → StateT Platform ProbComp (core.result.Result Unit E)) (erased : commitment.CommitmentTranscript)
variable (helper : QueryImpl (BeaconcryptCore.Refinement.AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
variable (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
local notation "actual" => RegistrationNativePlatformIdentityCtxTyped.handler (n := n) setup checks wire route representation created credential keys failure allocation
  reserveRegistration reservePeer reserveFrame erased helper writer

/-- Every literal non-bundle callback has the original source marginal in both canonical and private-censored runs. The actual callback's syntactic no-sign scope supplies all assumptions internally. -/
theorem callback (selected : Nat) (placeholder : Ed25519Signature) (censored : Bool)
    (query : RegistrationNativeRawAdapter.TypedSpec.Domain) (notBundle : ∀ index, query ≠ .inr (.bundle index))
    (before : Full (n := n) (KemSK := KemSK) (Platform := Platform) (mlSource := mlSource)) (inactive : before.1.2.active = false) :
    Prod.map id RegistrationNativeIdentityCensorActualHashSource.project <$>
      (interpret setup.joint selected placeholder censored (actual query)).run before =
      (RegistrationNativePlatformIdentityCtxMain.interpret setup.joint (actual query)).run
        (RegistrationNativeIdentityCensorActualHashSource.project before) := by
  have real := main setup.joint selected placeholder (actual query) before
    (RegistrationNativePlatformIdentityCtxSignScope.handler_safe setup checks wire route representation created credential keys failure allocation
      reserveRegistration reservePeer reserveFrame erased helper writer query notBundle before.1.1) inactive
  cases censored with
  | false => exact real
  | true =>
    rw [← RegistrationNativeIdentityCensorQuietSource.callback setup checks wire route representation created credential keys failure allocation
      reserveRegistration reservePeer reserveFrame erased helper writer selected placeholder query notBundle before]
    exact real

end Main

end BeaconcryptCore.Computational.RegistrationNativeIdentityCensorRealQuiet

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorRealQuiet.program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorRealQuiet.program

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorRealQuiet.main' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorRealQuiet.main

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorRealQuiet.callback' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorRealQuiet.callback
