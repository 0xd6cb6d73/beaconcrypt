-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorSourceFold
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorMldsaOutgoingSource
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorOperationalPrefix
import BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxSignScope

/-! Every actual non-bundle typed callback has no indexed Ed signing leaf. Its operational source tree therefore contains no omitted-signature marker, so real and private-censored interpretations agree exactly even after target selection. Combining the literal prior-log law gives the same complete projected callback from equal prior joint views. -/
open OracleComp OracleSpec CoreModels Aeneas beaconcrypt_core
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityCensorQuietSource
open PqxdhEd25519EufCma (Ed25519Signature)
open RegistrationNativeIdentityCensorCompiler (Mode)
open RegistrationNativeIdentityCensorEdOutgoingSource (Full interpret)
open RegistrationNativePlatformIdentityCtxSignScope (Allowed)
variable {A B : Type}
abbrev Spec := RegistrationNativePlatformIdentityCtxCompiler.Spec
abbrev OpSpec := RegistrationNativeIdentityCensorOperational.Spec
abbrev Private := RegistrationNativeIdentityCensorSource.State

private def NoOmitted : OpSpec.Domain → Prop
  | .inr (.omitted _ _) => False
  | _ => True

private theorem mapped {J X Y : Type} {queries : OracleSpec J}
    (work : OracleComp queries X) (change : X → Y) (predicate : J → Prop)
    (allowed : work.AllQueriesSatisfy predicate) : (change <$> work).AllQueriesSatisfy predicate := by
  rw [map_eq_bind_pure_comp]
  exact allQueriesSatisfy_bind allowed (fun _ => allQueriesSatisfy_pure _ _)

private theorem promote_run (work : StateT Mode (OracleComp RegistrationNativeIdentityCensorCompiler.Spec) A) (before : Mode) :
    (RegistrationNativeIdentityCensorOperational.promote work).run before =
      simulateQ RegistrationNativeIdentityCensorOperational.embed (work.run before) := rfl

private theorem embed_safe (work : OracleComp RegistrationNativeIdentityCensorCompiler.Spec A) :
    (simulateQ RegistrationNativeIdentityCensorOperational.embed work).AllQueriesSatisfy NoOmitted := by
  induction work using OracleComp.inductionOn with
  | pure value => trivial
  | query_bind query next ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, RegistrationNativeIdentityCensorOperational.embed]
    exact (allQueriesSatisfy_query_bind_iff _ _ _).mpr ⟨trivial, ih⟩

private theorem hash_run (selected : Nat) (placeholder : Ed25519Signature) (bytes : Pqxdh.Bytes) (before : Mode) :
    (RegistrationNativeIdentityCensorOperational.implementation selected placeholder (.inr bytes)).run before =
      (match (RegistrationNativeIdentityCensorCompiler.hashInput before bytes).input with
      | some _ => (RegistrationNativeIdentityCensorOperational.promote
          (RegistrationNativeIdentityCensorCompiler.implementation selected placeholder (.inr bytes))).run before
      | none => do
          let reply ← (OpSpec.query (.inr (.template selected before.target
            (RegistrationNativeIdentityCensorOperational.parts bytes).1 (RegistrationNativeIdentityCensorOperational.parts bytes).2)) : OracleComp OpSpec _)
          pure (reply, before)) := rfl

private theorem query_safe (selected : Nat) (placeholder : Ed25519Signature) (query : Spec.Domain)
    (allowed : Allowed query) (before : Mode) :
    ((RegistrationNativeIdentityCensorOperational.implementation selected placeholder query).run before).AllQueriesSatisfy NoOmitted := by
  rcases query with ((coin | request) | report) | bytes
  · exact embed_safe _
  · cases request with
    | create | reveal handle => exact embed_safe _
    | service handle request => cases request with
      | staticDh peer => exact embed_safe _
      | sign message => exact False.elim (allowed True.intro)
  · exact embed_safe _
  · rw [hash_run]
    cases (RegistrationNativeIdentityCensorCompiler.hashInput before bytes).input with
    | some input => rw [promote_run]; exact embed_safe _
    | none => exact (allQueriesSatisfy_query_bind_iff _ _ _).mpr ⟨trivial, fun _ => trivial⟩

private theorem program_safe (selected : Nat) (placeholder : Ed25519Signature) (work : OracleComp Spec A)
    (allowed : work.AllQueriesSatisfy Allowed) (before : Mode) :
    ((simulateQ (RegistrationNativeIdentityCensorOperational.implementation selected placeholder) work).run before).AllQueriesSatisfy NoOmitted := by
  induction work using OracleComp.inductionOn generalizing before with
  | pure value => simp only [simulateQ_pure, StateT.run_pure]; trivial
  | query_bind query next ih =>
    rw [allQueriesSatisfy_query_bind_iff] at allowed
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
    exact allQueriesSatisfy_bind (query_safe selected placeholder query allowed.1 before)
      (fun result => ih result.1 (allowed.2 result.1) result.2)

private theorem source_same (joint : PqxdhJointIdentity.Primitives) (selected : Nat) (placeholder : Ed25519Signature)
    (work : OracleComp OpSpec A) (allowed : work.AllQueriesSatisfy NoOmitted) (before : Private) :
    (simulateQ (RegistrationNativeIdentityCensorSource.implementation joint selected) work).run before =
      (simulateQ (RegistrationNativeIdentityCensorSource.censored joint selected placeholder) work).run before := by
  induction work using OracleComp.inductionOn generalizing before with
  | pure value => simp only [simulateQ_pure, StateT.run_pure]
  | query_bind query next ih =>
    rw [allQueriesSatisfy_query_bind_iff] at allowed
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
    have same : RegistrationNativeIdentityCensorSource.implementation joint selected query =
        RegistrationNativeIdentityCensorSource.censored joint selected placeholder query := by
      cases query with
      | inl query => rfl
      | inr query => cases query with
        | omitted handle message => exact False.elim allowed.1
        | template handle message leading trailing => rfl
    rw [same]
    exact bind_congr (fun result => ih result.1 (allowed.2 result.1) result.2)

/-- The exact source interpretations agree on every structurally nonsigning tree, retaining all private physical state and optional replies. -/
theorem program (joint : PqxdhJointIdentity.Primitives) (selected : Nat) (placeholder : Ed25519Signature)
    (work : OracleComp Spec A) (allowed : work.AllQueriesSatisfy Allowed) (before : Mode) (privateBefore : Private) :
    RegistrationNativeIdentityCensorMldsaOutgoingSource.run joint selected placeholder false work before privateBefore =
      RegistrationNativeIdentityCensorMldsaOutgoingSource.run joint selected placeholder true work before privateBefore := by
  exact source_same joint selected placeholder _ (program_safe selected placeholder work allowed before) privateBefore

/-- Before the public guessed bundle is armed, even signing trees have no omission marker; both interpretations retain their entire identical source state. -/
theorem unarmed (joint : PqxdhJointIdentity.Primitives) (selected : Nat) (placeholder : Ed25519Signature)
    (work : OracleComp Spec A) (before : Mode) (prior : RegistrationNativeIdentityCensorPrefix.Unarmed before)
    (privateBefore : Private) :
    RegistrationNativeIdentityCensorMldsaOutgoingSource.run joint selected placeholder false work before privateBefore =
      RegistrationNativeIdentityCensorMldsaOutgoingSource.run joint selected placeholder true work before privateBefore := by
  simp only [RegistrationNativeIdentityCensorMldsaOutgoingSource.run, Bool.false_eq_true, ite_false, ite_true]
  rw [RegistrationNativeIdentityCensorOperationalPrefix.program selected placeholder work before prior]
  exact source_same joint selected placeholder _ (embed_safe _) privateBefore

section Actual
open PqxdhServerAuthExperiment (Setup Checks)
variable {n : Nat} {I KemSK Platform E : Type} {base : OracleSpec I} {mlSource : RegistrationNativeMldsa.Source}
variable [primitive : BeaconcryptCore.Refinement.AdapterSealPrimitive.Operations]
variable (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
variable (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
variable (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (credential : RegistrationNativeMldsa.Credential mlSource)
variable (keys : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
variable (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
variable (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
variable (reserveFrame : Nat → StateT Platform ProbComp (core.result.Result Unit E)) (erased : commitment.CommitmentTranscript)
variable (helper : QueryImpl (BeaconcryptCore.Refinement.AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
variable (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
local notation "actual" => RegistrationNativePlatformIdentityCtxTyped.handler (n := n) setup checks wire route representation created credential
  keys failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
local notation "FullState" => Full (n := n) (KemSK := KemSK) (Platform := Platform) (mlSource := mlSource)

/-- Every literal non-bundle callback derives the needed syntactic restriction internally, including failed accepts, raw routing and corrected assigned-ID finish. -/
theorem callback (selected : Nat) (placeholder : Ed25519Signature) (query : RegistrationNativeRawAdapter.TypedSpec.Domain)
    (notBundle : ∀ index, query ≠ .inr (.bundle index)) (before : FullState) :
    (interpret setup.joint selected placeholder false (actual query)).run before =
      (interpret setup.joint selected placeholder true (actual query)).run before := by
  have same := congrArg (fun distribution => (fun result =>
      (result.1.1.1, ((result.1.1.2, result.1.2), result.2))) <$> distribution)
    (program setup.joint selected placeholder ((actual query).run before.1.1)
      (RegistrationNativePlatformIdentityCtxSignScope.handler_safe setup checks wire route representation created credential keys failure allocation
        reserveRegistration reservePeer reserveFrame erased helper writer query notBundle before.1.1)
      before.1.2 before.2)
  simpa only [interpret, StateT.run, RegistrationNativeIdentityCensorMldsaOutgoingSource.run, bind_pure_comp] using same

/-- Equal prior joint observations suffice for the actual non-bundle callback. Only raw stored Ed slots and compact ML receipts are projected; current replies and full private/P coordinates remain in the result. -/
theorem paired (selected : Nat) (placeholder : Ed25519Signature) (query : RegistrationNativeRawAdapter.TypedSpec.Domain)
    (notBundle : ∀ index, query ≠ .inr (.bundle index)) (left right : FullState)
    (same : RegistrationNativeIdentityCensorOutgoingView.view placeholder left =
      RegistrationNativeIdentityCensorOutgoingView.view placeholder right) :
    Prod.map id (RegistrationNativeIdentityCensorOutgoingView.view placeholder) <$>
      (interpret setup.joint selected placeholder false (actual query)).run left =
      Prod.map id (RegistrationNativeIdentityCensorOutgoingView.view placeholder) <$>
        (interpret setup.joint selected placeholder true (actual query)).run right := by
  have law := RegistrationNativePlatformIdentityCtxTypedJointView.handler_stable (n := n) setup checks wire route representation created credential keys failure allocation
    reserveRegistration reservePeer reserveFrame erased helper writer placeholder query
  rw [RegistrationNativeIdentityCensorOutgoingView.interpreted setup.joint selected placeholder false (actual query) law left,
    RegistrationNativeIdentityCensorOutgoingView.interpreted setup.joint selected placeholder true (actual query) law right,
    same,
    callback setup checks wire route representation created credential keys failure allocation reserveRegistration reservePeer reserveFrame
      erased helper writer selected placeholder query notBundle]

private theorem block_safe (work : OracleComp RegistrationNativeRawAdapter.TypedSpec A)
    (allowed : work.AllQueriesSatisfy (fun query => ∀ index, query ≠ .inr (.bundle index)))
    (before : RegistrationNativeIdentityMain.State n KemSK mlSource × Platform) :
    ((simulateQ actual work).run before).AllQueriesSatisfy Allowed := by
  induction work using OracleComp.inductionOn generalizing before with
  | pure value => simp only [simulateQ_pure, StateT.run_pure]; trivial
  | query_bind query next ih =>
    rw [allQueriesSatisfy_query_bind_iff] at allowed
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
    exact allQueriesSatisfy_bind
      (RegistrationNativePlatformIdentityCtxSignScope.handler_safe setup checks wire route representation created credential keys failure allocation
        reserveRegistration reservePeer reserveFrame erased helper writer query allowed.1 before)
      (fun result => ih result.1 (allowed.2 result.1) result.2)

/-- An arbitrary adaptive block of actual non-bundle callbacks preserves the same joint stopped-source observation, without an ownership or whole-handler simulation premise. -/
theorem block (selected : Nat) (placeholder : Ed25519Signature)
    (work : OracleComp RegistrationNativeRawAdapter.TypedSpec A)
    (allowed : work.AllQueriesSatisfy (fun query => ∀ index, query ≠ .inr (.bundle index)))
    (left right : FullState)
    (same : RegistrationNativeIdentityCensorOutgoingView.view placeholder left =
      RegistrationNativeIdentityCensorOutgoingView.view placeholder right) :
    Prod.map id (RegistrationNativeIdentityCensorOutgoingView.view placeholder) <$>
      (interpret setup.joint selected placeholder false (simulateQ actual work)).run left =
      Prod.map id (RegistrationNativeIdentityCensorOutgoingView.view placeholder) <$>
        (interpret setup.joint selected placeholder true (simulateQ actual work)).run right := by
  have law := RegistrationNativePlatformIdentityCtxTypedJointView.program_stable (n := n) setup checks wire route representation created credential keys failure allocation
    reserveRegistration reservePeer reserveFrame erased helper writer placeholder work
  rw [RegistrationNativeIdentityCensorOutgoingView.interpreted setup.joint selected placeholder false _ law left,
    RegistrationNativeIdentityCensorOutgoingView.interpreted setup.joint selected placeholder true _ law right, same]
  have exactSource := congrArg (fun distribution => (fun result =>
      (result.1.1.1, ((result.1.1.2, result.1.2), result.2))) <$> distribution)
    (program setup.joint selected placeholder ((simulateQ actual work).run (RegistrationNativeIdentityCensorOutgoingView.view placeholder right).1.1)
      (block_safe setup checks wire route representation created credential keys failure allocation reserveRegistration reservePeer reserveFrame
        erased helper writer work allowed _)
      (RegistrationNativeIdentityCensorOutgoingView.view placeholder right).1.2
      (RegistrationNativeIdentityCensorOutgoingView.view placeholder right).2)
  have full : (interpret setup.joint selected placeholder false (simulateQ actual work)).run
        (RegistrationNativeIdentityCensorOutgoingView.view placeholder right) =
      (interpret setup.joint selected placeholder true (simulateQ actual work)).run
        (RegistrationNativeIdentityCensorOutgoingView.view placeholder right) := by
    simpa only [interpret, StateT.run, RegistrationNativeIdentityCensorMldsaOutgoingSource.run, bind_pure_comp] using exactSource
  rw [full]

end Actual
end BeaconcryptCore.Computational.RegistrationNativeIdentityCensorQuietSource
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorQuietSource.program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorQuietSource.program
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorQuietSource.unarmed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorQuietSource.unarmed
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorQuietSource.callback' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorQuietSource.callback
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorQuietSource.paired' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorQuietSource.paired
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorQuietSource.block' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorQuietSource.block
