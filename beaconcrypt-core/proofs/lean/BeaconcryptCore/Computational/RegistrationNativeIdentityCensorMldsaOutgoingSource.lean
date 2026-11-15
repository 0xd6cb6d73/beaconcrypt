-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorEdOutgoingSource
import BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxMldsaCoins
/-! Actual ML outgoing source coupling uses its derived uniform-only syntax, retaining every optional reply, true native counter and P. Equal complete signing requests may carry different private payload/digest annotations; only compact receipts are projected. Private Mode, hash, target, canonical signature, framing, generated seed table and non-uniform signing history are preserved. No whole-handler equality or security conclusion is a premise. -/
open OracleComp OracleSpec CoreModels Aeneas beaconcrypt_core
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityCensorMldsaOutgoingSource
open PqxdhServerAuthExperiment (Setup Checks)
open PqxdhEd25519EufCma (Ed25519Signature)
open RegistrationNativeIdentityCensorCompiler (Mode)
open RegistrationNativePlatformIdentityCtxMldsaCoins (Coin)
open RegistrationNativeIdentityCensorEdOutgoingSource (Full interpret)
variable {n : Nat} {I KemSK Platform A B : Type} {base : OracleSpec I} {mlSource : RegistrationNativeMldsa.Source}
abbrev Private := RegistrationNativeIdentityCensorSource.State
abbrev Spec := RegistrationNativePlatformIdentityCtxCompiler.Spec

def stable (mode : Mode) (before : Private) : Mode × Private :=
  (mode, {before with pool := RegistrationNativeIdentityCompiler.poolView before.pool})

noncomputable def run (joint : PqxdhJointIdentity.Primitives) (selected : Nat) (placeholder : Ed25519Signature)
    (censored : Bool) (work : OracleComp Spec A) (mode : Mode) (before : Private) : ProbComp ((A × Mode) × Private) :=
  (simulateQ (if censored then RegistrationNativeIdentityCensorSource.censored joint selected placeholder
    else RegistrationNativeIdentityCensorSource.implementation joint selected)
    ((simulateQ (RegistrationNativeIdentityCensorOperational.implementation selected placeholder) work).run mode)).run before

private theorem run_bind (joint : PqxdhJointIdentity.Primitives) (selected : Nat) (placeholder : Ed25519Signature)
    (censored : Bool) (work : OracleComp Spec A) (next : A → OracleComp Spec B) (mode : Mode) (before : Private) :
    run joint selected placeholder censored (work >>= next) mode before = (do
      let result ← run joint selected placeholder censored work mode before
      run joint selected placeholder censored (next result.1.1) result.1.2 result.2) := by
  simp only [run, simulateQ_bind, StateT.run_bind]

private theorem run_pure (joint : PqxdhJointIdentity.Primitives) (selected : Nat) (placeholder : Ed25519Signature)
    (censored : Bool) (value : A) (mode : Mode) (before : Private) :
    run joint selected placeholder censored (pure value) mode before = pure ((value, mode), before) := by
  simp only [run, simulateQ_pure, StateT.run_pure]

private theorem lift_apply {S X : Type} {m : Type → Type} [Monad m]
    (work : m X) (before : S) :
    (StateT.lift work : StateT S m X) before = (do let reply ← work; pure (reply, before)) := rfl

private theorem map_apply {S X Y : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (change : X → Y) (work : StateT S m X) (before : S) :
    (change <$> work) before = Prod.map change id <$> work before := StateT.run_map change work before

private theorem operational_coin (selected : Nat) (placeholder : Ed25519Signature)
    (coin : unifSpec.Domain) (mode : Mode) :
    (RegistrationNativeIdentityCensorOperational.implementation selected placeholder
      (.inl (.inl (.inl coin)))).run mode =
      (RegistrationNativeIdentityCensorOperational.promote
        (StateT.lift (RegistrationNativeIdentityCensorCompiler.protocol (.inl (.inl coin))))).run mode := rfl

private theorem run_coin (joint : PqxdhJointIdentity.Primitives) (selected : Nat) (placeholder : Ed25519Signature)
    (censored : Bool) (coin : unifSpec.Domain) (mode : Mode) (before : Private) :
    run joint selected placeholder censored (Spec.query (.inl (.inl (.inl coin))) : OracleComp Spec (unifSpec.Range coin)) mode before =
      (fun answer : unifSpec.Range coin => ((answer, mode), {before with pool := PqxdhDynamicIdentityPool.record (.inl coin) answer before.pool})) <$>
        (unifSpec.query coin : ProbComp (unifSpec.Range coin)) := by
  rw [run, simulateQ_spec_query, operational_coin]
  cases censored <;>
    simp only [Bool.false_eq_true, ite_false, ite_true,
      RegistrationNativeIdentityCensorOperational.promote,
      RegistrationNativeIdentityCensorOperational.embed,
      RegistrationNativeIdentityCensorCompiler.protocol,
      lift_apply, bind_pure_comp, simulateQ_map,
      map_apply, simulateQ_spec_query,
      RegistrationNativeIdentityCensorSource.censored,
      RegistrationNativeIdentityCensorSource.implementation,
      RegistrationNativeIdentityCensorSource.protocol,
      RegistrationNativeIdentityMainSource.implementation,
      PqxdhDynamicIdentityPool.lazyImpl, PqxdhDynamicIdentityPool.poolImpl,
      StateT.run, Functor.map_map] <;> rfl

/-- Real and private-censored interpretations agree exactly for every derived uniform-only source tree. -/
theorem uniform_equal (joint : PqxdhJointIdentity.Primitives) (selected : Nat) (placeholder : Ed25519Signature)
    (work : OracleComp Spec A) (allowed : work.AllQueriesSatisfy Coin) (mode : Mode) (before : Private) :
    run joint selected placeholder false work mode before = run joint selected placeholder true work mode before := by
  induction work using OracleComp.inductionOn generalizing mode before with
  | pure value => rw [run_pure, run_pure]
  | query_bind query next ih =>
    rw [allQueriesSatisfy_query_bind_iff] at allowed
    rcases query with ((coin | service) | report) | bytes
    · rw [run_bind, run_bind, run_coin, run_coin]
      exact bind_congr (fun result => ih result.1.1 (allowed.2 result.1.1) result.1.2 result.2)
    · exact False.elim allowed.1
    · exact False.elim allowed.1
    · exact False.elim allowed.1

/-- Only chronological uniform transcript entries can change in the private source during these trees; Mode, hash, target, canonical, framing and seed table are exact. -/
theorem uniform_frame (joint : PqxdhJointIdentity.Primitives) (selected : Nat) (placeholder : Ed25519Signature)
    (censored : Bool) (work : OracleComp Spec A) (allowed : work.AllQueriesSatisfy Coin) (mode : Mode) (before : Private)
    (result : (A × Mode) × Private) (supported : result ∈ support (run joint selected placeholder censored work mode before)) :
    stable result.1.2 result.2 = stable mode before := by
  induction work using OracleComp.inductionOn generalizing mode before with
  | pure value =>
    rw [run_pure, support_pure, Set.mem_singleton_iff] at supported
    subst result
    rfl
  | query_bind query next ih =>
    rw [allQueriesSatisfy_query_bind_iff] at allowed
    rcases query with ((coin | service) | report) | bytes
    · rw [run_bind, mem_support_bind_iff] at supported
      obtain ⟨middle, drawn, later⟩ := supported
      have unchanged : stable middle.1.2 middle.2 = stable mode before := by
        rw [run_coin, support_map] at drawn
        obtain ⟨answer, _possible, rfl⟩ := drawn
        simp only [stable, RegistrationNativeIdentityCompiler.poolView, PqxdhDynamicIdentityPool.record,
          List.filter_append, List.filter_cons, RegistrationNativeIdentityCompiler.keep,
          Bool.false_eq_true, ↓reduceIte, List.filter_nil, List.append_nil]
      exact (ih middle.1.1 (allowed.2 middle.1.1) middle.1.2 middle.2 later).trans unchanged
    · exact False.elim allowed.1
    · exact False.elim allowed.1
    · exact False.elim allowed.1

private theorem run_map (joint : PqxdhJointIdentity.Primitives) (selected : Nat) (placeholder : Ed25519Signature)
    (censored : Bool) (change : A → B) (work : OracleComp Spec A) (mode : Mode) (before : Private) :
    run joint selected placeholder censored (change <$> work) mode before =
      Prod.map (Prod.map change id) id <$> run joint selected placeholder censored work mode before := by
  simp only [run, simulateQ_map, StateT.run_map]
  rfl

private def close (result : ((A × (RegistrationNativeIdentityMain.State n KemSK mlSource × Platform)) × Mode) × Private) :
    A × Full (n := n) (KemSK := KemSK) (Platform := Platform) (mlSource := mlSource) :=
  (result.1.1.1, ((result.1.1.2, result.1.2), result.2))

private theorem interpreted (joint : PqxdhJointIdentity.Primitives) (selected : Nat) (placeholder : Ed25519Signature)
    (censored : Bool) (work : RegistrationNativePlatformIdentityCtxMain.M n KemSK Platform mlSource A)
    (before : Full (n := n) (KemSK := KemSK) (Platform := Platform) (mlSource := mlSource)) :
    (interpret joint selected placeholder censored work).run before =
      close <$> run joint selected placeholder censored (work.run before.1.1) before.1.2 before.2 := by
  simp only [interpret, StateT.run, run, bind_pure_comp]
  rfl

def view (before : Full (n := n) (KemSK := KemSK) (Platform := Platform) (mlSource := mlSource)) :=
  ((RegistrationNativePlatformIdentityCtxReceiptView.view before.1.1, before.1.2), before.2)

section Actual
variable (setup : Setup base KemSK) (checks : Checks)
variable (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
variable (selected index : Nat) (owner : RegistrationNativeIdentityFrontend.Owner mlSource) (request : registration.MldsaSigningRequest)
variable (placeholder : Ed25519Signature)
local notation "action(" payload "," digest ")" => RegistrationNativePlatformIdentityCtxMain.beacon setup checks representation created
  (RegistrationNativePlatformIdentityProgram.native
    (RegistrationNativeIdentityFrontend.outgoing (n := n) (Auxiliary := RegistrationServerRoleBackend.State)
      setup mlSource index owner (Sum.inl (RegistrationSigningShared.Request.sign request payload digest))))

/-- Same ML request and arbitrary current annotations have identical full real/private-censored outcomes after clearing only compact ML receipts. -/
theorem outgoing (left right : MldsaTranscriptAuth.Payload) (digestLeft digestRight : CtxRomAuth.CtxDigest)
    (before : Full (n := n) (KemSK := KemSK) (Platform := Platform) (mlSource := mlSource)) :
    Prod.map id view <$> (interpret setup.joint selected placeholder false (action(left, digestLeft))).run before =
      Prod.map id view <$> (interpret setup.joint selected placeholder true (action(right, digestRight))).run before := by
  have metadata := RegistrationNativePlatformIdentityCtxOutgoingMetadata.outgoing setup checks representation created
    index owner request left right digestLeft digestRight before.1.1
  have transported := congrArg (fun script => close <$>
    run setup.joint selected placeholder false script before.1.2 before.2) metadata
  simp only [run_map, Functor.map_map, close, Prod.map_def, id_eq] at transported
  rw [interpreted, interpreted]
  rw [← uniform_equal setup.joint selected placeholder _
    (RegistrationNativePlatformIdentityCtxMldsaCoins.outgoing setup checks representation created index owner request right digestRight before.1.1)]
  simpa only [Functor.map_map, close, view, Prod.map_def, id_eq] using transported

/-- The actual ML source callback preserves complete Mode and private state except appended uniform transcript entries on every supported optional reply. -/
theorem frame (censored : Bool) (payload : MldsaTranscriptAuth.Payload) (digest : CtxRomAuth.CtxDigest)
    (before : Full (n := n) (KemSK := KemSK) (Platform := Platform) (mlSource := mlSource))
    (result : RegistrationSigningShared.SignReply × Full (n := n) (KemSK := KemSK) (Platform := Platform) (mlSource := mlSource))
    (supported : result ∈ support ((interpret setup.joint selected placeholder censored (action(payload, digest))).run before)) :
    stable result.2.1.2 result.2.2 = stable before.1.2 before.2 := by
  rw [interpreted, support_map] at supported
  obtain ⟨inner, possible, rfl⟩ := supported
  exact uniform_frame setup.joint selected placeholder censored _
    (RegistrationNativePlatformIdentityCtxMldsaCoins.outgoing setup checks representation created index owner request payload digest before.1.1)
    before.1.2 before.2 inner possible
end Actual
end BeaconcryptCore.Computational.RegistrationNativeIdentityCensorMldsaOutgoingSource

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorMldsaOutgoingSource.uniform_equal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorMldsaOutgoingSource.uniform_equal

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorMldsaOutgoingSource.uniform_frame' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorMldsaOutgoingSource.uniform_frame

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorMldsaOutgoingSource.outgoing' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorMldsaOutgoingSource.outgoing

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorMldsaOutgoingSource.frame' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorMldsaOutgoingSource.frame
