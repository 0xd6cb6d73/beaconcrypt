-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorSourceFold
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorMldsaOutgoingSource
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorConcreteWriter

/-! External capacity/serialization actions use their literal P program and only independent uniform capabilities. The native and private source states are retained rather than supplied as an arbitrary writer frame. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityCensorExternalSource
open PqxdhServerAuthExperiment (Setup Checks)
open PqxdhEd25519EufCma (Ed25519Signature)
open RegistrationNativeIdentityCensorEdOutgoingSource (Full interpret)
open RegistrationNativePlatformIdentityCtxCompiler (Spec coins)
variable {n : Nat} {I KemSK Platform A : Type} {base : OracleSpec I} {mlSource : RegistrationNativeMldsa.Source}

private theorem lifted_coins {S X : Type} (work : ProbComp X) (before : S) :
    (simulateQ (r := StateT S (OracleComp Spec)) ((fun query state => (fun answer => (answer, state)) <$> coins query) :
      QueryImpl unifSpec (StateT S (OracleComp Spec))) work).run before =
      (fun value => (value, before)) <$> simulateQ coins work := by
  induction work using OracleComp.inductionOn with
  | pure value => simp only [simulateQ_pure, StateT.run_pure, map_pure]
  | query_bind query next ih =>
    rw [simulateQ_bind, StateT.run_bind]
    simp only [simulateQ_spec_query]
    change ((fun answer => (answer, before)) <$> coins query >>= fun result =>
      (simulateQ (r := StateT S (OracleComp Spec)) ((fun query state => (fun answer => (answer, state)) <$> coins query) :
        QueryImpl unifSpec (StateT S (OracleComp Spec))) (next result.1)).run result.2) = _
    simp only [simulateQ_bind, simulateQ_spec_query, map_bind, bind_map_left]
    exact bind_congr (fun answer => ih answer)

private theorem map_apply {S X Y : Type} (change : X → Y) (work : StateT S (OracleComp Spec) X) (before : S) :
    (change <$> work) before = Prod.map change id <$> work before := StateT.run_map change work before

/-- The literal Main closing lens leaves native state unchanged during external P work and exposes only its actual uniform tree. -/
theorem native (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (work : StateT Platform ProbComp A) (before : RegistrationNativeIdentityMain.State n KemSK mlSource × Platform) :
    (RegistrationNativePlatformIdentityCtxMain.beacon setup checks representation created
      (RegistrationNativePlatformIdentityProgram.external work)).run before =
      (fun result => (result.1, (before.1, result.2))) <$> simulateQ coins (work.run before.2) := by
  rw [RegistrationNativePlatformIdentityCtxOutgoingFold.run]
  simp only [RegistrationNativePlatformIdentityProgram.external, StateT.run, simulateQ_map]
  rw [← QueryImpl.simulateQ_compose]
  have composed : RegistrationNativePlatformIdentityCtxCompiler.free
      (RegistrationNativePlatformIdentityCtxAmbient.program (source := mlSource) setup checks representation created) ∘ₛ
      RegistrationNativePlatformIdentityProgram.externalLift =
      (fun query state => (fun answer => (answer, state)) <$> coins query :
        QueryImpl unifSpec (StateT (RegistrationNativeIdentityWorld.Context n KemSK) (OracleComp Spec))) := by
    funext query state
    rfl
  rw [composed]
  have shifted := lifted_coins (work.run before.2) before.1.context
  simp only [StateT.run] at shifted
  rw [map_apply, shifted]
  simp only [Functor.map_map, RegistrationNativePlatformIdentityCtxOutgoingFold.close,
    RegistrationNativePlatformIdentityCtxEnvPatch.patch, Prod.map_def, id_eq, RegistrationWorldAgreementCompiler.join_erase]

/-- Every actual mutable P writer or allocator uses only independent coin leaves; no source signing or hash request is hidden in that action. -/
theorem coin_only (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (work : StateT Platform ProbComp A) (before : RegistrationNativeIdentityMain.State n KemSK mlSource × Platform) :
    ((RegistrationNativePlatformIdentityCtxMain.beacon setup checks representation created
      (RegistrationNativePlatformIdentityProgram.external work)).run before).AllQueriesSatisfy
      RegistrationNativePlatformIdentityCtxMldsaCoins.Coin := by
  rw [native setup checks representation created work before]
  rw [map_eq_bind_pure_comp]
  apply allQueriesSatisfy_bind
  · induction work.run before.2 using OracleComp.inductionOn with
    | pure value => trivial
    | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, coins]
      exact (allQueriesSatisfy_query_bind_iff _ _ _).mpr ⟨trivial, ih⟩
  · intro _; trivial


/-- Mapping the returned P value retains the same full native source tree and state. -/
theorem native_map {B : Type} (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (change : A → B) (work : StateT Platform ProbComp A) :
    RegistrationNativePlatformIdentityCtxMain.beacon (n := n) (source := mlSource) setup checks representation created
      (RegistrationNativePlatformIdentityProgram.external (change <$> work)) =
      change <$> RegistrationNativePlatformIdentityCtxMain.beacon setup checks representation created
        (RegistrationNativePlatformIdentityProgram.external work) := by
  funext before
  change (RegistrationNativePlatformIdentityCtxMain.beacon setup checks representation created
    (RegistrationNativePlatformIdentityProgram.external (change <$> work))).run before =
      (change <$> RegistrationNativePlatformIdentityCtxMain.beacon setup checks representation created
        (RegistrationNativePlatformIdentityProgram.external work)).run before
  simp only [StateT.run_map, native, simulateQ_map, Functor.map_map]

private theorem interpret_map {B : Type} (joint : PqxdhJointIdentity.Primitives) (selected : Nat) (placeholder : Ed25519Signature)
    (censored : Bool) (change : A → B) (work : RegistrationNativePlatformIdentityCtxMain.M n KemSK Platform mlSource A) :
    interpret joint selected placeholder censored (change <$> work) = change <$> interpret joint selected placeholder censored work := by
  simp only [map_eq_bind_pure_comp, Function.comp_def, RegistrationNativeIdentityCensorSourceFold.bind_source,
    RegistrationNativeIdentityCensorSourceFold.pure_source]

/-- Actual P-only callbacks have the same prior-log dependency law while all current values and private fields stay literal. -/
theorem stable (joint : PqxdhJointIdentity.Primitives) (selected : Nat) (placeholder : Ed25519Signature)
    (censored : Bool) (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (work : StateT Platform ProbComp A) :
    RegistrationNativePlatformViewStable.Stable (RegistrationNativeIdentityCensorOutgoingView.view placeholder)
      (interpret joint selected placeholder censored
        (RegistrationNativePlatformIdentityCtxMain.beacon (n := n) (source := mlSource) setup checks representation created
          (RegistrationNativePlatformIdentityProgram.external work))) := by
  apply RegistrationNativeIdentityCensorOutgoingView.interpreted
  apply RegistrationNativePlatformIdentityCtxTypedJointView.compose_stable
  · exact RegistrationNativePlatformIdentityCtxHistoryView.beacon placeholder setup checks representation created _
      (RegistrationNativePlatformIdentityHistoryView.external placeholder work)
  · exact RegistrationNativePlatformIdentityCtxReceiptView.beacon setup checks representation created _
      (RegistrationNativeIdentityEnvReceiptView.platform_external work)

/-- The concrete original Init writer is the same writer on the full current native/private state, with only its one literal reservation lifted. -/
theorem writer {E : Type} (joint : PqxdhJointIdentity.Primitives) (selected : Nat) (placeholder : Ed25519Signature)
    (censored : Bool) (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (reserve : Usize → StateT Platform ProbComp (core.result.Result Unit E)) (view : registration.InitView) :
    interpret joint selected placeholder censored
      (RegistrationNativePlatformIdentityCtxMain.beacon (n := n) (source := mlSource) setup checks representation created
        (RegistrationNativePlatformIdentityProgram.external (RegistrationNativeIdentityCensorConcreteWriter.encode reserve view))) =
      RegistrationNativeSourceWriterFailureView.writer
        (fun size => interpret joint selected placeholder censored
          (RegistrationNativePlatformIdentityCtxMain.beacon setup checks representation created
            (RegistrationNativePlatformIdentityProgram.external (reserve size))))
        RegistrationNativeConcreteCodec.serializerBranches view := by
  rw [RegistrationNativeIdentityCensorConcreteWriter.source]
  simp only [RegistrationNativeSourceWriterFailureView.writer, RegistrationNativeSourceWriterReadback.init_source]
  rw [native_map, interpret_map]


/-- Real and private-censored interpretation agree for every literal external P action, including its actual independent random transcript entries. -/
theorem source_equal (joint : PqxdhJointIdentity.Primitives) (selected : Nat) (placeholder : Ed25519Signature)
    (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (work : StateT Platform ProbComp A) :
    interpret joint selected placeholder false
      (RegistrationNativePlatformIdentityCtxMain.beacon (n := n) (source := mlSource) setup checks representation created
        (RegistrationNativePlatformIdentityProgram.external work)) =
    interpret joint selected placeholder true
      (RegistrationNativePlatformIdentityCtxMain.beacon setup checks representation created
        (RegistrationNativePlatformIdentityProgram.external work)) := by
  funext before
  have same := congrArg (fun distribution => (fun result => (result.1.1.1, ((result.1.1.2, result.1.2), result.2))) <$> distribution)
    (RegistrationNativeIdentityCensorMldsaOutgoingSource.uniform_equal joint selected placeholder _
      (coin_only setup checks representation created work before.1.1) before.1.2 before.2)
  simpa only [interpret, StateT.run, bind_pure_comp, RegistrationNativeIdentityCensorMldsaOutgoingSource.run] using same

end BeaconcryptCore.Computational.RegistrationNativeIdentityCensorExternalSource

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorExternalSource.native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorExternalSource.native

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorExternalSource.coin_only' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorExternalSource.coin_only

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorExternalSource.native_map' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorExternalSource.native_map

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorExternalSource.stable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorExternalSource.stable

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorExternalSource.writer' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorExternalSource.writer

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorExternalSource.source_equal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorExternalSource.source_equal
