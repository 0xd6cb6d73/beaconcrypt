-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeG3KnownWorldFrame
import BeaconcryptCore.Computational.RegistrationNativeG3Common

/-! Actual native common programs retain their complete chronological signing receipts while the G3 World view removes only its designated private bookkeeping. Publication has its own concrete hash/coin footprint; only direct environment requests require the explicit non-hidden-install classification. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeG3KnownWorldFrameCommon
open RegistrationNativeG3Common (State handler publication)
open PqxdhRecordLiftInterface (EnvEffects)
open RegistrationNativeSeedDelayFrames (ReadsSeed)
variable {n : Nat} {Value : Type}

def view (before : State n) : State n := (before.1, RegistrationNativeG3KnownWorldFrame.view before.2)

def EffectAllowed : (EnvEffects n).Domain → Prop
  | .inr query => ¬ReadsSeed query
  | .inl _ => True

def Allowed : (RegistrationNativePairedServerService.Common n).Domain → Prop
  | .inl _ => True
  | .inr query => EffectAllowed query

private theorem world_effect_input (query : (EnvEffects n).Domain) (quiet : EffectAllowed query)
    (before : PqxdhRecordLiftWorld.State n) :
    Prod.map id RegistrationNativeG3KnownWorldFrame.view <$> (PqxdhRecordLiftWorld.effects query).run before =
      Prod.map id RegistrationNativeG3KnownWorldFrame.view <$>
        (PqxdhRecordLiftWorld.effects query).run (RegistrationNativeG3KnownWorldFrame.view before) := by
  have seeds := congrArg (fun distribution => Prod.map id RegistrationNativeG3KnownWorldFrame.view <$> distribution)
    (RegistrationNativeG3KnownWorldFrameCore.effects_input query (by cases query <;> exact quiet) before)
  have native := congrArg (fun distribution => Prod.map id RegistrationNativeG3KnownWorldFrame.view <$> distribution)
    (RegistrationNativeWorldViewEffects.effects_input query (RegistrationNativeHiddenWorldInstall.view before))
  have uniform := congrArg (fun distribution => Prod.map id RegistrationNativeG3KnownWorldFrame.view <$> distribution)
    (RegistrationNativeKemWorldEffects.effects_input query
      (RegistrationNativeWorldView.project (RegistrationNativeHiddenWorldInstall.view before)))
  simp only [Functor.map_map, Prod.map_def, id_eq, RegistrationNativeG3KnownWorldFrame.view,
    RegistrationNativeKemWorldUniform.mask, RegistrationNativeWorldView.project, RegistrationNativeWorldView.eraseNative,
    RegistrationWorldCoinCompiler.eraseCoin, RegistrationNativeHiddenWorldInstall.view, Function.update_idem] at seeds native uniform ⊢
  exact seeds.trans (native.trans uniform)

private noncomputable def normalizedEffects : QueryImpl (EnvEffects n) (StateT (PqxdhRecordLiftWorld.State n) ProbComp) :=
  fun query state => Prod.map id RegistrationNativeG3KnownWorldFrame.view <$> (PqxdhRecordLiftWorld.effects query).run state

private theorem effects_program_normalized (work : OracleComp (EnvEffects n) Value)
    (quiet : AllQueriesSatisfy work EffectAllowed) (before : PqxdhRecordLiftWorld.State n) :
    Prod.map id RegistrationNativeG3KnownWorldFrame.view <$> (simulateQ PqxdhRecordLiftWorld.effects work).run before =
      (simulateQ normalizedEffects work).run (RegistrationNativeG3KnownWorldFrame.view before) := by
  induction work using OracleComp.inductionOn generalizing before with
  | pure value => simp only [simulateQ_pure, StateT.run_pure, map_pure, Prod.map_def, id_eq]
  | query_bind query next ih =>
      obtain ⟨first, later⟩ := (allQueriesSatisfy_query_bind_iff _ _ _).mp quiet
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, map_bind]
      change _ = (Prod.map id RegistrationNativeG3KnownWorldFrame.view <$>
        (PqxdhRecordLiftWorld.effects query).run (RegistrationNativeG3KnownWorldFrame.view before)) >>= _
      rw [← world_effect_input query first before, bind_map_left]
      exact bind_congr fun result => ih result.1 (later result.1) result.2

/-- Actual allowed environment programs do not read the erased G3 bookkeeping. -/
theorem effects_program_input (work : OracleComp (EnvEffects n) Value)
    (quiet : AllQueriesSatisfy work EffectAllowed) (before : PqxdhRecordLiftWorld.State n) :
    Prod.map id RegistrationNativeG3KnownWorldFrame.view <$> (simulateQ PqxdhRecordLiftWorld.effects work).run before =
      Prod.map id RegistrationNativeG3KnownWorldFrame.view <$>
        (simulateQ PqxdhRecordLiftWorld.effects work).run (RegistrationNativeG3KnownWorldFrame.view before) := by
  have first := effects_program_normalized work quiet before
  have second := effects_program_normalized work quiet (RegistrationNativeG3KnownWorldFrame.view before)
  rw [RegistrationNativeG3KnownWorldFrame.view_idempotent] at second
  exact first.trans second.symm

/-- Projecting the shared World leaves chronological signing receipts unchanged. -/
theorem view_idempotent (before : State n) : view (view before) = view before := by
  simp only [view, RegistrationNativeG3KnownWorldFrame.view_idempotent]

/-- Actual direct common effects preserve their complete receipt/semantic-World outcome under the bilateral input view. -/
theorem effect_input (query : (EnvEffects n).Domain) (quiet : EffectAllowed query) (before : State n) :
    Prod.map id view <$> (RegistrationNativeG3Common.effect query).run before =
      Prod.map id view <$> (RegistrationNativeG3Common.effect query).run (view before) := by
  have same := congrArg (fun distribution => (fun result => (result.1, (before.1, result.2))) <$> distribution)
    (world_effect_input query quiet before.2)
  simpa only [RegistrationNativeG3Common.effect, StateT.run, Functor.map_map, Prod.map_def, id_eq, view] using same

private theorem primitive_allowed (query : (EnvEffects n).Domain) (primitive : RegistrationNativeG3Common.Primitive query) :
    EffectAllowed query := by
  rcases query with coin | capability
  · trivial
  · cases capability <;> simp [EffectAllowed, ReadsSeed, RegistrationNativeG3Common.Primitive] at *

/-- Concrete record/hash/ML publication uses only its actual hash/coin compiler and needs no supplied footprint premise. -/
theorem publication_input (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (writer : RawCtxMixedShared.Writer)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (query : RegistrationBoundPublication.Spec.Domain) (before : State n) :
    Prod.map id view <$> (publication source writer sign query).run before =
      Prod.map id view <$> (publication source writer sign query).run (view before) := by
  rcases before with ⟨receipts, world⟩
  have quiet : AllQueriesSatisfy ((RegistrationBoundSourceCompiler.compiler (n := n) source writer sign query).run receipts) EffectAllowed :=
    (RegistrationNativeG3Common.compiler_primitive (n := n) source writer sign query receipts).mono primitive_allowed
  have same := congrArg (fun distribution => (fun result => (result.1.1, (result.1.2, result.2))) <$> distribution)
    (effects_program_input ((RegistrationBoundSourceCompiler.compiler source writer sign query).run receipts) quiet world)
  simpa only [publication, QueryImpl.flattenStateT_mapStateTBase_apply_run, Functor.map_map,
    Prod.map_def, id_eq, view] using same

/-- Every actual common query outside hidden installation retains its literal result and all current signing receipts. -/
theorem handler_input (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (writer : RawCtxMixedShared.Writer)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (query : (RegistrationNativePairedServerService.Common n).Domain) (quiet : Allowed query) (before : State n) :
    Prod.map id view <$> (handler source writer sign query).run before =
      Prod.map id view <$> (handler source writer sign query).run (view before) := by
  cases query with
  | inl query => exact publication_input source writer sign query before
  | inr query => exact effect_input query quiet before

private noncomputable def normalized (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (writer : RawCtxMixedShared.Writer)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply) :
    QueryImpl (RegistrationNativePairedServerService.Common n) (StateT (State n) ProbComp) :=
  fun query state => Prod.map id view <$> (handler source writer sign query).run state

private theorem program_normalized (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (writer : RawCtxMixedShared.Writer)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (work : OracleComp (RegistrationNativePairedServerService.Common n) Value)
    (quiet : AllQueriesSatisfy work Allowed) (before : State n) :
    Prod.map id view <$> (simulateQ (handler source writer sign) work).run before =
      (simulateQ (normalized source writer sign) work).run (view before) := by
  induction work using OracleComp.inductionOn generalizing before with
  | pure value => simp only [simulateQ_pure, StateT.run_pure, map_pure, Prod.map_def, id_eq]
  | query_bind query next ih =>
      obtain ⟨first, later⟩ := (allQueriesSatisfy_query_bind_iff _ _ _).mp quiet
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, map_bind]
      change _ = (Prod.map id view <$> (handler source writer sign query).run (view before)) >>= _
      rw [← handler_input source writer sign query first before, bind_map_left]
      exact bind_congr fun result => ih result.1 (later result.1) result.2

/-- Complete adaptive common programs retain their semantic World and chronological receipts under the actual G3 projection. -/
theorem program_input (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (writer : RawCtxMixedShared.Writer)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (work : OracleComp (RegistrationNativePairedServerService.Common n) Value)
    (quiet : AllQueriesSatisfy work Allowed) (before : State n) :
    Prod.map id view <$> (simulateQ (handler source writer sign) work).run before =
      Prod.map id view <$> (simulateQ (handler source writer sign) work).run (view before) := by
  have first := program_normalized source writer sign work quiet before
  have second := program_normalized source writer sign work quiet (view before)
  rw [view_idempotent] at second
  exact first.trans second.symm

end BeaconcryptCore.Computational.RegistrationNativeG3KnownWorldFrameCommon
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3KnownWorldFrameCommon.effects_program_input' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3KnownWorldFrameCommon.effects_program_input
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3KnownWorldFrameCommon.view_idempotent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3KnownWorldFrameCommon.view_idempotent
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3KnownWorldFrameCommon.effect_input' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3KnownWorldFrameCommon.effect_input
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3KnownWorldFrameCommon.publication_input' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3KnownWorldFrameCommon.publication_input
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3KnownWorldFrameCommon.handler_input' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3KnownWorldFrameCommon.handler_input
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3KnownWorldFrameCommon.program_input' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3KnownWorldFrameCommon.program_input
