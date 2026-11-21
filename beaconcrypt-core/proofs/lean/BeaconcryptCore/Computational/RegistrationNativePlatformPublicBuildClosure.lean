-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicSourceExecution
import BeaconcryptCore.Computational.RegistrationNativePlatformServerMemoCompiler
/-! Compiled dynamic builds use the same actual optional private memo and one World. The full leaf interpretation is derived before applying the named native/Envcoin accounting view; external uniforms remain uncounted native draws. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicBuildClosure
open PqxdhServerAuthExperiment (Setup)
open RegistrationNativeRetainedRoots (Memo)
open RegistrationNativePlatformServerFrontendCompiler (Spec)
open RegistrationNativePublicSourceEffects (close)
variable {n : Nat} {ι KemSK Value : Type} {base : OracleSpec ι}

noncomputable def full (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (memo : Memo) :
    QueryImpl (Spec n) (StateT (PqxdhRecordLiftWorld.State n) ProbComp)
  | .inl message => pure ((memo message).map fun root => RegistrationNativePairedChoice.Choice.known
      (PqxdhServerAuthKeySchedule.fromRoot source root))
  | .inr query => RegistrationNativePlatformWorldEffectClosure.implementation query

def embedded : QueryImpl (Spec n) (OracleComp (RegistrationNativePlatformPublicFrontend.Spec n KemSK)) :=
  RegistrationNativePlatformPublicFrontend.embedLocal ∘ₛ RegistrationNativePlatformPublicFrontend.buildEmbedding

/-- Every actual compiled build leaf preserves private roots and the KEM pool and runs precisely its optional material or World request. -/
theorem leaf (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (query : (Spec n).Domain) (before : RegistrationNativePublicInterpreter.State n KemSK) :
    (close setup seed scalar (simulateQ (RegistrationNativePlatformPublicSourceExecution.handler setup wire route sign)
      (embedded query))).run before =
      (fun result => (result.1, { before with world := result.2 })) <$>
        (full setup.source before.roots query).run before.world := by
  cases query with
  | inl message =>
      simp only [embedded, QueryImpl.compose, RegistrationNativePlatformPublicFrontend.buildEmbedding,
        RegistrationNativePlatformPublicFrontend.localQuery, RegistrationNativePlatformPublicFrontend.embedLocal,
        simulateQ_spec_query, RegistrationNativePlatformPublicSourceExecution.handler,
        RegistrationNativePublicInterpreter.handler, StateT.run_pure, full, map_pure]
      rfl
  | inr query => cases query with
    | inl effect =>
        have actual := RegistrationNativePublicSourceEffects.close_world setup seed scalar
          (PqxdhRecordLiftWorld.effects effect) before
        convert actual using 1 <;> first
          | rfl
          | simp only [embedded, QueryImpl.compose, RegistrationNativePlatformPublicFrontend.buildEmbedding,
              RegistrationNativePlatformPublicFrontend.effect, RegistrationNativePlatformPublicFrontend.localQuery,
              RegistrationNativePlatformPublicFrontend.embedLocal, simulateQ_spec_query,
              RegistrationNativePlatformPublicSourceExecution.handler, RegistrationNativePublicInterpreter.handler,
              RegistrationNativePublicInterpreter.common, RegistrationNativePublicInterpreter.effect]
    | inr coin =>
        simp only [embedded, QueryImpl.compose, RegistrationNativePlatformPublicFrontend.buildEmbedding,
          RegistrationNativePlatformPublicFrontend.localCoin, RegistrationNativePlatformPublicFrontend.embedLocal,
          RegistrationNativePlatformPublicFrontend.publicCoin, simulateQ_spec_query,
          RegistrationNativePlatformPublicSourceExecution.handler, StateT.run_lift,
          bind_pure_comp, full,
          RegistrationNativePlatformWorldEffectClosure.implementation, Functor.map_map]
        rfl


/-- Whole adaptive compiled builds share the same actual optional memo and full World while all remaining private coordinates stay fixed. -/
theorem world_program (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (work : OracleComp (Spec n) Value) (before : RegistrationNativePublicInterpreter.State n KemSK) :
    (close setup seed scalar (simulateQ (RegistrationNativePlatformPublicSourceExecution.handler setup wire route sign)
      (simulateQ embedded work))).run before =
      (fun result => (result.1, { before with world := result.2 })) <$>
        (simulateQ (full setup.source before.roots) work).run before.world := by
  induction work using OracleComp.inductionOn generalizing before with
  | pure value => rfl
  | query_bind query continuation ih =>
      have split : (close setup seed scalar
          (simulateQ (RegistrationNativePlatformPublicSourceExecution.handler setup wire route sign)
            (simulateQ embedded (((Spec n).query query : OracleComp (Spec n) _) >>= continuation)))).run before = (do
          let reached ← (close setup seed scalar
            (simulateQ (RegistrationNativePlatformPublicSourceExecution.handler setup wire route sign) (embedded query))).run before
          (close setup seed scalar (simulateQ (RegistrationNativePlatformPublicSourceExecution.handler setup wire route sign)
            (simulateQ embedded (continuation reached.1)))).run reached.2) := by
        simp only [simulateQ_bind, simulateQ_spec_query, close, StateT.run,
          StateT.monad_bind_def, StateT.bind, simulateQ_bind]
      rw [split, leaf]
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, bind_map_left, map_bind]
      apply bind_congr
      rintro ⟨reply, current⟩
      exact ih reply { before with world := current }

private theorem view_leaf (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (memo : Memo)
    (query : (Spec n).Domain) (before : PqxdhRecordLiftWorld.State n) :
    Prod.map id RegistrationNativeWorldView.project <$> (full source memo query).run before =
      (RegistrationNativePlatformServerMemoCompiler.optional source memo query).run (RegistrationNativeWorldView.project before) := by
  cases query with
  | inl message => simp only [full, RegistrationNativePlatformServerMemoCompiler.optional, StateT.run_pure, map_pure, Prod.map_def, id_eq]
  | inr query =>
      have actual := RegistrationNativePlatformWorldEffectView.program
        ((RegistrationNativePlatformEffectCompiler.Spec n).query query : OracleComp (RegistrationNativePlatformEffectCompiler.Spec n) _) before
      simpa only [full, RegistrationNativePlatformServerMemoCompiler.optional, simulateQ_spec_query] using actual

/-- Only the named native-call and Envcoin accounting view separates the full compiler World interpretation from its reduction interpreter. -/
theorem view_program (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (memo : Memo)
    (work : OracleComp (Spec n) Value) (before : PqxdhRecordLiftWorld.State n) :
    Prod.map id RegistrationNativeWorldView.project <$> (simulateQ (full source memo) work).run before =
      (simulateQ (RegistrationNativePlatformServerMemoCompiler.optional source memo) work).run (RegistrationNativeWorldView.project before) :=
  OracleComp.map_run_simulateQ_eq_of_query_map_eq _ _ RegistrationNativeWorldView.project
    (view_leaf source memo) work before


def worldView (before : RegistrationNativePublicInterpreter.State n KemSK) : RegistrationNativePublicInterpreter.State n KemSK :=
  { before with world := RegistrationNativeWorldView.project before.world }

/-- The complete actual new build query tree has its optional-memo reduction interpretation, preserving all private frame coordinates and actual uniforms under the stated accounting view. -/
theorem source_program (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (work : OracleComp (Spec n) Value) (before : RegistrationNativePublicInterpreter.State n KemSK) :
    Prod.map id worldView <$>
      (close setup seed scalar (simulateQ (RegistrationNativePlatformPublicSourceExecution.handler setup wire route sign)
        (simulateQ embedded work))).run before =
      (fun result => (result.1, { before with world := result.2 })) <$>
        (simulateQ (RegistrationNativePlatformServerMemoCompiler.optional setup.source before.roots) work).run
          (RegistrationNativeWorldView.project before.world) := by
  rw [world_program]
  have actual := congrArg (Functor.map (fun result => (result.1, { before with world := result.2 })))
    (view_program setup.source before.roots work before.world)
  simpa only [Functor.map_map, worldView, Prod.map_def, id_eq] using actual

end BeaconcryptCore.Computational.RegistrationNativePlatformPublicBuildClosure

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicBuildClosure.leaf' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicBuildClosure.leaf

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicBuildClosure.world_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicBuildClosure.world_program

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicBuildClosure.view_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicBuildClosure.view_program

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicBuildClosure.source_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicBuildClosure.source_program
