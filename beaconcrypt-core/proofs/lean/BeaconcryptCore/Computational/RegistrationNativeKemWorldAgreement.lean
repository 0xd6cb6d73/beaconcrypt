-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeKemWorldAuthentication

/-! The actual native agreement callback samples its real primitive work and appends its actual request log. Forgetting only uniform accounting retains the complete primitive reply, auxiliary state, cache, signing history and every native World coordinate. The same law holds for arbitrary controller continuations and the actual SDK replay-lookup agreement wrapper. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeKemWorldAgreement
open RegistrationWorldAgreement (State recorded)
variable {ι KemSK Reader Response Auxiliary Value : Type} {base : OracleSpec ι} {n : Nat}

def mask (state : State n Auxiliary) : State n Auxiliary :=
  { state with world := (RegistrationNativeKemWorldUniform.mask state.world.1, state.world.2) }

private theorem callback_canonical (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (primitive : QueryImpl RegistrationAgreementShared.PrimitiveSpec (StateT Auxiliary ProbComp))
    (query : RegistrationAgreementExecutor.Request) (state : State n Auxiliary) :
    Prod.map id mask <$> (RegistrationWorldAgreement.agreement source primitive query).run state =
      (fun result => (result.1, State.mk result.2 (state.requests ++ recorded query) state.recordRequests
        (RegistrationNativeKemWorldUniform.mask state.world.1, state.world.2))) <$>
        (RegistrationAgreementShared.auxiliary source primitive query).run state.auxiliary := by
  have law := congrArg (fun work => (fun result =>
      (result.1.1, State.mk result.1.2 (state.requests ++ recorded query) state.recordRequests
        (result.2, state.world.2))) <$> work)
    (RegistrationNativeKemWorldUniform.sampled_mask
      ((RegistrationAgreementShared.auxiliary source primitive query).run state.auxiliary) state.world.1)
  simpa only [RegistrationWorldAgreement.agreement, StateT.run, Functor.map_map,
    Prod.map, id_eq, mask, Function.comp_def] using law

/-- The real primitive callback and all request/cache/receipt coordinates are independent of its private uniform-count input. -/
theorem callback_input (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (primitive : QueryImpl RegistrationAgreementShared.PrimitiveSpec (StateT Auxiliary ProbComp))
    (query : RegistrationAgreementExecutor.Request) (state : State n Auxiliary) :
    Prod.map id mask <$> (RegistrationWorldAgreement.agreement source primitive query).run state =
      Prod.map id mask <$> (RegistrationWorldAgreement.agreement source primitive query).run (mask state) := by
  rw [callback_canonical, callback_canonical]
  rfl

private noncomputable def normalized (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (primitive : QueryImpl RegistrationAgreementShared.PrimitiveSpec (StateT Auxiliary ProbComp)) :
    QueryImpl RegistrationAgreementExecutor.Spec (StateT (State n Auxiliary) ProbComp) := fun query before =>
  Prod.map id mask <$> (RegistrationWorldAgreement.agreement source primitive query).run before

private theorem program_normalized (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (primitive : QueryImpl RegistrationAgreementShared.PrimitiveSpec (StateT Auxiliary ProbComp))
    (work : OracleComp RegistrationAgreementExecutor.Spec Value) (state : State n Auxiliary) :
    Prod.map id mask <$> (simulateQ (RegistrationWorldAgreement.agreement source primitive) work).run state =
      (simulateQ (normalized source primitive) work).run (mask state) :=
  OracleComp.map_run_simulateQ_eq_of_query_map_eq _ _ mask (callback_input source primitive) work state

/-- Every actual ordered native agreement continuation retains its whole projected source execution. -/
theorem program_input (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (primitive : QueryImpl RegistrationAgreementShared.PrimitiveSpec (StateT Auxiliary ProbComp))
    (work : OracleComp RegistrationAgreementExecutor.Spec Value) (state : State n Auxiliary) :
    Prod.map id mask <$> (simulateQ (RegistrationWorldAgreement.agreement source primitive) work).run state =
      Prod.map id mask <$> (simulateQ (RegistrationWorldAgreement.agreement source primitive) work).run (mask state) := by
  rw [program_normalized, program_normalized]
  rfl

/-- The actual SDK owned-replay lookup, native KEM/DH/HKDF controller and all successful or failed capabilities are retained by the same uniform-only projection. -/
theorem native_agree_input (setup : PqxdhServerAuthExperiment.Setup base KemSK)
    (checks : PqxdhServerAuthExperiment.Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (packet : registration.InitPacket)
    (authenticated : registration.AuthenticatedInit) (before : RegistrationServerFrontendCompiler.State n) :
    Prod.map id RegistrationNativeKemServerState.maskServer <$>
        (RegistrationServerNativeSource.agree setup checks representation created packet authenticated).run before =
      Prod.map id RegistrationNativeKemServerState.maskServer <$>
        (RegistrationServerNativeSource.agree setup checks representation created packet authenticated).run
          (RegistrationNativeKemServerState.maskServer before) := by
  have law := congrArg (fun work =>
      (fun result => (result.1, { RegistrationNativeKemServerState.maskServer before with world := result.2 })) <$> work)
    (program_input setup.source (RegistrationServerRoleBackend.native setup checks representation created.seed)
      (RegistrationReplaySchedule.begin before.control authenticated before.consumed) before.world)
  simpa only [RegistrationServerNativeSource.agree, StateT.run, Functor.map_map, Prod.map, id_eq,
    RegistrationNativeKemServerState.maskServer, mask, Function.comp_def] using law

/-- Native replay insertion and one-use handle retention preserve their exact result while leaving all counted World operations untouched. -/
theorem native_retain_input (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (accepted : agreement.ServerAgreement) (before : RegistrationServerFrontendCompiler.State n) :
    Prod.map id RegistrationNativeKemServerState.maskServer <$>
        (RegistrationServerNativeSource.retain created accepted).run before =
      Prod.map id RegistrationNativeKemServerState.maskServer <$>
        (RegistrationServerNativeSource.retain created accepted).run
          (RegistrationNativeKemServerState.maskServer before) := by
  simp only [RegistrationServerNativeSource.retain, RegistrationServerNativeSource.sourceStep,
    RegistrationWorldServerFrontend.retain, RegistrationServerFrontendCompiler.restore, StateT.run]
  cases consumed : RegistrationReplaySchedule.consume accepted before.consumed with
  | fail error | div => simp only [RegistrationNativeKemServerState.maskServer, consumed, map_pure,
      RegistrationServerFrontendCompiler.erase, RegistrationNativeKemWorldUniform.mask, Prod.map, id_eq]
  | ok result =>
      rcases result with ⟨stored, history⟩
      cases stored <;> simp only [RegistrationNativeKemServerState.maskServer, consumed, map_pure,
        RegistrationServerFrontendCompiler.erase, RegistrationNativeKemWorldUniform.mask, Prod.map, id_eq]

end BeaconcryptCore.Computational.RegistrationNativeKemWorldAgreement

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemWorldAgreement.callback_input' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemWorldAgreement.callback_input

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemWorldAgreement.program_input' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemWorldAgreement.program_input

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemWorldAgreement.native_agree_input' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemWorldAgreement.native_agree_input

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemWorldAgreement.native_retain_input' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemWorldAgreement.native_retain_input
