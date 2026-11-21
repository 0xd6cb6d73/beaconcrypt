-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeKemServerState

/-! Native authentication reads and updates the actual shared cache while being independent of the private uniform accounting coordinate. The explicit projection preserves every other operational and analysis field. This supplies the genuine World-side law for opening selected native KEM callbacks after authentication. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeKemWorldAuthentication
open PqxdhRecordLiftWorld (State capability effects chargeEffect)
open RegistrationNativeKemWorldUniform (mask)
open PqxdhServerAuthExperiment (Setup Codec)
variable {ι KemSK Reader Response Value : Type} {base : OracleSpec ι} {n : Nat}

private theorem hash_canonical (bytes : Pqxdh.Bytes) (state : State n) :
    Prod.map id mask <$> (capability (.hash bytes)).run state =
      (fun result => (result.1, { mask state with primitive := ((mask state).primitive.1, result.2) })) <$>
        (CtxRomAuth.ctxRandomOracle ((), bytes)).run state.primitive.2 := by
  have law := congrArg (fun work =>
    (fun result => (result.1.1, { result.2 with primitive := (result.2.primitive.1, result.1.2) })) <$> work)
      (RegistrationNativeKemWorldUniform.sampled_mask
        ((CtxRomAuth.ctxRandomOracle ((), bytes)).run state.primitive.2) state)
  simpa only [capability, StateT.run, map_bind, bind_pure_comp, Functor.map_map,
    Prod.map, id_eq, mask, Function.comp_def] using law

/-- Actual cached hash replies and the complete reached cache do not depend on the forgotten uniform ledger. -/
theorem hash_input (bytes : Pqxdh.Bytes) (state : State n) :
    Prod.map id mask <$> (capability (.hash bytes)).run state =
      Prod.map id mask <$> (capability (.hash bytes)).run (mask state) := by
  rw [hash_canonical, hash_canonical, RegistrationNativeKemWorldUniform.mask_idempotent]
  rfl

/-- Charging the real hash effect commutes with the uniform-only projection, retaining its actual effect counter. -/
theorem hash_effect_input (bytes : Pqxdh.Bytes) (state : State n) :
    Prod.map id mask <$> (effects (.inr (.hash bytes))).run state =
      Prod.map id mask <$> (effects (.inr (.hash bytes))).run (mask state) := by
  change Prod.map id mask <$> (capability (.hash bytes)).run (chargeEffect (.inr (.hash bytes)) state) =
    Prod.map id mask <$> (capability (.hash bytes)).run (chargeEffect (.inr (.hash bytes)) (mask state))
  rw [hash_canonical, hash_canonical]
  rfl

/-- Actual hash, ML verification and attached Ed verification callbacks preserve their replies under the same full-state projection. -/
theorem callback_input (setup : Setup base KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (verify : MldsaTranscriptAuth.Verify)
    (query : RegistrationAuthenticationExecutor.Request) (state : State n) :
    Prod.map id mask <$> (RegistrationWorldAuthentication.implementation setup codec route verify query).run state =
      Prod.map id mask <$> (RegistrationWorldAuthentication.implementation setup codec route verify query).run (mask state) := by
  cases query with
  | hash request =>
      have law := congrArg (fun work => Prod.map
        (fun digest => core.option.Option.Some (RegistrationAuthenticationShared.digestArray digest)) id <$> work)
        (hash_effect_input (BeaconcryptCore.Refinement.RegistrationInputs.hashBytes request) state)
      simp only [RegistrationWorldAuthentication.implementation, QueryImpl.apply_compose,
        RegistrationWorldAuthentication.callbacks, simulateQ_spec_query,
        simulateQ_map, PqxdhRecordLiftWorld.handler, StateT.run_map,
        bind_pure_comp, Functor.map_map, Prod.map, id_eq]
      simp only [Functor.map_map, Prod.map, id_eq] at law
      convert law using 1 <;> rfl
  | mldsa request | ed25519 request =>
      simp only [RegistrationWorldAuthentication.implementation, QueryImpl.apply_compose,
        RegistrationWorldAuthentication.callbacks, simulateQ_pure, StateT.run_pure, map_pure,
        Prod.map, id_eq, RegistrationNativeKemWorldUniform.mask_idempotent]

private noncomputable def normalized (setup : Setup base KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (verify : MldsaTranscriptAuth.Verify) :
    QueryImpl RegistrationAuthenticationExecutor.Spec (StateT (State n) ProbComp) := fun query before =>
  Prod.map id mask <$> (RegistrationWorldAuthentication.implementation setup codec route verify query).run before

private theorem program_normalized (setup : Setup base KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (verify : MldsaTranscriptAuth.Verify)
    (work : OracleComp RegistrationAuthenticationExecutor.Spec Value) (state : State n) :
    Prod.map id mask <$>
        (simulateQ (RegistrationWorldAuthentication.implementation setup codec route verify) work).run state =
      (simulateQ (normalized setup codec route verify) work).run (mask state) := by
  exact OracleComp.map_run_simulateQ_eq_of_query_map_eq _ _ mask
    (callback_input setup codec route verify) work state

/-- The whole actual authentication controller, with all seven callbacks and reached states, is independent of the private uniform accounting input. -/
theorem program_input (setup : Setup base KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (verify : MldsaTranscriptAuth.Verify)
    (work : OracleComp RegistrationAuthenticationExecutor.Spec Value) (state : State n) :
    Prod.map id mask <$>
        (simulateQ (RegistrationWorldAuthentication.implementation setup codec route verify) work).run state =
      Prod.map id mask <$>
        (simulateQ (RegistrationWorldAuthentication.implementation setup codec route verify) work).run (mask state) := by
  rw [program_normalized, program_normalized, RegistrationNativeKemWorldUniform.mask_idempotent]

/-- The actual native entry point retains the same successful or failed authentication result and reached operational state. -/
theorem begin_input (setup : Setup base KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (verify : MldsaTranscriptAuth.Verify)
    (pin : session.ServerAuthenticationPin) (packet : registration.InitPacket) (state : State n) :
    Prod.map id mask <$> (RegistrationWorldAuthentication.begin setup codec route verify pin packet).run state =
      Prod.map id mask <$> (RegistrationWorldAuthentication.begin setup codec route verify pin packet).run (mask state) := by
  simp only [RegistrationWorldAuthentication.begin, RegistrationWorldAuthentication.program,
    ← QueryImpl.simulateQ_compose]
  exact program_input setup codec route verify _ state

private def withWorld (before : RegistrationServerFrontendCompiler.State n) (world : State n) :
    RegistrationServerFrontendCompiler.State n :=
  { before with world := { before.world with world := (world, before.world.world.2) } }

private theorem authenticate_run (setup : Setup base KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (verify : MldsaTranscriptAuth.Verify)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (packet : registration.InitPacket)
    (before : RegistrationServerFrontendCompiler.State n) :
    (RegistrationServerNativeSource.authenticate setup codec route verify created packet).run before =
      (fun result => (result.1, withWorld before result.2)) <$>
        (RegistrationWorldAuthentication.begin setup codec route verify before.pin packet).run before.world.world.1 := by
  simp only [RegistrationServerNativeSource.authenticate, RegistrationServerNativeSource.sourceStep,
    RegistrationWorldServerFrontend.authenticate, RegistrationWorldServerFrontend.withWorld,
    RegistrationServerFrontendCompiler.restore, RegistrationServerFrontendCompiler.erase,
    StateT.run, Functor.map_map, Prod.map, id_eq, withWorld]

/-- The SDK's actual private authentication wrapper has the same complete projected output, including its retained control, replay/session tables, shared cache and all logs. -/
theorem native_auth_input (setup : Setup base KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (verify : MldsaTranscriptAuth.Verify)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (packet : registration.InitPacket)
    (before : RegistrationServerFrontendCompiler.State n) :
    Prod.map id RegistrationNativeKemServerState.maskServer <$>
        (RegistrationServerNativeSource.authenticate setup codec route verify created packet).run before =
      Prod.map id RegistrationNativeKemServerState.maskServer <$>
        (RegistrationServerNativeSource.authenticate setup codec route verify created packet).run
          (RegistrationNativeKemServerState.maskServer before) := by
  have law := congrArg (fun work => (fun result =>
      (result.1, withWorld (RegistrationNativeKemServerState.maskServer before) result.2)) <$> work)
    (begin_input setup codec route verify before.pin packet before.world.world.1)
  simpa only [authenticate_run, Functor.map_map, Prod.map, id_eq, Function.comp_def,
    RegistrationNativeKemServerState.maskServer, withWorld, mask] using law

end BeaconcryptCore.Computational.RegistrationNativeKemWorldAuthentication

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemWorldAuthentication.hash_input' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemWorldAuthentication.hash_input

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemWorldAuthentication.hash_effect_input' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemWorldAuthentication.hash_effect_input

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemWorldAuthentication.callback_input' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemWorldAuthentication.callback_input

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemWorldAuthentication.program_input' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemWorldAuthentication.program_input

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemWorldAuthentication.begin_input' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemWorldAuthentication.begin_input

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemWorldAuthentication.native_auth_input' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemWorldAuthentication.native_auth_input
