-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeWorldViewRecords
import BeaconcryptCore.Computational.RegistrationServerMaterialSourceState

/-! Actual native authentication preserves its full reply, cache and operational poststate under the explicitly named private accounting view. ML and Ed verification keep their original source predicates. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeWorldViewAuthentication
open PqxdhRecordLiftWorld (State capability effects chargeEffect)
open RegistrationNativeWorldView (project)
open PqxdhServerAuthExperiment (Setup Codec)
variable {ι KemSK Reader Response Value : Type} {base : OracleSpec ι} {n : Nat}

private theorem hash_effect_input (bytes : Pqxdh.Bytes) (state : State n) :
    Prod.map id project <$> (effects (.inr (.hash bytes))).run state =
      Prod.map id project <$> (effects (.inr (.hash bytes))).run (project state) :=
  RegistrationNativeWorldViewEffects.effects_input _ state

/-- Actual hash, ML verification and attached Ed verification callbacks preserve their replies under the same full-state projection. -/
theorem callback_input (setup : Setup base KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (verify : MldsaTranscriptAuth.Verify)
    (query : RegistrationAuthenticationExecutor.Request) (state : State n) :
    Prod.map id project <$> (RegistrationWorldAuthentication.implementation setup codec route verify query).run state =
      Prod.map id project <$> (RegistrationWorldAuthentication.implementation setup codec route verify query).run (project state) := by
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
        Prod.map, id_eq, RegistrationNativeWorldView.project_idempotent]

private noncomputable def normalized (setup : Setup base KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (verify : MldsaTranscriptAuth.Verify) :
    QueryImpl RegistrationAuthenticationExecutor.Spec (StateT (State n) ProbComp) := fun query before =>
  Prod.map id project <$> (RegistrationWorldAuthentication.implementation setup codec route verify query).run before

private theorem program_normalized (setup : Setup base KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (verify : MldsaTranscriptAuth.Verify)
    (work : OracleComp RegistrationAuthenticationExecutor.Spec Value) (state : State n) :
    Prod.map id project <$>
        (simulateQ (RegistrationWorldAuthentication.implementation setup codec route verify) work).run state =
      (simulateQ (normalized setup codec route verify) work).run (project state) := by
  exact OracleComp.map_run_simulateQ_eq_of_query_map_eq _ _ project
    (callback_input setup codec route verify) work state

/-- The whole actual authentication controller, with all seven callbacks and reached states, is independent of the private uniform accounting input. -/
theorem program_input (setup : Setup base KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (verify : MldsaTranscriptAuth.Verify)
    (work : OracleComp RegistrationAuthenticationExecutor.Spec Value) (state : State n) :
    Prod.map id project <$>
        (simulateQ (RegistrationWorldAuthentication.implementation setup codec route verify) work).run state =
      Prod.map id project <$>
        (simulateQ (RegistrationWorldAuthentication.implementation setup codec route verify) work).run (project state) := by
  rw [program_normalized, program_normalized, RegistrationNativeWorldView.project_idempotent]

/-- The actual native entry point retains the same successful or failed authentication result and reached operational state. -/
theorem begin_input (setup : Setup base KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (verify : MldsaTranscriptAuth.Verify)
    (pin : session.ServerAuthenticationPin) (packet : registration.InitPacket) (state : State n) :
    Prod.map id project <$> (RegistrationWorldAuthentication.begin setup codec route verify pin packet).run state =
      Prod.map id project <$> (RegistrationWorldAuthentication.begin setup codec route verify pin packet).run (project state) := by
  simp only [RegistrationWorldAuthentication.begin, RegistrationWorldAuthentication.program,
    ← QueryImpl.simulateQ_compose]
  exact program_input setup codec route verify _ state

private def withWorld (before : RegistrationServerFrontendCompiler.State n) (world : State n) :
    RegistrationServerFrontendCompiler.State n :=
  { before with world := { before.world with world := (world, before.world.world.2) } }

private theorem authenticate_run (setup : Setup base KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (verify : MldsaTranscriptAuth.Verify)
    (created : PqxdhLiveServerConstruction.Created Unit) (packet : registration.InitPacket)
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
    (created : PqxdhLiveServerConstruction.Created Unit) (packet : registration.InitPacket)
    (before : RegistrationServerFrontendCompiler.State n) :
    Prod.map id RegistrationServerMaterialSourceState.nativeView <$>
        (RegistrationServerNativeSource.authenticate setup codec route verify created packet).run before =
      Prod.map id RegistrationServerMaterialSourceState.nativeView <$>
        (RegistrationServerNativeSource.authenticate setup codec route verify created packet).run
          (RegistrationServerMaterialSourceState.nativeView before) := by
  have law := congrArg (fun work => (fun result =>
      (result.1, withWorld (RegistrationServerMaterialSourceState.nativeView before) result.2)) <$> work)
    (begin_input setup codec route verify before.pin packet before.world.world.1)
  simpa only [authenticate_run, Functor.map_map, Prod.map, id_eq, Function.comp_def,
    RegistrationServerMaterialSourceState.nativeView, withWorld, project, RegistrationNativeWorldView.eraseNative, RegistrationWorldCoinCompiler.eraseCoin, RegistrationServerRecordWorldSource.project, Function.update_idem] using law

end BeaconcryptCore.Computational.RegistrationNativeWorldViewAuthentication

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeWorldViewAuthentication.callback_input' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeWorldViewAuthentication.callback_input
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeWorldViewAuthentication.program_input' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeWorldViewAuthentication.program_input
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeWorldViewAuthentication.begin_input' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeWorldViewAuthentication.begin_input
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeWorldViewAuthentication.native_auth_input' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeWorldViewAuthentication.native_auth_input
