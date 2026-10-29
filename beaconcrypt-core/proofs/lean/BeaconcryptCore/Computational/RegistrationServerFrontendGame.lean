-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationServerFrontendCompiler

/-! The adaptive native Server API is compiled to a concrete related-root distinguishing client. Accept and build keep the actual ML gates, populated binding, private replay and one-use session order. Record, hash and adversary coin queries use the unchanged instrumented World. The family probability endpoint below is one composition hop; hidden-seed/key-schedule and selected-fresh event reductions remain separate. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationServerFrontendGame
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhRecordLiftInterface (RecordQuery RecordSpec WorldSpec)
open RegistrationServerRootCompiler (Local Family)
open PqxdhJointDhExtractRoot (RootSpec)
open RegistrationServerFrontendCompiler (State restore erase)
variable {ι KemSK Reader Response Encoded Result : Type} {base : OracleSpec ι} {n : Nat}

inductive Request where
  | accept : registration.InitPacket → Request
  | build : Nat → Slice U8 → Request
  | record : RecordQuery → Request
  | hash : Pqxdh.Bytes → Request

abbrev ApiSpec (Encoded : Type) : OracleSpec Request
  | .accept _ => RustM (Option Nat)
  | .build _ _ => RustM (Option (Std.U64 × Encoded))
  | .record query => (RecordSpec .O).Range query
  | .hash _ => CtxRomAuth.CtxDigest

abbrev Spec (Encoded : Type) := unifSpec + ApiSpec Encoded

/-- Ordinary World operations retain the native local state and chronological signing history. -/
noncomputable def ordinary (setup : Setup base KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (query : (WorldSpec n).Domain) :
    StateT (Local n) ProbComp ((WorldSpec n).Range query) := fun before =>
  (fun result => (result.1, { before with world := (result.2, before.world.2) })) <$>
    (PqxdhRecordLiftWorld.handler setup codec route query).run before.world.1

def liftWorld {Value : Type} (work : StateT (Local n) ProbComp Value) : StateT (State n) ProbComp Value := fun before =>
  (fun result => (result.1, { before with world := result.2 })) <$> work.run before.world

def nativeWorld {Value : Type} (work : StateT (Local n) ProbComp Value) :
    StateT (RegistrationWorldServerFrontend.State n RegistrationServerRoleBackend.State) ProbComp Value := fun before =>
  (fun result => (result.1, { before with global := (before.global.1, result.2) })) <$> work.run before.global.2

noncomputable def handler (setup : Setup base KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (verify : MldsaTranscriptAuth.Verify)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (encode : registration.SignedResponseView → core.option.Option Encoded) :
    QueryImpl (Spec Encoded) (StateT (State n) (OracleComp RootSpec))
  | .inl coin => RegistrationServerRootCompiler.liftProb
      (liftWorld (ordinary setup codec route (.inr (.inl (.inl coin)))))
  | .inr (.accept packet) => RegistrationServerFrontendCompiler.accept setup codec checks route verify packet
  | .inr (.build handle application) => RegistrationServerFrontendCompiler.build setup codec sign encode handle application
  | .inr (.record query) => RegistrationServerRootCompiler.liftProb
      (liftWorld (ordinary setup codec route (.inr (.inr query))))
  | .inr (.hash bytes) => RegistrationServerRootCompiler.liftProb
      (liftWorld (ordinary setup codec route (.inr (.inl (.inr (.hash bytes))))))

/-- The real profile dispatches the original native frontend and ordinary World with the same complete private state. -/
noncomputable def native (setup : Setup base KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (verify : MldsaTranscriptAuth.Verify)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (encode : registration.SignedResponseView → core.option.Option Encoded)
    (correct : PqxdhSecretInputKdf.SourceRootCorrect setup.source setup.hmac)
    (scalar : PqxdhJointGapDh.ScalarBytes) :
    QueryImpl (Spec Encoded) (StateT (RegistrationWorldServerFrontend.State n RegistrationServerRoleBackend.State) ProbComp)
  | .inl coin => nativeWorld (ordinary setup codec route (.inr (.inl (.inl coin))))
  | .inr (.accept packet) => RegistrationWorldServerFrontend.accept setup codec route verify correct scalar
      (RegistrationServerRoleBackend.localBackend setup checks) packet
  | .inr (.build handle application) => RegistrationWorldServerFrontend.build setup codec sign encode handle application
  | .inr (.record query) => nativeWorld (ordinary setup codec route (.inr (.inr query)))
  | .inr (.hash bytes) => nativeWorld (ordinary setup codec route (.inr (.inl (.inr (.hash bytes)))))

private theorem world_native {Value : Type} (setup : Setup base KemSK)
    (created : PqxdhLiveServerConstruction.Created Unit) (scalar : PqxdhJointGapDh.ScalarBytes)
    (work : StateT (Local n) ProbComp Value) (before : Family × State n) :
    Prod.map id (restore created) <$>
      (RegistrationServerRootCompiler.interpret (RegistrationServerRootCompiler.family setup.hmac setup.joint setup.dh created.seed scalar)
        (RegistrationServerRootCompiler.liftProb (liftWorld work))).run before =
      (nativeWorld work).run (restore created before) := by
  rw [RegistrationServerRootCompiler.liftProb_exact]
  simp only [RegistrationRootStage.lift, liftWorld, nativeWorld, restore, StateT.run,
    Functor.map_map, Prod.map, id_eq]

/-- Every actual adaptive API request has the same native outcome and complete World state under the private family interpretation. -/
theorem query_native (setup : Setup base KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (verify : MldsaTranscriptAuth.Verify)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (encode : registration.SignedResponseView → core.option.Option Encoded)
    (correct : PqxdhSecretInputKdf.SourceRootCorrect setup.source setup.hmac)
    (created : PqxdhLiveServerConstruction.Created Unit) (scalar : PqxdhJointGapDh.ScalarBytes)
    (query : (Spec Encoded).Domain) (before : Family × State n) :
    Prod.map id (restore created) <$>
      (RegistrationServerRootCompiler.interpret (RegistrationServerRootCompiler.family setup.hmac setup.joint setup.dh created.seed scalar)
        (handler setup codec checks route verify sign encode query)).run before =
      (native setup codec checks route verify sign encode correct scalar query).run (restore created before) := by
  cases query with
  | inl coin => exact world_native setup created scalar _ before
  | inr query =>
      cases query with
      | accept packet => exact RegistrationServerFrontendCompiler.accept_native setup codec checks route verify correct created scalar packet before
      | build handle application => exact RegistrationServerFrontendCompiler.build_native setup codec sign encode created scalar handle application before
      | record query => exact world_native setup created scalar _ before
      | hash bytes => exact world_native setup created scalar _ before

/-- Arbitrary interleavings retain the entire actual API result, populated metadata, one cache, signing chronology, live kernels and private replay/session state. -/
theorem program_native (setup : Setup base KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (verify : MldsaTranscriptAuth.Verify)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (encode : registration.SignedResponseView → core.option.Option Encoded)
    (correct : PqxdhSecretInputKdf.SourceRootCorrect setup.source setup.hmac)
    (created : PqxdhLiveServerConstruction.Created Unit) (scalar : PqxdhJointGapDh.ScalarBytes)
    (work : OracleComp (Spec Encoded) Result) (before : Family × State n) :
    Prod.map id (restore created) <$>
      (RegistrationServerRootCompiler.interpret (RegistrationServerRootCompiler.family setup.hmac setup.joint setup.dh created.seed scalar)
        (simulateQ (handler setup codec checks route verify sign encode) work)).run before =
      (simulateQ (native setup codec checks route verify sign encode correct scalar) work).run (restore created before) := by
  rw [RegistrationServerRootCompiler.interpret_program _ _
    (fun query => RegistrationServerRootCompiler.interpret
      (RegistrationServerRootCompiler.family setup.hmac setup.joint setup.dh created.seed scalar)
        (handler setup codec checks route verify sign encode query)) (fun _ => rfl)]
  exact OracleComp.map_run_simulateQ_eq_of_query_map_eq _ _ (restore created)
    (query_native setup codec checks route verify sign encode correct created scalar) work before

/-- The reduction receives only public challenge keys. Its initial state and final event are executable functions of those keys and the native public-client state. -/
noncomputable def client (setup : Setup base KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (verify : MldsaTranscriptAuth.Verify)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (encode : registration.SignedResponseView → core.option.Option Encoded)
    (initial : PqxdhJointGapDh.PublicChallenge → ProbComp (State n))
    (adversary : PqxdhJointGapDh.PublicChallenge → OracleComp (Spec Encoded) Result)
    (event : PqxdhJointGapDh.PublicChallenge → Result → State n → Bool)
    (publicValue : PqxdhJointGapDh.PublicChallenge) : OracleComp RootSpec Bool := do
  let before ← simulateQ RegistrationServerRootCompiler.coins (initial publicValue)
  let result ← (simulateQ (handler setup codec checks route verify sign encode) (adversary publicValue)).run before
  pure (event publicValue result.1 result.2)

/-- The source constructor's private selected seed occurs only inside this real native interpretation. Its actual complete replay/registration/record state is threaded into every API request. -/
noncomputable def realProfile (setup : Setup base KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (verify : MldsaTranscriptAuth.Verify)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (encode : registration.SignedResponseView → core.option.Option Encoded)
    (correct : PqxdhSecretInputKdf.SourceRootCorrect setup.source setup.hmac)
    (identityIndex : Nat) (serverKid : Std.U64)
    (initial : PqxdhJointGapDh.PublicChallenge → ProbComp (State n))
    (adversary : PqxdhJointGapDh.PublicChallenge → OracleComp (Spec Encoded) Result)
    (event : PqxdhJointGapDh.PublicChallenge → Result → State n → Bool) : ProbComp Bool := do
  let seed ← PqxdhJointIdentity.sampleSeed
  let scalar ← PqxdhJointGapDh.sampleScalar
  let publicValue := PqxdhJointGapDh.challenge setup.joint setup.dh seed scalar
  let created := PqxdhLiveServerConstruction.initialized (P := Unit) setup.joint identityIndex serverKid .generated seed
  let before ← initial publicValue
  let result ← (simulateQ (native setup codec checks route verify sign encode correct scalar) (adversary publicValue)).run
    (restore created (PqxdhJointDhExtractFamily.empty, before))
  pure (event publicValue result.1 (erase result.2))

noncomputable def idealProfile (setup : Setup base KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (verify : MldsaTranscriptAuth.Verify)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (encode : registration.SignedResponseView → core.option.Option Encoded)
    (initial : PqxdhJointGapDh.PublicChallenge → ProbComp (State n))
    (adversary : PqxdhJointGapDh.PublicChallenge → OracleComp (Spec Encoded) Result)
    (event : PqxdhJointGapDh.PublicChallenge → Result → State n → Bool) : ProbComp Bool :=
  PqxdhJointDhExtractRoot.idealRootGame setup.hmac setup.joint setup.dh
    (client setup codec checks route verify sign encode initial adversary event)

private theorem map_state_apply {S X Y : Type} (f : X → Y) (work : StateT S ProbComp X)
    (before : S) : (f <$> work) before = Prod.map f id <$> work before := by
  change (work before >>= fun result => pure (f result.1, result.2)) = _
  simp only [bind_pure_comp]
  rfl

private theorem coins_exact {Value : Type} (setup : Setup base KemSK)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (work : ProbComp Value) (before : Family) :
    (simulateQ (RegistrationServerRootCompiler.family setup.hmac setup.joint setup.dh seed scalar)
      (simulateQ RegistrationServerRootCompiler.coins work)).run before =
      (fun value => (value, before)) <$> work := by
  rw [← QueryImpl.simulateQ_compose]
  have same : RegistrationServerRootCompiler.family setup.hmac setup.joint setup.dh seed scalar ∘ₛ
      RegistrationServerRootCompiler.coins =
      (QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT Family ProbComp) := by
    funext query
    rfl
  rw [same, simulateQ_liftTarget, simulateQ_ofLift_eq_self, StateT.run_liftM, bind_pure_comp]

private theorem client_native (setup : Setup base KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (verify : MldsaTranscriptAuth.Verify)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (encode : registration.SignedResponseView → core.option.Option Encoded)
    (correct : PqxdhSecretInputKdf.SourceRootCorrect setup.source setup.hmac)
    (created : PqxdhLiveServerConstruction.Created Unit) (scalar : PqxdhJointGapDh.ScalarBytes)
    (initial : PqxdhJointGapDh.PublicChallenge → ProbComp (State n))
    (adversary : PqxdhJointGapDh.PublicChallenge → OracleComp (Spec Encoded) Result)
    (event : PqxdhJointGapDh.PublicChallenge → Result → State n → Bool)
    (publicValue : PqxdhJointGapDh.PublicChallenge) :
    (simulateQ (RegistrationServerRootCompiler.family setup.hmac setup.joint setup.dh created.seed scalar)
      (client setup codec checks route verify sign encode initial adversary event publicValue)).run' PqxdhJointDhExtractFamily.empty =
    (do let before ← initial publicValue
        let result ← (simulateQ (native setup codec checks route verify sign encode correct scalar) (adversary publicValue)).run
          (restore created (PqxdhJointDhExtractFamily.empty, before))
        pure (event publicValue result.1 (erase result.2))) := by
  simp only [client, simulateQ_bind, StateT.run'_eq, StateT.run_bind, map_bind,
    coins_exact, bind_map_left, bind_pure_comp]
  apply congrArg (fun continuation => initial publicValue >>= continuation)
  funext before
  have same := program_native setup codec checks route verify sign encode correct created scalar
    (adversary publicValue) (PqxdhJointDhExtractFamily.empty, before)
  have mapped := congrArg (fun work => (fun result => event publicValue result.1 (erase result.2)) <$> work) same
  simpa only [RegistrationServerRootCompiler.interpret, StateT.run, Functor.map_map,
    Prod.map, id_eq, erase, restore, simulateQ_map, map_state_apply, Functor.map_map] using mapped

/-- This coefficient-one probability bridge is derived from the complete actual adaptive API, rather than a supplied frontend/game equality. -/
theorem profile_real (setup : Setup base KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (verify : MldsaTranscriptAuth.Verify)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (encode : registration.SignedResponseView → core.option.Option Encoded)
    (correct : PqxdhSecretInputKdf.SourceRootCorrect setup.source setup.hmac)
    (identityIndex : Nat) (serverKid : Std.U64)
    (initial : PqxdhJointGapDh.PublicChallenge → ProbComp (State n))
    (adversary : PqxdhJointGapDh.PublicChallenge → OracleComp (Spec Encoded) Result)
    (event : PqxdhJointGapDh.PublicChallenge → Result → State n → Bool) :
    PqxdhJointDhExtractFamily.realGame setup.hmac setup.joint setup.dh
      (fun publicValue => simulateQ PqxdhJointDhExtractRoot.reduction
        (client setup codec checks route verify sign encode initial adversary event publicValue)) =
      realProfile setup codec checks route verify sign encode correct identityIndex serverKid initial adversary event := by
  simp only [PqxdhJointDhExtractFamily.realGame, realProfile, ← QueryImpl.simulateQ_compose]
  apply congrArg (fun continuation => PqxdhJointIdentity.sampleSeed >>= continuation)
  funext seed
  apply congrArg (fun continuation => PqxdhJointGapDh.sampleScalar >>= continuation)
  funext scalar
  exact client_native setup codec checks route verify sign encode correct
    (PqxdhLiveServerConstruction.initialized (P := Unit) setup.joint identityIndex serverKid .generated seed)
    scalar initial adversary event _

/-- The real native mandatory-ML Server profile pays exactly the constructed related-input family advantage to its ideal-root profile. This endpoint makes no smallness assumption and does not replace later key-schedule, hidden installation, or fresh-event record bounds. -/
theorem family_advantage (setup : Setup base KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (verify : MldsaTranscriptAuth.Verify)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (encode : registration.SignedResponseView → core.option.Option Encoded)
    (correct : PqxdhSecretInputKdf.SourceRootCorrect setup.source setup.hmac)
    (identityIndex : Nat) (serverKid : Std.U64)
    (initial : PqxdhJointGapDh.PublicChallenge → ProbComp (State n))
    (adversary : PqxdhJointGapDh.PublicChallenge → OracleComp (Spec Encoded) Result)
    (event : PqxdhJointGapDh.PublicChallenge → Result → State n → Bool) :
    (realProfile setup codec checks route verify sign encode correct identityIndex serverKid initial adversary event).boolDistance
      (idealProfile setup codec checks route verify sign encode initial adversary event) =
      PqxdhJointDhExtractFamily.advantage setup.hmac setup.joint setup.dh
        (fun publicValue => simulateQ PqxdhJointDhExtractRoot.reduction
          (client setup codec checks route verify sign encode initial adversary event publicValue)) := by
  rw [PqxdhJointDhExtractFamily.advantage,
    profile_real setup codec checks route verify sign encode correct identityIndex serverKid initial adversary event]
  rfl

end BeaconcryptCore.Computational.RegistrationServerFrontendGame

/-- info: 'BeaconcryptCore.Computational.RegistrationServerFrontendGame.query_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationServerFrontendGame.query_native

/-- info: 'BeaconcryptCore.Computational.RegistrationServerFrontendGame.program_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationServerFrontendGame.program_native

/-- info: 'BeaconcryptCore.Computational.RegistrationServerFrontendGame.profile_real' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationServerFrontendGame.profile_real

/-- info: 'BeaconcryptCore.Computational.RegistrationServerFrontendGame.family_advantage' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationServerFrontendGame.family_advantage
