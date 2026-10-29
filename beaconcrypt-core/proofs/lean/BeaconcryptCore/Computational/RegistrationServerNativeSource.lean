-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationServerFrontendGame

/-! This source interpreter executes the actual concrete role backend and native agreement controller under the owned replay lookup. The selected converter's fixed-width representation is explicit. Root-family bookkeeping is removed only from the analysis projection; actual SDK conversion/KEM/DH/HKDF, ML/Ed gates, replay insertion and publication effects remain. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationServerNativeSource
open PqxdhServerAuthExperiment (Setup Codec Checks)
open RegistrationServerRootCompiler (Local Family)
open PqxdhJointDhExtractRoot (RootSpec)
open RegistrationServerFrontendCompiler (State restore erase)
variable {ι KemSK Reader Response Encoded Value : Type} {base : OracleSpec ι} {n : Nat}

/-- The immutable constructor is private to the source interpreter. No selected seed is put into executable client state. -/
def sourceStep (created : PqxdhLiveServerConstruction.Created Unit)
    (work : StateT (RegistrationWorldServerFrontend.State n RegistrationServerRoleBackend.State) ProbComp Value) :
    StateT (State n) ProbComp Value := fun before =>
  Prod.map id erase <$> work.run (restore created (PqxdhJointDhExtractFamily.empty, before))

/-- Actual replay lookup precedes all actual concrete conversion/KEM/DH/root callbacks. -/
noncomputable def agree (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit)
    (packet : registration.InitPacket) (authenticated : registration.AuthenticatedInit) :
    StateT (State n) ProbComp (RustM agreement.AgreementEffect) := fun before =>
  (fun result => (result.1, { before with world := result.2 })) <$>
    (simulateQ (RegistrationWorldAgreement.agreement setup.source
      (RegistrationServerRoleBackend.native setup checks representation created.seed))
      (RegistrationReplaySchedule.begin before.control authenticated before.consumed)).run before.world

noncomputable def authenticate (setup : Setup base KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (verify : MldsaTranscriptAuth.Verify)
    (created : PqxdhLiveServerConstruction.Created Unit) (packet : registration.InitPacket) :=
  sourceStep (n := n) created (RegistrationWorldServerFrontend.authenticate setup codec route verify packet)

def retain (created : PqxdhLiveServerConstruction.Created Unit) (accepted : agreement.ServerAgreement) :=
  sourceStep (n := n) created (RegistrationWorldServerFrontend.retain accepted)

/-- The actual native source accepts only after mandatory ML/Ed authentication and private replay lookup, then inserts the ID before giving the one-use handle. -/
noncomputable def accept (setup : Setup base KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (verify : MldsaTranscriptAuth.Verify)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (packet : registration.InitPacket) :
    StateT (State n) ProbComp (RustM (Option Nat)) := do
  let checked ← authenticate setup codec route verify created packet
  match checked with
  | .fail error => pure (.fail error)
  | .div => pure .div
  | .ok (_events, .Accepted authenticated) =>
      let completed ← agree setup checks representation created packet authenticated
      match completed with
      | .fail error => pure (.fail error)
      | .div => pure .div
      | .ok (.ServerComplete accepted) => retain created accepted
      | .ok _ => pure (.ok none)
  | .ok _ => pure (.ok none)

private theorem map_state_apply {S X Y : Type} (f : X → Y) (work : StateT S ProbComp X)
    (before : S) : (f <$> work) before = Prod.map f id <$> work before := by
  change (work before >>= fun result => pure (f result.1, result.2)) = _
  simp only [bind_pure_comp]
  rfl

/-- Actual SDK converter validity is derived from the explicit Array32 representation, not an adversarial Fresh or successful-callback assertion. -/
theorem agree_source (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (correct : PqxdhSecretInputKdf.SourceRootCorrect setup.source setup.hmac)
    (created : PqxdhLiveServerConstruction.Created Unit) (scalar : PqxdhJointGapDh.ScalarBytes)
    (packet : registration.InitPacket) (authenticated : registration.AuthenticatedInit) (before : Family × State n) :
    Prod.map id Prod.snd <$>
      (RegistrationServerRootCompiler.interpret (RegistrationServerRootCompiler.family setup.hmac setup.joint setup.dh created.seed scalar)
        (RegistrationServerFrontendCompiler.agree setup checks packet authenticated)).run before =
      (agree setup checks representation created packet authenticated).run before.2 := by
  simp only [agree, StateT.run]
  rw [RegistrationReplaySchedule.begin_eq]
  by_cases consumed : before.2.consumed.contains (RegistrationReplaySchedule.identifier authenticated) = true
  · simp only [RegistrationServerRootCompiler.interpret, RegistrationServerFrontendCompiler.agree,
      StateT.run, consumed, ite_true, simulateQ_pure, ]
    rfl
  · have same := RegistrationServerRootCompiler.world_native setup checks representation correct created.seed scalar
      before.2.control packet authenticated (before.1, before.2.world)
    have mapped := congrArg (fun work =>
      (fun result => (result.1, { before.2 with world := result.2 })) <$> work) same
    simpa only [RegistrationServerRootCompiler.interpret, RegistrationServerFrontendCompiler.agree,
      RegistrationServerFrontendCompiler.world, RegistrationServerFrontendCompiler.withWorld,
      StateT.run, consumed, Bool.false_eq_true, ite_false, simulateQ_map, map_state_apply,
      Functor.map_map, Prod.map, id_eq] using mapped

private theorem authenticate_frame (setup : Setup base KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (verify : MldsaTranscriptAuth.Verify)
    (created : PqxdhLiveServerConstruction.Created Unit) (packet : registration.InitPacket)
    (family : Family) (before : State n) :
    Prod.map id erase <$>
      (RegistrationWorldServerFrontend.authenticate setup codec route verify packet).run (restore created (family, before)) =
      (authenticate setup codec route verify created packet).run before := by
  simp only [authenticate, sourceStep, RegistrationWorldServerFrontend.authenticate, RegistrationWorldServerFrontend.withWorld,
    restore, erase, StateT.run, Functor.map_map, Prod.map, id_eq]

private theorem retain_frame (created : PqxdhLiveServerConstruction.Created Unit) (accepted : agreement.ServerAgreement)
    (family : Family) (before : State n) :
    Prod.map id erase <$> (RegistrationWorldServerFrontend.retain accepted).run (restore created (family, before)) =
      (retain created accepted).run before := by
  simp only [retain, sourceStep, RegistrationWorldServerFrontend.retain, restore, StateT.run]
  cases actual : RegistrationReplaySchedule.consume accepted before.consumed with
  | fail error => simp only [map_pure]; rfl
  | div => simp only [map_pure]; rfl
  | ok result => rcases result with ⟨option, history⟩; cases option <;> simp only [map_pure] <;> rfl

private theorem erase_restore (created : PqxdhLiveServerConstruction.Created Unit) (state : Family × State n) :
    erase (restore created state) = state.2 := rfl

private theorem drop_eq {X : Type} :
    (Prod.map (id : X → X) (Prod.snd : Family × State n → State n)) =
      fun result => (result.1, result.2.2) := by
  funext result
  rcases result with ⟨value, family, state⟩
  rfl

private theorem authenticate_source (setup : Setup base KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (verify : MldsaTranscriptAuth.Verify)
    (created : PqxdhLiveServerConstruction.Created Unit) (scalar : PqxdhJointGapDh.ScalarBytes)
    (packet : registration.InitPacket) (before : Family × State n) :
    Prod.map id Prod.snd <$>
      (RegistrationServerRootCompiler.interpret (RegistrationServerRootCompiler.family setup.hmac setup.joint setup.dh created.seed scalar)
        (RegistrationServerFrontendCompiler.authenticate setup codec route verify packet)).run before =
      (authenticate setup codec route verify created packet).run before.2 := by
  have same := congrArg (fun work => Prod.map id erase <$> work)
    (RegistrationServerFrontendCompiler.authenticate_native setup codec route verify created scalar packet before)
  simpa only [drop_eq, Functor.map_map, Function.comp_def, Prod.map, id_eq, erase_restore] using same.trans
    (authenticate_frame setup codec route verify created packet before.1 before.2)

private theorem retain_source (setup : Setup base KemSK) (created : PqxdhLiveServerConstruction.Created Unit)
    (scalar : PqxdhJointGapDh.ScalarBytes) (accepted : agreement.ServerAgreement) (before : Family × State n) :
    Prod.map id Prod.snd <$>
      (RegistrationServerRootCompiler.interpret (RegistrationServerRootCompiler.family setup.hmac setup.joint setup.dh created.seed scalar)
        (RegistrationServerFrontendCompiler.retain accepted)).run before =
      (retain created accepted).run before.2 := by
  have same := congrArg (fun work => Prod.map id erase <$> work)
    (RegistrationServerFrontendCompiler.retain_native setup created scalar accepted before)
  simpa only [drop_eq, Functor.map_map, Function.comp_def, Prod.map, id_eq, erase_restore] using same.trans
    (retain_frame created accepted before.1 before.2)

private theorem pure_source {X : Type} (family : QueryImpl RootSpec (StateT Family ProbComp))
    (value : X) (before : Family × State n) :
    Prod.map id Prod.snd <$> (RegistrationServerRootCompiler.interpret family (pure value)).run before =
      (pure value : StateT (State n) ProbComp _).run before.2 := by
  rw [RegistrationServerRootCompiler.interpret_pure]
  simp only [StateT.run_pure, map_pure, Prod.map, id_eq]

private theorem bind_source {X Y : Type} (family : QueryImpl RootSpec (StateT Family ProbComp))
    (work : StateT (State n) (OracleComp RootSpec) X) (source : StateT (State n) ProbComp X)
    (next : X → StateT (State n) (OracleComp RootSpec) Y) (sourceNext : X → StateT (State n) ProbComp Y)
    (first : ∀ before, Prod.map id Prod.snd <$>
      (RegistrationServerRootCompiler.interpret family work).run before = source.run before.2)
    (rest : ∀ value before, Prod.map id Prod.snd <$>
      (RegistrationServerRootCompiler.interpret family (next value)).run before = (sourceNext value).run before.2)
    (before : Family × State n) :
    Prod.map id Prod.snd <$> (RegistrationServerRootCompiler.interpret family (work >>= next)).run before =
      (source >>= sourceNext).run before.2 := by
  rw [RegistrationServerRootCompiler.interpret_bind, StateT.run_bind, StateT.run_bind, map_bind,
    ← first before, bind_map_left]
  apply congrArg (fun continuation => (RegistrationServerRootCompiler.interpret family work).run before >>= continuation)
  funext result
  exact rest result.1 result.2

/-- The complete actual concrete-source mandatory-ML accept execution is derived, including optional converter/KEM/DH outcomes and all owned replay mutations. -/
theorem accept_source (setup : Setup base KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (verify : MldsaTranscriptAuth.Verify)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (correct : PqxdhSecretInputKdf.SourceRootCorrect setup.source setup.hmac)
    (created : PqxdhLiveServerConstruction.Created Unit) (scalar : PqxdhJointGapDh.ScalarBytes)
    (packet : registration.InitPacket) (before : Family × State n) :
    Prod.map id Prod.snd <$>
      (RegistrationServerRootCompiler.interpret (RegistrationServerRootCompiler.family setup.hmac setup.joint setup.dh created.seed scalar)
        (RegistrationServerFrontendCompiler.accept setup codec checks route verify packet)).run before =
      (accept setup codec checks route verify representation created packet).run before.2 := by
  unfold accept RegistrationServerFrontendCompiler.accept
  apply bind_source _ _ _ _ _ (authenticate_source setup codec route verify created scalar packet)
  intro checked current
  cases checked with
  | fail error => exact pure_source _ _ _
  | div => exact pure_source _ _ _
  | ok checked =>
      rcases checked with ⟨events, checked⟩
      cases checked <;> try exact pure_source _ _ _
      apply bind_source _ _ _ _ _ (agree_source setup checks representation correct created scalar packet _)
      intro completed after
      cases completed with
      | fail error => exact pure_source _ _ _
      | div => exact pure_source _ _ _
      | ok effect => cases effect <;> first
        | exact pure_source _ _ _
        | exact retain_source setup created scalar _ after

private theorem complete_frame (setup : Setup base KemSK) (codec : Codec Reader Response)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (encode : registration.SignedResponseView → core.option.Option Encoded)
    (created : PqxdhLiveServerConstruction.Created Unit) (family : Family) (before : State n)
    (consumed : peer.ConsumedRegistration) (application : Slice U8) :
    Prod.map id erase <$>
      (RegistrationWorldServerFrontend.complete setup codec sign encode consumed application).run (restore created (family, before)) =
    Prod.map id erase <$>
      (RegistrationWorldServerFrontend.complete setup codec sign encode consumed application).run
        (restore created (PqxdhJointDhExtractFamily.empty, before)) := by
  simp only [RegistrationWorldServerFrontend.complete, RegistrationWorldServerCompletion.global,
    restore, StateT.run, bind_map_left, map_bind, ]
  apply congrArg (fun continuation =>
    (RegistrationWorldServerCompletion.server setup codec sign encode before.control before.pin consumed application).run
      before.world >>= continuation)
  funext result
  rcases result with ⟨result, after⟩
  cases result with
  | fail error => rfl
  | div => rfl
  | ok result => cases result <;> rfl

private theorem get_bind {S X : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (next : S → StateT S m X) : (get >>= next) = fun before => (next before).run before := by
  funext before
  change ((pure (before, before) : m (S × S)) >>= fun current => (next current.1).run current.2) = _
  rw [pure_bind]

private theorem build_frame (setup : Setup base KemSK) (codec : Codec Reader Response)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (encode : registration.SignedResponseView → core.option.Option Encoded)
    (created : PqxdhLiveServerConstruction.Created Unit) (family : Family) (before : State n)
    (handle : Nat) (application : Slice U8) :
    Prod.map id erase <$>
      (RegistrationWorldServerFrontend.build setup codec sign encode handle application).run (restore created (family, before)) =
    Prod.map id erase <$>
      (RegistrationWorldServerFrontend.build setup codec sign encode handle application).run
        (restore created (PqxdhJointDhExtractFamily.empty, before)) := by
  simp only [RegistrationWorldServerFrontend.build]
  simp only [StateT.run_bind]
  simp only [RegistrationWorldServerFrontend.take, restore, StateT.run]
  cases actual : before.sessions[handle]? with
  | none => simp only [pure_bind]; rfl
  | some option =>
      cases option with
      | none => simp only [pure_bind]; rfl
      | some consumed =>
          simp only [pure_bind, get_bind]
          by_cases admitted : RegistrationWorldServerFrontend.responseAdmitted before.control application = true
          · simpa only [admitted, ite_true, restore] using
              complete_frame setup codec sign encode created family
                ({ before with sessions := before.sessions.set handle none }) consumed application
          · simp only [admitted, Bool.false_eq_true, ite_false]
            rfl

/-- Actual complete-source publication, including failures after64/76/ML signing or encoding, has no private family-state dependency. -/
theorem build_source (setup : Setup base KemSK) (codec : Codec Reader Response)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (encode : registration.SignedResponseView → core.option.Option Encoded)
    (created : PqxdhLiveServerConstruction.Created Unit) (scalar : PqxdhJointGapDh.ScalarBytes)
    (handle : Nat) (application : Slice U8) (before : Family × State n) :
    Prod.map id Prod.snd <$>
      (RegistrationServerRootCompiler.interpret (RegistrationServerRootCompiler.family setup.hmac setup.joint setup.dh created.seed scalar)
        (RegistrationServerFrontendCompiler.build setup codec sign encode handle application)).run before =
      (sourceStep created (RegistrationWorldServerFrontend.build setup codec sign encode handle application)).run before.2 := by
  have same := congrArg (fun work => Prod.map id erase <$> work)
    (RegistrationServerFrontendCompiler.build_native setup codec sign encode created scalar handle application before)
  simpa only [drop_eq, Functor.map_map, Function.comp_def, Prod.map, id_eq, erase_restore, sourceStep, StateT.run] using same.trans
    (build_frame setup codec sign encode created before.1 before.2 handle application)

/-- Every accept dispatches the actual concrete native role backend; ordinary commands retain the original native frontend/World implementation. -/
noncomputable def handler (setup : Setup base KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (verify : MldsaTranscriptAuth.Verify)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (encode : registration.SignedResponseView → core.option.Option Encoded)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (correct : PqxdhSecretInputKdf.SourceRootCorrect setup.source setup.hmac)
    (created : PqxdhLiveServerConstruction.Created Unit) (scalar : PqxdhJointGapDh.ScalarBytes) :
    QueryImpl (RegistrationServerFrontendGame.Spec Encoded) (StateT (State n) ProbComp)
  | .inr (.accept packet) => accept setup codec checks route verify representation created packet
  | query => sourceStep created
      (RegistrationServerFrontendGame.native setup codec checks route verify sign encode correct scalar query)

private theorem world_source {X : Type} (setup : Setup base KemSK)
    (created : PqxdhLiveServerConstruction.Created Unit) (scalar : PqxdhJointGapDh.ScalarBytes)
    (work : StateT (Local n) ProbComp X) (before : Family × State n) :
    Prod.map id Prod.snd <$>
      (RegistrationServerRootCompiler.interpret (RegistrationServerRootCompiler.family setup.hmac setup.joint setup.dh created.seed scalar)
        (RegistrationServerRootCompiler.liftProb (RegistrationServerFrontendGame.liftWorld work))).run before =
      (sourceStep created (RegistrationServerFrontendGame.nativeWorld work)).run before.2 := by
  rw [RegistrationServerRootCompiler.liftProb_exact]
  simp only [RegistrationRootStage.lift, RegistrationServerFrontendGame.liftWorld,
    RegistrationServerFrontendGame.nativeWorld, sourceStep, restore, erase, StateT.run,
    Functor.map_map, Prod.map, id_eq]

/-- The complete concrete-source API, including the explicit SDK representation boundary, is obtained request by request without a frontend-simulation assumption. -/
theorem query_source (setup : Setup base KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (verify : MldsaTranscriptAuth.Verify)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (encode : registration.SignedResponseView → core.option.Option Encoded)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (correct : PqxdhSecretInputKdf.SourceRootCorrect setup.source setup.hmac)
    (created : PqxdhLiveServerConstruction.Created Unit) (scalar : PqxdhJointGapDh.ScalarBytes)
    (query : (RegistrationServerFrontendGame.Spec Encoded).Domain) (before : Family × State n) :
    Prod.map id Prod.snd <$>
      (RegistrationServerRootCompiler.interpret (RegistrationServerRootCompiler.family setup.hmac setup.joint setup.dh created.seed scalar)
        (RegistrationServerFrontendGame.handler setup codec checks route verify sign encode query)).run before =
      (handler setup codec checks route verify sign encode representation correct created scalar query).run before.2 := by
  cases query with
  | inl coin => exact world_source setup created scalar _ before
  | inr query =>
      cases query with
      | accept packet => exact accept_source setup codec checks route verify representation correct created scalar packet before
      | build handle application => exact build_source setup codec sign encode created scalar handle application before
      | record query => exact world_source setup created scalar _ before
      | hash bytes => exact world_source setup created scalar _ before

/-- Any adaptive native transcript and final state are preserved while private root-family bookkeeping alone is forgotten. -/
theorem program_source {X : Type} (setup : Setup base KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (verify : MldsaTranscriptAuth.Verify)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (encode : registration.SignedResponseView → core.option.Option Encoded)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (correct : PqxdhSecretInputKdf.SourceRootCorrect setup.source setup.hmac)
    (created : PqxdhLiveServerConstruction.Created Unit) (scalar : PqxdhJointGapDh.ScalarBytes)
    (work : OracleComp (RegistrationServerFrontendGame.Spec Encoded) X) (before : Family × State n) :
    Prod.map id Prod.snd <$>
      (RegistrationServerRootCompiler.interpret (RegistrationServerRootCompiler.family setup.hmac setup.joint setup.dh created.seed scalar)
        (simulateQ (RegistrationServerFrontendGame.handler setup codec checks route verify sign encode) work)).run before =
      (simulateQ (handler setup codec checks route verify sign encode representation correct created scalar) work).run before.2 := by
  rw [RegistrationServerRootCompiler.interpret_program _ _
    (fun query => RegistrationServerRootCompiler.interpret
      (RegistrationServerRootCompiler.family setup.hmac setup.joint setup.dh created.seed scalar)
        (RegistrationServerFrontendGame.handler setup codec checks route verify sign encode query)) (fun _ => rfl)]
  exact OracleComp.map_run_simulateQ_eq_of_query_map_eq _ _ Prod.snd
    (query_source setup codec checks route verify sign encode representation correct created scalar) work before

/-- This real probability experiment executes the actual SDK-shaped typed Server source, not the analysis-family controller. -/
noncomputable def profile {X : Type} (setup : Setup base KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (verify : MldsaTranscriptAuth.Verify)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (encode : registration.SignedResponseView → core.option.Option Encoded)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (correct : PqxdhSecretInputKdf.SourceRootCorrect setup.source setup.hmac)
    (identityIndex : Nat) (serverKid : Std.U64)
    (initial : PqxdhJointGapDh.PublicChallenge → ProbComp (State n))
    (adversary : PqxdhJointGapDh.PublicChallenge → OracleComp (RegistrationServerFrontendGame.Spec Encoded) X)
    (event : PqxdhJointGapDh.PublicChallenge → X → State n → Bool) : ProbComp Bool := do
  let seed ← PqxdhJointIdentity.sampleSeed
  let scalar ← PqxdhJointGapDh.sampleScalar
  let publicValue := PqxdhJointGapDh.challenge setup.joint setup.dh seed scalar
  let created := PqxdhLiveServerConstruction.initialized (P := Unit) setup.joint identityIndex serverKid .generated seed
  let before ← initial publicValue
  let result ← (simulateQ (handler setup codec checks route verify sign encode representation correct created scalar)
    (adversary publicValue)).run before
  pure (event publicValue result.1 result.2)

private theorem coins_exact {X : Type} (setup : Setup base KemSK)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (work : ProbComp X) (before : Family) :
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

private theorem client_source {X : Type} (setup : Setup base KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (verify : MldsaTranscriptAuth.Verify)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (encode : registration.SignedResponseView → core.option.Option Encoded)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (correct : PqxdhSecretInputKdf.SourceRootCorrect setup.source setup.hmac)
    (created : PqxdhLiveServerConstruction.Created Unit) (scalar : PqxdhJointGapDh.ScalarBytes)
    (initial : PqxdhJointGapDh.PublicChallenge → ProbComp (State n))
    (adversary : PqxdhJointGapDh.PublicChallenge → OracleComp (RegistrationServerFrontendGame.Spec Encoded) X)
    (event : PqxdhJointGapDh.PublicChallenge → X → State n → Bool)
    (publicValue : PqxdhJointGapDh.PublicChallenge) :
    (simulateQ (RegistrationServerRootCompiler.family setup.hmac setup.joint setup.dh created.seed scalar)
      (RegistrationServerFrontendGame.client setup codec checks route verify sign encode initial adversary event publicValue)).run'
        PqxdhJointDhExtractFamily.empty =
    (do let before ← initial publicValue
        let result ← (simulateQ (handler setup codec checks route verify sign encode representation correct created scalar)
          (adversary publicValue)).run before
        pure (event publicValue result.1 result.2)) := by
  simp only [RegistrationServerFrontendGame.client, simulateQ_bind, StateT.run'_eq, StateT.run_bind,
    map_bind, coins_exact, bind_map_left, bind_pure_comp]
  apply congrArg (fun continuation => initial publicValue >>= continuation)
  funext before
  have same := program_source setup codec checks route verify sign encode representation correct created scalar
    (adversary publicValue) (PqxdhJointDhExtractFamily.empty, before)
  have mapped := congrArg (fun work => (fun result => event publicValue result.1 result.2) <$> work) same
  simpa only [RegistrationServerRootCompiler.interpret, StateT.run, Functor.map_map, Prod.map, id_eq,
    simulateQ_map, map_state_apply, Functor.map_map] using mapped

/-- The complete adaptive actual source probability is identified with a concrete related-root reduction under the explicit converted-key representation contract. -/
theorem profile_real {X : Type} (setup : Setup base KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (verify : MldsaTranscriptAuth.Verify)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (encode : registration.SignedResponseView → core.option.Option Encoded)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (correct : PqxdhSecretInputKdf.SourceRootCorrect setup.source setup.hmac)
    (identityIndex : Nat) (serverKid : Std.U64)
    (initial : PqxdhJointGapDh.PublicChallenge → ProbComp (State n))
    (adversary : PqxdhJointGapDh.PublicChallenge → OracleComp (RegistrationServerFrontendGame.Spec Encoded) X)
    (event : PqxdhJointGapDh.PublicChallenge → X → State n → Bool) :
    PqxdhJointDhExtractFamily.realGame setup.hmac setup.joint setup.dh
      (fun publicValue => simulateQ PqxdhJointDhExtractRoot.reduction
        (RegistrationServerFrontendGame.client setup codec checks route verify sign encode initial adversary event publicValue)) =
      profile setup codec checks route verify sign encode representation correct identityIndex serverKid initial adversary event := by
  simp only [PqxdhJointDhExtractFamily.realGame, profile, ← QueryImpl.simulateQ_compose]
  apply congrArg (fun continuation => PqxdhJointIdentity.sampleSeed >>= continuation)
  funext seed
  apply congrArg (fun continuation => PqxdhJointGapDh.sampleScalar >>= continuation)
  funext scalar
  exact client_source setup codec checks route verify sign encode representation correct
    (PqxdhLiveServerConstruction.initialized (P := Unit) setup.joint identityIndex serverKid .generated seed)
    scalar initial adversary event _

/-- The actual mandatory-ML SDK-source profile has coefficient-one related-root loss; no whole-game equality, supplied verifier verdict, guessed digest or adversarial Fresh status is an assumption. -/
theorem family_advantage {X : Type} (setup : Setup base KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (verify : MldsaTranscriptAuth.Verify)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (encode : registration.SignedResponseView → core.option.Option Encoded)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (correct : PqxdhSecretInputKdf.SourceRootCorrect setup.source setup.hmac)
    (identityIndex : Nat) (serverKid : Std.U64)
    (initial : PqxdhJointGapDh.PublicChallenge → ProbComp (State n))
    (adversary : PqxdhJointGapDh.PublicChallenge → OracleComp (RegistrationServerFrontendGame.Spec Encoded) X)
    (event : PqxdhJointGapDh.PublicChallenge → X → State n → Bool) :
    (profile setup codec checks route verify sign encode representation correct identityIndex serverKid initial adversary event).boolDistance
      (RegistrationServerFrontendGame.idealProfile setup codec checks route verify sign encode initial adversary event) =
      PqxdhJointDhExtractFamily.advantage setup.hmac setup.joint setup.dh
        (fun publicValue => simulateQ PqxdhJointDhExtractRoot.reduction
          (RegistrationServerFrontendGame.client setup codec checks route verify sign encode initial adversary event publicValue)) := by
  rw [PqxdhJointDhExtractFamily.advantage,
    profile_real setup codec checks route verify sign encode representation correct identityIndex serverKid initial adversary event]
  rfl

end BeaconcryptCore.Computational.RegistrationServerNativeSource

/-- info: 'BeaconcryptCore.Computational.RegistrationServerNativeSource.agree_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationServerNativeSource.agree_source

/-- info: 'BeaconcryptCore.Computational.RegistrationServerNativeSource.accept_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationServerNativeSource.accept_source

/-- info: 'BeaconcryptCore.Computational.RegistrationServerNativeSource.build_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationServerNativeSource.build_source

/-- info: 'BeaconcryptCore.Computational.RegistrationServerNativeSource.query_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationServerNativeSource.query_source

/-- info: 'BeaconcryptCore.Computational.RegistrationServerNativeSource.program_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationServerNativeSource.program_source

/-- info: 'BeaconcryptCore.Computational.RegistrationServerNativeSource.profile_real' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationServerNativeSource.profile_real

/-- info: 'BeaconcryptCore.Computational.RegistrationServerNativeSource.family_advantage' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationServerNativeSource.family_advantage
