-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeKemServerCompiler

/-! The actual closed SDK accept opens its literal selected KEM callback after authentication, replay lookup and registration reservation. Every reached operational state and the complete private pool are retained; only the independently bounded uniform accounting coordinate is projected. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeKemSdkCompiler
open PqxdhServerAuthExperiment (Setup Codec Checks)
open RegistrationNativeKemServerState (State mask)
open RegistrationNativeKemServerCompiler (project nativeAgreement)
open RegistrationNativeKemServerInterface (source)
variable {ι KemSK Reader Response Value A B : Type} {base : OracleSpec ι} {n : Nat}
variable {mlSource : RegistrationNativeMldsa.Source}

def server (work : StateT (RegistrationServerFrontendCompiler.State n) ProbComp Value) :
    StateT (State n mlSource × PqxdhLiveKemBirth.Pool KemSK) ProbComp Value := fun before =>
  (fun result => (result.1, ({ before.1 with server := result.2 }, before.2))) <$> work.run before.1.server

private theorem server_bind (work : StateT (RegistrationServerFrontendCompiler.State n) ProbComp A)
    (next : A → StateT (RegistrationServerFrontendCompiler.State n) ProbComp B) :
    (server (KemSK := KemSK) (mlSource := mlSource) (work >>= next)) = server work >>= fun result => server (next result) := by
  funext before
  simp only [server, StateT.run, StateT.monad_bind_def, StateT.bind, map_bind, bind_map_left]

private theorem server_pure (value : Value) :
    server (KemSK := KemSK) (n := n) (mlSource := mlSource) (pure value) = pure value := by
  funext before
  simp only [server, StateT.run_pure, map_pure]
  rfl

private theorem native_program (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (work : OracleComp RegistrationAgreementExecutor.Spec Value)
    (before : State n mlSource × PqxdhLiveKemBirth.Pool KemSK) :
    (simulateQ (nativeAgreement setup checks representation created) work).run before =
      (fun result => (result.1, ({ before.1 with server := { before.1.server with world := result.2 } }, before.2))) <$>
        (simulateQ (RegistrationWorldAgreement.agreement setup.source
          (RegistrationServerRoleBackend.native setup checks representation created.seed)) work).run before.1.server.world := by
  induction work using OracleComp.inductionOn generalizing before with
  | pure value => rfl
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, map_bind, ih]
      simp only [RegistrationNativeKemServerCompiler.nativeAgreement, StateT.run, bind_map_left]

private theorem get_run (setup : Setup base KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (verify : MldsaTranscriptAuth.Verify)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (before : State n mlSource × PqxdhLiveKemBirth.Pool KemSK) :
    (simulateQ (source setup codec checks route verify representation created)
      RegistrationNativeKemServerInterface.get).run before = pure (mask before.1, project before) := by
  simp only [RegistrationNativeKemServerInterface.get, simulateQ_spec_query, source,
    RegistrationNativeKemInterface.source, RegistrationNativeKemServerInterface.other,
    StateT.run, map_pure, project]

private theorem authenticate_source (setup : Setup base KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (verify : MldsaTranscriptAuth.Verify)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (packet : registration.InitPacket)
    (before : State n mlSource × PqxdhLiveKemBirth.Pool KemSK) :
    Prod.map id project <$> (server (RegistrationServerNativeSource.authenticate setup codec route verify created packet)).run before =
      (simulateQ (source setup codec checks route verify representation created)
        ((RegistrationNativeKemServerInterface.Spec n mlSource KemSK).query (.inl (.authenticate packet)) :
          OracleComp (RegistrationNativeKemServerInterface.Spec n mlSource KemSK)
            (RustM (List BeaconcryptCore.Refinement.RegistrationAuthenticationFlow.Event × registration.InitAuthentication)))).run (project before) := by
  have law := congrArg (fun work => (fun result => (result.1,
      ({ before.1 with server := result.2 }, before.2))) <$> work)
    (RegistrationNativeKemWorldAuthentication.native_auth_input setup codec route verify created packet before.1.server)
  simpa only [server, simulateQ_spec_query, source, RegistrationNativeKemInterface.source,
    RegistrationNativeKemServerInterface.other, RegistrationNativeKemServerInterface.server,
    StateT.run, Functor.map_map, Prod.map, id_eq, Function.comp_def, project, mask] using law

private theorem retain_source (setup : Setup base KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (verify : MldsaTranscriptAuth.Verify)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (accepted : agreement.ServerAgreement)
    (before : State n mlSource × PqxdhLiveKemBirth.Pool KemSK) :
    Prod.map id project <$> (server (RegistrationServerNativeSource.retain created accepted)).run before =
      (simulateQ (source setup codec checks route verify representation created)
        ((RegistrationNativeKemServerInterface.Spec n mlSource KemSK).query (.inl (.retain accepted)) :
          OracleComp (RegistrationNativeKemServerInterface.Spec n mlSource KemSK) (RustM (Option Nat)))).run (project before) := by
  have law := congrArg (fun work => (fun result => (result.1,
      ({ before.1 with server := result.2 }, before.2))) <$> work)
    (RegistrationNativeKemWorldAgreement.native_retain_input created accepted before.1.server)
  simpa only [server, simulateQ_spec_query, source, RegistrationNativeKemInterface.source,
    RegistrationNativeKemServerInterface.other, RegistrationNativeKemServerInterface.server,
    StateT.run, Functor.map_map, Prod.map, id_eq, Function.comp_def, project, mask] using law

noncomputable def begin (setup : Setup base KemSK) (checks : Checks) (authenticated : registration.AuthenticatedInit) :
    OracleComp (RegistrationNativeKemServerInterface.Spec n mlSource KemSK) (RustM agreement.AgreementEffect) := do
  let before ← RegistrationNativeKemServerInterface.get
  simulateQ (RegistrationNativeKemServerInterface.agreement setup checks)
    (RegistrationReplaySchedule.begin before.server.control authenticated before.server.consumed)

/-- The native agreement retains its actual controller, source root, role state and request log through the exposed selected KEM callback. -/
theorem agree_source (setup : Setup base KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (verify : MldsaTranscriptAuth.Verify)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (packet : registration.InitPacket)
    (authenticated : registration.AuthenticatedInit) (before : State n mlSource × PqxdhLiveKemBirth.Pool KemSK) :
    Prod.map id project <$> (server (RegistrationServerNativeSource.agree setup checks representation created packet authenticated)).run before =
      (simulateQ (source setup codec checks route verify representation created)
        (begin setup checks authenticated)).run (project before) := by
  have law := RegistrationNativeKemServerCompiler.agreement_program setup codec checks route verify representation created
    (RegistrationReplaySchedule.begin before.1.server.control authenticated before.1.server.consumed) before
  rw [native_program] at law
  simp only [begin, simulateQ_bind, StateT.run_bind, get_run, pure_bind]
  simpa only [server, RegistrationServerNativeSource.agree, StateT.run, Functor.map_map,
    Prod.map, id_eq, Function.comp_def, project, mask, RegistrationNativeKemServerState.maskServer,
    RegistrationNativeKemWorldUniform.mask_idempotent] using law

private theorem bind_project {A B S T : Type} (projection : S → T)
    (native : StateT S ProbComp A) (lower : StateT T ProbComp A)
    (nativeNext : A → StateT S ProbComp B) (lowerNext : A → StateT T ProbComp B)
    (queryLaw : ∀ before, Prod.map id projection <$> native.run before = lower.run (projection before))
    (nextLaw : ∀ value before, Prod.map id projection <$> (nativeNext value).run before = (lowerNext value).run (projection before))
    (before : S) :
    Prod.map id projection <$> (native >>= nativeNext).run before = (lower >>= lowerNext).run (projection before) := by
  simp only [StateT.run_bind, map_bind]
  simp_rw [nextLaw]
  rw [← queryLaw, bind_map_left]
  rfl

private def nativeContinue (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (result : RustM agreement.AgreementEffect) :
    StateT (State n mlSource × PqxdhLiveKemBirth.Pool KemSK) ProbComp (RustM (Option Nat)) :=
  match result with
  | .fail error => pure (.fail error)
  | .div => pure .div
  | .ok (.ServerComplete accepted) => server (RegistrationServerNativeSource.retain created accepted)
  | .ok _ => pure (.ok none)

private def lowerContinue (result : RustM agreement.AgreementEffect) :
    OracleComp (RegistrationNativeKemServerInterface.Spec n mlSource KemSK) (RustM (Option Nat)) :=
  match result with
  | .fail error => pure (.fail error)
  | .div => pure .div
  | .ok (.ServerComplete accepted) => (RegistrationNativeKemServerInterface.Spec n mlSource KemSK).query (.inl (.retain accepted))
  | .ok _ => pure (.ok none)

private theorem continue_source (setup : Setup base KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (verify : MldsaTranscriptAuth.Verify)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (result : RustM agreement.AgreementEffect)
    (before : State n mlSource × PqxdhLiveKemBirth.Pool KemSK) :
    Prod.map id project <$> (nativeContinue created result).run before =
      (simulateQ (source setup codec checks route verify representation created) (lowerContinue result)).run (project before) := by
  cases result with
  | fail error | div => simp only [nativeContinue, lowerContinue, simulateQ_pure, StateT.run_pure, map_pure, Prod.map, id_eq]
  | ok effect =>
      cases effect <;>
        simp only [nativeContinue, lowerContinue, simulateQ_pure, StateT.run_pure, map_pure, Prod.map, id_eq]
      exact retain_source setup codec checks route verify representation created _ before

noncomputable def afterAuthentication (setup : Setup base KemSK) (checks : Checks)
    (authenticated : registration.AuthenticatedInit) :
    OracleComp (RegistrationNativeKemServerInterface.Spec n mlSource KemSK) (RustM (Option Nat)) := do
  let before ← RegistrationNativeKemServerInterface.get
  if before.server.consumed.contains (RegistrationReplaySchedule.identifier authenticated) then pure (.ok none)
  else if checks.reserveRegistration then do
    let completed ← simulateQ (RegistrationNativeKemServerInterface.agreement setup checks)
      (RegistrationReplaySchedule.begin before.server.control authenticated before.server.consumed)
    lowerContinue completed
  else pure (.ok none)

private theorem server_after (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (packet : registration.InitPacket)
    (authenticated : registration.AuthenticatedInit) (before : State n mlSource × PqxdhLiveKemBirth.Pool KemSK) :
    (server (RegistrationServerSdkSource.afterAuthentication setup checks representation created packet authenticated)).run before =
      if before.1.server.consumed.contains (RegistrationReplaySchedule.identifier authenticated) then pure (.ok none, before)
      else if checks.reserveRegistration then
        (server (RegistrationServerNativeSource.agree setup checks representation created packet authenticated) >>= nativeContinue created).run before
      else pure (.ok none, before) := by
  simp only [server, RegistrationServerSdkSource.afterAuthentication, StateT.run]
  split
  · simp only [map_pure]
  · split
    · simp only [StateT.monad_bind_def, StateT.bind, map_bind]
      simp only [server, StateT.run, bind_map_left]
      congr 1
      funext result
      rcases result with ⟨reply, reached⟩
      cases reply with
      | fail error | div => simp only [nativeContinue, StateT.monad_pure_def, StateT.pure, map_pure]
      | ok effect => cases effect <;>
          simp only [nativeContinue, server, StateT.monad_pure_def, StateT.pure, StateT.run, map_pure]
    · simp only [map_pure]

private theorem after_source (setup : Setup base KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (verify : MldsaTranscriptAuth.Verify)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (packet : registration.InitPacket)
    (authenticated : registration.AuthenticatedInit) (before : State n mlSource × PqxdhLiveKemBirth.Pool KemSK) :
    Prod.map id project <$>
        (server (RegistrationServerSdkSource.afterAuthentication setup checks representation created packet authenticated)).run before =
      (simulateQ (source setup codec checks route verify representation created)
        (afterAuthentication setup checks authenticated)).run (project before) := by
  have agreed := bind_project project
    (server (RegistrationServerNativeSource.agree setup checks representation created packet authenticated))
    (simulateQ (source setup codec checks route verify representation created) (begin setup checks authenticated))
    (nativeContinue created) (fun result => simulateQ (source setup codec checks route verify representation created) (lowerContinue result))
    (agree_source setup codec checks route verify representation created packet authenticated)
    (continue_source setup codec checks route verify representation created) before
  simp only [afterAuthentication, simulateQ_bind, StateT.run_bind, get_run, pure_bind]
  rw [server_after]
  by_cases replayed : before.1.server.consumed.contains (RegistrationReplaySchedule.identifier authenticated) = true
  · simp only [replayed, ite_true,
      mask, RegistrationNativeKemServerState.maskServer, simulateQ_pure,
      StateT.monad_pure_def, StateT.pure, StateT.run, map_pure, Prod.map, id_eq, project,
      RegistrationNativeKemWorldUniform.mask_idempotent]
  · by_cases reserved : checks.reserveRegistration = true
    · simp only [begin, simulateQ_bind, StateT.run_bind, get_run, pure_bind] at agreed
      simp only [replayed, Bool.false_eq_true, ite_false,
        reserved, ite_true, mask, RegistrationNativeKemServerState.maskServer,
        project, RegistrationNativeKemWorldUniform.mask_idempotent]
      simpa only [StateT.run_bind, simulateQ_bind, project, mask,
        RegistrationNativeKemServerState.maskServer, RegistrationNativeKemWorldUniform.mask_idempotent] using agreed
    · simp only [replayed, Bool.false_eq_true, ite_false,
        reserved, mask, RegistrationNativeKemServerState.maskServer, simulateQ_pure,
        StateT.monad_pure_def, StateT.pure, StateT.run, map_pure, Prod.map, id_eq, project,
        RegistrationNativeKemWorldUniform.mask_idempotent]

private noncomputable def nativeChecked (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (packet : registration.InitPacket)
    (checked : RustM (List BeaconcryptCore.Refinement.RegistrationAuthenticationFlow.Event × registration.InitAuthentication)) :
    StateT (RegistrationServerFrontendCompiler.State n) ProbComp (RustM (Option Nat)) :=
  match checked with
  | .fail error => pure (.fail error)
  | .div => pure .div
  | .ok (_events, .Accepted authenticated) => RegistrationServerSdkSource.afterAuthentication setup checks representation created packet authenticated
  | .ok _ => pure (.ok none)

private noncomputable def lowerChecked (setup : Setup base KemSK) (checks : Checks)
    (checked : RustM (List BeaconcryptCore.Refinement.RegistrationAuthenticationFlow.Event × registration.InitAuthentication)) :
    OracleComp (RegistrationNativeKemServerInterface.Spec n mlSource KemSK) (RustM (Option Nat)) :=
  match checked with
  | .fail error => pure (.fail error)
  | .div => pure .div
  | .ok (_events, .Accepted authenticated) => afterAuthentication setup checks authenticated
  | .ok _ => pure (.ok none)

private theorem checked_source (setup : Setup base KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (verify : MldsaTranscriptAuth.Verify)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (packet : registration.InitPacket)
    (checked : RustM (List BeaconcryptCore.Refinement.RegistrationAuthenticationFlow.Event × registration.InitAuthentication))
    (before : State n mlSource × PqxdhLiveKemBirth.Pool KemSK) :
    Prod.map id project <$> (server (nativeChecked setup checks representation created packet checked)).run before =
      (simulateQ (source setup codec checks route verify representation created) (lowerChecked setup checks checked)).run (project before) := by
  cases checked with
  | fail error | div =>
      simp only [nativeChecked, lowerChecked, server_pure, StateT.run_pure, map_pure, simulateQ_pure,
        Prod.map, id_eq]
  | ok result =>
      rcases result with ⟨events, result⟩
      cases result <;> first
      | exact after_source setup codec checks route verify representation created packet _ before
      | simp only [nativeChecked, lowerChecked, server_pure, StateT.run_pure, map_pure, simulateQ_pure,
          Prod.map, id_eq]

/-- The literal closed SDK accept, including every authentication, replay, reservation and failed agreement outcome, is implemented by the selected-KEM client with its complete private pool retained. -/
theorem accept_source (setup : Setup base KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (verify : MldsaTranscriptAuth.Verify)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (packet : registration.InitPacket)
    (before : State n mlSource × PqxdhLiveKemBirth.Pool KemSK) :
    Prod.map id project <$> (server (RegistrationServerSdkSource.accept setup codec checks route verify representation created packet)).run before =
      (simulateQ (source setup codec checks route verify representation created)
        (RegistrationNativeKemServerInterface.accept setup checks packet)).run (project before) := by
  have law := bind_project project
    (server (RegistrationServerNativeSource.authenticate setup codec route verify created packet))
    (simulateQ (source setup codec checks route verify representation created)
      ((RegistrationNativeKemServerInterface.Spec n mlSource KemSK).query (.inl (.authenticate packet)) :
        OracleComp (RegistrationNativeKemServerInterface.Spec n mlSource KemSK)
          (RustM (List BeaconcryptCore.Refinement.RegistrationAuthenticationFlow.Event × registration.InitAuthentication))))
    (fun checked => server (nativeChecked setup checks representation created packet checked))
    (fun checked => simulateQ (source setup codec checks route verify representation created) (lowerChecked setup checks checked))
    (authenticate_source setup codec checks route verify representation created packet)
    (checked_source setup codec checks route verify representation created packet) before
  have nativeEq : RegistrationServerSdkSource.accept (n := n) setup codec checks route verify representation created packet =
      (RegistrationServerNativeSource.authenticate setup codec route verify created packet >>=
        nativeChecked setup checks representation created packet) := rfl
  have lowerEq : RegistrationNativeKemServerInterface.accept (n := n) (mlSource := mlSource) setup checks packet =
      (((RegistrationNativeKemServerInterface.Spec n mlSource KemSK).query (.inl (.authenticate packet)) :
        OracleComp (RegistrationNativeKemServerInterface.Spec n mlSource KemSK)
          (RustM (List BeaconcryptCore.Refinement.RegistrationAuthenticationFlow.Event × registration.InitAuthentication))) >>=
        lowerChecked setup checks) := by
    unfold RegistrationNativeKemServerInterface.accept lowerChecked afterAuthentication lowerContinue
    apply congrArg (fun next :
        RustM (List BeaconcryptCore.Refinement.RegistrationAuthenticationFlow.Event × registration.InitAuthentication) →
          OracleComp (RegistrationNativeKemServerInterface.Spec n mlSource KemSK) (RustM (Option Nat)) =>
      ((RegistrationNativeKemServerInterface.Spec n mlSource KemSK).query (.inl (.authenticate packet)) :
        OracleComp (RegistrationNativeKemServerInterface.Spec n mlSource KemSK)
          (RustM (List BeaconcryptCore.Refinement.RegistrationAuthenticationFlow.Event × registration.InitAuthentication))) >>= next)
    funext checked
    cases checked with
    | fail error | div => rfl
    | ok result => rcases result with ⟨events, result⟩; cases result <;> rfl
  rw [nativeEq, server_bind, lowerEq, simulateQ_bind]
  exact law

end BeaconcryptCore.Computational.RegistrationNativeKemSdkCompiler

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemSdkCompiler.agree_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemSdkCompiler.agree_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemSdkCompiler.accept_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemSdkCompiler.accept_source
