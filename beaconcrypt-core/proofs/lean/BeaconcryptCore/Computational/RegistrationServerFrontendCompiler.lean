-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationServerRootCompiler

/-! The adaptive Server client owns its replay set and one-use session table. Its executable state omits the selected identity seed and the private root-family state. All ordinary operations use the actual native frontend programs, while agreement calls the proved public root compiler. The private source interpretation restores only the original immutable constructor and root-family instrumentation. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationServerFrontendCompiler
open PqxdhServerAuthExperiment (Setup Codec Checks)
open RegistrationServerRootCompiler (Local Family)
open PqxdhJointDhExtractRoot (RootSpec)
variable {ι KemSK Reader Response Encoded : Type} {base : OracleSpec ι} {n : Nat}

/-- Neither selected identity seed nor family cache is a field in the reduction's executable state. Session roots are opaque oracle replies retained only by the native one-use capability. -/
structure State (n : Nat) where
  control : pqxdh.ServerState
  pin : session.ServerAuthenticationPin
  consumed : RegistrationReplaySchedule.State
  sessions : List (Option peer.ConsumedRegistration)
  world : Local n

def erase (state : RegistrationWorldServerFrontend.State n RegistrationServerRoleBackend.State) : State n :=
  ⟨state.control, state.pin, state.consumed, state.sessions, state.global.2⟩

def restore (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (state : Family × State n) :
    RegistrationWorldServerFrontend.State n RegistrationServerRoleBackend.State :=
  ⟨created, state.2.control, state.2.pin, state.2.consumed, state.2.sessions, (state.1, state.2.world)⟩

def withWorld (state : State n) (world : Local n) : State n := { state with world := world }

def world {Value : Type} (work : StateT (Local n) (OracleComp RootSpec) Value) :
    StateT (State n) (OracleComp RootSpec) Value := fun before =>
  (fun result => (result.1, withWorld before result.2)) <$> work.run before.world

noncomputable def authenticate (setup : Setup base KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (verify : MldsaTranscriptAuth.Verify)
    (packet : registration.InitPacket) : StateT (State n) (OracleComp RootSpec)
      (RustM (List BeaconcryptCore.Refinement.RegistrationAuthenticationFlow.Event × registration.InitAuthentication)) :=
  RegistrationServerRootCompiler.liftProb fun before =>
    (fun result => (result.1, { before with world := { before.world with world := (result.2, before.world.world.2) } })) <$>
      (RegistrationWorldAuthentication.begin setup codec route verify before.pin packet).run before.world.world.1

/-- Private replay lookup is performed before the actual seed-free root request client. -/
noncomputable def agree (setup : Setup base KemSK) (checks : Checks)
    (packet : registration.InitPacket) (authenticated : registration.AuthenticatedInit) :
    StateT (State n) (OracleComp RootSpec) (RustM agreement.AgreementEffect) := fun before =>
  if before.consumed.contains (RegistrationReplaySchedule.identifier authenticated) then
    pure (.ok (.Rejected .None), before)
  else (world (RegistrationServerRootCompiler.worldStage setup checks setup.serverDomain packet authenticated)).run before

/-- Literal native insertion stores the complete consumed token before returning the new public handle. -/
def retain (accepted : agreement.ServerAgreement) : StateT (State n) (OracleComp RootSpec) (RustM (Option Nat)) :=
  fun before => match RegistrationReplaySchedule.consume accepted before.consumed with
  | .fail error => pure (.fail error, before)
  | .div => pure (.div, before)
  | .ok (.None, history) => pure (.ok none, { before with consumed := history })
  | .ok (.Some consumed, history) => pure (.ok (some before.sessions.length),
      { before with consumed := history, sessions := before.sessions ++ [some consumed] })

noncomputable def accept (setup : Setup base KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (verify : MldsaTranscriptAuth.Verify)
    (packet : registration.InitPacket) : StateT (State n) (OracleComp RootSpec) (RustM (Option Nat)) := do
  let checked ← authenticate setup codec route verify packet
  match checked with
  | .fail error => pure (.fail error)
  | .div => pure .div
  | .ok (_events, .Accepted authenticated) =>
      let completed ← agree setup checks packet authenticated
      match completed with
      | .fail error => pure (.fail error)
      | .div => pure .div
      | .ok (.ServerComplete accepted) => retain accepted
      | .ok _ => pure (.ok none)
  | .ok _ => pure (.ok none)

def take (handle : Nat) : StateT (State n) (OracleComp RootSpec) (Option peer.ConsumedRegistration) := fun before =>
  match before.sessions[handle]? with
  | none => pure (none, before)
  | some none => pure (none, before)
  | some (some consumed) => pure (some consumed, { before with sessions := before.sessions.set handle none })

noncomputable def complete (setup : Setup base KemSK) (codec : Codec Reader Response)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (encode : registration.SignedResponseView → core.option.Option Encoded)
    (consumed : peer.ConsumedRegistration) (application : Slice U8) :
    StateT (State n) (OracleComp RootSpec) (RustM (Option (Std.U64 × Encoded))) :=
  RegistrationServerRootCompiler.liftProb fun before => do
    let result ← (RegistrationWorldServerCompletion.server setup codec sign encode before.control before.pin consumed application).run
      before.world
    let current := { before with world := result.2 }
    match result.1 with
    | .fail error => pure (.fail error, current)
    | .div => pure (.div, current)
    | .ok (.Err previous) => pure (.ok none, { current with control := previous })
    | .ok (.Ok published) => pure (.ok (some (published.key_id, published.encoded)),
        { current with control := published.control })

noncomputable def build (setup : Setup base KemSK) (codec : Codec Reader Response)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (encode : registration.SignedResponseView → core.option.Option Encoded)
    (handle : Nat) (application : Slice U8) :
    StateT (State n) (OracleComp RootSpec) (RustM (Option (Std.U64 × Encoded))) := do
  let consumed ← take handle
  match consumed with
  | none => pure (.ok none)
  | some consumed => do
      let current ← get
      if RegistrationWorldServerFrontend.responseAdmitted current.control application then
        complete setup codec sign encode consumed application
      else pure (.ok none)

private theorem map_state_apply {S X Y : Type} (f : X → Y) (work : StateT S ProbComp X)
    (before : S) : (f <$> work) before = Prod.map f id <$> work before := by
  change (work before >>= fun result => pure (f result.1, result.2)) = _
  simp only [bind_pure_comp]
  rfl

/-- Restoring an immutable private constructor and family state exactly inverts executable-state erasure. -/
theorem restore_erase (state : RegistrationWorldServerFrontend.State n RegistrationServerRoleBackend.State) :
    restore state.created (state.global.1, erase state) = state := rfl

/-- Actual attached Ed Init authentication, all failed gates, cache effects and prior receipts are identical. -/
theorem authenticate_native (setup : Setup base KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (verify : MldsaTranscriptAuth.Verify)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (scalar : PqxdhJointGapDh.ScalarBytes)
    (packet : registration.InitPacket) (before : Family × State n) :
    Prod.map id (restore created) <$>
      (RegistrationServerRootCompiler.interpret (RegistrationServerRootCompiler.family setup.hmac setup.joint setup.dh created.seed scalar)
        (authenticate setup codec route verify packet)).run before =
      (RegistrationWorldServerFrontend.authenticate setup codec route verify packet).run (restore created before) := by
  rw [authenticate, RegistrationServerRootCompiler.liftProb_exact]
  simp only [RegistrationRootStage.lift, StateT.run, Functor.map_map,
    restore, Prod.map, id_eq]
  rfl

/-- Actual owned replay lookup and complete real-family agreement preserve the entire private family and populated native state. -/
theorem agree_native (setup : Setup base KemSK) (checks : Checks)
    (correct : PqxdhSecretInputKdf.SourceRootCorrect setup.source setup.hmac)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (scalar : PqxdhJointGapDh.ScalarBytes)
    (packet : registration.InitPacket) (authenticated : registration.AuthenticatedInit) (before : Family × State n) :
    Prod.map id (restore created) <$>
      (RegistrationServerRootCompiler.interpret (RegistrationServerRootCompiler.family setup.hmac setup.joint setup.dh created.seed scalar)
        (agree setup checks packet authenticated)).run before =
      (RegistrationWorldServerFrontend.agree setup correct scalar (RegistrationServerRoleBackend.localBackend setup checks)
        packet authenticated).run (restore created before) := by
  by_cases consumed : before.2.consumed.contains (RegistrationReplaySchedule.identifier authenticated) = true
  · simp only [RegistrationServerRootCompiler.interpret, agree, StateT.run, consumed, ite_true,
      simulateQ_pure, map_pure, RegistrationWorldServerFrontend.agree,
      RegistrationWorldServerReplay.agreement, restore]
    rfl
  · have exactWorld := congrFun (RegistrationServerRootCompiler.world_exact (n := n) setup checks setup.serverDomain
      setup.hmac setup.dh created.seed scalar packet authenticated) (before.1, before.2.world)
    have mapped := congrArg (fun work =>
      (fun result => (result.1, restore created (result.2.1, withWorld before.2 result.2.2))) <$> work) exactWorld
    simpa only [RegistrationServerRootCompiler.interpret, agree, world, StateT.run,
      consumed, Bool.false_eq_true, ite_false, simulateQ_map, map_state_apply, Functor.map_map,
      RegistrationWorldServerFrontend.agree, RegistrationWorldServerReplay.agreement,
      RegistrationWorldServerFrontend.parameters, restore, withWorld, Prod.map, id_eq, Prod.mk.eta] using mapped

/-- Consumption precedes later work and retains every actual native rejection outcome. -/
theorem retain_native (setup : Setup base KemSK) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (scalar : PqxdhJointGapDh.ScalarBytes) (accepted : agreement.ServerAgreement) (before : Family × State n) :
    Prod.map id (restore created) <$>
      (RegistrationServerRootCompiler.interpret (RegistrationServerRootCompiler.family setup.hmac setup.joint setup.dh created.seed scalar)
        (retain accepted)).run before =
      (RegistrationWorldServerFrontend.retain accepted).run (restore created before) := by
  simp only [RegistrationServerRootCompiler.interpret, retain, RegistrationWorldServerFrontend.retain,
    StateT.run, restore]
  cases actual : RegistrationReplaySchedule.consume accepted before.2.consumed with
  | fail error => simp only [simulateQ_pure, ]; rfl
  | div => simp only [simulateQ_pure, ]; rfl
  | ok result => cases result with
    | mk option history => cases option <;> simp only [simulateQ_pure, ] <;> rfl

private theorem pure_native {Value : Type} (family : QueryImpl RootSpec (StateT Family ProbComp))
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (value : Value) (before : Family × State n) :
    Prod.map id (restore created) <$>
      (RegistrationServerRootCompiler.interpret family (pure value)).run before =
      pure (value, restore created before) := by
  rw [RegistrationServerRootCompiler.interpret_pure]
  simp only [StateT.run_pure, map_pure, Prod.map, id_eq]

private theorem bind_native {Value Result : Type} (family : QueryImpl RootSpec (StateT Family ProbComp))
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (work : StateT (State n) (OracleComp RootSpec) Value)
    (native : StateT (RegistrationWorldServerFrontend.State n RegistrationServerRoleBackend.State) ProbComp Value)
    (next : Value → StateT (State n) (OracleComp RootSpec) Result)
    (nativeNext : Value → StateT (RegistrationWorldServerFrontend.State n RegistrationServerRoleBackend.State) ProbComp Result)
    (first : ∀ before, Prod.map id (restore created) <$>
      (RegistrationServerRootCompiler.interpret family work).run before = native.run (restore created before))
    (rest : ∀ value before, Prod.map id (restore created) <$>
      (RegistrationServerRootCompiler.interpret family (next value)).run before =
        (nativeNext value).run (restore created before)) (before : Family × State n) :
    Prod.map id (restore created) <$>
      (RegistrationServerRootCompiler.interpret family (work >>= next)).run before =
      (native >>= nativeNext).run (restore created before) := by
  rw [RegistrationServerRootCompiler.interpret_bind, StateT.run_bind, StateT.run_bind, map_bind,
    ← first before, bind_map_left]
  apply congrArg (fun continuation =>
    (RegistrationServerRootCompiler.interpret family work).run before >>= continuation)
  funext result
  exact rest result.1 result.2

/-- The whole actual Ed-authenticated accept path, including owned replay insertion before every build, is the concrete open-root client. -/
theorem accept_native (setup : Setup base KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (verify : MldsaTranscriptAuth.Verify)
    (correct : PqxdhSecretInputKdf.SourceRootCorrect setup.source setup.hmac)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (scalar : PqxdhJointGapDh.ScalarBytes)
    (packet : registration.InitPacket) (before : Family × State n) :
    Prod.map id (restore created) <$>
      (RegistrationServerRootCompiler.interpret (RegistrationServerRootCompiler.family setup.hmac setup.joint setup.dh created.seed scalar)
        (accept setup codec checks route verify packet)).run before =
      (RegistrationWorldServerFrontend.accept setup codec route verify correct scalar
        (RegistrationServerRoleBackend.localBackend setup checks) packet).run (restore created before) := by
  unfold accept RegistrationWorldServerFrontend.accept
  apply bind_native _ created _ _ _ _ (authenticate_native setup codec route verify created scalar packet)
  intro checked current
  cases checked with
  | fail error => exact pure_native _ _ _ _
  | div => exact pure_native _ _ _ _
  | ok checked =>
      rcases checked with ⟨events, checked⟩
      cases checked <;> try exact pure_native _ _ _ _
      apply bind_native _ created _ _ _ _ (agree_native setup checks correct created scalar packet _)
      intro completed after
      cases completed with
      | fail error => exact pure_native _ _ _ _
      | div => exact pure_native _ _ _ _
      | ok effect =>
          cases effect <;> first
            | exact pure_native _ _ _ _
            | exact retain_native setup created scalar _ after

/-- Native response publication and the generated real kernel retain exactly the same World/cache/signing effects through every failure. -/
theorem complete_native (setup : Setup base KemSK) (codec : Codec Reader Response)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (encode : registration.SignedResponseView → core.option.Option Encoded)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (scalar : PqxdhJointGapDh.ScalarBytes)
    (consumed : peer.ConsumedRegistration) (application : Slice U8) (before : Family × State n) :
    Prod.map id (restore created) <$>
      (RegistrationServerRootCompiler.interpret (RegistrationServerRootCompiler.family setup.hmac setup.joint setup.dh created.seed scalar)
        (complete setup codec sign encode consumed application)).run before =
      (RegistrationWorldServerFrontend.complete setup codec sign encode consumed application).run (restore created before) := by
  rw [complete, RegistrationServerRootCompiler.liftProb_exact]
  simp only [RegistrationRootStage.lift, RegistrationWorldServerFrontend.complete,
    RegistrationWorldServerCompletion.global, restore, StateT.run,
    bind_map_left, map_bind, Functor.map_map, Prod.map, id_eq]
  apply congrArg (fun continuation =>
    (RegistrationWorldServerCompletion.server setup codec sign encode before.2.control before.2.pin consumed application).run
      before.2.world >>= continuation)
  funext result
  rcases result with ⟨result, after⟩
  cases result with
  | fail error => rfl
  | div => rfl
  | ok result => cases result <;> rfl

/-- Taking a session capability before admission is part of the compiled native program. -/
theorem take_native (setup : Setup base KemSK) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (scalar : PqxdhJointGapDh.ScalarBytes) (handle : Nat) (before : Family × State n) :
    Prod.map id (restore created) <$>
      (RegistrationServerRootCompiler.interpret (RegistrationServerRootCompiler.family setup.hmac setup.joint setup.dh created.seed scalar)
        (take handle)).run before =
      (RegistrationWorldServerFrontend.take handle).run (restore created before) := by
  simp only [RegistrationServerRootCompiler.interpret, take, RegistrationWorldServerFrontend.take,
    StateT.run, restore]
  cases actual : before.2.sessions[handle]? with
  | none => simp only [simulateQ_pure, ]; rfl
  | some option => cases option <;> simp only [simulateQ_pure, ] <;> rfl

private theorem get_bind {S Value : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (next : S → StateT S m Value) : (get >>= next) = fun before => (next before).run before := by
  funext before
  change ((pure (before, before) : m (S × S)) >>= fun current => (next current.1).run current.2) = _
  rw [pure_bind]

/-- Actual full-size preflight, pin/allocator checks, all64/76/signature/encoder failures, and session consumption are retained by the open client. -/
theorem build_native (setup : Setup base KemSK) (codec : Codec Reader Response)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (encode : registration.SignedResponseView → core.option.Option Encoded)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (scalar : PqxdhJointGapDh.ScalarBytes)
    (handle : Nat) (application : Slice U8) (before : Family × State n) :
    Prod.map id (restore created) <$>
      (RegistrationServerRootCompiler.interpret (RegistrationServerRootCompiler.family setup.hmac setup.joint setup.dh created.seed scalar)
        (build setup codec sign encode handle application)).run before =
      (RegistrationWorldServerFrontend.build setup codec sign encode handle application).run (restore created before) := by
  unfold build RegistrationWorldServerFrontend.build
  apply bind_native _ created _ _ _ _ (take_native setup created scalar handle)
  intro option current
  cases option with
  | none => exact pure_native _ _ _ _
  | some consumed =>
      by_cases admitted : RegistrationWorldServerFrontend.responseAdmitted current.2.control application = true
      · simpa only [get_bind, RegistrationServerRootCompiler.interpret, StateT.run, restore,
          admitted, ite_true] using complete_native setup codec sign encode created scalar consumed application current
      · simpa only [get_bind, RegistrationServerRootCompiler.interpret, StateT.run, restore,
          admitted, Bool.false_eq_true, ite_false, StateT.monad_pure_def, StateT.pure] using
          (pure_native (RegistrationServerRootCompiler.family setup.hmac setup.joint setup.dh created.seed scalar)
            created (.ok none : RustM (Option (Std.U64 × Encoded))) current)

end BeaconcryptCore.Computational.RegistrationServerFrontendCompiler

/-- info: 'BeaconcryptCore.Computational.RegistrationServerFrontendCompiler.restore_erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationServerFrontendCompiler.restore_erase

/-- info: 'BeaconcryptCore.Computational.RegistrationServerFrontendCompiler.authenticate_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationServerFrontendCompiler.authenticate_native

/-- info: 'BeaconcryptCore.Computational.RegistrationServerFrontendCompiler.agree_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationServerFrontendCompiler.agree_native

/-- info: 'BeaconcryptCore.Computational.RegistrationServerFrontendCompiler.retain_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationServerFrontendCompiler.retain_native

/-- info: 'BeaconcryptCore.Computational.RegistrationServerFrontendCompiler.accept_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationServerFrontendCompiler.accept_native

/-- info: 'BeaconcryptCore.Computational.RegistrationServerFrontendCompiler.complete_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationServerFrontendCompiler.complete_native

/-- info: 'BeaconcryptCore.Computational.RegistrationServerFrontendCompiler.take_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationServerFrontendCompiler.take_native

/-- info: 'BeaconcryptCore.Computational.RegistrationServerFrontendCompiler.build_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationServerFrontendCompiler.build_native
