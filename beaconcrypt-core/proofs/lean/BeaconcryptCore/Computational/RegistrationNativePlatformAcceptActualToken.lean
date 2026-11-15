-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformAcceptActualRoot
import BeaconcryptCore.Computational.RegistrationNativeTokenSource
import BeaconcryptCore.Computational.RegistrationNativePlatformHashReceipt

/-! The retained token is associated with the actual evaluated Root collector at the precise source insertion cut. Stateful reservations change only the external platform, and every retained session is either an old table entry or that actual consumed agreement. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformAcceptActualToken
open PqxdhServerAuthExperiment (Setup Checks Codec)
open RegistrationNativeKemServerState (State)
open RegistrationNativeKemCountedServerTrace (Log)
open RegistrationNativePlatformKemCountedAccept
open RegistrationNativePlatformAcceptActualRoot (Cut CheckedCut)
open PqxdhLiveKemBirth (Pool)
variable {n : Nat} {ι KemSK Platform Value Next Reader Response : Type} {base : OracleSpec ι}
variable {source : RegistrationNativeMldsa.Source}
local notation "CP" => RegistrationNativeKemCountedProgram.Spec KemSK
local notation "Client" => State n source
local notation "Front" => RegistrationServerFrontendCompiler.State n
local notation "M" => RegistrationNativePlatformKemCountedProgram.M KemSK Platform

private def flat (work : StateT Client M Value) (before : Client) (previous : Platform) := (work.run before).run previous
private noncomputable def eval (setup : Setup base KemSK) (work : StateT Client M Value)
    (before : Client) (previous : Platform) (pool : Pool KemSK) :=
  RegistrationNativeKemCountedProgram.evaluate setup.baseImpl setup.kem (flat work before previous).withQueryLog pool

private theorem evaluate_bind {A B : Type} (setup : Setup base KemSK)
    (work : OracleComp CP A) (next : A → OracleComp CP B) (pool : Pool KemSK) :
    RegistrationNativeKemCountedProgram.evaluate setup.baseImpl setup.kem (work >>= next) pool = (do
      let result ← RegistrationNativeKemCountedProgram.evaluate setup.baseImpl setup.kem work pool
      RegistrationNativeKemCountedProgram.evaluate setup.baseImpl setup.kem (next result.1) result.2) := by
  simp only [RegistrationNativeKemCountedProgram.evaluate, simulateQ_bind, StateT.run_bind]

private theorem evaluate_map {A B : Type} (setup : Setup base KemSK) (function : A → B) (work : OracleComp CP A) (pool : Pool KemSK) :
    RegistrationNativeKemCountedProgram.evaluate setup.baseImpl setup.kem (function <$> work) pool =
      Prod.map function id <$> RegistrationNativeKemCountedProgram.evaluate setup.baseImpl setup.kem work pool := by
  simp only [RegistrationNativeKemCountedProgram.evaluate, simulateQ_map, StateT.run_map]
  rfl

private theorem bind_cut (setup : Setup base KemSK) (work : StateT Client M Value) (next : Value → StateT Client M Next)
    (before : Client) (previous : Platform) (result : (Next × Client) × Platform) (log : Log KemSK)
    (beforePool afterPool : Pool KemSK)
    (supported : ((result, log), afterPool) ∈ support (eval setup (work >>= next) before previous beforePool)) :
    ∃ (first : (Value × Client) × Platform) (prefixLog suffixLog : Log KemSK) (middlePool : Pool KemSK),
      ((first, prefixLog), middlePool) ∈ support (eval setup work before previous beforePool) ∧
      ((result, suffixLog), afterPool) ∈ support (eval setup (next first.1.1) first.1.2 first.2 middlePool) ∧
      log = prefixLog ++ suffixLog := by
  simp only [eval, flat, StateT.run_bind, withQueryLog_bind, evaluate_bind, evaluate_map,
    mem_support_bind_iff, support_map] at supported
  obtain ⟨⟨⟨first, prefixLog⟩, middlePool⟩, head, ⟨⟨last, suffixLog⟩, finalPool⟩, tail, returned⟩ := supported
  simp only [Prod.map, id_eq, Prod.mk.injEq] at returned
  rcases returned with ⟨⟨rfl, rfl⟩, rfl⟩
  exact ⟨first, prefixLog, suffixLog, middlePool, head, tail, rfl⟩

private theorem pure_success (setup : Setup base KemSK) (value : RustM (Option Nat)) (before : Client) (previous : Platform)
    (handle : Nat) (after : Client) (finalPlatform : Platform) (log : Log KemSK) (beforePool afterPool : Pool KemSK)
    (supported : ((((.ok (some handle), after), finalPlatform), log), afterPool) ∈ support
      (eval setup (pure value) before previous beforePool)) : value = .ok (some handle) := by
  simp only [eval, flat, StateT.run_pure, withQueryLog_pure, RegistrationNativeKemCountedProgram.evaluate,
    simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at supported
  exact supported.1.1.1.1.symm

private theorem inject_run (work : StateT Client (OracleComp CP) Value) (before : Client) (previous : Platform) :
    flat (RegistrationNativePlatformKemCountedProgram.inject work) before previous =
      (fun result => (result, previous)) <$> work.run before := by
  change (work.run before >>= fun result => pure (result, previous)) = _
  exact bind_pure_comp _ _

private theorem logged_support (setup : Setup base KemSK) (work : StateT Client M Value)
    (before after : Client) (previous finalPlatform : Platform) (value : Value)
    (log : Log KemSK) (beforePool afterPool : Pool KemSK)
    (supported : ((((value, after), finalPlatform), log), afterPool) ∈ support (eval setup work before previous beforePool)) :
    (((value, after), finalPlatform), afterPool) ∈ support
      (RegistrationNativePlatformKemCountedProgram.runState setup work before previous beforePool) := by
  have law := congrArg (fun program => RegistrationNativeKemCountedProgram.evaluate setup.baseImpl setup.kem program beforePool)
    (loggingOracle.fst_map_run_simulateQ (flat work before previous))
  simp only [RegistrationNativeKemCountedProgram.evaluate, simulateQ_map, StateT.run_map] at law
  unfold eval at supported
  unfold RegistrationNativePlatformKemCountedProgram.runState RegistrationNativeKemCountedProgram.evaluate
  unfold flat at law supported
  rw [← law, support_map]
  exact ⟨_, supported, rfl⟩

private theorem map_apply {S A B : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (function : A → B) (work : StateT S m A) (before : S) :
    (function <$> work) before = Prod.map function id <$> work before := StateT.run_map function work before

private theorem server_run (setup : Setup base KemSK) (work : StateT Front M Value)
    (before : Client) (previous : Platform) (pool : Pool KemSK) :
    RegistrationNativePlatformKemCountedProgram.runState setup (server work) before previous pool =
      (fun result => (((result.1.1.1, { before with server := result.1.1.2 }), result.1.2), result.2)) <$>
        RegistrationNativePlatformKemCountedProgram.runState setup work before.server previous pool := by
  simp only [RegistrationNativePlatformKemCountedProgram.runState, server, StateT.run, map_apply,
    RegistrationNativeKemCountedProgram.evaluate, simulateQ_map]
  rfl

private theorem ordinary_server_run (setup : Setup base KemSK) (work : StateT Front (StateT Platform ProbComp) Value)
    (before : Client) (previous : Platform) (pool : Pool KemSK) :
    RegistrationNativePlatformKemCountedProgram.runState setup (ordinaryServer work) before previous pool =
      (fun result => (((result.1.1, { before with server := result.1.2 }), result.2), pool)) <$> ((work.run before.server).run previous) := by
  rw [ordinaryServer, server_run, RegistrationNativePlatformKemCountedProgram.run_lift, Functor.map_map]

private theorem ordinary_support (setup : Setup base KemSK) (work : StateT Front (StateT Platform ProbComp) Value)
    (before after : Client) (previous finalPlatform : Platform) (value : Value)
    (log : Log KemSK) (beforePool afterPool : Pool KemSK)
    (supported : ((((value, after), finalPlatform), log), afterPool) ∈ support
      (eval setup (ordinaryServer work) before previous beforePool)) :
    ((value, after.server), finalPlatform) ∈ support ((work.run before.server).run previous) := by
  have actual := logged_support setup (ordinaryServer work) before after previous finalPlatform value log beforePool afterPool supported
  rw [ordinary_server_run, support_map] at actual
  obtain ⟨⟨⟨reply, front⟩, platform⟩, called, same⟩ := actual
  have valueEq := congrArg (fun result => result.1.1.1) same
  have stateEq := congrArg (fun result => result.1.1.2.server) same
  have platformEq := congrArg (fun result => result.1.2) same
  change reply = value at valueEq
  change front = after.server at stateEq
  change platform = finalPlatform at platformEq
  rw [valueEq, stateEq, platformEq] at called
  exact called

private theorem reserved_state (setup : Setup base KemSK) (reserve : StateT Platform ProbComp Bool)
    (before after : Client) (previous finalPlatform : Platform) (allowed : Bool)
    (log : Log KemSK) (beforePool afterPool : Pool KemSK)
    (supported : ((((allowed, after), finalPlatform), log), afterPool) ∈ support
      (eval setup (ordinaryServer (StateT.lift reserve)) before previous beforePool)) : after = before := by
  have actual := logged_support setup (ordinaryServer (StateT.lift reserve)) before after previous finalPlatform allowed log beforePool afterPool supported
  rw [ordinary_server_run] at actual
  simp only [StateT.run_lift, bind_pure_comp, StateT.run_map, Functor.map_map] at actual
  change (((allowed, after), finalPlatform), afterPool) ∈ support
    ((fun result : Bool × Platform => (((result.1, before), result.2), beforePool)) <$> (reserve.run previous)) at actual
  rw [support_map] at actual
  obtain ⟨⟨value, platform⟩, _called, same⟩ := actual
  exact (congrArg (fun result => result.1.1.2) same).symm

/-- Actual successful replay/reservation/agreement/retention supplies a genuine native collector receipt and its actual same-log encapsulation reply. -/
theorem afterAuthentication (setup : Setup base KemSK) (checks : Checks)
    (reserve : StateT Platform ProbComp Bool)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (packet : registration.InitPacket)
    (authenticated : registration.AuthenticatedInit) (before after : Client) (previous finalPlatform : Platform)
    (handle : Nat) (log : Log KemSK) (beforePool afterPool : Pool KemSK)
    (supported : ((((.ok (some handle), after), finalPlatform), log), afterPool) ∈ support
      (eval setup (RegistrationNativePlatformKemCountedAccept.afterAuthentication setup checks (StateT.lift reserve) representation created packet authenticated)
        before previous beforePool)) :
    ∃ receipt : Cut setup checks representation created packet authenticated handle after finalPlatform log, receipt.beforeAgreement = before := by
  change ((((.ok (some handle), after), finalPlatform), log), afterPool) ∈ support
    (eval setup (if before.server.consumed.contains (RegistrationReplaySchedule.identifier authenticated) then pure (.ok none)
      else do
        let admitted ← ordinaryServer (StateT.lift reserve)
        if admitted then do
          let completed ← RegistrationNativePlatformKemCountedProgram.inject
            (RegistrationNativeKemCountedServerPrimitive.agree setup checks representation created authenticated)
          match completed with
          | .fail error => pure (.fail error)
          | .div => pure .div
          | .ok (.ServerComplete accepted) => ordinaryServer (RegistrationNativePlatformServerSdk.liftNative RegistrationNativePlatformMldsaProgram.coins (RegistrationServerNativeSource.retain created accepted))
          | .ok _ => pure (.ok none)
        else pure (.ok none)) before previous beforePool) at supported
  split at supported
  · cases pure_success setup (.ok none) before previous handle after finalPlatform log beforePool afterPool supported
  · obtain ⟨⟨⟨allowed, reserved⟩, reservedPlatform⟩, prefixLog, laterLog, reservedPool, reservedEffect, later, full⟩ :=
      bind_cut setup (ordinaryServer (StateT.lift reserve)) _ before previous _ log beforePool afterPool supported
    have reservedEq := reserved_state setup reserve before reserved previous reservedPlatform allowed prefixLog beforePool reservedPool reservedEffect
    subst reserved
    cases allowed with
    | false =>
      simp only [Bool.false_eq_true, ite_false] at later
      cases pure_success setup (.ok none) before reservedPlatform handle after finalPlatform laterLog reservedPool afterPool later
    | true =>
      simp only [ite_true] at later
      obtain ⟨⟨⟨effect, agreed⟩, agreedPlatform⟩, agreementLog, retainLog, agreementPool, actualAgree, retained, splitLog⟩ :=
        bind_cut setup (RegistrationNativePlatformKemCountedProgram.inject
          (RegistrationNativeKemCountedServerPrimitive.agree setup checks representation created authenticated))
          _ before reservedPlatform _ laterLog reservedPool afterPool later
      simp only [eval] at actualAgree
      rw [inject_run, RegistrationAgreementMacroTrace.logging_map, evaluate_map, support_map] at actualAgree
      obtain ⟨⟨⟨⟨actualEffect, actualAgreed⟩, actualLog⟩, actualPool⟩, ran, same⟩ := actualAgree
      simp only [Prod.map, id_eq, Prod.mk.injEq] at same
      rcases same with ⟨⟨⟨⟨rfl, rfl⟩, rfl⟩, rfl⟩, rfl⟩
      cases actualEffect with
      | fail error => cases pure_success setup (.fail error) actualAgreed reservedPlatform handle after finalPlatform retainLog actualPool afterPool retained
      | div => cases pure_success setup .div actualAgreed reservedPlatform handle after finalPlatform retainLog actualPool afterPool retained
      | ok answer =>
        cases answer <;> try {
          cases pure_success setup (.ok none) actualAgreed reservedPlatform handle after finalPlatform retainLog actualPool afterPool retained }
        case ServerComplete accepted =>
          obtain ⟨root⟩ := RegistrationNativeKemTracedServerSource.agree setup checks representation created packet authenticated accepted
            before actualAgreed reservedPool actualPool actualLog ran
          have sameLog : log = prefixLog ++ actualLog ++ retainLog := by rw [full, splitLog, List.append_assoc]
          rw [sameLog]
          exact ⟨⟨before, actualAgreed, reservedPlatform, accepted, actualLog, retainLog, reservedPool, actualPool, afterPool,
            ran, retained, { root with encapsulated := List.mem_append_left _ (List.mem_append_right _ root.encapsulated) }⟩, rfl⟩



attribute [local irreducible] RegistrationNativePlatformSourceAccept.authenticate
  RegistrationNativePlatformSourceBuild.pin RegistrationNativePlatformServerSdk.liftNative

private theorem auth_sessions (setup : Setup base KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (pin : session.ServerAuthenticationPin) (packet : registration.InitPacket)
    (before after : Client) (previous finalPlatform : Platform)
    (reply : RustM (List BeaconcryptCore.Refinement.RegistrationAuthenticationFlow.Event × registration.InitAuthentication))
    (log : Log KemSK) (beforePool afterPool : Pool KemSK)
    (supported : ((((reply, after), finalPlatform), log), afterPool) ∈ support
      (eval setup (ordinaryServer (RegistrationNativePlatformSourceAccept.authenticate RegistrationNativePlatformMldsaProgram.coins setup codec route source.verify pin packet))
        before previous beforePool)) : after.server.sessions = before.server.sessions := by
  have actual := ordinary_support setup _ before after previous finalPlatform reply log beforePool afterPool supported
  simp only [RegistrationNativePlatformSourceAccept.authenticate, StateT.run, map_apply, support_map] at actual
  obtain ⟨inner, _called, same⟩ := actual
  exact (congrArg (fun value => value.1.2.sessions) same).symm

private theorem pin_sessions (setup : Setup base KemSK) (before after : Client) (previous finalPlatform : Platform)
    (reply : RustM (core.option.Option session.ServerAuthenticationPin))
    (log : Log KemSK) (beforePool afterPool : Pool KemSK)
    (supported : ((((reply, after), finalPlatform), log), afterPool) ∈ support
      (eval setup (ordinaryServer (RegistrationNativePlatformSourceBuild.pin RegistrationNativePlatformMldsaProgram.coins)) before previous beforePool)) :
    after.server.sessions = before.server.sessions := by
  have actual := ordinary_support setup _ before after previous finalPlatform reply log beforePool afterPool supported
  simp only [RegistrationNativePlatformSourceBuild.pin, StateT.run, map_apply, support_map] at actual
  obtain ⟨inner, _called, same⟩ := actual
  exact (congrArg (fun value => value.1.2.sessions) same).symm


/-- The actual post-pin accept names a Root cut whose prior token table is exactly the table before mandatory authentication. -/
theorem afterPin (setup : Setup base KemSK) (codec : Codec Reader Response) (checks : Checks)
    (reserve : StateT Platform ProbComp Bool)
    (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (packet : registration.InitPacket)
    (pinResult : RustM (core.option.Option session.ServerAuthenticationPin))
    (before after : Client) (previous finalPlatform : Platform) (handle : Nat) (log : Log KemSK)
    (beforePool afterPool : Pool KemSK)
    (supported : ((((.ok (some handle), after), finalPlatform), log), afterPool) ∈ support
      (eval setup (RegistrationNativePlatformKemCountedAccept.afterPin setup codec checks (StateT.lift reserve) route representation created packet pinResult)
        before previous beforePool)) :
    ∃ pin, pinResult = .ok (.Some pin) ∧
      ∃ receipt : CheckedCut setup codec checks route representation created packet pin before previous handle after finalPlatform log,
        receipt.root.beforeAgreement.server.sessions = before.server.sessions := by
  unfold RegistrationNativePlatformKemCountedAccept.afterPin at supported
  cases pinResult with
  | fail error => cases pure_success setup (.fail error) before previous handle after finalPlatform log beforePool afterPool supported
  | div => cases pure_success setup .div before previous handle after finalPlatform log beforePool afterPool supported
  | ok option =>
    cases option with
    | none => cases pure_success setup (.ok none) before previous handle after finalPlatform log beforePool afterPool supported
    | some pin =>
      obtain ⟨⟨⟨checked, current⟩, currentPlatform⟩, checkLog, laterLog, currentPool, verified, later, full⟩ :=
        bind_cut setup (ordinaryServer (RegistrationNativePlatformSourceAccept.authenticate RegistrationNativePlatformMldsaProgram.coins
          setup codec route source.verify pin packet)) _ before previous _ log beforePool afterPool supported
      have sessions := auth_sessions setup codec route pin packet before current previous currentPlatform checked checkLog beforePool currentPool verified
      cases checked with
      | fail error => cases pure_success setup (.fail error) current currentPlatform handle after finalPlatform laterLog currentPool afterPool later
      | div => cases pure_success setup .div current currentPlatform handle after finalPlatform laterLog currentPool afterPool later
      | ok checked =>
        rcases checked with ⟨events, answer⟩
        cases answer <;> try {
          cases pure_success setup (.ok none) current currentPlatform handle after finalPlatform laterLog currentPool afterPool later }
        case Accepted authenticated =>
          obtain ⟨root, rootBefore⟩ := afterAuthentication setup checks reserve representation created packet authenticated
            current after currentPlatform finalPlatform handle laterLog currentPool afterPool later
          rw [full]
          let extended : Cut setup checks representation created packet authenticated handle after finalPlatform (checkLog ++ laterLog) :=
            { root with root := { root.root with encapsulated := List.mem_append_right _ root.root.encapsulated } }
          exact ⟨pin, rfl, ⟨authenticated, events, current, currentPlatform, checkLog, beforePool, currentPool, verified, extended⟩,
            (congrArg (fun state : Client => state.server.sessions) rootBefore).trans sessions⟩

/-- Actual pin recomputation, authentication and reservation preserve the earlier token table until this same accept's Root/retention cut. -/
theorem accept (setup : Setup base KemSK) (codec : Codec Reader Response) (checks : Checks)
    (reserve : StateT Platform ProbComp Bool)
    (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (packet : registration.InitPacket)
    (before after : Client) (previous finalPlatform : Platform) (handle : Nat) (log : Log KemSK)
    (beforePool afterPool : Pool KemSK)
    (supported : ((((.ok (some handle), after), finalPlatform), log), afterPool) ∈ support
      (eval setup (RegistrationNativePlatformKemCountedAccept.accept setup codec checks (StateT.lift reserve) route representation created packet)
        before previous beforePool)) :
    ∃ pin current currentPlatform,
      ∃ receipt : CheckedCut setup codec checks route representation created packet pin current currentPlatform handle after finalPlatform log,
        receipt.root.beforeAgreement.server.sessions = before.server.sessions := by
  unfold RegistrationNativePlatformKemCountedAccept.accept at supported
  obtain ⟨⟨⟨pinResult, current⟩, currentPlatform⟩, pinLog, laterLog, currentPool, pinned, later, full⟩ :=
    bind_cut setup (ordinaryServer (RegistrationNativePlatformSourceBuild.pin RegistrationNativePlatformMldsaProgram.coins))
      _ before previous _ log beforePool afterPool supported
  have sessions := pin_sessions setup before current previous currentPlatform pinResult pinLog beforePool currentPool pinned
  obtain ⟨pin, _pinEq, checked, rootBefore⟩ := afterPin setup codec checks reserve route representation created packet pinResult
    current after currentPlatform finalPlatform handle laterLog currentPool afterPool later
  rw [full]
  let extended : Cut setup checks representation created packet checked.authenticated handle after finalPlatform (pinLog ++ laterLog) :=
    { checked.root with root := { checked.root.root with encapsulated := List.mem_append_right _ checked.root.root.encapsulated } }
  exact ⟨pin, current, currentPlatform, { checked with root := extended }, rootBefore.trans sessions⟩


private theorem raw_unlog {A : Type} (setup : Setup base KemSK) (work : OracleComp CP A)
    (beforePool afterPool : Pool KemSK) (value : A) (log : Log KemSK)
    (supported : ((value, log), afterPool) ∈ support
      (RegistrationNativeKemCountedProgram.evaluate setup.baseImpl setup.kem work.withQueryLog beforePool)) :
    (value, afterPool) ∈ support (RegistrationNativeKemCountedProgram.evaluate setup.baseImpl setup.kem work beforePool) := by
  have law := congrArg (fun program => RegistrationNativeKemCountedProgram.evaluate setup.baseImpl setup.kem program beforePool)
    (loggingOracle.fst_map_run_simulateQ work)
  simp only [RegistrationNativeKemCountedProgram.evaluate, simulateQ_map, StateT.run_map] at law
  unfold RegistrationNativeKemCountedProgram.evaluate
  rw [← law, support_map]
  exact ⟨_, supported, rfl⟩

private theorem agree_sessions (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (packet : registration.InitPacket) (authenticated : registration.AuthenticatedInit)
    (handle : Nat) (after : Client) (finalPlatform : Platform) (log : Log KemSK)
    (receipt : Cut setup checks representation created packet authenticated handle after finalPlatform log) :
    receipt.afterAgreement.server.sessions = receipt.beforeAgreement.server.sessions := by
  have called := raw_unlog setup _ receipt.beforePool receipt.afterAgreementPool
    ((.ok (.ServerComplete receipt.accepted) : RustM agreement.AgreementEffect), receipt.afterAgreement) receipt.agreementLog receipt.agreed
  have executed : (.ok (.ServerComplete receipt.accepted), (receipt.afterAgreement, receipt.afterAgreementPool)) ∈ support
      ((RegistrationNativeKemCountedTrusted.execute setup
        (RegistrationNativeKemCountedServerPrimitive.agree setup checks representation created authenticated)).run
          (receipt.beforeAgreement, receipt.beforePool)) := by
    simp only [RegistrationNativeKemCountedTrusted.execute, StateT.run, support_map]
    exact ⟨_, called, rfl⟩
  have native : (.ok (.ServerComplete receipt.accepted), RegistrationNativeKemServerState.toNative receipt.afterAgreement receipt.afterAgreementPool) ∈ support
      ((RegistrationNativeExperiment.server (RegistrationServerNativeSource.agree setup checks representation created packet authenticated)).run
        (RegistrationNativeKemServerState.toNative receipt.beforeAgreement receipt.beforePool)) := by
    rw [← RegistrationNativeKemCountedServerSource.agree_native setup checks representation created packet authenticated,
      support_map]
    exact ⟨_, executed, rfl⟩
  simp only [RegistrationNativeExperiment.server, RegistrationServerNativeSource.agree, StateT.run, Functor.map_map, support_map] at native
  obtain ⟨result, _called, same⟩ := native
  exact (congrArg (fun result => result.2.server.sessions) same).symm

/-- A token newly inserted at this evaluated cut contains this very cut's actual completed agreement. -/
theorem new_agreement (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (packet : registration.InitPacket) (authenticated : registration.AuthenticatedInit)
    (handle : Nat) (after : Client) (finalPlatform : Platform) (log : Log KemSK)
    (receipt : Cut setup checks representation created packet authenticated handle after finalPlatform log)
    (token : peer.ConsumedRegistration) (present : RegistrationNativeTokenSource.Present token after.server)
    (newToken : ¬ RegistrationNativeTokenSource.Present token receipt.beforeAgreement.server) :
    token.agreement = receipt.accepted := by
  have actual := ordinary_support setup
    (RegistrationNativePlatformServerSdk.liftNative RegistrationNativePlatformMldsaProgram.coins (RegistrationServerNativeSource.retain created receipt.accepted))
    receipt.afterAgreement after receipt.atPlatform finalPlatform
    (.ok (some handle) : RustM (Option Nat)) receipt.retainLog receipt.afterAgreementPool receipt.afterPool receipt.retained
  simp only [RegistrationNativePlatformServerSdk.liftNative, StateT.run] at actual
  have native : (.ok (some handle), after.server) ∈ support
      ((RegistrationServerNativeSource.retain created receipt.accepted).run receipt.afterAgreement.server) :=
    RegistrationNativePlatformHashReceipt.native_support RegistrationNativePlatformMldsaProgram.coins _ _ receipt.atPlatform finalPlatform actual
  rcases RegistrationNativeTokenSource.retain created receipt.accepted receipt.afterAgreement.server
      (.ok (some handle), after.server) native token present with old | ⟨history, consumed⟩
  · have sessions := agree_sessions setup checks representation created packet authenticated handle after finalPlatform log receipt
    exact False.elim (newToken (by simpa only [RegistrationNativeTokenSource.Present, sessions] using old))
  · exact RegistrationNativeTokenSource.consume_agreement receipt.accepted receipt.afterAgreement.server.consumed history token consumed

/-- A new retained token from the complete actual acceptance names the genuine same-log Root collector of its own agreement. -/
theorem accept_new (setup : Setup base KemSK) (codec : Codec Reader Response) (checks : Checks)
    (reserve : StateT Platform ProbComp Bool)
    (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (packet : registration.InitPacket)
    (before after : Client) (previous finalPlatform : Platform) (handle : Nat) (log : Log KemSK)
    (beforePool afterPool : Pool KemSK)
    (supported : ((((.ok (some handle), after), finalPlatform), log), afterPool) ∈ support
      (eval setup (RegistrationNativePlatformKemCountedAccept.accept setup codec checks (StateT.lift reserve) route representation created packet)
        before previous beforePool))
    (token : peer.ConsumedRegistration) (present : RegistrationNativeTokenSource.Present token after.server)
    (newToken : ¬ RegistrationNativeTokenSource.Present token before.server) :
    ∃ pin current currentPlatform,
      ∃ receipt : CheckedCut setup codec checks route representation created packet pin current currentPlatform handle after finalPlatform log,
        token.agreement = receipt.root.accepted := by
  obtain ⟨pin, current, currentPlatform, receipt, sessions⟩ := accept setup codec checks reserve route representation created packet
    before after previous finalPlatform handle log beforePool afterPool supported
  refine ⟨pin, current, currentPlatform, receipt, new_agreement setup checks representation created packet receipt.authenticated
    handle after finalPlatform log receipt.root token present ?_⟩
  simpa only [RegistrationNativeTokenSource.Present, sessions] using newToken
/-- The exact complete client at the Root cut is the state actually returned by this mandatory authentication, before external-only reservation. -/
theorem afterPin_full (setup : Setup base KemSK) (codec : Codec Reader Response) (checks : Checks)
    (reserve : StateT Platform ProbComp Bool)
    (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (packet : registration.InitPacket)
    (pinResult : RustM (core.option.Option session.ServerAuthenticationPin))
    (before after : Client) (previous finalPlatform : Platform) (handle : Nat) (log : Log KemSK)
    (beforePool afterPool : Pool KemSK)
    (supported : ((((.ok (some handle), after), finalPlatform), log), afterPool) ∈ support
      (eval setup (RegistrationNativePlatformKemCountedAccept.afterPin setup codec checks (StateT.lift reserve) route representation created packet pinResult)
        before previous beforePool)) :
    ∃ pin, pinResult = .ok (.Some pin) ∧
      ∃ receipt : CheckedCut setup codec checks route representation created packet pin before previous handle after finalPlatform log,
        receipt.root.beforeAgreement = receipt.afterCheck ∧
        receipt.root.beforeAgreement.server.sessions = before.server.sessions := by
  unfold RegistrationNativePlatformKemCountedAccept.afterPin at supported
  cases pinResult with
  | fail error => cases pure_success setup (.fail error) before previous handle after finalPlatform log beforePool afterPool supported
  | div => cases pure_success setup .div before previous handle after finalPlatform log beforePool afterPool supported
  | ok option =>
    cases option with
    | none => cases pure_success setup (.ok none) before previous handle after finalPlatform log beforePool afterPool supported
    | some pin =>
      obtain ⟨⟨⟨checked, current⟩, currentPlatform⟩, checkLog, laterLog, currentPool, verified, later, full⟩ :=
        bind_cut setup (ordinaryServer (RegistrationNativePlatformSourceAccept.authenticate RegistrationNativePlatformMldsaProgram.coins
          setup codec route source.verify pin packet)) _ before previous _ log beforePool afterPool supported
      have sessions := auth_sessions setup codec route pin packet before current previous currentPlatform checked checkLog beforePool currentPool verified
      cases checked with
      | fail error => cases pure_success setup (.fail error) current currentPlatform handle after finalPlatform laterLog currentPool afterPool later
      | div => cases pure_success setup .div current currentPlatform handle after finalPlatform laterLog currentPool afterPool later
      | ok checked =>
        rcases checked with ⟨events, answer⟩
        cases answer <;> try {
          cases pure_success setup (.ok none) current currentPlatform handle after finalPlatform laterLog currentPool afterPool later }
        case Accepted authenticated =>
          obtain ⟨root, rootBefore⟩ := afterAuthentication setup checks reserve representation created packet authenticated
            current after currentPlatform finalPlatform handle laterLog currentPool afterPool later
          rw [full]
          let extended : Cut setup checks representation created packet authenticated handle after finalPlatform (checkLog ++ laterLog) :=
            { root with root := { root.root with encapsulated := List.mem_append_right _ root.root.encapsulated } }
          exact ⟨pin, rfl, ⟨authenticated, events, current, currentPlatform, checkLog, beforePool, currentPool, verified, extended⟩,
            rootBefore, (congrArg (fun state : Client => state.server.sessions) rootBefore).trans sessions⟩

/-- Full acceptance retains the actual authentication-to-Root state equality together with the earlier token table. -/
theorem accept_full (setup : Setup base KemSK) (codec : Codec Reader Response) (checks : Checks)
    (reserve : StateT Platform ProbComp Bool)
    (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (packet : registration.InitPacket)
    (before after : Client) (previous finalPlatform : Platform) (handle : Nat) (log : Log KemSK)
    (beforePool afterPool : Pool KemSK)
    (supported : ((((.ok (some handle), after), finalPlatform), log), afterPool) ∈ support
      (eval setup (RegistrationNativePlatformKemCountedAccept.accept setup codec checks (StateT.lift reserve) route representation created packet)
        before previous beforePool)) :
    ∃ pin current currentPlatform,
      ∃ receipt : CheckedCut setup codec checks route representation created packet pin current currentPlatform handle after finalPlatform log,
        receipt.root.beforeAgreement = receipt.afterCheck ∧
        receipt.root.beforeAgreement.server.sessions = before.server.sessions := by
  unfold RegistrationNativePlatformKemCountedAccept.accept at supported
  obtain ⟨⟨⟨pinResult, current⟩, currentPlatform⟩, pinLog, laterLog, currentPool, pinned, later, full⟩ :=
    bind_cut setup (ordinaryServer (RegistrationNativePlatformSourceBuild.pin RegistrationNativePlatformMldsaProgram.coins))
      _ before previous _ log beforePool afterPool supported
  have sessions := pin_sessions setup before current previous currentPlatform pinResult pinLog beforePool currentPool pinned
  obtain ⟨pin, _pinEq, checked, rootBefore, priorSessions⟩ := afterPin_full setup codec checks reserve route representation created packet pinResult
    current after currentPlatform finalPlatform handle laterLog currentPool afterPool later
  rw [full]
  let extended : Cut setup checks representation created packet checked.authenticated handle after finalPlatform (pinLog ++ laterLog) :=
    { checked.root with root := { checked.root.root with encapsulated := List.mem_append_right _ checked.root.root.encapsulated } }
  exact ⟨pin, current, currentPlatform, { checked with root := extended }, rootBefore, priorSessions.trans sessions⟩


/-- A new retained token from the complete actual acceptance names the genuine same-log Root collector of its own agreement. -/
theorem accept_new_full (setup : Setup base KemSK) (codec : Codec Reader Response) (checks : Checks)
    (reserve : StateT Platform ProbComp Bool)
    (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (packet : registration.InitPacket)
    (before after : Client) (previous finalPlatform : Platform) (handle : Nat) (log : Log KemSK)
    (beforePool afterPool : Pool KemSK)
    (supported : ((((.ok (some handle), after), finalPlatform), log), afterPool) ∈ support
      (eval setup (RegistrationNativePlatformKemCountedAccept.accept setup codec checks (StateT.lift reserve) route representation created packet)
        before previous beforePool))
    (token : peer.ConsumedRegistration) (present : RegistrationNativeTokenSource.Present token after.server)
    (newToken : ¬ RegistrationNativeTokenSource.Present token before.server) :
    ∃ pin current currentPlatform,
      ∃ receipt : CheckedCut setup codec checks route representation created packet pin current currentPlatform handle after finalPlatform log,
        receipt.root.beforeAgreement = receipt.afterCheck ∧ token.agreement = receipt.root.accepted := by
  obtain ⟨pin, current, currentPlatform, receipt, beforeEq, sessions⟩ := accept_full setup codec checks reserve route representation created packet
    before after previous finalPlatform handle log beforePool afterPool supported
  refine ⟨pin, current, currentPlatform, receipt, beforeEq, new_agreement setup checks representation created packet receipt.authenticated
    handle after finalPlatform log receipt.root token present ?_⟩
  simpa only [RegistrationNativeTokenSource.Present, sessions] using newToken


/-- The evaluated exact agreement block is supported by the literal native Server source body at its own reached states. -/
theorem agreed_native (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (packet : registration.InitPacket) (authenticated : registration.AuthenticatedInit)
    (handle : Nat) (after : Client) (finalPlatform : Platform) (log : Log KemSK)
    (receipt : Cut setup checks representation created packet authenticated handle after finalPlatform log) :
    (.ok (.ServerComplete receipt.accepted), receipt.afterAgreement.server) ∈ support
      ((RegistrationServerNativeSource.agree setup checks representation created packet authenticated).run receipt.beforeAgreement.server) := by
  have called := raw_unlog setup _ receipt.beforePool receipt.afterAgreementPool
    ((.ok (.ServerComplete receipt.accepted) : RustM agreement.AgreementEffect), receipt.afterAgreement) receipt.agreementLog receipt.agreed
  have executed : (.ok (.ServerComplete receipt.accepted), (receipt.afterAgreement, receipt.afterAgreementPool)) ∈ support
      ((RegistrationNativeKemCountedTrusted.execute setup
        (RegistrationNativeKemCountedServerPrimitive.agree setup checks representation created authenticated)).run
          (receipt.beforeAgreement, receipt.beforePool)) := by
    simp only [RegistrationNativeKemCountedTrusted.execute, StateT.run, support_map]
    exact ⟨_, called, rfl⟩
  have native : (.ok (.ServerComplete receipt.accepted), RegistrationNativeKemServerState.toNative receipt.afterAgreement receipt.afterAgreementPool) ∈ support
      ((RegistrationNativeExperiment.server (RegistrationServerNativeSource.agree setup checks representation created packet authenticated)).run
        (RegistrationNativeKemServerState.toNative receipt.beforeAgreement receipt.beforePool)) := by
    rw [← RegistrationNativeKemCountedServerSource.agree_native setup checks representation created packet authenticated, support_map]
    exact ⟨_, executed, rfl⟩
  simp only [RegistrationNativeExperiment.server, StateT.run, support_map] at native
  obtain ⟨⟨effect, frontend⟩, actual, same⟩ := native
  have effectEq : effect = .ok (.ServerComplete receipt.accepted) := congrArg Prod.fst same
  have frontendEq : frontend = receipt.afterAgreement.server := congrArg (fun result => result.2.server) same
  rw [effectEq, frontendEq] at actual
  exact actual

/-- Actual retention of this cut's handle is supported by the unchanged native replay-consume/table source body. -/
theorem retained_native (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (packet : registration.InitPacket) (authenticated : registration.AuthenticatedInit)
    (handle : Nat) (after : Client) (finalPlatform : Platform) (log : Log KemSK)
    (receipt : Cut setup checks representation created packet authenticated handle after finalPlatform log) :
    (.ok (some handle), after.server) ∈ support
      ((RegistrationServerNativeSource.retain created receipt.accepted).run receipt.afterAgreement.server) := by
  have actual := ordinary_support setup
    (RegistrationNativePlatformServerSdk.liftNative RegistrationNativePlatformMldsaProgram.coins (RegistrationServerNativeSource.retain created receipt.accepted))
    receipt.afterAgreement after receipt.atPlatform finalPlatform
    (.ok (some handle) : RustM (Option Nat)) receipt.retainLog receipt.afterAgreementPool receipt.afterPool receipt.retained
  simp only [RegistrationNativePlatformServerSdk.liftNative, StateT.run] at actual
  exact RegistrationNativePlatformHashReceipt.native_support RegistrationNativePlatformMldsaProgram.coins _ _ receipt.atPlatform finalPlatform actual

/-- All reached source pin/authentication states and the exact same evaluated Root cut of complete successful acceptance. -/
structure SourceCut (setup : Setup base KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (packet : registration.InitPacket)
    (before after : Client) (previous finalPlatform : Platform) (handle : Nat) (log : Log KemSK) where
  pin : session.ServerAuthenticationPin
  current : Client
  currentPlatform : Platform
  pinned : ((.ok (.Some pin), current.server), currentPlatform) ∈ support
    (((RegistrationNativePlatformSourceBuild.pin RegistrationNativePlatformMldsaProgram.coins).run before.server).run previous)
  receipt : CheckedCut setup codec checks route representation created packet pin current currentPlatform handle after finalPlatform log
  authenticated : ((.ok (receipt.events, .Accepted receipt.authenticated), receipt.afterCheck.server), receipt.checkPlatform) ∈ support
    (((RegistrationNativePlatformSourceAccept.authenticate RegistrationNativePlatformMldsaProgram.coins setup codec route source.verify pin packet).run current.server).run currentPlatform)
  beforeEq : receipt.root.beforeAgreement = receipt.afterCheck
  sessions : receipt.root.beforeAgreement.server.sessions = before.server.sessions

/-- Complete actual acceptance supplies all literal source prefixes alongside its same-log native collector; no cached-pin or authentication conclusion is assumed. -/
theorem accept_source_prefix (setup : Setup base KemSK) (codec : Codec Reader Response) (checks : Checks)
    (reserve : StateT Platform ProbComp Bool)
    (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (packet : registration.InitPacket)
    (before after : Client) (previous finalPlatform : Platform) (handle : Nat) (log : Log KemSK)
    (beforePool afterPool : Pool KemSK)
    (supported : ((((.ok (some handle), after), finalPlatform), log), afterPool) ∈ support
      (eval setup (RegistrationNativePlatformKemCountedAccept.accept setup codec checks (StateT.lift reserve) route representation created packet)
        before previous beforePool)) :
    Nonempty (SourceCut setup codec checks route representation created packet before after previous finalPlatform handle log) := by
  unfold RegistrationNativePlatformKemCountedAccept.accept at supported
  obtain ⟨⟨⟨pinResult, current⟩, currentPlatform⟩, pinLog, laterLog, currentPool, pinned, later, full⟩ :=
    bind_cut setup (ordinaryServer (RegistrationNativePlatformSourceBuild.pin RegistrationNativePlatformMldsaProgram.coins))
      _ before previous _ log beforePool afterPool supported
  have sessions := pin_sessions setup before current previous currentPlatform pinResult pinLog beforePool currentPool pinned
  have sourcePin := ordinary_support setup (RegistrationNativePlatformSourceBuild.pin RegistrationNativePlatformMldsaProgram.coins)
    before current previous currentPlatform pinResult pinLog beforePool currentPool pinned
  obtain ⟨pin, pinEq, checked, rootBefore, priorSessions⟩ := afterPin_full setup codec checks reserve route representation created packet pinResult
    current after currentPlatform finalPlatform handle laterLog currentPool afterPool later
  rw [pinEq] at sourcePin
  have sourceAuth := ordinary_support setup
    (RegistrationNativePlatformSourceAccept.authenticate RegistrationNativePlatformMldsaProgram.coins setup codec route source.verify pin packet)
    current checked.afterCheck currentPlatform checked.checkPlatform (.ok (checked.events, .Accepted checked.authenticated))
      checked.checkLog checked.beforePool checked.checkPool checked.checked
  rw [full]
  let extended : Cut setup checks representation created packet checked.authenticated handle after finalPlatform (pinLog ++ laterLog) :=
    { checked.root with root := { checked.root.root with encapsulated := List.mem_append_right _ checked.root.root.encapsulated } }
  exact ⟨⟨pin, current, currentPlatform, sourcePin, { checked with root := extended }, sourceAuth, rootBefore, priorSessions.trans sessions⟩⟩

/-- The exact cut's authentication history/cache reaches the actual returned acceptance history/cache unchanged after authentication. -/
theorem SourceCut.summary (setup : Setup base KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (packet : registration.InitPacket)
    (before after : Client) (previous finalPlatform : Platform) (handle : Nat) (log : Log KemSK)
    (cut : SourceCut setup codec checks route representation created packet before after previous finalPlatform handle log) :
    RegistrationNativeInitFinal.summary cut.receipt.afterCheck.server = RegistrationNativeInitFinal.summary after.server := by
  have agreed := agreed_native setup checks representation created packet cut.receipt.authenticated handle after finalPlatform log cut.receipt.root
  have retained := retained_native setup checks representation created packet cut.receipt.authenticated handle after finalPlatform log cut.receipt.root
  have first := RegistrationNativeInitFinal.agree setup checks representation created packet cut.receipt.authenticated
    cut.receipt.root.beforeAgreement.server (.ok (.ServerComplete cut.receipt.root.accepted), cut.receipt.root.afterAgreement.server) agreed
  have last := RegistrationNativeInitFinal.retain created cut.receipt.root.accepted cut.receipt.root.afterAgreement.server (.ok (some handle), after.server) retained
  rw [cut.beforeEq] at first
  exact (last.trans first).symm

end BeaconcryptCore.Computational.RegistrationNativePlatformAcceptActualToken

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformAcceptActualToken.afterAuthentication' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformAcceptActualToken.afterAuthentication

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformAcceptActualToken.afterPin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformAcceptActualToken.afterPin

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformAcceptActualToken.accept' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformAcceptActualToken.accept

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformAcceptActualToken.new_agreement' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformAcceptActualToken.new_agreement

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformAcceptActualToken.accept_new' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformAcceptActualToken.accept_new

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformAcceptActualToken.afterPin_full' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformAcceptActualToken.afterPin_full

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformAcceptActualToken.accept_full' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformAcceptActualToken.accept_full

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformAcceptActualToken.accept_new_full' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformAcceptActualToken.accept_new_full

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformAcceptActualToken.agreed_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformAcceptActualToken.agreed_native

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformAcceptActualToken.retained_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformAcceptActualToken.retained_native

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformAcceptActualToken.accept_source_prefix' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformAcceptActualToken.accept_source_prefix

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformAcceptActualToken.SourceCut.summary' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformAcceptActualToken.SourceCut.summary
