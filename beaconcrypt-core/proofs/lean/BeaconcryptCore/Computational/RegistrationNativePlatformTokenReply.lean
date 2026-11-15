-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformAcceptCut
import BeaconcryptCore.Computational.RegistrationNativePlatformAcceptCache
import BeaconcryptCore.Computational.RegistrationNativeTokenCacheSource

/-! A token newly appearing at an actual source callback requires that callback's successful one-use handle reply. Failed pin, authentication, allocation, agreement and replay branches cannot add a token. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformTokenReply
open BeaconcryptCore.Refinement
open PqxdhServerAuthExperiment (Setup Codec Checks)
open RegistrationServerFrontendCompiler (State)
open RegistrationNativeTokenSource (Present Born)
variable {n : Nat} {Platform ι KemSK Value Reader Response : Type} {base : OracleSpec ι}
attribute [local irreducible] RegistrationReplaySchedule.consume RegistrationWorldAuthentication.begin
  RegistrationServerNativeSource.authenticate RegistrationServerNativeSource.agree RegistrationAuthenticationShared.begin

private theorem pure_present (value : Value) (before : State n) (previous : Platform)
    (result : (Value × State n) × Platform)
    (supported : result ∈ support (((pure value : StateT (State n) (StateT Platform ProbComp) Value).run before).run previous))
    (token : peer.ConsumedRegistration) (present : Present token result.1.2) : Present token before := by
  simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
  cases supported
  exact present

private theorem agree_sessions (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (packet : registration.InitPacket)
    (authenticated : registration.AuthenticatedInit) (before : State n)
    (result : RustM agreement.AgreementEffect × State n)
    (supported : result ∈ support ((RegistrationServerNativeSource.agree setup checks representation created packet authenticated).run before)) :
    result.2.sessions = before.sessions := by
  simp only [RegistrationServerNativeSource.agree, StateT.run, support_map] at supported
  obtain ⟨inner, _called, same⟩ := supported
  cases same
  rfl

private theorem retain_reply (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (accepted : agreement.ServerAgreement)
    (before : State n) (result : RustM (Option Nat) × State n)
    (supported : result ∈ support ((RegistrationServerNativeSource.retain created accepted).run before))
    (token : peer.ConsumedRegistration) (present : Present token result.2) (newToken : ¬ Present token before) :
    ∃ handle, result.1 = .ok (some handle) := by
  simp only [RegistrationServerNativeSource.retain, RegistrationServerNativeSource.sourceStep,
    RegistrationWorldServerFrontend.retain, RegistrationServerFrontendCompiler.restore, StateT.run] at supported
  cases consumed : RegistrationReplaySchedule.consume accepted before.consumed with
  | fail error | div =>
      simp only [consumed, map_pure, support_pure, Set.mem_singleton_iff] at supported
      cases supported
      exact False.elim (newToken present)
  | ok answer =>
      rcases answer with ⟨option, history⟩
      cases option with
      | none =>
          simp only [consumed, map_pure, support_pure, Set.mem_singleton_iff] at supported
          cases supported
          exact False.elim (newToken present)
      | some actual =>
          simp only [consumed, map_pure, support_pure, Set.mem_singleton_iff] at supported
          cases supported
          exact ⟨before.sessions.length, rfl⟩

/-- Actual replay/reservation/agreement continuation only retains earlier tokens or inserts its literal consumed agreement. -/
theorem afterAuthentication (coins : QueryImpl unifSpec (StateT Platform ProbComp))
    (setup : Setup base KemSK) (checks : Checks) (reserve : StateT Platform ProbComp Bool)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (packet : registration.InitPacket)
    (authenticated : registration.AuthenticatedInit) (before : State n) (previous : Platform)
    (result : (RustM (Option Nat) × State n) × Platform)
    (supported : result ∈ support
      (((RegistrationNativePlatformServerSdk.afterAuthentication coins setup checks (StateT.lift reserve) representation created packet authenticated).run before).run previous))
    (token : peer.ConsumedRegistration) (present : Present token result.1.2) :
    Present token before ∨ ∃ handle, result.1.1 = .ok (some handle) := by
  simp only [RegistrationNativePlatformServerSdk.afterAuthentication, StateT.run_bind, StateT.run_get, pure_bind] at supported
  split at supported
  · exact Or.inl (pure_present _ before previous result supported token present)
  · simp only [StateT.run_bind, mem_support_bind_iff] at supported
    obtain ⟨reserved, admitted, continued⟩ := supported
    simp only [StateT.run_lift, bind_pure_comp, StateT.run_map, support_map] at admitted
    obtain ⟨⟨allowed, platform⟩, _reserved, same⟩ := admitted
    cases same
    cases allowed with
    | false => exact Or.inl (pure_present _ before platform result continued token present)
    | true =>
      simp only [ite_true, StateT.run_bind, mem_support_bind_iff] at continued
      obtain ⟨⟨⟨effect, afterAgreement⟩, afterPlatform⟩, agreed, later⟩ := continued
      have native : (effect, afterAgreement) ∈ support
          ((RegistrationServerNativeSource.agree setup checks representation created packet authenticated).run before) :=
        RegistrationNativePlatformHashReceipt.native_support coins _ _ platform afterPlatform agreed
      have sessions := agree_sessions setup checks representation created packet authenticated before (effect, afterAgreement) native
      change afterAgreement.sessions = before.sessions at sessions
      cases effect with
      | fail error | div =>
        have old := pure_present _ afterAgreement afterPlatform result later token present
        exact Or.inl (by simpa only [Present, sessions] using old)
      | ok answer => cases answer with
        | ServerComplete accepted =>
          have retained : result.1 ∈ support ((RegistrationServerNativeSource.retain created accepted).run afterAgreement) :=
            RegistrationNativePlatformHashReceipt.native_support coins _ _ afterPlatform result.2 later
          by_cases old : Present token before
          · exact Or.inl old
          · exact Or.inr (retain_reply created accepted afterAgreement result.1 retained token present
              (by simpa only [Present, sessions] using old))
        | _ =>
          have old := pure_present _ afterAgreement afterPlatform result later token present
          exact Or.inl (by simpa only [Present, sessions] using old)

private theorem map_apply {S X Y : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (f : X → Y) (work : StateT S m X) (before : S) :
    (f <$> work) before = Prod.map f id <$> work before := StateT.run_map f work before

private theorem pin_sessions (coins : QueryImpl unifSpec (StateT Platform ProbComp))
    (before : State n) (previous : Platform)
    (result : (RustM (core.option.Option session.ServerAuthenticationPin) × State n) × Platform)
    (supported : result ∈ support (((RegistrationNativePlatformSourceBuild.pin coins).run before).run previous)) :
    result.1.2.sessions = before.sessions := by
  simp only [RegistrationNativePlatformSourceBuild.pin, StateT.run, map_apply, support_map] at supported
  obtain ⟨inner, _called, same⟩ := supported
  exact (congrArg (fun value => value.1.2.sessions) same).symm

private theorem authenticate_sessions (coins : QueryImpl unifSpec (StateT Platform ProbComp))
    (setup : Setup base KemSK) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (verify : MldsaTranscriptAuth.Verify) (pin : session.ServerAuthenticationPin) (packet : registration.InitPacket)
    (before : State n) (previous : Platform)
    (result : (RustM (List RegistrationAuthenticationFlow.Event × registration.InitAuthentication) × State n) × Platform)
    (supported : result ∈ support (((RegistrationNativePlatformSourceAccept.authenticate coins setup codec route verify pin packet).run before).run previous)) :
    result.1.2.sessions = before.sessions := by
  simp only [RegistrationNativePlatformSourceAccept.authenticate, StateT.run, map_apply, support_map] at supported
  obtain ⟨inner, _called, same⟩ := supported
  exact (congrArg (fun value => value.1.2.sessions) same).symm

/-- A retained actual source token is inherited or comes from this callback's literal pin, mandatory authentication, agreement and replay-consume cuts. -/
theorem accept (coins : QueryImpl unifSpec (StateT Platform ProbComp))
    (setup : Setup base KemSK) (codec : Codec Reader Response) (checks : Checks) (reserve : StateT Platform ProbComp Bool)
    (route : RawCtxServerRouting.SenderDecoder) (verify : MldsaTranscriptAuth.Verify)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (packet : registration.InitPacket)
    (before : State n) (previous : Platform) (result : (RustM (Option Nat) × State n) × Platform)
    (supported : result ∈ support (((RegistrationNativePlatformSourceAccept.accept coins setup codec checks reserve route verify representation created packet).run before).run previous))
    (token : peer.ConsumedRegistration) (present : Present token result.1.2) :
    Present token before ∨ ∃ handle, result.1.1 = .ok (some handle) := by
  simp only [RegistrationNativePlatformSourceAccept.accept, RegistrationNativePlatformSourceAccept.acceptWith,
    StateT.run_bind, mem_support_bind_iff] at supported
  obtain ⟨⟨⟨pinReply, pinned⟩, pinPlatform⟩, pinCalled, continued⟩ := supported
  have samePin := pin_sessions coins before previous ((pinReply, pinned), pinPlatform) pinCalled
  change pinned.sessions = before.sessions at samePin
  cases pinReply with
  | fail error | div =>
    have old := pure_present _ pinned pinPlatform result continued token present
    exact Or.inl (by simpa only [Present, samePin] using old)
  | ok optional => cases optional with
    | none =>
      have old := pure_present _ pinned pinPlatform result continued token present
      exact Or.inl (by simpa only [Present, samePin] using old)
    | some pin =>
      simp only [RegistrationNativePlatformSourceAccept.afterPin, StateT.run_bind, mem_support_bind_iff] at continued
      obtain ⟨⟨⟨authReply, checked⟩, authPlatform⟩, authCalled, later⟩ := continued
      have sameAuth := authenticate_sessions coins setup codec route verify pin packet pinned pinPlatform ((authReply, checked), authPlatform) authCalled
      change checked.sessions = pinned.sessions at sameAuth
      have sessions : checked.sessions = before.sessions := sameAuth.trans samePin
      cases authReply with
      | fail error | div =>
        have old := pure_present _ checked authPlatform result later token present
        exact Or.inl (by simpa only [Present, sessions] using old)
      | ok pair =>
        rcases pair with ⟨events, status⟩
        cases status with
        | Accepted authenticated =>
          rcases afterAuthentication coins setup checks reserve representation created packet authenticated checked authPlatform result later token present with old | born
          · exact Or.inl (by simpa only [Present, sessions] using old)
          · exact Or.inr born
        | _ =>
          have old := pure_present _ checked authPlatform result later token present
          exact Or.inl (by simpa only [Present, sessions] using old)

end BeaconcryptCore.Computational.RegistrationNativePlatformTokenReply

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformTokenReply.afterAuthentication' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformTokenReply.afterAuthentication

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformTokenReply.accept' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformTokenReply.accept
