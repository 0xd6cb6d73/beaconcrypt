-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformAcceptCut
import BeaconcryptCore.Computational.RegistrationNativePlatformAcceptCache
import BeaconcryptCore.Computational.RegistrationNativeTokenCacheSource

/-! A literal token surviving actual source acceptance is inherited or born from the same callback's mandatory authentication and actual agreement/replay consume. Stateful external reservations and repeated pin hashing retain all their reached effects and failed prefixes. No successful API reply is required for the token provenance conclusion. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformTokenSource
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
    Present token before ∨ Born setup checks representation created packet authenticated before token := by
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
          rcases RegistrationNativeTokenSource.retain created accepted afterAgreement result.1 retained token present with old | ⟨history, consumed⟩
          · exact Or.inl (by simpa only [Present, sessions] using old)
          · exact Or.inr ⟨accepted, afterAgreement, history, native, consumed⟩
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
    Present token before ∨ ∃ pin pinned pinPlatform events authenticated checked authPlatform,
      ((.ok (.Some pin), pinned), pinPlatform) ∈ support (((RegistrationNativePlatformSourceBuild.pin coins).run before).run previous) ∧
      ((.ok (events, .Accepted authenticated), checked), authPlatform) ∈ support
        (((RegistrationNativePlatformSourceAccept.authenticate coins setup codec route verify pin packet).run pinned).run pinPlatform) ∧
      Born setup checks representation created packet authenticated checked token ∧
      RegistrationNativeInitFinal.summary checked = RegistrationNativeInitFinal.summary result.1.2 := by
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
          · exact Or.inr ⟨pin, pinned, pinPlatform, events, authenticated, checked, authPlatform, pinCalled, authCalled, born,
              (RegistrationNativePlatformAcceptCache.afterAuthentication coins setup checks reserve representation created packet authenticated checked authPlatform result later).symm⟩
        | _ =>
          have old := pure_present _ checked authPlatform result later token present
          exact Or.inl (by simpa only [Present, sessions] using old)

end BeaconcryptCore.Computational.RegistrationNativePlatformTokenSource

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformTokenSource.afterAuthentication' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformTokenSource.afterAuthentication

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformTokenSource.accept' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformTokenSource.accept
