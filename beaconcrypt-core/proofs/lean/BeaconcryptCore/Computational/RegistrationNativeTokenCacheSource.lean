-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeTokenRootReceipt
import BeaconcryptCore.Computational.RegistrationNativeInitFinal

/-! The token birth receipt retains its actual same-cut authentication cache through the complete accept callback. It also exposes the exact accepted Init cache query for later source-input pairing. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeTokenCacheSource
open PqxdhServerAuthExperiment (Setup Codec Checks)
open RegistrationServerFrontendCompiler (State)
attribute [local irreducible] RegistrationReplaySchedule.consume RegistrationWorldAuthentication.begin
  RegistrationServerNativeSource.authenticate RegistrationServerNativeSource.agree RegistrationNativeExperiment.handler
  RegistrationAuthenticationShared.begin
variable {n : Nat} {ι KemSK Value Reader Response : Type} {base : OracleSpec ι}

open RegistrationNativeTokenSource (Present Born)
private theorem pure_present (value : Value) (before : State n) (result : Value × State n)
    (supported : result ∈ support ((pure value : StateT (State n) ProbComp Value).run before))
    (token : peer.ConsumedRegistration) (present : Present token result.2) : Present token before := by
  simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
  cases supported
  exact present

private theorem authenticate_sessions (setup : Setup base KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (verify : MldsaTranscriptAuth.Verify)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (packet : registration.InitPacket)
    (before : State n) (result : RustM (List BeaconcryptCore.Refinement.RegistrationAuthenticationFlow.Event × registration.InitAuthentication) × State n)
    (supported : result ∈ support ((RegistrationServerNativeSource.authenticate setup codec route verify created packet).run before)) :
    result.2.sessions = before.sessions := by
  rw [RegistrationNativeInitAuthentication.authenticate, support_map] at supported
  obtain ⟨inner, _called, same⟩ := supported
  cases same
  rfl

/-- Every actual SDK accept token has an actual mandatory authentication prefix and supported same-call agreement birth, or was already present. -/
theorem accept (setup : Setup base KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (verify : MldsaTranscriptAuth.Verify)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (packet : registration.InitPacket)
    (before : State n) (result : RustM (Option Nat) × State n)
    (supported : result ∈ support ((RegistrationServerSdkSource.accept setup codec checks route verify representation created packet).run before))
    (token : peer.ConsumedRegistration) (present : Present token result.2) :
    Present token before ∨ ∃ events authenticated afterAuthentication,
      (.ok (events, .Accepted authenticated), afterAuthentication) ∈ support
        ((RegistrationServerNativeSource.authenticate setup codec route verify created packet).run before) ∧
      Born setup checks representation created packet authenticated afterAuthentication token ∧
      RegistrationNativeInitFinal.summary afterAuthentication = RegistrationNativeInitFinal.summary result.2 := by
  rw [RegistrationServerSdkSource.accept, StateT.run_bind, mem_support_bind_iff] at supported
  obtain ⟨checked, queried, continued⟩ := supported
  rcases checked with ⟨reply, afterAuth⟩
  have same : afterAuth.sessions = before.sessions := authenticate_sessions setup codec route verify created packet before (reply, afterAuth) queried
  change (reply, afterAuth) ∈ support ((RegistrationServerNativeSource.authenticate setup codec route verify created packet).run before) at queried
  cases responseEq : reply with
  | fail error | div =>
      simp only [responseEq] at continued
      have old := pure_present _ afterAuth result continued token present
      exact Or.inl (by simpa only [Present, same] using old)
  | ok checked =>
      rcases checked with ⟨events, authentication⟩
      cases authentication with
      | Accepted authenticated =>
          simp only [responseEq] at continued
          rcases RegistrationNativeTokenSource.afterAuthentication setup checks representation created packet authenticated afterAuth result continued token present with old | born
          · exact Or.inl (by simpa only [Present, same] using old)
          · exact Or.inr ⟨events, authenticated, afterAuth, by simpa only [responseEq] using queried, born, (RegistrationNativeInitFinal.afterAuthentication setup checks representation created packet authenticated afterAuth result continued).symm⟩
      | _ =>
          simp only [responseEq] at continued
          have old := pure_present _ afterAuth result continued token present
          exact Or.inl (by simpa only [Present, same] using old)

/-- The exact actual source authentication cut leaves the accepted Init preimage at its retained binding digest in the shared cache. -/
theorem authenticated_cache (setup : Setup base KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (verify : MldsaTranscriptAuth.Verify)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (packet : registration.InitPacket)
    (before after : State n) (events : List BeaconcryptCore.Refinement.RegistrationAuthenticationFlow.Event)
    (authenticated : registration.AuthenticatedInit)
    (supported : (.ok (events, .Accepted authenticated), after) ∈ support
      ((RegistrationServerNativeSource.authenticate setup codec route verify created packet).run before)) :
    ∃ digest,
      after.world.world.1.primitive.2 ((), BeaconcryptCore.Refinement.RegistrationAuthentication.initPreimage before.pin packet) = some digest ∧
      authenticated.binding.init_hash = RegistrationAuthenticationShared.digestArray digest := by
  exact RegistrationNativeInitAuthentication.authenticated_cache setup codec route verify created packet
    before after events authenticated supported

/-- Actual authentication changes the shared World alone; its pin, control and private token metadata are literal. -/
theorem authenticate_frame (setup : Setup base KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (verify : MldsaTranscriptAuth.Verify)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (packet : registration.InitPacket)
    (before after : State n) (reply : RustM (List BeaconcryptCore.Refinement.RegistrationAuthenticationFlow.Event × registration.InitAuthentication))
    (supported : (reply, after) ∈ support ((RegistrationServerNativeSource.authenticate setup codec route verify created packet).run before)) :
    after.pin = before.pin ∧ after.control = before.control ∧ after.consumed = before.consumed ∧ after.sessions = before.sessions := by
  rw [RegistrationNativeInitAuthentication.authenticate, support_map] at supported
  obtain ⟨inner, _called, same⟩ := supported
  have frame : RegistrationNativeInitAuthentication.withWorld before inner.2 = after := congrArg Prod.snd same
  rw [← frame]
  exact ⟨rfl, rfl, rfl, rfl⟩

end BeaconcryptCore.Computational.RegistrationNativeTokenCacheSource

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeTokenCacheSource.accept' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeTokenCacheSource.accept

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeTokenCacheSource.authenticated_cache' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeTokenCacheSource.authenticated_cache

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeTokenCacheSource.authenticate_frame' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeTokenCacheSource.authenticate_frame
