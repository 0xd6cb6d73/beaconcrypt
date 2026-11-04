-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformTokenSource

/-! Actual token-creating authentication retains the earlier stored pin and original Init preimage at its same reached cache. The explicit stored-pin hash receipt is an initialized execution invariant, not an equality assumption about two authentication games. The repeated hash charge remains in the reached native state. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformTokenCacheSource
open BeaconcryptCore.Refinement
open PqxdhServerAuthExperiment (Setup Codec)
open RegistrationServerFrontendCompiler (State)
variable {n : Nat} {Platform ι KemSK Reader Response : Type} {base : OracleSpec ι}
attribute [local irreducible] RegistrationServerNativeSource.authenticate RegistrationWorldAuthentication.begin
  RegistrationAuthenticationShared.begin RegistrationNativePlatformSourceAccept.authenticate RegistrationNativePlatformSourceBuild.pin

/-- The actual reached source pin/authentication pair supplies literal native authentication support at that same charged state. -/
theorem authentication (coins : QueryImpl unifSpec (StateT Platform ProbComp))
    (setup : Setup base KemSK) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (verify : MldsaTranscriptAuth.Verify) (created : PqxdhLiveServerConstruction.Created Unit) (packet : registration.InitPacket)
    (before pinned checked : State n) (previous pinPlatform authPlatform : Platform) (pin : session.ServerAuthenticationPin)
    (events : List RegistrationAuthenticationFlow.Event) (authenticated : registration.AuthenticatedInit)
    (cached : RegistrationNativeServerPinRecompute.Cached before.pin before.world.world.1.primitive.2)
    (pinCalled : ((.ok (.Some pin), pinned), pinPlatform) ∈ support (((RegistrationNativePlatformSourceBuild.pin coins).run before).run previous))
    (authCalled : ((.ok (events, .Accepted authenticated), checked), authPlatform) ∈ support
      (((RegistrationNativePlatformSourceAccept.authenticate coins setup codec route verify pin packet).run pinned).run pinPlatform)) :
    pin = before.pin ∧ pinned.pin = before.pin ∧
      (.ok (events, .Accepted authenticated), checked) ∈ support
        ((RegistrationServerNativeSource.authenticate setup codec route verify created packet).run pinned) := by
  rw [RegistrationNativePlatformSourceBuild.pin_hit coins before cached] at pinCalled
  simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at pinCalled
  have samePin : pin = before.pin := by
    have reply := congrArg (fun result => result.1.1) pinCalled
    simpa only [RustM.ok.injEq, Option.some.injEq] using reply
  have sameStored : pinned.pin = before.pin := congrArg (fun result => result.1.2.pin) pinCalled
  rw [samePin.trans sameStored.symm, RegistrationNativePlatformSourceAccept.authenticate_stored coins setup codec route verify created packet pinned] at authCalled
  exact ⟨samePin, sameStored, RegistrationNativePlatformHashReceipt.native_support coins _ _ pinPlatform authPlatform authCalled⟩

/-- The token-creating actual source cut retains exactly the original unsigned Init preimage at its authenticated binding digest. -/
theorem authenticated_cache (coins : QueryImpl unifSpec (StateT Platform ProbComp))
    (setup : Setup base KemSK) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (verify : MldsaTranscriptAuth.Verify) (created : PqxdhLiveServerConstruction.Created Unit) (packet : registration.InitPacket)
    (before pinned checked : State n) (previous pinPlatform authPlatform : Platform) (pin : session.ServerAuthenticationPin)
    (events : List RegistrationAuthenticationFlow.Event) (authenticated : registration.AuthenticatedInit)
    (cached : RegistrationNativeServerPinRecompute.Cached before.pin before.world.world.1.primitive.2)
    (pinCalled : ((.ok (.Some pin), pinned), pinPlatform) ∈ support (((RegistrationNativePlatformSourceBuild.pin coins).run before).run previous))
    (authCalled : ((.ok (events, .Accepted authenticated), checked), authPlatform) ∈ support
      (((RegistrationNativePlatformSourceAccept.authenticate coins setup codec route verify pin packet).run pinned).run pinPlatform)) :
    ∃ digest, checked.world.world.1.primitive.2 ((), RegistrationAuthentication.initPreimage before.pin packet) = some digest ∧
      authenticated.binding.init_hash = RegistrationAuthenticationShared.digestArray digest := by
  obtain ⟨_pin, stored, actual⟩ := authentication coins setup codec route verify created packet before pinned checked previous pinPlatform authPlatform pin
    events authenticated cached pinCalled authCalled
  obtain ⟨digest, receipt, binding⟩ := RegistrationNativeTokenCacheSource.authenticated_cache setup codec route verify created packet pinned checked events authenticated actual
  change pinned.pin = before.pin at stored
  rw [stored] at receipt
  exact ⟨digest, receipt, binding⟩

end BeaconcryptCore.Computational.RegistrationNativePlatformTokenCacheSource

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformTokenCacheSource.authentication' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformTokenCacheSource.authentication

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformTokenCacheSource.authenticated_cache' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformTokenCacheSource.authenticated_cache
