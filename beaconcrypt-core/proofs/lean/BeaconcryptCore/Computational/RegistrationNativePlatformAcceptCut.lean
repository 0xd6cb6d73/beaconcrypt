-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformSourceAccept
import BeaconcryptCore.Computational.RegistrationNativePlatformHashReceipt

/-! Actual successful source acceptance reaches the recomputed pin and mandatory Init authentication before replay, reservation, agreement or retention. The receipt retains both native and external states at those literal calls. It does not identify the recomputed pin with the stored pin without the separate reached cache receipt. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformAcceptCut
open PqxdhServerAuthExperiment (Setup Codec Checks)
open RegistrationServerFrontendCompiler (State)
variable {n : Nat} {Platform ι KemSK Reader Response : Type} {base : OracleSpec ι}

attribute [local irreducible] RegistrationNativePlatformSourceBuild.pin
  RegistrationNativePlatformSourceAccept.authenticate RegistrationNativePlatformServerSdk.afterAuthentication

structure Cut (coins : QueryImpl unifSpec (StateT Platform ProbComp))
    (setup : Setup base KemSK) (codec : Codec Reader Response) (checks : Checks)
    (reserve : StateT Platform ProbComp Bool) (route : RawCtxServerRouting.SenderDecoder) (verify : MldsaTranscriptAuth.Verify)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created Unit)
    (packet : registration.InitPacket) (before after : State n) (previous next : Platform) (handle : Nat) where
  pin : session.ServerAuthenticationPin
  pinned : State n
  pinPlatform : Platform
  events : List BeaconcryptCore.Refinement.RegistrationAuthenticationFlow.Event
  authenticated : registration.AuthenticatedInit
  checked : State n
  authPlatform : Platform
  pinCalled : ((.ok (.Some pin), pinned), pinPlatform) ∈ support
    (((RegistrationNativePlatformSourceBuild.pin coins).run before).run previous)
  authCalled : ((.ok (events, .Accepted authenticated), checked), authPlatform) ∈ support
    (((RegistrationNativePlatformSourceAccept.authenticate coins setup codec route verify pin packet).run pinned).run pinPlatform)
  continued : ((.ok (some handle), after), next) ∈ support
    (((RegistrationNativePlatformServerSdk.afterAuthentication coins setup checks (StateT.lift reserve)
      representation created packet authenticated).run checked).run authPlatform)

/-- Every literal successful actual source acceptance supplies its own reached pin, mandatory authentication and later same-run source continuation. -/
theorem accept (coins : QueryImpl unifSpec (StateT Platform ProbComp))
    (setup : Setup base KemSK) (codec : Codec Reader Response) (checks : Checks)
    (reserve : StateT Platform ProbComp Bool) (route : RawCtxServerRouting.SenderDecoder) (verify : MldsaTranscriptAuth.Verify)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created Unit)
    (packet : registration.InitPacket) (before after : State n) (previous next : Platform) (handle : Nat)
    (supported : ((.ok (some handle), after), next) ∈ support
      (((RegistrationNativePlatformSourceAccept.accept coins setup codec checks reserve route verify representation created packet).run before).run previous)) :
    Nonempty (Cut coins setup codec checks reserve route verify representation created packet before after previous next handle) := by
  simp only [RegistrationNativePlatformSourceAccept.accept, RegistrationNativePlatformSourceAccept.acceptWith,
    StateT.run_bind, mem_support_bind_iff] at supported
  obtain ⟨⟨⟨pinReply, pinned⟩, pinPlatform⟩, pinCalled, continued⟩ := supported
  cases pinReply with
  | fail error | div => simp [RegistrationNativePlatformSourceAccept.afterPin, StateT.run_pure] at continued
  | ok optional => cases optional with
    | none => simp [RegistrationNativePlatformSourceAccept.afterPin, StateT.run_pure] at continued
    | some pin =>
      simp only [RegistrationNativePlatformSourceAccept.afterPin, StateT.run_bind, mem_support_bind_iff] at continued
      obtain ⟨⟨⟨authReply, checked⟩, authPlatform⟩, authCalled, later⟩ := continued
      cases authReply with
      | fail error | div => simp [StateT.run_pure] at later
      | ok pair =>
        rcases pair with ⟨events, status⟩
        cases status with
        | Accepted authenticated => exact ⟨⟨pin, pinned, pinPlatform, events, authenticated, checked, authPlatform, pinCalled, authCalled, later⟩⟩
        | _ => simp [StateT.run_pure] at later

/-- A reached stored-pin hash receipt identifies both the actual recomputed pin and the pin retained at its real poststate. -/
theorem pin_fields (coins : QueryImpl unifSpec (StateT Platform ProbComp))
    (setup : Setup base KemSK) (codec : Codec Reader Response) (checks : Checks)
    (reserve : StateT Platform ProbComp Bool) (route : RawCtxServerRouting.SenderDecoder) (verify : MldsaTranscriptAuth.Verify)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created Unit)
    (packet : registration.InitPacket) (before after : State n) (previous next : Platform) (handle : Nat)
    (cut : Cut coins setup codec checks reserve route verify representation created packet before after previous next handle)
    (cached : RegistrationNativeServerPinRecompute.Cached before.pin before.world.world.1.primitive.2) :
    cut.pin = before.pin ∧ cut.pinned.pin = before.pin := by
  have called := cut.pinCalled
  rw [RegistrationNativePlatformSourceBuild.pin_hit coins before cached] at called
  simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at called
  have answer := congrArg (fun result => result.1.1) called
  have samePin : cut.pin = before.pin := by simpa only [RustM.ok.injEq, Option.some.injEq] using answer
  have sameStored : cut.pinned.pin = before.pin := congrArg (fun result => result.1.2.pin) called
  exact ⟨samePin, sameStored⟩

attribute [local irreducible] RegistrationServerNativeSource.authenticate

/-- The actual mandatory source authentication cut is the original native authentication body at the actual reached state, once the earlier stored-pin cache receipt is supplied. -/
theorem authentication (coins : QueryImpl unifSpec (StateT Platform ProbComp))
    (setup : Setup base KemSK) (codec : Codec Reader Response) (checks : Checks)
    (reserve : StateT Platform ProbComp Bool) (route : RawCtxServerRouting.SenderDecoder) (verify : MldsaTranscriptAuth.Verify)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created Unit)
    (packet : registration.InitPacket) (before after : State n) (previous next : Platform) (handle : Nat)
    (cut : Cut coins setup codec checks reserve route verify representation created packet before after previous next handle)
    (cached : RegistrationNativeServerPinRecompute.Cached before.pin before.world.world.1.primitive.2) :
    (.ok (cut.events, .Accepted cut.authenticated), cut.checked) ∈ support
      ((RegistrationServerNativeSource.authenticate setup codec route verify created packet).run cut.pinned) := by
  obtain ⟨samePin, sameStored⟩ := pin_fields coins setup codec checks reserve route verify representation created packet before after previous next handle cut cached
  have called := cut.authCalled
  rw [samePin.trans sameStored.symm, RegistrationNativePlatformSourceAccept.authenticate_stored coins setup codec route verify created packet cut.pinned] at called
  exact RegistrationNativePlatformHashReceipt.native_support coins _ _ cut.pinPlatform cut.authPlatform called

end BeaconcryptCore.Computational.RegistrationNativePlatformAcceptCut

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformAcceptCut.accept' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformAcceptCut.accept

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformAcceptCut.pin_fields' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformAcceptCut.pin_fields

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformAcceptCut.authentication' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformAcceptCut.authentication
