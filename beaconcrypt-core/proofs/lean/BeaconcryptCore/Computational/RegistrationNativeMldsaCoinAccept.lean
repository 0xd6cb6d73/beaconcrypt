-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeMldsaCoinAcceptPrimitives

/-! Actual Server SDK acceptance has a source-derived ordinary-uniform bill from authentication, private replay lookup, allocator gates and native agreement. Only the actual KEM encapsulation algorithm's draw cap is supplied. Every failed prefix and the native parsed-attempt counter remain in the original execution; no callback frame or successful-authentication premise is introduced. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeMldsaCoinAccept
attribute [local irreducible] RegistrationWorldAuthentication.begin RegistrationAuthenticationExecutor.execute
  registration.begin_init_authentication RegistrationServerNativeSource.authenticate
  RegistrationServerSdkSource.afterAuthentication RegistrationNativeExperiment.handler
open PqxdhServerAuthExperiment (Setup Codec Checks)
variable {n : Nat} {ι KemSK Reader Response : Type} {base : OracleSpec ι}

def bill (qEncap : Nat) := 512 + 9 * (32 + qEncap)

private theorem state_bind_apply {S X Y : Type} {m : Type → Type} [Monad m]
    (work : StateT S m X) (next : X → StateT S m Y) (before : S) :
    (work >>= next) before = (do let result ← work before; next result.1 result.2) := rfl

private theorem state_modify_apply {S : Type} {m : Type → Type} [Monad m]
    (change : S → S) (before : S) : (modify change : StateT S m Unit) before = pure ((), change before) := rfl

/-- Actual authentication is the same512-draw source bound under the SDK's retained state lens. -/
theorem authenticate (setup : Setup base KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (verify : MldsaTranscriptAuth.Verify)
    (created : PqxdhLiveServerConstruction.Created Unit) (packet : registration.InitPacket)
    (before : RegistrationServerFrontendCompiler.State n) :
    ((RegistrationServerNativeSource.authenticate setup codec route verify created packet).run before).IsTotalQueryBound 512 := by
  simpa only [RegistrationServerNativeSource.authenticate, RegistrationServerNativeSource.sourceStep,
    RegistrationWorldServerFrontend.authenticate, RegistrationServerFrontendCompiler.restore, StateT.run,
    IsTotalQueryBound, isQueryBound_map_iff] using
    RegistrationNativeMldsaCoinAcceptPrimitives.authentication setup codec route verify before.pin packet before.world.world.1

private theorem retain (created : PqxdhLiveServerConstruction.Created Unit) (accepted : agreement.ServerAgreement)
    (before : RegistrationServerFrontendCompiler.State n) :
    ((RegistrationServerNativeSource.retain created accepted).run before).IsTotalQueryBound 0 := by
  simp only [RegistrationServerNativeSource.retain, RegistrationServerNativeSource.sourceStep,
    RegistrationWorldServerFrontend.retain, RegistrationServerFrontendCompiler.restore, StateT.run]
  cases RegistrationReplaySchedule.consume accepted before.consumed with
  | fail error | div => trivial
  | ok result => rcases result with ⟨option, history⟩; cases option <;> trivial

private theorem afterAuthentication (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created Unit)
    (qEncap : Nat) (encapsulation : ∀ key, (simulateQ (PqxdhInitializerSecrecy.kemAmbientImpl setup.baseImpl)
      (setup.kem.encaps key)).IsTotalQueryBound qEncap)
    (packet : registration.InitPacket) (authenticated : registration.AuthenticatedInit)
    (before : RegistrationServerFrontendCompiler.State n) :
    ((RegistrationServerSdkSource.afterAuthentication setup checks representation created packet authenticated).run before).IsTotalQueryBound
      (9 * (32 + qEncap)) := by
  simp only [RegistrationServerSdkSource.afterAuthentication, StateT.run]
  split
  · trivial
  · split
    · apply isTotalQueryBound_bind (n₂ := 0)
        (RegistrationNativeMldsaCoinAcceptPrimitives.agreement_bound setup checks representation created qEncap encapsulation packet authenticated before)
      intro result
      cases result.1 with
      | fail error | div => trivial
      | ok effect => cases effect <;> first
        | exact retain created _ result.2
        | trivial
    · trivial

/-- All actual SDK accept outcomes pay at most authentication512 plus nine native agreement slots; only the encapsulation primitive cap is assumed. -/
theorem accept (setup : Setup base KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (verify : MldsaTranscriptAuth.Verify)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created Unit)
    (qEncap : Nat) (encapsulation : ∀ key, (simulateQ (PqxdhInitializerSecrecy.kemAmbientImpl setup.baseImpl)
      (setup.kem.encaps key)).IsTotalQueryBound qEncap)
    (packet : registration.InitPacket) (before : RegistrationServerFrontendCompiler.State n) :
    ((RegistrationServerSdkSource.accept setup codec checks route verify representation created packet).run before).IsTotalQueryBound (bill qEncap) := by
  simp only [RegistrationServerSdkSource.accept, StateT.run_bind, bill]
  apply isTotalQueryBound_bind (n₁ := 512) (n₂ := 9 * (32 + qEncap))
    (authenticate setup codec route verify created packet before)
  intro result
  cases result.1 with
  | fail error | div => trivial
  | ok checked =>
      rcases checked with ⟨events, checked⟩
      cases checked <;> first
        | exact afterAuthentication setup checks representation created qEncap encapsulation packet _ result.2
        | trivial

/-- The actual free typed accept callback retains that source-derived bill, including its parsed-attempt update. -/
theorem handler (source : RegistrationNativeMldsa.Source) (setup : Setup base KemSK) (checks : Checks)
    (wire : RegistrationNativeWire.Wire) (route : RawCtxServerRouting.SenderDecoder)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created Unit)
    (credential : RegistrationNativeMldsa.Credential source) (qEncap : Nat)
    (encapsulation : ∀ key, (simulateQ (PqxdhInitializerSecrecy.kemAmbientImpl setup.baseImpl)
      (setup.kem.encaps key)).IsTotalQueryBound qEncap)
    (packet : registration.InitPacket) (before : RegistrationNativeExperiment.State n KemSK source) :
    ((RegistrationNativeMldsaProfile.handler setup checks wire route representation created credential (.inr (.accept packet))).run before).IsQueryBoundP
      RegistrationNativeMldsaCoinPrimitives.IsCoin (bill qEncap) := by
  apply RegistrationNativeMldsaCoinPrimitives.ordinary _ (bill qEncap)
  simp only [RegistrationNativeExperiment.handler, StateT.run, state_bind_apply, state_modify_apply,
    pure_bind, RegistrationNativeExperiment.server, IsTotalQueryBound, isQueryBound_map_iff]
  exact accept setup (RegistrationNativeWire.ledgerCodec wire) checks route source.verify representation created
    qEncap encapsulation packet before.server
end BeaconcryptCore.Computational.RegistrationNativeMldsaCoinAccept

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaCoinAccept.authenticate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaCoinAccept.authenticate

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaCoinAccept.accept' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaCoinAccept.accept

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaCoinAccept.handler' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaCoinAccept.handler
