-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformCtxAccept
import BeaconcryptCore.Computational.RegistrationNativeEdOrigin
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxAcceptCandidate
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhEd25519EufCma (acceptPhase1Candidate)
open RegistrationServerFrontendCompiler (State)
variable {n : Nat} {I KemSK Reader Response Platform : Type} {base : OracleSpec I}
variable (setup : Setup base KemSK) (codec : Codec Reader Response)
variable (shortRejects : ∀ (publicKey : PqxdhEd25519EufCma.Ed25519PublicKey) bytes, bytes.length < 64 →
  setup.source.crypto.verify publicKey.toList bytes = none)
variable (route : RawCtxServerRouting.SenderDecoder) (verify : MldsaTranscriptAuth.Verify)
variable (packet : registration.InitPacket)
private theorem map_apply {S X Y : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (f : X → Y) (work : StateT S m X) (before : S) :
    (f <$> work) before = Prod.map f id <$> work before := StateT.run_map f work before
private theorem lift_apply {S X : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (work : m X) (before : S) :
    (StateT.lift work : StateT S m X) before = (fun value => (value, before)) <$> work := bind_pure_comp _ _
attribute [local irreducible] RegistrationWorldAuthentication.begin
include shortRejects in
private theorem authentication (pin : session.ServerAuthenticationPin) (before after : State n)
    (previous current : Platform) (events : List BeaconcryptCore.Refinement.RegistrationAuthenticationFlow.Event)
    (authenticated : registration.AuthenticatedInit)
    (supported : ((.ok (events, .Accepted authenticated), after), current) ∈ support
      (((RegistrationNativePlatformSourceAccept.authenticate RegistrationNativePlatformMldsaProgram.coins
        setup codec route verify pin packet).run before).run previous)) :
    acceptPhase1Candidate setup.joint.verify (RegistrationRootInput.candidate packet) =
      some (RegistrationRootInput.identity authenticated.registration, RegistrationRootInput.keys authenticated.registration) := by
  simp only [RegistrationNativePlatformSourceAccept.authenticate, StateT.run,
    RegistrationNativePlatformMldsaProgram.lift_coins, map_apply, lift_apply,
    Functor.map_map, support_map] at supported
  obtain ⟨result, reached, equal⟩ := supported
  have output := congrArg (fun result => result.1.1) equal
  change result.1 = .ok (events, .Accepted authenticated) at output
  have sameResult : result = (.ok (events, .Accepted authenticated), result.2) := Prod.ext output rfl
  rw [sameResult] at reached
  exact RegistrationNativeEdOrigin.accepted_detached setup codec shortRejects route verify pin packet
    before.world.world.1 result.2 events authenticated reached
include shortRejects in
/-- Success of the literal corrected after-pin controller implies detached phase-one validation, without any owner or key-created condition. -/
theorem after_pin (checks : Checks)
    (reserve : StateT (State n) (StateT Platform ProbComp) Bool)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (pinResult : RustM (core.option.Option session.ServerAuthenticationPin)) (tokenIndex : Nat)
    (before after : State n) (previous current : Platform)
    (supported : ((.ok (some tokenIndex), after), current) ∈ support
      (((RegistrationNativePlatformSourceAccept.afterPin RegistrationNativePlatformMldsaProgram.coins setup codec checks reserve route verify
        representation created packet pinResult).run before).run previous)) :
    ∃ identity decoded, acceptPhase1Candidate setup.joint.verify (RegistrationRootInput.candidate packet) = some (identity, decoded) := by
  cases pinResult with
  | fail error | div => simp only [RegistrationNativePlatformSourceAccept.afterPin, StateT.run_pure, mem_support_pure_iff] at supported; cases supported
  | ok selected => cases selected with
    | none => simp only [RegistrationNativePlatformSourceAccept.afterPin, StateT.run_pure, mem_support_pure_iff] at supported; cases supported
    | some pin =>
        simp only [RegistrationNativePlatformSourceAccept.afterPin, StateT.run_bind, mem_support_bind_iff] at supported
        obtain ⟨⟨⟨checked, afterAuth⟩, afterPlatform⟩, reached, supported⟩ := supported
        cases result : checked with
        | fail error | div => simp only [result, StateT.run_pure, mem_support_pure_iff] at supported; cases supported
        | ok checkedResult => rcases checkedResult with ⟨events, status⟩; cases status with
          | HashRequested _ | Ed25519VerificationRequested _ | Rejected => simp only [result, StateT.run_pure, mem_support_pure_iff] at supported; cases supported
          | Accepted authenticated =>
              refine ⟨_, _, authentication setup codec shortRejects route verify packet pin before afterAuth previous afterPlatform events authenticated ?_⟩
              simpa only [result] using reached
include shortRejects in
/-- Every successful actual source accept has a detached phase-one candidate; the common persistent platform state and all pin/reservation/authentication prefixes are retained. -/
theorem source_accept (checks : Checks) (reserve : StateT Platform ProbComp Bool)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (tokenIndex : Nat) (before after : State n) (previous current : Platform)
    (supported : ((.ok (some tokenIndex), after), current) ∈ support
      (((RegistrationNativePlatformSourceAccept.accept RegistrationNativePlatformMldsaProgram.coins setup codec checks reserve route verify
        representation created packet).run before).run previous)) :
    ∃ identity decoded, acceptPhase1Candidate setup.joint.verify (RegistrationRootInput.candidate packet) = some (identity, decoded) := by
  simp only [RegistrationNativePlatformSourceAccept.accept, RegistrationNativePlatformSourceAccept.acceptWith,
    StateT.run_bind, mem_support_bind_iff] at supported
  obtain ⟨pin, _recomputed, supported⟩ := supported
  exact after_pin setup codec shortRejects route verify packet checks (StateT.lift reserve) representation created
    pin.1.1 tokenIndex pin.1.2 after pin.2 current supported
attribute [local irreducible] RegistrationNativePlatformCtxContext.realize
  RegistrationNativePlatformCtxContext.interpret RegistrationNativePlatformCtxAccept.accept
include shortRejects codec route in
/-- The literal Context accept interpreter has the same unrestricted candidate conclusion at successful public acceptance. -/
theorem accepted (checks : Checks) (reserve : StateT Platform ProbComp Bool)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (tokenIndex : Nat) (before after : RegistrationNativePlatformCtxContext.Full n KemSK Platform)
    (supported : (.ok (some tokenIndex), after) ∈ support
      ((RegistrationNativePlatformCtxContext.interpret
        (RegistrationNativePlatformCtxAccept.accept setup checks reserve verify representation created packet)).run before)) :
    ∃ identity decoded, acceptPhase1Candidate setup.joint.verify (RegistrationRootInput.candidate packet) = some (identity, decoded) := by
  have mapped : (.ok (some tokenIndex), RegistrationNativePlatformCtxContext.realize after) ∈ support
      (Prod.map id RegistrationNativePlatformCtxContext.realize <$>
        (RegistrationNativePlatformCtxContext.interpret
          (RegistrationNativePlatformCtxAccept.accept setup checks reserve verify representation created packet)).run before) :=
    by
      rw [support_map]
      exact Set.mem_image_of_mem _ supported
  rw [RegistrationNativePlatformCtxAccept.accept_source setup codec checks reserve route verify representation created packet before] at mapped
  simp only [RegistrationNativePlatformCtxBuild.nativeServer, StateT.run, support_map] at mapped
  obtain ⟨result, reached, equal⟩ := mapped
  have same := congrArg Prod.fst equal
  change result.1.1 = .ok (some tokenIndex) at same
  have sameResult : result = ((.ok (some tokenIndex), result.1.2), result.2) := Prod.ext (Prod.ext same rfl) rfl
  rw [sameResult] at reached
  exact source_accept setup codec shortRejects route verify packet checks reserve representation created tokenIndex
    (RegistrationNativePlatformCtxAccept.increment (RegistrationNativePlatformCtxContext.realize before)).1.server
    result.1.2 (RegistrationNativePlatformCtxAccept.increment (RegistrationNativePlatformCtxContext.realize before)).2 result.2 reached
end BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxAcceptCandidate

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxAcceptCandidate.after_pin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxAcceptCandidate.after_pin
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxAcceptCandidate.source_accept' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxAcceptCandidate.source_accept
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxAcceptCandidate.accepted' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxAcceptCandidate.accepted
