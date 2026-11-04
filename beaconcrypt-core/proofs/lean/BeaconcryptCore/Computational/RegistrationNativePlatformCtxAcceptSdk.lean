-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformCtxAcceptAuthentication
/-! The literal SDK source acceptance uses repeated pin hashing, mandatory authentication, replay, actual shared reservation, source agreement and one-use insertion through the same physical CTX backend. Every primitive cache frame is derived; no public root-reference state or whole-controller law occurs. -/
open OracleComp OracleSpec CoreModels Aeneas beaconcrypt_core
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformCtxAcceptSdk
open PqxdhServerAuthExperiment (Setup Codec Checks)
open RegistrationServerFrontendCompiler (State)
open RegistrationNativePlatformCtxRunner (M publicWork)
open RegistrationNativePlatformCtxSdkCoupling (Coupled Native pure_source bind_source)
open RegistrationNativePlatformCtxAcceptFrame (ordinary ordinary_source)
variable {n : Nat} {I KemSK Reader Response Platform : Type} {base : OracleSpec I}

private def consumed {m : Type → Type} [Monad m] (authenticated : registration.AuthenticatedInit) : StateT (State n) m Bool :=
  fun before => pure (before.consumed.contains (RegistrationReplaySchedule.identifier authenticated), before)

private theorem state_pure_apply {S X : Type} {m : Type → Type} [Monad m]
    (value : X) (before : S) : (pure value : StateT S m X) before = pure (value, before) := rfl
private theorem state_bind_apply {S X Y : Type} {m : Type → Type} [Monad m]
    (work : StateT S m X) (next : X → StateT S m Y) (before : S) :
    (work >>= next) before = (do let result ← work before; next result.1 result.2) := rfl

private theorem state_get_apply {S : Type} {m : Type → Type} [Monad m] (before : S) :
    (get : StateT S m S) before = pure (before, before) := rfl

private theorem consumed_source (authenticated : registration.AuthenticatedInit) :
    Coupled (consumed (n := n) authenticated : M (State n) Platform Bool) (consumed authenticated) := by
  intro before
  simp only [RegistrationNativePlatformCtxRunner.interpret, consumed, StateT.run, state_pure_apply, simulateQ_pure, map_pure,
    RegistrationNativePlatformPackedState.pack, RegistrationNativePlatformCtxSdkCoupling.realize, Prod.map_def, id_eq]
  rfl

noncomputable def afterAuthentication (setup : Setup base KemSK) (checks : Checks) (reserve : StateT Platform ProbComp Bool)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created Unit)
    (packet : registration.InitPacket) (authenticated : registration.AuthenticatedInit) : M (State n) Platform (RustM (Option Nat)) := do
  let used ← consumed authenticated
  if used then pure (.ok none)
  else do
    let admitted ← publicWork reserve
    if admitted then do
      let completed ← ordinary (RegistrationServerNativeSource.agree setup checks representation created packet authenticated)
      match completed with
      | .fail error => pure (.fail error)
      | .div => pure .div
      | .ok (.ServerComplete accepted) => ordinary (RegistrationServerNativeSource.retain created accepted)
      | .ok _ => pure (.ok none)
    else pure (.ok none)

attribute [local irreducible] RegistrationServerNativeSource.agree RegistrationServerNativeSource.retain ordinary

/-- Replay rejection, actual reservation poststate, source agreement and one-use retention agree on every outcome. -/
theorem afterAuthentication_source (setup : Setup base KemSK) (checks : Checks) (reserve : StateT Platform ProbComp Bool)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created Unit)
    (packet : registration.InitPacket) (authenticated : registration.AuthenticatedInit) :
    Coupled (afterAuthentication (n := n) setup checks reserve representation created packet authenticated)
      (RegistrationNativePlatformServerSdk.afterAuthentication RegistrationNativePlatformMldsaProgram.coins setup checks
        (StateT.lift reserve) representation created packet authenticated) := by
  have actual : RegistrationNativePlatformServerSdk.afterAuthentication (n := n) RegistrationNativePlatformMldsaProgram.coins setup checks
      (StateT.lift reserve) representation created packet authenticated = (do
      let used ← consumed authenticated
      if used then pure (.ok none)
      else do
        let admitted ← StateT.lift reserve
        if admitted then do
          let completed ← RegistrationNativePlatformServerSdk.liftNative RegistrationNativePlatformMldsaProgram.coins
            (RegistrationServerNativeSource.agree setup checks representation created packet authenticated)
          match completed with
          | .fail error => pure (.fail error)
          | .div => pure .div
          | .ok (.ServerComplete accepted) =>
              RegistrationNativePlatformServerSdk.liftNative RegistrationNativePlatformMldsaProgram.coins
                (RegistrationServerNativeSource.retain created accepted)
          | .ok _ => pure (.ok none)
        else pure (.ok none)) := by
    funext before
    simp only [RegistrationNativePlatformServerSdk.afterAuthentication, state_bind_apply, state_get_apply, consumed, pure_bind]
    rfl
  rw [actual]
  unfold afterAuthentication
  apply bind_source _ _ _ _ (consumed_source authenticated)
  intro used
  cases used with
  | true => exact pure_source _
  | false =>
    apply bind_source _ _ _ _ (RegistrationNativePlatformCtxSdk.reserve_source reserve)
    intro admitted
    cases admitted with
    | false => exact pure_source _
    | true =>
      apply bind_source _ _ _ _ (ordinary_source _ (RegistrationNativePlatformCtxAcceptFrame.agree setup checks representation created packet authenticated))
      intro completed
      cases completed with
      | fail error | div => exact pure_source _
      | ok effect => cases effect <;> first
        | exact pure_source _
        | exact ordinary_source _ (RegistrationNativePlatformCtxAcceptFrame.retain created _)

noncomputable def afterPin (setup : Setup base KemSK) (checks : Checks) (reserve : StateT Platform ProbComp Bool)
    (verify : MldsaTranscriptAuth.Verify) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (packet : registration.InitPacket)
    (result : RegistrationNativeServerPinRecompute.PinReply) : M (State n) Platform (RustM (Option Nat)) :=
  match result with
  | .fail error => pure (.fail error)
  | .div => pure .div
  | .ok .None => pure (.ok none)
  | .ok (.Some pin) => do
      let checked ← RegistrationNativePlatformCtxAcceptAuthentication.authenticate setup verify pin packet
      match checked with
      | .fail error => pure (.fail error)
      | .div => pure .div
      | .ok (_events, .Accepted authenticated) => afterAuthentication setup checks reserve representation created packet authenticated
      | .ok _ => pure (.ok none)

/-- Every incoming authentication and optional failure branch reaches the same actual source continuation. -/
theorem afterPin_source (setup : Setup base KemSK) (codec : Codec Reader Response) (checks : Checks) (reserve : StateT Platform ProbComp Bool)
    (route : RawCtxServerRouting.SenderDecoder) (verify : MldsaTranscriptAuth.Verify)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created Unit)
    (packet : registration.InitPacket) (result : RegistrationNativeServerPinRecompute.PinReply) :
    Coupled (afterPin (n := n) setup checks reserve verify representation created packet result)
      (RegistrationNativePlatformSourceAccept.afterPin RegistrationNativePlatformMldsaProgram.coins setup codec checks (StateT.lift reserve)
        route verify representation created packet result) := by
  unfold afterPin RegistrationNativePlatformSourceAccept.afterPin
  cases result with
  | fail error | div => exact pure_source _
  | ok selected => cases selected with
    | none => exact pure_source _
    | some pin =>
      apply bind_source _ _ _ _ (RegistrationNativePlatformCtxAcceptAuthentication.authenticate_source setup codec route verify pin packet)
      intro checked
      cases checked with
      | fail error | div => exact pure_source _
      | ok pair =>
        rcases pair with ⟨events, verdict⟩
        cases verdict <;> first
          | exact pure_source _
          | exact afterAuthentication_source setup checks reserve representation created packet _

noncomputable def accept (setup : Setup base KemSK) (checks : Checks) (reserve : StateT Platform ProbComp Bool)
    (verify : MldsaTranscriptAuth.Verify) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (packet : registration.InitPacket) : M (State n) Platform (RustM (Option Nat)) := do
  let current ← RegistrationNativePlatformCtxSdk.pin
  afterPin setup checks reserve verify representation created packet current

/-- Complete actual source acceptance has a physical CTX realization without a root-reference or whole-handler premise. -/
theorem accept_source (setup : Setup base KemSK) (codec : Codec Reader Response) (checks : Checks) (reserve : StateT Platform ProbComp Bool)
    (route : RawCtxServerRouting.SenderDecoder) (verify : MldsaTranscriptAuth.Verify)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created Unit)
    (packet : registration.InitPacket) :
    Coupled (accept (n := n) setup checks reserve verify representation created packet)
      (RegistrationNativePlatformSourceAccept.accept RegistrationNativePlatformMldsaProgram.coins setup codec checks reserve
        route verify representation created packet) := by
  unfold accept RegistrationNativePlatformSourceAccept.accept RegistrationNativePlatformSourceAccept.acceptWith
  exact bind_source _ _ _ _ RegistrationNativePlatformCtxSdk.pin_source
    (afterPin_source setup codec checks reserve route verify representation created packet)

end BeaconcryptCore.Computational.RegistrationNativePlatformCtxAcceptSdk

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformCtxAcceptSdk.afterAuthentication_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformCtxAcceptSdk.afterAuthentication_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformCtxAcceptSdk.afterPin_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformCtxAcceptSdk.afterPin_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformCtxAcceptSdk.accept_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformCtxAcceptSdk.accept_source
