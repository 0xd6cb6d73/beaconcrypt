-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformSourceAccept
import BeaconcryptCore.Computational.RegistrationStateView
import BeaconcryptCore.Computational.RegistrationNativeServerViewAccept
/-! Corrected source acceptance ignores only the named native-call, Env-coin and request-marker instrumentation. True uniform counts, shared cache, protocol state and arbitrary common platform effects remain in both runs. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformSourceAcceptMetricView
open PqxdhServerAuthExperiment (Setup Checks Codec)
open RegistrationServerFrontendCompiler (State)
open RegistrationServerMaterialSourceState (nativeView)
open RegistrationStateView (Stable pure_stable bind_stable)
variable {n : Nat} {I KemSK Reader Response A : Type} {base : OracleSpec I}
variable {m : Type → Type} [Monad m] [LawfulMonad m]

attribute [local irreducible] RegistrationServerNativeSource.agree RegistrationServerNativeSource.retain RegistrationWorldAuthentication.begin

private theorem closed (coins : QueryImpl unifSpec m) (work : StateT (State n) ProbComp A)
    (stable : RegistrationStateView.Stable nativeView work) :
    Stable nativeView (RegistrationNativePlatformServerSdk.liftNative coins work) := by
  intro before
  have compared := congrArg (simulateQ coins) (stable before)
  simpa only [RegistrationNativePlatformServerSdk.liftNative, StateT.run, simulateQ_map] using compared

private noncomputable def inWorld (coins : QueryImpl unifSpec m)
    (work : StateT (PqxdhRecordLiftWorld.State n) ProbComp A) : StateT (State n) m A := fun before =>
  (fun result => (result.1, { before with world := {before.world with world := (result.2, before.world.world.2)} })) <$>
    simulateQ coins (work.run before.world.world.1)

private theorem world_stable (coins : QueryImpl unifSpec m)
    (work : StateT (PqxdhRecordLiftWorld.State n) ProbComp A)
    (stable : RegistrationStateView.Stable RegistrationNativeWorldView.project work) :
    Stable nativeView (inWorld coins work) := by
  intro before
  have compared := congrArg (simulateQ coins) (stable before.world.world.1)
  have mapped := congrArg (fun action => (fun result => (result.1,
    {nativeView before with world := {(nativeView before).world with world := (result.2, before.world.world.2)}})) <$> action) compared
  simpa only [inWorld, StateT.run, simulateQ_map, Functor.map_map, nativeView,
    RegistrationServerRecordWorldSource.project, Prod.map_def, id_eq, Function.comp_def,
    RegistrationNativeWorldView.project_idempotent] using mapped

private theorem pin_native (binding : pqxdh.ServerBinding) (key : Std.Array U8 1952#usize) :
    RegistrationStateView.Stable (RegistrationNativeWorldView.project (n := n))
      (RegistrationNativeServerPinRecompute.native binding key) := by
  intro before
  rw [RegistrationNativeServerPinRecompute.native_run, RegistrationNativeServerPinRecompute.native_run]
  have compared := congrArg (fun action => (fun result =>
    ((.ok (.Some (⟨binding, key, RegistrationAuthenticationShared.digestArray result.1⟩ : session.ServerAuthenticationPin)) : RegistrationNativeServerPinRecompute.PinReply), result.2)) <$> action)
    (RegistrationNativeWorldViewEffects.effects_input (.inr (.hash (PqxdhRefinement.absBytes key))) before)
  simpa only [bind_pure_comp, Functor.map_map, Prod.map_def, id_eq] using compared

omit [LawfulMonad m] in
private theorem pin_apply (coins : QueryImpl unifSpec m) (before : State n) :
    (RegistrationNativePlatformSourceBuild.pin coins) before =
      inWorld coins (RegistrationNativeServerPinRecompute.native before.pin.binding before.pin.public_key) before := rfl
private theorem pin_field (before : State n) : (nativeView before).pin = before.pin := rfl

/-- The actual repeated pin hash keeps its full sampler and reached public/native state under the named instrumentation view. -/
theorem pin (coins : QueryImpl unifSpec m) :
    Stable (nativeView (n := n)) (RegistrationNativePlatformSourceBuild.pin coins) := by
  intro before
  change Prod.map id nativeView <$> (RegistrationNativePlatformSourceBuild.pin coins) before =
    Prod.map id nativeView <$> (RegistrationNativePlatformSourceBuild.pin coins) (nativeView before)
  rw [pin_apply, pin_apply, pin_field]
  exact world_stable coins (RegistrationNativeServerPinRecompute.native before.pin.binding before.pin.public_key)
    (pin_native before.pin.binding before.pin.public_key) before

/-- Mandatory incoming authentication retains true uniforms and the entire shared cache in this view. -/
theorem authentication (coins : QueryImpl unifSpec m) (setup : Setup base KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (verify : MldsaTranscriptAuth.Verify)
    (pin : session.ServerAuthenticationPin) (packet : registration.InitPacket) :
    Stable (nativeView (n := n)) (RegistrationNativePlatformSourceAccept.authenticate coins setup codec route verify pin packet) :=
  world_stable coins _ (RegistrationNativeWorldViewAuthentication.begin_input setup codec route verify pin packet)

private def consumed : StateT (State n) m RegistrationReplaySchedule.State := fun before => pure (before.consumed, before)
private theorem consumed_stable : Stable nativeView (consumed (n := n) (m := m)) := by
  intro before
  simp only [consumed, StateT.run, map_pure, nativeView,
    RegistrationNativeLocalView.project_idempotent, Prod.map_def, id_eq]
private theorem external_stable (work : m A) : Stable (nativeView (n := n)) (StateT.lift work) := by
  intro before
  simp only [StateT.run_lift, map_bind, map_pure, nativeView, RegistrationNativeLocalView.project_idempotent, Prod.map_def, id_eq]

omit [LawfulMonad m] in
private theorem bind_apply {S X Y : Type} (work : StateT S m X) (next : X → StateT S m Y) (before : S) :
    (work >>= next) before = (do let result ← work before; next result.1 result.2) := rfl
omit [LawfulMonad m] in
private theorem get_apply {S : Type} (before : S) : (get : StateT S m S) before = pure (before, before) := rfl
omit [LawfulMonad m] in
private theorem pure_apply {S X : Type} (value : X) (before : S) : (pure value : StateT S m X) before = pure (value, before) := rfl

private theorem after_shape (coins : QueryImpl unifSpec m) (setup : Setup base KemSK) (checks : Checks) (reserve : m Bool)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created Unit)
    (packet : registration.InitPacket) (authenticated : registration.AuthenticatedInit) :
    RegistrationNativePlatformServerSdk.afterAuthentication (n := n) coins setup checks (StateT.lift reserve) representation created packet authenticated = (do
      let history ← consumed
      if history.contains (RegistrationReplaySchedule.identifier authenticated) then pure (.ok none)
      else do
        let allowed ← StateT.lift reserve
        if allowed then do
          let agreed ← RegistrationNativePlatformServerSdk.liftNative coins (RegistrationServerNativeSource.agree setup checks representation created packet authenticated)
          match agreed with
          | .fail error => pure (.fail error)
          | .div => pure .div
          | .ok (.ServerComplete accepted) => RegistrationNativePlatformServerSdk.liftNative coins (RegistrationServerNativeSource.retain created accepted)
          | .ok _ => pure (.ok none)
        else pure (.ok none)) := by
  funext before
  simp only [RegistrationNativePlatformServerSdk.afterAuthentication, consumed,
    bind_apply, get_apply, pure_bind]
  rfl

private theorem after_authentication (coins : QueryImpl unifSpec m) (setup : Setup base KemSK) (checks : Checks) (reserve : m Bool)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created Unit)
    (packet : registration.InitPacket) (authenticated : registration.AuthenticatedInit) :
    Stable (nativeView (n := n))
      (RegistrationNativePlatformServerSdk.afterAuthentication coins setup checks (StateT.lift reserve) representation created packet authenticated) := by
  rw [after_shape]
  apply bind_stable _ _ _ consumed_stable
  intro history
  split
  · exact pure_stable _ RegistrationNativeServerViewAccept.view_idempotent _
  · apply bind_stable _ _ _ (external_stable reserve)
    intro allowed
    cases allowed with
    | false => exact pure_stable _ RegistrationNativeServerViewAccept.view_idempotent _
    | true =>
      apply bind_stable _ _ _ (closed coins _ (RegistrationNativeServerViewAccept.agree_input setup checks representation created packet authenticated))
      intro agreed
      cases agreed with
      | fail error | div => exact pure_stable _ RegistrationNativeServerViewAccept.view_idempotent _
      | ok effect => cases effect <;> first
        | exact pure_stable _ RegistrationNativeServerViewAccept.view_idempotent _
        | exact closed coins _ (RegistrationNativeServerViewAccept.retain_input created _)

private theorem after_pin (coins : QueryImpl unifSpec m) (setup : Setup base KemSK) (codec : Codec Reader Response)
    (checks : Checks) (reserve : m Bool) (route : RawCtxServerRouting.SenderDecoder) (verify : MldsaTranscriptAuth.Verify)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created Unit)
    (packet : registration.InitPacket) (result : RegistrationNativeServerPinRecompute.PinReply) :
    Stable (nativeView (n := n)) (RegistrationNativePlatformSourceAccept.afterPin coins setup codec checks
      (StateT.lift reserve) route verify representation created packet result) := by
  cases result with
  | fail error | div => exact pure_stable _ RegistrationNativeServerViewAccept.view_idempotent _
  | ok optional => cases optional with
    | none => exact pure_stable _ RegistrationNativeServerViewAccept.view_idempotent _
    | some current =>
      apply bind_stable _ _ _ (authentication coins setup codec route verify current packet)
      intro checked
      cases checked with
      | fail error | div => exact pure_stable _ RegistrationNativeServerViewAccept.view_idempotent _
      | ok pair =>
        rcases pair with ⟨events, verdict⟩
        cases verdict <;> first
          | exact pure_stable _ RegistrationNativeServerViewAccept.view_idempotent _
          | exact after_authentication coins setup checks reserve representation created packet _

/-- Actual complete source acceptance is invariant under instrumentation projection while preserving its complete common-monad effects. -/
theorem accept (coins : QueryImpl unifSpec m) (setup : Setup base KemSK) (codec : Codec Reader Response)
    (checks : Checks) (reserve : m Bool) (route : RawCtxServerRouting.SenderDecoder) (verify : MldsaTranscriptAuth.Verify)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created Unit)
    (packet : registration.InitPacket) :
    Stable (nativeView (n := n)) (RegistrationNativePlatformSourceAccept.accept coins setup codec checks reserve route verify representation created packet) := by
  unfold RegistrationNativePlatformSourceAccept.accept RegistrationNativePlatformSourceAccept.acceptWith
  exact bind_stable _ _ _ (pin coins)
    (after_pin coins setup codec checks reserve route verify representation created packet)
end BeaconcryptCore.Computational.RegistrationNativePlatformSourceAcceptMetricView

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSourceAcceptMetricView.pin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSourceAcceptMetricView.pin

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSourceAcceptMetricView.authentication' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSourceAcceptMetricView.authentication

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSourceAcceptMetricView.accept' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSourceAcceptMetricView.accept
