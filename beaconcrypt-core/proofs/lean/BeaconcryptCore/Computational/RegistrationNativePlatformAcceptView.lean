-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformMldsaCountSdk
import BeaconcryptCore.Computational.RegistrationNativePlatformPinView
import BeaconcryptCore.Computational.RegistrationNativePlatformSourceAccept
import BeaconcryptCore.Computational.RegistrationNativeWorldViewAuthentication
import BeaconcryptCore.Computational.RegistrationNativeKemWorldAuthentication
import BeaconcryptCore.Computational.RegistrationNativeServerViewAccept
import BeaconcryptCore.Computational.RegistrationNativeKemWorldAgreement

/-! Actual source acceptance retains repeated pin hashing and dynamic reservation while ignoring omitted private accounting inputs. All mandatory authentication, agreement, replay and token-retention outcomes are retained at their reached native and platform states. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformAcceptView
open PqxdhServerAuthExperiment (Setup Codec Checks)
open RegistrationNativeMldsaCountServer (serverProject localProject)
open RegistrationNativeKemCounterIndependence (Stable)
open RegistrationNativePlatformMldsaCountRules (Correct)
open RegistrationNativePlatformMldsaProgram (M)
variable {n : Nat} {KemSK Platform Reader Response Value ι : Type} {base : OracleSpec ι} {source : RegistrationNativeMldsa.Source}

private theorem compose_stable {S V : Type} (first second : S → S)
    (commute : ∀ before, first (second before) = second (first before)) (work : StateT S ProbComp V)
    (left : Stable first work) (right : Stable second work) : Stable (fun before => second (first before)) work := by
  intro before
  have initial := congrArg (fun action => Prod.map id second <$> action) (left before)
  have following := congrArg (fun action => Prod.map id first <$> action) (right (first before))
  simp only [Functor.map_map, Prod.map, id_eq] at initial following ⊢
  simp only [commute] at following
  exact initial.trans following

private theorem agree (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (packet : registration.InitPacket) (authenticated : registration.AuthenticatedInit) :
    Stable (serverProject (n := n)) (RegistrationServerNativeSource.agree setup checks representation created packet authenticated) := by
  change Stable (fun before => RegistrationNativeKemServerState.maskServer (RegistrationServerMaterialSourceState.nativeView before)) _
  exact compose_stable RegistrationServerMaterialSourceState.nativeView RegistrationNativeKemServerState.maskServer (fun _ => rfl) _
    (RegistrationNativeServerViewAccept.agree_input setup checks representation created packet authenticated)
    (RegistrationNativeKemWorldAgreement.native_agree_input setup checks representation created packet authenticated)

private theorem retain (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (accepted : agreement.ServerAgreement) :
    Stable (serverProject (n := n)) (RegistrationServerNativeSource.retain created accepted) := by
  change Stable (fun before => RegistrationNativeKemServerState.maskServer (RegistrationServerMaterialSourceState.nativeView before)) _
  exact compose_stable RegistrationServerMaterialSourceState.nativeView RegistrationNativeKemServerState.maskServer (fun _ => rfl) _
    (RegistrationNativeServerViewAccept.retain_input created accepted)
    (RegistrationNativeKemWorldAgreement.native_retain_input created accepted)

private noncomputable def authNative (setup : Setup base KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (verify : MldsaTranscriptAuth.Verify)
    (pin : session.ServerAuthenticationPin) (packet : registration.InitPacket) :
    StateT (RegistrationServerFrontendCompiler.State n) ProbComp
      (RustM (List BeaconcryptCore.Refinement.RegistrationAuthenticationFlow.Event × registration.InitAuthentication)) := fun before =>
  (fun result => (result.1, { before with world := { before.world with world := (result.2, before.world.world.2) } })) <$>
    (RegistrationWorldAuthentication.begin setup codec route verify pin packet).run before.world.world.1

private theorem auth_stable (setup : Setup base KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (verify : MldsaTranscriptAuth.Verify)
    (pin : session.ServerAuthenticationPin) (packet : registration.InitPacket) :
    Stable (serverProject (n := n)) (authNative setup codec route verify pin packet) := by
  have worldStable : Stable (RegistrationNativeMldsaWorldView.project (n := n))
      (RegistrationWorldAuthentication.begin setup codec route verify pin packet) :=
    compose_stable RegistrationNativeWorldView.project RegistrationNativeKemWorldUniform.mask (fun _ => rfl) _
      (RegistrationNativeWorldViewAuthentication.begin_input setup codec route verify pin packet)
      (RegistrationNativeKemWorldAuthentication.begin_input setup codec route verify pin packet)
  intro before
  have same := congrArg (fun action => (fun result => (result.1,
    { serverProject before with world := { (serverProject before).world with world := (result.2, before.world.world.2) } })) <$> action)
    (worldStable before.world.world.1)
  simp only [authNative, serverProject, localProject, StateT.run, Functor.map_map, Prod.map, id_eq] at same ⊢
  exact same

private theorem auth_count (setup : Setup base KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (verify : MldsaTranscriptAuth.Verify)
    (pin : session.ServerAuthenticationPin) (packet : registration.InitPacket) :
    Correct (source := source) (serverProject (n := n))
      (RegistrationNativePlatformMldsaProgram.lift
        (RegistrationNativePlatformSourceAccept.authenticate (m := StateT Platform ProbComp)
          RegistrationNativePlatformMldsaProgram.coins setup codec route verify pin packet)) := by
  have closed : RegistrationNativePlatformSourceAccept.authenticate (n := n)
      (m := StateT Platform ProbComp) RegistrationNativePlatformMldsaProgram.coins setup codec route verify pin packet =
      (fun before => simulateQ RegistrationNativePlatformMldsaProgram.coins ((authNative setup codec route verify pin packet).run before)) := by
    funext before
    simp only [RegistrationNativePlatformSourceAccept.authenticate, authNative, StateT.run, simulateQ_map]
  rw [closed]
  exact RegistrationNativePlatformMldsaCountRules.native serverProject _ (auth_stable setup codec route verify pin packet)

private theorem server_idempotent (before : RegistrationServerFrontendCompiler.State n) : serverProject (serverProject before) = serverProject before := by
  simp only [serverProject, localProject, RegistrationNativeMldsaWorldView.idempotent]
private theorem bind_apply {S X Y : Type} {m : Type → Type} [Monad m]
    (work : StateT S m X) (next : X → StateT S m Y) (before : S) :
    (work >>= next) before = (do let middle ← work before; next middle.1 middle.2) := rfl
private theorem pure_apply {S X : Type} {m : Type → Type} [Monad m]
    (value : X) (before : S) : (pure value : StateT S m X) before = pure (value, before) := rfl
private theorem get_apply {S : Type} {m : Type → Type} [Monad m] (before : S) :
    (get : StateT S m S) before = pure (before, before) := rfl
private theorem lift_pure {S V : Type} (value : V) :
    RegistrationNativePlatformMldsaProgram.lift (source := source) (pure value : StateT S (StateT Platform ProbComp) V) = pure value := by
  funext before previous
  rfl
private theorem lift_bind {S V W : Type} (work : StateT S (StateT Platform ProbComp) V)
    (next : V → StateT S (StateT Platform ProbComp) W) :
    RegistrationNativePlatformMldsaProgram.lift (source := source) (work >>= next) =
      (RegistrationNativePlatformMldsaProgram.lift work >>= fun value => RegistrationNativePlatformMldsaProgram.lift (next value)) := by
  funext before previous
  simp only [RegistrationNativePlatformMldsaProgram.lift, RegistrationNativeMldsaProgram.liftState,
    RegistrationNativeMldsaProgram.lift, StateT.run_bind, simulateQ_bind]
  rfl
private def readConsumed : StateT (RegistrationServerFrontendCompiler.State n) (StateT Platform ProbComp) RegistrationReplaySchedule.State :=
  fun before => pure (before.consumed, before)
private theorem read_count : Correct (source := source) (serverProject (n := n))
    (RegistrationNativePlatformMldsaProgram.lift (readConsumed (Platform := Platform))) := by
  apply RegistrationNativePlatformMldsaCountRules.closed
  intro before
  simp only [RegistrationNativePlatformPackedState.pack, readConsumed, StateT.run, pure_apply, map_pure,
    RegistrationNativePlatformMldsaCountRules.project, Prod.map, id_eq, serverProject, localProject,
    RegistrationNativeMldsaWorldView.idempotent]

attribute [local irreducible] RegistrationServerNativeSource.agree RegistrationServerNativeSource.retain

private theorem after_shape (setup : Setup base KemSK) (checks : Checks) (reserve : StateT Platform ProbComp Bool)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (packet : registration.InitPacket) (authenticated : registration.AuthenticatedInit) :
    RegistrationNativePlatformServerSdk.afterAuthentication (n := n) RegistrationNativePlatformMldsaProgram.coins setup checks (StateT.lift reserve)
      representation created packet authenticated = (do
        let consumed ← readConsumed
        if consumed.contains (RegistrationReplaySchedule.identifier authenticated) then pure (.ok none)
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
  funext before previous
  simp only [RegistrationNativePlatformServerSdk.afterAuthentication, readConsumed, bind_apply, get_apply, pure_apply, pure_bind]
  congr 1

private theorem after_count (setup : Setup base KemSK) (checks : Checks) (reserve : StateT Platform ProbComp Bool)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (packet : registration.InitPacket) (authenticated : registration.AuthenticatedInit) :
    Correct (source := source) (serverProject (n := n))
      (RegistrationNativePlatformMldsaProgram.lift
        (RegistrationNativePlatformServerSdk.afterAuthentication RegistrationNativePlatformMldsaProgram.coins setup checks (StateT.lift reserve)
          representation created packet authenticated)) := by
  rw [after_shape, lift_bind]
  apply RegistrationNativePlatformMldsaCountRules.bind serverProject _ _ read_count
  intro consumed
  split
  · rw [lift_pure]
    exact RegistrationNativePlatformMldsaCountRules.pure serverProject server_idempotent _
  · rw [lift_bind]
    apply RegistrationNativePlatformMldsaCountRules.bind serverProject _ _
      (RegistrationNativePlatformMldsaCountRules.external serverProject server_idempotent reserve)
    intro admitted
    cases admitted with
    | false =>
      simp only [Bool.false_eq_true, ite_false, lift_pure]
      exact RegistrationNativePlatformMldsaCountRules.pure serverProject server_idempotent _
    | true =>
      simp only [ite_true, lift_bind]
      apply RegistrationNativePlatformMldsaCountRules.bind serverProject _ _
        (RegistrationNativePlatformMldsaCountRules.native serverProject _ (agree setup checks representation created packet authenticated))
      intro completed
      cases completed with
      | fail error | div =>
        rw [lift_pure]
        exact RegistrationNativePlatformMldsaCountRules.pure serverProject server_idempotent _
      | ok effect =>
        cases effect
        all_goals first
          | exact RegistrationNativePlatformMldsaCountRules.native serverProject _ (retain created _)
          | rw [lift_pure]
            exact RegistrationNativePlatformMldsaCountRules.pure serverProject server_idempotent _

private theorem afterPin_count (setup : Setup base KemSK) (codec : Codec Reader Response) (checks : Checks)
    (reserve : StateT Platform ProbComp Bool) (route : RawCtxServerRouting.SenderDecoder) (verify : MldsaTranscriptAuth.Verify)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (packet : registration.InitPacket) (pin : RustM (core.option.Option session.ServerAuthenticationPin)) :
    Correct (source := source) (serverProject (n := n))
      (RegistrationNativePlatformMldsaProgram.lift
        (RegistrationNativePlatformSourceAccept.afterPin RegistrationNativePlatformMldsaProgram.coins setup codec checks (StateT.lift reserve)
          route verify representation created packet pin)) := by
  unfold RegistrationNativePlatformSourceAccept.afterPin
  cases pin with
  | fail error | div =>
    rw [lift_pure]
    exact RegistrationNativePlatformMldsaCountRules.pure serverProject server_idempotent _
  | ok optional => cases optional with
    | none =>
      rw [lift_pure]
      exact RegistrationNativePlatformMldsaCountRules.pure serverProject server_idempotent _
    | some pin =>
      rw [lift_bind]
      apply RegistrationNativePlatformMldsaCountRules.bind serverProject _ _ (auth_count setup codec route verify pin packet)
      intro checked
      cases checked with
      | fail error | div =>
        rw [lift_pure]
        exact RegistrationNativePlatformMldsaCountRules.pure serverProject server_idempotent _
      | ok answer =>
        rcases answer with ⟨events, status⟩
        cases status with
        | Accepted authenticated => exact after_count setup checks reserve representation created packet authenticated
        | _ =>
          rw [lift_pure]
          exact RegistrationNativePlatformMldsaCountRules.pure serverProject server_idempotent _

/-- Actual source accept retains its repeated pin hash, reservation failure and all reached mandatory-authentication/agreement outcomes under both count equations. -/
theorem accept (setup : Setup base KemSK) (codec : Codec Reader Response) (checks : Checks)
    (reserve : StateT Platform ProbComp Bool) (route : RawCtxServerRouting.SenderDecoder) (verify : MldsaTranscriptAuth.Verify)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (packet : registration.InitPacket) :
    Correct (source := source) (serverProject (n := n))
      (RegistrationNativePlatformMldsaProgram.lift
        (RegistrationNativePlatformSourceAccept.accept RegistrationNativePlatformMldsaProgram.coins setup codec checks reserve
          route verify representation created packet)) := by
  unfold RegistrationNativePlatformSourceAccept.accept RegistrationNativePlatformSourceAccept.acceptWith
  rw [lift_bind]
  apply RegistrationNativePlatformMldsaCountRules.bind serverProject _ _
    (RegistrationNativePlatformMldsaCountRules.closed serverProject _
      (RegistrationNativePlatformPinView.pin RegistrationNativePlatformMldsaProgram.coins))
  intro pin
  exact afterPin_count setup codec checks reserve route verify representation created packet pin

end BeaconcryptCore.Computational.RegistrationNativePlatformAcceptView

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformAcceptView.accept' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformAcceptView.accept
