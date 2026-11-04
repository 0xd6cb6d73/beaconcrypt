-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformSourceBuild

/-! Typed Server acceptance recomputes the actual pin before mandatory authentication, then performs replay rejection, external stateful reservation, actual agreement and one-use retention. The packet is already the typed output of the decoder; no parser or container correspondence is assumed here. Pin/hash and allocation effects share the same outer interpreter as all native primitive draws. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformSourceAccept
open PqxdhServerAuthExperiment (Setup Codec Checks)
open RegistrationServerFrontendCompiler (State)
variable {n : Nat} {Value ι KemSK Reader Response : Type} {base : OracleSpec ι}
variable {m : Type → Type} [Monad m]

noncomputable def authenticate (coins : QueryImpl unifSpec m) (setup : Setup base KemSK)
    (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder) (verify : MldsaTranscriptAuth.Verify)
    (pin : session.ServerAuthenticationPin) (packet : registration.InitPacket) :
    StateT (State n) m (RustM (List BeaconcryptCore.Refinement.RegistrationAuthenticationFlow.Event ×
      registration.InitAuthentication)) := fun before =>
  (fun result => (result.1, { before with world :=
    { before.world with world := (result.2, before.world.world.2) } })) <$>
    simulateQ coins ((RegistrationWorldAuthentication.begin setup codec route verify pin packet).run before.world.world.1)

noncomputable def afterPin (coins : QueryImpl unifSpec m) (setup : Setup base KemSK)
    (codec : Codec Reader Response) (checks : Checks) (reserve : StateT (State n) m Bool)
    (route : RawCtxServerRouting.SenderDecoder) (verify : MldsaTranscriptAuth.Verify)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (packet : registration.InitPacket)
    (result : RustM (core.option.Option session.ServerAuthenticationPin)) :
    StateT (State n) m (RustM (Option Nat)) :=
  match result with
  | .fail error => pure (.fail error)
  | .div => pure .div
  | .ok .None => pure (.ok none)
  | .ok (.Some pin) => do
      let checked ← authenticate coins setup codec route verify pin packet
      match checked with
      | .fail error => pure (.fail error)
      | .div => pure .div
      | .ok (_events, .Accepted authenticated) =>
          RegistrationNativePlatformServerSdk.afterAuthentication coins setup checks reserve representation created packet authenticated
      | .ok _ => pure (.ok none)

noncomputable def acceptWith
    (pin : StateT (State n) m (RustM (core.option.Option session.ServerAuthenticationPin)))
    (coins : QueryImpl unifSpec m) (setup : Setup base KemSK) (codec : Codec Reader Response)
    (checks : Checks) (reserve : StateT (State n) m Bool)
    (route : RawCtxServerRouting.SenderDecoder) (verify : MldsaTranscriptAuth.Verify)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (packet : registration.InitPacket) :
    StateT (State n) m (RustM (Option Nat)) := do
  let current ← pin
  afterPin coins setup codec checks reserve route verify representation created packet current

noncomputable def accept (coins : QueryImpl unifSpec m) (setup : Setup base KemSK) (codec : Codec Reader Response)
    (checks : Checks) (reserve : m Bool)
    (route : RawCtxServerRouting.SenderDecoder) (verify : MldsaTranscriptAuth.Verify)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (packet : registration.InitPacket) :
    StateT (State n) m (RustM (Option Nat)) :=
  acceptWith (RegistrationNativePlatformSourceBuild.pin coins) coins setup codec checks (StateT.lift reserve)
    route verify representation created packet

theorem authenticate_run (coins : QueryImpl unifSpec m) (setup : Setup base KemSK)
    (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder) (verify : MldsaTranscriptAuth.Verify)
    (pin : session.ServerAuthenticationPin) (packet : registration.InitPacket) (before : State n) :
    (authenticate coins setup codec route verify pin packet).run before =
      (fun result => (result.1, { before with world :=
        { before.world with world := (result.2, before.world.world.2) } })) <$>
        simulateQ coins ((RegistrationWorldAuthentication.begin setup codec route verify pin packet).run before.world.world.1) := rfl

theorem acceptWith_run
    (pin : StateT (State n) m (RustM (core.option.Option session.ServerAuthenticationPin)))
    (coins : QueryImpl unifSpec m) (setup : Setup base KemSK) (codec : Codec Reader Response)
    (checks : Checks) (reserve : StateT (State n) m Bool)
    (route : RawCtxServerRouting.SenderDecoder) (verify : MldsaTranscriptAuth.Verify)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (packet : registration.InitPacket) (before : State n) :
    (acceptWith pin coins setup codec checks reserve route verify representation created packet).run before = (do
      let current ← pin.run before
      (afterPin coins setup codec checks reserve route verify representation created packet current.1).run current.2) :=
  StateT.run_bind _ _ _

variable [LawfulMonad m]

theorem authenticate_stored (coins : QueryImpl unifSpec m) (setup : Setup base KemSK)
    (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder) (verify : MldsaTranscriptAuth.Verify)
    (created : PqxdhLiveServerConstruction.Created Unit) (packet : registration.InitPacket) (before : State n) :
    (authenticate coins setup codec route verify before.pin packet).run before =
      simulateQ coins ((RegistrationServerNativeSource.authenticate setup codec route verify created packet).run before) := by
  simp only [authenticate, RegistrationServerNativeSource.authenticate, RegistrationServerNativeSource.sourceStep,
    RegistrationWorldServerFrontend.authenticate, RegistrationWorldServerFrontend.withWorld,
    RegistrationServerFrontendCompiler.restore, RegistrationServerFrontendCompiler.erase,
    StateT.run, Functor.map_map, Prod.map, id_eq, simulateQ_map]

theorem acceptWith_stored (coins : QueryImpl unifSpec m) (setup : Setup base KemSK) (codec : Codec Reader Response)
    (checks : Checks) (reserve : StateT (State n) m Bool)
    (route : RawCtxServerRouting.SenderDecoder) (verify : MldsaTranscriptAuth.Verify)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (packet : registration.InitPacket) :
    acceptWith RegistrationNativePlatformCompletionSdk.storedPin coins setup codec checks reserve
      route verify representation created packet =
      RegistrationNativePlatformServerSdk.accept coins setup codec checks reserve route verify representation created packet := by
  funext before
  change (acceptWith RegistrationNativePlatformCompletionSdk.storedPin coins setup codec checks reserve
    route verify representation created packet).run before =
      (RegistrationNativePlatformServerSdk.accept coins setup codec checks reserve route verify representation created packet).run before
  rw [acceptWith_run]
  have pinRun : (RegistrationNativePlatformCompletionSdk.storedPin : StateT (State n) m _).run before =
      pure (.ok (.Some before.pin), before) := rfl
  rw [pinRun, pure_bind]
  simp only [afterPin, RegistrationNativePlatformServerSdk.accept, StateT.run_bind]
  rw [authenticate_stored coins setup codec route verify created packet before]
  rfl

section Interpret
open RegistrationNativePlatformInterpret (state state_pure state_bind)
variable {κ : Type} {spec : OracleSpec.{0, 0} κ}

theorem authenticate_interpret (implementation : QueryImpl spec m) (coins : QueryImpl unifSpec (OracleComp spec))
    (setup : Setup base KemSK) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (verify : MldsaTranscriptAuth.Verify) (pin : session.ServerAuthenticationPin) (packet : registration.InitPacket) :
    state implementation (authenticate (n := n) coins setup codec route verify pin packet) =
      authenticate (fun query => simulateQ implementation (coins query)) setup codec route verify pin packet := by
  funext before
  unfold authenticate state StateT.run
  rw [simulateQ_map, ← QueryImpl.simulateQ_compose]
  rfl

theorem afterPin_interpret (implementation : QueryImpl spec m) (coins : QueryImpl unifSpec (OracleComp spec))
    (setup : Setup base KemSK) (codec : Codec Reader Response) (checks : Checks)
    (reserve : StateT (State n) (OracleComp spec) Bool)
    (route : RawCtxServerRouting.SenderDecoder) (verify : MldsaTranscriptAuth.Verify)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (packet : registration.InitPacket)
    (result : RustM (core.option.Option session.ServerAuthenticationPin)) :
    state implementation (afterPin coins setup codec checks reserve route verify representation created packet result) =
      afterPin (fun query => simulateQ implementation (coins query)) setup codec checks (state implementation reserve)
        route verify representation created packet result := by
  unfold afterPin
  cases result with
  | fail error => exact state_pure implementation _
  | div => exact state_pure implementation _
  | ok value =>
      cases value with
      | none => exact state_pure implementation _
      | some pin =>
          dsimp only
          rw [state_bind, authenticate_interpret]
          apply bind_congr
          intro checked
          cases checked with
          | fail error => exact state_pure implementation _
          | div => exact state_pure implementation _
          | ok output =>
              rcases output with ⟨events, result⟩
              cases result <;> first
                | exact RegistrationNativePlatformInterpret.afterAuthentication implementation coins setup checks
                    reserve representation created packet _
                | exact state_pure implementation _

theorem acceptWith_interpret (implementation : QueryImpl spec m)
    (pin : StateT (State n) (OracleComp spec) (RustM (core.option.Option session.ServerAuthenticationPin)))
    (coins : QueryImpl unifSpec (OracleComp spec)) (setup : Setup base KemSK) (codec : Codec Reader Response)
    (checks : Checks) (reserve : StateT (State n) (OracleComp spec) Bool)
    (route : RawCtxServerRouting.SenderDecoder) (verify : MldsaTranscriptAuth.Verify)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (packet : registration.InitPacket) :
    state implementation (acceptWith pin coins setup codec checks reserve route verify representation created packet) =
      acceptWith (state implementation pin) (fun query => simulateQ implementation (coins query)) setup codec checks
        (state implementation reserve) route verify representation created packet := by
  unfold acceptWith
  rw [state_bind]
  apply bind_congr
  intro current
  exact afterPin_interpret implementation coins setup codec checks reserve route verify representation created packet current

private theorem lift_interpret (implementation : QueryImpl spec m) (work : OracleComp spec Bool) :
    state implementation (StateT.lift work : StateT (State n) (OracleComp spec) Bool) =
      StateT.lift (simulateQ implementation work) := by
  funext before
  change simulateQ implementation ((StateT.lift work : StateT (State n) (OracleComp spec) Bool).run before) =
    (StateT.lift (simulateQ implementation work) : StateT (State n) m Bool).run before
  simp only [StateT.run_lift, simulateQ_bind, simulateQ_pure]

theorem accept_interpret (implementation : QueryImpl spec m) (coins : QueryImpl unifSpec (OracleComp spec))
    (setup : Setup base KemSK) (codec : Codec Reader Response) (checks : Checks) (reserve : OracleComp spec Bool)
    (route : RawCtxServerRouting.SenderDecoder) (verify : MldsaTranscriptAuth.Verify)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (packet : registration.InitPacket) :
    state implementation (accept (n := n) coins setup codec checks reserve route verify representation created packet) =
      accept (fun query => simulateQ implementation (coins query)) setup codec checks (simulateQ implementation reserve)
        route verify representation created packet := by
  unfold accept
  rw [acceptWith_interpret, RegistrationNativePlatformSourceBuild.pin_interpret, lift_interpret]

theorem accept_continuation (implementation : QueryImpl spec m) (coins : QueryImpl unifSpec (OracleComp spec))
    (setup : Setup base KemSK) (codec : Codec Reader Response) (checks : Checks) (reserve : OracleComp spec Bool)
    (route : RawCtxServerRouting.SenderDecoder) (verify : MldsaTranscriptAuth.Verify)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (packet : registration.InitPacket)
    (next : RustM (Option Nat) → StateT (State n) (OracleComp spec) Value) :
    state implementation (accept coins setup codec checks reserve route verify representation created packet >>= next) = (do
      let result ← accept (fun query => simulateQ implementation (coins query)) setup codec checks
        (simulateQ implementation reserve) route verify representation created packet
      state implementation (next result)) := by
  rw [state_bind, accept_interpret]

end Interpret

end BeaconcryptCore.Computational.RegistrationNativePlatformSourceAccept

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSourceAccept.authenticate_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSourceAccept.authenticate_run
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSourceAccept.acceptWith_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSourceAccept.acceptWith_run
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSourceAccept.authenticate_stored' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSourceAccept.authenticate_stored
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSourceAccept.acceptWith_stored' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSourceAccept.acceptWith_stored
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSourceAccept.authenticate_interpret' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSourceAccept.authenticate_interpret
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSourceAccept.afterPin_interpret' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSourceAccept.afterPin_interpret
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSourceAccept.acceptWith_interpret' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSourceAccept.acceptWith_interpret
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSourceAccept.accept_interpret' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSourceAccept.accept_interpret
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSourceAccept.accept_continuation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSourceAccept.accept_continuation
