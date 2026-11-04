-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformServerOpenAfterAuthentication
import BeaconcryptCore.Computational.RegistrationNativePlatformServerOpenEffects
open OracleComp OracleSpec CoreModels Aeneas beaconcrypt_core
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
/-! Full corrected SourceAccept is the private interpretation of the executable open-indexed public controller. The actual left run retains the provider pool, root memo and shared platform state on every result; only its explicit source comparison projects them. Repeated pin hashing, authentication, replay and stateful reservation keep their actual order. -/
namespace BeaconcryptCore.Computational.RegistrationNativePlatformServerOpenAuthentication
open PqxdhServerAuthExperiment (Setup Checks Codec)
open PqxdhSecretInputKdf (RootOutput)
open RegistrationNativeRelatedFamily (Message)
open RegistrationNativeKemReferenceWorld (Private)
open RegistrationNativePlatformServerOpenControl
open RegistrationNativePlatformServerOpenKernel (handler)
open RegistrationNativePlatformServerOpenSource (callbacks)
variable {n : Nat} {ι KemSK Extra Value Reader Response : Type} {base : OracleSpec ι}
variable {m : Type → Type} [Monad m] [LawfulMonad m]

private def closedState (before : State n KemSK Extra) : RegistrationNativePlatformServerReferenceAccept.State n :=
  (before.1, (before.2.1, before.2.2.world))

private theorem effect_closed (coins : QueryImpl unifSpec m) (setup : Setup base KemSK)
    (services : RegistrationNativePlatformServerOpenKernel.Callbacks n KemSK Extra m)
    (roots : RegistrationServerReferenceRestore.Roots)
    (work : OracleComp (PqxdhRecordLiftInterface.EnvEffects n) Value) (before : State n KemSK Extra) :
    Prod.map id (project roots) <$>
      (close (StateT.lift (StateT.lift (simulateQ (effects (handler coins setup services)) work)))).run before =
    Prod.map id (RegistrationNativePlatformServerReferenceAccept.project roots) <$>
      (RegistrationNativePlatformServerReferenceAccept.close (StateT.lift (StateT.lift
        (simulateQ (RegistrationNativePlatformServerReferencePrefix.effects coins) work)))).run (closedState before) := by
  rw [close_effect, RegistrationNativePlatformServerReferenceAuthentication.close_effect,
    RegistrationNativePlatformServerOpenEffects.program]
  simp only [Functor.map_map, Prod.map_def, id_eq, project,
    RegistrationNativePlatformServerReferenceAccept.project, RegistrationNativeKemReferenceBackend.project, closedState]

theorem pin_native (coins : QueryImpl unifSpec m) (setup : Setup base KemSK)
    (services : RegistrationNativePlatformServerOpenKernel.Callbacks n KemSK Extra m)
    (roots : RegistrationServerReferenceRestore.Roots) (before : State n KemSK Extra) :
    Prod.map id (project roots) <$>
      (close (StateT.lift (StateT.lift (RegistrationNativePlatformServerReferenceAccept.pin
        (effects (handler coins setup services)) before.1.pin)))).run before =
      (RegistrationNativePlatformSourceBuild.pin coins).run (project roots before) := by
  rw [close_effect, RegistrationNativePlatformServerOpenEffects.pin]
  have compared := RegistrationNativePlatformServerReferenceAuthentication.pin_native coins roots (closedState before)
  rw [RegistrationNativePlatformServerReferenceAuthentication.close_effect] at compared
  simpa only [RegistrationNativePlatformServerOpenEffects.withWorld, StateT.run,
    Functor.map_map, Prod.map_def, id_eq, project, closedState,
    RegistrationNativePlatformServerReferenceAccept.project, RegistrationNativeKemReferenceBackend.project] using compared

theorem authentication_native (coins : QueryImpl unifSpec m) (setup : Setup base KemSK)
    (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (verify : MldsaTranscriptAuth.Verify) (pin : session.ServerAuthenticationPin) (packet : registration.InitPacket)
    (services : RegistrationNativePlatformServerOpenKernel.Callbacks n KemSK Extra m)
    (roots : RegistrationServerReferenceRestore.Roots) (before : State n KemSK Extra) :
    Prod.map id (project roots) <$>
      (close (StateT.lift (StateT.lift (simulateQ (effects (handler coins setup services))
        (RegistrationAuthenticationCompiler.program setup.source.crypto verify pin packet))))).run before =
      (RegistrationNativePlatformSourceAccept.authenticate coins setup codec route verify pin packet).run (project roots before) := by
  exact (effect_closed coins setup services roots _ before).trans
    (RegistrationNativePlatformServerReferenceAuthentication.authentication_native coins setup codec route verify pin packet roots (closedState before))

theorem after_pin_native (coins : QueryImpl unifSpec m)
    (setup : Setup base KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (verify : MldsaTranscriptAuth.Verify)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (correct : PqxdhSecretInputKdf.SourceRootCorrect setup.source setup.hmac)
    (created : PqxdhLiveServerConstruction.Created Unit) (scalar : PqxdhJointGapDh.ScalarBytes)
    (remember : Extra → Message → Option RootOutput → Extra)
    (services : RegistrationNativeKemReferenceEffects.Callbacks n KemSK Extra)
    (demand : QueryImpl (Message →ₒ Option (RegistrationNativePairedChoice.Choice n)) (StateT (Private n KemSK Extra) m))
    (publication : QueryImpl RegistrationBoundPublication.Spec (StateT (Private n KemSK Extra) m))
    (reserve : m Bool) (packet : registration.InitPacket) (result : RegistrationNativeServerPinRecompute.PinReply) (before : State n KemSK Extra) :
    Prod.map id (project (RegistrationServerReferenceSourceClient.roots setup.source setup.joint setup.dh created.seed scalar)) <$>
      (close (afterPin
        (handler coins setup (callbacks setup created.seed scalar remember services demand publication))
        (StateT.lift reserve) setup checks verify packet result)).run before =
      (RegistrationNativePlatformSourceAccept.afterPin coins setup codec checks (StateT.lift reserve)
        route verify representation created packet result).run
        (project (RegistrationServerReferenceSourceClient.roots setup.source setup.joint setup.dh created.seed scalar) before) := by
  let roots := RegistrationServerReferenceSourceClient.roots setup.source setup.joint setup.dh created.seed scalar
  change Prod.map id (project roots) <$> _ =
    (RegistrationNativePlatformSourceAccept.afterPin coins setup codec checks (StateT.lift reserve)
      route verify representation created packet result).run (project roots before)
  unfold afterPin RegistrationNativePlatformSourceAccept.afterPin
  cases result with
  | fail error | div => simp only [close_pure, StateT.run_pure, map_pure, Prod.map_def, id_eq]
  | ok optional => cases optional with
    | none => simp only [close_pure, StateT.run_pure, map_pure, Prod.map_def, id_eq]
    | some pin =>
      simp only [StateT.run_bind]
      rw [close_bind, StateT.run_bind, map_bind,
        ← authentication_native coins setup codec route verify pin packet (callbacks setup created.seed scalar remember services demand publication) roots before, bind_map_left]
      apply bind_congr
      rintro ⟨checked, current⟩
      cases checked with
      | fail error | div => simp only [close_pure, StateT.run_pure, map_pure, Prod.map_def, id_eq]
      | ok pair =>
        rcases pair with ⟨events, authentication⟩
        cases authentication
        all_goals first
          | exact RegistrationNativePlatformServerOpenAfterAuthentication.native coins setup checks representation correct created scalar remember services demand publication reserve packet _ current
          | simp only [close_pure, StateT.run_pure, map_pure, Prod.map_def, id_eq]

theorem accept_native (coins : QueryImpl unifSpec m)
    (setup : Setup base KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (verify : MldsaTranscriptAuth.Verify)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (correct : PqxdhSecretInputKdf.SourceRootCorrect setup.source setup.hmac)
    (created : PqxdhLiveServerConstruction.Created Unit) (scalar : PqxdhJointGapDh.ScalarBytes)
    (remember : Extra → Message → Option RootOutput → Extra)
    (services : RegistrationNativeKemReferenceEffects.Callbacks n KemSK Extra)
    (demand : QueryImpl (Message →ₒ Option (RegistrationNativePairedChoice.Choice n)) (StateT (Private n KemSK Extra) m))
    (publication : QueryImpl RegistrationBoundPublication.Spec (StateT (Private n KemSK Extra) m))
    (reserve : m Bool) (packet : registration.InitPacket) (before : State n KemSK Extra) :
    Prod.map id (project (RegistrationServerReferenceSourceClient.roots setup.source setup.joint setup.dh created.seed scalar)) <$>
      (close (accept
        (handler coins setup (callbacks setup created.seed scalar remember services demand publication))
        (StateT.lift reserve) setup checks verify packet)).run before =
      (RegistrationNativePlatformSourceAccept.accept coins setup codec checks reserve route verify representation created packet).run
        (project (RegistrationServerReferenceSourceClient.roots setup.source setup.joint setup.dh created.seed scalar) before) := by
  let roots := RegistrationServerReferenceSourceClient.roots setup.source setup.joint setup.dh created.seed scalar
  change Prod.map id (project roots) <$> _ =
    (RegistrationNativePlatformSourceAccept.accept coins setup codec checks reserve route verify representation created packet).run (project roots before)
  unfold accept RegistrationNativePlatformSourceAccept.accept
  rw [close_bind, StateT.run_bind, close_get, pure_bind, RegistrationNativePlatformSourceAccept.acceptWith_run]
  rw [close_bind, StateT.run_bind, map_bind, ← pin_native coins setup (callbacks setup created.seed scalar remember services demand publication) roots before, bind_map_left]
  apply bind_congr
  rintro ⟨pinned, current⟩
  exact after_pin_native coins setup codec checks route verify representation correct created scalar remember services demand publication reserve packet pinned current

end BeaconcryptCore.Computational.RegistrationNativePlatformServerOpenAuthentication

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformServerOpenAuthentication.pin_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformServerOpenAuthentication.pin_native

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformServerOpenAuthentication.authentication_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformServerOpenAuthentication.authentication_native

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformServerOpenAuthentication.after_pin_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformServerOpenAuthentication.after_pin_native

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformServerOpenAuthentication.accept_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformServerOpenAuthentication.accept_native
