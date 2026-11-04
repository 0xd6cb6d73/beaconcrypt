-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicSourceServer
import BeaconcryptCore.Computational.RegistrationNativePlatformServerOpenAuthentication
/-! Actual OPEN acceptance in the adaptive shared-state client restores the literal corrected source SDK Server result. The comparison names the existing forwarding-counter view and retains the same reached platform state. Earlier roots are restored privately. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicAcceptNative
open PqxdhServerAuthExperiment (Setup Checks Codec)
open RegistrationNativePublicSourceEffects (Extra Private toPrivate)
open RegistrationNativePublicSourceCallbacks (services remember)
open RegistrationNativePlatformPublicSourceExecution (State execute)
open RegistrationNativePlatformPublicSourceServer (layout rebuild)
open RegistrationNativePlatformPublicSourceLocal (external interpret)
variable {n : Nat} {I KemSK Platform Reader Response : Type} {base : OracleSpec I}
variable {source : RegistrationNativeMldsa.Source}

private theorem map_apply {S A B : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (observe : A → B) (work : StateT S m A) (before : S) :
    (observe <$> work) before = Prod.map observe id <$> work before := StateT.run_map observe work before

/-- The new adaptive Server accept uses its actual indexed collector, mandatory authentication and stateful reservation on one common platform state. -/
theorem server (setup : Setup base KemSK) (codec : Codec Reader Response)
    (wire : RegistrationNativeWire.Wire) (checks : Checks) (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (verify : MldsaTranscriptAuth.Verify) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (correct : PqxdhSecretInputKdf.SourceRootCorrect setup.source setup.hmac)
    (created : PqxdhLiveServerConstruction.Created Unit) (scalar : PqxdhJointGapDh.ScalarBytes)
    (selected : Bool) (reserve : StateT Platform ProbComp Bool) (packet : registration.InitPacket)
    (before : State n KemSK Platform source) :
    (fun result => ((result.1, RegistrationNativePlatformServerOpenControl.project
      (RegistrationNativePublicSourceState.roots setup created.seed scalar) (layout result.2).1), result.2.1.2)) <$>
      (execute setup wire route sign created.seed scalar
        (RegistrationNativePlatformPublicFrontend.executeLocal (RegistrationNativePlatformPublicFrontend.serverOpen
          (RegistrationNativePlatformServerOpenControl.accept
            (RegistrationNativePlatformPublicFrontend.localHandler selected)
            (RegistrationNativePlatformPublicFrontend.platform reserve) setup checks verify packet)))).run before =
      ((RegistrationNativePlatformSourceAccept.accept external setup codec checks reserve route verify representation created packet).run
        (RegistrationNativePlatformServerOpenControl.project (RegistrationNativePublicSourceState.roots setup created.seed scalar)
          (layout before).1)).run before.1.2 := by
  rw [RegistrationNativePlatformPublicSourceServer.server, Functor.map_map]
  have interpreted := RegistrationNativePlatformPublicSourceAccept.accept (n := n) setup wire checks route sign created.seed scalar
    selected reserve verify packet before.1.1.server before.1.1.environment
  rw [interpreted]
  have actual := RegistrationNativePlatformServerOpenAuthentication.accept_native
    (external (Platform := Platform)) setup codec checks route verify representation correct created scalar remember
    (services setup wire route sign created.seed scalar)
    (fun query => RegistrationNativePlatformInterpret.state external ((services setup wire route sign created.seed scalar).demand query))
    (fun query => RegistrationNativePlatformInterpret.state external ((services setup wire route sign created.seed scalar).publication query))
    reserve packet (layout before).1
  have atPlatform := congrArg (fun work => work.run before.1.2) actual
  convert atPlatform using 1 <;> simp only [RegistrationNativePlatformPublicSourceAccept.actual,
    RegistrationNativePlatformPublicSourceAccept.actualCallbacks,
    RegistrationNativePlatformServerOpenControl.close,
    RegistrationNativePlatformServerOpenKernel.closeEnvironment,
    StateT.run, map_apply, Functor.map_map, layout, rebuild,
    RegistrationNativePublicSourceEffects.toPrivate, RegistrationNativePublicSourceEffects.fromPrivate,
    Prod.map_def, id_eq]
  all_goals rfl
end BeaconcryptCore.Computational.RegistrationNativePlatformPublicAcceptNative

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAcceptNative.server' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAcceptNative.server
