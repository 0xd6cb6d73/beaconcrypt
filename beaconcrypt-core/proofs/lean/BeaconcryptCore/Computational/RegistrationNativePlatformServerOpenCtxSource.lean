-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformServerOpenCtxAccept
open OracleComp OracleSpec CoreModels Aeneas beaconcrypt_core
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
/-! The full physical OPEN CTX accept execution has the actual corrected SourceAccept comparison. The left run retains provider/pool/Extra, physical CTX journal/cache and platform state; only the explicitly named source comparison projects reference roots and the provider frame. No closed/open ideal-game identity or whole source-handler premise is introduced. -/
namespace BeaconcryptCore.Computational.RegistrationNativePlatformServerOpenCtxSource
open PqxdhServerAuthExperiment (Setup Checks Codec)
open RegistrationNativeKemReferenceWorld (Private)
open RegistrationNativePlatformCtxRunner (Full interpret)
open RegistrationNativePlatformServerOpenCtxKernel (Callbacks Transport)
variable {n : Nat} {ι KemSK Extra Platform Reader Response : Type} {base : OracleSpec ι}

def project (roots : RegistrationServerReferenceRestore.Roots)
    (before : RegistrationNativePlatformServerOpenCtxAccept.State n KemSK Extra × Platform) : RegistrationServerFrontendCompiler.State n × Platform :=
  (RegistrationNativePlatformServerOpenControl.project roots before.1, before.2)

private theorem state_map_apply {S X Y : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (f : X → Y) (work : StateT S m X) (before : S) :
    (f <$> work) before = Prod.map f id <$> work before := StateT.run_map f work before

theorem accept_source (setup : Setup base KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (verify : MldsaTranscriptAuth.Verify)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (correct : PqxdhSecretInputKdf.SourceRootCorrect setup.source setup.hmac)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (scalar : PqxdhJointGapDh.ScalarBytes)
    (remember : Extra → RegistrationNativeRelatedFamily.Message → Option PqxdhSecretInputKdf.RootOutput → Extra)
    (services : RegistrationNativeKemReferenceEffects.Callbacks n KemSK Extra)
    (demand : QueryImpl (RegistrationNativeRelatedFamily.Message →ₒ Option (RegistrationNativePairedChoice.Choice n)) (StateT (Private n KemSK Extra) (StateT Platform ProbComp)))
    (publication : QueryImpl RegistrationBoundPublication.Spec (StateT (Private n KemSK Extra) (StateT Platform ProbComp)))
    (callbacks : Callbacks n KemSK Extra Platform)
    (transport : Transport setup callbacks (RegistrationNativePlatformServerOpenSource.callbacks setup created.seed scalar remember services demand publication))
    (reserve : StateT Platform ProbComp Bool) (packet : registration.InitPacket)
    (before : Full (RegistrationNativePlatformServerOpenCtxAccept.State n KemSK Extra) Platform) :
    Prod.map id (fun after => project (RegistrationServerReferenceSourceClient.roots setup.source setup.joint setup.dh created.seed scalar)
      (RegistrationNativePlatformServerOpenCtxAccept.realize after)) <$>
      (interpret (RegistrationNativePlatformServerOpenCtxAccept.accept callbacks reserve setup checks verify packet)).run before =
      (RegistrationAgreementNestedState.flatten (RegistrationNativePlatformSourceAccept.accept RegistrationNativePlatformMldsaProgram.coins setup codec checks reserve route verify representation created packet)).run
        (project (RegistrationServerReferenceSourceClient.roots setup.source setup.joint setup.dh created.seed scalar)
          (RegistrationNativePlatformServerOpenCtxAccept.realize before)) := by
  let roots := RegistrationServerReferenceSourceClient.roots setup.source setup.joint setup.dh created.seed scalar
  have physical := RegistrationNativePlatformServerOpenCtxAccept.physical_source setup checks verify packet callbacks
    (RegistrationNativePlatformServerOpenSource.callbacks setup created.seed scalar remember services demand publication) transport reserve before
  have mapped := congrArg (fun work => Prod.map id (project roots) <$> work) physical
  have source := RegistrationNativePlatformServerOpenAuthentication.accept_native RegistrationNativePlatformMldsaProgram.coins
    setup codec checks route verify representation correct created scalar remember services demand publication reserve packet
    (RegistrationNativePlatformServerOpenCtxAccept.realize before).1
  have sourceFull := congrArg (fun work => (fun result => (result.1.1, (result.1.2, result.2))) <$>
    work.run (RegistrationNativePlatformServerOpenCtxAccept.realize before).2) source
  have realized : Prod.map id (project roots) <$>
      (RegistrationAgreementNestedState.flatten (RegistrationNativePlatformServerOpenControl.close
        (RegistrationNativePlatformServerOpenControl.accept (RegistrationNativePlatformServerOpenKernel.handler RegistrationNativePlatformMldsaProgram.coins setup
          (RegistrationNativePlatformServerOpenSource.callbacks setup created.seed scalar remember services demand publication))
          (StateT.lift reserve) setup checks verify packet))).run (RegistrationNativePlatformServerOpenCtxAccept.realize before) =
      (RegistrationAgreementNestedState.flatten (RegistrationNativePlatformSourceAccept.accept RegistrationNativePlatformMldsaProgram.coins setup codec checks reserve route verify representation created packet)).run
        (project roots (RegistrationNativePlatformServerOpenCtxAccept.realize before)) := by
    simpa only [RegistrationAgreementNestedState.flatten, state_map_apply, Functor.map_map, project,
      StateT.run, Prod.map_def, id_eq, roots] using sourceFull
  have whole := mapped.trans realized
  simpa only [Functor.map_map, Prod.map_def, id_eq, roots] using whole

end BeaconcryptCore.Computational.RegistrationNativePlatformServerOpenCtxSource

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformServerOpenCtxSource.accept_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformServerOpenCtxSource.accept_source
