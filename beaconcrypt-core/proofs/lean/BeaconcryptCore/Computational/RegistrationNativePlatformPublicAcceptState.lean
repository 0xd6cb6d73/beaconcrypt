-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAcceptNative
import BeaconcryptCore.Computational.RegistrationNativePlatformOpenAcceptPool
/-! The actual adaptive accept restores the full native owner roster, private KEM pool and parsed counter. Its explicit source Server projection remains separate from later instrumentation-view normalization. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicAcceptState
open PqxdhServerAuthExperiment (Setup Checks Codec)
open RegistrationNativePlatformPublicSourceExecution (State execute)
open RegistrationNativePlatformPublicSourceServer (layout rebuild)
open RegistrationNativePlatformPublicSourceLocal (external)
variable {n : Nat} {I KemSK Platform Reader Response : Type} {base : OracleSpec I} {source : RegistrationNativeMldsa.Source}

noncomputable def project (setup : Setup base KemSK) (seed : PqxdhJointIdentity.IdentitySeed)
    (scalar : PqxdhJointGapDh.ScalarBytes) (before : State n KemSK Platform source) :
    RegistrationNativeExperiment.State n KemSK source :=
  ⟨RegistrationNativePlatformServerOpenControl.project (RegistrationNativePublicSourceState.roots setup seed scalar) (layout before).1,
    RegistrationNativePublicSourceState.owners scalar before.1.1.beacons, before.2.pool, before.1.1.parsedAccepts⟩

private theorem map_apply {S A B : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (observe : A → B) (work : StateT S m A) (before : S) :
    (observe <$> work) before = Prod.map observe id <$> work before := StateT.run_map observe work before

/-- Full actual OPEN acceptance retains the same complete native source state and reached platform state, including every failure prefix. -/
theorem accept (setup : Setup base KemSK) (codec : Codec Reader Response)
    (wire : RegistrationNativeWire.Wire) (checks : Checks) (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (verify : MldsaTranscriptAuth.Verify) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (correct : PqxdhSecretInputKdf.SourceRootCorrect setup.source setup.hmac)
    (created : PqxdhLiveServerConstruction.Created Unit) (scalar : PqxdhJointGapDh.ScalarBytes)
    (selected : Bool) (reserve : StateT Platform ProbComp Bool) (packet : registration.InitPacket)
    (before : State n KemSK Platform source) :
    (fun result => ((result.1, project setup created.seed scalar result.2), result.2.1.2)) <$>
      (execute setup wire route sign created.seed scalar
        (RegistrationNativePlatformPublicFrontend.executeLocal (RegistrationNativePlatformPublicFrontend.serverOpen
          (RegistrationNativePlatformServerOpenControl.accept
            (RegistrationNativePlatformPublicFrontend.localHandler selected)
            (RegistrationNativePlatformPublicFrontend.platform reserve) setup checks verify packet)))).run before =
      ((RegistrationNativePlatformExperiment.server
        (RegistrationNativePlatformSourceAccept.accept external setup codec checks reserve route verify representation created packet)).run
          (project setup created.seed scalar before)).run before.1.2 := by
  have compared := RegistrationNativePlatformPublicAcceptNative.server setup codec wire checks route sign verify representation correct
    created scalar selected reserve packet before
  have mapped := congrArg (fun action => (fun result =>
    ((result.1.1, { project setup created.seed scalar before with server := result.1.2 }), result.2)) <$> action) compared
  rw [Functor.map_map] at mapped
  calc
    _ = (fun result => ((result.1,
        { project setup created.seed scalar before with server := RegistrationNativePlatformServerOpenControl.project (RegistrationNativePublicSourceState.roots setup created.seed scalar) (layout result.2).1 }), result.2.1.2)) <$>
        (execute setup wire route sign created.seed scalar
          (RegistrationNativePlatformPublicFrontend.executeLocal (RegistrationNativePlatformPublicFrontend.serverOpen
            (RegistrationNativePlatformServerOpenControl.accept (RegistrationNativePlatformPublicFrontend.localHandler selected)
              (RegistrationNativePlatformPublicFrontend.platform reserve) setup checks verify packet)))).run before := by
      rw [map_eq_bind_pure_comp, map_eq_bind_pure_comp]
      apply bind_congr_of_forall_mem_support
      intro result supported
      rw [RegistrationNativePlatformPublicSourceServer.server, support_map] at supported
      obtain ⟨inner, reached, rfl⟩ := supported
      rw [RegistrationNativePlatformPublicSourceAccept.accept] at reached
      have pool := RegistrationNativePlatformOpenAcceptPool.accept_pool setup wire checks route sign created.seed scalar reserve
        verify packet before.1.1.server before.1.1.environment (RegistrationNativePublicSourceEffects.toPrivate before.2) before.1.2 inner reached
      simp only [project, rebuild, layout, RegistrationNativePublicSourceEffects.toPrivate,
        RegistrationNativePublicSourceEffects.fromPrivate] at pool ⊢
      rw [pool]
      rfl
    _ = _ := by
      simpa only [RegistrationNativePlatformExperiment.server, StateT.run, map_apply,
        Functor.map_map, project, Prod.map_def, id_eq] using mapped
end BeaconcryptCore.Computational.RegistrationNativePlatformPublicAcceptState

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAcceptState.accept' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAcceptState.accept
