-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformServerOpenControl
open OracleComp OracleSpec CoreModels Aeneas beaconcrypt_core
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
/-! The literal open collector and Root-reference client restore the same source agreement and one-use token. The actual left execution retains full private provider state; only the separately stated source comparison applies its projection. -/
namespace BeaconcryptCore.Computational.RegistrationNativePlatformServerOpenAgreement
open PqxdhServerAuthExperiment (Setup Checks)
open PqxdhSecretInputKdf (RootOutput)
open RegistrationNativeRelatedFamily (Message)
open RegistrationNativeKemReferenceWorld (Private)
open RegistrationServerReferenceRoot (Ready)
open RegistrationNativePlatformServerOpenControl (State close project sourceState)
open RegistrationNativePlatformServerOpenKernel (handler agreement)
open RegistrationNativePlatformServerOpenSource (callbacks)
variable {n : Nat} {ι KemSK Extra : Type} {base : OracleSpec ι}
variable {m : Type → Type} [Monad m] [LawfulMonad m]

theorem source (coins : QueryImpl unifSpec m) (setup : Setup base KemSK) (checks : Checks)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (remember : Extra → Message → Option RootOutput → Extra)
    (services : RegistrationNativeKemReferenceEffects.Callbacks n KemSK Extra)
    (demand : QueryImpl (Message →ₒ Option (RegistrationNativePairedChoice.Choice n)) (StateT (Private n KemSK Extra) m))
    (publication : QueryImpl RegistrationBoundPublication.Spec (StateT (Private n KemSK Extra) m))
    (packet : registration.InitPacket) (authenticated : registration.AuthenticatedInit) (before : State n KemSK Extra) :
    Prod.map id sourceState <$>
      (close (agreement (handler coins setup (callbacks setup seed scalar remember services demand publication))
        setup checks packet authenticated)).run before =
    simulateQ coins ((RegistrationServerReferenceSourceAccept.agree setup checks seed scalar packet authenticated).run (sourceState before)) := by
  have compared := congrArg (fun work => (fun result => (result.1, (before.1, result.2))) <$> work)
    (RegistrationNativePlatformServerOpenSource.project coins setup checks seed scalar remember services demand publication packet authenticated before.2)
  simpa only [close, sourceState, RegistrationNativePlatformServerOpenKernel.agreement_factor,
    RegistrationNativePlatformServerOpenKernel.closeEnvironment, RegistrationServerReferenceSourceAccept.agree,
    StateT.run, StateT.lift, StateT.monad_bind_def, StateT.bind, StateT.monad_pure_def, StateT.pure,
    map_bind, map_pure, bind_pure_comp, simulateQ_map, Functor.map_map, Prod.map_def, id_eq] using compared

theorem native (coins : QueryImpl unifSpec m) (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (correct : PqxdhSecretInputKdf.SourceRootCorrect setup.source setup.hmac)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (scalar : PqxdhJointGapDh.ScalarBytes)
    (remember : Extra → Message → Option RootOutput → Extra)
    (services : RegistrationNativeKemReferenceEffects.Callbacks n KemSK Extra)
    (demand : QueryImpl (Message →ₒ Option (RegistrationNativePairedChoice.Choice n)) (StateT (Private n KemSK Extra) m))
    (publication : QueryImpl RegistrationBoundPublication.Spec (StateT (Private n KemSK Extra) m))
    (packet : registration.InitPacket) (authenticated : registration.AuthenticatedInit) (before : State n KemSK Extra)
    (fresh : before.1.consumed.contains (RegistrationReplaySchedule.identifier authenticated) = false) :
    Prod.map (RegistrationServerReferenceSourceClient.restore
      (RegistrationServerReferenceSourceClient.roots setup.source setup.joint setup.dh created.seed scalar))
      (project (RegistrationServerReferenceSourceClient.roots setup.source setup.joint setup.dh created.seed scalar)) <$>
      (close (agreement (handler coins setup (callbacks setup created.seed scalar remember services demand publication))
        setup checks packet authenticated)).run before =
    simulateQ coins ((RegistrationServerNativeSource.agree setup checks representation created packet authenticated).run
      (project (RegistrationServerReferenceSourceClient.roots setup.source setup.joint setup.dh created.seed scalar) before)) := by
  let roots := RegistrationServerReferenceSourceClient.roots setup.source setup.joint setup.dh created.seed scalar
  have mapped := congrArg (fun work => Prod.map (RegistrationServerReferenceSourceClient.restore roots)
      (RegistrationServerReferenceSourceRetain.project roots) <$> work)
    (source coins setup checks created.seed scalar remember services demand publication packet authenticated before)
  have rooted := congrArg (simulateQ coins)
    (RegistrationServerReferenceSourceAccept.agree_native setup checks representation correct created scalar packet authenticated
      (sourceState before) fresh)
  rw [simulateQ_map] at rooted
  have compared := mapped.trans rooted
  simpa only [Functor.map_map, Prod.map_def, id_eq, project, sourceState,
    RegistrationServerReferenceSourceRetain.project, roots] using compared

theorem retain_native (coins : QueryImpl unifSpec m) (roots : RegistrationServerReferenceRestore.Roots)
    (ready : Ready) (before : State n KemSK Extra) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) :
    Prod.map id (project roots) <$> (close (RegistrationNativePlatformServerReferenceAccept.retain ready)).run before =
      simulateQ coins ((RegistrationServerNativeSource.retain created
        (RegistrationServerReferenceRoot.atRoot ready (roots ready.reference))).run (project roots before)) := by
  have compared := congrArg (simulateQ coins)
    (RegistrationServerReferenceSourceRetain.retain_native roots ready (sourceState before) created)
  unfold RegistrationServerReferenceSourceRetain.retain at compared
  cases retained : RegistrationServerMaterialFrontend.retain ready before.1 with
  | fail error | div =>
    simpa only [retained, close, RegistrationNativePlatformServerReferenceAccept.retain,
      RegistrationNativePlatformServerOpenKernel.closeEnvironment, StateT.run, StateT.monad_pure_def, StateT.pure,
      map_pure, sourceState, project, RegistrationServerReferenceSourceRetain.project, simulateQ_pure, Prod.map_def, id_eq] using compared
  | ok result =>
    rcases result with ⟨reply, after⟩
    simpa only [retained, close, RegistrationNativePlatformServerReferenceAccept.retain,
      RegistrationNativePlatformServerOpenKernel.closeEnvironment, StateT.run, StateT.monad_pure_def, StateT.pure,
      map_pure, sourceState, project, RegistrationServerReferenceSourceRetain.project, simulateQ_pure, Prod.map_def, id_eq] using compared

end BeaconcryptCore.Computational.RegistrationNativePlatformServerOpenAgreement

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformServerOpenAgreement.source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformServerOpenAgreement.source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformServerOpenAgreement.native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformServerOpenAgreement.native

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformServerOpenAgreement.retain_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformServerOpenAgreement.retain_native
