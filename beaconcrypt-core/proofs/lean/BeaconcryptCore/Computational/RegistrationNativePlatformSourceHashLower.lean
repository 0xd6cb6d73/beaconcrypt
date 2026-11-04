-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPairedServerService
import BeaconcryptCore.Computational.RegistrationNativePlatformSourceSeal
import BeaconcryptCore.Computational.RegistrationServerRecordWorldSource
/-! The actual mutable first-record commitment callback lowers to its literal public hash request on the one shared World cache. The replacement transcript and actual hash/uniform/admin state remain in the output; only the explicit source instrumentation view is applied. -/
open OracleComp OracleSpec CoreModels Aeneas beaconcrypt_core
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformSourceHashLower
open PqxdhServerAuthExperiment (Setup Codec)
open PqxdhRecordLiftInterface (EnvEffects)
open RegistrationServerRecordWorldSource (project target)
variable {n : Nat} {Auxiliary ι KemSK Reader Response : Type} {base : OracleSpec ι}
variable {m : Type → Type} [Monad m] [LawfulMonad m]

def hashing (effects : QueryImpl (EnvEffects n) m) (erased transcript : commitment.CommitmentTranscript) :
    m RegistrationNativePlatformCommitment.HashReply := do
  let digest ← effects (.inr (.hash (PqxdhRefinement.absBytes transcript.bytes)))
  pure (.ok (.Some (RegistrationAuthenticationShared.digestArray digest), erased))

private theorem state_map_apply {S A B : Type} {q : Type → Type} [Monad q] [LawfulMonad q]
    (observe : A → B) (work : StateT S q A) (before : S) :
    (observe <$> work) before = Prod.map observe id <$> work before := StateT.run_map observe work before

private theorem target_hash (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (writer : RawCtxMixedShared.Writer) (transcript : commitment.CommitmentTranscript)
    (before : RegistrationWorldAgreement.State n Auxiliary) :
    (target source writer (.hash transcript)).run before =
      (fun result => (.Some (RegistrationAuthenticationShared.digestArray result.1),
        { before with world := (result.2, before.world.2) })) <$>
          (PqxdhRecordLiftWorld.effects (.inr (.hash (PqxdhRefinement.absBytes transcript.bytes)))).run before.world.1 := by
  simp only [target, StateT.run, RegistrationServerRecordSourceProgram.native,
    RegistrationRawSealBridge.nativeAdapter, RegistrationBoundSourceCompiler.rawCompiler,
    QueryImpl.apply_compose, RegistrationBoundSourceCompiler.rawCallbacks,
    RegistrationBoundSourceCompiler.sharedCompiler, MldsaSharedNative.authLift,
    simulateQ_map, simulateQ_spec_query, PqxdhDeploymentEnvironment.request,
    bind_pure_comp, state_map_apply, Functor.map_map]
  rfl

/-- The actual source mutable commitment callback uses exactly one public hash capability and retains the same current common state after the stated accounting view. -/
theorem source (coins : QueryImpl unifSpec m) (setup : Setup base KemSK) (codec : Codec Reader Response)
    (erased transcript : commitment.CommitmentTranscript) (before : RegistrationWorldAgreement.State n Auxiliary) :
    Prod.map id project <$> (RegistrationNativePlatformSourceSeal.hash coins setup codec erased transcript).run before =
      (hashing (RegistrationNativePlatformPairedServerService.nativeEffects coins) erased transcript).run (project before) := by
  have raw := congrArg (fun work => simulateQ coins work)
    (RegistrationServerRecordWorldSource.query setup codec (.hash transcript) before)
  rw [target_hash] at raw
  have mapped := congrArg (fun action =>
    (fun result => (RustM.ok (result.1, erased), result.2)) <$> action) raw
  simp only [simulateQ_map, Functor.map_map] at mapped
  simpa only [RegistrationNativePlatformSourceSeal.hash, hashing, StateT.run_bind, StateT.run_pure,
    RegistrationNativePlatformServerCompletion.records, RegistrationNativePlatformServerCompletion.liftNative,
    RegistrationNativePlatformPairedServerService.nativeEffects, RegistrationServerPublicationWorldCompiler.effect,
    StateT.run, state_map_apply, bind_pure_comp, simulateQ_map, Functor.map_map, Prod.map, id_eq] using mapped

end BeaconcryptCore.Computational.RegistrationNativePlatformSourceHashLower

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSourceHashLower.source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSourceHashLower.source
