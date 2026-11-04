-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformServerOpenCtxSource
open OracleComp OracleSpec CoreModels Aeneas beaconcrypt_core
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
/-! Real-source specialization of the two individual reachable OPEN leaves. Preparation updates the same private memo; the indexed primitive uses its literal source sampler and pool, exposing only ordinary draws to the CTX backend. These equations do not replace the open protocol capabilities in an ideal or restricted game. -/
namespace BeaconcryptCore.Computational.RegistrationNativePlatformServerOpenCtxSourceLeaves
open PqxdhServerAuthExperiment (Setup)
open RegistrationNativeKemReferenceWorld (Private)
open RegistrationNativePlatformCtxRunner (M Full interpret privateWork)
open RegistrationNativePlatformServerOpenCtxEffects (replace realize)
variable {n : Nat} {ι KemSK Extra Platform : Type} {base : OracleSpec ι}

noncomputable def prepare (setup : Setup base KemSK) (seed : PqxdhJointIdentity.IdentitySeed)
    (scalar : PqxdhJointGapDh.ScalarBytes)
    (remember : Extra → RegistrationNativeRelatedFamily.Message → Option PqxdhSecretInputKdf.RootOutput → Extra) :
    QueryImpl RegistrationServerReferenceRoot.PrepareSpec (M (Private n KemSK Extra) Platform) :=
  fun query => privateWork (RegistrationNativePlatformServerOpenSource.prepare setup seed scalar remember query)

noncomputable def indexed (setup : Setup base KemSK) (other : QueryImpl RegistrationNativeKemInterface.OtherSpec ProbComp) :
    QueryImpl (RegistrationNativeKemInterface.Spec RegistrationNativeKemInterface.OtherSpec KemSK)
      (M (Private n KemSK Extra) Platform) := fun query =>
  privateWork (RegistrationNativePlatformInterpret.state RegistrationNativePlatformCtxBackend.coin
    (RegistrationNativeKemReferenceWorld.kem setup other query))

theorem kem_cache (setup : Setup base KemSK) (other : QueryImpl RegistrationNativeKemInterface.OtherSpec ProbComp)
    (query : (RegistrationNativeKemInterface.Spec RegistrationNativeKemInterface.OtherSpec KemSK).Domain)
    (cache : CtxRomAuth.CtxRO.QueryCache) (before : Private n KemSK Extra) :
    Prod.map id (replace cache) <$> (RegistrationNativeKemReferenceWorld.kem setup other query).run before =
      (RegistrationNativeKemReferenceWorld.kem setup other query).run (replace cache before) := by
  have framed := RegistrationNativePlatformCtxCacheFrame.sampled cache
    ((RegistrationNativeKemInterface.source setup.baseImpl setup.kem RegistrationNativeKemInterface.OtherSpec
      (fun request => StateT.lift (other request)) query).run ((), before.pool)) before.world
  have mapped := congrArg (fun action => (fun result => (result.1.1,
    { (replace cache before) with world := result.2, pool := result.1.2.2 })) <$> action) framed
  simpa only [RegistrationNativeKemReferenceWorld.kem, StateT.run, bind_pure_comp, Functor.map_map,
    replace, Prod.map_def, id_eq] using mapped

private theorem state_map_apply {S X Y : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (f : X → Y) (work : StateT S m X) (before : S) :
    (f <$> work) before = Prod.map f id <$> work before := StateT.run_map f work before

private theorem state_lift_apply {S X : Type} {m : Type → Type} [Monad m]
    (work : m X) (before : S) :
    (StateT.lift work : StateT S m X) before = (do let value ← work; pure (value, before)) := rfl

private theorem state_pure_apply {S X : Type} {m : Type → Type} [Monad m]
    (value : X) (before : S) :
    (pure value : StateT S m X) before = pure (value, before) := rfl

theorem prepare_source (setup : Setup base KemSK) (seed : PqxdhJointIdentity.IdentitySeed)
    (scalar : PqxdhJointGapDh.ScalarBytes)
    (remember : Extra → RegistrationNativeRelatedFamily.Message → Option PqxdhSecretInputKdf.RootOutput → Extra)
    (query : RegistrationServerReferenceRoot.PrepareSpec.Domain) (before : Full (Private n KemSK Extra) Platform) :
    Prod.map id realize <$> (interpret (prepare setup seed scalar remember query)).run before =
      (RegistrationAgreementNestedState.flatten
        (RegistrationNativePlatformServerOpenSource.prepare setup seed scalar remember query)).run (realize before) := by
  unfold prepare
  rw [RegistrationNativePlatformCtxRunner.private_run]
  simp only [RegistrationNativePlatformServerOpenSource.prepare, RegistrationAgreementNestedState.flatten,
    StateT.run, simulateQ_pure, state_pure_apply, map_pure, realize, replace, Prod.map_def, id_eq]

theorem indexed_source (setup : Setup base KemSK) (other : QueryImpl RegistrationNativeKemInterface.OtherSpec ProbComp)
    (query : (RegistrationNativeKemInterface.Spec RegistrationNativeKemInterface.OtherSpec KemSK).Domain)
    (before : Full (Private n KemSK Extra) Platform) :
    Prod.map id realize <$> (interpret (indexed setup other query)).run before =
      (RegistrationAgreementNestedState.flatten
        (RegistrationNativePlatformInterpret.state RegistrationNativePlatformMldsaProgram.coins
          (RegistrationNativeKemReferenceWorld.kem setup other query))).run (realize before) := by
  unfold indexed
  rw [RegistrationNativePlatformCtxRunner.private_run]
  have framed := kem_cache setup other query before.2.1 before.1.1
  have mapped := congrArg (fun action => (fun result => (result.1, (result.2, before.1.2))) <$> action) framed
  simpa only [RegistrationNativePlatformInterpret.state, StateT.run, RegistrationNativePlatformCtxBackend.coins,
    RegistrationNativePlatformMldsaProgram.lift_coins, RegistrationAgreementNestedState.flatten,
    state_map_apply, state_lift_apply, bind_pure_comp, Functor.map_map, realize, Prod.map_def, id_eq] using mapped

noncomputable def callbacks (setup : Setup base KemSK) (seed : PqxdhJointIdentity.IdentitySeed)
    (scalar : PqxdhJointGapDh.ScalarBytes)
    (remember : Extra → RegistrationNativeRelatedFamily.Message → Option PqxdhSecretInputKdf.RootOutput → Extra)
    (other : QueryImpl RegistrationNativeKemInterface.OtherSpec ProbComp)
    (demand : QueryImpl (RegistrationNativeRelatedFamily.Message →ₒ Option (RegistrationNativePairedChoice.Choice n)) (M (Private n KemSK Extra) Platform))
    (publication : QueryImpl RegistrationBoundPublication.Spec (M (Private n KemSK Extra) Platform)) :
    RegistrationNativePlatformServerOpenCtxKernel.Callbacks n KemSK Extra Platform where
  prepare := prepare setup seed scalar remember
  demand := demand
  publication := publication
  indexed := indexed setup other

theorem transport (setup : Setup base KemSK) (seed : PqxdhJointIdentity.IdentitySeed)
    (scalar : PqxdhJointGapDh.ScalarBytes)
    (remember : Extra → RegistrationNativeRelatedFamily.Message → Option PqxdhSecretInputKdf.RootOutput → Extra)
    (services : RegistrationNativeKemReferenceEffects.Callbacks n KemSK Extra)
    (demand : QueryImpl (RegistrationNativeRelatedFamily.Message →ₒ Option (RegistrationNativePairedChoice.Choice n)) (M (Private n KemSK Extra) Platform))
    (publication : QueryImpl RegistrationBoundPublication.Spec (M (Private n KemSK Extra) Platform))
    (nativeDemand : QueryImpl (RegistrationNativeRelatedFamily.Message →ₒ Option (RegistrationNativePairedChoice.Choice n)) (StateT (Private n KemSK Extra) (StateT Platform ProbComp)))
    (nativePublication : QueryImpl RegistrationBoundPublication.Spec (StateT (Private n KemSK Extra) (StateT Platform ProbComp))) :
    RegistrationNativePlatformServerOpenCtxKernel.Transport setup
      (callbacks setup seed scalar remember services.other demand publication)
      (RegistrationNativePlatformServerOpenSource.callbacks setup seed scalar remember services nativeDemand nativePublication) where
  prepare := prepare_source setup seed scalar remember
  indexed := indexed_source setup services.other

theorem accept_source {Reader Response : Type} (setup : Setup base KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (checks : PqxdhServerAuthExperiment.Checks)
    (route : RawCtxServerRouting.SenderDecoder) (verify : MldsaTranscriptAuth.Verify)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (correct : PqxdhSecretInputKdf.SourceRootCorrect setup.source setup.hmac)
    (created : PqxdhLiveServerConstruction.Created Unit) (scalar : PqxdhJointGapDh.ScalarBytes)
    (remember : Extra → RegistrationNativeRelatedFamily.Message → Option PqxdhSecretInputKdf.RootOutput → Extra)
    (services : RegistrationNativeKemReferenceEffects.Callbacks n KemSK Extra)
    (demand : QueryImpl (RegistrationNativeRelatedFamily.Message →ₒ Option (RegistrationNativePairedChoice.Choice n)) (M (Private n KemSK Extra) Platform))
    (publication : QueryImpl RegistrationBoundPublication.Spec (M (Private n KemSK Extra) Platform))
    (nativeDemand : QueryImpl (RegistrationNativeRelatedFamily.Message →ₒ Option (RegistrationNativePairedChoice.Choice n)) (StateT (Private n KemSK Extra) (StateT Platform ProbComp)))
    (nativePublication : QueryImpl RegistrationBoundPublication.Spec (StateT (Private n KemSK Extra) (StateT Platform ProbComp)))
    (reserve : StateT Platform ProbComp Bool) (packet : registration.InitPacket)
    (before : Full (RegistrationNativePlatformServerOpenCtxAccept.State n KemSK Extra) Platform) :
    Prod.map id (fun after => RegistrationNativePlatformServerOpenCtxSource.project
      (RegistrationServerReferenceSourceClient.roots setup.source setup.joint setup.dh created.seed scalar)
      (RegistrationNativePlatformServerOpenCtxAccept.realize after)) <$>
      (interpret (RegistrationNativePlatformServerOpenCtxAccept.accept
        (callbacks setup created.seed scalar remember services.other demand publication) reserve setup checks verify packet)).run before =
      (RegistrationAgreementNestedState.flatten (RegistrationNativePlatformSourceAccept.accept RegistrationNativePlatformMldsaProgram.coins
        setup codec checks reserve route verify representation created packet)).run
        (RegistrationNativePlatformServerOpenCtxSource.project
          (RegistrationServerReferenceSourceClient.roots setup.source setup.joint setup.dh created.seed scalar)
          (RegistrationNativePlatformServerOpenCtxAccept.realize before)) :=
  RegistrationNativePlatformServerOpenCtxSource.accept_source setup codec checks route verify representation correct created scalar remember
    services nativeDemand nativePublication (callbacks setup created.seed scalar remember services.other demand publication)
    (transport setup created.seed scalar remember services demand publication nativeDemand nativePublication) reserve packet before

end BeaconcryptCore.Computational.RegistrationNativePlatformServerOpenCtxSourceLeaves

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformServerOpenCtxSourceLeaves.kem_cache' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformServerOpenCtxSourceLeaves.kem_cache

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformServerOpenCtxSourceLeaves.prepare_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformServerOpenCtxSourceLeaves.prepare_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformServerOpenCtxSourceLeaves.indexed_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformServerOpenCtxSourceLeaves.indexed_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformServerOpenCtxSourceLeaves.transport' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformServerOpenCtxSourceLeaves.transport

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformServerOpenCtxSourceLeaves.accept_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformServerOpenCtxSourceLeaves.accept_source
