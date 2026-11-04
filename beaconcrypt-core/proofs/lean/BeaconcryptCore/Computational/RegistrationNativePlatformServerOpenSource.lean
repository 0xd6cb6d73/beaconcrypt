-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformServerOpenKernel
open OracleComp OracleSpec CoreModels Aeneas beaconcrypt_core
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
/-! Actual public indexed agreement and private root memo execute in the same common monad. The full private KEM pool and extra state remain in the left execution; only the stated comparison map projects them. The real-source equations do not identify alternate indexed-KEM policies or their security games. -/
namespace BeaconcryptCore.Computational.RegistrationNativePlatformServerOpenSource
open PqxdhServerAuthExperiment (Setup Checks)
open PqxdhSecretInputKdf (RootOutput)
open RegistrationNativeRelatedFamily (Message)
open RegistrationNativeKemReferenceWorld (Private)
open RegistrationNativePlatformServerOpenKernel
variable {n : Nat} {ι KemSK Extra : Type} {base : OracleSpec ι}
variable {m : Type → Type} [Monad m] [LawfulMonad m]

noncomputable def prepare (setup : Setup base KemSK) (seed : PqxdhJointIdentity.IdentitySeed)
    (scalar : PqxdhJointGapDh.ScalarBytes) (remember : Extra → Message → Option RootOutput → Extra) :
    QueryImpl RegistrationServerReferenceRoot.PrepareSpec (StateT (Private n KemSK Extra) m) := fun message before =>
  let root := RegistrationNativeSourceRoot.value setup.source setup.joint setup.dh seed scalar message
  pure (root.map (fun _ => message), { before with extra := remember before.extra message root })

omit [LawfulMonad m] in
theorem prepare_lift (coins : QueryImpl unifSpec m) (setup : Setup base KemSK) (seed : PqxdhJointIdentity.IdentitySeed)
    (scalar : PqxdhJointGapDh.ScalarBytes) (remember : Extra → Message → Option RootOutput → Extra)
    (message : Message) :
    prepare (n := n) setup seed scalar remember message =
      RegistrationNativePlatformInterpret.state coins (RegistrationServerOpenReferenceSourceStage.prepare setup seed scalar remember message) := by
  funext before
  simp only [prepare, RegistrationNativePlatformInterpret.state, StateT.run,
    RegistrationServerOpenReferenceSourceStage.prepare, simulateQ_pure]

noncomputable def callbacks (setup : Setup base KemSK) (seed : PqxdhJointIdentity.IdentitySeed)
    (scalar : PqxdhJointGapDh.ScalarBytes) (remember : Extra → Message → Option RootOutput → Extra)
    (services : RegistrationNativeKemReferenceEffects.Callbacks n KemSK Extra)
    (demand : QueryImpl (Message →ₒ Option (RegistrationNativePairedChoice.Choice n)) (StateT (Private n KemSK Extra) m))
    (publication : QueryImpl RegistrationBoundPublication.Spec (StateT (Private n KemSK Extra) m)) : Callbacks n KemSK Extra m where
  other := services.other
  prepare := prepare setup seed scalar remember
  demand := demand
  publication := publication

theorem source (coins : QueryImpl unifSpec m) (setup : Setup base KemSK) (checks : Checks)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (remember : Extra → Message → Option RootOutput → Extra)
    (services : RegistrationNativeKemReferenceEffects.Callbacks n KemSK Extra)
    (demand : QueryImpl (Message →ₒ Option (RegistrationNativePairedChoice.Choice n)) (StateT (Private n KemSK Extra) m))
    (publication : QueryImpl RegistrationBoundPublication.Spec (StateT (Private n KemSK Extra) m))
    (packet : registration.InitPacket) (authenticated : registration.AuthenticatedInit)
    (before : RegistrationNativeKemReferenceBackend.State n KemSK Extra) :
    (closeEnvironment (localAgreement (handler coins setup
      (callbacks setup seed scalar remember services demand publication)) setup checks packet authenticated)).run before =
    simulateQ coins ((RegistrationServerOpenReferenceSourceStage.agreement setup checks seed scalar remember services packet authenticated).run before) := by
  rw [localAgreement_independent coins setup checks
    (callbacks setup seed scalar remember services demand publication)
    (liftCallbacks coins (RegistrationServerOpenReferenceSourceStage.callbacks setup seed scalar remember services)) rfl
    (funext (prepare_lift coins setup seed scalar remember))]
  exact localAgreement_source coins setup checks seed scalar remember services packet authenticated before

theorem project (coins : QueryImpl unifSpec m) (setup : Setup base KemSK) (checks : Checks)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (remember : Extra → Message → Option RootOutput → Extra)
    (services : RegistrationNativeKemReferenceEffects.Callbacks n KemSK Extra)
    (demand : QueryImpl (Message →ₒ Option (RegistrationNativePairedChoice.Choice n)) (StateT (Private n KemSK Extra) m))
    (publication : QueryImpl RegistrationBoundPublication.Spec (StateT (Private n KemSK Extra) m))
    (packet : registration.InitPacket) (authenticated : registration.AuthenticatedInit)
    (before : RegistrationNativeKemReferenceBackend.State n KemSK Extra) :
    Prod.map id RegistrationNativeKemReferenceBackend.project <$>
      (closeEnvironment (localAgreement (handler coins setup
        (callbacks setup seed scalar remember services demand publication)) setup checks packet authenticated)).run before =
    simulateQ coins ((RegistrationServerReferenceSourceStage.referenceStage setup checks seed scalar packet authenticated).run
      (RegistrationNativeKemReferenceBackend.project before)) := by
  rw [source, ← simulateQ_map, RegistrationServerOpenReferenceSourceStage.agreement_project]

theorem collect_source (coins : QueryImpl unifSpec m) (setup : Setup base KemSK) (checks : Checks)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (remember : Extra → Message → Option RootOutput → Extra)
    (services : RegistrationNativeKemReferenceEffects.Callbacks n KemSK Extra)
    (demand : QueryImpl (Message →ₒ Option (RegistrationNativePairedChoice.Choice n)) (StateT (Private n KemSK Extra) m))
    (publication : QueryImpl RegistrationBoundPublication.Spec (StateT (Private n KemSK Extra) m))
    (packet : registration.InitPacket) (authenticated : registration.AuthenticatedInit)
    (before : RegistrationNativeKemReferenceBackend.State n KemSK Extra) :
    (closeEnvironment (collect (handler coins setup
      (callbacks setup seed scalar remember services demand publication)) setup checks packet authenticated)).run before =
    simulateQ coins ((RegistrationNativeKemReferencePrefix.lower setup
      (RegistrationServerOpenReferenceSourceStage.callbacks setup seed scalar remember services)
      (RegistrationNativeKemReferenceCompiler.collect setup checks packet authenticated)).run before) := by
  rw [collect_independent coins setup checks
    (callbacks setup seed scalar remember services demand publication)
    (liftCallbacks coins (RegistrationServerOpenReferenceSourceStage.callbacks setup seed scalar remember services)) rfl
    (funext (prepare_lift coins setup seed scalar remember))]
  exact environment_source coins setup _ _ before

theorem native (coins : QueryImpl unifSpec m) (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (correct : PqxdhSecretInputKdf.SourceRootCorrect setup.source setup.hmac)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (remember : Extra → Message → Option RootOutput → Extra)
    (services : RegistrationNativeKemReferenceEffects.Callbacks n KemSK Extra)
    (demand : QueryImpl (Message →ₒ Option (RegistrationNativePairedChoice.Choice n)) (StateT (Private n KemSK Extra) m))
    (publication : QueryImpl RegistrationBoundPublication.Spec (StateT (Private n KemSK Extra) m))
    (control : pqxdh.ServerState) (packet : registration.InitPacket) (authenticated : registration.AuthenticatedInit)
    (before : RegistrationNativeKemReferenceBackend.State n KemSK Extra) :
    Prod.map (RegistrationServerReferenceSourceClient.restore
      (RegistrationServerReferenceSourceClient.roots setup.source setup.joint setup.dh seed scalar))
      RegistrationNativeKemReferenceBackend.project <$>
      (closeEnvironment (localAgreement (handler coins setup
        (callbacks setup seed scalar remember services demand publication)) setup checks packet authenticated)).run before =
    simulateQ coins ((simulateQ (RegistrationWorldAgreement.agreement setup.source
      (RegistrationServerRoleBackend.native setup checks representation seed))
      (RegistrationAgreementExecutor.server control .Fresh authenticated)).run
      (RegistrationNativeKemReferenceBackend.project before)) := by
  have compared := congrArg (fun work => Prod.map (RegistrationServerReferenceSourceClient.restore
      (RegistrationServerReferenceSourceClient.roots setup.source setup.joint setup.dh seed scalar)) id <$> work)
    (project coins setup checks seed scalar remember services demand publication packet authenticated before)
  rw [← simulateQ_map, RegistrationServerReferenceSourceStage.reference_native setup checks representation correct
    seed scalar control packet authenticated (RegistrationNativeKemReferenceBackend.project before)] at compared
  simpa only [Functor.map_map, Prod.map_def, id_eq] using compared

end BeaconcryptCore.Computational.RegistrationNativePlatformServerOpenSource

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformServerOpenSource.prepare_lift' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformServerOpenSource.prepare_lift

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformServerOpenSource.source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformServerOpenSource.source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformServerOpenSource.project' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformServerOpenSource.project

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformServerOpenSource.collect_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformServerOpenSource.collect_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformServerOpenSource.native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformServerOpenSource.native
