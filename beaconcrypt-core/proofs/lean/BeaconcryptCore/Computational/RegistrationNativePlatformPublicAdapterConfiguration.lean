-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBundleRawSteps
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterCreateNormalized
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAcceptNormalized
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterOrdinaryRawSteps
import BeaconcryptCore.Computational.RegistrationNativePlatformSdkFinishPhysical
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterInitialization
import BeaconcryptCore.Refinement.AdapterServerConstructorGeneration
/-! The concrete public adapter is configured only by original primitive operations, their individual functional/sampling contracts and standard collection leaves. No callback, source-profile, security-event or complete local correspondence is a field. The same configuration is independent of startup's sampled Server identity and credential. -/
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterConfiguration
open BeaconcryptCore.Refinement
open AdapterPublicWrapperRequestMonad
open AdapterPublicWrapperRustT (RustT)
open AdapterPublicWrapperStorage (Views ReplaySet PeerMap Remote)
variable {I KemSK P E R Error : Type} {base : OracleSpec I} {source : RegistrationNativeMldsa.Source}
variable [material : PublicWrapperPlatform.Material] [platform : PublicWrapperPlatform.Platform]
variable [ed : AdapterInitEdPrimitive.Operations] [primitives : AdapterSealPrimitive.Operations]
variable [PublicWrapperPlatform.Allocator] [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations]
variable [PublicWrapperPlatform.CryptoOperations] [AdapterPublicOrdinaryPlatform.LookupOperations]
variable [FrameDispatchFallback.Operations]
variable [originalGenerators : AdapterBeaconConstructorRequestMonad.Operations (RustT ProbComp)]
variable [originalCrypto : CryptoOperations (RustT ProbComp)]
variable [originalLocal : LocalOperations (RustT (StateT P ProbComp))]
variable [originalContainers : ContainerOperations (RustT (StateT P ProbComp))]

structure Configuration (setup : PqxdhServerAuthExperiment.Setup base KemSK) (checks : PqxdhServerAuthExperiment.Checks) where
  view : AdapterPublicWrapperState.MaterialView source KemSK
  views : Views
  generator : rand_core.TryCryptoRng R Error
  agreement : AdapterPublicAgreementPrimitiveModel.Model (m:=ProbComp) generator setup checks view
  entropy : AdapterPublicAgreementServerNative.Entropy agreement
  kem : AdapterBeaconConstructorKem.Representation view R
  mlGeneration : AdapterServerConstructorGeneration.MldsaContract generator view (RegistrationNativeMldsa.generate source)
  edGeneration : AdapterBeaconConstructorGeneration.EdContract generator view setup.joint PqxdhJointIdentity.sampleSeed
  prekeyGeneration : AdapterBeaconConstructorGeneration.KxContract generator view
    (fun scalar=>PqxdhRootTableInitialization.rootArray (setup.dh.publicKey scalar)) PqxdhJointGapDh.sampleScalar
  kemGeneration : RegistrationNativePlatformPublicAdapterCreateKem.Contract view setup kem generator
  pins : RegistrationNativePlatformPublicAdapterPinParsing.EdContract view
  decapsulation : RegistrationNativePlatformSdkFinishDecapsulation.Aligned setup agreement.decapsulate
  edFunctional : RegistrationNativePlatformAuthentication.EdFunctional setup.source.crypto
  edGetter : ∀key,originalCrypto.edPublicBytes key=pure (view.edPublic key)
  mlGetter : ∀identity,(originalLocal.auth_MldsaIdentity_public_key identity).run=pure (.ok (view.mldsa identity).publicKey)
  keyView : RegistrationNativePlatformSourceSeal.KeyView
  converted : RegistrationNativePlatformOrdinarySourceNative.Conversion keyView
  sealLength : RegistrationNativePlatformOrdinarySourceWorld.AeadLength setup.source.crypto
  openLength : RegistrationNativeExtractedReceive.AeadLength setup.source.crypto
  sealFailure : primitives.Error
  edFailure : ed.Error
  initial : ∀request,(originalLocal.ratchet_initial_ratchet_hkdf request).run=
    pure (.ok (RawCtxSourceHkdf.initialResponse setup.source.crypto request).bytes)
  reserveFrame : Nat→StateT P ProbComp (core.result.Result Unit E)
  reservePackets : Usize→StateT P ProbComp (core.result.Result Unit E)
  allocateJoin : alloc.vec.Vec U8→Usize→StateT P ProbComp (core.result.Result Unit E)
  erased : commitment.CommitmentTranscript
  parseEd : Slice U8→StateT P ProbComp (RustM (core.result.Result ed.PublicKey ed.Error))
  verifyEd : Slice U8→ed.PublicKey→StateT P ProbComp (RustM (core.option.Option (alloc.vec.Vec U8)))
  reserveRegistration : StateT P ProbComp Bool
  reservePeer : StateT P ProbComp Bool
  replayAllocate : ReplaySet→StateT P ProbComp AdapterPublicServerReservationNative.AllocationReply
  replayReserve : ∀history,(AdapterPublicServerAcceptBody.setReserve (m:=StateT P ProbComp) history).run=
    RustM.ok <$>replayAllocate history
  replayAdmission : ∀history,(fun result : AdapterPublicServerReservationNative.AllocationReply=>
    match result.1 with | .Err _=>false | .Ok _=>true) <$>replayAllocate history=reserveRegistration
  replayFootprint : ∀history before result after,(result,after)∈support ((replayAllocate history).run before)→
    AdapterPublicWrapperStorage.ReplayReserve views history result
  replayMember : ∀history identifier,AdapterPublicServerReplayPrefix.contains (m:=StateT P ProbComp) history identifier=
    pure (views.replay history identifier)
  replayInsert : ∀history identifier,∃result,
    AdapterPublicServerAcceptBody.setInsert (m:=StateT P ProbComp) history identifier=pure result ∧
    AdapterPublicWrapperStorage.ReplayInsert views history identifier result
  peerAllocate : PeerMap→StateT P ProbComp AdapterPublicServerBuildPrefix.AllocationReply
  peerReserve : ∀known,(originalContainers.mapReserve core.U64.Insts.CoreCmpEq core.U64.Insts.CoreHashHash
    beaconcrypt_public_request.collections.KeyedHasher.Insts.CoreHashBuildHasherSipHasher13
    hashbrown.alloc.inner.Global.Insts.HashbrownAllocInnerAllocator known 1#usize).run=
    RustM.ok <$>peerAllocate known
  peerAdmission : ∀known,AdapterPublicServerBuildPrefix.admitted <$>peerAllocate known=reservePeer
  peerFootprint : ∀known before result after,(result,after)∈support ((peerAllocate known).run before)→
    AdapterPublicWrapperStorage.PeerReserve views known result
  peerMember : ∀known identifier,(originalContainers.mapContains core.U64.Insts.CoreCmpEq core.U64.Insts.CoreHashHash
    beaconcrypt_public_request.collections.KeyedHasher.Insts.CoreHashBuildHasherSipHasher13
    hashbrown.alloc.inner.Global.Insts.HashbrownAllocInnerAllocator core.U64.Insts.CoreHashHash
    (hashbrown.Equivalent.Blanket core.U64.Insts.CoreCmpEq (core.borrow.Borrow.Blanket U64)) known identifier).run=
    pure (.ok (views.peer known identifier).isSome)
  peerInstall : ∀self pending publicKey,AdapterPublicServerInstallFunctional.Standard (m:=StateT P ProbComp) views self pending publicKey
  peerBack : PeerMap→U64→Option (Remote ed.PublicKey)→PeerMap
  peerLens : ∀known target changed query,views.peer (peerBack known target changed) query=
    if query=target then changed else views.peer known query
  peerGet : ∀known key,AdapterPublicOrdinaryPlatform.LookupOperations.get core.U64.Insts.CoreCmpEq core.U64.Insts.CoreHashHash
    beaconcrypt_public_wrapper.collections.KeyedHasher.Insts.CoreHashBuildHasherSipHasher13
    hashbrown.alloc.inner.Global.Insts.HashbrownAllocInnerAllocator core.U64.Insts.CoreHashHash
    (hashbrown.Equivalent.Blanket core.U64.Insts.CoreCmpEq (core.borrow.Borrow.Blanket U64)) known key=.ok (views.peer known key)
  peerBorrow : ∀known key,AdapterPublicOrdinaryPlatform.LookupOperations.getMut core.U64.Insts.CoreCmpEq core.U64.Insts.CoreHashHash
    beaconcrypt_public_wrapper.collections.KeyedHasher.Insts.CoreHashBuildHasherSipHasher13
    hashbrown.alloc.inner.Global.Insts.HashbrownAllocInnerAllocator core.U64.Insts.CoreHashHash
    (hashbrown.Equivalent.Blanket core.U64.Insts.CoreCmpEq (core.borrow.Borrow.Blanket U64)) known key=.ok (views.peer known key,peerBack known key)

variable {setup : PqxdhServerAuthExperiment.Setup base KemSK} {checks : PqxdhServerAuthExperiment.Checks}
variable (configuration : Configuration (P:=P) (E:=E) (R:=R) (Error:=Error) (source:=source) setup checks)

noncomputable def common : AdapterPublicAgreementCommonModel.Model (m:=ProbComp) setup configuration.view where
  representation:=configuration.agreement.representation
  scalar:=configuration.agreement.scalar
  getters:=configuration.agreement.getters
  identity:=configuration.agreement.identity
  conversion:=configuration.agreement.conversion
  hkdf:=configuration.agreement.hkdf
  decapsulate:=configuration.agreement.decapsulate
  decapView:=configuration.agreement.decapView
  cipherParsing:=configuration.agreement.cipherParsing
  shared:=configuration.agreement.shared
  decap:=configuration.agreement.decap

noncomputable def generation : AdapterPublicAgreementGeneration.Contract configuration.generator configuration.view
    (fun scalar=>PqxdhRootTableInitialization.rootArray (setup.dh.publicKey scalar)) PqxdhJointGapDh.sampleScalar :=by
  simpa only [configuration.entropy.sample] using configuration.agreement.generation

end BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterConfiguration

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterConfiguration.common' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterConfiguration.common

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterConfiguration.generation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterConfiguration.generation
