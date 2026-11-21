-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterExecution
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterUnifiedStartupEd
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterSecurity
import BeaconcryptCore.Computational.RegistrationNativePlatformExtractedDictionaryRecords
/-! Record-origin and corrected UKS bounds for the canonical initialized actual public-adapter execution. Startup uses the same configured Ed generator and pure-true admission. The only additional source-closure contract identifies the individual standard allocation leaf with its public capacity reservation, preserving its complete reply and platform computation. The observer uses the same actual source execution as authentication and agreement; source correspondence is discharged internally. -/
open CoreModels Aeneas OracleComp OracleSpec ENNReal
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterRecordSecurity
open BeaconcryptCore.Refinement
open AdapterPublicWrapperRequestMonad
open AdapterPublicWrapperRustT (RustT)
variable {I KemSK P E R Error Value :Type} {base :OracleSpec I} {source :RegistrationNativeMldsa.Source}
variable [material :PublicWrapperPlatform.Material] [platform :PublicWrapperPlatform.Platform]
variable [ed :AdapterInitEdPrimitive.Operations] [primitives :AdapterSealPrimitive.Operations]
variable [PublicWrapperPlatform.Allocator] [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations]
variable [PublicWrapperPlatform.CryptoOperations] [AdapterPublicOrdinaryPlatform.LookupOperations] [FrameDispatchFallback.Operations]
variable [originalGenerators :AdapterBeaconConstructorRequestMonad.Operations (RustT ProbComp)]
variable [originalCrypto :CryptoOperations (RustT ProbComp)]
variable [originalLocal :LocalOperations (RustT (StateT P ProbComp))]
variable [originalContainers :ContainerOperations (RustT (StateT P ProbComp))]
variable [AdapterServerConstructorPrimitive.Standard]
variable {setup :PqxdhServerAuthExperiment.Setup base KemSK} {checks :PqxdhServerAuthExperiment.Checks}
variable (configuration :RegistrationNativePlatformPublicAdapterConfiguration.Configuration
  (P:=P) (E:=E) (R:=R) (Error:=Error) (source:=source) setup checks)
variable (objects :AdapterServerConstructorObjects.Leaves configuration.views)
variable (allocation :∀before capacity,configuration.allocateJoin before capacity=configuration.reserveFrame capacity.val)


variable (identityIndex :Nat) (serverKeyId :U64) (rng :R) (bounds :PqxdhDeploymentInterface.FreshBounds)
variable (mode :PqxdhDeploymentInterface.Mode)
variable (adversary :RegistrationNativeExperiment.Public→OracleComp (RegistrationNativePlatformPublicAdapterInterface.ModeSpec mode) Value)
variable (budget :PqxdhDeploymentInterface.Budget)
variable (bounded :∀publication,RegistrationNativePlatformPublicAdapterInterface.Respects mode budget (adversary publication))
variable (previous :P)
local notation "compiled"=>fun publication=>RegistrationNativePlatformPublicAdapterInterface.compile mode (adversary publication)
local notation "wire"=>RegistrationNativePlatformConcreteSource.wire
local notation "route"=>RegistrationNativePlatformPublicAdapterRouting.route
local notation "cap"=>budget.cap 4+budget.cap 5
variable (qGenerate qSign qKem qKeygen qEncap :Nat) (caps :RegistrationNativePlatformPublicExternalCaps.Caps)
variable (kind :RegistrationNativePlatformRecordSessionTargets.Kind)
variable (fallback :CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery)
variable (edFallback :PqxdhDynamicIdentityRouting.DynamicForgery) (ordinaryFallback :PqxdhJointIdentity.Forgery)
noncomputable def originLoss :ℝ≥0∞:=RegistrationNativePlatformRecordSessionSecurity.originLoss setup checks route source
  (pure true) identityIndex serverKeyId configuration.keyView configuration.sealFailure configuration.reserveRegistration
  configuration.reservePeer configuration.reserveFrame configuration.erased configuration.reservePackets bounds mode compiled budget previous
  configuration.agreement.representation edFallback ordinaryFallback
noncomputable def targetLoss (target :Fin budget.accept×Fin budget.capacity) :ℝ≥0∞:=
  RegistrationNativePlatformRecordSessionSecurity.targetLoss setup checks route source (pure true) identityIndex serverKeyId
    configuration.keyView configuration.sealFailure configuration.reserveRegistration configuration.reservePeer configuration.reserveFrame
    configuration.erased configuration.reservePackets bounds mode compiled budget previous 0 qGenerate qSign qKem qKeygen qEncap caps kind fallback target
noncomputable def original :ProbComp Bool:=Prod.fst <$>
  ((RegistrationNativePlatformPublicAdapterExecution.profile (n:=cap) configuration identityIndex serverKeyId rng bounds mode adversary
    (fun _ value _=>@decide (RegistrationNativePlatformRecordSessionTargets.Failure setup.source.crypto
      (RegistrationNativeWire.ledgerCodec (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire))
      serverKeyId budget route kind value []) (Classical.propDecidable _))).run previous)

include objects allocation bounded in
theorem bound
    (generation :source.generate.IsTotalQueryBound qGenerate)
    (signing :∀key request,(source.sign key request).IsTotalQueryBound qSign)
    (kemBound :∀(selected :Fin (budget.create+1))
      (parameters :RegistrationNativePlatformG3UniformRecordProgram.Sample KemSK (budget.cap 4+budget.cap 5)) query before,
      ((RegistrationNativeSecretWordKemEarly.actual setup.baseImpl setup.kem selected.val parameters.profile.pairs
        parameters.profile.publicKey parameters.profile.challenge parameters.candidate query).run before).IsTotalQueryBound qKem)
    (keygenBound :(simulateQ (PqxdhInitializerSecrecy.kemAmbientImpl setup.baseImpl) setup.kem.keygen).IsTotalQueryBound qKeygen)
    (encapBound :∀publicKey,(simulateQ (PqxdhInitializerSecrecy.kemAmbientImpl setup.baseImpl) (setup.kem.encaps publicKey)).IsTotalQueryBound qEncap)
    (registrationBound :∀before,(configuration.reserveRegistration.run before).IsTotalQueryBound caps.registration)
    (peerBound :∀before,(configuration.reservePeer.run before).IsTotalQueryBound caps.peer)
    (bytesBound :∀amount before,((configuration.reserveFrame amount).run before).IsTotalQueryBound caps.bytes)
    (packetsBound :∀amount before,((configuration.reservePackets amount).run before).IsTotalQueryBound caps.packet)
    (correct :PqxdhFullSecretInputKdf.SourceFullCorrect setup.source setup.hmac)
    (functional :PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem)
    (candidate :PqxdhKemIndCca.MlKemSharedSecret) (filler :PqxdhServerAuthKeySchedule.Output)
    (shortRejects :∀(publicKey :PqxdhEd25519EufCma.Ed25519PublicKey) bytes,bytes.length<64→setup.source.crypto.verify publicKey.toList bytes=none) :
    𝒟[original configuration identityIndex serverKeyId rng bounds mode adversary budget previous kind] {true}≤
      originLoss configuration identityIndex serverKeyId bounds mode adversary budget previous edFallback ordinaryFallback+
      ∑target:Fin budget.accept×Fin budget.capacity,targetLoss configuration identityIndex serverKeyId bounds mode adversary budget previous
        qGenerate qSign qKem qKeygen qEncap caps kind fallback target :=by
  have transported:=RegistrationNativePlatformPublicAdapterSecurity.profile_event (n:=cap) configuration objects allocation
    identityIndex serverKeyId rng bounds mode adversary (fun result=>@decide
      (RegistrationNativePlatformRecordSessionTargets.Failure setup.source.crypto
        (RegistrationNativeWire.ledgerCodec (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire))
        serverKeyId budget route kind result []) (Classical.propDecidable _))
  simp only [original,transported]
  exact RegistrationNativePlatformExtractedDictionaryRecords.bound setup checks route source (pure true) identityIndex serverKeyId
    configuration.keyView configuration.sealFailure configuration.reserveRegistration configuration.reservePeer configuration.reserveFrame
    configuration.erased configuration.reservePackets bounds mode compiled budget
    (fun publication=>RegistrationNativePlatformPublicAdapterInterface.compile_bound mode budget _ (bounded publication)) previous
    0 qGenerate qSign qKem qKeygen qEncap caps kind configuration.agreement.representation fallback edFallback ordinaryFallback
    (by trivial) generation signing kemBound keygenBound encapBound registrationBound peerBound bytesBound packetsBound correct functional candidate filler shortRejects
    configuration.sealLength configuration.openLength configuration.converted configuration.edFunctional

end BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterRecordSecurity
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterRecordSecurity.bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterRecordSecurity.bound
