-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterExecution
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterLedgerSecurity
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterUnifiedStartupEd
import BeaconcryptCore.Computational.RegistrationNativePlatformExtractedDictionarySecurity
/-! LR and weighted APP bounds for the canonical initialized actual public-adapter execution. Startup uses the same configured Ed generator and pure-true admission. The only additional source-closure contract identifies the individual standard allocation leaf with its public capacity reservation, preserving its complete reply and platform computation. Both observers use the same actual source execution and erase only its operation log internally. -/
open CoreModels Aeneas OracleComp OracleSpec ENNReal
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterSecurity
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

include objects allocation in
theorem profile_event {n :Nat} (identityIndex :Nat) (serverKeyId :U64) (rng :R)
    (bounds :PqxdhDeploymentInterface.FreshBounds) (mode :PqxdhDeploymentInterface.Mode)
    (adversary :RegistrationNativeExperiment.Public→OracleComp (RegistrationNativePlatformPublicAdapterInterface.ModeSpec mode) Value)
    (decision :Value×RegistrationNativeLedger.State→Bool) :
    RegistrationNativePlatformPublicAdapterExecution.profile (n:=n) configuration identityIndex serverKeyId rng bounds mode adversary
      (fun _ value _=>decision value)=
    RegistrationNativePlatformExtractedExperiment.profile (n:=n) setup checks RegistrationNativePlatformConcreteSource.wire
      RegistrationNativePlatformPublicAdapterRouting.route configuration.agreement.representation source (pure true) identityIndex serverKeyId
      configuration.keyView configuration.sealFailure (RegistrationNativePlatformConcreteSource.rawAllocation configuration.reserveFrame)
      configuration.reserveRegistration configuration.reservePeer configuration.reserveFrame configuration.erased
      (RegistrationNativePlatformConcreteSource.helper configuration.reserveFrame)
      (RegistrationNativePlatformConcreteSource.writer configuration.reservePackets) bounds mode
      (fun publication=>RegistrationNativePlatformPublicAdapterInterface.compile mode (adversary publication))
      (fun result=>decision (result.1,result.2.1)) :=
  (RegistrationNativePlatformPublicAdapterExecution.profile_ledger configuration identityIndex serverKeyId rng bounds mode adversary
    (fun result=>decision result.1)).trans
    (RegistrationNativePlatformPublicAdapterLedgerSecurity.profile_event configuration objects allocation identityIndex serverKeyId rng bounds mode adversary decision)

variable (identityIndex :Nat) (serverKeyId :U64) (rng :R) (bounds :PqxdhDeploymentInterface.FreshBounds)
variable (adversary :RegistrationNativeExperiment.Public→OracleComp
  (RegistrationNativePlatformPublicAdapterInterface.ModeSpec PqxdhDeploymentInterface.Mode.P) Value)
variable (budget :PqxdhDeploymentInterface.Budget)
variable (bounded :∀publication,RegistrationNativePlatformPublicAdapterInterface.Respects PqxdhDeploymentInterface.Mode.P budget (adversary publication))
variable (previous :P)
local notation "compiled"=>fun publication=>RegistrationNativePlatformPublicAdapterInterface.compile PqxdhDeploymentInterface.Mode.P (adversary publication)
local notation "wire"=>RegistrationNativePlatformConcreteSource.wire
local notation "canonical"=>RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire
local notation "route"=>RegistrationNativePlatformPublicAdapterRouting.route
local notation "cap"=>budget.cap 4+budget.cap 5
local notation "rawAllocation"=>RegistrationNativePlatformConcreteSource.rawAllocation configuration.reserveFrame
local notation "helper"=>RegistrationNativePlatformConcreteSource.helper configuration.reserveFrame
local notation "writer"=>RegistrationNativePlatformConcreteSource.writer configuration.reservePackets
variable (qGenerate qSign qKem qKeygen qEncap :Nat) (caps :RegistrationNativePlatformPublicExternalCaps.Caps)
variable (fallback :CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery)
variable (edFallback :PqxdhDynamicIdentityRouting.DynamicForgery) (ordinaryFallback :PqxdhJointIdentity.Forgery)
noncomputable def originLoss :ℝ≥0∞:=RegistrationNativePlatformOrdinaryEventComposition.originLoss (n:=cap)
  setup checks route configuration.agreement.representation configuration.keyView configuration.sealFailure rawAllocation
  configuration.reserveRegistration configuration.reservePeer configuration.reserveFrame configuration.erased helper configuration.reservePackets
  source (pure true) identityIndex serverKeyId bounds compiled previous budget.create edFallback ordinaryFallback

variable (generation :source.generate.IsTotalQueryBound qGenerate)
variable (signing :∀key request,(source.sign key request).IsTotalQueryBound qSign)
variable (kemBound :∀(selected :Fin (budget.create+1))
  (parameters :RegistrationNativePlatformG3UniformRecordProgram.Sample KemSK (budget.cap 4+budget.cap 5)) query before,
  ((RegistrationNativeSecretWordKemEarly.actual setup.baseImpl setup.kem selected.val parameters.profile.pairs
    parameters.profile.publicKey parameters.profile.challenge parameters.candidate query).run before).IsTotalQueryBound qKem)
variable (keygenBound :(simulateQ (PqxdhInitializerSecrecy.kemAmbientImpl setup.baseImpl) setup.kem.keygen).IsTotalQueryBound qKeygen)
variable (encapBound :∀publicKey,(simulateQ (PqxdhInitializerSecrecy.kemAmbientImpl setup.baseImpl) (setup.kem.encaps publicKey)).IsTotalQueryBound qEncap)
variable (registrationBound :∀before,(configuration.reserveRegistration.run before).IsTotalQueryBound caps.registration)
variable (peerBound :∀before,(configuration.reservePeer.run before).IsTotalQueryBound caps.peer)
variable (bytesBound :∀amount before,((configuration.reserveFrame amount).run before).IsTotalQueryBound caps.bytes)
variable (packetsBound :∀amount before,((configuration.reservePackets amount).run before).IsTotalQueryBound caps.packet)
variable (correct :PqxdhFullSecretInputKdf.SourceFullCorrect setup.source setup.hmac)
variable (functional :PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem)
variable (candidate :PqxdhKemIndCca.MlKemSharedSecret)
variable (shortRejects :∀(publicKey :PqxdhEd25519EufCma.Ed25519PublicKey) bytes,bytes.length<64→setup.source.crypto.verify publicKey.toList bytes=none)

section Lor
variable (filter :RegistrationNativeLorEvents.Filter Value) (guess :Value→Bool)
noncomputable def lorLoss (target :Fin budget.accept×Fin budget.capacity) (winning :Bool) :ℝ≥0∞:=
  RegistrationNativePlatformExtractedDictionarySecurity.lorLoss setup checks route source (pure true) identityIndex serverKeyId
    configuration.keyView configuration.sealFailure configuration.reserveRegistration configuration.reservePeer configuration.reserveFrame
    configuration.erased configuration.reservePackets bounds compiled budget previous 0 qGenerate qSign qKem qKeygen qEncap caps fallback filter guess target winning
noncomputable def lorBroad (winning :Bool) :ProbComp Bool:=Prod.fst <$>
  ((RegistrationNativePlatformPublicAdapterExecution.profile (n:=cap) configuration identityIndex serverKeyId rng bounds
    PqxdhDeploymentInterface.Mode.P adversary (fun _ value _=>RegistrationNativeLorCoverage.broad setup.source.crypto canonical serverKeyId budget filter guess winning value)).run previous)

include objects allocation bounded generation signing kemBound keygenBound encapBound registrationBound peerBound bytesBound packetsBound correct functional candidate shortRejects in
theorem lor :
    (𝒟[lorBroad configuration identityIndex serverKeyId rng bounds adversary budget previous filter guess true] {true}≤
      2⁻¹*𝒟[lorBroad configuration identityIndex serverKeyId rng bounds adversary budget previous filter guess false] {true}+
      originLoss configuration identityIndex serverKeyId bounds adversary budget previous edFallback ordinaryFallback+
      (∑target,lorLoss configuration identityIndex serverKeyId bounds adversary budget previous qGenerate qSign qKem qKeygen qEncap caps fallback filter guess target true)+
      2⁻¹*(∑target,lorLoss configuration identityIndex serverKeyId bounds adversary budget previous qGenerate qSign qKem qKeygen qEncap caps fallback filter guess target false)) ∧
    (2⁻¹*𝒟[lorBroad configuration identityIndex serverKeyId rng bounds adversary budget previous filter guess false] {true}≤
      𝒟[lorBroad configuration identityIndex serverKeyId rng bounds adversary budget previous filter guess true] {true}+
      originLoss configuration identityIndex serverKeyId bounds adversary budget previous edFallback ordinaryFallback+
      (∑target,lorLoss configuration identityIndex serverKeyId bounds adversary budget previous qGenerate qSign qKem qKeygen qEncap caps fallback filter guess target true)+
      2⁻¹*(∑target,lorLoss configuration identityIndex serverKeyId bounds adversary budget previous qGenerate qSign qKem qKeygen qEncap caps fallback filter guess target false)) :=by
  have transported (winning :Bool):=profile_event (n:=cap) configuration objects allocation identityIndex serverKeyId rng bounds PqxdhDeploymentInterface.Mode.P adversary
    (RegistrationNativeLorCoverage.broad setup.source.crypto canonical serverKeyId budget filter guess winning)
  simp only [lorBroad,transported]
  exact RegistrationNativePlatformExtractedDictionarySecurity.lor setup checks route source (pure true) identityIndex serverKeyId
    configuration.keyView configuration.sealFailure configuration.reserveRegistration configuration.reservePeer configuration.reserveFrame
    configuration.erased configuration.reservePackets bounds compiled budget
    (fun publication=>RegistrationNativePlatformPublicAdapterInterface.compile_bound _ budget _ (bounded publication)) previous
    0 qGenerate qSign qKem qKeygen qEncap caps fallback (by trivial) generation signing kemBound keygenBound encapBound registrationBound peerBound bytesBound packetsBound
    configuration.agreement.representation correct functional candidate shortRejects edFallback ordinaryFallback configuration.sealLength configuration.openLength
    configuration.converted configuration.edFunctional filter guess
end Lor

section App
variable (claim :Value→Option (Nat×Pqxdh.Bytes))
noncomputable def appLoss (target :Fin budget.accept×Fin budget.capacity) (winning :Bool) :ℝ≥0∞:=
  RegistrationNativePlatformExtractedDictionarySecurity.appLoss setup checks route source (pure true) identityIndex serverKeyId
    configuration.keyView configuration.sealFailure configuration.reserveRegistration configuration.reservePeer configuration.reserveFrame
    configuration.erased configuration.reservePackets bounds compiled budget previous 0 qGenerate qSign qKem qKeygen qEncap caps fallback claim target winning
noncomputable def appBroad :ProbComp Bool:=Prod.fst <$>
  ((RegistrationNativePlatformPublicAdapterExecution.profile (n:=cap) configuration identityIndex serverKeyId rng bounds
    PqxdhDeploymentInterface.Mode.P adversary (fun _ value _=>RegistrationNativeEvents.ceAppEvent setup.source.crypto canonical serverKeyId budget claim
      (value.1,(value.2,())))).run previous)

include objects allocation bounded generation signing kemBound keygenBound encapBound registrationBound peerBound bytesBound packetsBound correct functional candidate shortRejects in
theorem app_weighted :
    𝒟[appBroad configuration identityIndex serverKeyId rng bounds adversary budget previous claim] {true}≤
      originLoss configuration identityIndex serverKeyId bounds adversary budget previous edFallback ordinaryFallback+
      ((256^bounds.min:Nat):ℝ≥0∞)⁻¹+
      (∑target,appLoss configuration identityIndex serverKeyId bounds adversary budget previous qGenerate qSign qKem qKeygen qEncap caps fallback claim target true)+
      ((256^bounds.min:Nat):ℝ≥0∞)⁻¹*(∑target,appLoss configuration identityIndex serverKeyId bounds adversary budget previous qGenerate qSign qKem qKeygen qEncap caps fallback claim target false) :=by
  have transported:=profile_event (n:=cap) configuration objects allocation identityIndex serverKeyId rng bounds PqxdhDeploymentInterface.Mode.P adversary
    (fun result=>RegistrationNativeEvents.ceAppEvent setup.source.crypto canonical serverKeyId budget claim (result.1,(result.2,())))
  simp only [appBroad,transported]
  exact RegistrationNativePlatformExtractedDictionarySecurity.app_weighted setup checks route source (pure true) identityIndex serverKeyId
    configuration.keyView configuration.sealFailure configuration.reserveRegistration configuration.reservePeer configuration.reserveFrame
    configuration.erased configuration.reservePackets bounds compiled budget
    (fun publication=>RegistrationNativePlatformPublicAdapterInterface.compile_bound _ budget _ (bounded publication)) previous
    0 qGenerate qSign qKem qKeygen qEncap caps fallback (by trivial) generation signing kemBound keygenBound encapBound registrationBound peerBound bytesBound packetsBound
    configuration.agreement.representation correct functional candidate shortRejects edFallback ordinaryFallback configuration.sealLength configuration.openLength
    configuration.converted configuration.edFunctional claim
end App
end BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterSecurity
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterSecurity.profile_event' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterSecurity.profile_event
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterSecurity.lor' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterSecurity.lor
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterSecurity.app_weighted' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterSecurity.app_weighted
