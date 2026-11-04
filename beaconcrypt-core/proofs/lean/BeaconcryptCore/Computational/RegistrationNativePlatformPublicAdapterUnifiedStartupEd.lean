-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterConfiguration
import BeaconcryptCore.Refinement.AdapterServerConstructorJoint
import BeaconcryptCore.Refinement.AdapterServerConstructorStartup
/-! Concrete startup uses the same original Ed sampler and caller RNG as subsequent source constructors. Its optional representation is derived from the configured total Ed primitive contract with ensureInit fixed to true; no second startup-generation contract is supplied. ML generation retains its original optional failures. -/
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterUnifiedStartupEd
open BeaconcryptCore.Refinement
open AdapterPublicWrapperRequestMonad
open AdapterPublicWrapperRustT (RustT)

 theorem core :AdapterServerConstructorStartup.edCore (pure true)=some <$>PqxdhJointIdentity.sampleSeed :=by
  simp only [AdapterServerConstructorStartup.edCore,StateT.run_pure,pure_bind,ite_true]

variable {I KemSK P E R Error :Type} {base :OracleSpec I} {source :RegistrationNativeMldsa.Source}
variable [material :PublicWrapperPlatform.Material] [platform :PublicWrapperPlatform.Platform]
variable [ed :AdapterInitEdPrimitive.Operations] [primitives :AdapterSealPrimitive.Operations]
variable [PublicWrapperPlatform.Allocator] [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations]
variable [PublicWrapperPlatform.CryptoOperations] [AdapterPublicOrdinaryPlatform.LookupOperations]
variable [FrameDispatchFallback.Operations]
variable [originalGenerators :AdapterBeaconConstructorRequestMonad.Operations (RustT ProbComp)]
variable [originalCrypto :CryptoOperations (RustT ProbComp)]
variable [originalLocal :LocalOperations (RustT (StateT P ProbComp))]
variable [originalContainers :ContainerOperations (RustT (StateT P ProbComp))]
variable {setup :PqxdhServerAuthExperiment.Setup base KemSK} {checks :PqxdhServerAuthExperiment.Checks}
variable (configuration :RegistrationNativePlatformPublicAdapterConfiguration.Configuration
  (P:=P) (E:=E) (R:=R) (Error:=Error) (source:=source) setup checks)

noncomputable def contract :AdapterServerConstructorJoint.EdContract configuration.generator configuration.view setup.joint
    (AdapterServerConstructorStartup.edCore (pure true)) where
  joint:=fun rng=>(fun result=>(some result.1,result.2)) <$>configuration.edGeneration.joint rng
  nativeMarginal:=by
    intro rng
    rw [core]
    have mapped:=congrArg (fun work :ProbComp PqxdhJointIdentity.IdentitySeed=>some <$>work)
      (configuration.edGeneration.nativeMarginal rng)
    simpa only [Functor.map_map,Function.comp_def] using mapped
  realize:=configuration.edGeneration.realize
  privateView:=configuration.edGeneration.privateView
  publicView:=configuration.edGeneration.publicView
  failure:=configuration.edFailure
  operation:=by
    intro rng
    rw [configuration.edGeneration.operation]
    simp only [Functor.map_map]

end BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterUnifiedStartupEd
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterUnifiedStartupEd.core' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterUnifiedStartupEd.core

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterUnifiedStartupEd.contract' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterUnifiedStartupEd.contract
