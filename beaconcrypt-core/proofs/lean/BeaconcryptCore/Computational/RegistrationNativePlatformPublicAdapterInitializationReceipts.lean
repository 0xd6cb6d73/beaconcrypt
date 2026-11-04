-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterInitializationPhysical
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterInitializationReceipts
open BeaconcryptCore.Refinement
open AdapterPublicWrapperRustT (RustT)
open AdapterPublicWrapperRequestMonad
variable {n :Nat} {I KemSK R Error P :Type} {base :OracleSpec I} {source :RegistrationNativeMldsa.Source}
variable [material :PublicWrapperPlatform.Material] [platform :PublicWrapperPlatform.Platform]
variable [ed :AdapterInitEdPrimitive.Operations] [PublicWrapperPlatform.Allocator]
variable [AdapterServerConstructorPrimitive.Standard]
variable [originalGenerators :AdapterBeaconConstructorRequestMonad.Operations (RustT ProbComp)]
variable [originalCrypto :CryptoOperations (RustT ProbComp)]
variable [originalLocal :LocalOperations (RustT (StateT P ProbComp))]
variable (setup :PqxdhServerAuthExperiment.Setup base KemSK)
variable (generator :rand_core.TryCryptoRng R Error) (view :AdapterPublicWrapperState.MaterialView source KemSK)
local notation "World"=>PqxdhRecordLiftWorld.State n
local notation "WorldM"=>StateT (PqxdhRecordLiftWorld.State n) ProbComp
noncomputable local instance generators :AdapterBeaconConstructorRequestMonad.Operations (RustT WorldM):=
  RegistrationNativePlatformPublicAdapterInitialization.generators (n:=n)
noncomputable local instance cryptography :CryptoOperations (RustT WorldM):=
  RegistrationNativePlatformPublicAdapterInitialization.cryptography (n:=n)
noncomputable local instance children :ChildOperations (RustT WorldM):=
  RegistrationNativePlatformPublicAdapterInitialization.children (n:=n)

omit [PublicWrapperPlatform.Allocator] in
theorem ready (previous :P) (identityIndex :Nat) (identifier :U64) (rng :R)
    (result :AdapterServerConstructorRunner.Receipt n KemSK R source×PqxdhRecordLiftWorld.State n)
    (ready :AdapterServerConstructorInitialized.Ready n KemSK R source)
    (supported :result∈support (RegistrationNativePlatformPublicAdapterInitializationPhysical.raw (n:=n) setup generator view previous identityIndex identifier rng))
    (returned :result.1.ready=some ready) :
    ready.initial.state.server.world.world.2=[] :=by
  let :LocalOperations (RustT WorldM):=RegistrationNativePlatformPublicAdapterInitialization.localOperations (n:=n) previous
  simp only [RegistrationNativePlatformPublicAdapterInitializationPhysical.raw,AdapterServerConstructorRunner.run,StateT.run_bind,bind_pure_comp,mem_support_bind_iff] at supported
  obtain ⟨⟨called,current⟩,_generated,continued⟩:=supported
  cases called with
  | fail error | div=>
    cases continued
    cases returned
  | ok outcome=>
    rcases outcome with ⟨selected,nextRng⟩
    cases selected with
    | Err error=>
      cases continued
      cases returned
    | Ok self=>
      simp only [StateT.run_map,support_map] at continued
      obtain ⟨finished,reached,same⟩:=continued
      cases same
      unfold AdapterServerConstructorInitialized.finish at reached
      simp only [StateT.run,mem_support_bind_iff] at reached
      obtain ⟨installed,_installed,pinned,_pinned,closed⟩:=reached
      simp only [mem_support_pure_iff] at closed
      cases closed
      cases calledPin:pinned.1 with
      | fail error | div=>simp only [calledPin] at returned;cases returned
      | ok optional=>cases optional with
        | none=>simp only [calledPin] at returned;cases returned
        | some pin=>
          simp only [calledPin,Option.some.injEq] at returned
          cases returned
          rfl

end BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterInitializationReceipts

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterInitializationReceipts.ready' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterInitializationReceipts.ready
