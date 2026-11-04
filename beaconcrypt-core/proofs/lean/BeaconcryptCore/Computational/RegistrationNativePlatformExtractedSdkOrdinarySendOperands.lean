-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinarySendCommon
import BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinaryServerShell
open CoreModels Aeneas OracleComp OracleSpec beaconcrypt_core
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
namespace BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinarySendOperands
open BeaconcryptCore.Refinement
open PqxdhServerAuthExperiment (Setup Codec)
open RegistrationNativePlatformExtractedSdkOrdinaryDriver (M)
open RegistrationNativePlatformExtractedSdkOrdinarySendCommon (project ownerNative owner_noop)
variable {Platform E I KemSK Reader Response : Type} {base : OracleSpec I}
variable [primitives : AdapterSealPrimitive.Operations] [FrameDispatchFallback.Operations]
def owner (target : U64) (associated : Array U8 281#usize)
    (kernel : ratchet.concrete.ConcreteRatchetKernel) (rawBefore : Nat) : RawCtxWholeOwner.OwnerState Unit :=
  ⟨⟨kernel,target,PqxdhRefinement.absBytes associated,()⟩,rawBefore⟩
noncomputable def sample (setup : Setup base KemSK) (codec : Codec Reader Response)
    (reserve : Nat →StateT Platform ProbComp (core.result.Result Unit E))
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitives.Error)
    (erased : commitment.CommitmentTranscript) (target sender : U64) (associated : Array U8 281#usize)
    (kernel : ratchet.concrete.ConcreteRatchetKernel) (bytes : Slice U8) :
    M Platform (RustM AdapterRecordStatefulSend.Result) :=
  match AdapterPublicOrdinaryEnvelope.prepareSend bytes target sender associated kernel with
  | .ok (some context)=>RegistrationNativePlatformExtractedSdkOrdinaryDriver.send setup codec reserve view failure erased kernel context
  | _=>pure (.ok (kernel,none))
theorem native (setup : Setup base KemSK) (codec : Codec Reader Response)
    (reserve : Nat →StateT Platform ProbComp (core.result.Result Unit E))
    (length : RegistrationNativePlatformOrdinarySourceWorld.AeadLength setup.source.crypto)
    (view : RegistrationNativePlatformSourceSeal.KeyView)
    (converted : RegistrationNativePlatformOrdinarySourceNative.Conversion view)
    (failure : primitives.Error) (erased : commitment.CommitmentTranscript)
    (target sender : U64) (associated : Array U8 281#usize) (kernel : ratchet.concrete.ConcreteRatchetKernel) (bytes : Slice U8) (rawBefore : Nat) :
    project (owner target associated kernel rawBefore) <$>
      sample setup codec reserve view failure erased target sender associated kernel bytes =
    if CborRecordWorldClient.nextFits bytes.val.length kernel.refined.control.send_sequence.val sender.val then
      ownerNative setup codec reserve (owner target associated kernel rawBefore) sender bytes
    else pure (none,owner target associated kernel rawBefore) := by
  unfold sample
  rw [AdapterPublicOrdinarySendGate.prepare]
  cases empty : bytes.val.isEmpty with
  | true=>
      simp only [ite_true,map_pure]
      cases fits : CborRecordWorldClient.nextFits bytes.val.length kernel.refined.control.send_sequence.val sender.val
      · rfl
      · simp only [ite_true]
        exact (owner_noop setup codec reserve _ _ bytes (Or.inl empty)).symm
  | false=>
      simp only [Bool.false_eq_true,ite_false]
      by_cases live : kernel.refined.control.send_sequence.val<UScalar.max .U64
      · simp only [live,ite_true]
        cases fits : CborRecordWorldClient.nextFits bytes.val.length kernel.refined.control.send_sequence.val sender.val
        · rfl
        · simp only [ite_true]
          exact RegistrationNativePlatformExtractedSdkOrdinarySendCommon.native setup codec reserve length view converted failure erased _ bytes sender associated rfl
      · have exhausted : kernel.refined.control.send_sequence=core.num.U64.MAX := by
          apply UScalar.eq_of_val_eq
          have maximum : core.num.U64.MAX.val=UScalar.max .U64 := by
            simp [core.num.U64.MAX,U64.rMax,UScalar.max_def]
          rw [maximum]
          have bound := kernel.refined.control.send_sequence.hmax
          simp only [UScalar.max_def] at live ⊢
          omega
        simp only [live,ite_false,map_pure]
        cases fits : CborRecordWorldClient.nextFits bytes.val.length kernel.refined.control.send_sequence.val sender.val
        · rfl
        · simp only [ite_true]
          exact (owner_noop setup codec reserve _ _ bytes (Or.inr exhausted)).symm

theorem normal (setup : Setup base KemSK) (codec : Codec Reader Response)
    (reserve : Nat →StateT Platform ProbComp (core.result.Result Unit E))
    (length : RegistrationNativePlatformOrdinarySourceWorld.AeadLength setup.source.crypto)
    (view : RegistrationNativePlatformSourceSeal.KeyView)
    (converted : RegistrationNativePlatformOrdinarySourceNative.Conversion view)
    (failure : primitives.Error) (erased : commitment.CommitmentTranscript)
    (target sender : U64) (associated : Array U8 281#usize) (kernel : ratchet.concrete.ConcreteRatchetKernel) (bytes : Slice U8)
    (before after : RegistrationNativePlatformExtractedSdkOrdinaryDriver.State) (previous next : Platform)
    (reply : RustM AdapterRecordStatefulSend.Result)
    (supported : ((reply,after),next) ∈support
      (((sample setup codec reserve view failure erased target sender associated kernel bytes).run before).run previous)) :
    ∃value,reply=.ok value := by
  unfold sample at supported
  rw [AdapterPublicOrdinarySendGate.prepare] at supported
  split_ifs at supported
  all_goals first
    | exact RegistrationNativePlatformExtractedSdkOrdinaryDriver.send_normal setup codec reserve length view converted failure erased
        (owner target associated kernel 0) bytes sender associated rfl before after previous next reply supported
    | simp only [StateT.run_pure,support_pure,Set.mem_singleton_iff] at supported
      exact ⟨(kernel,none),congrArg (fun result=>result.1.1) supported⟩

variable [material : PublicWrapperPlatform.Material] [platform : PublicWrapperPlatform.Platform]
variable [PublicWrapperPlatform.Allocator] [ed : AdapterInitEdPrimitive.Operations]
variable [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations]
variable [AdapterPublicOrdinaryPlatform.LookupOperations]
open AdapterPublicWrapperStorage
open AdapterPublicWrapperRustT (RustT)

def returned (self : beaconcrypt_public_wrapper.server.Server)
    (remote : Remote ed.PublicKey) (back : Option (Remote ed.PublicKey) →PeerMap) :
    RustM AdapterRecordStatefulSend.Result →RustM (Option beaconcrypt_record_send.shared.Encrypted ×beaconcrypt_public_wrapper.server.Server)
  | .ok result =>.ok (result.2,AdapterPublicOrdinaryServerLookup.restore self (some remote) back
      (some (AdapterPublicOrdinaryEnvelope.manager result.1)))
  | .fail error =>.fail error
  | .div =>.div

omit [PublicWrapperPlatform.Allocator] [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations]
  [AdapterPublicOrdinaryPlatform.LookupOperations] primitives [FrameDispatchFallback.Operations] in
private theorem returned_run (self : beaconcrypt_public_wrapper.server.Server)
    (remote : Remote ed.PublicKey) (back : Option (Remote ed.PublicKey) →PeerMap)
    (work : M Platform (RustM AdapterRecordStatefulSend.Result)) :
    (do
      let result←(⟨work⟩ :RustT (M Platform) _)
      pure (result.2,AdapterPublicOrdinaryServerLookup.restore self (some remote) back
        (some (AdapterPublicOrdinaryEnvelope.manager result.1)))).run =returned self remote back <$>work := by
  rw [RustT.run_bind]
  simp only [RustT.run_pure]
  rw [←bind_pure_comp]
  apply bind_congr
  intro result
  cases result <;>rfl

omit [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations] in
theorem source_kernel (setup : Setup base KemSK) (codec : Codec Reader Response)
    (reserve : Nat →StateT Platform ProbComp (core.result.Result Unit E))
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitives.Error)
    (erased : commitment.CommitmentTranscript) (self : beaconcrypt_public_wrapper.server.Server)
    (remote : Remote ed.PublicKey) (back : Option (Remote ed.PublicKey) →PeerMap)
    (kernel : ratchet.concrete.ConcreteRatchetKernel) (bytes : Slice U8) (target : U64) :
    letI:=RegistrationNativePlatformExtractedSdkOrdinary.operations setup codec reserve view failure erased
    returned self remote back <$>
      sample setup codec reserve view failure erased target (platform.arcView self.identity).identity_key_kid
        remote.peer.binding.associated_data kernel bytes =
    (RegistrationNativePlatformExtractedSdkOrdinaryServerShell.sendKernel
      self bytes target remote back kernel :RustT (M Platform) _).run := by
  let := RegistrationNativePlatformExtractedSdkOrdinary.operations setup codec reserve view failure erased
  unfold RegistrationNativePlatformExtractedSdkOrdinaryServerShell.sendKernel sample
  simp only [RustT.run_bind,RustT.run_liftRust,pure_bind]
  rw [AdapterPublicOrdinarySendGate.prepare]
  split_ifs <;>simp only [map_pure,returned,RustT.run_pure]
  exact (returned_run self remote back _).symm

theorem source (setup : Setup base KemSK) (codec : Codec Reader Response)
    (reserve : Nat →StateT Platform ProbComp (core.result.Result Unit E))
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitives.Error)
    (erased : commitment.CommitmentTranscript) (views : Views) (self : beaconcrypt_public_wrapper.server.Server)
    (remote : Remote ed.PublicKey) (back : Option (Remote ed.PublicKey) →PeerMap)
    (kernel : ratchet.concrete.ConcreteRatchetKernel) (bytes : Slice U8) (target : U64)
    (selected : views.peer self.known_ids target=some remote)
    (stored : remote.peer.ratchet.refined.kernel=some kernel)
    (get : letI:=RegistrationNativePlatformExtractedSdkOrdinary.operations setup codec reserve view failure erased
      AdapterPublicOrdinaryServerLookup.read (m:=M Platform) self.known_ids target=pure (views.peer self.known_ids target))
    (borrow : letI:=RegistrationNativePlatformExtractedSdkOrdinary.operations setup codec reserve view failure erased
      AdapterPublicOrdinaryServerLookup.borrow (m:=M Platform) self.known_ids target=pure (views.peer self.known_ids target,back)) :
    returned self remote back <$>
      sample setup codec reserve view failure erased target (platform.arcView self.identity).identity_key_kid
        remote.peer.binding.associated_data kernel bytes =
    RegistrationNativePlatformExtractedSdkOrdinary.serverSend setup codec reserve view failure erased self bytes target := by
  let := RegistrationNativePlatformExtractedSdkOrdinary.operations setup codec reserve view failure erased
  rw [RegistrationNativePlatformExtractedSdkOrdinaryServerShell.server_send setup codec reserve view failure erased views self bytes target back get borrow,
    selected,RegistrationNativePlatformExtractedSdkOrdinaryServerShell.send_kernel self bytes target remote back kernel stored]
  exact source_kernel setup codec reserve view failure erased self remote back kernel bytes target

end BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinarySendOperands

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinarySendOperands.native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinarySendOperands.native

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinarySendOperands.normal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinarySendOperands.normal

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinarySendOperands.source_kernel' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinarySendOperands.source_kernel

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinarySendOperands.source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinarySendOperands.source
