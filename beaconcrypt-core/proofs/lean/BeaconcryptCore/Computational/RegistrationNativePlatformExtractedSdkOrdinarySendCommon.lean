-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinaryBeacon
open CoreModels Aeneas OracleComp OracleSpec beaconcrypt_core
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
namespace BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinarySendCommon
open BeaconcryptCore.Refinement
open PqxdhServerAuthExperiment (Setup Codec)
open RegistrationNativePlatformExtractedSdkOrdinaryDriver (M)
variable {Platform E I KemSK Reader Response : Type} {base : OracleSpec I}
variable [primitives : AdapterSealPrimitive.Operations] [FrameDispatchFallback.Operations]

def project {Metadata : Type} (owner : RawCtxWholeOwner.OwnerState Metadata) :
    RustM AdapterRecordStatefulSend.Result →Option RawCtxSourceSend.Encrypted ×RawCtxWholeOwner.OwnerState Metadata :=
  RegistrationNativePlatformOrdinarySourceLoggedWorld.total owner ∘
    RegistrationNativePlatformOrdinarySourceReceiptOwner.ownerResult owner ∘
    RegistrationNativePlatformOrdinarySourceReceipt.abstractOutput

theorem native (setup : Setup base KemSK) (codec : Codec Reader Response)
    (reserve : Nat →StateT Platform ProbComp (core.result.Result Unit E))
    (length : RegistrationNativePlatformOrdinarySourceWorld.AeadLength setup.source.crypto)
    (view : RegistrationNativePlatformSourceSeal.KeyView)
    (converted : RegistrationNativePlatformOrdinarySourceNative.Conversion view)
    (failure : primitives.Error) (erased : commitment.CommitmentTranscript)
    {Metadata : Type} (owner : RawCtxWholeOwner.OwnerState Metadata)
    (plaintext : Slice U8) (sender : U64) (associated : Array U8 281#usize)
    (sameAD : owner.owner.associatedData=PqxdhRefinement.absBytes associated) :
    project owner <$> RegistrationNativePlatformExtractedSdkOrdinaryDriver.send setup codec reserve view failure erased
      owner.owner.kernel ⟨plaintext,.None,associated,owner.owner.expectedSender,sender,.Frame⟩ =
    simulateQ (RegistrationNativePlatformOrdinarySourceJournal.native setup codec reserve)
      (simulateQ RawCtxMixedOwner.sendAdapter
        ((RawCtxSourceSend.sendOwner sender (TranscriptAuthParts.absSlice plaintext)).run owner)) := by
  have source := congrArg (fun work=>RegistrationNativePlatformOrdinarySourceLoggedWorld.total owner <$> work)
    (RegistrationNativePlatformExtractedSdkOrdinaryDriver.send_native setup codec reserve length view converted failure erased
      owner plaintext sender associated sameAD)
  simpa only [project,Functor.map_map,Function.comp_def,
    RegistrationNativePlatformOrdinarySourceLoggedWorld.total,id_map'] using source

noncomputable def ownerNative (setup : Setup base KemSK) (codec : Codec Reader Response)
    (reserve : Nat →StateT Platform ProbComp (core.result.Result Unit E))
    {Metadata : Type} (owner : RawCtxWholeOwner.OwnerState Metadata) (sender : U64) (plaintext : Slice U8) :
    M Platform (Option RawCtxSourceSend.Encrypted ×RawCtxWholeOwner.OwnerState Metadata) :=
  simulateQ (RegistrationNativePlatformOrdinarySourceJournal.native setup codec reserve)
    (simulateQ RawCtxMixedOwner.sendAdapter
      ((RawCtxSourceSend.sendOwner sender (TranscriptAuthParts.absSlice plaintext)).run owner))

omit primitives [FrameDispatchFallback.Operations] in
theorem owner_noop (setup : Setup base KemSK) (codec : Codec Reader Response)
    (reserve : Nat →StateT Platform ProbComp (core.result.Result Unit E))
    {Metadata : Type} (owner : RawCtxWholeOwner.OwnerState Metadata) (sender : U64) (plaintext : Slice U8)
    (inactive : plaintext.val.isEmpty=true ∨owner.owner.kernel.refined.control.send_sequence=core.num.U64.MAX) :
    ownerNative setup codec reserve owner sender plaintext=pure (none,owner) := by
  have empty : (TranscriptAuthParts.absSlice plaintext).isEmpty=plaintext.val.isEmpty := by
    simp only [TranscriptAuthParts.absSlice,List.isEmpty_map]
  unfold ownerNative
  rcases inactive with stopped | exhausted
  · simp only [RawCtxSourceSend.sendOwner,StateT.run,empty,stopped,ite_true,simulateQ_pure]
  · unfold RawCtxSourceSend.sendOwner
    change simulateQ _ (simulateQ _ (if (TranscriptAuthParts.absSlice plaintext).isEmpty then pure (none,owner) else _)) = _
    split_ifs
    · simp only [simulateQ_pure]
    · dsimp only
      rw [RawCtxSourceSend.send_exhausted _ _ exhausted]
      simp only [simulateQ_pure,pure_bind]

variable [material : PublicWrapperPlatform.Material] [platform : PublicWrapperPlatform.Platform]
variable [PublicWrapperPlatform.Allocator] [ed : AdapterInitEdPrimitive.Operations]
variable [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations]
variable [AdapterPublicOrdinaryPlatform.LookupOperations]

noncomputable def sample (setup : Setup base KemSK) (codec : Codec Reader Response)
    (reserve : Nat →StateT Platform ProbComp (core.result.Result Unit E))
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitives.Error)
    (erased : commitment.CommitmentTranscript) (self : beaconcrypt_public_wrapper.beacon.Beacon)
    (control : pqxdh.BeaconEstablished) (binding : session.SessionBinding)
    (kernel : ratchet.concrete.ConcreteRatchetKernel) (bytes : Slice U8) :
    M Platform (RustM AdapterRecordStatefulSend.Result) :=
  match AdapterPublicOrdinaryEnvelope.prepareSend bytes control.server_binding.identity_key_id
    self.identity_key_kid binding.associated_data kernel with
  | .ok (some context)=>RegistrationNativePlatformExtractedSdkOrdinaryDriver.send setup codec reserve view failure erased kernel context
  | _=>pure (.ok (kernel,none))

omit [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations] in
theorem source (setup : Setup base KemSK) (codec : Codec Reader Response)
    (reserve : Nat →StateT Platform ProbComp (core.result.Result Unit E))
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitives.Error)
    (erased : commitment.CommitmentTranscript) (self : beaconcrypt_public_wrapper.beacon.Beacon)
    (control : pqxdh.BeaconEstablished) (binding : session.SessionBinding)
    (kernel : ratchet.concrete.ConcreteRatchetKernel)
    (stored : self.state=.Established control binding (AdapterPublicOrdinaryEnvelope.manager kernel)) (bytes : Slice U8) :
    AdapterPublicOrdinaryKernel.returned self control binding <$>
      sample setup codec reserve view failure erased self control binding kernel bytes =
    RegistrationNativePlatformExtractedSdkOrdinary.beaconSend setup codec reserve view failure erased self bytes := by
  rw [RegistrationNativePlatformExtractedSdkOrdinaryBeacon.send_source setup codec reserve view failure erased self control binding kernel stored bytes]
  unfold sample RegistrationNativePlatformExtractedSdkOrdinaryBeacon.send
  rw [AdapterPublicOrdinarySendGate.prepare]
  have restored : {self with state:=beaconcrypt_public_wrapper.beacon.BeaconState.Established control binding (AdapterPublicOrdinaryEnvelope.manager kernel)}=self := by
    rw [← stored]
  split_ifs <;> simp only [map_pure,AdapterPublicOrdinaryKernel.returned_exact]
  all_goals exact congrArg pure (congrArg (RustM.ok ∘Prod.mk none) restored)

def owner (control : pqxdh.BeaconEstablished) (binding : session.SessionBinding)
    (kernel : ratchet.concrete.ConcreteRatchetKernel) (rawBefore : Nat) : RawCtxWholeOwner.OwnerState Unit :=
  ⟨⟨kernel,control.server_binding.identity_key_id,PqxdhRefinement.absBytes binding.associated_data,()⟩,rawBefore⟩

omit [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations]
  [AdapterPublicOrdinaryPlatform.LookupOperations] platform [PublicWrapperPlatform.Allocator] in
theorem sample_native (setup : Setup base KemSK) (codec : Codec Reader Response)
    (reserve : Nat →StateT Platform ProbComp (core.result.Result Unit E))
    (length : RegistrationNativePlatformOrdinarySourceWorld.AeadLength setup.source.crypto)
    (view : RegistrationNativePlatformSourceSeal.KeyView)
    (converted : RegistrationNativePlatformOrdinarySourceNative.Conversion view)
    (failure : primitives.Error) (erased : commitment.CommitmentTranscript)
    (self : beaconcrypt_public_wrapper.beacon.Beacon) (control : pqxdh.BeaconEstablished)
    (binding : session.SessionBinding) (kernel : ratchet.concrete.ConcreteRatchetKernel) (bytes : Slice U8) (rawBefore : Nat) :
    project (owner control binding kernel rawBefore) <$>
      sample setup codec reserve view failure erased self control binding kernel bytes =
    if CborRecordWorldClient.nextFits bytes.val.length kernel.refined.control.send_sequence.val self.identity_key_kid.val then
      ownerNative setup codec reserve (owner control binding kernel rawBefore) self.identity_key_kid bytes
    else pure (none,owner control binding kernel rawBefore) := by
  unfold sample
  rw [AdapterPublicOrdinarySendGate.prepare]
  cases empty : bytes.val.isEmpty with
  | true=>
      simp only [ite_true,map_pure]
      cases fits : CborRecordWorldClient.nextFits bytes.val.length kernel.refined.control.send_sequence.val self.identity_key_kid.val
      · rfl
      · simp only [ite_true]
        exact (owner_noop setup codec reserve _ _ bytes (Or.inl empty)).symm
  | false=>
      simp only [Bool.false_eq_true,ite_false]
      by_cases live : kernel.refined.control.send_sequence.val<UScalar.max .U64
      · simp only [live,ite_true]
        cases fits : CborRecordWorldClient.nextFits bytes.val.length kernel.refined.control.send_sequence.val self.identity_key_kid.val
        · rfl
        · simp only [ite_true]
          exact native setup codec reserve length view converted failure erased _ bytes self.identity_key_kid binding.associated_data rfl
      · have exhausted : kernel.refined.control.send_sequence=core.num.U64.MAX := by
          apply UScalar.eq_of_val_eq
          have maximum : core.num.U64.MAX.val=UScalar.max .U64 := by
            simp [core.num.U64.MAX,U64.rMax,UScalar.max_def]
          rw [maximum]
          have bound := kernel.refined.control.send_sequence.hmax
          simp only [UScalar.max_def] at live ⊢
          omega
        simp only [live,ite_false,map_pure]
        cases fits : CborRecordWorldClient.nextFits bytes.val.length kernel.refined.control.send_sequence.val self.identity_key_kid.val
        · rfl
        · simp only [ite_true]
          exact (owner_noop setup codec reserve _ _ bytes (Or.inr exhausted)).symm

omit [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations]
  [AdapterPublicOrdinaryPlatform.LookupOperations] platform [PublicWrapperPlatform.Allocator] in
theorem sample_normal (setup : Setup base KemSK) (codec : Codec Reader Response)
    (reserve : Nat →StateT Platform ProbComp (core.result.Result Unit E))
    (length : RegistrationNativePlatformOrdinarySourceWorld.AeadLength setup.source.crypto)
    (view : RegistrationNativePlatformSourceSeal.KeyView)
    (converted : RegistrationNativePlatformOrdinarySourceNative.Conversion view)
    (failure : primitives.Error) (erased : commitment.CommitmentTranscript)
    (self : beaconcrypt_public_wrapper.beacon.Beacon) (control : pqxdh.BeaconEstablished)
    (binding : session.SessionBinding) (kernel : ratchet.concrete.ConcreteRatchetKernel) (bytes : Slice U8)
    (before after : RegistrationNativePlatformExtractedSdkOrdinaryDriver.State) (previous next : Platform)
    (reply : RustM AdapterRecordStatefulSend.Result)
    (supported : ((reply,after),next) ∈support
      (((sample setup codec reserve view failure erased self control binding kernel bytes).run before).run previous)) :
    ∃value,reply=.ok value := by
  unfold sample at supported
  rw [AdapterPublicOrdinarySendGate.prepare] at supported
  split_ifs at supported
  all_goals first
    | exact RegistrationNativePlatformExtractedSdkOrdinaryDriver.send_normal setup codec reserve length view converted failure erased
        (owner control binding kernel 0) bytes self.identity_key_kid binding.associated_data rfl before after previous next reply supported
    | simp only [StateT.run_pure,support_pure,Set.mem_singleton_iff] at supported
      exact ⟨(kernel,none),congrArg (fun result=>result.1.1) supported⟩

end BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinarySendCommon
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinarySendCommon.native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinarySendCommon.native

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinarySendCommon.source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinarySendCommon.source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinarySendCommon.owner_noop' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinarySendCommon.owner_noop

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinarySendCommon.sample_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinarySendCommon.sample_native

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinarySendCommon.sample_normal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinarySendCommon.sample_normal
