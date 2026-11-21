-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRecordFactsOriginAcceptedFlag
import BeaconcryptCore.Computational.PqxdhRecordFactsOriginDispatch

/-! Literal owner and physical role receive commands retain their selected replay marker. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhRecordFactsOriginMarkerOwner
open CtxRomAuth AdaptiveCtxReceive
open PqxdhRecordLiftIdeal (CtxPrivate KeyMode handleSlot)
open PqxdhRecordLiftWorldCompiler (Label StoredKernel Owner)
open PqxdhRecordFactsOriginHandles
open PqxdhDeploymentInterface (Handle)
variable {n : Nat} {ι KemSK Reader Response : Type} {baseSpec : OracleSpec ι}

/-- The source interpreter with only the selected replay flag added. -/
noncomputable abbrev service (target : Label n) (modes : Label n → KeyMode)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) :=
  PqxdhRecordFactsOriginMuteAdaptive.marked target (RawCtxUniversalDecoder.decoder codec.frameRead)
    (PqxdhRecordFactsPrivateCacheWorld.erased modes replace setup codec)

/-- Successful receiving through the actual looked-up hidden owner raises the precise selected marker, keeping the actual optional plaintext and complete poststate. -/
theorem ownerReceive_flag (target : Label n) (modes : Label n → KeyMode)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (control : PqxdhRecordLiftProtocol.Control n) (safe : PqxdhRecordLiftProtocolHistory.Safe control)
    (handle : Handle) (owner : Owner n) (stored : handleKernel control handle = some owner.kernel)
    (slot : handleSlot control handle = some target.slot) (direction : target.direction = !handleDirection handle)
    (raw : Pqxdh.Bytes) (before : CtxPrivate n × Bool)
    (result : (core.option.Option RawCtxWholeOwner.Decrypted × Owner n) × (CtxPrivate n × Bool))
    (supported : result ∈ support ((simulateQ (service target modes replace setup codec)
      (PqxdhRecordLiftProtocol.ownerReceive codec.frameRead raw owner)).run before))
    (opened : RawCtxWholeOwner.Decrypted) (returned : result.1.1 = .Some opened)
    (position : target.position + 1 = opened.sequence.val) : result.2.2 = true := by
  cases storedKind : owner.kernel with
  | known kernel =>
    have absent := PqxdhRecordFactsOriginAccepted.known_no_slot control handle
      (PqxdhRecordFactsOriginPublished.known_of_handleKernel control handle kernel (by simpa only [storedKind] using stored))
    simp only [absent, reduceCtorEq] at slot
  | hidden actualSlot entry =>
    simp only [PqxdhRecordLiftProtocol.ownerReceive] at supported
    repeat' split at supported
    case h_2.isTrue =>
      simp only [storedKind, bind_pure_comp, simulateQ_map, StateT.run_map, support_map] at supported
      obtain ⟨inner, reached, rfl⟩ := supported
      apply PqxdhRecordFactsOriginAcceptedFlag.kernel_accepted_flag target modes replace setup codec (handleRole handle)
        actualSlot entry (handleKernel_oriented control safe handle _ (by simpa only [storedKind] using stored))
        _ _ _ _ before inner reached opened returned position
      · exact Option.some.inj (slot.symm.trans (handleKernel_slot control handle actualSlot entry (by simpa only [storedKind] using stored)))
      · simpa only [handleRole_direction] using direction
    all_goals simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
    all_goals simp only [supported, reduceCtorEq] at returned

/-- The actual owner command's following publication preserves the marker established by its successful receive. -/
theorem ownerRun_flag (target : Label n) (modes : Label n → KeyMode)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (control : PqxdhRecordLiftProtocol.Control n) (safe : PqxdhRecordLiftProtocolHistory.Safe control)
    (handle : Handle) (owner : Owner n) (stored : handleKernel control handle = some owner.kernel)
    (slot : handleSlot control handle = some target.slot) (direction : target.direction = !handleDirection handle)
    (tag : PqxdhDeploymentInterface.FrameTag) (sender : Std.U64)
    (raw : Pqxdh.Bytes) (before : CtxPrivate n × Bool)
    (result : (core.option.Option RawCtxWholeOwner.Decrypted × Owner n) × (CtxPrivate n × Bool))
    (supported : result ∈ support ((simulateQ (service target modes replace setup codec)
      (PqxdhRecordLiftProtocol.ownerRun tag sender codec.frameRead (.inr raw) owner)).run before))
    (opened : RawCtxWholeOwner.Decrypted) (returned : result.1.1 = .Some opened)
    (position : target.position + 1 = opened.sequence.val) : result.2.2 = true := by
  simp only [PqxdhRecordLiftProtocol.ownerRun, PqxdhRecordLiftProtocol.ownerStep,
    simulateQ_bind, simulateQ_spec_query, simulateQ_pure, StateT.run_bind, StateT.run_pure,
    mem_support_bind_iff] at supported
  obtain ⟨received, receiveSupported, published, publishSupported, finished⟩ := supported
  obtain rfl := (mem_support_pure_iff _ _).mp finished
  exact PqxdhRecordFactsOriginMuteAdaptive.marked_sticky target (RawCtxUniversalDecoder.decoder codec.frameRead)
    (PqxdhRecordFactsPrivateCacheWorld.erased modes replace setup codec) (.publish tag) received.2
    (ownerReceive_flag target modes replace setup codec control safe handle owner stored slot direction raw before received receiveSupported opened returned position)
    published publishSupported

/-- A successful Server receive through the actual routed peer raises the target marker. -/
theorem serverReceive_flag (target : Label n) (modes : Label n → KeyMode)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (control : PqxdhRecordLiftProtocol.Control n) (safe : PqxdhRecordLiftProtocolHistory.Safe control)
    (raw : Pqxdh.Bytes) (keyId : Std.U64) (routed : route raw = some keyId)
    (slot : handleSlot control (.peer keyId) = some target.slot)
    (direction : target.direction = !handleDirection (.peer keyId))
    (before : CtxPrivate n × Bool)
    (result : (core.option.Option RawCtxWholeOwner.Decrypted × PqxdhRecordLiftProtocol.Control n) × (CtxPrivate n × Bool))
    (supported : result ∈ support ((simulateQ (service target modes replace setup codec)
      (PqxdhRecordLiftProtocol.serverStep codec.frameRead route (.inr raw) control)).run before))
    (opened : RawCtxWholeOwner.Decrypted) (returned : result.1.1 = .Some opened)
    (position : target.position + 1 = opened.sequence.val) : result.2.2 = true := by
  cases existing : control.server with
  | none =>
    simp only [PqxdhRecordLiftProtocol.serverStep, existing, simulateQ_pure,
      StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
    simp only [supported, reduceCtorEq] at returned
  | some server =>
    cases found : server.peers keyId with
    | none =>
      simp only [PqxdhRecordLiftProtocol.serverStep, existing, routed, found, simulateQ_pure,
        StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
      simp only [supported, reduceCtorEq] at returned
    | some peer =>
      simp only [PqxdhRecordLiftProtocol.serverStep, existing, routed, found, bind_pure_comp,
        simulateQ_map, StateT.run_map, support_map] at supported
      obtain ⟨inner, reached, rfl⟩ := supported
      apply ownerRun_flag target modes replace setup codec control safe (.peer keyId)
        (PqxdhRecordLiftWorldCompiler.serverOwner server keyId peer) _ slot direction _ server.sender raw
        before inner reached opened returned position
      simp only [handleKernel, existing, Option.bind_some, found, Option.map_some,
        PqxdhRecordLiftWorldCompiler.serverOwner]

/-- A successful Beacon receive through its actual established owner raises the target marker. -/
theorem beaconReceive_flag (target : Label n) (modes : Label n → KeyMode)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (control : PqxdhRecordLiftProtocol.Control n) (safe : PqxdhRecordLiftProtocolHistory.Safe control)
    (index : Nat) (raw : Pqxdh.Bytes)
    (slot : handleSlot control (.owner index) = some target.slot)
    (direction : target.direction = !handleDirection (.owner index))
    (before : CtxPrivate n × Bool)
    (result : (core.option.Option RawCtxWholeOwner.Decrypted × PqxdhRecordLiftProtocol.Control n) × (CtxPrivate n × Bool))
    (supported : result ∈ support ((simulateQ (service target modes replace setup codec)
      (PqxdhRecordLiftProtocol.beaconStep codec.frameRead index (.inr raw) control)).run before))
    (opened : RawCtxWholeOwner.Decrypted) (returned : result.1.1 = .Some opened)
    (position : target.position + 1 = opened.sequence.val) : result.2.2 = true := by
  rcases found : control.owners[index]? with _ | (phase | ⟨shell, kernel⟩)
  · simp only [PqxdhRecordLiftProtocol.beaconStep, found, PqxdhDeploymentNative.absent,
      simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
    simp only [supported, reduceCtorEq] at returned
  · simp only [PqxdhRecordLiftProtocol.beaconStep, found, simulateQ_pure,
      StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
    simp only [supported, reduceCtorEq] at returned
  · simp only [PqxdhRecordLiftProtocol.beaconStep, found, bind_pure_comp,
      simulateQ_map, StateT.run_map, support_map] at supported
    obtain ⟨inner, reached, rfl⟩ := supported
    apply ownerRun_flag target modes replace setup codec control safe (.owner index)
      (PqxdhRecordLiftWorldCompiler.beaconOwner shell kernel (control.ownerRaw index))
      _ slot direction _ shell.identityKeyId raw before inner reached opened returned position
    simp only [handleKernel, found, Option.bind_some, PqxdhRecordLiftWorldCompiler.beaconOwner]

end BeaconcryptCore.Computational.PqxdhRecordFactsOriginMarkerOwner

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginMarkerOwner.ownerReceive_flag' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginMarkerOwner.ownerReceive_flag

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginMarkerOwner.ownerRun_flag' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginMarkerOwner.ownerRun_flag

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginMarkerOwner.serverReceive_flag' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginMarkerOwner.serverReceive_flag

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginMarkerOwner.beaconReceive_flag' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginMarkerOwner.beaconReceive_flag
