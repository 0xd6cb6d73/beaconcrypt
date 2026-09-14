import BeaconcryptCore.Computational.RawCtxGenericFamilyLive
import BeaconcryptCore.Computational.RawCtxGenericServerNative
import BeaconcryptCore.Computational.RawCtxGenericNativeCalls

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RawCtxGenericFamilyNative
open RawCtxGenericRoleStorage RawCtxGenericRoleFamily

set_option backward.isDefEq.respectTransparency false in
/-- The full original role step is realized through an arbitrary backend, preserving every installed role and public effect. -/
theorem step {Kernel Metadata PeerMetadata Identity DhPair KemPair : Type}
    {serverCount beaconCount : Nat} {m : Type → Type*} [Monad m] [LawfulMonad m]
    (interpret : Kernel → ConcreteRatchetKernel) (calls : RawCtxChainOwner.Calls Kernel m)
    (backend : QueryImpl RawCtxServerServices.BackendSpec m)
    (receiveRealized : ∀ entry target context,
      simulateQ (((backend ∘ₛ RawCtxServerServices.nativeLift) ∘ₛ RawCtxMixedOwner.receiveAdapter) ∘ₛ RawCtxWholeOwner.adapter)
        (RawCtxOwnerOracle.receive (interpret entry) target context) =
        (fun result => (interpret result.1, result.2)) <$> calls.receive entry target context)
    (sendRealized : ∀ entry context,
      simulateQ (((backend ∘ₛ RawCtxServerServices.nativeLift) ∘ₛ RawCtxMixedOwner.sendAdapter) ∘ₛ RawCtxSourceSend.adapter)
        (RawCtxSourceSend.send (interpret entry) context) =
        (fun result => (interpret result.1, result.2)) <$> calls.send entry context)
    (senderId : Metadata → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (query : (RawCtxProtocolRoles.SourceSpec serverCount beaconCount).Domain)
    (state : Roles Kernel Metadata PeerMetadata Identity DhPair KemPair serverCount beaconCount) :
    simulateQ backend ((RawCtxProtocolRoles.protocolImpl serverCount beaconCount senderId route decode query).run
      (nativeRoles interpret state)) =
      Prod.map id (nativeRoles interpret) <$>
        (RawCtxGenericFamilyFrontend.impl calls (backend ∘ₛ RawCtxServerServices.publicLift) senderId route decode query).run state := by
  rcases query with ⟨index, request⟩ | (⟨index, request⟩ | request)
  all_goals simp only [RawCtxProtocolRoles.protocolImpl, RawCtxRoleFamily.familyImpl,
    RawCtxGenericFamilyFrontend.impl, StateT.run, nativeRoles, bind_pure_comp,
    simulateQ_map, ← QueryImpl.simulateQ_compose]
  all_goals simp only [Functor.map_map]
  case inl =>
    have mapped := congrArg (fun computation => (fun result =>
      (result.1, (Function.update (fun index => nativeServer interpret (state.1 index)) index result.2,
        fun index => nativeBeacon interpret (state.2 index)))) <$> computation)
      (RawCtxGenericServerNative.server_native interpret calls (backend ∘ₛ RawCtxServerServices.nativeLift)
        receiveRealized sendRealized senderId route decode request (state.1 index))
    convert mapped using 1 <;> try rfl
    simp only [Functor.map_map]
    congr 1
    funext result
    simp only [Prod.map_def, id_eq, nativeRoles]
    congr 1
    exact congrArg (fun updated => (updated, fun index => nativeBeacon interpret (state.2 index)))
      (Function.comp_update (nativeServer interpret) state.1 index result.2)
  case inr.inl =>
    have mapped := congrArg (fun computation => (fun result =>
      (result.1, (fun index => nativeServer interpret (state.1 index),
        Function.update (fun index => nativeBeacon interpret (state.2 index)) index result.2))) <$> computation)
      (RawCtxGenericBeacon.native_step interpret calls (backend ∘ₛ RawCtxServerServices.nativeLift)
        receiveRealized sendRealized decode request (state.2 index))
    convert mapped using 1 <;> try rfl
    simp only [Functor.map_map]
    congr 1
    funext result
    simp only [Prod.map_def, id_eq, nativeRoles]
    congr 1
    exact congrArg (fun updated => (fun index => nativeServer interpret (state.1 index), updated))
      (Function.comp_update (nativeBeacon interpret) state.2 index result.2)
  case inr.inr => rfl

set_option backward.isDefEq.respectTransparency false in
/-- The full native live step retains the actual source optional read, original history and arbitrary backend effects. -/
theorem live_step {Kernel Metadata PeerMetadata Identity DhPair KemPair : Type}
    {serverCount beaconCount : Nat} {m : Type → Type*} [Monad m] [LawfulMonad m]
    (interpret : Kernel → ConcreteRatchetKernel) (calls : RawCtxChainOwner.Calls Kernel m)
    (backend : QueryImpl RawCtxServerServices.BackendSpec m)
    (receiveRealized : ∀ entry target context,
      simulateQ (((backend ∘ₛ RawCtxServerServices.nativeLift) ∘ₛ RawCtxMixedOwner.receiveAdapter) ∘ₛ RawCtxWholeOwner.adapter)
        (RawCtxOwnerOracle.receive (interpret entry) target context) =
        (fun result => (interpret result.1, result.2)) <$> calls.receive entry target context)
    (sendRealized : ∀ entry context,
      simulateQ (((backend ∘ₛ RawCtxServerServices.nativeLift) ∘ₛ RawCtxMixedOwner.sendAdapter) ∘ₛ RawCtxSourceSend.adapter)
        (RawCtxSourceSend.send (interpret entry) context) =
        (fun result => (interpret result.1, result.2)) <$> calls.send entry context)
    (senderId : Metadata → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (query : (RawCtxProtocolReveals.SourceSpec serverCount beaconCount).Domain)
    (state : RawCtxGenericFamilyLive.State Kernel Metadata PeerMetadata Identity DhPair KemPair serverCount beaconCount) :
    simulateQ backend ((RawCtxProtocolReveals.protocolImpl serverCount beaconCount senderId route decode query).run
      (RawCtxGenericFamilyLive.nativeState interpret state)) =
      Prod.map id (RawCtxGenericFamilyLive.nativeState interpret) <$>
        (RawCtxGenericFamilyLive.impl calls (backend ∘ₛ RawCtxServerServices.publicLift)
          (RawCtxGenericFamilyRead.nativeReader interpret) senderId route decode query).run state := by
  cases query with
  | inl request =>
      have mapped := congrArg (fun computation => (fun result =>
        (result.1, (result.2, RawCtxProtocolReveals.tick state.2))) <$> computation)
        (step interpret calls backend receiveRealized sendRealized senderId route decode request state.1)
      simpa only [RawCtxProtocolReveals.protocolImpl, RawCtxGenericFamilyLive.impl,
        RawCtxGenericFamilyLive.nativeState, StateT.run, bind_pure_comp, simulateQ_map,
        Functor.map_map, Prod.map_def, Function.comp_def, id_eq] using mapped
  | inr request =>
      simp only [RawCtxProtocolReveals.protocolImpl, RawCtxGenericFamilyLive.impl,
        RawCtxGenericFamilyLive.nativeState, RawCtxGenericFamilyRead.nativeReader, StateT.run,
        pure_bind, simulateQ_pure, map_pure, RawCtxGenericFamilyRead.source_value, Prod.map_def, id_eq]

/-- Arbitrary adaptive original live schedules preserve every native role, actual optional reply, history entry and backend effect. -/
theorem live_schedule {Kernel Metadata PeerMetadata Identity DhPair KemPair Result : Type}
    {serverCount beaconCount : Nat} {m : Type → Type*} [Monad m] [LawfulMonad m]
    (interpret : Kernel → ConcreteRatchetKernel) (calls : RawCtxChainOwner.Calls Kernel m)
    (backend : QueryImpl RawCtxServerServices.BackendSpec m)
    (receiveRealized : ∀ entry target context,
      simulateQ (((backend ∘ₛ RawCtxServerServices.nativeLift) ∘ₛ RawCtxMixedOwner.receiveAdapter) ∘ₛ RawCtxWholeOwner.adapter)
        (RawCtxOwnerOracle.receive (interpret entry) target context) =
        (fun result => (interpret result.1, result.2)) <$> calls.receive entry target context)
    (sendRealized : ∀ entry context,
      simulateQ (((backend ∘ₛ RawCtxServerServices.nativeLift) ∘ₛ RawCtxMixedOwner.sendAdapter) ∘ₛ RawCtxSourceSend.adapter)
        (RawCtxSourceSend.send (interpret entry) context) =
        (fun result => (interpret result.1, result.2)) <$> calls.send entry context)
    (senderId : Metadata → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp (RawCtxProtocolReveals.SourceSpec serverCount beaconCount) Result)
    (state : RawCtxGenericFamilyLive.State Kernel Metadata PeerMetadata Identity DhPair KemPair serverCount beaconCount) :
    simulateQ backend ((simulateQ (RawCtxProtocolReveals.protocolImpl serverCount beaconCount senderId route decode) client).run
      (RawCtxGenericFamilyLive.nativeState interpret state)) =
      Prod.map id (RawCtxGenericFamilyLive.nativeState interpret) <$>
        (simulateQ (RawCtxGenericFamilyLive.impl calls (backend ∘ₛ RawCtxServerServices.publicLift)
          (RawCtxGenericFamilyRead.nativeReader interpret) senderId route decode) client).run state := by
  rw [QueryImpl.simulateQ_mapStateTBase_run]
  exact (map_run_simulateQ_eq_of_query_map_eq
    (RawCtxGenericFamilyLive.impl calls (backend ∘ₛ RawCtxServerServices.publicLift)
      (RawCtxGenericFamilyRead.nativeReader interpret) senderId route decode)
    (backend.mapStateTBase (RawCtxProtocolReveals.protocolImpl serverCount beaconCount senderId route decode))
    (RawCtxGenericFamilyLive.nativeState interpret)
    (fun query state => (live_step interpret calls backend receiveRealized sendRealized senderId route decode query state).symm)
    client state).symm

/-- The complete original live source has a concrete native-kernel representation under any mutable backend, without a supplied realization premise. -/
theorem actual {Metadata PeerMetadata Identity DhPair KemPair Result : Type}
    {serverCount beaconCount : Nat} {m : Type → Type*} [Monad m] [LawfulMonad m]
    (backend : QueryImpl RawCtxServerServices.BackendSpec m)
    (senderId : Metadata → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp (RawCtxProtocolReveals.SourceSpec serverCount beaconCount) Result)
    (state : RawCtxProtocolReveals.State Metadata PeerMetadata Identity DhPair KemPair serverCount beaconCount) :
    simulateQ backend ((simulateQ (RawCtxProtocolReveals.protocolImpl serverCount beaconCount senderId route decode) client).run state) =
      Prod.map id (RawCtxGenericFamilyLive.nativeState ConcreteRatchetKernel.mk) <$>
        (simulateQ (RawCtxGenericFamilyLive.impl
          (RawCtxGenericNativeCalls.calls (backend ∘ₛ RawCtxServerServices.nativeLift))
          (backend ∘ₛ RawCtxServerServices.publicLift) (RawCtxGenericFamilyRead.nativeReader ConcreteRatchetKernel.mk)
          senderId route decode) client).run (fromRoles ConcreteRatchetKernel.refined state.1, state.2) := by
  have represented : RawCtxGenericFamilyLive.nativeState ConcreteRatchetKernel.mk
      (fromRoles ConcreteRatchetKernel.refined state.1, state.2) = state := by
    apply Prod.ext
    · exact roundtrip ConcreteRatchetKernel.refined ConcreteRatchetKernel.mk (fun kernel => by cases kernel; rfl) state.1
    · rfl
  simpa only [represented] using live_schedule ConcreteRatchetKernel.mk
    (RawCtxGenericNativeCalls.calls (backend ∘ₛ RawCtxServerServices.nativeLift)) backend
    (RawCtxGenericNativeCalls.receive_realized (backend ∘ₛ RawCtxServerServices.nativeLift))
    (RawCtxGenericNativeCalls.send_realized (backend ∘ₛ RawCtxServerServices.nativeLift))
    senderId route decode client (fromRoles ConcreteRatchetKernel.refined state.1, state.2)

end BeaconcryptCore.Computational.RawCtxGenericFamilyNative

/-- info: 'BeaconcryptCore.Computational.RawCtxGenericFamilyNative.step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxGenericFamilyNative.step

/-- info: 'BeaconcryptCore.Computational.RawCtxGenericFamilyNative.live_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxGenericFamilyNative.live_step

/-- info: 'BeaconcryptCore.Computational.RawCtxGenericFamilyNative.live_schedule' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxGenericFamilyNative.live_schedule

/-- info: 'BeaconcryptCore.Computational.RawCtxGenericFamilyNative.actual' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxGenericFamilyNative.actual

