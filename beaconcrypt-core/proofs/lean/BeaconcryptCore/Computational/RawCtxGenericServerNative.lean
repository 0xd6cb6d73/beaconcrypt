import BeaconcryptCore.Computational.RawCtxGenericServer

/-!
The generic Server frontend realizes the original native mixed Server source program through complete receive/send call equations. These are operational equations in the same lawful monad and retain optional replies and every primitive effect. The native specialization and complete adaptive transport retain all routing, peer metadata, assigned IDs and attempted receives; they add no identity-injectivity, freshness or security premise.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RawCtxGenericServerNative
open RawCtxGenericRoleStorage RawCtxGenericServer

def nativePeer {Kernel PeerMetadata : Type} (interpret : Kernel → ConcreteRatchetKernel)
    (peer : Peer Kernel PeerMetadata) : RawCtxServerRouting.Peer PeerMetadata :=
  ⟨peer.identity, interpret peer.kernel, peer.metadata⟩

/-- Native AD uses exactly the same two original identity fields. -/
theorem associated_native {Kernel Metadata PeerMetadata : Type} (interpret : Kernel → ConcreteRatchetKernel)
    (state : ServerState Kernel Metadata PeerMetadata) (kid : Std.U64) :
    RawCtxServerRouting.peerAssociatedData (nativeServer interpret state).server kid =
      peerAssociatedData state.server kid := by
  cases found : state.server.peers kid <;>
    simp [RawCtxServerRouting.peerAssociatedData, peerAssociatedData, nativeServer, found]

/-- Native publication changes the same peer kernel while preserving the rest of the entire Server. -/
theorem put_native {Kernel Metadata PeerMetadata : Type} (interpret : Kernel → ConcreteRatchetKernel)
    (state : ServerState Kernel Metadata PeerMetadata) (kid : Std.U64) (peer : Peer Kernel PeerMetadata)
    (kernel : Kernel) (attempts : Nat) :
    nativeServer interpret (⟨putPeer state.server kid peer kernel, attempts⟩ : ServerState Kernel Metadata PeerMetadata) =
      ⟨RawCtxServerRouting.putPeer (nativeServer interpret state).server kid
        (nativePeer interpret peer) (interpret kernel), attempts⟩ := by
  simp only [nativeServer, putPeer, RawCtxServerRouting.putPeer]
  congr 1
  congr 1
  funext other
  by_cases same : other = kid
  · subst other
    simp only [Function.update_self, Option.map_some]
    rfl
  · simp only [Function.update_of_ne same]

/-- The original native raw Server executes the same selected receive and exact full-map publication. -/
theorem raw_native {Kernel Metadata PeerMetadata : Type} {m : Type → Type*} [Monad m] [LawfulMonad m]
    (interpret : Kernel → ConcreteRatchetKernel) (calls : RawCtxChainOwner.Calls Kernel m)
    (native : QueryImpl RawCtxMixedOwner.NativeSpec m)
    (receiveRealized : ∀ entry target context,
      simulateQ ((native ∘ₛ RawCtxMixedOwner.receiveAdapter) ∘ₛ RawCtxWholeOwner.adapter)
        (RawCtxOwnerOracle.receive (interpret entry) target context) =
        (fun result => (interpret result.1, result.2)) <$> calls.receive entry target context)
    (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (raw : Pqxdh.Bytes) (state : ServerState Kernel Metadata PeerMetadata) :
    simulateQ native (RawCtxServerMixed.rawServer route decode raw (nativeServer interpret state)) =
      Prod.map id (nativeServer interpret) <$> rawServer calls route decode raw state := by
  simp only [RawCtxServerMixed.rawServer, rawServer, associated_native]
  cases routed : route raw with
  | some kid =>
    cases adFound : peerAssociatedData state.server kid with
    | some ad =>
      cases found : state.server.peers kid with
      | some peer =>
        simp only [adFound, nativeServer, found, Option.map_some, bind_pure_comp, simulateQ_map,
          ← QueryImpl.simulateQ_compose]
        have mapped := RawCtxChainOwner.rawReceive_native interpret calls
          (native ∘ₛ RawCtxMixedOwner.receiveAdapter) receiveRealized decode raw
          (selectedOwner kid ad peer state.rawAttempts)
        change simulateQ (native ∘ₛ RawCtxMixedOwner.receiveAdapter)
          ((RawCtxWholeOwner.rawReceive decode raw).run
            ⟨RawCtxServerRouting.selectedOwner kid ad (nativePeer interpret peer), state.rawAttempts⟩) = _ at mapped
        simp only [nativePeer] at mapped
        rw [mapped, Functor.map_map, Functor.map_map]
        congr 1
        funext result
        simp only [Prod.map_apply, id_eq]
        exact congrArg (Prod.mk result.1) (put_native interpret state kid peer result.2.kernel result.2.rawAttempts).symm
      | none => simp [adFound, nativeServer, found, Prod.map_apply]
    | none => simp [adFound, nativeServer, Prod.map_apply]
  | none => simp [nativeServer, Prod.map_apply]

/-- The original native send retains routing order, every optional sealing result and the same advanced peer. -/
theorem send_native {Kernel Metadata PeerMetadata : Type} {m : Type → Type*} [Monad m] [LawfulMonad m]
    (interpret : Kernel → ConcreteRatchetKernel) (calls : RawCtxChainOwner.Calls Kernel m)
    (native : QueryImpl RawCtxMixedOwner.NativeSpec m)
    (sendRealized : ∀ entry context,
      simulateQ ((native ∘ₛ RawCtxMixedOwner.sendAdapter) ∘ₛ RawCtxSourceSend.adapter)
        (RawCtxSourceSend.send (interpret entry) context) =
        (fun result => (interpret result.1, result.2)) <$> calls.send entry context)
    (senderId : Metadata → Std.U64) (plaintext : Pqxdh.Bytes) (kid : Std.U64)
    (state : ServerState Kernel Metadata PeerMetadata) :
    simulateQ native (RawCtxServerMixed.sendServer senderId plaintext kid (nativeServer interpret state)) =
      Prod.map id (nativeServer interpret) <$> sendServer calls senderId plaintext kid state := by
  simp only [RawCtxServerMixed.sendServer, RawCtxServerSend.sendServer, sendServer, associated_native]
  cases adFound : peerAssociatedData state.server kid with
  | some ad =>
    cases found : state.server.peers kid with
    | some peer =>
      simp only [nativeServer, found, Option.map_some, bind_pure_comp, simulateQ_map,
        ← QueryImpl.simulateQ_compose]
      have mapped := RawCtxChainOwner.sendOwner_native interpret calls
        (native ∘ₛ RawCtxMixedOwner.sendAdapter) sendRealized
        (senderId state.server.metadata) plaintext (selectedOwner kid ad peer state.rawAttempts)
      change simulateQ (native ∘ₛ RawCtxMixedOwner.sendAdapter)
        ((RawCtxSourceSend.sendOwner (senderId state.server.metadata) plaintext).run
          ⟨RawCtxServerRouting.selectedOwner kid ad (nativePeer interpret peer), state.rawAttempts⟩) = _ at mapped
      simp only [nativePeer, RawCtxMixedOwner.sendAdapter] at mapped
      rw [mapped, Functor.map_map, Functor.map_map]
      congr 1
      funext result
      simp only [Prod.map_apply, id_eq]
      exact congrArg (Prod.mk result.1) (put_native interpret state kid peer result.2.kernel result.2.rawAttempts).symm
    | none => simp [nativeServer, found, Prod.map_apply]
  | none => simp [Prod.map_apply]

/-- One complete original native Server query realizes the generic source query with the same full state. -/
theorem server_native {Kernel Metadata PeerMetadata : Type} {m : Type → Type*} [Monad m] [LawfulMonad m]
    (interpret : Kernel → ConcreteRatchetKernel) (calls : RawCtxChainOwner.Calls Kernel m)
    (native : QueryImpl RawCtxMixedOwner.NativeSpec m)
    (receiveRealized : ∀ entry target context,
      simulateQ ((native ∘ₛ RawCtxMixedOwner.receiveAdapter) ∘ₛ RawCtxWholeOwner.adapter)
        (RawCtxOwnerOracle.receive (interpret entry) target context) =
        (fun result => (interpret result.1, result.2)) <$> calls.receive entry target context)
    (sendRealized : ∀ entry context,
      simulateQ ((native ∘ₛ RawCtxMixedOwner.sendAdapter) ∘ₛ RawCtxSourceSend.adapter)
        (RawCtxSourceSend.send (interpret entry) context) =
        (fun result => (interpret result.1, result.2)) <$> calls.send entry context)
    (senderId : Metadata → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (query : RawCtxServerMixed.SourceSpec.Domain) (state : ServerState Kernel Metadata PeerMetadata) :
    simulateQ native ((RawCtxServerMixed.serverImpl senderId route decode query).run (nativeServer interpret state)) =
      Prod.map id (nativeServer interpret) <$> (serverImpl calls senderId route decode query).run state := by
  cases query with
  | inl request => exact send_native interpret calls native sendRealized senderId request.1 request.2 state
  | inr raw => exact raw_native interpret calls native receiveRealized route decode raw state

/-- Arbitrary original adaptive Server execution retains every peer and all effects under the concrete native interpreter. -/
theorem schedule_native {Kernel Metadata PeerMetadata Result : Type} {m : Type → Type*} [Monad m] [LawfulMonad m]
    (interpret : Kernel → ConcreteRatchetKernel) (calls : RawCtxChainOwner.Calls Kernel m)
    (native : QueryImpl RawCtxMixedOwner.NativeSpec m)
    (receiveRealized : ∀ entry target context,
      simulateQ ((native ∘ₛ RawCtxMixedOwner.receiveAdapter) ∘ₛ RawCtxWholeOwner.adapter)
        (RawCtxOwnerOracle.receive (interpret entry) target context) =
        (fun result => (interpret result.1, result.2)) <$> calls.receive entry target context)
    (sendRealized : ∀ entry context,
      simulateQ ((native ∘ₛ RawCtxMixedOwner.sendAdapter) ∘ₛ RawCtxSourceSend.adapter)
        (RawCtxSourceSend.send (interpret entry) context) =
        (fun result => (interpret result.1, result.2)) <$> calls.send entry context)
    (senderId : Metadata → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp RawCtxServerMixed.SourceSpec Result) (state : ServerState Kernel Metadata PeerMetadata) :
    simulateQ native ((simulateQ (RawCtxServerMixed.serverImpl senderId route decode) client).run (nativeServer interpret state)) =
      Prod.map id (nativeServer interpret) <$> (simulateQ (serverImpl calls senderId route decode) client).run state := by
  rw [QueryImpl.simulateQ_mapStateTBase_run]
  exact (map_run_simulateQ_eq_of_query_map_eq (serverImpl calls senderId route decode)
    (native.mapStateTBase (RawCtxServerMixed.serverImpl senderId route decode)) (nativeServer interpret)
    (fun query state => (server_native interpret calls native receiveRealized sendRealized senderId route decode query state).symm)
    client state).symm

end BeaconcryptCore.Computational.RawCtxGenericServerNative

/-- info: 'BeaconcryptCore.Computational.RawCtxGenericServerNative.associated_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxGenericServerNative.associated_native

/-- info: 'BeaconcryptCore.Computational.RawCtxGenericServerNative.put_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxGenericServerNative.put_native

/-- info: 'BeaconcryptCore.Computational.RawCtxGenericServerNative.raw_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxGenericServerNative.raw_native

/-- info: 'BeaconcryptCore.Computational.RawCtxGenericServerNative.send_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxGenericServerNative.send_native

/-- info: 'BeaconcryptCore.Computational.RawCtxGenericServerNative.server_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxGenericServerNative.server_native

/-- info: 'BeaconcryptCore.Computational.RawCtxGenericServerNative.schedule_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxGenericServerNative.schedule_native
