import BeaconcryptCore.Computational.RawCtxSourceChainHandles

/-!
The complete native established-owner source adapter factors through private kernel calls while retaining its original public send/raw query and optional reply types. Empty sends, raw empty/decode/pin/shape rejection, attempted receive counts, whole-kernel publication, immutable owner metadata and all callback poststate are preserved. The generic law takes explicit functional call equations; the concrete handle specialization discharges both with the unchanged fixed-source backend.

The arbitrary adaptive equality retains one complete owner and one shared primitive state before any projection. Its underlying query allowance and actual64*(qSend+qRaw) uniform bound follow from literal OracleComp equality, with every rejected attempt retained. Local source checks, label interpretation/recomputation, copying and deterministic primitive work remain separate costs.

The initial kernel representation and root interpretation are supplied private protocol context. This module does not derive native registration installation, independent chains, selected-input secrecy, public-evaluation freshness, reveal/ancestor restrictions, snapshot/restore policy, or a global security conclusion. Dynamic interpretation changes still need their own full-state realization.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.refined ratchet.concrete
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RawCtxChainOwner

structure State (Kernel Metadata : Type) where
  kernel : Kernel
  expectedSender : Std.U64
  associatedData : Pqxdh.Bytes
  metadata : Metadata
  rawAttempts : Nat

def nativeState {Kernel Metadata : Type} (interpret : Kernel → ConcreteRatchetKernel)
    (state : State Kernel Metadata) : RawCtxWholeOwner.OwnerState Metadata :=
  ⟨⟨interpret state.kernel, state.expectedSender, state.associatedData, state.metadata⟩, state.rawAttempts⟩

structure Calls (Kernel : Type) (m : Type → Type*) where
  receive : Kernel → Std.U64 → RawCtxWholeOwner.OpenContext → m (Kernel × core.option.Option RawCtxWholeOwner.Decrypted)
  send : Kernel → RawCtxSourceSend.SealContext → m (Kernel × Option RawCtxSourceSend.Encrypted)

def publish {Kernel Metadata : Type} (state : State Kernel Metadata)
    (result : Kernel × core.option.Option RawCtxWholeOwner.Decrypted) :
    core.option.Option RawCtxWholeOwner.Decrypted × State Kernel Metadata :=
  (result.2, {state with kernel := result.1, rawAttempts := state.rawAttempts + 1})

noncomputable def rawReceive {Kernel Metadata : Type} {m : Type → Type*} [Monad m]
    (calls : Calls Kernel m) (decode : RawCtxReceive.FrameDecoder) (raw : Pqxdh.Bytes) :
    StateT (State Kernel Metadata) m (core.option.Option RawCtxWholeOwner.Decrypted) := fun state =>
  if raw.isEmpty then pure (publish state (state.kernel, .None)) else
  match decode raw with
  | none => pure (publish state (state.kernel, .None))
  | some frame =>
    if RawCtxReceive.ValidFrame state.expectedSender state.associatedData frame then do
      let result ← calls.receive state.kernel frame.sequence ⟨raw, frame, state.associatedData⟩
      pure (publish state result)
    else pure (publish state (state.kernel, .None))

/-- Every raw rejection and publication branch retains the exact owner fields and reached primitive state. -/
theorem rawReceive_native {Kernel Metadata : Type} {m : Type → Type*} [Monad m] [LawfulMonad m]
    (interpret : Kernel → ConcreteRatchetKernel) (calls : Calls Kernel m)
    (native : QueryImpl RawCtxWholeOwner.PrimitiveSpec m)
    (realized : ∀ entry target context,
      simulateQ (native ∘ₛ RawCtxWholeOwner.adapter) (RawCtxOwnerOracle.receive (interpret entry) target context) =
        (fun result => (interpret result.1, result.2)) <$> calls.receive entry target context)
    (decode : RawCtxReceive.FrameDecoder) (raw : Pqxdh.Bytes) (state : State Kernel Metadata) :
    simulateQ native ((RawCtxWholeOwner.rawReceive decode raw).run (nativeState interpret state)) =
      Prod.map id (nativeState interpret) <$> (rawReceive calls decode raw).run state := by
  simp only [RawCtxWholeOwner.rawReceive, rawReceive, nativeState, StateT.run]
  by_cases empty : raw.isEmpty = true
  · simp only [empty, if_true, simulateQ_pure, map_pure, RawCtxWholeOwner.publish, publish, Prod.map_def, id_eq, nativeState]
  · simp only [empty, Bool.false_eq_true, if_false]
    cases decoded : decode raw with
    | some frame =>
      by_cases valid : RawCtxReceive.ValidFrame state.expectedSender state.associatedData frame
      · simp only [valid, if_true, bind_pure_comp, simulateQ_map, ← QueryImpl.simulateQ_compose]
        rw [realized, Functor.map_map, Functor.map_map]
        rfl
      · simp only [valid, if_false, simulateQ_pure, map_pure, RawCtxWholeOwner.publish, publish, Prod.map_def, id_eq, nativeState]
    | none =>
      simp only [simulateQ_pure, map_pure, RawCtxWholeOwner.publish, publish, Prod.map_def, id_eq, nativeState]

noncomputable def sendOwner {Kernel Metadata : Type} {m : Type → Type*} [Monad m]
    (calls : Calls Kernel m) (senderId : Std.U64) (plaintext : Pqxdh.Bytes) :
    StateT (State Kernel Metadata) m (Option RawCtxSourceSend.Encrypted) := fun state =>
  if plaintext.isEmpty then pure (none, state) else do
    let result ← calls.send state.kernel ⟨plaintext, state.expectedSender, senderId, state.associatedData⟩
    pure (result.2, {state with kernel := result.1})

/-- Empty sends reject before callbacks; active optional failures retain the actual advanced owner. -/
theorem sendOwner_native {Kernel Metadata : Type} {m : Type → Type*} [Monad m] [LawfulMonad m]
    (interpret : Kernel → ConcreteRatchetKernel) (calls : Calls Kernel m)
    (native : QueryImpl RawCtxSourceSend.PrimitiveSpec m)
    (realized : ∀ entry context,
      simulateQ (native ∘ₛ RawCtxSourceSend.adapter) (RawCtxSourceSend.send (interpret entry) context) =
        (fun result => (interpret result.1, result.2)) <$> calls.send entry context)
    (senderId : Std.U64) (plaintext : Pqxdh.Bytes) (state : State Kernel Metadata) :
    simulateQ native ((RawCtxSourceSend.sendOwner senderId plaintext).run (nativeState interpret state)) =
      Prod.map id (nativeState interpret) <$> (sendOwner calls senderId plaintext).run state := by
  simp only [RawCtxSourceSend.sendOwner, sendOwner, nativeState, StateT.run]
  by_cases empty : plaintext.isEmpty = true
  · simp only [empty, if_true, simulateQ_pure, map_pure, Prod.map_def, id_eq, nativeState]
  · simp only [empty, Bool.false_eq_true, if_false, bind_pure_comp, simulateQ_map, ← QueryImpl.simulateQ_compose]
    rw [realized, Functor.map_map, Functor.map_map]
    rfl

noncomputable def ownerImpl {Kernel Metadata : Type} {m : Type → Type*} [Monad m]
    (calls : Calls Kernel m) (senderId : Std.U64) (decode : RawCtxReceive.FrameDecoder) :
    QueryImpl RawCtxMixedOwner.SourceSpec (StateT (State Kernel Metadata) m)
  | .inl plaintext => sendOwner calls senderId plaintext
  | .inr raw => rawReceive calls decode raw

/-- The whole mixed owner invokes the same source callbacks while exposing only original API replies. -/
theorem owner_native {Kernel Metadata : Type} {m : Type → Type*} [Monad m] [LawfulMonad m]
    (interpret : Kernel → ConcreteRatchetKernel) (calls : Calls Kernel m)
    (native : QueryImpl RawCtxMixedOwner.NativeSpec m)
    (receiveRealized : ∀ entry target context,
      simulateQ ((native ∘ₛ RawCtxMixedOwner.receiveAdapter) ∘ₛ RawCtxWholeOwner.adapter)
        (RawCtxOwnerOracle.receive (interpret entry) target context) =
        (fun result => (interpret result.1, result.2)) <$> calls.receive entry target context)
    (sendRealized : ∀ entry context,
      simulateQ ((native ∘ₛ RawCtxMixedOwner.sendAdapter) ∘ₛ RawCtxSourceSend.adapter)
        (RawCtxSourceSend.send (interpret entry) context) =
        (fun result => (interpret result.1, result.2)) <$> calls.send entry context)
    (senderId : Std.U64) (decode : RawCtxReceive.FrameDecoder)
    (query : RawCtxMixedOwner.SourceSpec.Domain) (state : State Kernel Metadata) :
    simulateQ native ((RawCtxMixedOwner.ownerImpl senderId decode query).run (nativeState interpret state)) =
      Prod.map id (nativeState interpret) <$> (ownerImpl calls senderId decode query).run state := by
  cases query with
  | inl plaintext =>
    simp only [RawCtxMixedOwner.ownerImpl, ownerImpl, StateT.run, ← QueryImpl.simulateQ_compose]
    exact sendOwner_native interpret calls (native ∘ₛ RawCtxMixedOwner.sendAdapter) sendRealized senderId plaintext state
  | inr raw =>
    simp only [RawCtxMixedOwner.ownerImpl, ownerImpl, StateT.run, ← QueryImpl.simulateQ_compose]
    exact rawReceive_native interpret calls (native ∘ₛ RawCtxMixedOwner.receiveAdapter) receiveRealized decode raw state

noncomputable def sourceImpl {Kernel Metadata PrimitiveState ι : Type} {base : OracleSpec ι}
    (calls : Calls Kernel (StateT PrimitiveState (OracleComp base)))
    (senderId : Std.U64) (decode : RawCtxReceive.FrameDecoder) :
    QueryImpl RawCtxMixedOwner.SourceSpec (StateT (State Kernel Metadata × PrimitiveState) (OracleComp base)) :=
  (ownerImpl calls senderId decode).flattenStateT

/-- Flattening keeps the actual full owner and entire primitive poststate on every original source step. -/
theorem source_step {Kernel Metadata PrimitiveState ι : Type} {base : OracleSpec ι}
    (interpret : Kernel → ConcreteRatchetKernel) (calls : Calls Kernel (StateT PrimitiveState (OracleComp base)))
    (native : QueryImpl RawCtxMixedOwner.NativeSpec (StateT PrimitiveState (OracleComp base)))
    (receiveRealized : ∀ entry target context,
      simulateQ ((native ∘ₛ RawCtxMixedOwner.receiveAdapter) ∘ₛ RawCtxWholeOwner.adapter)
        (RawCtxOwnerOracle.receive (interpret entry) target context) =
        (fun result => (interpret result.1, result.2)) <$> calls.receive entry target context)
    (sendRealized : ∀ entry context,
      simulateQ ((native ∘ₛ RawCtxMixedOwner.sendAdapter) ∘ₛ RawCtxSourceSend.adapter)
        (RawCtxSourceSend.send (interpret entry) context) =
        (fun result => (interpret result.1, result.2)) <$> calls.send entry context)
    (senderId : Std.U64) (decode : RawCtxReceive.FrameDecoder)
    (query : RawCtxMixedOwner.SourceSpec.Domain) (state : State Kernel Metadata × PrimitiveState) :
    (RawCtxMixedOwner.sourceImpl native senderId decode query).run (nativeState interpret state.1, state.2) =
      Prod.map id (Prod.map (nativeState interpret) id) <$>
        (sourceImpl calls senderId decode query).run state := by
  have hrun := congrArg (fun work : StateT PrimitiveState (OracleComp base)
      (RawCtxMixedOwner.SourceSpec.Range query × RawCtxWholeOwner.OwnerState Metadata) => work.run state.2)
    (owner_native interpret calls native receiveRealized sendRealized senderId decode query state.1)
  have reassoc := congrArg (fun work : OracleComp base
      ((RawCtxMixedOwner.SourceSpec.Range query × RawCtxWholeOwner.OwnerState Metadata) × PrimitiveState) =>
    (fun result => (result.1.1, (result.1.2, result.2))) <$> work) hrun
  simp only [StateT.run_map, Functor.map_map] at reassoc
  rw [← RawCtxMixedOwner.owner_interpretation]
  simpa only [sourceImpl, QueryImpl.flattenStateT, QueryImpl.mapStateTBase, StateT.run, StateT.mk,
    Functor.map_map, Prod.map_def, id_eq] using reassoc

/-- Every adaptive source continuation keeps the complete owner, reply and primitive state. -/
theorem source_schedule {Kernel Metadata PrimitiveState Result ι : Type} {base : OracleSpec ι}
    (interpret : Kernel → ConcreteRatchetKernel) (calls : Calls Kernel (StateT PrimitiveState (OracleComp base)))
    (native : QueryImpl RawCtxMixedOwner.NativeSpec (StateT PrimitiveState (OracleComp base)))
    (receiveRealized : ∀ entry target context,
      simulateQ ((native ∘ₛ RawCtxMixedOwner.receiveAdapter) ∘ₛ RawCtxWholeOwner.adapter)
        (RawCtxOwnerOracle.receive (interpret entry) target context) =
        (fun result => (interpret result.1, result.2)) <$> calls.receive entry target context)
    (sendRealized : ∀ entry context,
      simulateQ ((native ∘ₛ RawCtxMixedOwner.sendAdapter) ∘ₛ RawCtxSourceSend.adapter)
        (RawCtxSourceSend.send (interpret entry) context) =
        (fun result => (interpret result.1, result.2)) <$> calls.send entry context)
    (senderId : Std.U64) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp RawCtxMixedOwner.SourceSpec Result) (state : State Kernel Metadata × PrimitiveState) :
    (simulateQ (RawCtxMixedOwner.sourceImpl native senderId decode) client).run (nativeState interpret state.1, state.2) =
      Prod.map id (Prod.map (nativeState interpret) id) <$>
        (simulateQ (sourceImpl calls senderId decode) client).run state := by
  exact (map_run_simulateQ_eq_of_query_map_eq
    (sourceImpl calls senderId decode) (RawCtxMixedOwner.sourceImpl native senderId decode)
    (Prod.map (nativeState interpret) id)
    (fun query state => (source_step interpret calls native receiveRealized sendRealized senderId decode query state).symm)
    client state).symm

/-- Concrete private calls execute the actual source effects while retaining only derivation handles in the kernel. -/
noncomputable def handleCalls {Atom Auxiliary : Type}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (roots : Atom → RatchetChain) :
    Calls (RawCtxSourceChainHandles.HandleKernel Atom) (StateT (RawCtxSharedPrimitive.SharedState Auxiliary) ProbComp) :=
  { receive := fun entry target context =>
      simulateQ (RawCtxSourceChainHandles.receiveLabels source writer roots)
        (RawCtxChainReceive.execute entry target context)
    send := fun entry context =>
      simulateQ (RawCtxSourceChainHandles.sendLabels source writer roots)
        (RawCtxChainSend.execute entry context) }

/-- The actual shared fixed-source game supplies every realization equation internally for the whole adaptive owner. -/
theorem handles_source {Atom Auxiliary Metadata Result : Type}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (roots : Atom → RatchetChain) (senderId : Std.U64) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp RawCtxMixedOwner.SourceSpec Result)
    (state : State (RawCtxSourceChainHandles.HandleKernel Atom) Metadata × RawCtxSharedPrimitive.SharedState Auxiliary) :
    (simulateQ (RawCtxMixedOwner.sourceImpl (RawCtxSourceMaterialLabels.nativeImpl source writer)
      senderId decode) client).run
        (nativeState (RawCtxSourceChainHandles.nativeKernel source roots) state.1, state.2) =
      Prod.map id (Prod.map (nativeState (RawCtxSourceChainHandles.nativeKernel source roots)) id) <$>
        (simulateQ (sourceImpl (handleCalls source writer roots) senderId decode) client).run state :=
  source_schedule (RawCtxSourceChainHandles.nativeKernel source roots) (handleCalls source writer roots)
    (RawCtxSourceMaterialLabels.nativeImpl source writer)
    (RawCtxSourceChainHandles.receive_source source writer roots)
    (RawCtxSourceChainHandles.send_source source writer roots) senderId decode client state

/-- Exact whole-source equality preserves every selective underlying query allowance. -/
theorem handles_query_bounds {Atom Auxiliary Metadata Result : Type}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (roots : Atom → RatchetChain) (senderId : Std.U64) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp RawCtxMixedOwner.SourceSpec Result)
    (state : State (RawCtxSourceChainHandles.HandleKernel Atom) Metadata × RawCtxSharedPrimitive.SharedState Auxiliary)
    (predicate : unifSpec.Domain → Prop) [DecidablePred predicate] (budget : Nat) :
    ((simulateQ (RawCtxMixedOwner.sourceImpl (RawCtxSourceMaterialLabels.nativeImpl source writer)
      senderId decode) client).run
        (nativeState (RawCtxSourceChainHandles.nativeKernel source roots) state.1, state.2)).IsQueryBoundP predicate budget ↔
      ((simulateQ (sourceImpl (handleCalls source writer roots) senderId decode) client).run state).IsQueryBoundP
        predicate budget := by
  rw [handles_source, isQueryBoundP_map_iff]

/-- Rejected attempts and original callback effects retain the actual 64-byte commitment bound. -/
theorem handles_uniform {Atom Auxiliary Metadata Result : Type}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (roots : Atom → RatchetChain) (senderId : Std.U64) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp RawCtxMixedOwner.SourceSpec Result) (qSend qRaw : Nat)
    (sendBound : client.IsQueryBoundP (fun query => query.isLeft = true) qSend)
    (rawBound : client.IsQueryBoundP (fun query => query.isRight = true) qRaw)
    (state : State (RawCtxSourceChainHandles.HandleKernel Atom) Metadata × RawCtxSharedPrimitive.SharedState Auxiliary) :
    ((simulateQ (sourceImpl (handleCalls source writer roots) senderId decode) client).run state).IsTotalQueryBound
      (64 * (qSend + qRaw)) := by
  have bound := RawCtxSourceHkdf.mixed_uniform source writer senderId decode client qSend qRaw
    sendBound rawBound (nativeState (RawCtxSourceChainHandles.nativeKernel source roots) state.1) state.2
  rw [RawCtxMixedShared.shared_source] at bound
  have direct : ((simulateQ (RawCtxMixedOwner.sourceImpl (RawCtxSourceMaterialLabels.nativeImpl source writer)
      senderId decode) client).run
      (nativeState (RawCtxSourceChainHandles.nativeKernel source roots) state.1, state.2)).IsTotalQueryBound
      (64 * (qSend + qRaw)) := (isQueryBound_map_iff _ _ _ _ _).mp bound
  rw [handles_source] at direct
  exact (isQueryBound_map_iff _ _ _ _ _).mp direct

end BeaconcryptCore.Computational.RawCtxChainOwner

/-- info: 'BeaconcryptCore.Computational.RawCtxChainOwner.rawReceive_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxChainOwner.rawReceive_native

/-- info: 'BeaconcryptCore.Computational.RawCtxChainOwner.sendOwner_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxChainOwner.sendOwner_native

/-- info: 'BeaconcryptCore.Computational.RawCtxChainOwner.owner_native' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxChainOwner.owner_native

/-- info: 'BeaconcryptCore.Computational.RawCtxChainOwner.source_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxChainOwner.source_step

/-- info: 'BeaconcryptCore.Computational.RawCtxChainOwner.source_schedule' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxChainOwner.source_schedule

/-- info: 'BeaconcryptCore.Computational.RawCtxChainOwner.handles_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxChainOwner.handles_source

/-- info: 'BeaconcryptCore.Computational.RawCtxChainOwner.handles_query_bounds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxChainOwner.handles_query_bounds

/-- info: 'BeaconcryptCore.Computational.RawCtxChainOwner.handles_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxChainOwner.handles_uniform
