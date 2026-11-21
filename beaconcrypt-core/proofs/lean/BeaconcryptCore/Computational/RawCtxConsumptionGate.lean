import BeaconcryptCore.Computational.RawCtxReceiveConsumption

/-!
The source consumption guard is derived from actual control/cache rejection, rather than imposed as an authentication premise. An index already present in the checked source history is below the receive counter and absent from the live cache. The actual zero/replay source branch therefore rejects before every KDF or opening callback. Exact raw and monitored equations retain the original owner, raw-attempt publication and complete primitive state.

An explicit private consumed-position guard is then proved equal to the original monitored source operation on every reachable state. The equality extends through arbitrary adaptive mixed send/raw continuations and erases only the private history to give the original complete OracleComp program. Either actual source initializer establishes the required empty-history relation for any supplied root. Every selective underlying uniform-oracle bound is exactly equivalent; no resource conclusion is transported through only a marginal probability equality.

The guard uses the same pure functional raw decoder, so it may perform extra local decoding and list membership work. These equalities preserve protocol results and primitive requests, not native parser/traversal traces, timing, allocation or local runtime. No hash or other primitive effect is discarded; an actually consumed source request has none. The history is private analysis state, excluded from network/reveal/snapshot/persistence interfaces.

Scope remains one uninterrupted initialized owner under the existing fixed functional source KDF. A restored or copied earlier kernel need not satisfy the current consumed-history relation. Source lifecycle/registration handoffs, concurrent ownership, storage/rollback/CAS/crash premises, correlated evolving-output interpretation and the persistent ProVerif trace mapping remain explicit obligations. Distinct positions may share material bytes; the guard establishes neither key uniqueness nor cryptographic freshness or origin. No primitive implementation, parser library or global security theorem is proved here.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
open OracleComp OracleSpec
open BeaconcryptCore.Refinement.RepresentationBridge
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RawCtxConsumptionGate
open RawCtxMaterialPositions RawCtxReceiveConsumption

/-- Actual source control/cache membership rejects a consumed target before any callback, including target zero. -/
theorem receive_spent {Context Plaintext : Type}
    (c : Pqxdh.Crypto) (sendOrigin receiveOrigin : RatchetChain)
    (kernel : ConcreteRatchetKernel) (spent : List Nat)
    (invariant : ConsumedRefines c sendOrigin receiveOrigin kernel spent)
    (target : Std.U64) (context : Context) (consumed : target.val - 1 ∈ spent) :
    (RawCtxOwnerOracle.receive kernel target context :
      OracleComp (RawCtxOwnerOracle.ReceiveSpec Context Plaintext)
        (ConcreteRatchetKernel × core.option.Option Plaintext)) = pure (kernel, .None) := by
  obtain ⟨send, receive, refines, aligned, recorded, unique⟩ := invariant
  have absent := recorded _ consumed
  have rejected : begin_receive kernel target context = ok (.ReceiveRejected kernel context) :=
    if zero : target = 0#u64 then zero ▸ refines.begin_receive_zero
      (crypto c) receiveOrigin send receive kernel context
    else refines.begin_receive_replay (crypto c) receiveOrigin send receive kernel target context
      (by omega) (by scalar_tac) absent.2
  have began : RawCtxOwnerOracle.begin kernel target context = .ReceiveRejected kernel context :=
    RustM.ok.inj ((RawCtxOwnerOracle.begin_exact kernel target context).symm.trans rejected)
  simp only [RawCtxOwnerOracle.receive, began, RawCtxOwnerOracle.program]

/-- The raw decoder and validation wrapper retain exact None publication for a consumed decoded position. -/
theorem rawReceive_spent {Metadata : Type}
    (c : Pqxdh.Crypto) (sendOrigin receiveOrigin : RatchetChain)
    (state : RawCtxWholeOwner.OwnerState Metadata) (spent : List Nat)
    (invariant : ConsumedRefines c sendOrigin receiveOrigin state.owner.kernel spent)
    (decode : RawCtxReceive.FrameDecoder) (raw : Pqxdh.Bytes)
    (frame : RawCtxReceive.DecodedFrame) (decoded : decode raw = some frame)
    (consumed : frame.sequence.val - 1 ∈ spent) :
    (RawCtxWholeOwner.rawReceive decode raw).run state =
      pure (RawCtxWholeOwner.publish state (state.owner.kernel, .None)) := by
  simp only [RawCtxWholeOwner.rawReceive, StateT.run, decoded]
  simp only [receive_spent c sendOrigin receiveOrigin state.owner.kernel spent invariant
    frame.sequence _ consumed, simulateQ_pure, pure_bind, ite_self]

/-- Arbitrary primitive state is preserved exactly because the actual consumed branch issues no primitive request. -/
theorem rawGame_spent {Metadata PrimitiveState : Type} {ι : Type} {base : OracleSpec ι}
    (c : Pqxdh.Crypto) (sendOrigin receiveOrigin : RatchetChain)
    (state : RawCtxWholeOwner.OwnerState Metadata) (spent : List Nat)
    (invariant : ConsumedRefines c sendOrigin receiveOrigin state.owner.kernel spent)
    (impl : QueryImpl RawCtxWholeOwner.PrimitiveSpec (StateT PrimitiveState (OracleComp base)))
    (primitive : PrimitiveState) (decode : RawCtxReceive.FrameDecoder) (raw : Pqxdh.Bytes)
    (frame : RawCtxReceive.DecodedFrame) (decoded : decode raw = some frame)
    (consumed : frame.sequence.val - 1 ∈ spent) :
    RawCtxWholeOwner.rawGame impl decode raw state primitive =
      pure (RawCtxWholeOwner.publish state (state.owner.kernel, .None), primitive) := by
  simp only [RawCtxWholeOwner.rawGame,
    rawReceive_spent c sendOrigin receiveOrigin state spent invariant decode raw frame decoded consumed,
    simulateQ_pure, StateT.run_pure]

/-- The original private monitor records no new entry after actual consumed-position rejection. -/
theorem tracked_raw_spent {Metadata Auxiliary : Type}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (sendOrigin receiveOrigin : RatchetChain) (sender : Std.U64)
    (state : RawCtxWholeOwner.OwnerState Metadata × RawCtxSharedPrimitive.SharedState Auxiliary)
    (spent : List Nat)
    (invariant : ConsumedRefines source.crypto sendOrigin receiveOrigin state.1.owner.kernel spent)
    (decode : RawCtxReceive.FrameDecoder) (raw : Pqxdh.Bytes)
    (frame : RawCtxReceive.DecodedFrame) (decoded : decode raw = some frame)
    (consumed : frame.sequence.val - 1 ∈ spent) :
    (trackedImpl source writer sender decode (.inr raw)).run (state, spent) =
      pure (.None, ((RawCtxWholeOwner.publish state.1 (state.1.owner.kernel, .None)).2,
        state.2), spent) := by
  simp only [trackedImpl, RawCtxMixedOwner.sourceImpl, StateT.run]
  simp only [RawCtxWholeOwner.ownerImpl]
  simp only [rawGame_spent source.crypto sendOrigin receiveOrigin state.1 spent invariant
    _ state.2 decode raw frame decoded consumed, pure_bind, recordSource, recordReply,
    RawCtxWholeOwner.publish]

noncomputable def gatedImpl {Metadata Auxiliary : Type}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (sender : Std.U64) (decode : RawCtxReceive.FrameDecoder) :
    QueryImpl RawCtxMixedOwner.SourceSpec
      (StateT ((RawCtxWholeOwner.OwnerState Metadata × RawCtxSharedPrimitive.SharedState Auxiliary) × List Nat) ProbComp) :=
  fun query state => match query with
  | .inl plaintext => (trackedImpl source writer sender decode (.inl plaintext)).run state
  | .inr raw => match decode raw with
      | none => (trackedImpl source writer sender decode (.inr raw)).run state
      | some frame =>
          if frame.sequence.val - 1 ∈ state.2 then
            pure (.None, ((RawCtxWholeOwner.publish state.1.1 (state.1.1.owner.kernel, .None)).2,
              state.1.2), state.2)
          else (trackedImpl source writer sender decode (.inr raw)).run state

/-- An explicit private consumed-position guard has the identical full source step on the proved owner invariant. -/
theorem gated_step {Metadata Auxiliary : Type}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (sendOrigin receiveOrigin : RatchetChain) (sender : Std.U64) (decode : RawCtxReceive.FrameDecoder)
    (query : RawCtxMixedOwner.SourceSpec.Domain)
    (state : (RawCtxWholeOwner.OwnerState Metadata × RawCtxSharedPrimitive.SharedState Auxiliary) × List Nat)
    (invariant : ConsumedRefines source.crypto sendOrigin receiveOrigin state.1.1.owner.kernel state.2) :
    (gatedImpl source writer sender decode query).run state =
      (trackedImpl source writer sender decode query).run state := by
  cases query with
  | inl plaintext => rfl
  | inr raw =>
      simp only [gatedImpl, StateT.run]
      cases decoded : decode raw with
      | none => rfl
      | some frame =>
          dsimp only
          split
          · rename_i consumed
            exact (tracked_raw_spent source writer sendOrigin receiveOrigin sender state.1 state.2
              invariant decode raw frame decoded consumed).symm
          · rfl

/-- The same guard preserves complete arbitrary adaptive continuations and all actual source states. -/
theorem gated_schedule {Metadata Auxiliary Result : Type}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (sendOrigin receiveOrigin : RatchetChain) (sender : Std.U64) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp RawCtxMixedOwner.SourceSpec Result)
    (state : (RawCtxWholeOwner.OwnerState Metadata × RawCtxSharedPrimitive.SharedState Auxiliary) × List Nat)
    (invariant : ConsumedRefines source.crypto sendOrigin receiveOrigin state.1.1.owner.kernel state.2) :
    (simulateQ (gatedImpl source writer sender decode) client).run state =
      (simulateQ (trackedImpl source writer sender decode) client).run state := by
  induction client using OracleComp.inductionOn generalizing state with
  | pure value => rfl
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind,
        gated_step source writer sendOrigin receiveOrigin sender decode query state invariant]
      apply bind_congr_of_forall_mem_support
      intro reply supported
      exact ih reply.1 reply.2 (tracked_step_spent source writer sendOrigin receiveOrigin
        sender decode query state invariant reply supported)

/-- Erasing only the private history gives the original whole source program after the checked guard substitution. -/
theorem gated_source_erasure {Metadata Auxiliary Result : Type}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (sendOrigin receiveOrigin : RatchetChain) (sender : Std.U64) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp RawCtxMixedOwner.SourceSpec Result)
    (state : RawCtxWholeOwner.OwnerState Metadata × RawCtxSharedPrimitive.SharedState Auxiliary)
    (spent : List Nat)
    (invariant : ConsumedRefines source.crypto sendOrigin receiveOrigin state.1.owner.kernel spent) :
    (fun result => (result.1, result.2.1)) <$>
        (simulateQ (gatedImpl source writer sender decode) client).run (state, spent) =
      (simulateQ (RawCtxMixedOwner.sourceImpl
        (RawCtxMixedShared.sharedImpl source.crypto writer (RawCtxSourceHkdf.kdfImpl source)) sender decode) client).run state := by
  rw [gated_schedule source writer sendOrigin receiveOrigin sender decode client (state, spent) invariant,
    tracked_erasure]

/-- Every selective underlying uniform-query cap is exactly equivalent on the same source execution. -/
theorem gated_query_bounds {Metadata Auxiliary Result : Type}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (sendOrigin receiveOrigin : RatchetChain) (sender : Std.U64) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp RawCtxMixedOwner.SourceSpec Result)
    (state : RawCtxWholeOwner.OwnerState Metadata × RawCtxSharedPrimitive.SharedState Auxiliary)
    (spent : List Nat)
    (invariant : ConsumedRefines source.crypto sendOrigin receiveOrigin state.1.owner.kernel spent)
    (predicate : unifSpec.Domain → Prop) [DecidablePred predicate] (budget : Nat) :
    ((simulateQ (gatedImpl source writer sender decode) client).run (state, spent)).IsQueryBoundP predicate budget ↔
      ((simulateQ (RawCtxMixedOwner.sourceImpl
        (RawCtxMixedShared.sharedImpl source.crypto writer (RawCtxSourceHkdf.kdfImpl source)) sender decode) client).run state).IsQueryBoundP predicate budget := by
  rw [gated_schedule source writer sendOrigin receiveOrigin sender decode client (state, spent) invariant,
    tracked_query_bounds]

open BeaconcryptCore.Refinement.PqxdhConcreteSession

/-- Either actual initializer derives the empty-history guard equivalence for the supplied root. -/
theorem initialized_erasure {Metadata Auxiliary Result : Type}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (root : Std.Array Std.U8 32#usize) (sender : Std.U64) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp RawCtxMixedOwner.SourceSpec Result)
    (state : RawCtxWholeOwner.OwnerState Metadata × RawCtxSharedPrimitive.SharedState Auxiliary)
    (initialized : initializeBeacon root (RawCtxSourceHkdf.initialResponse source.crypto) = ok state.1.owner.kernel ∨
      initializeServer root (RawCtxSourceHkdf.initialResponse source.crypto) = ok state.1.owner.kernel) :
    (fun result => (result.1, result.2.1)) <$>
        (simulateQ (gatedImpl source writer sender decode) client).run (state, []) =
      (simulateQ (RawCtxMixedOwner.sourceImpl
        (RawCtxMixedShared.sharedImpl source.crypto writer (RawCtxSourceHkdf.kdfImpl source)) sender decode) client).run state := by
  exact gated_source_erasure source writer state.1.owner.kernel.refined.send_chain
    state.1.owner.kernel.refined.receive_chain sender decode client state []
    (initialized_spent source.crypto root state.1.owner.kernel initialized)

end BeaconcryptCore.Computational.RawCtxConsumptionGate

/--
info: 'BeaconcryptCore.Computational.RawCtxConsumptionGate.receive_spent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxConsumptionGate.receive_spent

/--
info: 'BeaconcryptCore.Computational.RawCtxConsumptionGate.rawReceive_spent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxConsumptionGate.rawReceive_spent

/--
info: 'BeaconcryptCore.Computational.RawCtxConsumptionGate.rawGame_spent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxConsumptionGate.rawGame_spent

/--
info: 'BeaconcryptCore.Computational.RawCtxConsumptionGate.tracked_raw_spent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxConsumptionGate.tracked_raw_spent

/--
info: 'BeaconcryptCore.Computational.RawCtxConsumptionGate.gated_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxConsumptionGate.gated_step

/--
info: 'BeaconcryptCore.Computational.RawCtxConsumptionGate.gated_schedule' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxConsumptionGate.gated_schedule

/--
info: 'BeaconcryptCore.Computational.RawCtxConsumptionGate.gated_source_erasure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxConsumptionGate.gated_source_erasure

/--
info: 'BeaconcryptCore.Computational.RawCtxConsumptionGate.gated_query_bounds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxConsumptionGate.gated_query_bounds

/--
info: 'BeaconcryptCore.Computational.RawCtxConsumptionGate.initialized_erasure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxConsumptionGate.initialized_erasure
