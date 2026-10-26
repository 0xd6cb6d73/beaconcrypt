import BeaconcryptCore.Computational.RawCtxSelectedParentCalls

/-!
The original native mixed-owner backend uses the same retained private KDF response table as the interpreted native Calls. Every opening, sealing, commitment and writer callback remains the original full shared-state implementation. Adapter and complete call equalities discharge the concrete source-realization obligations used by the finite role frontends. This is an explicit retained-table intermediate; public HKDF remains the separate real service, and no freshness or cryptographic premise is introduced.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.refined ratchet.concrete
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RawCtxSelectedParentNativeBackend
open RawCtxSelectedParentCalls RawCtxSelectedParentEntry RawCtxSelectedParentTable
open PqxdhJointKdf PqxdhJointKdfGame PqxdhSecretInputKdf

noncomputable def backend {Auxiliary : Type}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (entry : Entry) (target : RootOutput) :
    QueryImpl RawCtxMixedOwner.NativeSpec (StateT (RawCtxSharedPrimitive.SharedState Auxiliary) ProbComp)
  | .inl request => pure (RawCtxSelectedParentSource.response prior entry target request)
  | .inr query => RawCtxSourceMaterialLabels.nativeImpl source writer (.inr query)

private theorem opening_lift {Auxiliary : Type}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (entry : Entry) (target : RootOutput) :
    backend (Auxiliary := Auxiliary) source writer prior entry target ∘ₛ
        (RawCtxMixedOwner.receiveLift ∘ₛ RawCtxSourceOpen.openLift) =
      RawCtxSourceMaterialLabels.nativeImpl source writer ∘ₛ
        (RawCtxMixedOwner.receiveLift ∘ₛ RawCtxSourceOpen.openLift) := by
  funext query
  cases query <;> simp [QueryImpl.compose, RawCtxSourceOpen.openLift, RawCtxMixedOwner.receiveLift,
    backend, OracleSpec.query]

private theorem open_input {Auxiliary : Type}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (entry : Entry) (target : RootOutput) (input : RawCtxWholeOwner.OpenInput) :
    (backend (Auxiliary := Auxiliary) source writer prior entry target ∘ₛ RawCtxMixedOwner.receiveAdapter) (.inr input) =
      (RawCtxSourceMaterialLabels.nativeImpl source writer ∘ₛ RawCtxMixedOwner.receiveAdapter) (.inr input) := by
  simp only [RawCtxMixedOwner.receiveAdapter, QueryImpl.compose, RawCtxSourceOpen.nativeAdapter]
  simp only [← QueryImpl.simulateQ_compose, opening_lift]

/-- The actual native receive adapter decodes the same retained response and opens with unchanged source arguments and shared state. -/
theorem receive_adapter {Auxiliary : Type}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (entry : Entry) (target : RootOutput) :
    ((backend (Auxiliary := Auxiliary) source writer prior entry target ∘ₛ RawCtxMixedOwner.receiveAdapter) ∘ₛ
      RawCtxWholeOwner.adapter) ∘ₛ RawCtxInterpretedReceive.nativeAdapter =
      RawCtxSelectedParentSource.nativeReceive source writer prior entry target := by
  funext query
  cases query with
  | inl request =>
    simp [QueryImpl.compose, RawCtxInterpretedReceive.nativeAdapter, RawCtxWholeOwner.adapter,
      RawCtxMixedOwner.receiveAdapter, RawCtxSourceOpen.nativeAdapter, RawCtxMixedOwner.receiveLift,
      backend, RawCtxSelectedParentSource.nativeReceive, OracleSpec.query]
  | inr opening =>
    change (simulateQ ((backend source writer prior entry target ∘ₛ RawCtxMixedOwner.receiveAdapter) ∘ₛ
      RawCtxWholeOwner.adapter)
      ((RawCtxOwnerOracle.ReceiveSpec RawCtxWholeOwner.OpenContext RawCtxWholeOwner.Decrypted).query
        (.inr (RawCtxInterpretedOpening.toNative opening))) :
        StateT (RawCtxSharedPrimitive.SharedState Auxiliary) ProbComp (core.option.Option RawCtxWholeOwner.Decrypted)) = _
    refine (_root_.simulateQ_spec_query _ _).trans ?_
    simp only [QueryImpl.compose, RawCtxSelectedParentSource.nativeReceive, RawCtxSourceChainHandles.receiveNative,
      RawCtxWholeOwner.adapter]
    split
    · rfl
    · simp only [simulateQ_bind, simulateQ_spec_query, simulateQ_pure]
      rw [open_input]

private theorem sealing_lift {Auxiliary : Type}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (entry : Entry) (target : RootOutput) :
    backend (Auxiliary := Auxiliary) source writer prior entry target ∘ₛ
        (RawCtxMixedOwner.sendLift ∘ₛ RawCtxSourceSeal.sealLift) =
      RawCtxSourceMaterialLabels.nativeImpl source writer ∘ₛ
        (RawCtxMixedOwner.sendLift ∘ₛ RawCtxSourceSeal.sealLift) := by
  funext query
  rcases query with input | (bytes | frame)
  all_goals simp [QueryImpl.compose, RawCtxSourceSeal.sealLift, RawCtxMixedOwner.sendLift,
    backend, OracleSpec.query]

private theorem seal_input {Auxiliary : Type}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (entry : Entry) (target : RootOutput) (input : RawCtxSourceSend.SealInput) :
    (backend (Auxiliary := Auxiliary) source writer prior entry target ∘ₛ RawCtxMixedOwner.sendAdapter) (.inr input) =
      (RawCtxSourceMaterialLabels.nativeImpl source writer ∘ₛ RawCtxMixedOwner.sendAdapter) (.inr input) := by
  simp only [RawCtxMixedOwner.sendAdapter, QueryImpl.compose, RawCtxSourceSeal.nativeAdapter]
  simp only [← QueryImpl.simulateQ_compose, sealing_lift]

/-- The actual send adapter uses the same retained KDF and complete original seal, commitment, serialization and optional result. -/
theorem send_adapter {Auxiliary : Type}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (entry : Entry) (target : RootOutput) :
    ((backend (Auxiliary := Auxiliary) source writer prior entry target ∘ₛ RawCtxMixedOwner.sendAdapter) ∘ₛ
      RawCtxSourceSend.adapter) ∘ₛ RawCtxInterpretedSend.nativeAdapter =
      RawCtxSelectedParentSource.nativeSend source writer prior entry target := by
  funext query
  cases query with
  | inl request =>
    simp [QueryImpl.compose, RawCtxInterpretedSend.nativeAdapter, RawCtxSourceSend.adapter,
      RawCtxMixedOwner.sendAdapter, RawCtxSourceSeal.nativeAdapter, RawCtxMixedOwner.sendLift,
      backend, RawCtxSelectedParentSource.nativeSend, OracleSpec.query]
  | inr sealing =>
    change (simulateQ ((backend source writer prior entry target ∘ₛ RawCtxMixedOwner.sendAdapter) ∘ₛ
      RawCtxSourceSend.adapter)
      ((RawCtxSourceSend.SendSpec RawCtxSourceSend.SealContext RawCtxSourceSend.Encrypted).query
        (.inr (RawCtxInterpretedSend.nativeSeal sealing))) :
        StateT (RawCtxSharedPrimitive.SharedState Auxiliary) ProbComp (Option RawCtxSourceSend.Encrypted)) = _
    refine (_root_.simulateQ_spec_query _ _).trans ?_
    simp only [QueryImpl.compose, RawCtxSelectedParentSource.nativeSend, RawCtxSourceChainHandles.sendNative,
      RawCtxSourceSend.adapter, simulateQ_bind, simulateQ_spec_query, simulateQ_pure]
    exact congrArg (fun work : StateT (RawCtxSharedPrimitive.SharedState Auxiliary) ProbComp (Option Pqxdh.Bytes) =>
      work >>= fun ciphertext => pure (ciphertext.map (RawCtxSourceSend.encrypted
        (RawCtxSourceSend.arguments (RawCtxInterpretedSend.nativeSeal sealing)))))
      (seal_input source writer prior entry target _)

/-- The concrete retained-table receive discharges the original owner realization obligation for the entire native kernel. -/
theorem receive_realized {Auxiliary : Type}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (entry : Entry) (target : RootOutput) (kernel : Kernel RatchetChain)
    (sequence : Std.U64) (context : RawCtxWholeOwner.OpenContext) :
    simulateQ ((backend (Auxiliary := Auxiliary) source writer prior entry target ∘ₛ RawCtxMixedOwner.receiveAdapter) ∘ₛ
      RawCtxWholeOwner.adapter) (RawCtxOwnerOracle.receive ⟨kernel⟩ sequence context) =
      (fun result => (ConcreteRatchetKernel.mk result.1, result.2)) <$>
        (nativeCalls source writer prior entry target).receive kernel sequence context := by
  rw [RawCtxInterpretedReceive.receive_native, simulateQ_map, ← QueryImpl.simulateQ_compose, receive_adapter]
  rfl

/-- The concrete retained-table send discharges the original owner realization obligation through failed seals and retained advanced state. -/
theorem send_realized {Auxiliary : Type}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (entry : Entry) (target : RootOutput) (kernel : Kernel RatchetChain)
    (context : RawCtxSourceSend.SealContext) :
    simulateQ ((backend (Auxiliary := Auxiliary) source writer prior entry target ∘ₛ RawCtxMixedOwner.sendAdapter) ∘ₛ
      RawCtxSourceSend.adapter) (RawCtxSourceSend.send ⟨kernel⟩ context) =
      (fun result => (ConcreteRatchetKernel.mk result.1, result.2)) <$>
        (nativeCalls source writer prior entry target).send kernel context := by
  rw [RawCtxInterpretedSend.send_native, simulateQ_map, ← QueryImpl.simulateQ_compose, send_adapter]
  rfl

/-- The original raw/send owner is realized by concrete retained-table Calls without any supplied callback-compatibility premise. -/
theorem owner_realized {Metadata Auxiliary : Type}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (entry : Entry) (target : RootOutput) (sender : Std.U64) (decode : RawCtxReceive.FrameDecoder)
    (query : RawCtxMixedOwner.SourceSpec.Domain) (state : RawCtxChainOwner.State (Kernel RatchetChain) Metadata) :
    simulateQ (backend (Auxiliary := Auxiliary) source writer prior entry target)
      ((RawCtxMixedOwner.ownerImpl sender decode query).run (RawCtxChainOwner.nativeState ConcreteRatchetKernel.mk state)) =
      Prod.map id (RawCtxChainOwner.nativeState ConcreteRatchetKernel.mk) <$>
        (RawCtxChainOwner.ownerImpl (nativeCalls source writer prior entry target) sender decode query).run state := by
  exact RawCtxChainOwner.owner_native ConcreteRatchetKernel.mk (nativeCalls source writer prior entry target)
    (backend source writer prior entry target) (receive_realized source writer prior entry target)
    (send_realized source writer prior entry target) sender decode query state

/-- Retaining an actual source response recovers the original mixed native backend on every request. -/
theorem source_backend {Auxiliary : Type}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (address : JointKdfAddress) :
    backend (Auxiliary := Auxiliary) source writer (productionStream source.crypto)
      (fromOutput address (productionStream source.crypto address))
      (PqxdhOrderedChainHybrids.nextChain (productionStream source.crypto address)) =
      RawCtxSourceMaterialLabels.nativeImpl source writer := by
  funext query
  cases query with
  | inl request =>
    simp only [backend, RawCtxSelectedParentSource.response_source]
    simp [RawCtxSourceMaterialLabels.nativeImpl, RawCtxMixedShared.sharedImpl, QueryImpl.compose,
      RawCtxMixedShared.sharedAdapter, OracleSpec.query]
    rfl
  | inr query => rfl

/-- Complete original owner interpretation preserves every selective primitive-query cap by literal program equality. -/
theorem owner_queries {Metadata Auxiliary : Type}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (entry : Entry) (target : RootOutput) (sender : Std.U64) (decode : RawCtxReceive.FrameDecoder)
    (query : RawCtxMixedOwner.SourceSpec.Domain) (state : RawCtxChainOwner.State (Kernel RatchetChain) Metadata)
    (shared : RawCtxSharedPrimitive.SharedState Auxiliary) (predicate : unifSpec.Domain → Prop)
    [DecidablePred predicate] (budget : Nat) :
    ((simulateQ (backend source writer prior entry target)
      ((RawCtxMixedOwner.ownerImpl sender decode query).run
        (RawCtxChainOwner.nativeState ConcreteRatchetKernel.mk state))).run shared).IsQueryBoundP predicate budget ↔
      (((RawCtxChainOwner.ownerImpl (nativeCalls source writer prior entry target) sender decode query).run state).run
        shared).IsQueryBoundP predicate budget := by
  rw [owner_realized, StateT.run_map, isQueryBoundP_map_iff]

end BeaconcryptCore.Computational.RawCtxSelectedParentNativeBackend

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedParentNativeBackend.receive_adapter' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedParentNativeBackend.receive_adapter
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedParentNativeBackend.send_adapter' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedParentNativeBackend.send_adapter
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedParentNativeBackend.receive_realized' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedParentNativeBackend.receive_realized
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedParentNativeBackend.send_realized' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedParentNativeBackend.send_realized
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedParentNativeBackend.owner_realized' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedParentNativeBackend.owner_realized
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedParentNativeBackend.source_backend' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedParentNativeBackend.source_backend
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedParentNativeBackend.owner_queries' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedParentNativeBackend.owner_queries
