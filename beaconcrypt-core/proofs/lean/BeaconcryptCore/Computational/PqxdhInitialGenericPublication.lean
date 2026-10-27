import BeaconcryptCore.Computational.PqxdhInitialPrivateCurrent
import BeaconcryptCore.Computational.RawCtxGenericRoleStorage
import BeaconcryptCore.Computational.RawCtxSelectedParentNativeBackend

/-!
The actual registration first send and publication preserve a kernel-representation map before the first ciphertext. The generic state retains every existing peer, source identity, allocation control and consumed registration. Only private ratchet representation changes. Concrete retained-table send equations discharge the native source callback law; the labelled continuation receives no selected initial half.
-/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhInitialGenericPublication
open PqxdhServerRegistrationPublication
variable {Kernel Metadata PeerMetadata Consumed Result : Type}
variable {m : Type → Type} [Monad m] [LawfulMonad m]

structure State (Kernel Metadata PeerMetadata Consumed : Type) where
  server : RawCtxGenericRoleStorage.Server Kernel Metadata PeerMetadata
  identityKeyId : Std.U64
  control : pqxdh.ServerState
  consumed : Consumed

def native (interpret : Kernel → ConcreteRatchetKernel) (state : State Kernel Metadata PeerMetadata Consumed) :
    PqxdhServerRegistrationPublication.State Metadata PeerMetadata Consumed :=
  ⟨(RawCtxGenericRoleStorage.nativeServer interpret ⟨state.server, 0⟩).server,
    state.identityKeyId, state.control, state.consumed⟩

def publish (state : State Kernel Metadata PeerMetadata Consumed)
    (candidate : pqxdh.ServerRegistrationCandidate) (kernel : Kernel) (metadata : PeerMetadata) :
    State Kernel Metadata PeerMetadata Consumed :=
  { state with
    control := candidate.next_state
    server := { state.server with peers := Function.update state.server.peers candidate.key_id (some ⟨candidate.beacon_identity_public_key, kernel, metadata⟩) } }

/-- Installing the advanced first-send kernel updates exactly the original peer while retaining all other peers, source identities and allocation/consumed fields. -/
theorem publish_native (interpret : Kernel → ConcreteRatchetKernel)
    (state : State Kernel Metadata PeerMetadata Consumed) (candidate : pqxdh.ServerRegistrationCandidate)
    (kernel : Kernel) (metadata : PeerMetadata) :
    native interpret (publish state candidate kernel metadata) =
      PqxdhServerRegistrationPublication.publish (native interpret state) candidate (interpret kernel) metadata := by
  simp only [native, publish, PqxdhServerRegistrationPublication.publish, RawCtxGenericRoleStorage.nativeServer]
  congr 1
  congr 1
  funext key
  by_cases same : key = candidate.key_id
  · subst key
    simp only [Function.update_self, Option.map_some]
  · simp only [Function.update_of_ne same]

noncomputable def afterInitialization (calls : RawCtxChainOwner.Calls Kernel m) (aux : QueryImpl AuxSpec m)
    (candidate : pqxdh.ServerRegistrationCandidate) (authenticated : Pqxdh.Bytes)
    (kernel : Kernel) (metadata : PeerMetadata) (state : State Kernel Metadata PeerMetadata Consumed) :
    m (Option Response × State Kernel Metadata PeerMetadata Consumed) := do
  let (advanced, encrypted) ← calls.send kernel (firstContext candidate authenticated)
  let _ ← aux (.erase authenticated)
  match encrypted with
  | none => pure (none, state)
  | some encrypted =>
      let serialized ← aux (.write (responseFields candidate encrypted))
      match serialized with
      | none => pure (none, state)
      | some serialized => pure (some ⟨serialized, candidate.key_id⟩, publish state candidate advanced metadata)

noncomputable def nativeImpl (backend : QueryImpl RawCtxMixedOwner.NativeSpec m) (aux : QueryImpl AuxSpec m) :
    QueryImpl PqxdhServerRegistrationPublication.NativeSpec m
  | .inl query => (backend ∘ₛ RawCtxMixedOwner.sendLift) query
  | .inr query => aux query

set_option backward.isDefEq.respectTransparency false in
/-- The actual registration send adapter forwards precisely the original mixed native send interface before any ciphertext is produced. -/
theorem send_adapter (backend : QueryImpl RawCtxMixedOwner.NativeSpec m) (aux : QueryImpl AuxSpec m) :
    (nativeImpl backend aux ∘ₛ PqxdhServerRegistrationPublication.nativeAdapter) ∘ₛ
      PqxdhServerRegistrationPublication.sendLift = backend ∘ₛ RawCtxMixedOwner.sendAdapter := by
  funext query
  simp only [QueryImpl.compose, PqxdhServerRegistrationPublication.sendLift, simulateQ_spec_query,
    PqxdhServerRegistrationPublication.nativeAdapter, RawCtxMixedOwner.sendAdapter,
    ← QueryImpl.simulateQ_compose]
  congr 1
  funext request
  simp only [QueryImpl.compose, simulateQ_spec_query, nativeImpl]

set_option backward.isDefEq.respectTransparency false in
/-- The actual first-send, erase, serialization and publication tail is natural in the complete private kernel representation, under the explicit send program equation. -/
theorem after_native (interpret : Kernel → ConcreteRatchetKernel)
    (calls : RawCtxChainOwner.Calls Kernel m) (backend : QueryImpl RawCtxMixedOwner.NativeSpec m)
    (aux : QueryImpl AuxSpec m)
    (sendRealized : ∀ entry context,
      simulateQ ((backend ∘ₛ RawCtxMixedOwner.sendAdapter) ∘ₛ RawCtxSourceSend.adapter)
        (RawCtxSourceSend.send (interpret entry) context) =
        (fun result => (interpret result.1, result.2)) <$> calls.send entry context)
    (candidate : pqxdh.ServerRegistrationCandidate) (authenticated : Pqxdh.Bytes)
    (kernel : Kernel) (metadata : PeerMetadata) (state : State Kernel Metadata PeerMetadata Consumed) :
    simulateQ (nativeImpl backend aux)
      (simulateQ PqxdhServerRegistrationPublication.nativeAdapter
        (PqxdhServerRegistrationPublication.afterInitialization candidate authenticated (interpret kernel) metadata (native interpret state))) =
      Prod.map id (native interpret) <$> afterInitialization calls aux candidate authenticated kernel metadata state := by
  have first :
      simulateQ (nativeImpl backend aux)
        (simulateQ PqxdhServerRegistrationPublication.nativeAdapter
          (simulateQ PqxdhServerRegistrationPublication.sendLift
            (simulateQ RawCtxSourceSend.adapter (RawCtxSourceSend.send (interpret kernel) (firstContext candidate authenticated))))) =
        (fun result => (interpret result.1, result.2)) <$> calls.send kernel (firstContext candidate authenticated) := by
    rw [← QueryImpl.simulateQ_compose, ← QueryImpl.simulateQ_compose, send_adapter,
      ← QueryImpl.simulateQ_compose, sendRealized]
  simp only [PqxdhServerRegistrationPublication.afterInitialization, afterInitialization,
    simulateQ_bind, first, bind_map_left, map_bind]
  simp only [simulateQ_spec_query, PqxdhServerRegistrationPublication.nativeAdapter, nativeImpl]
  apply bind_congr
  rintro ⟨advanced, encrypted⟩
  apply bind_congr
  intro erased
  cases encrypted with
  | none => simp only [simulateQ_pure, map_pure, Prod.map_apply, id_eq]
  | some encrypted =>
      simp only [simulateQ_bind, simulateQ_spec_query, PqxdhServerRegistrationPublication.nativeAdapter, nativeImpl, map_bind]
      apply bind_congr
      intro serialized
      cases serialized <;> simp only [simulateQ_pure, map_pure, Prod.map_apply, id_eq, publish_native]

/-- The original registration interpreter is the concrete real-backend instance of this exact publication interface. -/
theorem registration_source {A : Type} (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (writer : RawCtxMixedShared.Writer)
    (aux : QueryImpl AuxSpec (StateT (RawCtxSharedPrimitive.SharedState A) ProbComp)) :
    nativeImpl (RawCtxSourceMaterialLabels.nativeImpl source writer) aux =
      PqxdhRegistrationProtocolState.registrationImpl source writer aux := rfl

/-- The retained private table supplies the actual native send equation for every labelled kernel, including failure and already-advanced state; no caller-supplied source compatibility remains. -/
theorem selected_send {A : Type} (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (writer : RawCtxMixedShared.Writer) (prior : RawCtxSelectedParentTable.Prior)
    (entry : RawCtxSelectedParentEntry.Entry) (target : PqxdhSecretInputKdf.RootOutput)
    (kernel : RawCtxSelectedChain.Kernel) (context : RawCtxSourceSend.SealContext) :
    simulateQ ((RawCtxSelectedParentNativeBackend.backend (Auxiliary := A) source writer prior entry target ∘ₛ
      RawCtxMixedOwner.sendAdapter) ∘ₛ RawCtxSourceSend.adapter)
      (RawCtxSourceSend.send (RawCtxSelectedChain.nativeKernel (RawCtxFreshChainCut.concreteChain target) kernel) context) =
      (fun result => (RawCtxSelectedChain.nativeKernel (RawCtxFreshChainCut.concreteChain target) result.1, result.2)) <$>
        (RawCtxSelectedParentCalls.labelCalls source writer prior entry
          (RawCtxSelectedParentCalls.childResponse prior entry target)).send kernel context := by
  have sent := RawCtxSelectedParentNativeBackend.send_realized (Auxiliary := A) source writer prior entry target
    (RawCtxSelectedParentCalls.nativeKernel target kernel) context
  rw [RawCtxSelectedParentCalls.send_map] at sent
  simpa only [Functor.map_map, RawCtxSelectedChain.nativeKernel, RawCtxSelectedParentCalls.nativeKernel, Prod.map_fst, Prod.map_snd, id_eq] using sent

/-- The entire first ciphertext/publication tail runs with labelled private kernels and a supplied child response, while the actual selected input remains confined to the native interpretation. -/
theorem selected_after {A : Type} (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (writer : RawCtxMixedShared.Writer) (prior : RawCtxSelectedParentTable.Prior)
    (entry : RawCtxSelectedParentEntry.Entry) (target : PqxdhSecretInputKdf.RootOutput)
    (aux : QueryImpl AuxSpec (StateT (RawCtxSharedPrimitive.SharedState A) ProbComp))
    (candidate : pqxdh.ServerRegistrationCandidate) (authenticated : Pqxdh.Bytes)
    (kernel : RawCtxSelectedChain.Kernel) (metadata : PeerMetadata)
    (state : State RawCtxSelectedChain.Kernel Metadata PeerMetadata Consumed) :
    simulateQ (nativeImpl (RawCtxSelectedParentNativeBackend.backend source writer prior entry target) aux)
      (simulateQ PqxdhServerRegistrationPublication.nativeAdapter
        (PqxdhServerRegistrationPublication.afterInitialization candidate authenticated
          (RawCtxSelectedChain.nativeKernel (RawCtxFreshChainCut.concreteChain target) kernel) metadata
          (native (RawCtxSelectedChain.nativeKernel (RawCtxFreshChainCut.concreteChain target)) state))) =
      Prod.map id (native (RawCtxSelectedChain.nativeKernel (RawCtxFreshChainCut.concreteChain target))) <$>
        afterInitialization (RawCtxSelectedParentCalls.labelCalls source writer prior entry
          (RawCtxSelectedParentCalls.childResponse prior entry target)) aux candidate authenticated kernel metadata state :=
  after_native _ _ _ aux (selected_send source writer prior entry target) candidate authenticated kernel metadata state

end BeaconcryptCore.Computational.PqxdhInitialGenericPublication

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialGenericPublication.publish_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialGenericPublication.publish_native

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialGenericPublication.send_adapter' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialGenericPublication.send_adapter

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialGenericPublication.after_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialGenericPublication.after_native

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialGenericPublication.registration_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialGenericPublication.registration_source

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialGenericPublication.selected_send' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialGenericPublication.selected_send

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialGenericPublication.selected_after' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialGenericPublication.selected_after
