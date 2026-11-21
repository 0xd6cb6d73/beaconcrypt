import BeaconcryptCore.Computational.RawCtxSelectedParentTable

/-!
The original pending receive/send continuations run over one retained prior lookup plus the selected predecessor entry. Exact callback equations preserve both live chain coordinates, all staged material/control/context and complete shared primitive effects. The receive cut is before the remaining skip/open continuation; the send cut uses the actual extracted resumption and preserves advancement even when sealing fails. Only chain fields proved unread by primitive getters are omitted from those callbacks.

The supplied predecessor response and pending state remain private source context. A reached prefix must still establish their exact request/entry correspondence and the prior cache/miss distribution before any uniform replacement. These operational laws do not provide that correspondence, a target-free reached sampler, small exposure, an alias exclusion or a public random-HKDF assumption. The fixed-source specialization reconstructs actual typed responses from the original predecessor output. Selective query bounds transfer through literal full-program equality; local lookup/KDF/conversion work and the separately sampled full76 response remain charged. Snapshots, persistence and restoration are excluded.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.refined ratchet.concrete
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RawCtxSelectedParentSource
open RawCtxSelectedChain RawCtxChainInterpretation RawCtxSelectedParentEntry RawCtxSelectedParentTable
open PqxdhJointKdf PqxdhJointKdfGame PqxdhSecretInputKdf PqxdhFullSecretInputKdf

noncomputable def response (prior : Prior) (entry : Entry)
    (target : RootOutput) (request : SymmetricRatchetKdfRequest) : RatchetKdfResponse :=
  RawCtxKdfRequestTable.fullResponse (lookup prior entry target (RawCtxKdfRequestTable.address request))

noncomputable def nativeReceive {Auxiliary : Type}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (entry : Entry) (target : RootOutput) :
    QueryImpl (RawCtxInterpretedReceive.ReceiveSpec RatchetMaterial
      RawCtxWholeOwner.OpenContext RawCtxWholeOwner.Decrypted)
      (StateT (RawCtxSharedPrimitive.SharedState Auxiliary) ProbComp)
  | .inl request => pure (RawCtxInterpretedReceive.decodeResponse (response prior entry target request))
  | .inr pending => RawCtxSourceChainHandles.receiveNative source writer
      (.inr (RawCtxInterpretedOpening.toNative pending))

noncomputable def labelReceive {Auxiliary : Type}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (entry : Entry) (challenge : RatchetKdfResponse) :
    QueryImpl (RawCtxChainReceive.ReceiveSpec Slot Slot RatchetMaterial
      RawCtxWholeOwner.OpenContext RawCtxWholeOwner.Decrypted)
      (StateT (RawCtxSharedPrimitive.SharedState Auxiliary) ProbComp)
  | .inl request => pure (RawCtxSelectedParentTable.step prior entry challenge request)
  | .inr pending => receiveLabels source writer challenge (.inr pending)

/-- The native request and selected predecessor step share the complete response before the same full-state receive continuation. -/
theorem receive_kdf {Auxiliary : Type}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (entry : Entry) (target : RootOutput) (request : Slot) :
    nativeReceive (Auxiliary := Auxiliary) source writer prior entry target
      (.inl (RawCtxChainSend.nativeRequest (interpret (RawCtxFreshChainCut.concreteChain target) request))) =
      (fun reply => (interpret (RawCtxFreshChainCut.concreteChain target) reply.1, reply.2)) <$>
        labelReceive source writer prior entry
          (response prior entry target (RawCtxChainSend.nativeRequest (RawCtxFreshChainCut.concreteChain target)))
          (.inl request) := by
  simp only [nativeReceive, labelReceive, map_pure]
  exact congrArg pure (RawCtxSelectedParentTable.step_table prior entry target request)

/-- The opening callback reads the same material, sequence and context; retaining the predecessor does not alter any optional primitive effect. -/
theorem receive_open {Auxiliary : Type}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (entry : Entry) (target : RootOutput) (challenge : RatchetKdfResponse)
    (pending : RawCtxInterpretedOpening.Opening Slot Slot RatchetMaterial RawCtxWholeOwner.OpenContext) :
    nativeReceive (Auxiliary := Auxiliary) source writer prior entry target
      (.inr (mapOpeningChains (interpret (RawCtxFreshChainCut.concreteChain target))
        (interpret (RawCtxFreshChainCut.concreteChain target)) pending)) =
      labelReceive source writer prior entry challenge (.inr pending) :=
  RawCtxSelectedChain.receive_open source writer (RawCtxFreshChainCut.concreteChain target) challenge pending

/-- Every remaining source skip/open continuation retains the predecessor entry and complete callback state through original rejection and rollback. -/
theorem receive_program {Auxiliary : Type}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (entry : Entry) (target : RootOutput)
    (effect : RawCtxChainReceive.Effect Slot Slot RatchetMaterial RawCtxWholeOwner.OpenContext) :
    simulateQ (nativeReceive (Auxiliary := Auxiliary) source writer prior entry target)
      (RawCtxInterpretedReceive.program (RawCtxChainReceive.nativeEffect
        (interpret (RawCtxFreshChainCut.concreteChain target))
        (interpret (RawCtxFreshChainCut.concreteChain target)) effect)) =
      (fun result => (mapChains (interpret (RawCtxFreshChainCut.concreteChain target))
        (interpret (RawCtxFreshChainCut.concreteChain target)) result.1, result.2)) <$>
      simulateQ (labelReceive source writer prior entry
        (response prior entry target (RawCtxChainSend.nativeRequest (RawCtxFreshChainCut.concreteChain target))))
        (RawCtxChainReceive.program effect) :=
  RawCtxChainReceive.program_native
    (interpret (RawCtxFreshChainCut.concreteChain target))
    (interpret (RawCtxFreshChainCut.concreteChain target))
    (labelReceive source writer prior entry
      (response prior entry target (RawCtxChainSend.nativeRequest (RawCtxFreshChainCut.concreteChain target))))
    (nativeReceive source writer prior entry target) (receive_kdf source writer prior entry target)
    (receive_open source writer prior entry target _) effect

/-- The stopped point is the actual source KDF resumption, before any remaining skipped derivation or optional opening. The same complete predecessor output supplies the material and hidden next chain. -/
theorem receive_cut {Auxiliary : Type}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (entry : Entry) (target : RootOutput)
    (pending : RawCtxChainReceive.Kdf Slot Slot RatchetMaterial RawCtxWholeOwner.OpenContext) :
    simulateQ (nativeReceive (Auxiliary := Auxiliary) source writer prior entry target)
      (RawCtxInterpretedReceive.program (RawCtxInterpretedReceive.normalResume
        (RawCtxChainReceive.nativeKdf (interpret (RawCtxFreshChainCut.concreteChain target))
          (interpret (RawCtxFreshChainCut.concreteChain target)) pending)
        (RawCtxInterpretedReceive.decodeResponse (RawCtxKdfRequestTable.fullResponse (realize entry target))))) =
      (fun result => (mapChains (interpret (RawCtxFreshChainCut.concreteChain target))
        (interpret (RawCtxFreshChainCut.concreteChain target)) result.1, result.2)) <$>
      simulateQ (labelReceive source writer prior entry
        (response prior entry target (RawCtxChainSend.nativeRequest (RawCtxFreshChainCut.concreteChain target))))
        (RawCtxChainReceive.program (RawCtxChainReceive.normalResume pending
          (.hidden, RawCtxFreshChainCut.concreteMaterial entry.material))) := by
  rw [decoded_response]
  have resumed := RawCtxChainReceive.normalResume_native (interpret (RawCtxFreshChainCut.concreteChain target))
    (interpret (RawCtxFreshChainCut.concreteChain target)) pending
    (.hidden, RawCtxFreshChainCut.concreteMaterial entry.material)
  simp only [interpret] at resumed
  rw [resumed, receive_program]

noncomputable def nativeSend {Auxiliary : Type}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (entry : Entry) (target : RootOutput) :
    QueryImpl (RawCtxInterpretedSend.SendSpec RatchetMaterial
      RawCtxSourceSend.SealContext RawCtxSourceSend.Encrypted)
      (StateT (RawCtxSharedPrimitive.SharedState Auxiliary) ProbComp)
  | .inl request => pure (RawCtxInterpretedReceive.decodeResponse (response prior entry target request))
  | .inr pending => RawCtxSourceChainHandles.sendNative source writer
      (.inr (RawCtxInterpretedSend.nativeSeal pending))

noncomputable def labelSend {Auxiliary : Type}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (entry : Entry) (challenge : RatchetKdfResponse) :
    QueryImpl (RawCtxChainSend.SendSpec Slot Slot RatchetMaterial
      RawCtxSourceSend.SealContext RawCtxSourceSend.Encrypted)
      (StateT (RawCtxSharedPrimitive.SharedState Auxiliary) ProbComp)
  | .inl request => pure (RawCtxSelectedParentTable.step prior entry challenge request)
  | .inr pending => sendLabels source writer challenge (.inr pending)

/-- Both source directions use the same retained predecessor response and shared primitive state. -/
theorem send_kdf {Auxiliary : Type}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (entry : Entry) (target : RootOutput) (request : Slot) :
    nativeSend (Auxiliary := Auxiliary) source writer prior entry target
      (.inl (RawCtxChainSend.nativeRequest (interpret (RawCtxFreshChainCut.concreteChain target) request))) =
      (fun reply => (interpret (RawCtxFreshChainCut.concreteChain target) reply.1, reply.2)) <$>
        labelSend source writer prior entry
          (response prior entry target (RawCtxChainSend.nativeRequest (RawCtxFreshChainCut.concreteChain target)))
          (.inl request) :=
  receive_kdf source writer prior entry target request

/-- The seal callback omits only chain fields that its actual getters do not read and retains the complete optional primitive computation. -/
theorem send_seal {Auxiliary : Type}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (entry : Entry) (target : RootOutput) (challenge : RatchetKdfResponse)
    (pending : RawCtxChainSend.Seal Slot Slot RatchetMaterial RawCtxSourceSend.SealContext) :
    nativeSend (Auxiliary := Auxiliary) source writer prior entry target
      (.inr (RawCtxChainSend.nativeSeal (interpret (RawCtxFreshChainCut.concreteChain target))
        (interpret (RawCtxFreshChainCut.concreteChain target)) pending)) =
      labelSend source writer prior entry challenge (.inr pending) :=
  RawCtxSelectedChain.send_seal source writer (RawCtxFreshChainCut.concreteChain target) challenge pending

/-- Original send admission, the one KDF callback and failed-seal advancement retain the complete same-table source program. -/
theorem send_program {Auxiliary : Type}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (entry : Entry) (target : RootOutput)
    (start : RawCtxChainSend.Start Slot Slot RatchetMaterial RawCtxSourceSend.SealContext) :
    simulateQ (nativeSend (Auxiliary := Auxiliary) source writer prior entry target)
      (RawCtxInterpretedSend.program (RawCtxChainSend.nativeStart
        (interpret (RawCtxFreshChainCut.concreteChain target))
        (interpret (RawCtxFreshChainCut.concreteChain target)) start)) =
      (fun result => (mapChains (interpret (RawCtxFreshChainCut.concreteChain target))
        (interpret (RawCtxFreshChainCut.concreteChain target)) result.1, result.2)) <$>
      simulateQ (labelSend source writer prior entry
        (response prior entry target (RawCtxChainSend.nativeRequest (RawCtxFreshChainCut.concreteChain target))))
        (RawCtxChainSend.program start) :=
  RawCtxChainSend.program_native
    (interpret (RawCtxFreshChainCut.concreteChain target))
    (interpret (RawCtxFreshChainCut.concreteChain target))
    (labelSend source writer prior entry
      (response prior entry target (RawCtxChainSend.nativeRequest (RawCtxFreshChainCut.concreteChain target))))
    (nativeSend source writer prior entry target) (send_kdf source writer prior entry target)
    (send_seal source writer prior entry target _) start

/-- The actual extracted send resumption installs the predecessor's same second32 chain and first32/final12 material before sealing. -/
theorem send_ready (entry : Entry) (target : RootOutput)
    (pending : RawCtxChainSend.Kdf Slot Slot RatchetMaterial RawCtxSourceSend.SealContext) :
    RawCtxSourceSend.resumeSend
      (RawCtxInterpretedSend.nativeKdf (RawCtxChainSend.nativeKdf
        (interpret (RawCtxFreshChainCut.concreteChain target))
        (interpret (RawCtxFreshChainCut.concreteChain target)) pending))
      (RawCtxKdfRequestTable.fullResponse (realize entry target)) =
      RawCtxInterpretedSend.nativeSeal (RawCtxChainSend.nativeSeal
        (interpret (RawCtxFreshChainCut.concreteChain target))
        (interpret (RawCtxFreshChainCut.concreteChain target))
        (RawCtxChainSend.ready pending (.hidden, RawCtxFreshChainCut.concreteMaterial entry.material))) := by
  rw [RawCtxInterpretedSend.ready_native, decoded_response]
  rfl

/-- After the actual KDF response, the same source seal and full advanced state survive both success and failure; the label continuation cannot inspect the next chain. -/
theorem send_cut {Auxiliary : Type}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (entry : Entry) (target : RootOutput) (challenge : RatchetKdfResponse)
    (pending : RawCtxChainSend.Kdf Slot Slot RatchetMaterial RawCtxSourceSend.SealContext) :
    (do
      let ready := RawCtxSourceSend.resumeSend
        (RawCtxInterpretedSend.nativeKdf (RawCtxChainSend.nativeKdf
          (interpret (RawCtxFreshChainCut.concreteChain target))
          (interpret (RawCtxFreshChainCut.concreteChain target)) pending))
        (RawCtxKdfRequestTable.fullResponse (realize entry target))
      let sealed ← RawCtxSourceChainHandles.sendNative (Auxiliary := Auxiliary) source writer (.inr ready)
      pure (ready.advanced, sealed)) =
      (fun result => (nativeKernel (RawCtxFreshChainCut.concreteChain target) result.1, result.2)) <$>
      (do
        let ready := RawCtxChainSend.ready pending (.hidden, RawCtxFreshChainCut.concreteMaterial entry.material)
        let sealed ← labelSend source writer prior entry challenge (.inr ready)
        pure (ready.advanced, sealed)) := by
  rw [send_ready]
  simp only [bind_pure_comp, Functor.map_map]
  rfl

/-- Exact whole-program interpretation preserves every selective underlying query bound; evaluated distribution equality is not used to infer work. -/
theorem receive_query_bounds {Auxiliary : Type}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (entry : Entry) (target : RootOutput)
    (effect : RawCtxChainReceive.Effect Slot Slot RatchetMaterial RawCtxWholeOwner.OpenContext)
    (state : RawCtxSharedPrimitive.SharedState Auxiliary)
    (predicate : unifSpec.Domain → Prop) [DecidablePred predicate] (budget : Nat) :
    ((simulateQ (nativeReceive source writer prior entry target)
      (RawCtxInterpretedReceive.program (RawCtxChainReceive.nativeEffect
        (interpret (RawCtxFreshChainCut.concreteChain target))
        (interpret (RawCtxFreshChainCut.concreteChain target)) effect))).run state).IsQueryBoundP predicate budget ↔
    ((simulateQ (labelReceive source writer prior entry
      (response prior entry target (RawCtxChainSend.nativeRequest (RawCtxFreshChainCut.concreteChain target))))
      (RawCtxChainReceive.program effect)).run state).IsQueryBoundP predicate budget := by
  rw [receive_program, StateT.run_map, isQueryBoundP_map_iff]

/-- The same exact selective-query preservation holds for the entire send program, including exhausted and failed-seal branches. -/
theorem send_query_bounds {Auxiliary : Type}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (entry : Entry) (target : RootOutput)
    (start : RawCtxChainSend.Start Slot Slot RatchetMaterial RawCtxSourceSend.SealContext)
    (state : RawCtxSharedPrimitive.SharedState Auxiliary)
    (predicate : unifSpec.Domain → Prop) [DecidablePred predicate] (budget : Nat) :
    ((simulateQ (nativeSend source writer prior entry target)
      (RawCtxInterpretedSend.program (RawCtxChainSend.nativeStart
        (interpret (RawCtxFreshChainCut.concreteChain target))
        (interpret (RawCtxFreshChainCut.concreteChain target)) start))).run state).IsQueryBoundP predicate budget ↔
    ((simulateQ (labelSend source writer prior entry
      (response prior entry target (RawCtxChainSend.nativeRequest (RawCtxFreshChainCut.concreteChain target))))
      (RawCtxChainSend.program start)).run state).IsQueryBoundP predicate budget := by
  rw [send_program, StateT.run_map, isQueryBoundP_map_iff]

/-- A retained original predecessor specializes every typed KDF response back to the actual fixed source; the entry carries no new primitive correctness assumption. -/
theorem response_source (source : FixedHkdfSha512NoSaltSource) (address : JointKdfAddress)
    (request : SymmetricRatchetKdfRequest) :
    response (productionStream source.crypto) (fromOutput address (productionStream source.crypto address))
      (PqxdhOrderedChainHybrids.nextChain (productionStream source.crypto address)) request =
      RawCtxSourceHkdf.response source.crypto request := by
  rw [response, lookup_source, RawCtxKdfRequestTable.fullResponse_source]

end BeaconcryptCore.Computational.RawCtxSelectedParentSource

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedParentSource.receive_kdf' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedParentSource.receive_kdf

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedParentSource.receive_open' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedParentSource.receive_open

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedParentSource.receive_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedParentSource.receive_program

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedParentSource.receive_cut' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedParentSource.receive_cut

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedParentSource.send_kdf' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedParentSource.send_kdf

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedParentSource.send_seal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedParentSource.send_seal

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedParentSource.send_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedParentSource.send_program

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedParentSource.send_ready' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedParentSource.send_ready

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedParentSource.send_cut' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedParentSource.send_cut

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedParentSource.receive_query_bounds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedParentSource.receive_query_bounds

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedParentSource.send_query_bounds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedParentSource.send_query_bounds

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedParentSource.response_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedParentSource.response_source
