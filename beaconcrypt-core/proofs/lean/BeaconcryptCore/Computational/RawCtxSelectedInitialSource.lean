import BeaconcryptCore.Computational.RawCtxSelectedInitialTable

/-!
The original receive and send programs run over one retained initial first32 entry and the entire prior lookup. Both current chain fields, staged material, context and complete shared primitive effects are preserved. The labeled KDF handler explicitly retains a target parameter: a known callback at the initializer root reconstructs the target as first32 material. The separate InitialTable.initializerQuery/step_before interface identifies that case; these exact source equations do not pretend it is target-free. Actual initial64 uses the shared prefix and does not manufacture an initialization nonce.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.refined ratchet.concrete
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RawCtxSelectedInitialSource
open RawCtxSelectedChain RawCtxChainInterpretation RawCtxSelectedInitialEntry RawCtxSelectedInitialTable
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
    (prior : Prior) (entry : Entry) (target : RootOutput) (challenge : RatchetKdfResponse) :
    QueryImpl (RawCtxChainReceive.ReceiveSpec Slot Slot RatchetMaterial
      RawCtxWholeOwner.OpenContext RawCtxWholeOwner.Decrypted)
      (StateT (RawCtxSharedPrimitive.SharedState Auxiliary) ProbComp)
  | .inl request => pure (RawCtxSelectedInitialTable.step prior entry target challenge request)
  | .inr pending => receiveLabels source writer challenge (.inr pending)

/-- The native request and selected initializer step share the complete response before the same full-state receive continuation. -/
theorem receive_kdf {Auxiliary : Type}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (entry : Entry) (target : RootOutput) (request : Slot) :
    nativeReceive (Auxiliary := Auxiliary) source writer prior entry target
      (.inl (RawCtxChainSend.nativeRequest (interpret (RawCtxFreshChainCut.concreteChain target) request))) =
      (fun reply => (interpret (RawCtxFreshChainCut.concreteChain target) reply.1, reply.2)) <$>
        labelReceive source writer prior entry target
          (response prior entry target (RawCtxChainSend.nativeRequest (RawCtxFreshChainCut.concreteChain target)))
          (.inl request) := by
  simp only [nativeReceive, labelReceive, map_pure]
  exact congrArg pure (RawCtxSelectedInitialTable.step_table prior entry target request)

/-- The opening callback reads the same material, sequence and context; retaining the initializer does not alter any optional primitive effect. -/
theorem receive_open {Auxiliary : Type}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (entry : Entry) (target : RootOutput) (challenge : RatchetKdfResponse)
    (pending : RawCtxInterpretedOpening.Opening Slot Slot RatchetMaterial RawCtxWholeOwner.OpenContext) :
    nativeReceive (Auxiliary := Auxiliary) source writer prior entry target
      (.inr (mapOpeningChains (interpret (RawCtxFreshChainCut.concreteChain target))
        (interpret (RawCtxFreshChainCut.concreteChain target)) pending)) =
      labelReceive source writer prior entry target challenge (.inr pending) :=
  RawCtxSelectedChain.receive_open source writer (RawCtxFreshChainCut.concreteChain target) challenge pending

/-- Every remaining source skip/open continuation retains the initializer entry and complete callback state through original rejection and rollback. -/
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
      simulateQ (labelReceive source writer prior entry target
        (response prior entry target (RawCtxChainSend.nativeRequest (RawCtxFreshChainCut.concreteChain target))))
        (RawCtxChainReceive.program effect) :=
  RawCtxChainReceive.program_native
    (interpret (RawCtxFreshChainCut.concreteChain target))
    (interpret (RawCtxFreshChainCut.concreteChain target))
    (labelReceive source writer prior entry target
      (response prior entry target (RawCtxChainSend.nativeRequest (RawCtxFreshChainCut.concreteChain target))))
    (nativeReceive source writer prior entry target) (receive_kdf source writer prior entry target)
    (receive_open source writer prior entry target _) effect

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
    (prior : Prior) (entry : Entry) (target : RootOutput) (challenge : RatchetKdfResponse) :
    QueryImpl (RawCtxChainSend.SendSpec Slot Slot RatchetMaterial
      RawCtxSourceSend.SealContext RawCtxSourceSend.Encrypted)
      (StateT (RawCtxSharedPrimitive.SharedState Auxiliary) ProbComp)
  | .inl request => pure (RawCtxSelectedInitialTable.step prior entry target challenge request)
  | .inr pending => sendLabels source writer challenge (.inr pending)

/-- Both source directions use the same retained initializer response and shared primitive state. -/
theorem send_kdf {Auxiliary : Type}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (entry : Entry) (target : RootOutput) (request : Slot) :
    nativeSend (Auxiliary := Auxiliary) source writer prior entry target
      (.inl (RawCtxChainSend.nativeRequest (interpret (RawCtxFreshChainCut.concreteChain target) request))) =
      (fun reply => (interpret (RawCtxFreshChainCut.concreteChain target) reply.1, reply.2)) <$>
        labelSend source writer prior entry target
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
      labelSend source writer prior entry target challenge (.inr pending) :=
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
      simulateQ (labelSend source writer prior entry target
        (response prior entry target (RawCtxChainSend.nativeRequest (RawCtxFreshChainCut.concreteChain target))))
        (RawCtxChainSend.program start) :=
  RawCtxChainSend.program_native
    (interpret (RawCtxFreshChainCut.concreteChain target))
    (interpret (RawCtxFreshChainCut.concreteChain target))
    (labelSend source writer prior entry target
      (response prior entry target (RawCtxChainSend.nativeRequest (RawCtxFreshChainCut.concreteChain target))))
    (nativeSend source writer prior entry target) (send_kdf source writer prior entry target)
    (send_seal source writer prior entry target _) start

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
    ((simulateQ (labelReceive source writer prior entry target
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
    ((simulateQ (labelSend source writer prior entry target
      (response prior entry target (RawCtxChainSend.nativeRequest (RawCtxFreshChainCut.concreteChain target))))
      (RawCtxChainSend.program start)).run state).IsQueryBoundP predicate budget := by
  rw [send_program, StateT.run_map, isQueryBoundP_map_iff]

/-- A retained original initializer specializes every typed KDF response back to the actual fixed source; the entry carries no new primitive correctness assumption. -/
theorem response_source (source : FixedHkdfSha512NoSaltSource) (address : JointKdfAddress)
    (request : SymmetricRatchetKdfRequest) :
    response (productionStream source.crypto) (fromOutput address (productionStream source.crypto address))
      (JointKdfProjection.first32.project (productionStream source.crypto address)) request =
      RawCtxSourceHkdf.response source.crypto request := by
  rw [response, lookup_source, RawCtxKdfRequestTable.fullResponse_source]

end BeaconcryptCore.Computational.RawCtxSelectedInitialSource

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedInitialSource.receive_kdf' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedInitialSource.receive_kdf

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedInitialSource.receive_open' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedInitialSource.receive_open

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedInitialSource.receive_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedInitialSource.receive_program

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedInitialSource.send_kdf' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedInitialSource.send_kdf

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedInitialSource.send_seal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedInitialSource.send_seal

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedInitialSource.send_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedInitialSource.send_program

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedInitialSource.receive_query_bounds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedInitialSource.receive_query_bounds

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedInitialSource.send_query_bounds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedInitialSource.send_query_bounds

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedInitialSource.response_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedInitialSource.response_source
