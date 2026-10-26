import BeaconcryptCore.Computational.RawCtxSelectedInputCandidates

/-!
Pure candidate instrumentation executes the original source callback before recording available input bytes. Erasing only this log preserves the entire original adaptive result and primitive state. Hidden requests contribute no available bytes; known requests retain exact source bytes, every repetition and every failed attempt. Actual send/receive drivers give one/51 bounds under all supported primitive replies.

The log and all owner state remain private reduction context. These per-driver laws do not yet supply the complete mixed public/reveal trace, the reached native uniform cut, or consistent random-table alias reconciliation. Live exposure transport remains explicit; snapshots, persistence and restoration are excluded.
-/

open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RawCtxSelectedQueryTrace
open PqxdhSecretInputKdf

/-- Record only available source input candidates after the original callback, preserving its full primitive state. -/
def recorded {ι State : Type} {spec : OracleSpec ι}
    (handler : QueryImpl spec (StateT State ProbComp)) (record : spec.Domain → List RootOutput) :
    QueryImpl spec (StateT (State × List RootOutput) ProbComp) := fun query state => do
  let result ← (handler query).run state.1
  pure (result.1, (result.2, state.2 ++ record query))

/-- A recorded query retains the original optional reply and entire primitive poststate. -/
theorem query_erase {ι State : Type} {spec : OracleSpec ι}
    (handler : QueryImpl spec (StateT State ProbComp)) (record : spec.Domain → List RootOutput)
    (query : spec.Domain) (state : State × List RootOutput) :
    (Prod.map id Prod.fst) <$> (recorded handler record query).run state =
      (handler query).run state.1 := by
  simp [recorded, StateT.run]

/-- Erasing only the input log preserves the complete arbitrary adaptive execution. -/
theorem complete {ι State Result : Type} {spec : OracleSpec ι}
    (handler : QueryImpl spec (StateT State ProbComp)) (record : spec.Domain → List RootOutput)
    (client : OracleComp spec Result) (state : State × List RootOutput) :
    (Prod.map id Prod.fst) <$> (simulateQ (recorded handler record) client).run state =
      (simulateQ handler client).run state.1 := by
  exact map_run_simulateQ_eq_of_query_map_eq
    (recorded handler record) handler Prod.fst (query_erase handler record) client state

/-- Every supported adaptive run retains its original candidate prefix and charges all repeated source attempts. -/
theorem length_bound {ι State Result : Type} {spec : OracleSpec ι}
    (handler : QueryImpl spec (StateT State ProbComp)) (record : spec.Domain → List RootOutput)
    (predicate : spec.Domain → Prop) [DecidablePred predicate]
    (stepBound : ∀ query, (record query).length ≤ if predicate query then 1 else 0)
    (client : OracleComp spec Result) (budget : Nat) (bounded : client.IsQueryBoundP predicate budget)
    (state : State × List RootOutput) (result : Result × (State × List RootOutput))
    (supported : result ∈ support ((simulateQ (recorded handler record) client).run state)) :
    result.2.2.length ≤ state.2.length + budget := by
  induction client using OracleComp.inductionOn generalizing budget state result with
  | pure value =>
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
    subst result
    exact Nat.le_add_right _ _
  | query_bind query next ih =>
    rw [isQueryBoundP_query_bind_iff] at bounded
    simp only [simulateQ_bind, simulateQ_spec_query] at supported
    change result ∈ support (((recorded handler record query).run state) >>= fun reply =>
      (simulateQ (recorded handler record) (next reply.1)).run reply.2) at supported
    simp only [recorded, StateT.run, bind_assoc, pure_bind] at supported
    rw [mem_support_bind_iff] at supported
    obtain ⟨reply, _, tailSupport⟩ := supported
    have tail := ih reply.1 _ (bounded.2 reply.1) _ result tailSupport
    have head := stepBound query
    simp only [List.length_append] at tail
    have available := bounded.1
    by_cases h : predicate query <;> simp only [h, ite_true, ite_false, not_true_eq_false, false_or] at head tail available <;> omega

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.refined ratchet.concrete
open BeaconcryptCore.Refinement.ProtocolComposition BeaconcryptCore.Refinement.RepresentationBridge
open RawCtxSelectedChain PqxdhRefinement

/-- The original available input bytes; this conversion neither labels nor changes their values. -/
def rootVector (chain : RatchetChain) : RootOutput :=
  ⟨absBytes chain.bytes, by simpa [absBytes] using chain.bytes.property⟩

/-- The available-input view preserves the exact sampled chain bytes. -/
theorem rootVector_concrete (value : RootOutput) :
    rootVector (RawCtxFreshChainCut.concreteChain value) = value := by
  apply Subtype.ext
  simp [rootVector, RawCtxFreshChainCut.concreteChain, absBytes, List.map_map,
    Function.comp_def, List.Vector.toList]

/-- Hidden requests contain no available input; every known input is recorded, including repeats. -/
def inputs {Other : Type} : Slot ⊕ Other → List RootOutput
  | .inl (.known chain) => [rootVector chain]
  | _ => []

/-- Each original KDF request contributes at most one input and all other callbacks contribute none. -/
theorem inputs_bound {Other : Type} (query : Slot ⊕ Other) :
    (inputs query).length ≤ if query.isLeft = true then 1 else 0 := by
  cases query with
  | inl slot => cases slot <;> simp [inputs]
  | inr other => simp [inputs]

noncomputable def receiveCalls {Auxiliary : Type}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (challenge : RatchetKdfResponse) :=
  recorded (receiveLabels (Auxiliary := Auxiliary) source writer challenge) inputs

noncomputable def sendCalls {Auxiliary : Type}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (challenge : RatchetKdfResponse) :=
  recorded (sendLabels (Auxiliary := Auxiliary) source writer challenge) inputs

/-- Tracing the actual selected receive erases to its exact full result and primitive state. -/
theorem receive_erase {Auxiliary : Type}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (challenge : RatchetKdfResponse) (entry : Kernel) (target : Std.U64) (context : RawCtxWholeOwner.OpenContext)
    (state : RawCtxSharedPrimitive.SharedState Auxiliary × List RootOutput) :
    (Prod.map id Prod.fst) <$>
      (simulateQ (receiveCalls source writer challenge) (RawCtxChainReceive.execute entry target context)).run state =
      (simulateQ (receiveLabels source writer challenge) (RawCtxChainReceive.execute entry target context)).run state.1 :=
  complete _ _ _ _

/-- Tracing the actual selected send retains failure advancement and the complete primitive poststate. -/
theorem send_erase {Auxiliary : Type}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (challenge : RatchetKdfResponse) (entry : Kernel) (context : RawCtxSourceSend.SealContext)
    (state : RawCtxSharedPrimitive.SharedState Auxiliary × List RootOutput) :
    (Prod.map id Prod.fst) <$>
      (simulateQ (sendCalls source writer challenge) (RawCtxChainSend.execute entry context)).run state =
      (simulateQ (sendLabels source writer challenge) (RawCtxChainSend.execute entry context)).run state.1 :=
  complete _ _ _ _

/-- Every supported receive adds at most 51 actual known KDF inputs, retaining repeated and rejected attempts. -/
theorem receive_length {Auxiliary : Type}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (challenge : RatchetKdfResponse) (entry : Kernel) (target : Std.U64) (context : RawCtxWholeOwner.OpenContext)
    (state : RawCtxSharedPrimitive.SharedState Auxiliary × List RootOutput)
    (result : (Kernel × core.option.Option RawCtxWholeOwner.Decrypted) ×
      (RawCtxSharedPrimitive.SharedState Auxiliary × List RootOutput))
    (supported : result ∈ support
      ((simulateQ (receiveCalls source writer challenge) (RawCtxChainReceive.execute entry target context)).run state)) :
    result.2.2.length ≤ state.2.length + 51 :=
  length_bound _ inputs (fun query => query.isLeft = true) inputs_bound _ _
    (RawCtxChainReceiveBounds.receive_bound entry target context) state result supported

/-- Every supported send adds at most one actual known input, including an unsuccessful seal. -/
theorem send_length {Auxiliary : Type}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (challenge : RatchetKdfResponse) (entry : Kernel) (context : RawCtxSourceSend.SealContext)
    (state : RawCtxSharedPrimitive.SharedState Auxiliary × List RootOutput)
    (result : (Kernel × Option RawCtxSourceSend.Encrypted) ×
      (RawCtxSharedPrimitive.SharedState Auxiliary × List RootOutput))
    (supported : result ∈ support
      ((simulateQ (sendCalls source writer challenge) (RawCtxChainSend.execute entry context)).run state)) :
    result.2.2.length ≤ state.2.length + 1 :=
  length_bound _ inputs (fun query => query.isLeft = true) inputs_bound _ _
    (RawCtxChainSend.program_kdf_bound _) state result supported

end BeaconcryptCore.Computational.RawCtxSelectedQueryTrace

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedQueryTrace.query_erase' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedQueryTrace.query_erase

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedQueryTrace.complete' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedQueryTrace.complete

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedQueryTrace.length_bound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedQueryTrace.length_bound

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedQueryTrace.rootVector_concrete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedQueryTrace.rootVector_concrete

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedQueryTrace.inputs_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedQueryTrace.inputs_bound

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedQueryTrace.receive_erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedQueryTrace.receive_erase

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedQueryTrace.send_erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedQueryTrace.send_erase

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedQueryTrace.receive_length' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedQueryTrace.receive_length

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedQueryTrace.send_length' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedQueryTrace.send_length
