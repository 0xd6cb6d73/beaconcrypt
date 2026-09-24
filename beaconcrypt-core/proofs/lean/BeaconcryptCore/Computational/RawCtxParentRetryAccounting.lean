import BeaconcryptCore.Computational.PqxdhInitialFutureInputCandidates

/-!
The concrete private send-step audit records a known chain before routing its bytes. A selected-input hit is therefore in the existing candidate ledger; an exact retained predecessor retry is recorded as that predecessor, while its returned chain is hidden. This distinction is preserved in the complete primitive poststate and disclosure flag, and no assumption that retries guess the child is made. The enclosing source ancestry selection remains separate.
-/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RawCtxParentRetryAccounting
open PqxdhSecretInputKdf PqxdhFullSecretInputKdf PqxdhJointKdfGame
open PqxdhInitialBeaconAmbient PqxdhInitialParentObserverCompiler PqxdhInitialParentObserver
open RawCtxSelectedChain RawCtxSelectedParentTable RawCtxSelectedParentEntry
variable {ι I D K X Response Shared A N C Result : Type} {extra : OracleSpec ι} {S B : Nat}
variable (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
  (prior : RawCtxSelectedParentTable.Prior) (entry : RawCtxSelectedParentEntry.Entry)
  (output : FullOutput)
  (pre : QueryImpl (PqxdhBeaconPhase2Shared.Spec I D K X Response Shared) (Ambient A N C))
  (application : Response → Ambient A N C (Option Pqxdh.Bytes))
  (initial : PqxdhBeaconPhase2Shared.Secrets Shared → Ambient A N C InitialReply)
  (selector : QueryImpl extra (Ambient A N C))
  (aux : QueryImpl PqxdhServerRegistrationPublication.AuxSpec (Ambient A N C))


noncomputable def sendRequest (chain : Slot) : (Spec extra I D K X Response Shared).Domain :=
  .inl (.inl (.inr (.inl (.inl chain))))

private theorem state_pure {State Value : Type} (value : Value) (state : State) :
    (pure value : StateT State ProbComp Value) state = pure (value, state) := rfl

/-- The concrete known-send request logs its actual chain bytes once, independent of the subsequent private alias-routing branch. -/
theorem known_logged (reader : RawCtxSelectedLiveTrace.Reader) (target : RootOutput)
    (chain : RatchetChain) (state : PqxdhInitialParentObserver.State A N C)
    (candidates : List RootOutput) (flag : Bool) :
    ((PqxdhInitialParentPrivateObserver.observed source writer prior entry output pre application initial selector aux reader target)
      (sendRequest (extra := extra) (I := I) (D := D) (K := K) (X := X) (Response := Response) (Shared := Shared) (.known chain))).run
        ((state, candidates), flag) =
      pure (RawCtxSelectedParentTable.step prior entry (RawCtxKdfRequestTable.fullResponse output)
        (if target = RawCtxSelectedQueryTrace.rootVector chain then .hidden else .known chain),
        ((state, candidates ++ [RawCtxSelectedQueryTrace.rootVector chain]), flag)) := by
  simp only [PqxdhInitialParentPrivateObserver.observed, RawCtxFlaggedQueryTrace.trace,
    StateT.run, sendRequest, PqxdhInitialParentPrivateObserver.old_source, RawCtxSelectedParentPrivate.known_send]
  simp [PqxdhInitialParentObserver.flatten, PqxdhInitialBeaconAmbient.lift,
    PqxdhInitialParentObserver.inputs, PqxdhInitialParentObserver.direct,
    RawCtxSelectedLiveCompiler.inputs, RawCtxSelectedAliasPrimitives.inputs,
    RawCtxSelectedQueryTrace.inputs, RawCtxSelectedParentReadMask.direct, state_pure]

/-- An exact retained predecessor retry regenerates the hidden child, and records the predecessor rather than pretending to record an independent child-input guess. -/
theorem parent_retry_logged (reader : RawCtxSelectedLiveTrace.Reader) (target : RootOutput)
    (chain : RatchetChain)
    (parent : RawCtxKdfRequestTable.address (RawCtxChainSend.nativeRequest chain) = entry.address)
    (different : target ≠ RawCtxSelectedQueryTrace.rootVector chain)
    (state : PqxdhInitialParentObserver.State A N C) (candidates : List RootOutput) (flag : Bool) :
    ((PqxdhInitialParentPrivateObserver.observed source writer prior entry output pre application initial selector aux reader target)
      (sendRequest (extra := extra) (I := I) (D := D) (K := K) (X := X) (Response := Response) (Shared := Shared) (.known chain))).run
        ((state, candidates), flag) =
      pure ((.hidden, RawCtxFreshChainCut.concreteMaterial entry.material),
        ((state, candidates ++ [RawCtxSelectedQueryTrace.rootVector chain]), flag)) := by
  rw [known_logged]
  simp only [if_neg different, RawCtxSelectedParentTable.step, if_pos parent]

/-- The concrete hidden send request reuses its one full child response without inventing a known-input candidate. -/
theorem hidden_logged (reader : RawCtxSelectedLiveTrace.Reader) (target : RootOutput)
    (state : PqxdhInitialParentObserver.State A N C)
    (candidates : List RootOutput) (flag : Bool) :
    ((PqxdhInitialParentPrivateObserver.observed source writer prior entry output pre application initial selector aux reader target)
      (sendRequest (extra := extra) (I := I) (D := D) (K := K) (X := X) (Response := Response) (Shared := Shared) (.hidden))).run
        ((state, candidates), flag) =
      pure (RawCtxSelectedParentTable.step prior entry (RawCtxKdfRequestTable.fullResponse output)
        .hidden,
        ((state, candidates), flag)) := by
  simp only [PqxdhInitialParentPrivateObserver.observed, RawCtxFlaggedQueryTrace.trace,
    StateT.run, sendRequest, PqxdhInitialParentPrivateObserver.old_source, RawCtxSelectedParentPrivate.hidden_send]
  simp [PqxdhInitialParentObserver.flatten, PqxdhInitialBeaconAmbient.lift,
    PqxdhInitialParentObserver.inputs, PqxdhInitialParentObserver.direct,
    RawCtxSelectedLiveCompiler.inputs, RawCtxSelectedAliasPrimitives.inputs,
    RawCtxSelectedQueryTrace.inputs, RawCtxSelectedParentReadMask.direct, state_pure]


/-- The original full adaptive primitive/source continuation retains every already recorded candidate, including all reads and all rejected callbacks. -/
theorem retained (reader : RawCtxSelectedLiveTrace.Reader) (target : RootOutput)
    (client : OracleComp (Spec extra I D K X Response Shared) Result)
    (state : (PqxdhInitialParentObserver.State A N C × List RootOutput) × Bool)
    (result : Result × ((PqxdhInitialParentObserver.State A N C × List RootOutput) × Bool))
    (supported : result ∈ support ((simulateQ
      (PqxdhInitialParentPrivateObserver.observed source writer prior entry output pre application initial selector aux reader target)
      client).run state)) : state.1.2 ⊆ result.2.1.2 := by
  induction client using OracleComp.inductionOn generalizing state result with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
      subst result
      exact List.Subset.refl _
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query] at supported
      change result ∈ support (((PqxdhInitialParentPrivateObserver.observed source writer prior entry output
        pre application initial selector aux reader target query).run state) >>= fun reply =>
        (simulateQ (PqxdhInitialParentPrivateObserver.observed source writer prior entry output
          pre application initial selector aux reader target) (next reply.1)).run reply.2) at supported
      simp only [PqxdhInitialParentPrivateObserver.observed, RawCtxFlaggedQueryTrace.trace,
        StateT.run, bind_assoc, pure_bind] at supported
      rw [mem_support_bind_iff] at supported
      obtain ⟨reply, _, tailSupport⟩ := supported
      exact List.Subset.trans (List.subset_append_left _ _) (ih reply.1 _ result tailSupport)

/-- The actual known-send request remains in the candidate list after its complete original adaptive continuation, regardless of all later replies, disclosures or failures. -/
theorem known_followed (reader : RawCtxSelectedLiveTrace.Reader) (target : RootOutput)
    (chain : RatchetChain)
    (next : Slot × RatchetMaterial → OracleComp (Spec extra I D K X Response Shared) Result)
    (state : PqxdhInitialParentObserver.State A N C) (candidates : List RootOutput) (flag : Bool)
    (result : Result × ((PqxdhInitialParentObserver.State A N C × List RootOutput) × Bool))
    (supported : result ∈ support ((simulateQ
      (PqxdhInitialParentPrivateObserver.observed source writer prior entry output pre application initial selector aux reader target)
      (do let reply ← (Spec extra I D K X Response Shared).query (sendRequest (.known chain)); next reply)).run
        ((state, candidates), flag))) :
    RawCtxSelectedQueryTrace.rootVector chain ∈ result.2.1.2 := by
  simp only [simulateQ_bind, simulateQ_spec_query] at supported
  change result ∈ support (((PqxdhInitialParentPrivateObserver.observed source writer prior entry output
    pre application initial selector aux reader target (sendRequest (.known chain))).run ((state, candidates), flag)) >>= fun reply =>
    (simulateQ (PqxdhInitialParentPrivateObserver.observed source writer prior entry output
      pre application initial selector aux reader target) (next reply.1)).run reply.2) at supported
  rw [known_logged] at supported
  exact retained source writer prior entry output pre application initial selector aux reader target _ _ result supported (by simp)

/-- A private derivation creates a hidden next-chain slot only at the exact retained predecessor address. Equal-byte aliases of a known input are not discarded. -/
theorem hidden_next (request : Slot) :
    (RawCtxSelectedParentTable.step prior entry (RawCtxKdfRequestTable.fullResponse output) request).1 = .hidden ↔
      ∃ chain, request = .known chain ∧
        RawCtxKdfRequestTable.address (RawCtxChainSend.nativeRequest chain) = entry.address := by
  cases request with
  | hidden => simp [RawCtxSelectedParentTable.step]
  | known chain =>
      by_cases parent : RawCtxKdfRequestTable.address (RawCtxChainSend.nativeRequest chain) = entry.address
      all_goals simp [RawCtxSelectedParentTable.step, parent]

set_option backward.isDefEq.respectTransparency false in
/-- The actual source audit can regenerate a hidden child only by a recorded known predecessor retry, with the parent/child input alias branch kept separate. -/
theorem source_hidden (reader : RawCtxSelectedLiveTrace.Reader) (target : RootOutput)
    (request : Slot) (state : PqxdhInitialParentObserver.State A N C) (candidates : List RootOutput) (flag : Bool)
    (result : (Slot × RatchetMaterial) × ((PqxdhInitialParentObserver.State A N C × List RootOutput) × Bool))
    (supported : result ∈ support ((PqxdhInitialParentPrivateObserver.observed source writer prior entry output
      pre application initial selector aux reader target (sendRequest request)).run ((state, candidates), flag)))
    (hidden : result.1.1 = .hidden) :
    ∃ chain, request = .known chain ∧
      RawCtxKdfRequestTable.address (RawCtxChainSend.nativeRequest chain) = entry.address ∧
      target ≠ RawCtxSelectedQueryTrace.rootVector chain ∧
      result.2 = ((state, candidates ++ [RawCtxSelectedQueryTrace.rootVector chain]), flag) := by
  cases request with
  | hidden =>
      rw [hidden_logged, mem_support_pure_iff] at supported
      subst result
      simp [RawCtxSelectedParentTable.step] at hidden
  | known chain =>
      rw [known_logged, mem_support_pure_iff] at supported
      subst result
      by_cases same : target = RawCtxSelectedQueryTrace.rootVector chain
      · simp [same, RawCtxSelectedParentTable.step] at hidden
      · have parent := (hidden_next prior entry output (.known chain)).mp (by simpa only [if_neg same] using hidden)
        obtain ⟨actual, equal, address⟩ := parent
        cases Slot.known.inj equal
        exact ⟨chain, rfl, address, same, rfl⟩

end BeaconcryptCore.Computational.RawCtxParentRetryAccounting

/-- info: 'BeaconcryptCore.Computational.RawCtxParentRetryAccounting.known_logged' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxParentRetryAccounting.known_logged

/-- info: 'BeaconcryptCore.Computational.RawCtxParentRetryAccounting.parent_retry_logged' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxParentRetryAccounting.parent_retry_logged

/-- info: 'BeaconcryptCore.Computational.RawCtxParentRetryAccounting.hidden_logged' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxParentRetryAccounting.hidden_logged

/-- info: 'BeaconcryptCore.Computational.RawCtxParentRetryAccounting.retained' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxParentRetryAccounting.retained

/-- info: 'BeaconcryptCore.Computational.RawCtxParentRetryAccounting.known_followed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxParentRetryAccounting.known_followed

/-- info: 'BeaconcryptCore.Computational.RawCtxParentRetryAccounting.hidden_next' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxParentRetryAccounting.hidden_next

/-- info: 'BeaconcryptCore.Computational.RawCtxParentRetryAccounting.source_hidden' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxParentRetryAccounting.source_hidden
