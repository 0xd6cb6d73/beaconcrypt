import BeaconcryptCore.Computational.PqxdhInitialDisclosureState
import BeaconcryptCore.Computational.RawCtxFamilyStoppedResources

/-!
The original saved builder/post cut resumes under the actual audited interpreter and derives its final disclosure invariant. Its seed history comes from the literal continuation that will run: the inner LIVE context for a record, or the saved frontend for a finish or first builder. The proof retains the full installation/publication trace, all ambient effects and every earlier candidate. It neither identifies unrelated histories nor assumes final freshness.
-/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.PqxdhInitialStoppedDisclosure
open PqxdhSecretInputKdf PqxdhInitialPendingPost RawCtxSelectedChain RawCtxFamilyFreshnessProxy
open PqxdhInitialDisclosureState PqxdhInitialOriginContext
variable {ι M P I D K X Response Shared Result Origin Z : Type} {extra : OracleSpec ι} {S B : Nat}

def history (context : Context extra M P I D K Result Origin S B) : RawCtxProtocolReveals.History S B :=
  match context.original with
  | .inl (.record _ _ _ inner) => RawCtxFamilyStoppedResources.history inner
  | .inl (.finish _ before _ _ _ _) => before.roles.2
  | .inr builder => builder.before.roles.2

/-- The stopped family continuation begins at its own actual saved history and retains the complete final disclosure invariant. -/
theorem family_stopped (target : RootOutput)
    (impl : QueryImpl (Base extra I D K X Response Shared S B) (StateT (State Z) ProbComp))
    (rules : Rules target impl) (prior : List RatchetChain)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (context : RawCtxSelectedFamilyContext.Context M P I D K Result S B) (material : PqxdhOrderedChainHybrids.Material)
    (state : State Z) (valid : Invariant target prior (RawCtxFamilyStoppedResources.history context) state)
    (result : (Result × RawCtxPendingFamilyLiveQueries.State Slot M P I D K S B) × State Z)
    (supported : result ∈ support ((simulateQ impl (simulateQ liveForward
      (RawCtxSelectedFamilyContext.stopped sender route decode context material))).run state)) :
    Invariant target prior result.1.2.2 result.2 := by
  cases context with
  | family request saved outside inner =>
    simp only [RawCtxSelectedFamilyContext.stopped, RawCtxPendingFamilyLiveTails.liftFamily,
      simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at supported
    obtain ⟨completed, reached, rest⟩ := supported
    have forwarding : liveForward ∘ₛ RawCtxPendingFamilyLiveQueries.primitiveForward =
        (primitiveForward : QueryImpl (RawCtxPendingOwnerQueries.Spec Slot) (OracleComp (Base extra I D K X Response Shared S B))) := by
      funext query
      exact simulateQ_spec_query _ _
    rw [← QueryImpl.simulateQ_compose liveForward RawCtxPendingFamilyLiveQueries.primitiveForward, forwarding] at reached
    have kept := quiet_program target impl rules _ (primitive_quiet _) state completed reached
    exact live_schedule_invariant target impl rules prior sender route decode (outside completed.1.1)
      (completed.1.2, RawCtxProtocolReveals.tick saved) completed.2
      (invariant_keep target prior saved state completed.2 valid kept) result rest

private theorem aux_quiet (query : PqxdhServerRegistrationPublication.AuxSpec.Domain) :
    (auxForward (extra := extra) (Chain := Slot) (I := I) (D := D) (K := K) (X := X)
      (Response := Response) (Shared := Shared) (S := S) (B := B) query).IsQueryBoundP (isRead (extra := extra)) 0 :=
  (isQueryBoundP_query_iff _ _ _).mpr (by simp only [isRead, IsEmpty.forall_iff])

/-- The original erase and optional serialization tail contains no adversary disclosure operation. -/
theorem after_send_quiet (candidate : pqxdh.ServerRegistrationCandidate) (authenticated : Pqxdh.Bytes)
    (metadata : P) (before : PqxdhInitialGenericPublication.State (KernelOf Slot) M P (List Pqxdh.Bytes))
    (sent : KernelOf Slot × Option RawCtxSourceSend.Encrypted) :
    (PqxdhInitialBuilderContext.afterSend
      (auxForward (extra := extra) (I := I) (D := D) (K := K) (X := X) (Response := Response) (Shared := Shared) (S := S) (B := B))
      candidate authenticated metadata before sent).IsQueryBoundP (isRead (extra := extra)) 0 := by
  unfold PqxdhInitialBuilderContext.afterSend
  apply isQueryBoundP_bind (n := 0) (m := 0) (aux_quiet _)
  intro _ _
  cases sent.2 with
  | none => trivial
  | some encrypted =>
    apply isQueryBoundP_bind (n := 0) (m := 0) (aux_quiet _)
    intro serialized _
    cases serialized <;> trivial

/-- The actual first-send completion preserves its saved history through erase, optional serialization and publication before the original outside post client. -/
theorem complete_invariant (target : RootOutput)
    (impl : QueryImpl (Base extra I D K X Response Shared S B) (StateT (State Z) ProbComp))
    (rules : Rules target impl) (prior : List RatchetChain)
    (mark : PqxdhBeaconPhase2Shared.Secrets Shared → Origin)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (index : Fin S) (before : Front Slot M P I D K S B) (trace : PqxdhInitialOriginPost.Trace Origin S B)
    (origin : Option Origin) (candidate : pqxdh.ServerRegistrationCandidate) (authenticated : Pqxdh.Bytes) (metadata : P)
    (outside : PqxdhInitialBuilderContext.BuildResult → OracleComp (PqxdhInitialPostContext.PostSpec extra S B) Result)
    (sent : KernelOf Slot × Option RawCtxSourceSend.Encrypted)
    (state : State Z) (valid : Invariant target prior before.roles.2 state)
    (result : (Result × (Front Slot M P I D K S B × PqxdhInitialOriginPost.Trace Origin S B)) × State Z)
    (supported : result ∈ support ((simulateQ impl (complete mark sender route decode index before trace origin
      candidate authenticated metadata outside sent)).run state)) :
    Invariant target prior result.1.2.1.roles.2 result.2 := by
  simp only [complete, simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at supported
  obtain ⟨completed, reached, rest⟩ := supported
  have kept := quiet_program target impl rules _ (after_send_quiet candidate authenticated metadata _ sent) state completed reached
  exact schedule_invariant target impl rules prior mark sender route decode _ _ completed.2
    (invariant_keep target prior before.roles.2 state completed.2 valid kept) result rest

/-- The literal material-only saved source cut derives its full final disclosure invariant in all record, finish and first-builder cases. -/
theorem stopped_invariant (target : RootOutput)
    (impl : QueryImpl (Base extra I D K X Response Shared S B) (StateT (State Z) ProbComp))
    (rules : Rules target impl) (prior : List RatchetChain)
    (mark : PqxdhBeaconPhase2Shared.Secrets Shared → Origin)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (context : Context extra M P I D K Result Origin S B) (material : PqxdhOrderedChainHybrids.Material)
    (state : State Z) (valid : Invariant target prior (history context) state)
    (result : (Result × (Front Slot M P I D K S B × PqxdhInitialOriginPost.Trace Origin S B)) × State Z)
    (supported : result ∈ support ((simulateQ impl (stopped mark sender route decode context material)).run state)) :
    Invariant target prior result.1.2.1.roles.2 result.2 := by
  rcases context with ⟨original, trace, origin⟩
  cases original with
  | inl original =>
    cases original with
    | record request before outside inner =>
      simp only [stopped, simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at supported
      obtain ⟨completed, reached, rest⟩ := supported
      exact schedule_invariant target impl rules prior mark sender route decode _ _ completed.2
        (family_stopped target impl rules prior sender route decode inner material state valid completed reached) result rest
    | finish index before control candidate outside inner =>
      simp only [stopped, simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at supported
      obtain ⟨completed, reached, rest⟩ := supported
      have kept := quiet_program target impl rules _ (primitive_quiet _) state completed reached
      exact schedule_invariant target impl rules prior mark sender route decode _ _ completed.2
        (invariant_keep target prior before.roles.2 state completed.2 valid kept) result rest
  | inr builder =>
    simp only [stopped, simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at supported
    obtain ⟨completed, reached, rest⟩ := supported
    have kept := rules.quiet _ (by simp only [isRead, not_false_eq_true]) state completed reached
    exact complete_invariant target impl rules prior mark sender route decode _ _ _ _ _ _ _ _ _ completed.2
      (invariant_keep target prior builder.before.roles.2 state completed.2 valid kept) result rest


def initial (disclosed : List RatchetChain) (context : Context extra M P I D K Result Origin S B)
    (state : Z) (candidates : List RootOutput) : State Z :=
  ((state, knownInputs disclosed (history context) ++ candidates), false)

/-- The original saved history seeds the exact source disclosure invariant before the omitted parent coordinate is sampled. -/
theorem initial_invariant (target : RootOutput) (disclosed : List RatchetChain)
    (context : Context extra M P I D K Result Origin S B) (state : Z) (candidates : List RootOutput) :
    Invariant target disclosed (history context) (initial disclosed context state candidates) := by
  constructor
  · intro impossible
    cases impossible
  · intro _
    exact List.subset_append_left _ _

section Actual
open PqxdhFullSecretInputKdf PqxdhJointKdfGame PqxdhInitialBeaconAmbient
variable {A N C ContextId : Type}
variable (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
  (prior : RawCtxSelectedParentTable.Prior) (entry : RawCtxSelectedParentEntry.Entry) (output : FullOutput)
  (pre : QueryImpl (PqxdhBeaconPhase2Shared.Spec I D K X Response Shared) (Ambient A N C))
  (application : Response → Ambient A N C (Option Pqxdh.Bytes))
  (initializer : PqxdhBeaconPhase2Shared.Secrets Shared → Ambient A N C PqxdhInitialParentObserverCompiler.InitialReply)
  (selector : QueryImpl extra (Ambient A N C)) (aux : QueryImpl PqxdhServerRegistrationPublication.AuxSpec (Ambient A N C))
  (target : RootOutput)

/-- The actual complete routed source observer derives its final disclosure witness from the same saved history and candidate seed, with no callback or final-history premise. -/
theorem actual_stopped (disclosed : List RatchetChain)
    (mark : PqxdhBeaconPhase2Shared.Secrets Shared → Origin)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (context : Context extra M P I D K Result Origin S B) (material : PqxdhOrderedChainHybrids.Material)
    (state : PqxdhInitialParentObserver.State A N C) (candidates : List RootOutput)
    (result : (Result × (Front Slot M P I D K S B × PqxdhInitialOriginPost.Trace Origin S B)) ×
      State (PqxdhInitialParentObserver.State A N C))
    (supported : result ∈ support ((simulateQ
      (PqxdhInitialParentObserverAliases.observed source writer prior entry output pre application initializer selector aux
        (RawCtxSelectedLiveTrace.nativeReader (RawCtxFreshChainCut.concreteChain target)) target)
      (simulateQ PqxdhInitialParentObserverCompiler.compiler (stopped mark sender route decode context material))).run
        (initial disclosed context state candidates))) :
    Invariant target disclosed result.1.2.1.roles.2 result.2 := by
  rw [← QueryImpl.simulateQ_compose] at supported
  exact stopped_invariant target _ (actual_rules source writer prior entry output pre application initializer selector aux target)
    disclosed mark sender route decode context material _ (initial_invariant target disclosed context state candidates) result supported

end Actual

private theorem checker_forward_quiet (client : OracleComp (RawCtxFiniteLineageCheck.Spec Slot) (List Slot)) :
    (simulateQ (PqxdhInitialParentStoppedHop.checkerCompiler (extra := extra) (I := I) (D := D) (K := K) (X := X)
      (Response := Response) (Shared := Shared)) client).IsQueryBoundP
      (fun query => PqxdhInitialParentObserver.direct (extra := extra) query = true) 0 := by
  induction client using OracleComp.inductionOn with
  | pure value => trivial
  | query_bind query next ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, PqxdhInitialParentStoppedHop.checkerCompiler,
      PqxdhInitialParentObserverCompiler.oldForward, isQueryBoundP_query_bind_iff]
    exact ⟨Or.inl (by simp [PqxdhInitialParentObserver.direct, RawCtxSelectedParentReadMask.direct]), fun reply => ih reply⟩

/-- Every appended lineage derivation is a literal private primitive callback, preserving the source disclosure bit while retaining its input candidates. -/
theorem checker_quiet (depth : Option Nat) :
    (PqxdhInitialParentStoppedHop.checker (extra := extra) (I := I) (D := D) (K := K) (X := X)
      (Response := Response) (Shared := Shared) depth).IsQueryBoundP
      (fun query => PqxdhInitialParentObserver.direct (extra := extra) query = true) 0 := by
  cases depth with
  | none => trivial
  | some depth => exact checker_forward_quiet _

/-- The literal stopped source followed by its actual finite checker retains the original full-post disclosure invariant and every prior candidate. -/
theorem checked_invariant {A N C ContextId : Type}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (mark : PqxdhBeaconPhase2Shared.Secrets Shared → Origin)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (continuation : PqxdhInitialParentStoppedHop.Continuation ContextId extra M P I D K X Response Shared A N C Result Origin S B)
    (context : ContextId × RawCtxSelectedParentEntry.Entry) (target : RootOutput) (output : PqxdhFullSecretInputKdf.FullOutput)
    (disclosed : List RatchetChain) (state : PqxdhInitialParentObserver.State A N C) (candidates : List RootOutput)
    (result : PqxdhInitialParentStoppedHop.Trace M P I D K A N C Result Origin S B)
    (supported : result ∈ support ((simulateQ
      (PqxdhInitialParentObserverAliases.observed source writer (continuation.prior context.1) context.2 output
        (continuation.pre context.1) (continuation.application context.1) (continuation.initializer context.1)
        (continuation.selector context.1) (continuation.aux context.1)
        (RawCtxSelectedLiveTrace.nativeReader (RawCtxFreshChainCut.concreteChain target)) target)
      (PqxdhInitialParentStoppedHop.program mark sender route decode continuation context)).run
        (initial disclosed (continuation.cut context.1) state candidates))) :
    Invariant target disclosed result.1.1.2.1.roles.2 result.2 := by
  simp only [PqxdhInitialParentStoppedHop.program, simulateQ_bind, StateT.run_bind, mem_support_bind_iff,
    simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at supported
  obtain ⟨completed, sourceReached, checked, checkerReached, rfl⟩ := supported
  have established := actual_stopped source writer (continuation.prior context.1) context.2 output
    (continuation.pre context.1) (continuation.application context.1) (continuation.initializer context.1)
    (continuation.selector context.1) (continuation.aux context.1) target disclosed mark sender route decode
    (continuation.cut context.1) context.2.material state candidates completed sourceReached
  have kept := trace_keep _ _ _ _ (checker_quiet (continuation.depth context.1)) completed.2 checked checkerReached
  exact invariant_keep target disclosed completed.1.2.1.roles.2 completed.2 checked.2 established kept

end BeaconcryptCore.Computational.PqxdhInitialStoppedDisclosure

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialStoppedDisclosure.family_stopped' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialStoppedDisclosure.family_stopped

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialStoppedDisclosure.after_send_quiet' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialStoppedDisclosure.after_send_quiet

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialStoppedDisclosure.complete_invariant' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialStoppedDisclosure.complete_invariant

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialStoppedDisclosure.stopped_invariant' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialStoppedDisclosure.stopped_invariant

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialStoppedDisclosure.initial_invariant' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialStoppedDisclosure.initial_invariant

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialStoppedDisclosure.actual_stopped' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialStoppedDisclosure.actual_stopped

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialStoppedDisclosure.checker_quiet' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialStoppedDisclosure.checker_quiet

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialStoppedDisclosure.checked_invariant' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialStoppedDisclosure.checked_invariant
