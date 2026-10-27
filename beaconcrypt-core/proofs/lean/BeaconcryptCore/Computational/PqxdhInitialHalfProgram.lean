import BeaconcryptCore.Computational.PqxdhInitialHalfDisclosure
import BeaconcryptCore.Computational.PqxdhInitialParentStoppedHop

/-!
The first-half comparison executes the complete original Server builder before the original adaptive post client and then the finite private lineage checker. Its initial history is the pre-builder history. The compiler preserves optional hidden initializer kernels, all ambient effects and the installed-session/publication trace.
-/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhInitialHalfProgram
open PqxdhJointKdfGame PqxdhSecretInputKdf PqxdhFullSecretInputKdf
open PqxdhInitialBeaconAmbient PqxdhInitialHalfObserverCompiler
open PqxdhInitialParentObserver (State)
open PqxdhInitialPendingPost PqxdhInitialPostContext
open PqxdhInitialParentStoppedHop (SourceFinal Final Trace)
variable {ι M P I D K X Response Shared A N C Result Origin Store : Type} {extra : OracleSpec ι} {S B : Nat}

structure Execution (extra : OracleSpec ι) (M P I D K Result Origin : Type) (S B : Nat) where
  first : RustM (KernelOf RawCtxSelectedChain.Slot)
  index : Fin S
  metadata : P
  ready : PqxdhPrivateAcceptedRoot.Ready
  post : RustM (Option PqxdhServerRegistrationPublication.Response) → OracleComp (PqxdhInitialGenericPost.Spec extra S B) Result
  before : LabelFront M P I D K S B
  trace : PqxdhInitialOriginPost.Trace Origin S B
  origin : Origin

noncomputable def checkerCompiler : QueryImpl (RawCtxFiniteLineageCheck.Spec RawCtxSelectedChain.Slot)
    (OracleComp (PqxdhInitialHalfObserverCompiler.Spec extra I D K X Response Shared)) :=
  fun input => oldForward (.inl (.inr (.inl (.inl input))))

noncomputable def checker (depth : Nat) : OracleComp (PqxdhInitialHalfObserverCompiler.Spec extra I D K X Response Shared)
    (List RawCtxSelectedChain.Slot) :=
  simulateQ checkerCompiler (RawCtxFiniteLineageCheck.program RawCtxFiniteLineageCheck.labelKey depth .hidden)

noncomputable def baseProgram (source : FixedHkdfSha512NoSaltSource)
    (mark : PqxdhBeaconPhase2Shared.Secrets Shared → Origin)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (execution : Execution extra M P I D K Result Origin S B) :
    OracleComp (PqxdhInitialHalfObserverCompiler.Spec extra I D K X Response Shared) (SourceFinal M P I D K Result Origin S B) :=
  simulateQ PqxdhInitialHalfObserverCompiler.compiler
    ((PqxdhInitialOriginPost.sequence source execution.first mark execution.origin sender route decode
      execution.index execution.metadata execution.ready execution.post).run (execution.before, execution.trace))

noncomputable def program (source : FixedHkdfSha512NoSaltSource)
    (mark : PqxdhBeaconPhase2Shared.Secrets Shared → Origin)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (execution : Execution extra M P I D K Result Origin S B) (depth : Nat) :
    OracleComp (PqxdhInitialHalfObserverCompiler.Spec extra I D K X Response Shared) (Final M P I D K Result Origin S B) := do
  let result ← baseProgram source mark sender route decode execution
  let forbidden ← checker depth
  pure (result, forbidden)

def initial (disclosed : List RatchetChain) (execution : Execution extra M P I D K Result Origin S B)
    (state : State A N C) (candidates : List RootOutput) : (State A N C × List RootOutput) × Bool :=
  ((state, RawCtxFamilyFreshnessProxy.knownInputs disclosed execution.before.roles.2 ++ candidates), false)

/-- The literal pre-builder source history supplies the initial disclosure invariant without using the unavailable chain. -/
theorem initial_invariant (target : RootOutput) (disclosed : List RatchetChain)
    (execution : Execution extra M P I D K Result Origin S B) (state : State A N C) (candidates : List RootOutput) :
    PqxdhInitialDisclosureState.Invariant target disclosed execution.before.roles.2 (initial disclosed execution state candidates) :=
  ⟨(fun impossible => by cases impossible), fun _ => List.subset_append_left _ _⟩

/-- The actual appended checker retains the hidden initial half under every backend, independently of source success or rejection. -/
theorem checked_contains
    (backend : QueryImpl (PqxdhInitialHalfObserverCompiler.Spec extra I D K X Response Shared) (StateT Store ProbComp))
    (source : FixedHkdfSha512NoSaltSource) (mark : PqxdhBeaconPhase2Shared.Secrets Shared → Origin)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (execution : Execution extra M P I D K Result Origin S B) (depth : Nat)
    (state : Store) (result : Final M P I D K Result Origin S B × Store)
    (supported : result ∈ support ((simulateQ backend (program source mark sender route decode execution depth)).run state)) :
    RawCtxSelectedChain.Slot.hidden ∈ result.1.2 := by
  simp only [program, simulateQ_bind, StateT.run_bind, mem_support_bind_iff,
    simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at supported
  obtain ⟨original, _, tail, reached, rfl⟩ := supported
  exact RawCtxFiniteLineageCheck.returned_contains RawCtxFiniteLineageCheck.labelKey
    (backend ∘ₛ checkerCompiler) depth .hidden original.2 tail
    (by simpa only [checker, QueryImpl.simulateQ_compose] using reached)

/-- The finite private lineage check has no direct adversary-read operation. -/
theorem checker_quiet (depth : Nat) :
    (checker (extra := extra) (I := I) (D := D) (K := K) (X := X) (Response := Response) (Shared := Shared) depth).IsQueryBoundP
      (fun query => PqxdhInitialHalfObserver.direct (extra := extra) query = true) 0 := by
  unfold checker
  induction RawCtxFiniteLineageCheck.program RawCtxFiniteLineageCheck.labelKey depth .hidden using OracleComp.inductionOn with
  | pure value => trivial
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query]
      apply isQueryBoundP_bind (n := 0) (m := 0)
      · exact (isQueryBoundP_query_iff _ _ _).mpr (by simp [PqxdhInitialHalfObserver.direct,
          RawCtxSelectedParentReadMask.direct])
      · exact fun reply _ => ih reply

/-- The original full firstbuilder/post execution and its private checker derive the same final byte-disclosure invariant from the actual pre-builder history. -/
theorem checked_invariant
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : RawCtxSelectedParentTable.Prior) (entry : RawCtxSelectedParentEntry.Entry)
    (pre : QueryImpl (PqxdhBeaconPhase2Shared.Spec I D K X Response Shared) (Ambient A N C))
    (application : Response → Ambient A N C (Option Pqxdh.Bytes))
    (initializer : PqxdhBeaconPhase2Shared.Secrets Shared → Ambient A N C InitialReply)
    (selector : QueryImpl extra (Ambient A N C)) (aux : QueryImpl PqxdhServerRegistrationPublication.AuxSpec (Ambient A N C))
    (mark : PqxdhBeaconPhase2Shared.Secrets Shared → Origin)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (execution : Execution extra M P I D K Result Origin S B) (depth : Nat) (target : RootOutput) (output : FullOutput)
    (disclosed : List RatchetChain) (state : State A N C) (candidates : List RootOutput)
    (result : Trace M P I D K A N C Result Origin S B)
    (supported : result ∈ support ((simulateQ
      (PqxdhInitialHalfPrivateObserver.observed source writer prior entry output pre application initializer selector aux
        (RawCtxSelectedLiveTrace.nativeReader (RawCtxFreshChainCut.concreteChain target)) target)
      (program source mark sender route decode execution depth)).run (initial disclosed execution state candidates))) :
    PqxdhInitialDisclosureState.Invariant target disclosed result.1.1.2.1.roles.2 result.2 := by
  simp only [program, simulateQ_bind, StateT.run_bind, mem_support_bind_iff,
    simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at supported
  obtain ⟨completed, sourceReached, checked, checkerReached, rfl⟩ := supported
  rw [baseProgram, ← QueryImpl.simulateQ_compose] at sourceReached
  have established := PqxdhInitialHalfDisclosure.sequence_invariant target _
    (PqxdhInitialHalfPrivateObserver.actual_rules source writer prior entry output pre application initializer selector aux target)
    disclosed source execution.first mark execution.origin sender route decode execution.index execution.metadata execution.ready execution.post
    (execution.before, execution.trace) _ (initial_invariant target disclosed execution state candidates) completed sourceReached
  have kept := PqxdhInitialDisclosureState.trace_keep _ _ _ _ (checker_quiet depth) completed.2 checked checkerReached
  exact PqxdhInitialDisclosureState.invariant_keep target disclosed completed.1.2.1.roles.2 completed.2 checked.2 established kept

end BeaconcryptCore.Computational.PqxdhInitialHalfProgram

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialHalfProgram.initial_invariant' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialHalfProgram.initial_invariant

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialHalfProgram.checked_contains' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialHalfProgram.checked_contains

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialHalfProgram.checker_quiet' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialHalfProgram.checker_quiet

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialHalfProgram.checked_invariant' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialHalfProgram.checked_invariant
