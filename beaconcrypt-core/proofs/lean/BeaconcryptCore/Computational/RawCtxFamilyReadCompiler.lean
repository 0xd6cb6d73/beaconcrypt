import BeaconcryptCore.Computational.RawCtxGenericFamilyRead
import BeaconcryptCore.Computational.RawCtxSelectedParentPrivate

/-!
The finite-family reader retains its original owner in the outer source history while forwarding only the private read kind and optional selected kernel to the existing selected-live primitive interface. Missing owners reject without a primitive callback. The native optional value, candidate append and sticky direct-disclosure flag are exact. Complete non-read programs retain the same flag, original callbacks and candidate log; all supported traces preserve their prior candidate prefix.

These are operational source/trace equations. They do not assume that the direct flag is unlikely or that candidates miss a hidden input. Whole-family freshness and alias reductions must consume the original returned-value history. Each read uses at most one private read query and contributes at most one available candidate; the original source attempt and local lookup/copy work remain accounted separately. Snapshots and persistence are excluded.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RawCtxFamilyReadCompiler
open RawCtxSelectedChain RawCtxSelectedLiveTrace RawCtxSelectedLiveCompiler
open PqxdhSecretInputKdf PqxdhFullSecretInputKdf PqxdhJointKdfGame

abbrev Input (serverCount beaconCount : Nat) := RawCtxGenericFamilyRead.ReadInput Kernel serverCount beaconCount

def kind {serverCount beaconCount : Nat} : RawCtxProtocolReveals.Request serverCount beaconCount → RawCtxSelectedLiveRead.Read
  | .sendChain _ => .sendChain
  | .receiveChain _ => .receiveChain
  | .skippedKey _ sequence => .skippedKey sequence

noncomputable def value {serverCount beaconCount : Nat} (reader : Reader) :
    (input : Input serverCount beaconCount) → (RawCtxGenericFamilyRead.ReadSpec Kernel serverCount beaconCount).Range input
  | (.sendChain _, none) => .None
  | (.receiveChain _, none) => .None
  | (.skippedKey _ _, none) => .None
  | (.sendChain _, some kernel) => reader .sendChain (some kernel)
  | (.receiveChain _, some kernel) => reader .receiveChain (some kernel)
  | (.skippedKey _ sequence, some kernel) => reader (.skippedKey sequence) (some kernel)

noncomputable def compiler {serverCount beaconCount : Nat} :
    QueryImpl (RawCtxGenericFamilyRead.ReadSpec Kernel serverCount beaconCount) (OracleComp Spec)
  | (.sendChain _, none) => pure .None
  | (.receiveChain _, none) => pure .None
  | (.skippedKey _ _, none) => pure .None
  | (.sendChain _, some kernel) => Spec.query (.inr (.sendChain, some kernel))
  | (.receiveChain _, some kernel) => Spec.query (.inr (.receiveChain, some kernel))
  | (.skippedKey _ sequence, some kernel) => Spec.query (.inr (.skippedKey sequence, some kernel))

/-- The read compiler removes only the private owner tag and returns the actual native optional reply. -/
theorem native_value {serverCount beaconCount : Nat} (target : RatchetChain) (input : Input serverCount beaconCount) :
    value (nativeReader target) input = RawCtxGenericFamilyRead.nativeValue (nativeKernel target) input := by
  rcases input with ⟨request, entry⟩
  cases request <;> cases entry <;> rfl

private theorem state_pure {State Result : Type} (result : Result) (state : State) :
    (pure result : StateT State ProbComp Result) state = pure (result, state) := rfl

set_option backward.isDefEq.respectTransparency false in
/-- The concrete private-alias reader retains the original shared state and appends exactly the available values and direct-disclosure flag. -/
theorem trace_read {Auxiliary : Type} {serverCount beaconCount : Nat}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : RawCtxSelectedParentTable.Prior) (entry : RawCtxSelectedParentEntry.Entry)
    (output : FullOutput) (reader : Reader) (view : RawCtxSelectedParentLive.View) (target : RootOutput)
    (input : Input serverCount beaconCount) (state : RawCtxSelectedParentLive.State Auxiliary) :
    (simulateQ (RawCtxSelectedParentPrivate.observed source writer prior entry output reader view target)
      (compiler input)).run state =
      pure (value reader input, ((state.1.1,
        state.1.2 ++ RawCtxSelectedLiveRead.candidates (kind input.1) input.2),
        state.2 || RawCtxSelectedLiveRead.exposed (kind input.1) input.2)) := by
  rcases input with ⟨request, kernel⟩
  cases request <;> cases kernel <;>
    simp [compiler, value, kind, RawCtxSelectedParentPrivate.observed,
      RawCtxFlaggedQueryTrace.trace, RawCtxSelectedParentPrivate.read_same,
      RawCtxSelectedLiveCompiler.inputs, RawCtxSelectedParentReadMask.direct,
      RawCtxSelectedLiveRead.candidates, RawCtxSelectedLiveRead.labelRead,
      RawCtxSelectedLiveRead.replyInputs, RawCtxSelectedLiveRead.exposed, StateT.run, state_pure]

set_option backward.isDefEq.respectTransparency false in
/-- Every non-read primitive preserves the direct-disclosure bit and retains the same reply, shared effects and candidate append. -/
theorem primitive_step {State : Type}
    (handler : QueryImpl Spec (StateT State ProbComp))
    (query : RawCtxSelectedAliasPrimitives.Spec.Domain)
    (state : State × List RootOutput) (flag : Bool) :
    Prod.map id (fun result => (result, flag)) <$>
      (RawCtxSelectedQueryTrace.recorded (fun query => handler (.inl query))
        RawCtxSelectedAliasPrimitives.inputs query).run state =
      (RawCtxFlaggedQueryTrace.trace handler inputs RawCtxSelectedParentReadMask.direct (.inl query)).run (state, flag) := by
  simp [RawCtxSelectedQueryTrace.recorded, RawCtxFlaggedQueryTrace.trace,
    RawCtxSelectedParentReadMask.direct, inputs, StateT.run, Functor.map_map, Prod.map_def]
  rfl

/-- An arbitrary adaptive non-read program preserves the sticky bit while retaining every original primitive callback and candidate entry. -/
theorem primitive_complete {State Result : Type}
    (handler : QueryImpl Spec (StateT State ProbComp))
    (client : OracleComp RawCtxSelectedAliasPrimitives.Spec Result)
    (state : State × List RootOutput) (flag : Bool) :
    Prod.map id (fun result => (result, flag)) <$>
      (simulateQ (RawCtxSelectedQueryTrace.recorded (fun query => handler (.inl query))
        RawCtxSelectedAliasPrimitives.inputs) client).run state =
      (simulateQ (RawCtxFlaggedQueryTrace.trace handler inputs RawCtxSelectedParentReadMask.direct)
        (simulateQ primitiveForward client)).run (state, flag) := by
  rw [← QueryImpl.simulateQ_compose]
  apply map_run_simulateQ_eq_of_query_map_eq
  intro query prior
  exact (primitive_step handler query prior flag).trans
    (congrArg (fun work => work.run (prior, flag))
      (_root_.simulateQ_spec_query
        (RawCtxFlaggedQueryTrace.trace handler inputs RawCtxSelectedParentReadMask.direct)
        (.inl query))).symm


/-- Every supported full trace retains all prior candidates, including across arbitrary non-read callbacks. -/
theorem retained_candidates {State Result : Type}
    (handler : QueryImpl Spec (StateT State ProbComp))
    (client : OracleComp Spec Result) (state : (State × List RootOutput) × Bool)
    (result : Result × ((State × List RootOutput) × Bool))
    (supported : result ∈ support ((simulateQ
      (RawCtxFlaggedQueryTrace.trace handler inputs RawCtxSelectedParentReadMask.direct) client).run state)) :
    state.1.2 ⊆ result.2.1.2 := by
  induction client using OracleComp.inductionOn generalizing state result with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
      subst result
      exact List.Subset.refl _
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query] at supported
      change result ∈ support (((RawCtxFlaggedQueryTrace.trace handler inputs RawCtxSelectedParentReadMask.direct query).run state) >>= fun reply =>
        (simulateQ (RawCtxFlaggedQueryTrace.trace handler inputs RawCtxSelectedParentReadMask.direct) (next reply.1)).run reply.2) at supported
      simp only [RawCtxFlaggedQueryTrace.trace, StateT.run, bind_assoc, pure_bind] at supported
      rw [mem_support_bind_iff] at supported
      obtain ⟨reply, _, tailSupport⟩ := supported
      exact List.Subset.trans (List.subset_append_left _ _) (ih reply.1 _ result tailSupport)

/-- A family read spends at most one private read-interface query; absent owners reject without a callback. -/
theorem compiler_total {serverCount beaconCount : Nat} (input : Input serverCount beaconCount) :
    (compiler input).IsTotalQueryBound 1 := by
  rcases input with ⟨request, kernel⟩
  cases request <;> cases kernel
  all_goals first | trivial | exact (isQueryBound_query_iff _ _ _ _).mpr (by decide)

/-- Each original read attempt contributes at most one available candidate value. -/
theorem candidates_length {serverCount beaconCount : Nat} (input : Input serverCount beaconCount) :
    (RawCtxSelectedLiveRead.candidates (kind input.1) input.2).length ≤ 1 :=
  RawCtxSelectedLiveRead.reply_length _ _

end BeaconcryptCore.Computational.RawCtxFamilyReadCompiler

/-- info: 'BeaconcryptCore.Computational.RawCtxFamilyReadCompiler.native_value' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxFamilyReadCompiler.native_value

/-- info: 'BeaconcryptCore.Computational.RawCtxFamilyReadCompiler.trace_read' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxFamilyReadCompiler.trace_read

/-- info: 'BeaconcryptCore.Computational.RawCtxFamilyReadCompiler.primitive_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxFamilyReadCompiler.primitive_step

/-- info: 'BeaconcryptCore.Computational.RawCtxFamilyReadCompiler.primitive_complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxFamilyReadCompiler.primitive_complete

/-- info: 'BeaconcryptCore.Computational.RawCtxFamilyReadCompiler.retained_candidates' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxFamilyReadCompiler.retained_candidates

/-- info: 'BeaconcryptCore.Computational.RawCtxFamilyReadCompiler.compiler_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxFamilyReadCompiler.compiler_total

/-- info: 'BeaconcryptCore.Computational.RawCtxFamilyReadCompiler.candidates_length' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxFamilyReadCompiler.candidates_length
