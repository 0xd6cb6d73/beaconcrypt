import BeaconcryptCore.Computational.RawCtxSelectedParentPrivateRealization
import BeaconcryptCore.Computational.RawCtxFamilyAdaptiveFreshness

/-!
The final freshness checker follows one finite selected input lineage and includes the selected record's material key. Its queries are private reduction bookkeeping after the original adversary has stopped; none is delivered to the network or reveal interface. Every checker input remains an explicit candidate and each additional derivation is separately counted. This finite checker does not prove that a protocol schedule reaches the selected logical record or that any input is secret.
-/
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.refined ratchet.concrete
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RawCtxFiniteLineageCheck
open RawCtxSelectedChain PqxdhSecretInputKdf PqxdhFullSecretInputKdf

abbrev Spec (Chain : Type) : OracleSpec Chain := fun _ => Chain × RatchetMaterial

def nativeKey (material : RatchetMaterial) : RatchetChain := ⟨material.key.bytes⟩
def labelKey (material : RatchetMaterial) : Slot := .known (nativeKey material)

noncomputable def program {Chain : Type} (key : RatchetMaterial → Chain) : Nat → Chain → OracleComp (Spec Chain) (List Chain)
  | 0, input => do
      let reply ← (Spec Chain).query input
      pure [input, key reply.2]
  | n + 1, input => do
      let reply ← (Spec Chain).query input
      let rest ← program key n reply.1
      pure (input :: rest)

/-- Material-key interpretation retains every key byte and adds no chain operation. -/
theorem key_map (target : RootOutput) (material : RatchetMaterial) :
    interpret (RawCtxFreshChainCut.concreteChain target) (labelKey material) = nativeKey material := rfl

/-- The private finite checker makes at most the reserved number of derivation requests on all possible replies. -/
theorem queries {Chain : Type} (key : RatchetMaterial → Chain) (n : Nat) (input : Chain) :
    (program key n input).IsTotalQueryBound (n + 1) := by
  induction n generalizing input with
  | zero =>
    simp only [program, isTotalQueryBound_query_bind_iff]
    exact ⟨by omega, fun _ => trivial⟩
  | succ n ih =>
    rw [program, isTotalQueryBound_query_bind_iff]
    simpa only [Nat.add_sub_cancel, bind_pure_comp, IsTotalQueryBound, isQueryBound_map_iff] using
      (show 0 < n + 1 + 1 ∧ ∀ reply : Chain × RatchetMaterial, (program key n reply.1).IsTotalQueryBound (n + 1) from
        ⟨by omega, fun reply => ih reply.1⟩)

noncomputable def trace {Chain : Type} (key : RatchetMaterial → Chain)
    (step : Chain → Chain × RatchetMaterial) : Nat → Chain → List Chain
  | 0, input => [input, key (step input).2]
  | n + 1, input => input :: trace key step n (step input).1

/-- A deterministic private derivation backend evaluates the entire finite checker exactly and introduces no additional effects or observations. -/
theorem evaluate {Chain : Type} {m : Type → Type*} [Monad m] [LawfulMonad m]
    (key : RatchetMaterial → Chain) (step : Chain → Chain × RatchetMaterial) (n : Nat) (input : Chain) :
    simulateQ (fun query => (pure (step query) : m _)) (program key n input) = pure (trace key step n input) := by
  induction n generalizing input with
  | zero => simp only [program, trace, simulateQ_bind, simulateQ_spec_query, simulateQ_pure, pure_bind]
  | succ n ih =>
    simp only [program, trace, simulateQ_bind, simulateQ_spec_query, simulateQ_pure, pure_bind, ih]

/-- Mapping each original step and material key maps the complete finite lineage, including its selected record key. -/
theorem trace_map {Chain Native : Type} (convert : Chain → Native)
    (key : RatchetMaterial → Chain) (nativeKey : RatchetMaterial → Native)
    (step : Chain → Chain × RatchetMaterial) (nativeStep : Native → Native × RatchetMaterial)
    (keys : ∀ material, convert (key material) = nativeKey material)
    (steps : ∀ input, nativeStep (convert input) = Prod.map convert id (step input))
    (n : Nat) (input : Chain) :
    (trace key step n input).map convert = trace nativeKey nativeStep n (convert input) := by
  induction n generalizing input with
  | zero => simp only [trace, List.map_cons, List.map_nil, steps, Prod.map_snd, id_eq, keys]
  | succ n ih => simp only [trace, List.map_cons, steps, Prod.map_fst, ih]

noncomputable def routedStep (prior : RawCtxSelectedParentTable.Prior) (entry : RawCtxSelectedParentEntry.Entry)
    (target : RootOutput) (output : FullOutput) (input : Slot) : Slot × RatchetMaterial :=
  RawCtxSelectedParentTable.step prior entry (RawCtxKdfRequestTable.fullResponse output)
    (match input with
    | .hidden => .hidden
    | .known chain => if target = RawCtxSelectedQueryTrace.rootVector chain then .hidden else .known chain)

/-- The actual privately patched native function gives exactly the interpreted complete checker lineage; the separately charged parent-input collision remains explicit. -/
theorem native_trace (prior : RawCtxSelectedParentTable.Prior) (entry : RawCtxSelectedParentEntry.Entry)
    (target : RootOutput) (output : FullOutput)
    (separate : RawCtxSelectedParentPrivatePatch.targetAddress target ≠ entry.address) (n : Nat) (input : Slot) :
    (trace labelKey (routedStep prior entry target output) n input).map
        (interpret (RawCtxFreshChainCut.concreteChain target)) =
      trace nativeKey (RawCtxSelectedParentTable.nativeStep
        (RawCtxSelectedParentPrivatePatch.privatePatch prior target output) entry target)
        n (interpret (RawCtxFreshChainCut.concreteChain target) input) :=
  trace_map _ _ _ _ _ (key_map target)
    (RawCtxSelectedParentPrivatePatch.native_step prior entry target output separate) n input

/-- The selected input itself remains forbidden even when subsequent steps revisit it or alias another value. -/
theorem trace_contains {Chain : Type} (key : RatchetMaterial → Chain)
    (step : Chain → Chain × RatchetMaterial) (n : Nat) (input : Chain) : input ∈ trace key step n input := by
  cases n <;> exact List.mem_cons_self

/-- The finite checker retains one value for each input plus the selected material key, without removing repetitions. -/
theorem trace_length {Chain : Type} (key : RatchetMaterial → Chain)
    (step : Chain → Chain × RatchetMaterial) (n : Nat) (input : Chain) : (trace key step n input).length = n + 2 := by
  induction n generalizing input with
  | zero => rfl
  | succ n ih => simp only [trace, List.length_cons, ih, Nat.add_right_comm]

def knownValues : List Slot → List RatchetChain
  | [] => []
  | .hidden :: rest => knownValues rest
  | .known chain :: rest => chain :: knownValues rest

/-- The complete interpreted forbidden list consists exactly of its hidden coordinate when present and all retained known values, including aliases and repetitions. -/
theorem interpreted_mem (target value : RatchetChain) (slots : List Slot) :
    value ∈ slots.map (interpret target) ↔
      (value = target ∧ Slot.hidden ∈ slots) ∨ value ∈ knownValues slots := by
  induction slots with
  | nil => simp [knownValues]
  | cons slot rest ih =>
    cases slot
    all_goals simp only [knownValues, List.map_cons, List.mem_cons, interpret, ih, reduceCtorEq, false_or]
    all_goals simp only [true_or, and_true, ← or_assoc, or_comm]
    exact or_congr_left ⟨fun h => h.elim id And.left, Or.inl⟩

/-- If the private checker contains its hidden starting input, its exact value-based freshness is that input plus every retained known value. No injectivity or absence of aliases is required. -/
theorem interpreted_fresh (target : RatchetChain) (slots : List Slot) (values : List RatchetChain)
    (hidden : Slot.hidden ∈ slots) :
    RawCtxLiveLineage.FreshValues (slots.map (interpret target)) values ↔
      RawCtxLiveLineage.FreshValues (target :: knownValues slots) values := by
  unfold RawCtxLiveLineage.FreshValues
  apply forall_congr'
  intro value
  simp only [interpreted_mem, hidden, and_true, List.mem_cons]

/-- The original private native lineage freshness reduces to the supplied hidden coordinate plus the checker’s retained known values, including its selected material key. The same actual private function is used for every step. -/
theorem native_fresh (prior : RawCtxSelectedParentTable.Prior) (entry : RawCtxSelectedParentEntry.Entry)
    (target : RootOutput) (output : FullOutput)
    (separate : RawCtxSelectedParentPrivatePatch.targetAddress target ≠ entry.address) (n : Nat) (values : List RatchetChain) :
    RawCtxLiveLineage.FreshValues
      (trace nativeKey (RawCtxSelectedParentTable.nativeStep
        (RawCtxSelectedParentPrivatePatch.privatePatch prior target output) entry target)
        n (RawCtxFreshChainCut.concreteChain target)) values ↔
    RawCtxLiveLineage.FreshValues (RawCtxFreshChainCut.concreteChain target ::
      knownValues (trace labelKey (routedStep prior entry target output) n .hidden)) values := by
  simpa only [native_trace prior entry target output separate n .hidden, interpret] using
    interpreted_fresh (RawCtxFreshChainCut.concreteChain target)
      (trace labelKey (routedStep prior entry target output) n .hidden) values (trace_contains _ _ n Slot.hidden)

/-- Under every adaptive private backend, the finite checker retains its starting input; no backend correctness or secrecy premise is used. -/
theorem returned_contains {Chain State : Type} (key : RatchetMaterial → Chain)
    (handler : QueryImpl (Spec Chain) (StateT State ProbComp)) (n : Nat) (input : Chain)
    (state : State) (result : List Chain × State)
    (reached : result ∈ support ((simulateQ handler (program key n input)).run state)) : input ∈ result.1 := by
  cases n
  all_goals simp only [program, simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at reached
  all_goals simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at reached
  all_goals rcases reached with ⟨_, _, reached⟩
  all_goals first | (rcases reached with rfl; exact List.mem_cons_self) | (rcases reached with ⟨_, _, rfl⟩; exact List.mem_cons_self)

end BeaconcryptCore.Computational.RawCtxFiniteLineageCheck

/-- info: 'BeaconcryptCore.Computational.RawCtxFiniteLineageCheck.key_map' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxFiniteLineageCheck.key_map

/-- info: 'BeaconcryptCore.Computational.RawCtxFiniteLineageCheck.queries' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxFiniteLineageCheck.queries

/-- info: 'BeaconcryptCore.Computational.RawCtxFiniteLineageCheck.evaluate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxFiniteLineageCheck.evaluate

/-- info: 'BeaconcryptCore.Computational.RawCtxFiniteLineageCheck.trace_map' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxFiniteLineageCheck.trace_map

/-- info: 'BeaconcryptCore.Computational.RawCtxFiniteLineageCheck.native_trace' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxFiniteLineageCheck.native_trace

/-- info: 'BeaconcryptCore.Computational.RawCtxFiniteLineageCheck.trace_contains' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxFiniteLineageCheck.trace_contains

/-- info: 'BeaconcryptCore.Computational.RawCtxFiniteLineageCheck.trace_length' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxFiniteLineageCheck.trace_length

/-- info: 'BeaconcryptCore.Computational.RawCtxFiniteLineageCheck.interpreted_mem' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxFiniteLineageCheck.interpreted_mem

/-- info: 'BeaconcryptCore.Computational.RawCtxFiniteLineageCheck.interpreted_fresh' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxFiniteLineageCheck.interpreted_fresh

/-- info: 'BeaconcryptCore.Computational.RawCtxFiniteLineageCheck.native_fresh' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxFiniteLineageCheck.native_fresh

/-- info: 'BeaconcryptCore.Computational.RawCtxFiniteLineageCheck.returned_contains' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxFiniteLineageCheck.returned_contains
