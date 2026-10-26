-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRecordFactsOriginOrdinalTrace
import BeaconcryptCore.Computational.PqxdhRecordFactsOriginAverage

/-! Supported-prefix averaging and a finite attempted-seal union in one actual source run. -/
open OracleComp OracleSpec ENNReal MeasureTheory ProbabilityTheory
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhRecordFactsOriginOrdinalProbability
open PqxdhRecordLiftWorldCompiler (Label)
open PqxdhRecordLiftIdeal (CtxPrivate)
open PqxdhRecordLiftProtocol (Service ServiceSpec)
open PqxdhRecordFactsOriginOrdinalCut (Cut Outcome scan resume)
open PqxdhRecordFactsOriginOrdinalTrace (track Result selected markedResume)
local instance (α : Type) : MeasurableSpace α := ⊤
local instance (α : Type) : DiscreteMeasurableSpace α := ⟨fun _ => trivial⟩
variable {n : Nat} {X : Type}
local instance : MeasurableSpace (X × CtxPrivate n) := ⊤
local instance : DiscreteMeasurableSpace (X × CtxPrivate n) := ⟨fun _ => trivial⟩
local instance : MeasurableSpace (Outcome n X) := ⊤
local instance : DiscreteMeasurableSpace (Outcome n X) := ⟨fun _ => trivial⟩
local instance : MeasurableSpace (Option (Cut n X) × (X × CtxPrivate n)) := ⊤
local instance : DiscreteMeasurableSpace (Option (Cut n X) × (X × CtxPrivate n)) := ⟨fun _ => trivial⟩
local instance : MeasurableSpace (Result n X) := ⊤
local instance : DiscreteMeasurableSpace (Result n X) := ⟨fun _ => trivial⟩

/-- An ordinal contributes only when that cut exists; the event sees its complete cut and original final source result. -/
def SelectedEvent (event : Cut n X → X × CtxPrivate n → Prop)
    (result : Option (Cut n X) × (X × CtxPrivate n)) : Prop :=
  match result.1 with
  | none => False
  | some cut => event cut result.2

/-- Retaining cut metadata does not alter the selected continuation event probability. -/
theorem marked_pending (service : QueryImpl (ServiceSpec n) (StateT (CtxPrivate n) ProbComp))
    (event : Cut n X → X × CtxPrivate n → Prop) (cut : Cut n X) :
    𝒟[markedResume service (.inr cut)] {result | SelectedEvent event result} =
      𝒟[resume service (.inr cut)] {result | event cut result} := by
  simp only [markedResume]
  rw [← prEvent_eq_evalDist_of_discrete, ← prEvent_eq_evalDist_of_discrete, prEvent_map]
  rfl

/-- Completion before the selected callback contributes probability zero. -/
theorem marked_complete (service : QueryImpl (ServiceSpec n) (StateT (CtxPrivate n) ProbComp))
    (event : Cut n X → X × CtxPrivate n → Prop) (value : X × CtxPrivate n) :
    𝒟[markedResume service (.inl value)] {result | SelectedEvent event result} = 0 := by
  classical
  simp only [markedResume]
  rw [← prEvent_eq_evalDist_of_discrete, prEvent_pure]
  simp [SelectedEvent]

/-- The selected continuation bound is averaged over the complete unchanged supported prefix, without conditioning on a later result. -/
theorem selected_bound (service : QueryImpl (ServiceSpec n) (StateT (CtxPrivate n) ProbComp))
    (work : OracleComp (ServiceSpec n) X) (index : Nat) (state : CtxPrivate n) (past : List (Label n))
    (event : Cut n X → X × CtxPrivate n → Prop) (cap : ℝ≥0∞)
    (bounded : ∀ cut, Sum.inr cut ∈ support (scan service work index state past) →
      𝒟[resume service (.inr cut)] {result | event cut result} ≤ cap) :
    𝒟[track service work state past] {result | SelectedEvent event (selected index result)} ≤ cap := by
  have mapped : 𝒟[selected index <$> track service work state past] {result | SelectedEvent event result} =
      𝒟[track service work state past] {result | SelectedEvent event (selected index result)} := by
    rw [← prEvent_eq_evalDist_of_discrete, ← prEvent_eq_evalDist_of_discrete, prEvent_map]
  rw [← mapped, PqxdhRecordFactsOriginOrdinalTrace.track_selected]
  apply PqxdhRecordFactsOriginAverage.bind_le
  intro outcome supported
  cases outcome with
  | inl value => rw [marked_complete]; exact bot_le
  | inr cut => rw [marked_pending]; exact bounded cut supported

/-- A finite union over attempted ordinals is taken in the same complete original source trace. -/
theorem finite_union_bound (service : QueryImpl (ServiceSpec n) (StateT (CtxPrivate n) ProbComp))
    (work : OracleComp (ServiceSpec n) X) (state : CtxPrivate n) (past : List (Label n))
    (event : Cut n X → X × CtxPrivate n → Prop) (count : Nat) (cap : ℝ≥0∞)
    (bounded : ∀ index : Fin count, ∀ cut,
      Sum.inr cut ∈ support (scan service work index.val state past) →
        𝒟[resume service (.inr cut)] {result | event cut result} ≤ cap) :
    𝒟[track service work state past]
      {result | ∃ index : Fin count, SelectedEvent event (selected index.val result)} ≤ count * cap := by
  have cover : {result : Result n X | ∃ index : Fin count, SelectedEvent event (selected index.val result)} =
      ⋃ index : Fin count, {result | SelectedEvent event (selected index.val result)} := by
    ext result
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion]
  rw [cover]
  refine (measure_iUnion_le _).trans ((ENNReal.tsum_le_tsum fun index =>
    selected_bound service work index.val state past event cap (bounded index)).trans ?_)
  simp only [tsum_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, le_refl]

/-- Every cut in a supported trace is covered by one of the original charged sealing ordinals. -/
theorem trace_event_cover (service : QueryImpl (ServiceSpec n) (StateT (CtxPrivate n) ProbComp))
    (work : OracleComp (ServiceSpec n) X) (state : CtxPrivate n) (past : List (Label n))
    (event : Cut n X → X × CtxPrivate n → Prop) (count : Nat)
    (bounded : PqxdhRecordLiftCtxProgramBounds.Weighted PqxdhRecordFactsHashSealBills.sealCost work count)
    (result : Result n X) (supported : result ∈ support (track service work state past))
    (hit : ∃ cut ∈ result.1, event cut result.2) :
    ∃ index : Fin count, SelectedEvent event (selected index.val result) := by
  obtain ⟨cut, member, hit⟩ := hit
  obtain ⟨index, within, same⟩ := List.mem_iff_getElem.mp member
  have length := PqxdhRecordFactsOriginOrdinalTrace.track_length service work count bounded state past result supported
  refine ⟨⟨index, Nat.lt_of_lt_of_le within length⟩, ?_⟩
  have chosen : result.1[index]? = some cut := List.getElem?_eq_some_iff.mpr ⟨within, same⟩
  simpa only [selected, SelectedEvent, chosen] using hit

/-- The actual finite attempted-seal allowance multiplies a pointwise selected continuation bound once, without independence between ordinal events. -/
theorem any_cut_bound (service : QueryImpl (ServiceSpec n) (StateT (CtxPrivate n) ProbComp))
    (work : OracleComp (ServiceSpec n) X) (state : CtxPrivate n) (past : List (Label n))
    (event : Cut n X → X × CtxPrivate n → Prop) (count : Nat) (cap : ℝ≥0∞)
    (billed : PqxdhRecordLiftCtxProgramBounds.Weighted PqxdhRecordFactsHashSealBills.sealCost work count)
    (bounded : ∀ index : Fin count, ∀ cut,
      Sum.inr cut ∈ support (scan service work index.val state past) →
        𝒟[resume service (.inr cut)] {result | event cut result} ≤ cap) :
    𝒟[track service work state past] {result | ∃ cut ∈ result.1, event cut result.2} ≤ count * cap := by
  refine le_trans ?_ (finite_union_bound service work state past event count cap bounded)
  apply measure_mono_ae
  apply OracleComp.ae_evalDist_of_forall_mem_support
  intro result supported hit
  exact trace_event_cover service work state past event count billed result supported hit

/-- An original source event inherits the attempted-seal union bound after its explicit supported-trace inclusion and local callback bound have been proved. -/
theorem source_event_bound (service : QueryImpl (ServiceSpec n) (StateT (CtxPrivate n) ProbComp))
    (work : OracleComp (ServiceSpec n) X) (state : CtxPrivate n) (past : List (Label n))
    (sourceEvent : X × CtxPrivate n → Prop) (event : Cut n X → X × CtxPrivate n → Prop)
    (count : Nat) (cap : ℝ≥0∞)
    (billed : PqxdhRecordLiftCtxProgramBounds.Weighted PqxdhRecordFactsHashSealBills.sealCost work count)
    (covered : ∀ result ∈ support (track service work state past), sourceEvent result.2 →
      ∃ cut ∈ result.1, event cut result.2)
    (bounded : ∀ index : Fin count, ∀ cut,
      Sum.inr cut ∈ support (scan service work index.val state past) →
        𝒟[resume service (.inr cut)] {result | event cut result} ≤ cap) :
    𝒟[(simulateQ service work).run state] {result | sourceEvent result} ≤ count * cap := by
  have original : 𝒟[(simulateQ service work).run state] {result | sourceEvent result} =
      𝒟[track service work state past] {result | sourceEvent result.2} := by
    rw [← PqxdhRecordFactsOriginOrdinalTrace.track_drop service work state past]
    rw [← prEvent_eq_evalDist_of_discrete, ← prEvent_eq_evalDist_of_discrete, prEvent_map]
  rw [original]
  refine le_trans ?_ (any_cut_bound service work state past event count cap billed bounded)
  apply measure_mono_ae
  apply OracleComp.ae_evalDist_of_forall_mem_support
  exact covered

end BeaconcryptCore.Computational.PqxdhRecordFactsOriginOrdinalProbability

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginOrdinalProbability.marked_pending' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginOrdinalProbability.marked_pending

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginOrdinalProbability.marked_complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginOrdinalProbability.marked_complete

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginOrdinalProbability.selected_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginOrdinalProbability.selected_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginOrdinalProbability.finite_union_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginOrdinalProbability.finite_union_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginOrdinalProbability.trace_event_cover' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginOrdinalProbability.trace_event_cover

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginOrdinalProbability.any_cut_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginOrdinalProbability.any_cut_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginOrdinalProbability.source_event_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginOrdinalProbability.source_event_bound
