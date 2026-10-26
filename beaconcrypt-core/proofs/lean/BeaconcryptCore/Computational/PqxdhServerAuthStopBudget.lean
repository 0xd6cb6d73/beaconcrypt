import BeaconcryptCore.Computational.PqxdhServerAuthStopMonitor

section BudgetSection

open OracleComp OracleSpec ENNReal
set_option autoImplicit false

namespace BeaconcryptCore.Computational.PqxdhServerAuthCtxStop
open PqxdhServerAuthExperiment PqxdhServerAuthEntryFactor PqxdhServerAuthPendingBudget
open PqxdhServerAuthGapDh
variable {KemSK τ : Type}

/-- One build remains available until the first selected allocation, and thereafter only while its actual one-use pending token remains. -/
def buildReserve (game : GameState KemSK) (first : Option Nat) : Nat :=
  match first with
  | none => 1
  | some index => slotWeight (game.pending index)

/-- Count a reached selected builder only when the original dispatch finds its pending token. -/
def buildBill (query : ServerAuthSpec.Domain) (state : FlatState KemSK τ) : Nat :=
  match query with
  | .inr (.build index _) => if state.2.1 index then slotWeight (state.1.pending index) else 0
  | _ => 0

/-- This reservation is a global one-call budget, independent of the number of Server sessions or attempted network deliveries. -/
theorem buildReserve_le_one (game : GameState KemSK) (first : Option Nat) : buildReserve game first ≤ 1 := by
  cases first with
  | none => exact Nat.le_refl 1
  | some index => cases found : game.pending index <;> simp only [buildReserve, found, slotWeight, Nat.zero_le, Nat.le_refl]

/-- Every immediate selected build is paid before any optional component refusal, using only the actual monitor and token. -/
theorem buildBill_le (query : ServerAuthSpec.Domain) (state : FlatState KemSK τ)
    (first : Option Nat) (tracked : Tracked state.2.1 first) : buildBill query state ≤ buildReserve state.1 first := by
  cases query with
  | inl coin => exact Nat.zero_le _
  | inr query =>
      cases query with
      | build index payload =>
          simp only [buildBill]
          split_ifs with marked
          · rw [tracked.unique index marked]
            exact Nat.le_refl _
          · exact Nat.zero_le _
      | accept _ | finish _ | hmac _ _ | hash _ | reveal _ => exact Nat.zero_le _

/-- The complete source footprint pays each selected builder and leaves the remaining reservation only on a normal checkpoint reply. The second accept's prefix work is unaffected by this selected-call ledger. -/
theorem build_potential_step (query : ServerAuthSpec.Domain) (before after : FlatState KemSK τ)
    (first : Option Nat) (tracked : Tracked before.2.1 first)
    (fresh : before.2.1 before.1.sessions = false) (footprint : ResourceStep query before.1 after.1)
    (reply : ServerAuthSpec.Range query) :
    buildBill query before +
      (if (checkpoint query before.1.sessions after.2.1 first reply).1.isSome then
        buildReserve after.1 (checkpoint query before.1.sessions after.2.1 first reply).2 else 0) ≤
      buildReserve before.1 first := by
  cases query with
  | inl coin =>
      simp only [checkpoint, Option.isSome_some, ↓reduceIte, buildBill, Nat.zero_add]
      cases first <;> simp only [buildReserve, footprint.2.2, Nat.le_refl]
  | inr query =>
      cases query with
      | accept raw =>
          simp only [buildBill, Nat.zero_add, checkpoint]
          by_cases marked : after.2.1 before.1.sessions = true
          · simp only [marked, ↓reduceIte]
            cases first with
            | none => exact buildReserve_le_one after.1 (some before.1.sessions)
            | some index => exact Nat.zero_le _
          · simp only [marked, Bool.false_eq_true, ↓reduceIte]
            cases first with
            | none => exact Nat.le_refl _
            | some index =>
                have old := tracked.present index rfl
                have different : index ≠ before.1.sessions := by
                  intro same
                  rw [same, fresh] at old
                  cases old
                rcases footprint.2.2 with unchanged | ⟨token, inserted⟩
                · simp only [buildReserve, unchanged, Option.isSome_some, ↓reduceIte, Nat.le_refl]
                · simp only [buildReserve, inserted, Function.update_of_ne different, Option.isSome_some, ↓reduceIte, Nat.le_refl]
      | build index payload =>
          simp only [checkpoint, Option.isSome_some, ↓reduceIte, buildBill]
          by_cases marked : before.2.1 index = true
          · have recorded := tracked.unique index marked
            simp only [marked, ↓reduceIte, recorded, buildReserve, footprint.2.2, Function.update_self,
              slotWeight, Nat.add_zero, Nat.le_refl]
          · simp only [marked, Bool.false_eq_true, ↓reduceIte, Nat.zero_add]
            cases first with
            | none => exact Nat.le_refl _
            | some selected =>
                have different : selected ≠ index := by
                  intro same
                  exact marked (same ▸ tracked.present selected rfl)
                simp only [buildReserve, footprint.2.2, Function.update_of_ne different, Nat.le_refl]
      | finish raw =>
          simp only [checkpoint, Option.isSome_some, ↓reduceIte, buildBill, Nat.zero_add]
          cases first <;> simp only [buildReserve, footprint.2.1, Nat.le_refl]
      | hmac key bytes | hash bytes | reveal key =>
          simp only [checkpoint, Option.isSome_some, ↓reduceIte, buildBill, Nat.zero_add]
          cases first <;> simp only [buildReserve, footprint.2.2, Nat.le_refl]

/-- A possible raw component opening is charged for every active finish attempt, before parser or native rejection. -/
def rawBill (query : ServerAuthSpec.Domain) (game : GameState KemSK) : Nat :=
  match query with
  | .inr (.finish _) => initSentFlag game
  | _ => 0

/-- The original one-shot phase covers each raw attempt before any optional refusal. -/
theorem rawBill_le (query : ServerAuthSpec.Domain) (game : GameState KemSK) :
    rawBill query game ≤ initSentFlag game := by
  cases query with
  | inl coin => exact Nat.zero_le _
  | inr query => cases query <;> first | exact Nat.zero_le _ | exact Nat.le_refl _

/-- Every completed native finish exhausts the one-shot budget, including rejected and failed opening paths. -/
theorem raw_potential_step (query : ServerAuthSpec.Domain) (before after : GameState KemSK)
    (footprint : ResourceStep query before after) (continues : Bool) :
    rawBill query before + (if continues then initSentFlag after else 0) ≤ initSentFlag before := by
  have paid : rawBill query before + initSentFlag after = initSentFlag before := by
    rw [ResourceStep.flag query before after footprint]
    cases query with
    | inl coin => exact Nat.zero_add _
    | inr query => cases query <;> simp only [rawBill, resourceFlag, Nat.add_zero, Nat.zero_add]
  calc
    rawBill query before + (if continues then initSentFlag after else 0) ≤
        rawBill query before + initSentFlag after := Nat.add_le_add_left (by split <;> omega) _
    _ = initSentFlag before := paid

/-- Every marked coordinate belongs to a strictly earlier source allocation. -/
def Below (state : FlatState KemSK τ) : Prop :=
  ∀ index, state.2.1 index = true → index < state.1.sessions

/-- The next attempted allocation cannot already be marked. -/
theorem Below.fresh (state : FlatState KemSK τ) (below : Below state) :
    state.2.1 state.1.sessions = false := by
  apply Bool.eq_false_of_not_eq_true
  intro marked
  exact Nat.lt_irrefl _ (below _ marked)

/-- Literal allocation and mark footprints preserve strict chronological coordinates, independently of all cryptographic replies and component refusals. -/
theorem Below.step (query : ServerAuthSpec.Domain) (before after : FlatState KemSK τ)
    (below : Below before) (resources : ResourceStep query before.1 after.1)
    (marks : MarkStep query before after) : Below after := by
  intro index marked
  cases query with
  | inl coin =>
      rw [marks] at marked
      rw [resources.1]
      exact below index marked
  | inr query =>
      cases query with
      | accept raw =>
          rw [resources.1]
          rcases marks with unchanged | updated
          · rw [unchanged] at marked
            exact Nat.lt_succ_of_lt (below index marked)
          · by_cases same : index = before.1.sessions
            · omega
            · rw [updated, Function.update_of_ne same] at marked
              exact Nat.lt_succ_of_lt (below index marked)
      | build _ _ | finish _ | hmac _ _ | hash _ | reveal _ =>
          rw [marks] at marked
          rw [resources.1]
          exact below index marked

end BeaconcryptCore.Computational.PqxdhServerAuthCtxStop

end BudgetSection

section ProgramBoundsSection

open OracleComp OracleSpec ENNReal
set_option autoImplicit false

namespace BeaconcryptCore.Computational.PqxdhServerAuthCtxStop

/-- Optional interpreters pay all reached work before either native or monitor refusal. Only a normal reply carries a continuation reservation. The source-class budgets and concrete immediate oracle bills remain explicit. -/
theorem optional_potential_invariant {ι₁ ι₂ State : Type} {spec₁ : OracleSpec ι₁} {spec₂ : OracleSpec ι₂}
    {k : Nat} (handler : QueryImpl spec₁ (OptionT (StateT State (OracleComp spec₂))))
    (invariant : State → Prop) (classes : Fin k → ι₁ → Prop) [∀ i, DecidablePred (classes i)]
    (target : ι₂ → Prop) [DecidablePred target] (potential : (Fin k → Nat) → State → Nat)
    (step : ∀ query state (budget : Fin k → Nat), invariant state →
      (∀ i, classes i query → 0 < budget i) →
      ∃ cost, ((handler query).run state).IsQueryBoundP target cost ∧ cost ≤ potential budget state ∧
        ∀ result ∈ support ((handler query).run state), ∀ reply, result.1 = some reply →
          invariant result.2 ∧ cost + potential (fun i => if classes i query then budget i - 1 else budget i) result.2 ≤ potential budget state)
    {Result : Type} (client : OracleComp spec₁ Result) (budget : Fin k → Nat)
    (bounded : ∀ i, client.IsQueryBoundP (classes i) (budget i)) (state : State) (valid : invariant state) :
    (((simulateQ handler client).run).run state).IsQueryBoundP target (potential budget state) := by
  induction client using OracleComp.inductionOn generalizing budget state with
  | pure value => simp [simulateQ_pure]
  | query_bind query next ih =>
      have split := fun i => (isQueryBoundP_query_bind_iff (classes i) query next (budget i)).mp (bounded i)
      obtain ⟨cost, costBound, costLe, after⟩ := step query state budget valid
        (fun i found => (split i).1.resolve_left (not_not.mpr found))
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, id_map,
        OptionT.run_bind, Option.elimM, StateT.run]
      have rest : ∀ result ∈ support ((handler query).run state),
          ((result.1.elim (pure none) (fun reply => (simulateQ handler (next reply)).run)) result.2).IsQueryBoundP
            target (potential budget state - cost) := by
        intro result supported
        cases response : result.1 with
        | none =>
            simp only [Option.elim_none]
            exact isQueryBoundP_pure _ _ _
        | some reply =>
            simp only [Option.elim_some]
            exact (ih reply _ (fun i => (split i).2 reply) result.2 (after result supported reply response).1).mono
              (Nat.le_sub_of_add_le' (after result supported reply response).2)
      have combined := isQueryBoundP_bind costBound rest
      rw [Nat.add_sub_cancel' costLe] at combined
      exact combined

end BeaconcryptCore.Computational.PqxdhServerAuthCtxStop

end ProgramBoundsSection

section StoppedBoundsSection

open OracleComp OracleSpec ENNReal
set_option autoImplicit false

namespace BeaconcryptCore.Computational.PqxdhServerAuthCtxStop
open PqxdhServerAuthExperiment PqxdhServerAuthEntryFactor PqxdhServerAuthPendingBudget PqxdhServerAuthGapDh
variable {KemSK τ State : Type}

/-- The executable control invariant contains only allocation coordinates and the unique selected pending handle. -/
def ControlValid (view : State → FlatState KemSK τ) (state : State × Option Nat) : Prop :=
  Tracked (view state.1).2.1 state.2 ∧ Below (view state.1)

/-- Separate attempted-call bills for selected sealing and raw opening. Other component and source resource classes remain separately charged. -/
def callbackBill (raw : Bool) (query : ServerAuthSpec.Domain) (state : FlatState KemSK τ) : Nat :=
  if raw then rawBill query state.1 else buildBill query state

/-- Each selected callback class has its own remaining source reservation. -/
def callbackReserve (raw : Bool) (state : FlatState KemSK τ) (first : Option Nat) : Nat :=
  if raw then initSentFlag state.1 else buildReserve state.1 first

/-- Immediate callback work is charged even if the component itself refuses before a normal source return. -/
theorem callbackBill_le (raw : Bool) (query : ServerAuthSpec.Domain) (state : FlatState KemSK τ)
    (first : Option Nat) (tracked : Tracked state.2.1 first) :
    callbackBill raw query state ≤ callbackReserve raw state first := by
  cases raw
  · exact buildBill_le query state first tracked
  · exact rawBill_le query state.1

/-- A completed original source step supplies both future control and the exact selected-callback reservation. -/
theorem checkpoint_budget (raw : Bool) (query : ServerAuthSpec.Domain) (before after : FlatState KemSK τ)
    (first : Option Nat) (tracked : Tracked before.2.1 first) (below : Below before)
    (resources : ResourceStep query before.1 after.1) (marks : MarkStep query before after)
    (reply answer : ServerAuthSpec.Range query)
    (continues : (checkpoint query before.1.sessions after.2.1 first reply).1 = some answer) :
    Tracked after.2.1 (checkpoint query before.1.sessions after.2.1 first reply).2 ∧ Below after ∧
      callbackBill raw query before + callbackReserve raw after (checkpoint query before.1.sessions after.2.1 first reply).2 ≤
        callbackReserve raw before first := by
  have control := checkpoint_control query before after first tracked (below.fresh before) marks reply
  simp only [continues] at control
  refine ⟨control, below.step query before after resources marks, ?_⟩
  cases raw <;> simp only [callbackBill, callbackReserve, Bool.false_eq_true, ↓reduceIte]
  · have paid := build_potential_step query before after first tracked (below.fresh before) resources reply
    simpa only [continues, Option.isSome_some, ↓reduceIte] using paid
  · exact raw_potential_step query before.1 after.1 resources true

/-- Whole optional-program selected-call bound. The premises are exact operational footprints and immediate oracle bills, to be supplied by the concrete handler; no security event, fresh nonce or successful source run is assumed. -/
theorem stopped_callback_bound {ι : Type} {spec : OracleSpec ι}
    (view : State → FlatState KemSK τ)
    (handler : QueryImpl ServerAuthSpec (OptionT (StateT State (OracleComp spec))))
    (normal : ∀ query before, ∀ result ∈ support ((handler query).run before),
      ∀ reply, result.1 = some reply →
        ResourceStep query (view before).1 (view result.2).1 ∧ MarkStep query (view before) (view result.2))
    (raw : Bool) (target : ι → Prop) [DecidablePred target]
    (calls : ∀ query state, ((handler query).run state).IsQueryBoundP target (callbackBill raw query (view state)))
    {Result : Type} (client : OracleComp ServerAuthSpec Result) (state : State × Option Nat)
    (valid : ControlValid view state) :
    (((simulateQ (stopped (fun state => (view state).1.sessions) (fun state => (view state).2.1) handler) client).run).run state).IsQueryBoundP
      target (callbackReserve raw (view state.1) state.2) := by
  classical
  apply optional_potential_invariant _ (ControlValid view) (fun (i : Fin 0) => Fin.elim0 i) target
    (fun _ state => callbackReserve raw (view state.1) state.2) ?_ client (fun i => Fin.elim0 i) (fun i => Fin.elim0 i) state valid
  intro query before budget invariant _
  refine ⟨callbackBill raw query (view before.1), ?_, callbackBill_le raw query (view before.1) before.2 invariant.1, ?_⟩
  · rw [stopped_step]
    simpa only [isQueryBoundP_map_iff] using calls query before.1
  · intro result supported answer continues
    rw [stopped_step] at supported
    simp only [support_map, Set.mem_image] at supported
    obtain ⟨original, originalSupported, rfl⟩ := supported
    cases reply : original.1 with
    | none =>
        simp only [observe, reply] at continues
        cases continues
    | some value =>
        simp only [observe, reply] at continues ⊢
        have footprint := normal query before.1 original originalSupported value reply
        have paid := checkpoint_budget raw query (view before.1) (view original.2) before.2
          invariant.1 invariant.2 footprint.1 footprint.2 value answer continues
        exact ⟨⟨paid.1, paid.2.1⟩, paid.2.2⟩

/-- Both reservations are bounded by one even in arbitrary states; correctness of allocation is required only when carrying them through execution. -/
theorem callbackReserve_le_one (raw : Bool) (state : FlatState KemSK τ) (first : Option Nat) :
    callbackReserve raw state first ≤ 1 := by
  cases raw
  · exact buildReserve_le_one state.1 first
  · exact initSentFlag_le state.1

/-- Each complete stopped adaptive program makes at most one selected call in the chosen class, counting calls performed before any refusal. Concrete handler footprints and immediate class counts are the only interface obligations. -/
theorem stopped_callback_one {ι : Type} {spec : OracleSpec ι}
    (view : State → FlatState KemSK τ)
    (handler : QueryImpl ServerAuthSpec (OptionT (StateT State (OracleComp spec))))
    (normal : ∀ query before, ∀ result ∈ support ((handler query).run before),
      ∀ reply, result.1 = some reply →
        ResourceStep query (view before).1 (view result.2).1 ∧ MarkStep query (view before) (view result.2))
    (raw : Bool) (target : ι → Prop) [DecidablePred target]
    (calls : ∀ query state, ((handler query).run state).IsQueryBoundP target (callbackBill raw query (view state)))
    {Result : Type} (client : OracleComp ServerAuthSpec Result) (state : State × Option Nat)
    (valid : ControlValid view state) :
    (((simulateQ (stopped (fun state => (view state).1.sessions) (fun state => (view state).2.1) handler) client).run).run state).IsQueryBoundP target 1 :=
  (stopped_callback_bound view handler normal raw target calls client state valid).mono
    (callbackReserve_le_one raw (view state.1) state.2)

end BeaconcryptCore.Computational.PqxdhServerAuthCtxStop

end StoppedBoundsSection

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxStop.buildReserve_le_one' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxStop.buildReserve_le_one
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxStop.buildBill_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxStop.buildBill_le
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxStop.build_potential_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxStop.build_potential_step
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxStop.rawBill_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxStop.rawBill_le
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxStop.raw_potential_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxStop.raw_potential_step
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxStop.Below.fresh' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxStop.Below.fresh
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxStop.Below.step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxStop.Below.step
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxStop.optional_potential_invariant' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxStop.optional_potential_invariant
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxStop.callbackBill_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxStop.callbackBill_le
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxStop.checkpoint_budget' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxStop.checkpoint_budget
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxStop.stopped_callback_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxStop.stopped_callback_bound
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxStop.callbackReserve_le_one' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxStop.callbackReserve_le_one
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxStop.stopped_callback_one' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxStop.stopped_callback_one
