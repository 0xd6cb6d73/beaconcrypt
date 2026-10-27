import BeaconcryptCore.Computational.PqxdhServerAuthGapDh

/-!
The actual authentication API allocates pending Server tokens once, consumes them even on failed builds, and preserves the same full state in every other operation. The finite token potential is derived from original source execution and its existing invariant. No new freshness, successful-publication or schedule restriction is imposed.
-/

open OracleComp OracleSpec
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhServerAuthPendingBudget
open PqxdhJointIdentity PqxdhJointGapDh PqxdhServerAuthExperiment

variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}

def slotWeight {α : Type} : Option α → Nat
  | none => 0
  | some _ => 1

def pendingSlots {α : Type} (limit : Nat) (slots : Nat → Option α) : Nat :=
  ∑ index ∈ Finset.range limit, slotWeight (slots index)

def pendingCount (state : GameState KemSK) : Nat := pendingSlots state.sessions state.pending

/-- The newly allocated public attempt index is outside the old finite pending-token registry. -/
theorem pending_new {α : Type} (limit : Nat) (slots : Nat → Option α) (value : Option α) :
    pendingSlots (limit + 1) (Function.update slots limit value) = pendingSlots limit slots + slotWeight value := by
  unfold pendingSlots
  rw [Finset.sum_range_succ, Function.update_self]
  congr 1
  apply Finset.sum_congr rfl
  intro index member
  rw [Function.update_of_ne (Nat.ne_of_lt (Finset.mem_range.mp member))]

/-- A missing new token costs zero and a present new token costs one. -/
theorem slotWeight_le {α : Type} (value : Option α) : slotWeight value ≤ 1 := by
  cases value <;> simp [slotWeight]

/-- Clearing an allocated slot removes exactly its previous token weight, even if later sealing or publication failed. -/
theorem pending_clear {α : Type} (limit : Nat) (slots : Nat → Option α) (index : Nat) (inside : index < limit) :
    pendingSlots limit (Function.update slots index none) + slotWeight (slots index) = pendingSlots limit slots := by
  unfold pendingSlots
  simp only [Function.apply_update (fun _ value => slotWeight value) slots index none,
    Finset.sum_update_of_mem (Finset.mem_range.mpr inside)]
  have split : (∑ i ∈ Finset.range limit, slotWeight (slots i)) = slotWeight (slots index) +
      ∑ i ∈ Finset.range limit \ {index}, slotWeight (slots i) := by
    simpa only [Function.update_eq_self] using Finset.sum_update_of_mem
      (Finset.mem_range.mpr inside) (fun i => slotWeight (slots i)) (slotWeight (slots index))
  rw [split]
  simp only [slotWeight, Nat.zero_add, Nat.add_comm]

/-- Merely exposing the next finite index can add at most one existing slot weight. -/
theorem pending_extend {α : Type} (limit : Nat) (slots : Nat → Option α) :
    pendingSlots (limit + 1) slots = pendingSlots limit slots + slotWeight (slots limit) := by
  exact Finset.sum_range_succ _ _

/-- An actual accept allocates exactly one attempt and either leaves the pending map unchanged or installs its one returned token at that new index. -/
theorem accept_pending (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (publicValue : PublicChallenge) (raw : Pqxdh.Bytes) (state : GameState KemSK)
    (result : Option Nat × GameState KemSK)
    (supported : result ∈ support ((acceptOracle setup codec checks publicValue raw).run state)) :
    result.2.sessions = state.sessions + 1 ∧
      (result.2.pending = state.pending ∨ ∃ token,
        result.2.pending = Function.update state.pending state.sessions (some token)) := by
  simp only [acceptOracle, StateT.run_bind, StateT.run_get, pure_bind] at supported
  obtain ⟨collected, lifted, supported⟩ := (mem_support_bind_iff _ _ _).1 supported
  obtain ⟨_, same⟩ := liftCoins_mem _ _ _ lifted
  simp only [StateT.run_set, pure_bind, same] at supported
  cases hc : collected.1.1 with
  | none =>
      simp only [hc, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
      subst supported
      exact ⟨rfl, Or.inl rfl⟩
  | some input =>
      simp only [hc, StateT.run_bind, mem_support_bind_iff] at supported
      obtain ⟨returned, derived, supported⟩ := supported
      obtain ⟨consumed, extra, eq, _, _⟩ := client_run state.sessions (binding setup publicValue) input _ returned derived
      have sessionsEq : returned.2.sessions = state.sessions + 1 := by rw [eq]
      have pendingEq : returned.2.pending = state.pending := by rw [eq]
      rcases returned with ⟨outcome, after⟩
      dsimp only at sessionsEq pendingEq
      rcases outcome with (_ | token) | error | _
      all_goals simp only [StateT.run_bind, StateT.run_modify, pure_bind, StateT.run_pure,
        support_pure, Set.mem_singleton_iff] at supported
      all_goals subst supported
      · exact ⟨sessionsEq, Or.inl pendingEq⟩
      · exact ⟨sessionsEq, Or.inr ⟨token, by simp only [pendingEq]⟩⟩
      · exact ⟨sessionsEq, Or.inl pendingEq⟩
      · exact ⟨sessionsEq, Or.inl pendingEq⟩

/-- Every actual accept, including rejection, adds at most one unit to the pending-build potential. -/
theorem accept_pending_count (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (publicValue : PublicChallenge) (raw : Pqxdh.Bytes) (state : GameState KemSK)
    (result : Option Nat × GameState KemSK)
    (supported : result ∈ support ((acceptOracle setup codec checks publicValue raw).run state)) :
    pendingCount result.2 ≤ pendingCount state + 1 := by
  obtain ⟨sessionsEq, old | ⟨token, installed⟩⟩ := accept_pending setup codec checks publicValue raw state result supported
  · simp only [pendingCount, sessionsEq, old, pending_extend]
    exact Nat.add_le_add_left (slotWeight_le _) _
  · simp only [pendingCount, sessionsEq, installed, pending_new, slotWeight, le_refl]

/-- Every build disposes of precisely the requested pending token, independently of every optional or diagnostic tail result. -/
theorem build_pending (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (session : Nat) (payload : Option Pqxdh.Bytes) (state : GameState KemSK)
    (result : Option PqxdhServerRegistrationPublication.Response × GameState KemSK)
    (supported : result ∈ support ((buildOracle setup codec checks session payload).run state)) :
    result.2.sessions = state.sessions ∧ result.2.pending = Function.update state.pending session none := by
  simp only [buildOracle, StateT.run_bind, StateT.run_get, pure_bind] at supported
  cases hp : state.pending session with
  | none =>
      simp only [hp, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
      subst supported
      exact ⟨rfl, by rw [← hp, Function.update_eq_self]⟩
  | some token =>
      simp only [hp, StateT.run_bind, mem_support_bind_iff] at supported
      obtain ⟨tail, lifted, supported⟩ := supported
      obtain ⟨_, same⟩ := liftCoins_mem _ _ _ lifted
      simp only [same, StateT.run_set, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
      obtain ⟨_, rfl, rfl⟩ := supported
      exact ⟨rfl, rfl⟩

/-- A reachable present token pays for one complete build attempt even when that attempt fails; an absent token pays zero. -/
theorem build_pending_count (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (publicValue : PublicChallenge) (session : Nat) (payload : Option Pqxdh.Bytes) (state : GameState KemSK)
    (invariant : GameInv Reader Response setup publicValue state)
    (result : Option PqxdhServerRegistrationPublication.Response × GameState KemSK)
    (supported : result ∈ support ((buildOracle setup codec checks session payload).run state)) :
    pendingCount result.2 + slotWeight (state.pending session) = pendingCount state := by
  obtain ⟨sessionsEq, pendingEq⟩ := build_pending setup codec checks session payload state result supported
  simp only [pendingCount, sessionsEq, pendingEq]
  cases hp : state.pending session with
  | none => rw [slotWeight, Nat.add_zero, ← hp, Function.update_eq_self]
  | some token => simpa only [hp] using pending_clear state.sessions state.pending session (invariant.pendingBelow session token hp)

/-- The actual complete Beacon finish changes neither Server attempt allocation nor any pending Server token. -/
theorem finish_pending (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (publicValue : PublicChallenge) (beaconSeed : IdentitySeed) (raw : Pqxdh.Bytes)
    (state : GameState KemSK) (result : Option Pqxdh.Bytes × GameState KemSK)
    (supported : result ∈ support ((finishOracle setup codec publicValue beaconSeed raw).run state)) :
    result.2.sessions = state.sessions ∧ result.2.pending = state.pending := by
  simp only [finishOracle, StateT.run_bind, StateT.run_get, pure_bind] at supported
  cases hphase : state.beacon.beacon.phase with
  | initSent control prekey oneTime kem =>
      simp only [hphase, StateT.run_bind, mem_support_bind_iff] at supported
      obtain ⟨staged, stageRun, supported⟩ := supported
      obtain ⟨cache, extra, stagedEq, _⟩ := stage_run setup codec beaconSeed
        publicValue control state.beacon.beacon.identity oneTime kem raw state staged stageRun
      simp only [StateT.run_get, StateT.run_set, StateT.run_pure, support_pure,
        Set.mem_singleton_iff] at supported
      obtain ⟨_, rfl, _, rfl, rfl⟩ := supported
      rw [stagedEq]
      exact ⟨rfl, rfl⟩
  | _ =>
      simp only [hphase, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
      subst supported
      exact ⟨rfl, rfl⟩

/-- Every other original capability preserves the allocated pending-token registry, including the whole Beacon finish and post-registration state reveal. -/
theorem handler_pending_quiet (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (publicValue : PublicChallenge) (beaconSeed : IdentitySeed) (query : ServerAuthSpec.Domain)
    (notAccept : ¬ IsAcceptQuery query) (notBuild : ∀ index payload, query ≠ .inr (.build index payload))
    (state : GameState KemSK) (result : ServerAuthSpec.Range query × GameState KemSK)
    (supported : result ∈ support ((authHandler setup codec checks publicValue beaconSeed query).run state)) :
    result.2.sessions = state.sessions ∧ result.2.pending = state.pending := by
  rcases query with coin | query
  · rw [forward_support _ _ _ supported]
    exact ⟨rfl, rfl⟩
  cases query with
  | accept raw => exact (notAccept trivial).elim
  | build index payload => exact (notBuild index payload rfl).elim
  | finish raw => exact finish_pending setup codec publicValue beaconSeed raw state result supported
  | hmac key message =>
      change result ∈ support ((hmacOracle key message).run state) at supported
      simp only [hmacOracle] at supported
      split_ifs at supported
      · obtain ⟨middle, first, rest⟩ := run_bind_support _ _ _ _ supported
        rw [record_run, support_pure, Set.mem_singleton_iff] at first
        subst first
        rw [forward_support _ _ _ rest]
        exact ⟨rfl, rfl⟩
      · rw [forward_support _ _ _ supported]
        exact ⟨rfl, rfl⟩
  | hash bytes =>
      obtain ⟨cache, same⟩ := hashOracle_step bytes state result supported
      rw [same]
      exact ⟨rfl, rfl⟩
  | reveal keyId =>
      change result ∈ support (pure _ : OracleComp PqxdhJointDhExtractRoot.RootSpec _) at supported
      rw [support_pure, Set.mem_singleton_iff] at supported
      subst supported
      exact ⟨rfl, rfl⟩

/-- The actual eager setup starts with no pending Server build tokens. -/
theorem pending_initial (setup : Setup baseSpec KemSK) (publicValue : PublicChallenge)
    (beacon : RawCtxBeaconLifecycle.State Unit (Unit ⊕ ScalarBytes) KemSK) :
    pendingCount (initialGameState setup publicValue beacon) = 0 := by
  simp [pendingCount, pendingSlots, initialGameState]

/-- The potential is unchanged by all other actual capabilities, without restricting their replies. -/
theorem handler_pending_count_quiet (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (publicValue : PublicChallenge) (beaconSeed : IdentitySeed) (query : ServerAuthSpec.Domain)
    (notAccept : ¬ IsAcceptQuery query) (notBuild : ∀ index payload, query ≠ .inr (.build index payload))
    (state : GameState KemSK) (result : ServerAuthSpec.Range query × GameState KemSK)
    (supported : result ∈ support ((authHandler setup codec checks publicValue beaconSeed query).run state)) :
    pendingCount result.2 = pendingCount state := by
  obtain ⟨sessionsEq, pendingEq⟩ := handler_pending_quiet setup codec checks publicValue beaconSeed query
    notAccept notBuild state result supported
  simp only [pendingCount, sessionsEq, pendingEq]

section Potential
variable {ι₁ ι₂ : Type} {spec₁ : OracleSpec ι₁} {spec₂ : OracleSpec ι₂} {σ : Type}

/-- A stateful resource potential may use an operational invariant, provided every supported original step preserves it. The complete result-dependent continuation remains in the induction. -/
theorem run_potential_invariant {k : Nat} (impl : QueryImpl spec₁ (StateT σ (OracleComp spec₂)))
    (invariant : σ → Prop) (p : Fin k → ι₁ → Prop) [∀ i, DecidablePred (p i)]
    (target : ι₂ → Prop) [DecidablePred target] (bound : (Fin k → Nat) → σ → Nat)
    (step : ∀ query state (budget : Fin k → Nat), invariant state →
      (∀ i, p i query → 0 < budget i) →
      ∃ cost, ((impl query).run state).IsQueryBoundP target cost ∧ cost ≤ bound budget state ∧
        ∀ result ∈ support ((impl query).run state), invariant result.2 ∧
          cost + bound (fun i => if p i query then budget i - 1 else budget i) result.2 ≤ bound budget state)
    {α : Type} (work : OracleComp spec₁ α) (budget : Fin k → Nat)
    (bounded : ∀ i, work.IsQueryBoundP (p i) (budget i)) (state : σ) (valid : invariant state) :
    ((simulateQ impl work).run state).IsQueryBoundP target (bound budget state) := by
  induction work using OracleComp.inductionOn generalizing budget state with
  | pure value => simp [simulateQ_pure]
  | query_bind query next ih =>
      have split := fun i => (isQueryBoundP_query_bind_iff (p i) query next (budget i)).mp (bounded i)
      obtain ⟨cost, costBound, costLe, after⟩ := step query state budget valid
        (fun i found => (split i).1.resolve_left (not_not.mpr found))
      rw [simulateQ_query_bind, StateT.run_bind]
      have rest : ∀ result ∈ support ((impl query).run state),
          ((simulateQ impl (next result.1)).run result.2).IsQueryBoundP target (bound budget state - cost) :=
        fun result member => (ih result.1 _ (fun i => (split i).2 result.1) result.2 (after result member).1).mono
          (Nat.le_sub_of_add_le' (after result member).2)
      have combined := isQueryBoundP_bind costBound rest
      rw [Nat.add_sub_cancel' costLe] at combined
      exact combined

end Potential

end BeaconcryptCore.Computational.PqxdhServerAuthPendingBudget

/-! ## Checked theorem dependencies -/

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPendingBudget.pending_new' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPendingBudget.pending_new

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPendingBudget.slotWeight_le' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPendingBudget.slotWeight_le

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPendingBudget.pending_clear' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPendingBudget.pending_clear

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPendingBudget.pending_extend' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPendingBudget.pending_extend

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPendingBudget.accept_pending' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPendingBudget.accept_pending

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPendingBudget.accept_pending_count' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPendingBudget.accept_pending_count

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPendingBudget.build_pending' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPendingBudget.build_pending

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPendingBudget.build_pending_count' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPendingBudget.build_pending_count

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPendingBudget.finish_pending' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPendingBudget.finish_pending

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPendingBudget.handler_pending_quiet' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPendingBudget.handler_pending_quiet

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPendingBudget.pending_initial' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPendingBudget.pending_initial

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPendingBudget.handler_pending_count_quiet' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPendingBudget.handler_pending_count_quiet

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPendingBudget.run_potential_invariant' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPendingBudget.run_potential_invariant
