import BeaconcryptCore.Computational.PqxdhRegistrationJointBeaconFinishOnceOwners

/-!
# The KEM creation counter of the router (item 2, stage T, router)

A Beacon owner receives its KEM creation index from the KEM router's creation counter: the router answers a creation with the current value of `created` and increments it, and no other request changes it (`PqxdhDynamicKemRouter.router` after the challenge and `PqxdhDynamicKemRouter.source` in the stopped prefix; `router_counts`, `source_counts`). So the router hands out every index at most once. This module states that fact and carries it through the joint identity/KEM wrapper (`PqxdhDynamicKemJointRouter.combine`) and through the forwarding layers above it:

- `StepMono`: a measure that no step of an optional stateful interpreter decreases; it passes through a stateless layer above (`stepMono_compose`), through `fwdOption` (`stepMono_fwdOption`) and through `composeOpt` (`stepMono_composeOpt`);
- `combine_mono`: the creation counter is such a measure for the joint router;
- `client_created`: the joint creation client `PqxdhRegistrationJointCreation.client`, run against the joint router, returns a born owner whose KEM index is the counter before the request, and leaves the counter incremented by one;
- `option_lift_state`: an interpreter that answers every request of a program by the router's step, keeping an extra state component and lifting into a larger interface, runs the program as the router does.

These are structural facts about the executable router; they charge nothing.
-/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc

set_option autoImplicit false
set_option maxRecDepth 100000

namespace BeaconcryptCore.Computational.PqxdhRegistrationJointBeaconFinishOnce

open PqxdhKemIndCca
open PqxdhRegistrationJointKemPostSkeleton (fwd fwdOption fwdOption_inl fwdOption_inr)

/-! ### Measures that no step decreases -/

section Mono

variable {ι ι' σ : Type} {spec : OracleSpec.{0, 0} ι} {spec' : OracleSpec.{0, 0} ι'}

/-- A measure that no step of an optional stateful interpreter decreases. -/
def StepMono (handler : QueryImpl spec (OptionT (StateT σ (OracleComp spec')))) (μ : σ → ℕ) : Prop :=
  ∀ query state, ∀ result ∈ support (((handler query).run).run state), μ state ≤ μ result.2

theorem stepMono_compose {ι'' : Type} {spec'' : OracleSpec.{0, 0} ι''}
    (low : QueryImpl spec' (OptionT (StateT σ (OracleComp spec'')))) (μ : σ → ℕ) (mono : StepMono low μ)
    (pre : QueryImpl spec (OracleComp spec')) : StepMono (low ∘ₛ pre) μ := by
  intro query state result member
  rw [QueryImpl.apply_compose] at member
  exact option_monotone low μ mono (pre query) state result member

theorem stepMono_fwdOption {ιT : Type} {T : OracleSpec.{0, 0} ιT}
    (layer : QueryImpl spec (OptionT (StateT σ (OracleComp spec')))) (μ : σ → ℕ) (mono : StepMono layer μ) :
    StepMono (fwdOption (T := T) layer) μ := by
  intro query state result member
  rcases query with query | query
  · rw [fwdOption_inl] at member
    exact mono query state result (mem_support_of_mem_support_liftComp _ _ result member)
  · rw [fwdOption_inr, support_map] at member
    obtain ⟨_, -, rfl⟩ := member
    exact le_rfl

theorem stepMono_composeOpt {ιE ιM ιB S J : Type} {E : OracleSpec.{0, 0} ιE} {M : OracleSpec.{0, 0} ιM}
    {B : OracleSpec.{0, 0} ιB} (top : QueryImpl E (StateT S (OracleComp M)))
    (low : QueryImpl M (OptionT (StateT J (OracleComp B)))) (μ : J → ℕ) (mono : StepMono low μ) :
    StepMono (composeOpt top low) (fun state => μ state.2) := by
  intro query state result member
  rw [composeOpt_step, support_map] at member
  obtain ⟨inner, reached, rfl⟩ := member
  exact option_monotone low μ mono _ state.2 inner reached

end Mono

/-! ### Answering a program by the router's steps with an extra state component -/

section Lift

variable {ι ι' ι'' S J α : Type} {spec : OracleSpec.{0, 0} ι} {spec' : OracleSpec.{0, 0} ι'}
  {spec'' : OracleSpec.{0, 0} ι''}

/-- An interpreter that answers each request by the step of `router`, lifted into a larger interface and keeping the extra state component, runs every program as `router` does. -/
theorem option_lift_state [MonadLiftT (OracleQuery spec') (OracleQuery spec'')]
    (router : QueryImpl spec (OptionT (StateT J (OracleComp spec'))))
    (handler : QueryImpl spec (OptionT (StateT (S × J) (OracleComp spec''))))
    (agrees : ∀ query extra lower, ((handler query).run).run (extra, lower) =
      (fun result => (result.1, (extra, result.2))) <$> (((router query).run).run lower).liftComp spec'')
    (work : OracleComp spec α) (extra : S) (lower : J) :
    ((simulateQ handler work).run).run (extra, lower) =
      (fun result => (result.1, (extra, result.2))) <$> (((simulateQ router work).run).run lower).liftComp spec'' := by
  induction work using OracleComp.inductionOn generalizing lower with
  | pure value => simp
  | query_bind query next ih =>
      rw [option_run_bind, option_run_bind, agrees, liftComp_bind, map_bind, bind_map_left]
      apply bind_congr
      rintro ⟨_ | reply, after⟩
      · simp
      · exact ih reply after

end Lift

/-! ### The KEM creation counter -/

section Counter

variable {ι ι' : Type} {baseSpec : OracleSpec ι} {spec' : OracleSpec.{0, 0} ι'} {KemSK : Type}

/-- The KEM creation counter of the joint router state. -/
def created (state : PqxdhDynamicKemJointSource.State KemSK) : Nat := state.2.created

/-- One while the router has not yet handed out the KEM index `selected`, that is while its counter is at most `selected`. -/
def pending (selected counter : Nat) : Nat := if counter ≤ selected then 1 else 0

theorem pending_anti (selected : Nat) {counter counter' : Nat} (le : counter ≤ counter') :
    pending selected counter' ≤ pending selected counter := by
  unfold pending
  split_ifs <;> omega

theorem pending_step (selected counter : Nat) :
    (if counter = selected then 1 else 0) + pending selected (counter + 1) = pending selected counter := by
  unfold pending
  split_ifs <;> omega

theorem pending_le_one (selected counter : Nat) : pending selected counter ≤ 1 := by
  unfold pending
  split_ifs <;> omega

/-- A KEM pool interpreter whose creation answers with the creation counter and increments it, and whose steps never decrease the counter. -/
def CountsCreates (pool : QueryImpl (PqxdhLiveKemBirth.PoolSpec KemSK)
    (OptionT (StateT (PqxdhDynamicKemRouter.State KemSK) (OracleComp spec')))) : Prop :=
  (∀ state, ∀ result ∈ support (((pool .create).run).run state), ∀ reply, result.1 = some reply →
    reply.1 = state.created ∧ result.2.created = state.created + 1) ∧
  (∀ query state, ∀ result ∈ support (((pool query).run).run state), state.created ≤ result.2.created)

/-- The executable router (before and after the challenge) answers a creation with its counter and increments it. -/
theorem router_counts
    (decapsulation : PqxdhDynamicKemRouter.Reservation KemSK → Nat → MlKem768Ciphertext →
      OracleComp (MlKemCCAOracleSpec baseSpec) (Option MlKemSharedSecret))
    (selected : Nat) (reservation : PqxdhDynamicKemRouter.Reservation KemSK) :
    CountsCreates (PqxdhDynamicKemRouter.router decapsulation selected reservation) := by
  refine ⟨fun state result member reply found => ?_, fun query state result member => ?_⟩
  · simp only [PqxdhDynamicKemRouter.router, OptionT.run_mk, StateT.run] at member
    split at member
    · simp only [support_pure, Set.mem_singleton_iff] at member
      rw [member] at found
      cases found
    · simp only [support_pure, Set.mem_singleton_iff] at member
      rw [member] at found ⊢
      cases found
      exact ⟨rfl, rfl⟩
  · cases query with
    | create =>
        simp only [PqxdhDynamicKemRouter.router, OptionT.run_mk, StateT.run] at member
        split at member <;>
        · simp only [support_pure, Set.mem_singleton_iff] at member
          subst member
          simp [PqxdhDynamicKemRouter.record]
    | decapsulate index ciphertext =>
        simp only [PqxdhDynamicKemRouter.router, OptionT.run_mk, StateT.run, mem_support_bind_iff, support_pure,
          Set.mem_singleton_iff] at member
        obtain ⟨_, -, rfl⟩ := member
        simp [PqxdhDynamicKemRouter.record]
    | reveal index =>
        simp only [PqxdhDynamicKemRouter.router, OptionT.run_mk, StateT.run] at member
        split at member
        · simp only [support_pure, Set.mem_singleton_iff] at member
          subst member
          simp [PqxdhDynamicKemRouter.record]
        · split at member <;>
          · simp only [support_pure, Set.mem_singleton_iff] at member
            subst member
            simp [PqxdhDynamicKemRouter.record]

/-- The stopped source interpreter of the prefix answers a creation with its counter and increments it. -/
theorem source_counts (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (selected : Nat)
    (pairs : List (MlKem768PublicKey × KemSK)) :
    CountsCreates (PqxdhDynamicKemRouter.source baseImpl kem selected pairs) := by
  refine ⟨fun state result member reply found => ?_, fun query state result member => ?_⟩
  · simp only [PqxdhDynamicKemRouter.source, OptionT.run_mk, StateT.run] at member
    split at member
    · simp only [support_pure, Set.mem_singleton_iff] at member
      rw [member] at found
      cases found
    · simp only [support_pure, Set.mem_singleton_iff] at member
      rw [member] at found ⊢
      cases found
      exact ⟨rfl, rfl⟩
  · cases query with
    | create =>
        simp only [PqxdhDynamicKemRouter.source, OptionT.run_mk, StateT.run] at member
        split at member <;>
        · simp only [support_pure, Set.mem_singleton_iff] at member
          subst member
          simp [PqxdhDynamicKemRouter.record]
    | decapsulate index ciphertext =>
        simp only [PqxdhDynamicKemRouter.source, OptionT.run_mk, StateT.run] at member
        split at member
        · simp only [pure_bind, support_pure, Set.mem_singleton_iff] at member
          subst member
          simp [PqxdhDynamicKemRouter.record]
        · simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at member
          obtain ⟨_, -, rfl⟩ := member
          simp [PqxdhDynamicKemRouter.record]
    | reveal index =>
        simp only [PqxdhDynamicKemRouter.source, OptionT.run_mk, StateT.run] at member
        split at member
        · simp only [support_pure, Set.mem_singleton_iff] at member
          subst member
          simp [PqxdhDynamicKemRouter.record]
        · split at member <;>
          · simp only [support_pure, Set.mem_singleton_iff] at member
            subst member
            simp [PqxdhDynamicKemRouter.record]

variable {m : Type → Type} [Monad m] [LawfulMonad m]

/-- The joint wrapper never decreases the KEM creation counter. -/
theorem combine_mono (coins : {X : Type} → ProbComp X → OracleComp spec' X) (primitives : PqxdhJointIdentity.Primitives)
    (pool : QueryImpl (PqxdhLiveKemBirth.PoolSpec KemSK)
      (OptionT (StateT (PqxdhDynamicKemRouter.State KemSK) (OracleComp spec'))))
    (counts : CountsCreates pool) : StepMono (PqxdhDynamicKemJointRouter.combine coins primitives pool) created := by
  intro query state result member
  rcases query with identity | (coin | query)
  · simp only [PqxdhDynamicKemJointRouter.combine, OptionT.run_mk, StateT.run, support_map] at member
    obtain ⟨_, -, rfl⟩ := member
    exact le_rfl
  · simp only [PqxdhDynamicKemJointRouter.combine, OptionT.run_mk, StateT.run, support_map] at member
    obtain ⟨_, -, rfl⟩ := member
    exact le_rfl
  · simp only [PqxdhDynamicKemJointRouter.combine, OptionT.run_mk, StateT.run, support_map] at member
    obtain ⟨inner, reached, rfl⟩ := member
    exact counts.2 query state.2 inner reached

/-- Coins never stop the joint wrapper and keep its whole state. -/
theorem coins_keep (coins : {X : Type} → ProbComp X → OracleComp spec' X) (primitives : PqxdhJointIdentity.Primitives)
    (pool : QueryImpl (PqxdhLiveKemBirth.PoolSpec KemSK)
      (OptionT (StateT (PqxdhDynamicKemRouter.State KemSK) (OracleComp spec')))) {α : Type} (work : ProbComp α)
    (state : PqxdhDynamicKemJointSource.State KemSK) :
    ∀ result ∈ support (((simulateQ (PqxdhDynamicKemJointRouter.combine coins primitives pool)
        (PqxdhLiveKemBirth.coins (KemSK := KemSK) work)).run).run state), result.2 = state := by
  unfold PqxdhLiveKemBirth.coins
  rw [← QueryImpl.simulateQ_compose]
  refine option_invariant _ (fun current => current = state) (fun query current holds result member => ?_) work state rfl
  rw [QueryImpl.apply_compose, simulateQ_spec_query] at member
  simp only [PqxdhDynamicKemJointRouter.combine, OptionT.run_mk, StateT.run, support_map] at member
  obtain ⟨_, -, rfl⟩ := member
  exact holds

/-- The joint creation client, run against the joint wrapper, returns a born owner whose KEM index is the creation counter before the request, and leaves the counter incremented by one. -/
theorem client_created (coins : {X : Type} → ProbComp X → OracleComp spec' X)
    (primitives : PqxdhJointIdentity.Primitives)
    (pool : QueryImpl (PqxdhLiveKemBirth.PoolSpec KemSK)
      (OptionT (StateT (PqxdhDynamicKemRouter.State KemSK) (OracleComp spec'))))
    (counts : CountsCreates pool) (state : PqxdhDynamicKemJointSource.State KemSK) :
    ∀ result ∈ support (((simulateQ (PqxdhDynamicKemJointRouter.combine coins primitives pool)
        (PqxdhRegistrationJointCreation.client (KemSK := KemSK))).run).run state), ∀ value,
      result.1 = some (some value) → value.kemIndex = created state ∧ created result.2 = created state + 1 := by
  intro result member value found
  unfold PqxdhRegistrationJointCreation.client at member
  rw [option_run_bind, mem_support_bind_iff] at member
  obtain ⟨first, firstReached, member⟩ := member
  have kept : first.2.2 = state.2 := by
    simp only [PqxdhDynamicKemJointRouter.combine, OptionT.run_mk, StateT.run, support_map] at firstReached
    obtain ⟨_, -, rfl⟩ := firstReached
    rfl
  rcases first with ⟨_ | identity, afterIdentity⟩
  · simp only [support_pure, Set.mem_singleton_iff] at member
    rw [member] at found
    cases found
  · dsimp only at member kept
    cases identity with
    | none =>
        simp only [simulateQ_pure, OptionT.run_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at member
        rw [member] at found
        cases found
    | some identity =>
        dsimp only at member
        rw [option_simulate_bind, mem_support_bind_iff] at member
        obtain ⟨second, secondReached, member⟩ := member
        have same := coins_keep coins primitives pool _ afterIdentity second secondReached
        rcases second with ⟨_ | prekey, afterCoins⟩
        · simp only [support_pure, Set.mem_singleton_iff] at member
          rw [member] at found
          cases found
        · dsimp only at member same
          rw [option_run_bind, mem_support_bind_iff] at member
          obtain ⟨third, thirdReached, member⟩ := member
          rcases third with ⟨_ | pair, afterCreate⟩
          · simp only [support_pure, Set.mem_singleton_iff] at member
            rw [member] at found
            cases found
          · simp only [simulateQ_pure, OptionT.run_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at member
            rw [member] at found
            simp only [Option.some.injEq] at found
            subst found
            simp only [PqxdhDynamicKemJointRouter.combine, OptionT.run_mk, StateT.run, support_map] at thirdReached
            obtain ⟨inner, reached, equal⟩ := thirdReached
            simp only [Prod.mk.injEq] at equal
            obtain ⟨replyEq, stateEq⟩ := equal
            have count := counts.1 afterCoins.2 inner reached pair replyEq
            subst same
            rw [member]
            refine ⟨count.1.trans (by rw [kept]; rfl), ?_⟩
            simp only [created, ← stateEq]
            rw [count.2, kept]

end Counter

end BeaconcryptCore.Computational.PqxdhRegistrationJointBeaconFinishOnce

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointBeaconFinishOnce.stepMono_compose' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointBeaconFinishOnce.stepMono_compose

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointBeaconFinishOnce.stepMono_fwdOption' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointBeaconFinishOnce.stepMono_fwdOption

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointBeaconFinishOnce.stepMono_composeOpt' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointBeaconFinishOnce.stepMono_composeOpt

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointBeaconFinishOnce.option_lift_state' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointBeaconFinishOnce.option_lift_state

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointBeaconFinishOnce.pending_anti' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointBeaconFinishOnce.pending_anti

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointBeaconFinishOnce.pending_step' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointBeaconFinishOnce.pending_step

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointBeaconFinishOnce.pending_le_one' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointBeaconFinishOnce.pending_le_one

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointBeaconFinishOnce.router_counts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointBeaconFinishOnce.router_counts

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointBeaconFinishOnce.source_counts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointBeaconFinishOnce.source_counts

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointBeaconFinishOnce.combine_mono' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointBeaconFinishOnce.combine_mono

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointBeaconFinishOnce.coins_keep' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointBeaconFinishOnce.coins_keep

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointBeaconFinishOnce.client_created' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointBeaconFinishOnce.client_created
