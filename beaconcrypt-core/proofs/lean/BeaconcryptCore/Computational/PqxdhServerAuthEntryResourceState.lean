import BeaconcryptCore.Computational.PqxdhServerAuthEntryServices
import BeaconcryptCore.Computational.PqxdhServerAuthBodyCosts

open OracleComp OracleSpec
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
set_option autoImplicit false

namespace BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor
open PqxdhServerAuthExperiment PqxdhJointIdentity PqxdhJointGapDh
open PqxdhServerAuthPendingBudget PqxdhServerAuthGapDh
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response τ : Type}

/-- Resource validity needs only allocated pending handles, not the security event or the selected table's refusal flag. -/
def ResourceValid (game : GameState KemSK) : Prop :=
  ∀ index token, game.pending index = some token → index < game.sessions

/-- Every root reply preserves allocation and the one-shot Beacon phase, installing at most one token at the current attempt. -/
theorem afterDerive_resources (setup : Setup baseSpec KemSK) (publicValue : PublicChallenge)
    (index : Nat) (input : PqxdhServerRootPreparation.Inputs Reader ScalarBytes PeerEncoding)
    (reply : Reply) (game : GameState KemSK) :
    (afterDerive setup publicValue index input reply game).2.sessions = game.sessions ∧
    (afterDerive setup publicValue index input reply game).2.beacon = game.beacon ∧
    ((afterDerive setup publicValue index input reply game).2.pending = game.pending ∨
      ∃ token, (afterDerive setup publicValue index input reply game).2.pending =
        Function.update game.pending index (some token)) := by
  cases reply
  all_goals exact ⟨rfl, rfl, by first | exact Or.inl rfl | exact Or.inr ⟨_, rfl⟩⟩

/-- Every attempted accept allocates one index and creates at most one pending token, even under arbitrary selected-entry services. -/
theorem acceptStep_resources (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (publicValue : PublicChallenge) (services : Services Response τ)
    (raw : Pqxdh.Bytes) (state : FlatState KemSK τ)
    (result : Option Nat × FlatState KemSK τ)
    (supported : result ∈ support ((acceptStep setup codec checks publicValue services raw).run state)) :
    result.2.1.sessions = state.1.sessions + 1 ∧ result.2.1.beacon = state.1.beacon ∧
      (result.2.1.pending = state.1.pending ∨ ∃ token,
        result.2.1.pending = Function.update state.1.pending state.1.sessions (some token)) := by
  simp only [acceptStep, StateT.run, mem_support_bind_iff] at supported
  obtain ⟨collected, _, supported⟩ := supported
  cases found : collected.1 with
  | none =>
      simp only [found, support_pure, Set.mem_singleton_iff] at supported
      subst supported
      exact ⟨rfl, rfl, Or.inl rfl⟩
  | some input =>
      simp only [found] at supported
      split_ifs at supported with nonzero
      · obtain ⟨derived, _, supported⟩ := (mem_support_bind_iff _ _ _).1 supported
        simp only [support_pure, Set.mem_singleton_iff] at supported
        subst supported
        exact afterDerive_resources setup publicValue state.1.sessions input derived.1 _
      · simp only [support_pure, Set.mem_singleton_iff] at supported
        subst supported
        exact ⟨rfl, rfl, Or.inl rfl⟩

/-- Every complete build consumes its selected pending token; arbitrary failure, cache and logging effects cannot allocate tokens or change the Beacon phase. -/
theorem buildStep_resources (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (services : Services Response τ) (index : Nat) (payload : Option Pqxdh.Bytes)
    (state : FlatState KemSK τ) (result : Option PqxdhServerRegistrationPublication.Response × FlatState KemSK τ)
    (supported : result ∈ support ((buildStep setup codec checks services index payload).run state)) :
    result.2.1.sessions = state.1.sessions ∧ result.2.1.beacon = state.1.beacon ∧
      result.2.1.pending = Function.update state.1.pending index none := by
  simp only [buildStep, StateT.run] at supported
  cases found : state.1.pending index with
  | none =>
      simp only [found, support_pure, Set.mem_singleton_iff] at supported
      subst supported
      exact ⟨rfl, rfl, by rw [← found, Function.update_eq_self]⟩
  | some token =>
      simp only [found, mem_support_bind_iff] at supported
      obtain ⟨built, _, supported⟩ := supported
      simp only [support_pure, Set.mem_singleton_iff] at supported
      subst supported
      exact ⟨rfl, rfl, rfl⟩

/-- Final registration checks exhaust the Beacon finish opportunity on every result and leave all Server pending handles intact. -/
theorem finishOutcome_resources (control : pqxdh.BeaconInitSent) (game : GameState KemSK)
    (staged : Option PqxdhBeaconPhase2Publication.Staged) :
    (finishOutcome control game staged).2.sessions = game.sessions ∧
    (finishOutcome control game staged).2.pending = game.pending ∧
    initSentFlag (finishOutcome control game staged).2 = 0 := by
  refine ⟨rfl, rfl, initSentFlag_zero _ ?_⟩
  rintro ⟨control', prekey, oneTime, kem, phase⟩
  exact finish_phase control game.beacon staged control' prekey oneTime kem phase

/-- The complete finish preserves pending allocation and cannot retain an active finish phase, even after a refused selected-entry derivation. -/
theorem finishStep_resources (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (publicValue : PublicChallenge) (beaconSeed : IdentitySeed) (services : Services Response τ)
    (raw : Pqxdh.Bytes) (state : FlatState KemSK τ) (result : Option Pqxdh.Bytes × FlatState KemSK τ)
    (supported : result ∈ support ((finishStep setup codec publicValue beaconSeed services raw).run state)) :
    result.2.1.sessions = state.1.sessions ∧ result.2.1.pending = state.1.pending ∧
      initSentFlag result.2.1 = 0 := by
  simp only [finishStep, StateT.run] at supported
  cases phase : state.1.beacon.beacon.phase with
  | initSent control prekey oneTime kem =>
      simp only [phase, mem_support_bind_iff] at supported
      obtain ⟨prepared, _, supported⟩ := supported
      cases found : prepared with
      | none =>
          simp only [found, support_pure, Set.mem_singleton_iff] at supported
          subst supported
          exact finishOutcome_resources control state.1 none
      | some pending =>
          simp only [found, mem_support_bind_iff] at supported
          obtain ⟨derived, _, supported⟩ := supported
          cases reply : derived.1 with
          | rejected =>
              simp only [reply, support_pure, Set.mem_singleton_iff] at supported
              subst supported
              exact finishOutcome_resources control _ none
          | root root =>
              simp only [reply, mem_support_bind_iff] at supported
              obtain ⟨staged, _, supported⟩ := supported
              simp only [support_pure, Set.mem_singleton_iff] at supported
              subst supported
              exact finishOutcome_resources control _ staged.1
          | hidden =>
              simp only [reply, mem_support_bind_iff] at supported
              obtain ⟨staged, _, supported⟩ := supported
              simp only [support_pure, Set.mem_singleton_iff] at supported
              subst supported
              exact finishOutcome_resources control _ staged.1
  | _ =>
      simp only [phase, support_pure, Set.mem_singleton_iff] at supported
      subst supported
      exact ⟨rfl, rfl, by simp only [initSentFlag, phase]⟩

/-- The resource footprint of an actual API step, ignoring no callback effects: only its allocated tokens and one-shot Beacon phase determine future random work. -/
def ResourceStep (query : ServerAuthSpec.Domain) (before after : GameState KemSK) : Prop :=
  match query with
  | .inr (.accept _) =>
      after.sessions = before.sessions + 1 ∧ after.beacon = before.beacon ∧
      (after.pending = before.pending ∨ ∃ token,
        after.pending = Function.update before.pending before.sessions (some token))
  | .inr (.build index _) =>
      after.sessions = before.sessions ∧ after.beacon = before.beacon ∧
        after.pending = Function.update before.pending index none
  | .inr (.finish _) =>
      after.sessions = before.sessions ∧ after.pending = before.pending ∧ initSentFlag after = 0
  | _ => after.sessions = before.sessions ∧ after.beacon = before.beacon ∧ after.pending = before.pending

/-- The full flattened source API supplies that footprint for every service reply, including execution after a sticky refusal. -/
theorem skeleton_resources (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (publicValue : PublicChallenge) (beaconSeed : IdentitySeed)
    (services : Services Response τ) (query : ServerAuthSpec.Domain) (state : FlatState KemSK τ)
    (result : ServerAuthSpec.Range query × FlatState KemSK τ)
    (supported : result ∈ support ((skeleton setup codec checks publicValue beaconSeed services query).run state)) :
    ResourceStep query state.1 result.2.1 := by
  rcases query with coin | query
  · simp only [skeleton, StateT.run, support_map, Set.mem_image] at supported
    obtain ⟨value, _, rfl⟩ := supported
    exact ⟨rfl, rfl, rfl⟩
  cases query with
  | accept raw => exact acceptStep_resources setup codec checks publicValue services raw state result supported
  | build index payload => exact buildStep_resources setup codec checks services index payload state result supported
  | finish raw => exact finishStep_resources setup codec publicValue beaconSeed services raw state result supported
  | hmac key bytes =>
      simp only [skeleton, hmacStep, StateT.run] at supported
      split_ifs at supported
      · obtain ⟨read, _, supported⟩ := (mem_support_bind_iff _ _ _).1 supported
        simp only [support_pure, Set.mem_singleton_iff] at supported
        subst supported
        exact ⟨rfl, rfl, rfl⟩
      · simp only [support_pure, Set.mem_singleton_iff] at supported
        subst supported
        exact ⟨rfl, rfl, rfl⟩
  | hash bytes =>
      simp only [skeleton, hashStep, StateT.run, mem_support_bind_iff] at supported
      obtain ⟨read, _, supported⟩ := supported
      simp only [support_pure, Set.mem_singleton_iff] at supported
      subst supported
      exact ⟨rfl, rfl, rfl⟩
  | reveal key =>
      simp only [skeleton, StateT.run, support_pure, Set.mem_singleton_iff] at supported
      subst supported
      exact ⟨rfl, rfl, rfl⟩

/-- Refusal instrumentation changes neither the native game nor its resource fields. -/
theorem keepHiddenBad_game {α : Type} (before : HiddenState KemSK) (result : α × HiddenState KemSK) :
    (keepHiddenBad before result).2.1.1 = result.2.1.1 := by
  unfold keepHiddenBad
  split <;> rfl

/-- The actual omitted-entry handler has the source resource footprint on all runs, before and after refusal, for arbitrary continuation services. -/
theorem hiddenHandler_resources (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (context : Context KemSK) (Q : Nat) (j : Fin (Q + 1))
    (services : Services Response HiddenTable) (query : ServerAuthSpec.Domain) (state : HiddenState KemSK)
    (result : ServerAuthSpec.Range query × HiddenState KemSK)
    (supported : result ∈ support ((hiddenHandler setup codec checks context Q j services query).run state)) :
    ResourceStep query state.1.1 result.2.1.1 := by
  simp only [hiddenHandler, StateT.run, support_map, Set.mem_image] at supported
  obtain ⟨middle, supported, rfl⟩ := supported
  rw [keepHiddenBad_game]
  simp only [once, StateT.run] at supported
  split_ifs at supported
  all_goals
    simp only [latch, StateT.run, support_map, Set.mem_image] at supported
    obtain ⟨step, supported, rfl⟩ := supported
    exact skeleton_resources setup codec checks (context.publicValue setup) context.beaconSeed _ query state.1 step supported

/-- The checked resource footprint preserves allocation validity without using any secrecy or freshness event. -/
theorem ResourceStep.valid (query : ServerAuthSpec.Domain) (before after : GameState KemSK)
    (valid : ResourceValid before) (step : ResourceStep query before after) : ResourceValid after := by
  have transfer (sessions : after.sessions = before.sessions) (pending : after.pending = before.pending) :
      ResourceValid after := by
    intro index token found
    rw [pending] at found
    rw [sessions]
    exact valid index token found
  rcases query with coin | query
  · exact transfer step.1 step.2.2
  cases query with
  | accept raw =>
      rcases step with ⟨sessions, _, pending | ⟨newToken, pending⟩⟩
      · intro index token found
        rw [pending] at found
        rw [sessions]
        exact Nat.lt_succ_of_lt (valid index token found)
      · intro index token found
        rw [pending] at found
        rw [sessions]
        by_cases current : index = before.sessions
        · subst current
          exact Nat.lt_succ_self _
        · rw [Function.update_of_ne current] at found
          exact Nat.lt_succ_of_lt (valid index token found)
  | build requested payload =>
      intro index token found
      rw [step.2.2] at found
      rw [step.1]
      by_cases current : index = requested
      · subst current
        simp only [Function.update_self] at found
        cases found
      · rw [Function.update_of_ne current] at found
        exact valid index token found
  | finish raw => exact transfer step.1 step.2.1
  | hmac key bytes => exact transfer step.1 step.2.2
  | hash bytes => exact transfer step.1 step.2.2
  | reveal key => exact transfer step.1 step.2.2

/-- Every reachable present pending handle is included in the finite build reservation. -/
theorem resource_pending_weight (game : GameState KemSK) (valid : ResourceValid game) (index : Nat) :
    slotWeight (game.pending index) ≤ pendingCount game := by
  cases found : game.pending index with
  | none => simp [slotWeight]
  | some token =>
      simpa only [found, pendingCount, pendingSlots] using
        Finset.single_le_sum (fun i _ => Nat.zero_le (slotWeight (game.pending i)))
          (Finset.mem_range.mpr (valid index token found))

/-- Attempted accepts reserve at most one build, attempted builds consume exactly their old weight, and all other operations preserve the reservation. -/
def PendingStep (query : ServerAuthSpec.Domain) (before after : GameState KemSK) : Prop :=
  match query with
  | .inr (.accept _) => pendingCount after ≤ pendingCount before + 1
  | .inr (.build index _) => pendingCount after + slotWeight (before.pending index) = pendingCount before
  | _ => pendingCount after = pendingCount before

/-- Every original step's pending reservation follows from its exact allocation/consumption footprint. -/
theorem ResourceStep.pending (query : ServerAuthSpec.Domain) (before after : GameState KemSK)
    (valid : ResourceValid before) (step : ResourceStep query before after) : PendingStep query before after := by
  have transfer (sessions : after.sessions = before.sessions) (pending : after.pending = before.pending) :
      pendingCount after = pendingCount before := by simp only [pendingCount, sessions, pending]
  rcases query with coin | query
  · exact transfer step.1 step.2.2
  cases query with
  | accept raw =>
      rcases step with ⟨sessions, _, pending | ⟨newToken, pending⟩⟩
      · simp only [PendingStep, pendingCount, sessions, pending, pending_extend]
        exact Nat.add_le_add_left (slotWeight_le _) _
      · simp only [PendingStep, pendingCount, sessions, pending, pending_new, slotWeight, le_refl]
  | build requested payload =>
      change pendingCount after + slotWeight (before.pending requested) = pendingCount before
      simp only [pendingCount, step.1, step.2.2]
      cases found : before.pending requested with
      | none => rw [slotWeight, Nat.add_zero, ← found, Function.update_eq_self]
      | some token => simpa only [found] using pending_clear before.sessions before.pending requested (valid requested token found)
  | finish raw => exact transfer step.1 step.2.1
  | hmac key bytes => exact transfer step.1 step.2.2
  | hash bytes => exact transfer step.1 step.2.2
  | reveal key => exact transfer step.1 step.2.2

/-- Only a finish consumes the active phase; every other operation preserves it. -/
def resourceFlag (query : ServerAuthSpec.Domain) (before : GameState KemSK) : Nat :=
  match query with
  | .inr (.finish _) => 0
  | _ => initSentFlag before

/-- The phase reserve is exact, not conditioned on a successful finish. -/
theorem ResourceStep.flag (query : ServerAuthSpec.Domain) (before after : GameState KemSK)
    (step : ResourceStep query before after) : initSentFlag after = resourceFlag query before := by
  rcases query with coin | query
  · simp only [resourceFlag, initSentFlag, step.2.1]
  cases query with
  | finish raw => exact step.2.2
  | accept raw | build index payload | hmac key bytes | hash bytes | reveal key =>
      simp only [resourceFlag, initSentFlag, step.2.1]

end BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.afterDerive_resources' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.afterDerive_resources
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.acceptStep_resources' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.acceptStep_resources
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.buildStep_resources' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.buildStep_resources
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.finishOutcome_resources' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.finishOutcome_resources
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.finishStep_resources' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.finishStep_resources
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.skeleton_resources' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.skeleton_resources
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.keepHiddenBad_game' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.keepHiddenBad_game
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.hiddenHandler_resources' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.hiddenHandler_resources
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.ResourceStep.valid' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.ResourceStep.valid
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.resource_pending_weight' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.resource_pending_weight
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.ResourceStep.pending' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.ResourceStep.pending
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.ResourceStep.flag' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.ResourceStep.flag
