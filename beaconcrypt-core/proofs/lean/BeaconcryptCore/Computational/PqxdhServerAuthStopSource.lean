import BeaconcryptCore.Computational.PqxdhServerAuthStopTrace

section HandlersSection

open OracleComp OracleSpec ENNReal
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
set_option autoImplicit false

namespace BeaconcryptCore.Computational.PqxdhServerAuthCtxStop
open PqxdhServerAuthExperiment PqxdhServerAuthEntryFactor
open PqxdhJointIdentity PqxdhSecretInputKdf PqxdhJointKdfGame PqxdhJointGapDh
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}

/-- The entire actual accept prefix and consumer establish selected-mark provenance before any optional stopping decision. -/
theorem accept_trace (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (context : Context KemSK) (Q : Nat) (j : Fin (Q + 1)) (tails : Services Response HiddenTable)
    (raw : Pqxdh.Bytes) (state : HiddenState KemSK) (invariant : TraceInvariant setup context Q j state)
    (chosen : Bool) (fresh : chosen = true → state.2 = false)
    (designated : chosen = true → state.1.1.sessions = j.val ∧ j.val < Q)
    (result : Option Nat × FlatState KemSK HiddenTable)
    (supported : result ∈ support ((acceptStep setup codec checks (context.publicValue setup)
      (chosenServices setup context tails chosen) raw).run state.1)) :
    TraceInvariant setup context Q j (result.2, state.2 || chosen) := by
  simp only [acceptStep, StateT.run, mem_support_bind_iff] at supported
  obtain ⟨collected, _, supported⟩ := supported
  cases found : collected.1 with
  | none =>
      simp only [found, support_pure, Set.mem_singleton_iff] at supported
      subst supported
      exact TraceInvariant.prefix setup context Q j state invariant collected.2 chosen
  | some input =>
      simp only [found] at supported
      split_ifs at supported with nonzero
      · obtain ⟨derived, derivedSupported, supported⟩ := (mem_support_bind_iff _ _ _).1 supported
        simp only [support_pure, Set.mem_singleton_iff] at supported
        subst supported
        have table := chosen_trace setup context tails chosen (PqxdhServerRelatedRootInput.message input)
          state.1.2.2 (fun selected => invariant.unselected (fresh selected)) derived derivedSupported
        exact TraceInvariant.accept setup context Q j state invariant collected.2 chosen input derived.1 derived.2
          table.1 table.2 designated
      · simp only [support_pure, Set.mem_singleton_iff] at supported
        subst supported
        exact TraceInvariant.prefix setup context Q j state invariant collected.2 chosen

/-- The entire actual raw finish preserves selected-input provenance across rejected preparation, every derive answer and every optional tail result. -/
theorem finish_trace (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (context : Context KemSK) (Q : Nat) (j : Fin (Q + 1)) (tails : Services Response HiddenTable)
    (raw : Pqxdh.Bytes) (state : HiddenState KemSK) (invariant : TraceInvariant setup context Q j state)
    (chosen : Bool) (fresh : chosen = true → state.2 = false)
    (designated : chosen = true → j.val = Q)
    (result : Option Pqxdh.Bytes × FlatState KemSK HiddenTable)
    (supported : result ∈ support ((finishStep setup codec (context.publicValue setup) context.beaconSeed
      (chosenServices setup context tails chosen) raw).run state.1)) :
    TraceInvariant setup context Q j (result.2, state.2 || chosen) := by
  simp only [finishStep, StateT.run] at supported
  cases phase : state.1.1.beacon.beacon.phase with
  | initSent control prekey oneTime kem =>
      have active : InitSent state.1.1 := ⟨control, prekey, oneTime, kem, phase⟩
      simp only [phase, mem_support_bind_iff] at supported
      obtain ⟨prepared, _, supported⟩ := supported
      cases found : prepared with
      | none =>
          simp only [found, support_pure, Set.mem_singleton_iff] at supported
          subst supported
          apply TraceInvariant.keep setup context Q j state _ invariant
            (Shape.finish control state.1.1 none invariant.shape.touched invariant.shape.once)
          · rw [finishOutcome_touches]
          · rfl
          · rfl
          · exact fun flags => (Bool.or_eq_false_iff.mp flags).1
      | some pending =>
          simp only [found, mem_support_bind_iff] at supported
          obtain ⟨derived, derivedSupported, supported⟩ := supported
          have table := chosen_trace setup context tails chosen
            (PqxdhJointDhExtractRoot.beaconMessage (context.publicValue setup) pending.collected)
            state.1.2.2 (fun selected => invariant.unselected (fresh selected)) derived derivedSupported
          have kept := fun cache staged => TraceInvariant.finish setup context Q j state invariant control active
            (PqxdhJointDhExtractRoot.beaconMessage (context.publicValue setup) pending.collected)
            cache staged chosen derived.1 derived.2 table.1 table.2 designated
          cases reply : derived.1 with
          | rejected =>
              simp only [reply, support_pure, Set.mem_singleton_iff] at supported
              subst supported
              exact kept state.1.1.ctx none
          | root root =>
              simp only [reply, mem_support_bind_iff] at supported
              obtain ⟨staged, _, supported⟩ := supported
              simp only [support_pure, Set.mem_singleton_iff] at supported
              subst supported
              exact kept staged.2.2 staged.1
          | hidden =>
              simp only [reply, mem_support_bind_iff] at supported
              obtain ⟨staged, _, supported⟩ := supported
              simp only [support_pure, Set.mem_singleton_iff] at supported
              subst supported
              exact kept staged.2.2 staged.1
  | _ =>
      simp only [phase, support_pure, Set.mem_singleton_iff] at supported
      subst supported
      exact { invariant with unselected := fun flags => invariant.unselected (Bool.or_eq_false_iff.mp flags).1 }

/-- All original dispatch branches retain the exact selected-input provenance under the actual designation schedule. -/
theorem skeleton_trace (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (context : Context KemSK) (Q : Nat) (j : Fin (Q + 1)) (tails : Services Response HiddenTable)
    (query : ServerAuthSpec.Domain) (state : HiddenState KemSK) (invariant : TraceInvariant setup context Q j state)
    (chosen : Bool) (fresh : chosen = true → state.2 = false)
    (schedule : chosen = true → hiddenDesignated Q j query state.1 = true)
    (result : ServerAuthSpec.Range query × FlatState KemSK HiddenTable)
    (supported : result ∈ support ((skeleton setup codec checks (context.publicValue setup) context.beaconSeed
      (chosenServices setup context tails chosen) query).run state.1)) :
    TraceInvariant setup context Q j (result.2, state.2 || chosen) := by
  have shape := skeleton_shape setup codec checks (context.publicValue setup) context.beaconSeed
    (chosenServices setup context tails chosen) query state.1 invariant.shape result supported
  cases query with
  | inl coin =>
      simp only [skeleton, StateT.run, support_map, Set.mem_image] at supported
      obtain ⟨value, _, rfl⟩ := supported
      exact { invariant with unselected := fun flags => invariant.unselected (Bool.or_eq_false_iff.mp flags).1 }
  | inr query =>
      cases query with
      | accept raw =>
          apply accept_trace setup codec checks context Q j tails raw state invariant chosen fresh _ result supported
          intro selected
          have position : j.val < Q ∧ state.1.1.sessions = j.val := of_decide_eq_true (schedule selected)
          exact ⟨position.2, position.1⟩
      | finish raw =>
          apply finish_trace setup codec context Q j tails raw state invariant chosen fresh _ result supported
          intro selected
          by_contra notLast
          have current := schedule selected
          simp only [hiddenDesignated, designated, notLast, ↓reduceIte] at current
          cases current
      | build index payload =>
          simp only [skeleton, buildStep, StateT.run] at supported
          cases found : state.1.1.pending index with
          | none =>
              simp only [found, support_pure, Set.mem_singleton_iff] at supported
              subst supported
              exact { invariant with unselected := fun flags => invariant.unselected (Bool.or_eq_false_iff.mp flags).1 }
          | some token =>
              simp only [found, mem_support_bind_iff] at supported
              obtain ⟨built, _, supported⟩ := supported
              simp only [support_pure, Set.mem_singleton_iff] at supported
              subst supported
              exact TraceInvariant.keep setup context Q j state _ invariant shape (List.prefix_refl _)
                rfl rfl (fun flags => (Bool.or_eq_false_iff.mp flags).1)
      | hmac key bytes =>
          simp only [skeleton, hmacStep, StateT.run] at supported
          split_ifs at supported with inside
          · obtain ⟨read, readSupported, supported⟩ := (mem_support_bind_iff _ _ _).1 supported
            simp only [support_pure, Set.mem_singleton_iff] at supported
            subst supported
            refine TraceInvariant.keep setup context Q j state _ invariant shape ?_ ?_ ?_ ?_
            · exact List.prefix_append _ _
            · rfl
            · cases chosen <;> exact public_retains bytes state.1.2.2 read readSupported
            · exact fun flags => (Bool.or_eq_false_iff.mp flags).1
          · simp only [support_pure, Set.mem_singleton_iff] at supported
            subst supported
            exact { invariant with unselected := fun flags => invariant.unselected (Bool.or_eq_false_iff.mp flags).1 }
      | hash bytes =>
          simp only [skeleton, hashStep, StateT.run, mem_support_bind_iff] at supported
          obtain ⟨read, _, supported⟩ := supported
          simp only [support_pure, Set.mem_singleton_iff] at supported
          subst supported
          exact TraceInvariant.keep setup context Q j state _ invariant shape (List.prefix_refl _)
            rfl rfl (fun flags => (Bool.or_eq_false_iff.mp flags).1)
      | reveal key =>
          simp only [skeleton, StateT.run, support_pure, Set.mem_singleton_iff] at supported
          subst supported
          exact { invariant with unselected := fun flags => invariant.unselected (Bool.or_eq_false_iff.mp flags).1 }

/-- Sticky refusal changes no private input/mark or source chronology field used by the invariant. -/
theorem keep_bad_trace {Result : Type} (setup : Setup baseSpec KemSK) (context : Context KemSK)
    (Q : Nat) (j : Fin (Q + 1)) (before : HiddenState KemSK) (result : Result × HiddenState KemSK)
    (invariant : TraceInvariant setup context Q j result.2) :
    TraceInvariant setup context Q j (keepHiddenBad before result).2 := by
  unfold keepHiddenBad
  split
  · exact ⟨invariant.shape, invariant.unselected, invariant.selected, invariant.marked⟩
  · exact invariant

/-- The literal hidden handler establishes mark/input provenance on every original reply path, with arbitrary typed hidden tail callbacks. -/
theorem hidden_trace (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (context : Context KemSK) (Q : Nat) (j : Fin (Q + 1)) (tails : Services Response HiddenTable)
    (query : ServerAuthSpec.Domain) (state : HiddenState KemSK) (invariant : TraceInvariant setup context Q j state)
    (result : ServerAuthSpec.Range query × HiddenState KemSK)
    (supported : result ∈ support ((hiddenHandler setup codec checks context Q j
      (tableServices setup context tails) query).run state)) :
    TraceInvariant setup context Q j result.2 := by
  simp only [hiddenHandler, StateT.run, support_map, Set.mem_image] at supported
  obtain ⟨middle, supported, rfl⟩ := supported
  apply keep_bad_trace setup context Q j state middle
  simp only [once, StateT.run] at supported
  split_ifs at supported with already selected
  · simp only [latch, StateT.run, support_map, Set.mem_image] at supported
    obtain ⟨step, supported, rfl⟩ := supported
    have kept := skeleton_trace setup codec checks context Q j tails query state invariant false
      (fun no => Bool.noConfusion no) (fun no => Bool.noConfusion no) step supported
    simpa only [already, Bool.true_or, Bool.or_false] using kept
  · simp only [latch, StateT.run, support_map, Set.mem_image] at supported
    obtain ⟨step, supported, rfl⟩ := supported
    have before : state.2 = false := Bool.eq_false_of_not_eq_true already
    have kept := skeleton_trace setup codec checks context Q j tails query state invariant true
      (fun _ => before) (fun _ => selected) step supported
    simpa only [selected] using kept
  · simp only [latch, StateT.run, support_map, Set.mem_image] at supported
    obtain ⟨step, supported, rfl⟩ := supported
    have notSelected : hiddenDesignated Q j query state.1 = false := Bool.eq_false_of_not_eq_true selected
    have kept := skeleton_trace setup codec checks context Q j tails query state invariant false
      (fun no => Bool.noConfusion no) (fun no => Bool.noConfusion no) step supported
    simpa only [notSelected] using kept

/-- The complete adaptive source client retains the literal selected-input and mark witnesses without a successful-execution or good-cache premise. -/
theorem client_trace (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (context : Context KemSK) (Q : Nat) (j : Fin (Q + 1)) (tails : Services Response HiddenTable)
    {Result : Type} (client : OracleComp ServerAuthSpec Result) (state : HiddenState KemSK)
    (invariant : TraceInvariant setup context Q j state) (result : Result × HiddenState KemSK)
    (supported : result ∈ support ((simulateQ (hiddenHandler setup codec checks context Q j
      (tableServices setup context tails)) client).run state)) :
    TraceInvariant setup context Q j result.2 := by
  induction client using OracleComp.inductionOn generalizing state with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
      subst supported
      exact invariant
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
        id_map, StateT.run_bind, mem_support_bind_iff] at supported
      obtain ⟨step, stepSupported, supported⟩ := supported
      exact ih step.1 step.2 (hidden_trace setup codec checks context Q j tails query state invariant step stepSupported) supported

/-- The actual context-initialized run supplies its own complete provenance; callers need not furnish an arbitrary trace certificate. -/
theorem run_trace (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (context : Context KemSK) (Q : Nat) (j : Fin (Q + 1)) (tails : Services Response HiddenTable)
    (adversary : Adversary) (revealSeed : Bool) (result : HiddenState KemSK)
    (supported : result ∈ support (hiddenRun setup codec checks adversary revealSeed context Q j
      (tableServices setup context tails))) : TraceInvariant setup context Q j result := by
  simp only [hiddenRun, support_map, Set.mem_image] at supported
  obtain ⟨finished, supported, rfl⟩ := supported
  exact client_trace setup codec checks context Q j tails _ _ (TraceInvariant.initial setup context Q j) finished supported

/-- The actual uniform-factor experiment's original winning event excludes two marked Server attempts. No original-key state invariant is assumed after the key-schedule replacement. -/
theorem factor_marks_unique (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (context : Context KemSK) (Q : Nat) (j : Fin (Q + 1)) (value : PqxdhServerAuthKeySchedule.Output)
    (adversary : Adversary) (revealSeed : Bool) (result : HiddenState KemSK)
    (supported : result ∈ support (hiddenRun setup codec checks adversary revealSeed context Q j
      (factorServices setup codec checks context value)))
    (event : EntryEvent setup context.seed context.scalar Q j result.1.1.ghost)
    (first second : Nat) (one : result.1.2.1 first = true) (two : result.1.2.1 second = true) : first = second := by
  have invariant := run_trace setup codec checks context Q j (factorServices setup codec checks context value)
    adversary revealSeed result supported
  exact marked_unique setup context Q j result invariant.shape.once invariant.selected invariant.marked event first second one two

end BeaconcryptCore.Computational.PqxdhServerAuthCtxStop

end HandlersSection

section ControlSection

open OracleComp OracleSpec ENNReal
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
set_option autoImplicit false

namespace BeaconcryptCore.Computational.PqxdhServerAuthCtxStop
open PqxdhServerAuthExperiment PqxdhServerAuthEntryFactor
open PqxdhJointIdentity PqxdhSecretInputKdf PqxdhJointKdfGame PqxdhJointGapDh
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response τ : Type}

/-- Actual accept changes marks only by setting its freshly allocated index to true. -/
theorem accept_marks (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (publicValue : PublicChallenge) (services : Services Response τ)
    (raw : Pqxdh.Bytes) (state : FlatState KemSK τ) (result : Option Nat × FlatState KemSK τ)
    (supported : result ∈ support ((acceptStep setup codec checks publicValue services raw).run state)) :
    result.2.2.1 = state.2.1 ∨ result.2.2.1 = Function.update state.2.1 state.1.sessions true := by
  simp only [acceptStep, StateT.run, mem_support_bind_iff] at supported
  obtain ⟨collected, _, supported⟩ := supported
  cases found : collected.1 with
  | none =>
      simp only [found, support_pure, Set.mem_singleton_iff] at supported
      subst supported
      exact Or.inl rfl
  | some input =>
      simp only [found] at supported
      split_ifs at supported with nonzero
      · obtain ⟨derived, _, supported⟩ := (mem_support_bind_iff _ _ _).1 supported
        simp only [support_pure, Set.mem_singleton_iff] at supported
        subst supported
        split
        · exact Or.inr rfl
        · exact Or.inl rfl
      · simp only [support_pure, Set.mem_singleton_iff] at supported
        subst supported
        exact Or.inl rfl

/-- The complete raw finish retains all Server marks for every preparation, derive and opening outcome. -/
theorem finish_marks (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (publicValue : PublicChallenge) (beaconSeed : IdentitySeed) (services : Services Response τ)
    (raw : Pqxdh.Bytes) (state : FlatState KemSK τ) (result : Option Pqxdh.Bytes × FlatState KemSK τ)
    (supported : result ∈ support ((finishStep setup codec publicValue beaconSeed services raw).run state)) :
    result.2.2.1 = state.2.1 := by
  simp only [finishStep, StateT.run] at supported
  cases phase : state.1.beacon.beacon.phase with
  | initSent control prekey oneTime kem =>
      simp only [phase, mem_support_bind_iff] at supported
      obtain ⟨prepared, _, supported⟩ := supported
      cases found : prepared with
      | none =>
          simp only [found, support_pure, Set.mem_singleton_iff] at supported
          subst supported
          rfl
      | some pending =>
          simp only [found, mem_support_bind_iff] at supported
          obtain ⟨derived, _, supported⟩ := supported
          cases reply : derived.1 with
          | rejected =>
              simp only [reply, support_pure, Set.mem_singleton_iff] at supported
              subst supported
              rfl
          | root root =>
              simp only [reply, mem_support_bind_iff] at supported
              obtain ⟨staged, _, supported⟩ := supported
              simp only [support_pure, Set.mem_singleton_iff] at supported
              subst supported
              rfl
          | hidden =>
              simp only [reply, mem_support_bind_iff] at supported
              obtain ⟨staged, _, supported⟩ := supported
              simp only [support_pure, Set.mem_singleton_iff] at supported
              subst supported
              rfl
  | _ =>
      simp only [phase, support_pure, Set.mem_singleton_iff] at supported
      subst supported
      rfl

/-- The source mark transition changes at most the current accept-attempt index. -/
def MarkStep (query : ServerAuthSpec.Domain) (before after : FlatState KemSK τ) : Prop :=
  match query with
  | .inr (.accept _) => after.2.1 = before.2.1 ∨ after.2.1 = Function.update before.2.1 before.1.sessions true
  | _ => after.2.1 = before.2.1

/-- The original seven-query dispatch supplies that mark transition for every actual callback reply. -/
theorem skeleton_marks (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (publicValue : PublicChallenge) (beaconSeed : IdentitySeed) (services : Services Response τ)
    (query : ServerAuthSpec.Domain) (state : FlatState KemSK τ)
    (result : ServerAuthSpec.Range query × FlatState KemSK τ)
    (supported : result ∈ support ((skeleton setup codec checks publicValue beaconSeed services query).run state)) :
    MarkStep query state result.2 := by
  cases query with
  | inl coin =>
      simp only [skeleton, StateT.run, support_map, Set.mem_image] at supported
      obtain ⟨value, _, rfl⟩ := supported
      rfl
  | inr query =>
      cases query with
      | accept raw => exact accept_marks setup codec checks publicValue services raw state result supported
      | finish raw => exact finish_marks setup codec publicValue beaconSeed services raw state result supported
      | build index payload =>
          simp only [skeleton, buildStep, StateT.run] at supported
          cases found : state.1.pending index with
          | none =>
              simp only [found, support_pure, Set.mem_singleton_iff] at supported
              subst supported
              rfl
          | some token =>
              simp only [found, mem_support_bind_iff] at supported
              obtain ⟨built, _, supported⟩ := supported
              simp only [support_pure, Set.mem_singleton_iff] at supported
              subst supported
              rfl
      | hmac key bytes =>
          simp only [skeleton, hmacStep, StateT.run] at supported
          split_ifs at supported
          · obtain ⟨read, _, supported⟩ := (mem_support_bind_iff _ _ _).1 supported
            simp only [support_pure, Set.mem_singleton_iff] at supported
            subst supported
            rfl
          · simp only [support_pure, Set.mem_singleton_iff] at supported
            subst supported
            rfl
      | hash bytes =>
          simp only [skeleton, hashStep, StateT.run, mem_support_bind_iff] at supported
          obtain ⟨read, _, supported⟩ := supported
          simp only [support_pure, Set.mem_singleton_iff] at supported
          subst supported
          rfl
      | reveal key =>
          simp only [skeleton, StateT.run, support_pure, Set.mem_singleton_iff] at supported
          subst supported
          rfl

/-- Session marks remain true across every source transition; replacing a mark sets it to true again. -/
theorem MarkStep.monotone (query : ServerAuthSpec.Domain) (before after : FlatState KemSK τ)
    (step : MarkStep query before after) (index : Nat) (marked : before.2.1 index = true) :
    after.2.1 index = true := by
  cases query with
  | inl coin => exact step ▸ marked
  | inr query =>
      cases query with
      | accept raw =>
          rcases step with same | updated
          · exact same ▸ marked
          · rw [updated]
            by_cases equal : index = before.1.sessions
            · simp [equal]
            · simpa only [Function.update_of_ne equal] using marked
      | build _ _ | finish _ | hmac _ _ | hash _ | reveal _ => exact step ▸ marked

/-- The actual designation/refusal wrapper retains the same source mark transition. -/
theorem hidden_marks (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (context : Context KemSK) (Q : Nat) (j : Fin (Q + 1)) (services : Services Response HiddenTable)
    (query : ServerAuthSpec.Domain) (state : HiddenState KemSK)
    (result : ServerAuthSpec.Range query × HiddenState KemSK)
    (supported : result ∈ support ((hiddenHandler setup codec checks context Q j services query).run state)) :
    MarkStep query state.1 result.2.1 := by
  simp only [hiddenHandler, StateT.run, support_map, Set.mem_image] at supported
  obtain ⟨middle, supported, rfl⟩ := supported
  have transition : MarkStep query state.1 middle.2.1 := by
    simp only [once, StateT.run] at supported
    split_ifs at supported
    all_goals
      simp only [latch, StateT.run, support_map, Set.mem_image] at supported
      obtain ⟨step, supported, rfl⟩ := supported
      exact skeleton_marks setup codec checks (context.publicValue setup) context.beaconSeed _ query state.1 step supported
  unfold keepHiddenBad
  split <;> exact transition

/-- Every complete adaptive continuation retains each previously marked source attempt, including behavior after refusal. -/
theorem client_marks (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (context : Context KemSK) (Q : Nat) (j : Fin (Q + 1)) (services : Services Response HiddenTable)
    {Result : Type} (client : OracleComp ServerAuthSpec Result) (state : HiddenState KemSK)
    (index : Nat) (marked : state.1.2.1 index = true) (result : Result × HiddenState KemSK)
    (supported : result ∈ support ((simulateQ (hiddenHandler setup codec checks context Q j services) client).run state)) :
    result.2.1.2.1 index = true := by
  induction client using OracleComp.inductionOn generalizing state with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
      subst supported
      exact marked
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
        id_map, StateT.run_bind, mem_support_bind_iff] at supported
      obtain ⟨step, stepSupported, supported⟩ := supported
      exact ih step.1 step.2 (MarkStep.monotone query state.1 step.2.1
        (hidden_marks setup codec checks context Q j services query state step stepSupported) index marked) supported

end BeaconcryptCore.Computational.PqxdhServerAuthCtxStop

end ControlSection

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxStop.accept_trace' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxStop.accept_trace
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxStop.finish_trace' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxStop.finish_trace
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxStop.skeleton_trace' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxStop.skeleton_trace
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxStop.keep_bad_trace' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxStop.keep_bad_trace
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxStop.hidden_trace' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxStop.hidden_trace
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxStop.client_trace' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxStop.client_trace
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxStop.run_trace' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxStop.run_trace
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxStop.factor_marks_unique' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxStop.factor_marks_unique
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxStop.accept_marks' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxStop.accept_marks
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxStop.finish_marks' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxStop.finish_marks
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxStop.skeleton_marks' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxStop.skeleton_marks
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxStop.MarkStep.monotone' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxStop.MarkStep.monotone
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxStop.hidden_marks' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxStop.hidden_marks
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxStop.client_marks' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxStop.client_marks
