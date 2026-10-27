import BeaconcryptCore.Computational.PqxdhServerAuthStopSource
import BeaconcryptCore.Computational.PqxdhServerAuthCtxAcceptanceHistory

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhServerAuthDesignation
open PqxdhServerAuthExperiment PqxdhServerAuthEntryFactor PqxdhServerAuthCtxStop
open PqxdhServerAuthGapDh PqxdhServerAuthPendingBudget
open PqxdhJointIdentity PqxdhSecretInputKdf PqxdhJointKdfGame PqxdhJointGapDh
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}

/-- The actual designated operation has already passed its source allocation or one-shot initial Beacon phase. -/
def Passed (Q : Nat) (j : Fin (Q + 1)) (game : GameState KemSK) : Prop :=
  if j.val < Q then j.val < game.sessions else initSentFlag game = 0

/-- Every actual allocation/token/phase footprint preserves a coordinate that has already passed. -/
theorem Passed.step (Q : Nat) (j : Fin (Q + 1)) (query : ServerAuthSpec.Domain)
    (before after : GameState KemSK) (passed : Passed Q j before)
    (resources : ResourceStep query before after) : Passed Q j after := by
  unfold Passed at passed ⊢
  split_ifs at passed ⊢ with session
  · cases query with
    | inl coin => simpa only [resources.1] using passed
    | inr query => cases query <;> dsimp only [ResourceStep] at resources <;> omega
  · rw [ResourceStep.flag query before after resources]
    cases query with
    | inl coin => exact passed
    | inr query => cases query <;> simp only [resourceFlag, passed]

/-- Completing the literal designated request moves past its allocated coordinate, even when the native operation fails. -/
theorem designated_passed (Q : Nat) (j : Fin (Q + 1)) (query : ServerAuthSpec.Domain)
    (before : FlatState KemSK HiddenTable) (after : GameState KemSK)
    (selected : hiddenDesignated Q j query before = true)
    (resources : ResourceStep query before.1 after) : Passed Q j after := by
  cases query with
  | inl coin => simp [hiddenDesignated, designated] at selected
  | inr query =>
      cases query with
      | accept raw =>
          simp only [hiddenDesignated, designated, decide_eq_true_eq] at selected
          simp only [Passed, selected.1, ↓reduceIte, resources.1, selected.2, Nat.lt_succ_self]
      | finish raw =>
          have last : j.val = Q := by
            by_contra different
            simp [hiddenDesignated, designated, different] at selected
          simpa only [Passed, last, lt_self_iff_false, ↓reduceIte] using resources.2.2
      | build _ _ | hmac _ _ | hash _ | reveal _ => simp [hiddenDesignated, designated] at selected

/-- The actual one-shot latch may be set only after its source coordinate has passed. -/
def Latched (Q : Nat) (j : Fin (Q + 1)) (state : HiddenState KemSK) : Prop :=
  state.2 = true → Passed Q j state.1.1

/-- Every complete source handler updates the one-shot flag by exactly the original designated-operation test, retaining arbitrary tail effects. -/
theorem handler_flag (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (context : Context KemSK) (Q : Nat) (j : Fin (Q + 1)) (services : Services Response HiddenTable)
    (query : ServerAuthSpec.Domain) (state : HiddenState KemSK)
    (result : ServerAuthSpec.Range query × HiddenState KemSK)
    (supported : result ∈ support ((hiddenHandler setup codec checks context Q j services query).run state)) :
    result.2.2 = (state.2 || hiddenDesignated Q j query state.1) := by
  simp only [hiddenHandler, StateT.run, support_map, Set.mem_image] at supported
  obtain ⟨middle, supported, rfl⟩ := supported
  have flag : (keepHiddenBad state middle).2.2 = middle.2.2 := by
    unfold keepHiddenBad
    split <;> rfl
  rw [flag]
  simp only [once, StateT.run] at supported
  split_ifs at supported
  all_goals
    simp only [latch, StateT.run, support_map, Set.mem_image] at supported
    obtain ⟨step, _, rfl⟩ := supported
    rfl

/-- The complete original handler establishes the passed-coordinate interpretation of its one-shot flag. -/
theorem handler_latched (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (context : Context KemSK) (Q : Nat) (j : Fin (Q + 1)) (services : Services Response HiddenTable)
    (query : ServerAuthSpec.Domain) (state : HiddenState KemSK) (latched : Latched Q j state)
    (result : ServerAuthSpec.Range query × HiddenState KemSK)
    (supported : result ∈ support ((hiddenHandler setup codec checks context Q j services query).run state)) :
    Latched Q j result.2 := by
  intro flagged
  rw [handler_flag setup codec checks context Q j services query state result supported] at flagged
  simp only [Bool.or_eq_true_eq_eq_true_or_eq_true] at flagged
  rcases flagged with old | chosen
  · exact Passed.step Q j query state.1.1 result.2.1.1 (latched old)
      (hiddenHandler_resources setup codec checks context Q j services query state result supported)
  · exact designated_passed Q j query state.1 result.2.1.1 chosen
      (hiddenHandler_resources setup codec checks context Q j services query state result supported)

/-- A passed coordinate cannot be the current designated source operation. -/
theorem Passed.not_designated (Q : Nat) (j : Fin (Q + 1)) (query : ServerAuthSpec.Domain)
    (state : FlatState KemSK HiddenTable) (passed : Passed Q j state.1) :
    hiddenDesignated Q j query state = false := by
  apply Bool.eq_false_of_not_eq_true
  intro selected
  cases query with
  | inl coin => simp [hiddenDesignated, designated] at selected
  | inr query =>
      cases query with
      | accept raw =>
          simp only [hiddenDesignated, designated, decide_eq_true_eq] at selected
          simp only [Passed, selected.1, ↓reduceIte, selected.2, lt_self_iff_false] at passed
      | finish raw =>
          have last : j.val = Q := by
            by_contra different
            simp [hiddenDesignated, designated, different] at selected
          cases phase : state.1.beacon.beacon.phase <;>
            simp [Passed, hiddenDesignated, designated, last, phase, initSentFlag] at passed selected
      | build _ _ | hmac _ _ | hash _ | reveal _ => simp [hiddenDesignated, designated] at selected

/-- A source input was retained privately, or the actual selected operation has already refused a prior table hit. -/
def Established (table : HiddenTable) : Prop := table.hidden.isSome = true ∨ table.bad = true

/-- The concrete ordinary and designated table routes retain prior establishment, establish every valid designated input, and reject every missing root input. -/
theorem chosen_complete (setup : Setup baseSpec KemSK) (context : Context KemSK)
    (tails : Services Response HiddenTable) (chosen : Bool)
    (message : PqxdhJointDhExtractFamily.Message) (before : HiddenTable) (result : Reply × HiddenTable)
    (supported : result ∈ support (((chosenServices setup context tails chosen).derive message).run before)) :
    (Established before → Established result.2) ∧
      (chosen = true → (rootInput setup context.seed context.scalar message).isSome = true → Established result.2) ∧
      (result.1 ≠ .rejected → (rootInput setup context.seed context.scalar message).isSome = true) := by
  cases chosen with
  | true =>
      change result ∈ support ((selectHidden setup.joint setup.dh context.seed context.scalar message).run before) at supported
      simp only [selectHidden, StateT.run] at supported
      cases input : PqxdhJointDhExtractFamily.input setup.joint setup.dh context.seed context.scalar message with
      | none =>
          simp only [input, support_pure, Set.mem_singleton_iff] at supported
          subst supported
          simp [rootInput, input]
      | some bytes =>
          simp only [input] at supported
          cases cached : before.cache bytes
          all_goals
            simp only [cached, support_pure, Set.mem_singleton_iff] at supported
            subst supported
            simp [Established, rootInput, input]
  | false =>
      change result ∈ support ((hiddenDerive setup.hmac setup.joint setup.dh context.seed context.scalar message).run before) at supported
      simp only [hiddenDerive, StateT.run] at supported
      cases input : PqxdhJointDhExtractFamily.input setup.joint setup.dh context.seed context.scalar message with
      | none =>
          simp only [input, support_pure, Set.mem_singleton_iff] at supported
          subst supported
          simp [rootInput, input]
      | some bytes =>
          simp only [input] at supported
          split at supported
          · simp only [support_pure, Set.mem_singleton_iff] at supported
            subst supported
            simp [rootInput, input]
          · simp only [ordinaryHiddenDerive, StateT.run, support_map, Set.mem_image] at supported
            obtain ⟨read, _, rfl⟩ := supported
            simp [Established, rootInput, input]

/-- A literal rooted derivation touch belongs to the designated operation coordinate. The coordinate is an actual allocation index or the one-shot Beacon request, not key-byte equality. -/
def Relevant (setup : Setup baseSpec KemSK) (context : Context KemSK)
    (Q : Nat) (j : Fin (Q + 1)) : Touch → Prop
  | .session index message _ => index = j.val ∧ j.val < Q ∧
      (rootInput setup context.seed context.scalar message).isSome = true
  | .beacon message => j.val = Q ∧ (rootInput setup context.seed context.scalar message).isSome = true
  | .adversary _ => False

/-- Every actually delivered rooted designated touch has either established the omitted input or raised the source refusal. -/
def Covered (setup : Setup baseSpec KemSK) (context : Context KemSK)
    (Q : Nat) (j : Fin (Q + 1)) (ghost : Ghost) (table : HiddenTable) : Prop :=
  ∀ touch ∈ ghost.touches, Relevant setup context Q j touch → Established table

/-- Unchanged touch history transports its concrete establishment evidence through a retained table update. -/
theorem Covered.transport (setup : Setup baseSpec KemSK) (context : Context KemSK)
    (Q : Nat) (j : Fin (Q + 1)) (before after : Ghost) (old next : HiddenTable)
    (covered : Covered setup context Q j before old) (touches : after.touches = before.touches)
    (keeps : Established old → Established next) : Covered setup context Q j after next := by
  intro touch member relevant
  rw [touches] at member
  exact keeps (covered touch member relevant)

/-- An actual appended touch is covered by its own completed derivation while every previous occurrence is retained. -/
theorem Covered.append (setup : Setup baseSpec KemSK) (context : Context KemSK)
    (Q : Nat) (j : Fin (Q + 1)) (before after : Ghost) (old next : HiddenTable)
    (touch : Touch) (covered : Covered setup context Q j before old)
    (touches : after.touches = before.touches ++ [touch])
    (keeps : Established old → Established next)
    (newTouch : Relevant setup context Q j touch → Established next) :
    Covered setup context Q j after next := by
  intro other member relevant
  rw [touches] at member
  rcases List.mem_append.mp member with prior | appended
  · exact keeps (covered other prior relevant)
  · exact newTouch ((List.mem_singleton.mp appended) ▸ relevant)

/-- The full actual Server prefix and derivation establish coverage before returning any optional pending handle. -/
theorem accept_covered (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (context : Context KemSK) (Q : Nat) (j : Fin (Q + 1)) (tails : Services Response HiddenTable)
    (raw : Pqxdh.Bytes) (state : FlatState KemSK HiddenTable)
    (covered : Covered setup context Q j state.1.ghost state.2.2) (chosen : Bool)
    (needed : hiddenDesignated Q j (.inr (.accept raw)) state = true → chosen = true)
    (result : Option Nat × FlatState KemSK HiddenTable)
    (supported : result ∈ support ((acceptStep setup codec checks (context.publicValue setup)
      (chosenServices setup context tails chosen) raw).run state)) :
    Covered setup context Q j result.2.1.ghost result.2.2.2 := by
  simp only [acceptStep, StateT.run, mem_support_bind_iff] at supported
  obtain ⟨collected, _, supported⟩ := supported
  cases found : collected.1 with
  | none =>
      simp only [found, support_pure, Set.mem_singleton_iff] at supported
      subst supported
      exact covered
  | some input =>
      simp only [found] at supported
      split_ifs at supported with nonzero
      · obtain ⟨derived, derivedSupported, supported⟩ := (mem_support_bind_iff _ _ _).1 supported
        simp only [support_pure, Set.mem_singleton_iff] at supported
        subst supported
        have facts := chosen_complete setup context tails chosen (PqxdhServerRelatedRootInput.message input)
          state.2.2 derived derivedSupported
        apply Covered.append setup context Q j state.1.ghost _ state.2.2 derived.2
          (.session state.1.sessions (PqxdhServerRelatedRootInput.message input) derived.1.value) covered
          (afterDerive_touches setup (context.publicValue setup) state.1.sessions input derived.1
            (acceptedPrefix state.1 collected.2)) facts.1
        intro relevant
        exact facts.2.1 (needed (by
          simpa only [hiddenDesignated, designated, decide_eq_true_eq] using
            And.intro relevant.2.1 relevant.1)) relevant.2.2
      · simp only [support_pure, Set.mem_singleton_iff] at supported
        subst supported
        exact covered

/-- Complete raw initial receive retains delivered-touch coverage through all derivation, native opening and publication outcomes. -/
theorem finish_covered (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (context : Context KemSK) (Q : Nat) (j : Fin (Q + 1)) (tails : Services Response HiddenTable)
    (raw : Pqxdh.Bytes) (state : FlatState KemSK HiddenTable)
    (covered : Covered setup context Q j state.1.ghost state.2.2) (chosen : Bool)
    (needed : hiddenDesignated Q j (.inr (.finish raw)) state = true → chosen = true)
    (result : Option Pqxdh.Bytes × FlatState KemSK HiddenTable)
    (supported : result ∈ support ((finishStep setup codec (context.publicValue setup) context.beaconSeed
      (chosenServices setup context tails chosen) raw).run state)) :
    Covered setup context Q j result.2.1.ghost result.2.2.2 := by
  simp only [finishStep, StateT.run] at supported
  cases phase : state.1.beacon.beacon.phase with
  | initSent control prekey oneTime kem =>
      simp only [phase, mem_support_bind_iff] at supported
      obtain ⟨prepared, _, supported⟩ := supported
      cases found : prepared with
      | none =>
          simp only [found, support_pure, Set.mem_singleton_iff] at supported
          subst supported
          exact Covered.transport setup context Q j state.1.ghost _ state.2.2 state.2.2
            covered (finishOutcome_touches control state.1 none) id
      | some pending =>
          simp only [found, mem_support_bind_iff] at supported
          obtain ⟨derived, derivedSupported, supported⟩ := supported
          have facts := chosen_complete setup context tails chosen
            (PqxdhJointDhExtractRoot.beaconMessage (context.publicValue setup) pending.collected)
            state.2.2 derived derivedSupported
          have kept (cache : CtxRomAuth.CtxRO.QueryCache) (staged : Option PqxdhBeaconPhase2Publication.Staged) :
              Covered setup context Q j
                (finishOutcome control { state.1 with ctx := cache, ghost := { state.1.ghost with touches := state.1.ghost.touches ++
                    [.beacon (PqxdhJointDhExtractRoot.beaconMessage (context.publicValue setup) pending.collected)] } } staged).2.ghost
                derived.2 := by
            apply Covered.append setup context Q j state.1.ghost _ state.2.2 derived.2
              (.beacon (PqxdhJointDhExtractRoot.beaconMessage (context.publicValue setup) pending.collected))
              covered (finishOutcome_touches control _ staged) facts.1
            intro relevant
            exact facts.2.1 (needed (by simp [hiddenDesignated, designated, relevant.1, phase])) relevant.2
          cases reply : derived.1 with
          | rejected =>
              simp only [reply, support_pure, Set.mem_singleton_iff] at supported
              subst supported
              exact kept state.1.ctx none
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
      exact covered

/-- The actual public table call preserves established selection or refusal, including its own forbidden-input branch. -/
theorem public_established (bytes : Pqxdh.Bytes) (before : HiddenTable) (result : HmacBlock × HiddenTable)
    (supported : result ∈ support ((hiddenPublic bytes).run before)) :
    Established before → Established result.2 := by
  simp only [hiddenPublic, StateT.run] at supported
  split at supported
  · simp only [support_pure, Set.mem_singleton_iff] at supported
    subst supported
    simp [Established]
  · simp only [support_map, Set.mem_image] at supported
    obtain ⟨read, _, rfl⟩ := supported
    exact id

/-- Every actual source API branch preserves designated-touch coverage with its real table service and complete tail callbacks. -/
theorem skeleton_covered (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (context : Context KemSK) (Q : Nat) (j : Fin (Q + 1)) (tails : Services Response HiddenTable)
    (query : ServerAuthSpec.Domain) (state : FlatState KemSK HiddenTable)
    (covered : Covered setup context Q j state.1.ghost state.2.2) (chosen : Bool)
    (needed : hiddenDesignated Q j query state = true → chosen = true)
    (result : ServerAuthSpec.Range query × FlatState KemSK HiddenTable)
    (supported : result ∈ support ((skeleton setup codec checks (context.publicValue setup) context.beaconSeed
      (chosenServices setup context tails chosen) query).run state)) :
    Covered setup context Q j result.2.1.ghost result.2.2.2 := by
  cases query with
  | inl coin =>
      simp only [skeleton, StateT.run, support_map, Set.mem_image] at supported
      obtain ⟨value, _, rfl⟩ := supported
      exact covered
  | inr query =>
      cases query with
      | accept raw => exact accept_covered setup codec checks context Q j tails raw state covered chosen needed result supported
      | finish raw => exact finish_covered setup codec context Q j tails raw state covered chosen needed result supported
      | build index payload =>
          simp only [skeleton, buildStep, StateT.run] at supported
          cases found : state.1.pending index with
          | none =>
              simp only [found, support_pure, Set.mem_singleton_iff] at supported
              subst supported
              exact covered
          | some token =>
              simp only [found, mem_support_bind_iff] at supported
              obtain ⟨built, _, supported⟩ := supported
              simp only [support_pure, Set.mem_singleton_iff] at supported
              subst supported
              exact covered
      | hmac key bytes =>
          simp only [skeleton, hmacStep, StateT.run] at supported
          split_ifs at supported with inside
          · obtain ⟨read, readSupported, supported⟩ := (mem_support_bind_iff _ _ _).1 supported
            simp only [support_pure, Set.mem_singleton_iff] at supported
            subst supported
            apply Covered.append setup context Q j state.1.ghost _ state.2.2 read.2 (.adversary bytes) covered rfl
            · cases chosen <;> exact public_established bytes state.2.2 read readSupported
            · intro impossible
              exact impossible.elim
          · simp only [support_pure, Set.mem_singleton_iff] at supported
            subst supported
            exact covered
      | hash bytes =>
          simp only [skeleton, hashStep, StateT.run, mem_support_bind_iff] at supported
          obtain ⟨read, _, supported⟩ := supported
          simp only [support_pure, Set.mem_singleton_iff] at supported
          subst supported
          exact covered
      | reveal keyId =>
          simp only [skeleton, StateT.run, support_pure, Set.mem_singleton_iff] at supported
          subst supported
          exact covered

/-- The literal sticky-refusal wrapper preserves coverage without altering source touch history. -/
theorem keep_bad_covered {Result : Type} (setup : Setup baseSpec KemSK) (context : Context KemSK)
    (Q : Nat) (j : Fin (Q + 1)) (before : HiddenState KemSK) (result : Result × HiddenState KemSK)
    (covered : Covered setup context Q j result.2.1.1.ghost result.2.1.2.2) :
    Covered setup context Q j (keepHiddenBad before result).2.1.1.ghost (keepHiddenBad before result).2.1.2.2 := by
  unfold keepHiddenBad
  split
  · intro touch member relevant
    exact Or.inr rfl
  · exact covered

/-- Actual one-shot designation cannot skip a newly delivered rooted coordinate: the source latch already means that coordinate has passed. -/
theorem handler_covered (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (context : Context KemSK) (Q : Nat) (j : Fin (Q + 1)) (tails : Services Response HiddenTable)
    (query : ServerAuthSpec.Domain) (state : HiddenState KemSK) (latched : Latched Q j state)
    (covered : Covered setup context Q j state.1.1.ghost state.1.2.2)
    (result : ServerAuthSpec.Range query × HiddenState KemSK)
    (supported : result ∈ support ((hiddenHandler setup codec checks context Q j
      (tableServices setup context tails) query).run state)) :
    Covered setup context Q j result.2.1.1.ghost result.2.1.2.2 := by
  simp only [hiddenHandler, StateT.run, support_map, Set.mem_image] at supported
  obtain ⟨middle, supported, rfl⟩ := supported
  apply keep_bad_covered setup context Q j state middle
  simp only [once, StateT.run] at supported
  split_ifs at supported with already selected
  · simp only [latch, StateT.run, support_map, Set.mem_image] at supported
    obtain ⟨step, supported, rfl⟩ := supported
    apply skeleton_covered setup codec checks context Q j tails query state.1 covered false _ step supported
    intro designated
    have absent := Passed.not_designated Q j query state.1 (latched already)
    rw [absent] at designated
    cases designated
  · simp only [latch, StateT.run, support_map, Set.mem_image] at supported
    obtain ⟨step, supported, rfl⟩ := supported
    exact skeleton_covered setup codec checks context Q j tails query state.1 covered true (fun _ => rfl) step supported
  · simp only [latch, StateT.run, support_map, Set.mem_image] at supported
    obtain ⟨step, supported, rfl⟩ := supported
    exact skeleton_covered setup codec checks context Q j tails query state.1 covered false
      (fun designated => (selected designated).elim) step supported

/-- Every complete reply-dependent source program preserves actual designation and rooted-touch coverage. -/
theorem program_covered {Result : Type} (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (context : Context KemSK) (Q : Nat) (j : Fin (Q + 1))
    (tails : Services Response HiddenTable) (program : OracleComp ServerAuthSpec Result)
    (state : HiddenState KemSK) (latched : Latched Q j state)
    (covered : Covered setup context Q j state.1.1.ghost state.1.2.2)
    (result : Result × HiddenState KemSK)
    (supported : result ∈ support ((simulateQ (hiddenHandler setup codec checks context Q j
      (tableServices setup context tails)) program).run state)) :
    Latched Q j result.2 ∧ Covered setup context Q j result.2.1.1.ghost result.2.1.2.2 := by
  induction program using OracleComp.inductionOn generalizing state with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
      subst supported
      exact ⟨latched, covered⟩
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
        id_map, StateT.run_bind, mem_support_bind_iff] at supported
      obtain ⟨step, reached, supported⟩ := supported
      exact ih step.1 step.2
        (handler_latched setup codec checks context Q j _ query state latched step reached)
        (handler_covered setup codec checks context Q j tails query state latched covered step reached) supported

/-- The original context-initialized factor-side execution supplies both invariants itself, with arbitrary replaced factor values and full adaptive traffic. -/
theorem run_covered (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (adversary : Adversary) (revealSeed : Bool) (context : Context KemSK)
    (value : PqxdhServerAuthKeySchedule.Output) (Q : Nat) (j : Fin (Q + 1)) (result : HiddenState KemSK)
    (supported : result ∈ support (hiddenRun setup codec checks adversary revealSeed context Q j
      (factorServices setup codec checks context value))) :
    Latched Q j result ∧ Covered setup context Q j result.1.1.ghost result.1.2.2 := by
  simp only [hiddenRun, support_map, Set.mem_image] at supported
  obtain ⟨final, reached, rfl⟩ := supported
  apply program_covered setup codec checks context Q j (factorServices setup codec checks context value)
    _ _ _ _ final reached
  · intro impossible
    cases impossible
  · intro touch member
    cases member

/-- Every actual accepted observation contains a defined Beacon root input, including after factor replacement. This is a source rejection fact, not a cryptographic assumption. -/
def Resolved (setup : Setup baseSpec KemSK) (context : Context KemSK) (ghost : Ghost) : Prop :=
  ∀ snap, ghost.acceptance = some snap →
    (beaconInput setup context.seed context.scalar snap.touches).isSome = true

/-- Actual final publication either retains an earlier valid observation or captures the current defined input. -/
theorem Resolved.finish (setup : Setup baseSpec KemSK) (context : Context KemSK)
    (control : pqxdh.BeaconInitSent) (game : GameState KemSK) (staged : Option PqxdhBeaconPhase2Publication.Staged)
    (resolved : Resolved setup context game.ghost)
    (current : (beaconInput setup context.seed context.scalar game.ghost.touches).isSome = true) :
    Resolved setup context (finishOutcome control game staged).2.ghost := by
  intro snap found
  rcases Ghost.accept_frozen game.ghost _ snap found with old | fresh
  · exact resolved snap old
  · simpa only [fresh.1] using current

/-- A failed staged receive cannot create an accepted observation with an undefined input. -/
theorem Resolved.finish_none (setup : Setup baseSpec KemSK) (context : Context KemSK)
    (control : pqxdh.BeaconInitSent) (game : GameState KemSK) (resolved : Resolved setup context game.ghost) :
    Resolved setup context (finishOutcome control game none).2.ghost := by
  exact resolved

/-- A reached nonrejected initial derivation appends the first actual Beacon touch before the original publication checks. -/
theorem Resolved.finish_touched (setup : Setup baseSpec KemSK) (context : Context KemSK)
    (control : pqxdh.BeaconInitSent) (game : GameState KemSK) (resolved : Resolved setup context game.ghost)
    (clean : ∀ message, Touch.beacon message ∉ game.ghost.touches)
    (message : PqxdhJointDhExtractFamily.Message)
    (valid : (rootInput setup context.seed context.scalar message).isSome = true)
    (cache : CtxRomAuth.CtxRO.QueryCache) (staged : Option PqxdhBeaconPhase2Publication.Staged) :
    Resolved setup context
      (finishOutcome control { game with ctx := cache, ghost := { game.ghost with
        touches := game.ghost.touches ++ [.beacon message] } } staged).2.ghost := by
  apply Resolved.finish setup context control
    { game with ctx := cache, ghost := { game.ghost with touches := game.ghost.touches ++ [.beacon message] } } staged resolved
  simpa only [beaconInput, firstBeacon_after game.ghost.touches [] message clean, Option.bind_some] using valid

/-- An actual accepted initial response cannot use an undefined root input: rejected derivations never invoke a successful native tail. -/
theorem finish_resolved (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (context : Context KemSK) (tails : Services Response HiddenTable)
    (raw : Pqxdh.Bytes) (state : FlatState KemSK HiddenTable) (shape : Shape state.1)
    (resolved : Resolved setup context state.1.ghost) (chosen : Bool)
    (result : Option Pqxdh.Bytes × FlatState KemSK HiddenTable)
    (supported : result ∈ support ((finishStep setup codec (context.publicValue setup) context.beaconSeed
      (chosenServices setup context tails chosen) raw).run state)) :
    Resolved setup context result.2.1.ghost := by
  simp only [finishStep, StateT.run] at supported
  cases phase : state.1.beacon.beacon.phase with
  | initSent control prekey oneTime kem =>
      simp only [phase, mem_support_bind_iff] at supported
      obtain ⟨prepared, _, supported⟩ := supported
      cases found : prepared with
      | none =>
          simp only [found, support_pure, Set.mem_singleton_iff] at supported
          subst supported
          exact Resolved.finish_none setup context control state.1 resolved
      | some pending =>
          simp only [found, mem_support_bind_iff] at supported
          obtain ⟨derived, derivedSupported, supported⟩ := supported
          have facts := chosen_complete setup context tails chosen
            (PqxdhJointDhExtractRoot.beaconMessage (context.publicValue setup) pending.collected)
            state.2.2 derived derivedSupported
          cases reply : derived.1 with
          | rejected =>
              simp only [reply, support_pure, Set.mem_singleton_iff] at supported
              subst supported
              exact Resolved.finish_none setup context control
                { state.1 with ghost := { state.1.ghost with touches := state.1.ghost.touches ++
                  [.beacon (PqxdhJointDhExtractRoot.beaconMessage (context.publicValue setup) pending.collected)] } } resolved
          | root root =>
              simp only [reply, mem_support_bind_iff] at supported
              obtain ⟨staged, _, supported⟩ := supported
              simp only [support_pure, Set.mem_singleton_iff] at supported
              subst supported
              exact Resolved.finish_touched setup context control state.1 resolved
                (shape.clean ⟨control, prekey, oneTime, kem, phase⟩) _
                (facts.2.2 (by simp only [reply, ne_eq, reduceCtorEq, not_false_eq_true])) staged.2.2 staged.1
          | hidden =>
              simp only [reply, mem_support_bind_iff] at supported
              obtain ⟨staged, _, supported⟩ := supported
              simp only [support_pure, Set.mem_singleton_iff] at supported
              subst supported
              exact Resolved.finish_touched setup context control state.1 resolved
                (shape.clean ⟨control, prekey, oneTime, kem, phase⟩) _
                (facts.2.2 (by simp only [reply, ne_eq, reduceCtorEq, not_false_eq_true])) staged.2.2 staged.1
  | _ =>
      simp only [phase, support_pure, Set.mem_singleton_iff] at supported
      subst supported
      exact resolved

/-- The full source dispatch preserves defined inputs in every accepted observation, with both actual derive routes and arbitrary typed tail outcomes. -/
theorem skeleton_resolved (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (context : Context KemSK) (tails : Services Response HiddenTable)
    (query : ServerAuthSpec.Domain) (state : FlatState KemSK HiddenTable) (shape : Shape state.1)
    (resolved : Resolved setup context state.1.ghost) (chosen : Bool)
    (result : ServerAuthSpec.Range query × FlatState KemSK HiddenTable)
    (supported : result ∈ support ((skeleton setup codec checks (context.publicValue setup) context.beaconSeed
      (chosenServices setup context tails chosen) query).run state)) :
    Resolved setup context result.2.1.ghost := by
  cases query with
  | inl coin =>
      simp only [skeleton, StateT.run, support_map, Set.mem_image] at supported
      obtain ⟨value, _, rfl⟩ := supported
      exact resolved
  | inr query =>
      cases query with
      | accept raw =>
          simp only [skeleton, acceptStep, StateT.run, mem_support_bind_iff] at supported
          obtain ⟨collected, _, supported⟩ := supported
          cases found : collected.1 with
          | none =>
              simp only [found, support_pure, Set.mem_singleton_iff] at supported
              subst supported
              exact resolved
          | some input =>
              simp only [found] at supported
              split_ifs at supported with nonzero
              · obtain ⟨derived, _, supported⟩ := (mem_support_bind_iff _ _ _).1 supported
                simp only [support_pure, Set.mem_singleton_iff] at supported
                subst supported
                cases derived.1 <;> exact resolved
              · simp only [support_pure, Set.mem_singleton_iff] at supported
                subst supported
                exact resolved
      | finish raw => exact finish_resolved setup codec context tails raw state shape resolved chosen result supported
      | build index payload =>
          simp only [skeleton, buildStep, StateT.run] at supported
          cases found : state.1.pending index with
          | none =>
              simp only [found, support_pure, Set.mem_singleton_iff] at supported
              subst supported
              exact resolved
          | some token =>
              simp only [found, mem_support_bind_iff] at supported
              obtain ⟨built, _, supported⟩ := supported
              simp only [support_pure, Set.mem_singleton_iff] at supported
              subst supported
              exact resolved
      | hmac key bytes =>
          simp only [skeleton, hmacStep, StateT.run] at supported
          split_ifs at supported
          · obtain ⟨read, _, supported⟩ := (mem_support_bind_iff _ _ _).1 supported
            simp only [support_pure, Set.mem_singleton_iff] at supported
            subst supported
            exact resolved
          · simp only [support_pure, Set.mem_singleton_iff] at supported
            subst supported
            exact resolved
      | hash bytes =>
          simp only [skeleton, hashStep, StateT.run, mem_support_bind_iff] at supported
          obtain ⟨read, _, supported⟩ := supported
          simp only [support_pure, Set.mem_singleton_iff] at supported
          subst supported
          exact resolved
      | reveal keyId =>
          simp only [skeleton, StateT.run, support_pure, Set.mem_singleton_iff] at supported
          subst supported
          exact resolved

/-- The original designation and refusal wrapper preserve accepted-input validity through the actual ordinary and selected source handlers. -/
theorem handler_resolved (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (context : Context KemSK) (Q : Nat) (j : Fin (Q + 1)) (tails : Services Response HiddenTable)
    (query : ServerAuthSpec.Domain) (state : HiddenState KemSK) (shape : Shape state.1.1)
    (resolved : Resolved setup context state.1.1.ghost)
    (result : ServerAuthSpec.Range query × HiddenState KemSK)
    (supported : result ∈ support ((hiddenHandler setup codec checks context Q j
      (tableServices setup context tails) query).run state)) :
    Resolved setup context result.2.1.1.ghost := by
  simp only [hiddenHandler, StateT.run, support_map, Set.mem_image] at supported
  obtain ⟨middle, supported, rfl⟩ := supported
  rw [keepHiddenBad_game]
  simp only [once, StateT.run] at supported
  split_ifs at supported
  all_goals
    simp only [latch, StateT.run, support_map, Set.mem_image] at supported
    obtain ⟨step, supported, rfl⟩ := supported
    first
    | exact skeleton_resolved setup codec checks context tails query state.1 shape resolved false step supported
    | exact skeleton_resolved setup codec checks context tails query state.1 shape resolved true step supported

/-- Full adaptive source continuations retain the actual defined input of every accepted observation. -/
theorem program_resolved {Result : Type} (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (context : Context KemSK) (Q : Nat) (j : Fin (Q + 1))
    (tails : Services Response HiddenTable) (program : OracleComp ServerAuthSpec Result)
    (state : HiddenState KemSK) (shape : Shape state.1.1)
    (resolved : Resolved setup context state.1.1.ghost) (result : Result × HiddenState KemSK)
    (supported : result ∈ support ((simulateQ (hiddenHandler setup codec checks context Q j
      (tableServices setup context tails)) program).run state)) :
    Resolved setup context result.2.1.1.ghost := by
  induction program using OracleComp.inductionOn generalizing state with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
      subst supported
      exact resolved
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
        id_map, StateT.run_bind, mem_support_bind_iff] at supported
      obtain ⟨step, reached, supported⟩ := supported
      exact ih step.1 step.2
        (hidden_shape setup codec checks context Q j _ query state shape step reached)
        (handler_resolved setup codec checks context Q j tails query state shape resolved step reached) supported

/-- The literal context-initialized factor execution has no accepted observation with an undefined root input. -/
theorem run_resolved (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (adversary : Adversary) (revealSeed : Bool) (context : Context KemSK)
    (value : PqxdhServerAuthKeySchedule.Output) (Q : Nat) (j : Fin (Q + 1)) (result : HiddenState KemSK)
    (supported : result ∈ support (hiddenRun setup codec checks adversary revealSeed context Q j
      (factorServices setup codec checks context value))) :
    Resolved setup context result.1.1.ghost := by
  simp only [hiddenRun, support_map, Set.mem_image] at supported
  obtain ⟨final, reached, rfl⟩ := supported
  apply program_resolved setup codec checks context Q j (factorServices setup codec checks context value)
    _ _ (TraceInvariant.initial setup context Q j).shape _ final reached
  intro snap impossible
  cases impossible

/-- Actual owner attribution and an accepted, defined input force the designated table branch to have executed or refused. -/
theorem accepted_established (setup : Setup baseSpec KemSK) (context : Context KemSK)
    (Q : Nat) (j : Fin (Q + 1)) (game : GameState KemSK) (table : HiddenTable)
    (history : PqxdhServerAuthCtxAcceptanceHistory.History game)
    (resolved : Resolved setup context game.ghost)
    (covered : Covered setup context Q j game.ghost table)
    (snap : Snapshot) (accepted : game.ghost.acceptance = some snap)
    (owned : entryOwner setup context.seed context.scalar Q game.ghost = some j) :
    Established table := by
  obtain ⟨before, message, equal, clean, first, _⟩ := history.first game snap accepted
  by_cases session : j.val < Q
  · obtain ⟨serverMessage, reply, bytes, member, rooted, _⟩ :=
      owner_session_ghost setup context.seed context.scalar Q game.ghost snap
        (history.frozen snap accepted).1 before message equal clean j owned session
    apply covered (.session j.val serverMessage reply)
      ((history.frozen snap accepted).1.subset member)
    exact ⟨rfl, session, by simp only [rooted, Option.isSome_some]⟩
  · have last : j.val = Q := by omega
    have valid := resolved snap accepted
    simp only [beaconInput, first, Option.bind_some] at valid
    apply covered (.beacon message)
      ((history.frozen snap accepted).1.subset (by simp only [equal, List.mem_append, List.mem_cons, List.not_mem_nil, or_false, or_true]))
    exact ⟨last, valid⟩

/-- The original successful entry decision forces an actual selected input in the complete factor-side run; no caller supplies a designation witness. -/
theorem decision_hidden (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (adversary : Adversary) (context : Context KemSK) (value : PqxdhServerAuthKeySchedule.Output)
    (Q : Nat) (j : Fin (Q + 1)) (result : HiddenState KemSK)
    (supported : result ∈ support (hiddenRun setup codec checks adversary false context Q j
      (factorServices setup codec checks context value)))
    (decision : hiddenDecision setup context Q j result = true) :
    ∃ bytes, result.1.2.2.hidden = some bytes := by
  classical
  have event : result.1.2.2.bad = false ∧
      EntryEvent setup context.seed context.scalar Q j result.1.1.ghost := of_decide_eq_true decision
  have accepted : ∃ snap, result.1.1.ghost.acceptance = some snap := by
    rcases event.2.1 with ⟨snap, found, _⟩ | ⟨snap, found, _⟩ <;> exact ⟨snap, found⟩
  obtain ⟨snap, found⟩ := accepted
  have established := accepted_established setup context Q j result.1.1 result.1.2.2
    (PqxdhServerAuthCtxAcceptanceHistory.run_history setup codec checks adversary false context value Q j result supported)
    (run_resolved setup codec checks adversary false context value Q j result supported)
    (run_covered setup codec checks adversary false context value Q j result supported).2
    snap found event.2.2.2.2
  cases hidden : result.1.2.2.hidden with
  | none => simp only [Established, hidden, Option.isSome_none, event.1, Bool.false_eq_true, or_self] at established
  | some bytes => exact ⟨bytes, rfl⟩

/-- The actual successful entry decision identifies the selected table input with the final Beacon input in the same full source run. -/
theorem decision_input (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (adversary : Adversary) (context : Context KemSK) (value : PqxdhServerAuthKeySchedule.Output)
    (Q : Nat) (j : Fin (Q + 1)) (result : HiddenState KemSK)
    (supported : result ∈ support (hiddenRun setup codec checks adversary false context Q j
      (factorServices setup codec checks context value)))
    (decision : hiddenDecision setup context Q j result = true) :
    ∃ bytes, result.1.2.2.hidden = some bytes ∧
      beaconInput setup context.seed context.scalar result.1.1.ghost.touches = some bytes := by
  classical
  obtain ⟨bytes, hidden⟩ := decision_hidden setup codec checks adversary context value Q j result supported decision
  have event : result.1.2.2.bad = false ∧
      EntryEvent setup context.seed context.scalar Q j result.1.1.ghost := of_decide_eq_true decision
  have trace := run_trace setup codec checks context Q j (factorServices setup codec checks context value)
    adversary false result supported
  exact ⟨bytes, hidden, selected_input setup context Q j result.1.1.ghost
    trace.shape.once event.2.2.2.2 bytes (trace.selected bytes hidden)⟩

end BeaconcryptCore.Computational.PqxdhServerAuthDesignation

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthDesignation.Passed.step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthDesignation.Passed.step
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthDesignation.designated_passed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthDesignation.designated_passed
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthDesignation.handler_flag' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthDesignation.handler_flag
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthDesignation.handler_latched' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthDesignation.handler_latched
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthDesignation.Passed.not_designated' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthDesignation.Passed.not_designated
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthDesignation.chosen_complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthDesignation.chosen_complete
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthDesignation.Covered.transport' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthDesignation.Covered.transport
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthDesignation.Covered.append' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthDesignation.Covered.append
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthDesignation.accept_covered' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthDesignation.accept_covered
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthDesignation.finish_covered' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthDesignation.finish_covered
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthDesignation.public_established' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthDesignation.public_established
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthDesignation.skeleton_covered' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthDesignation.skeleton_covered
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthDesignation.keep_bad_covered' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthDesignation.keep_bad_covered
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthDesignation.handler_covered' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthDesignation.handler_covered
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthDesignation.program_covered' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthDesignation.program_covered
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthDesignation.run_covered' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthDesignation.run_covered
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthDesignation.Resolved.finish' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthDesignation.Resolved.finish
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthDesignation.Resolved.finish_none' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthDesignation.Resolved.finish_none
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthDesignation.Resolved.finish_touched' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthDesignation.Resolved.finish_touched
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthDesignation.finish_resolved' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthDesignation.finish_resolved
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthDesignation.skeleton_resolved' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthDesignation.skeleton_resolved
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthDesignation.handler_resolved' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthDesignation.handler_resolved
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthDesignation.program_resolved' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthDesignation.program_resolved
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthDesignation.run_resolved' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthDesignation.run_resolved
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthDesignation.accepted_established' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthDesignation.accepted_established
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthDesignation.decision_hidden' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthDesignation.decision_hidden
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthDesignation.decision_input' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthDesignation.decision_input
