import BeaconcryptCore.Computational.PqxdhServerAuthEntryBound
import BeaconcryptCore.Computational.PqxdhServerAuthEntryResourceGame

section TraceSection

open OracleComp OracleSpec ENNReal
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
set_option autoImplicit false

namespace BeaconcryptCore.Computational.PqxdhServerAuthCtxStop
open PqxdhServerAuthExperiment PqxdhServerAuthEntryFactor
open PqxdhJointIdentity PqxdhSecretInputKdf PqxdhJointKdfGame PqxdhJointGapDh
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}

/-- A selected session has the Beacon's input whenever the original owner event holds. Only uniqueness of the actual session message is needed; arbitrary tail outcomes and key aliases are permitted. -/
theorem selected_input (setup : Setup baseSpec KemSK) (context : Context KemSK)
    (Q : Nat) (j : Fin (Q + 1)) (ghost : Ghost)
    (once : ∀ index message reply message' reply', Touch.session index message reply ∈ ghost.touches →
      Touch.session index message' reply' ∈ ghost.touches → message = message')
    (owned : entryOwner setup context.seed context.scalar Q ghost = some j)
    (bytes : Pqxdh.Bytes) (selected : SelectedAt setup context.seed context.scalar Q j ghost bytes) :
    beaconInput setup context.seed context.scalar ghost.touches = some bytes := by
  by_cases session : j.val < Q
  · obtain ⟨message, reply, touched, rooted⟩ :
        ∃ message reply, Touch.session j.val message reply ∈ ghost.touches ∧
          rootInput setup context.seed context.scalar message = some bytes := by
      simpa only [SelectedAt, session, ↓reduceIte] using selected
    unfold entryOwner at owned
    cases input : beaconInput setup context.seed context.scalar ghost.touches with
    | none =>
        simp only [input, Option.some.injEq] at owned
        have value := congrArg Fin.val owned
        simp only [Fin.val_last] at value
        omega
    | some value =>
        simp only [input] at owned
        cases found : ghost.touches.find? (fun touch => decide
            (touchInput setup context.seed context.scalar touch = some value)) with
        | none =>
            simp only [found, Option.some.injEq] at owned
            have equal := congrArg Fin.val owned
            simp only [Fin.val_last] at equal
            omega
        | some touch =>
            have member := List.mem_of_find?_eq_some found
            have hit :=  List.find?_some found
            cases touch with
            | adversary other => simp [found] at owned
            | beacon other =>
                simp only [found, Option.some.injEq] at owned
                have equal := congrArg Fin.val owned
                simp only [Fin.val_last] at equal
                omega
            | session index other answer =>
                simp only [found] at owned
                split_ifs at owned with bound
                · have equal : index = j.val := congrArg Fin.val (Option.some.inj owned)
                  subst index
                  have same := once j.val message reply other answer touched member
                  have rooted' : rootInput setup context.seed context.scalar other = some value := by
                    exact of_decide_eq_true hit
                  rw [← same, rooted] at rooted'
                  exact rooted'.symm
  · simpa only [SelectedAt, session, ↓reduceIte] using selected

/-- The original per-entry event permits at most one marked Server attempt. Its two candidate witnesses come from the actual touch log at the selected input, rather than equality of roots or keys. -/
theorem marked_unique (setup : Setup baseSpec KemSK) (context : Context KemSK)
    (Q : Nat) (j : Fin (Q + 1)) (state : HiddenState KemSK)
    (once : ∀ index message reply message' reply', Touch.session index message reply ∈ state.1.1.ghost.touches →
      Touch.session index message' reply' ∈ state.1.1.ghost.touches → message = message')
    (selected : ∀ bytes, state.1.2.2.hidden = some bytes →
      SelectedAt setup context.seed context.scalar Q j state.1.1.ghost bytes)
    (marked : ∀ index, state.1.2.1 index = true →
      ∃ message reply bytes, Touch.session index message reply ∈ state.1.1.ghost.touches ∧
        state.1.2.2.hidden = some bytes ∧ rootInput setup context.seed context.scalar message = some bytes)
    (event : EntryEvent setup context.seed context.scalar Q j state.1.1.ghost)
    (first second : Nat) (firstMarked : state.1.2.1 first = true)
    (secondMarked : state.1.2.1 second = true) : first = second := by
  by_contra distinct
  obtain ⟨firstMessage, firstReply, bytes, firstTouch, hidden, firstInput⟩ := marked first firstMarked
  obtain ⟨secondMessage, secondReply, other, secondTouch, otherHidden, secondInput⟩ := marked second secondMarked
  have same : other = bytes := Option.some.inj (otherHidden.symm.trans hidden)
  subst other
  have beacon := selected_input setup context Q j state.1.1.ghost once event.2.2.2 bytes (selected bytes hidden)
  exact event.2.2.1 ⟨first, second, firstMessage, secondMessage, firstReply, secondReply, bytes,
    distinct, firstTouch, secondTouch, beacon, firstInput, secondInput⟩

/-- Only source chronology is needed to attribute the selected input. It is independent of sampled root or message-key values and of any successful tail result. -/
structure Shape (game : GameState KemSK) : Prop where
  touched : ∀ index message reply, Touch.session index message reply ∈ game.ghost.touches → index < game.sessions
  once : ∀ index message reply message' reply', Touch.session index message reply ∈ game.ghost.touches →
    Touch.session index message' reply' ∈ game.ghost.touches → message = message'
  clean : InitSent game → ∀ message, Touch.beacon message ∉ game.ghost.touches

/-- Mark provenance retains literal source touch/input evidence and the original designation latch. -/
structure TraceInvariant (setup : Setup baseSpec KemSK) (context : Context KemSK)
    (Q : Nat) (j : Fin (Q + 1)) (state : HiddenState KemSK) : Prop where
  shape : Shape state.1.1
  unselected : state.2 = false → state.1.2.2.hidden = none
  selected : ∀ bytes, state.1.2.2.hidden = some bytes →
    SelectedAt setup context.seed context.scalar Q j state.1.1.ghost bytes
  marked : ∀ index, state.1.2.1 index = true →
    ∃ message reply bytes, Touch.session index message reply ∈ state.1.1.ghost.touches ∧
      state.1.2.2.hidden = some bytes ∧ rootInput setup context.seed context.scalar message = some bytes

/-- Every selected mark was allocated strictly before the next source attempt. -/
theorem TraceInvariant.below (setup : Setup baseSpec KemSK) (context : Context KemSK)
    (Q : Nat) (j : Fin (Q + 1)) (state : HiddenState KemSK)
    (invariant : TraceInvariant setup context Q j state) (index : Nat)
    (marked : state.1.2.1 index = true) : index < state.1.1.sessions := by
  obtain ⟨message, reply, _, touched, _⟩ := invariant.marked index marked
  exact invariant.shape.touched index message reply touched

/-- Literal empty instrumentation supplies the trace invariant independently of later tail replies. -/
theorem TraceInvariant.initial (setup : Setup baseSpec KemSK) (context : Context KemSK)
    (Q : Nat) (j : Fin (Q + 1)) :
    TraceInvariant setup context Q j
      ((contextState setup context, fun _ => false, ⟨∅, none, false⟩), false) := by
  refine ⟨⟨?_, ?_, ?_⟩, (fun _ => rfl), ?_, ?_⟩
  · intro index message reply member
    cases member
  · intro index message reply message' reply' member
    cases member
  · intro active message member
    cases member
  · intro bytes found
    cases found
  · intro index marked
    cases marked

/-- The actual allocation prefix increments the attempt count even when preparation later rejects. -/
theorem Shape.prefix (game : GameState KemSK) (shape : Shape game) (consumed : List Pqxdh.Bytes) :
    Shape (acceptedPrefix game consumed) := by
  exact ⟨fun index message reply member => Nat.lt_succ_of_lt (shape.touched index message reply member),
    shape.once, shape.clean⟩

/-- The exact source accept consumer appends one touch at the newly allocated index, preserving unique session origins even if derivation rejects. -/
theorem Shape.derived (setup : Setup baseSpec KemSK) (publicValue : PublicChallenge)
    (game : GameState KemSK) (shape : Shape game) (consumed : List Pqxdh.Bytes)
    (input : PqxdhServerRootPreparation.Inputs Reader ScalarBytes PeerEncoding) (reply : Reply) :
    Shape (afterDerive setup publicValue game.sessions input reply (acceptedPrefix game consumed)).2 := by
  have resources := afterDerive_resources setup publicValue game.sessions input reply (acceptedPrefix game consumed)
  refine ⟨?_, ?_, ?_⟩
  · intro index message value member
    rw [resources.1]
    rw [afterDerive_touches] at member
    rcases List.mem_append.mp member with old | fresh
    · exact Nat.lt_succ_of_lt (shape.touched index message value old)
    · have same := List.mem_singleton.mp fresh
      cases same
      exact Nat.lt_succ_self _
  · intro index message value other answer first second
    rw [afterDerive_touches] at first second
    rcases List.mem_append.mp first with first | first
    · rcases List.mem_append.mp second with second | second
      · exact shape.once index message value other answer first second
      · have same := List.mem_singleton.mp second
        cases same
        exact (Nat.lt_irrefl _ (shape.touched _ _ _ first)).elim
    · have same := List.mem_singleton.mp first
      cases same
      rcases List.mem_append.mp second with second | second
      · exact (Nat.lt_irrefl _ (shape.touched _ _ _ second)).elim
      · have same := List.mem_singleton.mp second
        cases same
        rfl
  · intro active message member
    have activeBefore : InitSent game := by
      unfold InitSent at active ⊢
      rw [resources.2.1] at active
      exact active
    rw [afterDerive_touches] at member
    rcases List.mem_append.mp member with old | fresh
    · exact shape.clean activeBefore message old
    · simp at fresh

/-- A finish always exhausts the native InitSent phase, while preserving exactly its supplied touch history. -/
theorem Shape.finish (control : pqxdh.BeaconInitSent) (game : GameState KemSK)
    (staged : Option PqxdhBeaconPhase2Publication.Staged)
    (touched : ∀ index message reply, Touch.session index message reply ∈ game.ghost.touches → index < game.sessions)
    (once : ∀ index message reply message' reply', Touch.session index message reply ∈ game.ghost.touches →
      Touch.session index message' reply' ∈ game.ghost.touches → message = message') :
    Shape (finishOutcome control game staged).2 := by
  have resources := finishOutcome_resources control game staged
  refine ⟨?_, ?_, ?_⟩
  · intro index message reply member
    rw [finishOutcome_touches] at member
    rw [resources.1]
    exact touched index message reply member
  · intro index message reply message' reply' first second
    rw [finishOutcome_touches] at first second
    exact once index message reply message' reply' first second
  · rintro ⟨control', prekey, oneTime, kem, phase⟩ message member
    exact (finish_phase control game.beacon staged control' prekey oneTime kem phase).elim

/-- Appending a Beacon touch preserves the exact previous Server-attempt information before the final phase transition. -/
theorem Shape.finishTouched (control : pqxdh.BeaconInitSent) (game : GameState KemSK)
    (shape : Shape game) (message : PqxdhJointDhExtractFamily.Message)
    (cache : CtxRomAuth.CtxRO.QueryCache) (staged : Option PqxdhBeaconPhase2Publication.Staged) :
    Shape (finishOutcome control { game with
      ctx := cache
      ghost := { game.ghost with touches := game.ghost.touches ++ [.beacon message] } } staged).2 := by
  apply Shape.finish
  · intro index other reply member
    have old : Touch.session index other reply ∈ game.ghost.touches := by
      simpa only [List.mem_append, List.mem_singleton, reduceCtorEq, or_false] using member
    exact shape.touched index other reply old
  · intro index other reply another answer first second
    apply shape.once index other reply another answer
    · simpa only [List.mem_append, List.mem_singleton, reduceCtorEq, or_false] using first
    · simpa only [List.mem_append, List.mem_singleton, reduceCtorEq, or_false] using second

end BeaconcryptCore.Computational.PqxdhServerAuthCtxStop

end TraceSection

section ShapeSection

open OracleComp OracleSpec ENNReal
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
set_option autoImplicit false

namespace BeaconcryptCore.Computational.PqxdhServerAuthCtxStop
open PqxdhServerAuthExperiment PqxdhServerAuthEntryFactor
open PqxdhJointIdentity PqxdhSecretInputKdf PqxdhJointKdfGame PqxdhJointGapDh
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response τ : Type}

/-- Every actual finish keeps Server-attempt chronology and exhausts the one-shot Beacon phase, for arbitrary typed hidden-tail replies. -/
theorem finish_shape (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (publicValue : PublicChallenge) (beaconSeed : IdentitySeed) (services : Services Response τ)
    (raw : Pqxdh.Bytes) (state : FlatState KemSK τ) (shape : Shape state.1)
    (result : Option Pqxdh.Bytes × FlatState KemSK τ)
    (supported : result ∈ support ((finishStep setup codec publicValue beaconSeed services raw).run state)) :
    Shape result.2.1 := by
  simp only [finishStep, StateT.run] at supported
  cases phase : state.1.beacon.beacon.phase with
  | initSent control prekey oneTime kem =>
      simp only [phase, mem_support_bind_iff] at supported
      obtain ⟨prepared, _, supported⟩ := supported
      cases found : prepared with
      | none =>
          simp only [found, support_pure, Set.mem_singleton_iff] at supported
          subst supported
          exact Shape.finish control state.1 none shape.touched shape.once
      | some pending =>
          simp only [found, mem_support_bind_iff] at supported
          obtain ⟨derived, _, supported⟩ := supported
          cases reply : derived.1 with
          | rejected =>
              simp only [reply, support_pure, Set.mem_singleton_iff] at supported
              subst supported
              exact Shape.finishTouched control state.1 shape _ state.1.ctx none
          | root root =>
              simp only [reply, mem_support_bind_iff] at supported
              obtain ⟨staged, _, supported⟩ := supported
              simp only [support_pure, Set.mem_singleton_iff] at supported
              subst supported
              exact Shape.finishTouched control state.1 shape _ staged.2.2 staged.1
          | hidden =>
              simp only [reply, mem_support_bind_iff] at supported
              obtain ⟨staged, _, supported⟩ := supported
              simp only [support_pure, Set.mem_singleton_iff] at supported
              subst supported
              exact Shape.finishTouched control state.1 shape _ staged.2.2 staged.1
  | _ =>
      simp only [phase, support_pure, Set.mem_singleton_iff] at supported
      subst supported
      exact shape

/-- The entire original dispatch preserves chronology for every table reply and every typed tail outcome. -/
theorem skeleton_shape (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (publicValue : PublicChallenge) (beaconSeed : IdentitySeed) (services : Services Response τ)
    (query : ServerAuthSpec.Domain) (state : FlatState KemSK τ) (shape : Shape state.1)
    (result : ServerAuthSpec.Range query × FlatState KemSK τ)
    (supported : result ∈ support ((skeleton setup codec checks publicValue beaconSeed services query).run state)) :
    Shape result.2.1 := by
  cases query with
  | inl coin =>
      simp only [skeleton, StateT.run, support_map, Set.mem_image] at supported
      obtain ⟨value, _, rfl⟩ := supported
      exact shape
  | inr query =>
      cases query with
      | accept raw =>
          simp only [skeleton, acceptStep, StateT.run, mem_support_bind_iff] at supported
          obtain ⟨collected, _, supported⟩ := supported
          cases found : collected.1 with
          | none =>
              simp only [found, support_pure, Set.mem_singleton_iff] at supported
              subst supported
              exact Shape.prefix state.1 shape collected.2
          | some input =>
              simp only [found] at supported
              split_ifs at supported with nonzero
              · obtain ⟨derived, _, supported⟩ := (mem_support_bind_iff _ _ _).1 supported
                simp only [support_pure, Set.mem_singleton_iff] at supported
                subst supported
                exact Shape.derived setup publicValue state.1 shape collected.2 input derived.1
              · simp only [support_pure, Set.mem_singleton_iff] at supported
                subst supported
                exact Shape.prefix state.1 shape collected.2
      | build session payload =>
          simp only [skeleton, buildStep, StateT.run] at supported
          cases found : state.1.pending session with
          | none =>
              simp only [found, support_pure, Set.mem_singleton_iff] at supported
              subst supported
              exact shape
          | some token =>
              simp only [found, mem_support_bind_iff] at supported
              obtain ⟨built, _, supported⟩ := supported
              simp only [support_pure, Set.mem_singleton_iff] at supported
              subst supported
              exact ⟨shape.touched, shape.once, shape.clean⟩
      | finish raw =>
          exact finish_shape setup codec publicValue beaconSeed services raw state shape result supported
      | hmac key bytes =>
          simp only [skeleton, hmacStep, StateT.run] at supported
          split_ifs at supported with inside
          · obtain ⟨read, _, supported⟩ := (mem_support_bind_iff _ _ _).1 supported
            simp only [support_pure, Set.mem_singleton_iff] at supported
            subst supported
            refine ⟨?_, ?_, ?_⟩
            · intro index message reply member
              apply shape.touched index message reply
              simpa only [List.mem_append, List.mem_singleton, reduceCtorEq, or_false] using member
            · intro index message reply other answer first second
              apply shape.once index message reply other answer
              · simpa only [List.mem_append, List.mem_singleton, reduceCtorEq, or_false] using first
              · simpa only [List.mem_append, List.mem_singleton, reduceCtorEq, or_false] using second
            · intro active message member
              apply shape.clean active message
              simpa only [List.mem_append, List.mem_singleton, reduceCtorEq, or_false] using member
          · simp only [support_pure, Set.mem_singleton_iff] at supported
            subst supported
            exact shape
      | hash bytes =>
          simp only [skeleton, hashStep, StateT.run, mem_support_bind_iff] at supported
          obtain ⟨read, _, supported⟩ := supported
          simp only [support_pure, Set.mem_singleton_iff] at supported
          subst supported
          exact ⟨shape.touched, shape.once, shape.clean⟩
      | reveal key =>
          simp only [skeleton, StateT.run, support_pure, Set.mem_singleton_iff] at supported
          subst supported
          exact shape

/-- The designation latch and sticky table refusal do not alter actual source chronology. -/
theorem hidden_shape (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (context : Context KemSK) (Q : Nat) (j : Fin (Q + 1)) (services : Services Response HiddenTable)
    (query : ServerAuthSpec.Domain) (state : HiddenState KemSK) (shape : Shape state.1.1)
    (result : ServerAuthSpec.Range query × HiddenState KemSK)
    (supported : result ∈ support ((hiddenHandler setup codec checks context Q j services query).run state)) :
    Shape result.2.1.1 := by
  simp only [hiddenHandler, StateT.run, support_map, Set.mem_image] at supported
  obtain ⟨middle, supported, rfl⟩ := supported
  rw [keepHiddenBad_game]
  simp only [once, StateT.run] at supported
  split_ifs at supported
  all_goals
    simp only [latch, StateT.run, support_map, Set.mem_image] at supported
    obtain ⟨step, supported, rfl⟩ := supported
    exact skeleton_shape setup codec checks (context.publicValue setup) context.beaconSeed _ query state.1 shape step supported

/-- Every adaptive reply-dependent continuation retains the original source's fresh session indices and one-shot Beacon chronology. -/
theorem client_shape (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (context : Context KemSK) (Q : Nat) (j : Fin (Q + 1)) (services : Services Response HiddenTable)
    {Result : Type} (client : OracleComp ServerAuthSpec Result) (state : HiddenState KemSK)
    (shape : Shape state.1.1) (result : Result × HiddenState KemSK)
    (supported : result ∈ support ((simulateQ (hiddenHandler setup codec checks context Q j services) client).run state)) :
    Shape result.2.1.1 := by
  induction client using OracleComp.inductionOn generalizing state with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
      subst supported
      exact shape
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
        id_map, StateT.run_bind, mem_support_bind_iff] at supported
      obtain ⟨step, stepSupported, supported⟩ := supported
      exact ih step.1 step.2 (hidden_shape setup codec checks context Q j services query state shape step stepSupported) supported

end BeaconcryptCore.Computational.PqxdhServerAuthCtxStop

end ShapeSection

section TableSection

open OracleComp OracleSpec ENNReal
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
set_option autoImplicit false

namespace BeaconcryptCore.Computational.PqxdhServerAuthCtxStop
open PqxdhServerAuthExperiment PqxdhServerAuthEntryFactor
open PqxdhJointIdentity PqxdhSecretInputKdf PqxdhJointKdfGame PqxdhJointGapDh
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}

/-- Tail callbacks retain their exact types and outcomes; only the unchanged source table services are fixed here. -/
noncomputable def tableServices (setup : Setup baseSpec KemSK) (context : Context KemSK)
    (tails : Services Response HiddenTable) : Services Response HiddenTable :=
  { tails with
    derive := hiddenDerive setup.hmac setup.joint setup.dh context.seed context.scalar
    table := hiddenPublic }

/-- Exact label provenance of a reached table derivation, including already-refused source branches. -/
structure DeriveTrace (setup : Setup baseSpec KemSK) (context : Context KemSK)
    (message : PqxdhJointDhExtractFamily.Message) (before : HiddenTable) (result : Reply × HiddenTable) : Prop where
  retained : ∀ bytes, before.hidden = some bytes → result.2.hidden = some bytes
  origin : ∀ bytes, result.2.hidden = some bytes →
    before.hidden = some bytes ∨ rootInput setup context.seed context.scalar message = some bytes
  hidden : result.1.isHidden = true → ∃ bytes, result.2.hidden = some bytes ∧
    rootInput setup context.seed context.scalar message = some bytes

/-- The literal ordinary derivation preserves its selected-input label on every reply. -/
theorem derive_retains (setup : Setup baseSpec KemSK) (context : Context KemSK)
    (message : PqxdhJointDhExtractFamily.Message) (before : HiddenTable) (result : Reply × HiddenTable)
    (supported : result ∈ support ((hiddenDerive setup.hmac setup.joint setup.dh
      context.seed context.scalar message).run before)) : result.2.hidden = before.hidden := by
  simp only [hiddenDerive, StateT.run] at supported
  cases input : PqxdhJointDhExtractFamily.input setup.joint setup.dh context.seed context.scalar message with
  | none =>
      simp only [input, support_pure, Set.mem_singleton_iff] at supported
      subst supported
      rfl
  | some bytes =>
      simp only [input] at supported
      split at supported
      · simp only [support_pure, Set.mem_singleton_iff] at supported
        subst supported
        rfl
      · simp only [ordinaryHiddenDerive, StateT.run, support_map, Set.mem_image] at supported
        obtain ⟨read, _, rfl⟩ := supported
        rfl

/-- Every ordinary hidden-table reply exposes exact input provenance, without a good-cache premise. -/
theorem derive_trace (setup : Setup baseSpec KemSK) (context : Context KemSK)
    (message : PqxdhJointDhExtractFamily.Message) (before : HiddenTable) (result : Reply × HiddenTable)
    (supported : result ∈ support ((hiddenDerive setup.hmac setup.joint setup.dh
      context.seed context.scalar message).run before)) : DeriveTrace setup context message before result := by
  have kept := derive_retains setup context message before result supported
  exact ⟨fun bytes found => kept.trans found, fun bytes found => Or.inl (kept.symm.trans found),
    hiddenDerive_hidden setup context.seed context.scalar message before result supported⟩

/-- The actual designated derivation records its exact input or refuses a prior cache hit. Rejection and cache-hit branches retain their original work and state. -/
theorem select_trace (setup : Setup baseSpec KemSK) (context : Context KemSK)
    (message : PqxdhJointDhExtractFamily.Message) (before : HiddenTable)
    (unselected : before.hidden = none) (result : Reply × HiddenTable)
    (supported : result ∈ support ((selectHidden setup.joint setup.dh
      context.seed context.scalar message).run before)) : DeriveTrace setup context message before result := by
  have impossible : ∀ bytes, before.hidden ≠ some bytes := by simp only [unselected, ne_eq, reduceCtorEq, not_false_eq_true, implies_true]
  simp only [selectHidden, StateT.run] at supported
  cases input : PqxdhJointDhExtractFamily.input setup.joint setup.dh context.seed context.scalar message with
  | none =>
      simp only [input, support_pure, Set.mem_singleton_iff] at supported
      subst supported
      exact ⟨fun bytes found => (impossible bytes found).elim,
        fun bytes found => (impossible bytes found).elim, fun hidden => Bool.noConfusion hidden⟩
  | some bytes =>
      simp only [input] at supported
      cases cached : before.cache bytes with
      | some value =>
          simp only [cached, support_pure, Set.mem_singleton_iff] at supported
          subst supported
          exact ⟨fun bytes found => (impossible bytes found).elim,
            fun bytes found => (impossible bytes found).elim, fun hidden => Bool.noConfusion hidden⟩
      | none =>
          simp only [cached, support_pure, Set.mem_singleton_iff] at supported
          subst supported
          refine ⟨fun bytes found => (impossible bytes found).elim, ?_, ?_⟩
          · intro other found
            exact Or.inr (input.trans found)
          · intro hidden
            exact ⟨bytes, rfl, input⟩

/-- Public Extract requests never alter the selected input, including the exact query that raises refusal. -/
theorem public_retains (bytes : Pqxdh.Bytes) (before : HiddenTable) (result : HmacBlock × HiddenTable)
    (supported : result ∈ support ((hiddenPublic bytes).run before)) : result.2.hidden = before.hidden := by
  simp only [hiddenPublic, StateT.run] at supported
  split at supported
  · simp only [support_pure, Set.mem_singleton_iff] at supported
    subst supported
    rfl
  · simp only [support_map, Set.mem_image] at supported
    obtain ⟨read, _, rfl⟩ := supported
    rfl

/-- The source designation changes only the actual derive callback; both typed tail continuations remain identical. -/
noncomputable def chosenServices (setup : Setup baseSpec KemSK) (context : Context KemSK)
    (tails : Services Response HiddenTable) (chosen : Bool) : Services Response HiddenTable :=
  if chosen then selectingServices setup context (tableServices setup context tails)
  else tableServices setup context tails

/-- Both concrete derive routes supply the provenance conditions used by the actual source transition. -/
theorem chosen_trace (setup : Setup baseSpec KemSK) (context : Context KemSK)
    (tails : Services Response HiddenTable) (chosen : Bool)
    (message : PqxdhJointDhExtractFamily.Message) (before : HiddenTable)
    (unselected : chosen = true → before.hidden = none) (result : Reply × HiddenTable)
    (supported : result ∈ support (((chosenServices setup context tails chosen).derive message).run before)) :
    DeriveTrace setup context message before result ∧
      (chosen = false → result.2.hidden = before.hidden) := by
  cases chosen with
  | false =>
      exact ⟨derive_trace setup context message before result supported,
        fun _ => derive_retains setup context message before result supported⟩
  | true =>
      exact ⟨select_trace setup context message before (unselected rfl) result supported,
        fun impossible => Bool.noConfusion impossible⟩

end BeaconcryptCore.Computational.PqxdhServerAuthCtxStop

end TableSection

section TransitionsSection

open OracleComp OracleSpec ENNReal
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
set_option autoImplicit false

namespace BeaconcryptCore.Computational.PqxdhServerAuthCtxStop
open PqxdhServerAuthExperiment PqxdhServerAuthEntryFactor
open PqxdhJointIdentity PqxdhSecretInputKdf PqxdhJointKdfGame PqxdhJointGapDh
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}

/-- The literal source allocation prefix retains every mark and selected-input witness, even on preparation rejection. -/
theorem TraceInvariant.prefix (setup : Setup baseSpec KemSK) (context : Context KemSK)
    (Q : Nat) (j : Fin (Q + 1)) (state : HiddenState KemSK)
    (invariant : TraceInvariant setup context Q j state) (consumed : List Pqxdh.Bytes) (chosen : Bool) :
    TraceInvariant setup context Q j
      ((acceptedPrefix state.1.1 consumed, state.1.2), state.2 || chosen) := by
  refine ⟨Shape.prefix state.1.1 invariant.shape consumed, ?_, invariant.selected, invariant.marked⟩
  intro flag
  exact invariant.unselected (Bool.or_eq_false_iff.mp flag).1

/-- The original allocation and actual derive reply supply complete mark provenance. The operational table conditions are instantiated by its two unchanged interpreters. -/
theorem TraceInvariant.accept (setup : Setup baseSpec KemSK) (context : Context KemSK)
    (Q : Nat) (j : Fin (Q + 1)) (state : HiddenState KemSK)
    (invariant : TraceInvariant setup context Q j state) (consumed : List Pqxdh.Bytes) (chosen : Bool)
    (input : PqxdhServerRootPreparation.Inputs Reader ScalarBytes PeerEncoding) (reply : Reply) (next : HiddenTable)
    (derived : DeriveTrace setup context (PqxdhServerRelatedRootInput.message input) state.1.2.2 (reply, next))
    (ordinary : chosen = false → next.hidden = state.1.2.2.hidden)
    (designated : chosen = true → state.1.1.sessions = j.val ∧ j.val < Q) :
    TraceInvariant setup context Q j
      (((afterDerive setup (context.publicValue setup) state.1.1.sessions input reply
          (acceptedPrefix state.1.1 consumed)).2,
        acceptedMarks state.1.2.1 state.1.1.sessions reply, next), state.2 || chosen) := by
  have grown : state.1.1.ghost.touches <+:
      (afterDerive setup (context.publicValue setup) state.1.1.sessions input reply
        (acceptedPrefix state.1.1 consumed)).2.ghost.touches := by
    rw [afterDerive_touches]
    exact List.prefix_append _ _
  refine ⟨Shape.derived setup (context.publicValue setup) state.1.1 invariant.shape consumed input reply,
    ?_, ?_, ?_⟩
  · intro flag
    have flags := Bool.or_eq_false_iff.mp flag
    exact (ordinary flags.2).trans (invariant.unselected flags.1)
  · intro bytes found
    by_cases old : state.1.2.2.hidden = some bytes
    · exact selectedAt_prefix setup context.seed context.scalar Q j _ _ bytes grown (invariant.selected bytes old)
    · have rooted := (derived.origin bytes found).resolve_left old
      have chosenTrue : chosen = true := by
        cases h : chosen with
        | true => rfl
        | false => exact (old ((ordinary h).symm.trans found)).elim
      obtain ⟨index, inside⟩ := designated chosenTrue
      simp only [SelectedAt, inside, ↓reduceIte]
      refine ⟨PqxdhServerRelatedRootInput.message input, reply.value, ?_, rooted⟩
      rw [afterDerive_touches, index]
      exact List.mem_append_right _ (List.mem_singleton_self _)
  · intro index marked
    by_cases fresh : reply.isHidden = true ∧ index = state.1.1.sessions
    · obtain ⟨bytes, hidden, rooted⟩ := derived.hidden fresh.1
      refine ⟨PqxdhServerRelatedRootInput.message input, reply.value, bytes, ?_, hidden, rooted⟩
      rw [afterDerive_touches, fresh.2]
      exact List.mem_append_right _ (List.mem_singleton_self _)
    · have old : state.1.2.1 index = true := by
        unfold acceptedMarks at marked
        split at marked
        · rename_i hidden
          simpa only [Function.update_of_ne (fun same => fresh ⟨hidden, same⟩)] using marked
        · exact marked
      obtain ⟨message, value, bytes, touched, hidden, rooted⟩ := invariant.marked index old
      exact ⟨message, value, bytes, grown.subset touched, derived.retained bytes hidden, rooted⟩

/-- Unrelated actual state updates transport the private provenance through their exact touch prefix and unchanged mark/input fields. -/
theorem TraceInvariant.keep (setup : Setup baseSpec KemSK) (context : Context KemSK)
    (Q : Nat) (j : Fin (Q + 1)) (before after : HiddenState KemSK)
    (invariant : TraceInvariant setup context Q j before) (shape : Shape after.1.1)
    (grown : before.1.1.ghost.touches <+: after.1.1.ghost.touches)
    (marks : after.1.2.1 = before.1.2.1) (hidden : after.1.2.2.hidden = before.1.2.2.hidden)
    (flag : after.2 = false → before.2 = false) : TraceInvariant setup context Q j after := by
  refine ⟨shape, fun fresh => hidden.trans (invariant.unselected (flag fresh)), ?_, ?_⟩
  · intro bytes found
    exact selectedAt_prefix setup context.seed context.scalar Q j _ _ bytes grown
      (invariant.selected bytes (hidden.symm.trans found))
  · intro index marked
    obtain ⟨message, reply, bytes, touched, selected, rooted⟩ := invariant.marked index (marks ▸ marked)
    exact ⟨message, reply, bytes, grown.subset touched, hidden.trans selected, rooted⟩

/-- The exact post-input Beacon continuation preserves private source provenance for every staged result and cache effect. -/
theorem TraceInvariant.finish (setup : Setup baseSpec KemSK) (context : Context KemSK)
    (Q : Nat) (j : Fin (Q + 1)) (state : HiddenState KemSK)
    (invariant : TraceInvariant setup context Q j state) (control : pqxdh.BeaconInitSent)
    (active : InitSent state.1.1) (message : PqxdhJointDhExtractFamily.Message)
    (cache : CtxRomAuth.CtxRO.QueryCache) (staged : Option PqxdhBeaconPhase2Publication.Staged)
    (chosen : Bool) (reply : Reply) (next : HiddenTable)
    (derived : DeriveTrace setup context message state.1.2.2 (reply, next))
    (ordinary : chosen = false → next.hidden = state.1.2.2.hidden)
    (designated : chosen = true → j.val = Q) :
    TraceInvariant setup context Q j
      (((finishAfterInput control state.1.1 message cache staged).2, state.1.2.1, next), state.2 || chosen) := by
  have grown : state.1.1.ghost.touches <+:
      (finishAfterInput control state.1.1 message cache staged).2.ghost.touches := by
    simp only [finishAfterInput, finishOutcome_touches, finishTouched]
    exact List.prefix_append _ _
  refine ⟨Shape.finishTouched control state.1.1 invariant.shape message cache staged, ?_, ?_, ?_⟩
  · intro flag
    have flags := Bool.or_eq_false_iff.mp flag
    exact (ordinary flags.2).trans (invariant.unselected flags.1)
  · intro bytes found
    by_cases old : state.1.2.2.hidden = some bytes
    · exact selectedAt_prefix setup context.seed context.scalar Q j _ _ bytes grown (invariant.selected bytes old)
    · have rooted := (derived.origin bytes found).resolve_left old
      have chosenTrue : chosen = true := by
        cases h : chosen with
        | true => rfl
        | false => exact (old ((ordinary h).symm.trans found)).elim
      have last := designated chosenTrue
      simp only [SelectedAt, last, Nat.lt_irrefl, ↓reduceIte, finishAfterInput,
        finishOutcome_touches, finishTouched, beaconInput]
      rw [firstBeacon_after _ [] _ (invariant.shape.clean active)]
      exact rooted
  · intro index marked
    obtain ⟨other, value, bytes, touched, hidden, rooted⟩ := invariant.marked index marked
    exact ⟨other, value, bytes, grown.subset touched, derived.retained bytes hidden, rooted⟩

end BeaconcryptCore.Computational.PqxdhServerAuthCtxStop

end TransitionsSection

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxStop.selected_input' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxStop.selected_input
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxStop.marked_unique' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxStop.marked_unique
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxStop.TraceInvariant.below' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxStop.TraceInvariant.below
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxStop.TraceInvariant.initial' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxStop.TraceInvariant.initial
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxStop.Shape.prefix' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxStop.Shape.prefix
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxStop.Shape.derived' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxStop.Shape.derived
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxStop.Shape.finish' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxStop.Shape.finish
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxStop.Shape.finishTouched' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxStop.Shape.finishTouched
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxStop.finish_shape' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxStop.finish_shape
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxStop.skeleton_shape' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxStop.skeleton_shape
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxStop.hidden_shape' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxStop.hidden_shape
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxStop.client_shape' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxStop.client_shape
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxStop.derive_retains' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxStop.derive_retains
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxStop.derive_trace' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxStop.derive_trace
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxStop.select_trace' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxStop.select_trace
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxStop.public_retains' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxStop.public_retains
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxStop.chosen_trace' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxStop.chosen_trace
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxStop.TraceInvariant.prefix' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxStop.TraceInvariant.prefix
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxStop.TraceInvariant.accept' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxStop.TraceInvariant.accept
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxStop.TraceInvariant.keep' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxStop.TraceInvariant.keep
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxStop.TraceInvariant.finish' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxStop.TraceInvariant.finish
