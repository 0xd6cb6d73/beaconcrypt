-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhDeploymentIdealBeacon

/-!
# The transcript guess of the Beacon-side anomaly (CE-11b, unit U4)

The first half of `anomaly_le` (design-v2 section 7.2, item 6): the Beacon-side anomaly `PqxdhDeploymentIdealTrace.Anomaly` (owner `k` designates the target through a finish made before the selected raw accept) is contained in a public event whose probability the second half (`PqxdhDeploymentIdealAnomalyBound`) bounds by the KEM ciphertext guess.

- A generic coupling of two stateful simulations of one program that are identical until a stop and keep a frozen observable once stopped (`UntilStop`, `relTriple_until_stop`, the variant of `PqxdhServerAuthEntryFactor.relTriple_until_bad` that carries the observable), with the equality in law (`LazyOracleDiscard.LawEq`) of every view that agrees on such coupled final states (`lawEq_until_stop`).
- The transcript guess: `cutAt` (the prefix of a transcript before its raw accept attempt of a given ordinal; `cutAt_prefix`, `acceptCount_cons`, `cutAt_append`, `cutAt_keeps`), `earlyFinish` (the input of owner `k`'s first successful finish made before the selected raw accept; `earlyFinish_eq`: under `FinishBefore` it is the input of owner `k`'s first successful finish), and `guessCt` (the bytes of the Phase 2 ciphertext of that input), which later entries do not change once the selected raw accept happened (`guessCt_append`).
- `anomaly_guess`: on every outcome of the record world with the ideal environment of a target, under `Phase1ReadBack` and `Phase2ReadBack`, the anomaly implies that the transcript guess is the challenge ciphertext of the drawn parameters (from the Beacon provenance invariant of `PqxdhDeploymentIdealBeacon`).

These are definitions, a generic coupling and support facts; no security claim is made here.
-/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open PqxdhRefinement
open OracleComp.ProgramLogic.Relational

set_option autoImplicit false

namespace BeaconcryptCore.Computational.PqxdhDeploymentIdealGuess

/-! ### Identical until a stop with a frozen observable -/

section UntilStop
variable {ι : Type} {spec : OracleSpec ι}

/-- The coupling postcondition of identical-until-stop with a frozen observable: equal answers with related states, or both runs stopped with the same observable. -/
def UntilStop {α σ₁ σ₂ V : Type} (related : σ₁ → σ₂ → Prop) (stop₁ : σ₁ → Option V) (stop₂ : σ₂ → Option V)
    (left : α × σ₁) (right : α × σ₂) : Prop :=
  (left.1 = right.1 ∧ related left.2 right.2) ∨ ∃ value, stop₁ left.2 = some value ∧ stop₂ right.2 = some value

/-- Identical until a stop, as a coupling of two stateful simulations of the same program: if from related states every query is coupled so that the answers agree and the states stay related, or both runs stop with the same observable, and every step keeps a stopped state's observable, then the whole simulations are coupled in the same way (`PqxdhServerAuthEntryFactor.relTriple_until_bad` with the observable carried along). -/
theorem relTriple_until_stop {α σ₁ σ₂ V : Type}
    (impl₁ : QueryImpl spec (StateT σ₁ ProbComp)) (impl₂ : QueryImpl spec (StateT σ₂ ProbComp))
    (related : σ₁ → σ₂ → Prop) (stop₁ : σ₁ → Option V) (stop₂ : σ₂ → Option V)
    (keeps₁ : ∀ query state value, stop₁ state = some value →
      ∀ result ∈ support ((impl₁ query).run state), stop₁ result.2 = some value)
    (keeps₂ : ∀ query state value, stop₂ state = some value →
      ∀ result ∈ support ((impl₂ query).run state), stop₂ result.2 = some value)
    (step : ∀ query state₁ state₂, related state₁ state₂ →
      RelTriple ((impl₁ query).run state₁) ((impl₂ query).run state₂) (UntilStop related stop₁ stop₂))
    (work : OracleComp spec α) (state₁ : σ₁) (state₂ : σ₂) (start : related state₁ state₂) :
    RelTriple ((simulateQ impl₁ work).run state₁) ((simulateQ impl₂ work).run state₂)
      (UntilStop related stop₁ stop₂) := by
  have bothStopped : ∀ (left right : OracleComp spec α) (first : σ₁) (second : σ₂) (value : V),
      stop₁ first = some value → stop₂ second = some value →
      RelTriple ((simulateQ impl₁ left).run first) ((simulateQ impl₂ right).run second)
        (UntilStop related stop₁ stop₂) := fun left right first second value firstStop secondStop =>
    relTriple_post_mono (PqxdhServerAuthEntryFactor.relTriple_support _ _ _ _
      (PqxdhServerAuthEntryFactor.support_run_bad impl₁ (fun state => stop₁ state = some value)
        (fun query state held => keeps₁ query state value held) left first firstStop)
      (PqxdhServerAuthEntryFactor.support_run_bad impl₂ (fun state => stop₂ state = some value)
        (fun query state held => keeps₂ query state value held) right second secondStop))
      fun _ _ both => Or.inr ⟨value, both⟩
  induction work using OracleComp.inductionOn generalizing state₁ state₂ with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure]
      exact relTriple_pure_pure (Or.inl ⟨rfl, start⟩)
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, id_map,
        StateT.run_bind]
      refine relTriple_bind (step query state₁ state₂ start) fun left right post => ?_
      rcases post with ⟨same, rel⟩ | ⟨value, leftStop, rightStop⟩
      · rw [same]
        exact ih right.1 left.2 right.2 rel
      · exact bothStopped _ _ left.2 right.2 value leftStop rightStop

set_option linter.deprecated false in
/-- Identical until a stop with a frozen observable gives the two simulations the same law (`LazyOracleDiscard.LawEq`) of every view that agrees on related final states and on final states stopped with the same observable. -/
theorem lawEq_until_stop {α σ₁ σ₂ V β : Type}
    (impl₁ : QueryImpl spec (StateT σ₁ ProbComp)) (impl₂ : QueryImpl spec (StateT σ₂ ProbComp))
    (related : σ₁ → σ₂ → Prop) (stop₁ : σ₁ → Option V) (stop₂ : σ₂ → Option V)
    (keeps₁ : ∀ query state value, stop₁ state = some value →
      ∀ result ∈ support ((impl₁ query).run state), stop₁ result.2 = some value)
    (keeps₂ : ∀ query state value, stop₂ state = some value →
      ∀ result ∈ support ((impl₂ query).run state), stop₂ result.2 = some value)
    (step : ∀ query state₁ state₂, related state₁ state₂ →
      RelTriple ((impl₁ query).run state₁) ((impl₂ query).run state₂) (UntilStop related stop₁ stop₂))
    (work : OracleComp spec α) (state₁ : σ₁) (state₂ : σ₂) (start : related state₁ state₂)
    (view₁ : α × σ₁ → β) (view₂ : α × σ₂ → β)
    (agree : ∀ left right, UntilStop related stop₁ stop₂ left right → view₁ left = view₂ right) :
    LazyOracleDiscard.LawEq (view₁ <$> (simulateQ impl₁ work).run state₁)
      (view₂ <$> (simulateQ impl₂ work).run state₂) := by
  have coupled := relTriple_until_stop impl₁ impl₂ related stop₁ stop₂ keeps₁ keeps₂ step work state₁ state₂ start
  have mapped : RelTriple (view₁ <$> (simulateQ impl₁ work).run state₁) (view₂ <$> (simulateQ impl₂ work).run state₂)
      (EqRel β) := by
    rw [map_eq_bind_pure_comp, map_eq_bind_pure_comp]
    exact relTriple_bind coupled fun left right post => relTriple_pure_pure (agree left right post)
  intro γ _ continuation
  apply evalDist_eq_of_evalSPMF_eq
  rw [evalSPMF_bind, evalSPMF_bind, evalSPMF_eq_of_relTriple_eqRel mapped]

end UntilStop


/-! ### The transcript guess of the Beacon-side anomaly -/

section Transcript
open PqxdhDeploymentInterface (Entry)
open PqxdhDeploymentTranscript (acceptCount finishOf)
open PqxdhDeploymentIdealParams (Target)
variable {count : ℕ}

/-- The prefix of a transcript before its raw accept attempt of ordinal `n` (counted from zero): every entry up to that attempt, which is excluded, or the whole transcript when there are at most `n` attempts. -/
def cutAt : ℕ → List Entry → List Entry
  | _, [] => []
  | n, entry :: rest => match entry.query with
    | .inl (.inr (.accept _)) => match n with
      | 0 => []
      | n + 1 => entry :: cutAt n rest
    | _ => entry :: cutAt n rest

/-- The cut is a prefix. -/
theorem cutAt_prefix (n : ℕ) (transcript : List Entry) : ∃ rest, transcript = cutAt n transcript ++ rest := by
  induction transcript generalizing n with
  | nil => exact ⟨[], rfl⟩
  | cons entry tail ih =>
      rcases entry with ⟨(coin | command) | secrecy, reply⟩
      · obtain ⟨rest, same⟩ := ih n
        exact ⟨rest, by simp only [cutAt, List.cons_append]; rw [← same]⟩
      · cases command with
        | accept raw =>
            cases n with
            | zero => exact ⟨_, rfl⟩
            | succ n =>
                obtain ⟨rest, same⟩ := ih n
                exact ⟨rest, by simp only [cutAt, List.cons_append]; rw [← same]⟩
        | _ =>
            obtain ⟨rest, same⟩ := ih n
            exact ⟨rest, by simp only [cutAt, List.cons_append]; rw [← same]⟩
      · obtain ⟨rest, same⟩ := ih n
        exact ⟨rest, by simp only [cutAt, List.cons_append]; rw [← same]⟩

/-- The accept attempts of a transcript with one more entry in front. -/
theorem acceptCount_cons (entry : Entry) (rest : List Entry) :
    acceptCount (entry :: rest) = acceptCount rest + (match entry.query with
      | .inl (.inr (.accept _)) => 1
      | _ => 0) := by
  unfold acceptCount
  rw [List.countP_cons]
  rcases entry with ⟨(coin | command) | secrecy, reply⟩
  · rfl
  · cases command <;> rfl
  · rfl

/-- Once a transcript has more than `n` raw accept attempts, later entries do not change its cut at ordinal `n`. -/
theorem cutAt_append (n : ℕ) (transcript more : List Entry) (later : n < acceptCount transcript) :
    cutAt n (transcript ++ more) = cutAt n transcript := by
  induction transcript generalizing n with
  | nil => exact absurd later (Nat.not_lt_zero n)
  | cons entry tail ih =>
      rw [acceptCount_cons] at later
      rcases entry with ⟨(coin | command) | secrecy, reply⟩
      · simp only [List.cons_append, cutAt]
        rw [ih n later]
      · cases command with
        | accept raw =>
            cases n with
            | zero => rfl
            | succ n =>
                simp only [List.cons_append, cutAt]
                rw [ih n (by simp only at later; omega)]
        | _ =>
            simp only [List.cons_append, cutAt]
            rw [ih n later]
      · simp only [List.cons_append, cutAt]
        rw [ih n later]

/-- An entry that is not a raw accept and follows at most `n` raw accept attempts is kept by the cut at ordinal `n`. -/
theorem cutAt_keeps (n : ℕ) (before after : List Entry) (entry : Entry) (count : acceptCount before ≤ n)
    (notAccept : ∀ raw reply, entry ≠ ⟨.inl (.inr (.accept raw)), reply⟩) :
    ∃ after', cutAt n (before ++ entry :: after) = before ++ entry :: after' := by
  induction before generalizing n with
  | nil =>
      rcases entry with ⟨(coin | command) | secrecy, reply⟩
      · exact ⟨_, rfl⟩
      · cases command with
        | accept raw => exact absurd rfl (notAccept raw reply)
        | _ => exact ⟨_, rfl⟩
      · exact ⟨_, rfl⟩
  | cons first tail ih =>
      rw [acceptCount_cons] at count
      rcases first with ⟨(coin | command) | secrecy, reply⟩
      · obtain ⟨after', same⟩ := ih n count
        exact ⟨after', by simp only [List.cons_append, cutAt]; rw [same]⟩
      · cases command with
        | accept raw =>
            cases n with
            | zero => simp only at count; omega
            | succ n =>
                obtain ⟨after', same⟩ := ih n (by simp only at count; omega)
                exact ⟨after', by simp only [List.cons_append, cutAt]; rw [same]⟩
        | _ =>
            obtain ⟨after', same⟩ := ih n count
            exact ⟨after', by simp only [List.cons_append, cutAt]; rw [same]⟩
      · obtain ⟨after', same⟩ := ih n count
        exact ⟨after', by simp only [List.cons_append, cutAt]; rw [same]⟩

/-- The input of owner `k`'s first successful finish made before the selected raw accept: `finishOf` on the cut at the selected ordinal. -/
def earlyFinish (t : Target count) (transcript : List Entry) : Option Pqxdh.Bytes :=
  finishOf (cutAt t.accept transcript) t.kem.val

/-- When owner `k` finished successfully before the selected raw accept, its first successful finish was made before it. -/
theorem earlyFinish_eq (t : Target count) (transcript : List Entry)
    (early : PqxdhDeploymentIdealTrace.FinishBefore t transcript) :
    earlyFinish t transcript = finishOf transcript t.kem.val := by
  obtain ⟨before, raw, reply, after, rfl, count⟩ := early
  let finished : Entry := ⟨.inl (.inr (.finish t.kem.val raw)), some reply⟩
  obtain ⟨after', cut⟩ := cutAt_keeps t.accept before after finished count (fun raw' reply' same => by
    simp only [finished, PqxdhDeploymentInterface.Entry.mk.injEq, Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq,
      false_and] at same)
  obtain ⟨rest, whole⟩ := cutAt_prefix t.accept (before ++ finished :: after)
  have found : (finishOf (cutAt t.accept (before ++ finished :: after)) t.kem.val).isSome := by
    rw [cut]
    unfold finishOf
    rw [List.findSome?_isSome_iff]
    exact ⟨finished, List.mem_append_right before (List.mem_cons_self ..), by simp [finished]⟩
  unfold earlyFinish
  conv_rhs => rw [whole]
  unfold finishOf at found ⊢
  rw [List.findSome?_append]
  obtain ⟨value, same⟩ := Option.isSome_iff_exists.mp found
  rw [same, Option.some_or]

end Transcript


section Guess
open PqxdhDeploymentInterface (Entry)
open PqxdhDeploymentTranscript (acceptCount)
open PqxdhDeploymentIdealParams (Target)
variable {Reader Response : Type} (codec : PqxdhServerAuthExperiment.Codec Reader Response) {count : ℕ}

/-- The transcript guess of the challenge ciphertext: the bytes of the ciphertext that the Phase 2 reader gives on the input of owner `k`'s first successful finish made before the selected raw accept. A function of the transcript. -/
def guessCt (t : Target count) (transcript : List Entry) : Option PqxdhKemIndCca.MlKem768Ciphertext :=
  (earlyFinish t transcript).bind fun raw =>
    ((codec.read2 raw).bind codec.ciphertext).map PqxdhPhase2InputBytes.ciphertext

/-- After the selected raw accept, later entries do not change the transcript guess. -/
theorem guessCt_append (t : Target count) (transcript more : List Entry) (later : t.accept < acceptCount transcript) :
    guessCt codec t (transcript ++ more) = guessCt codec t transcript := by
  unfold guessCt earlyFinish
  rw [cutAt_append t.accept transcript more later]

end Guess

/-! ### The anomaly hits the guess on every outcome of the record world -/

section World
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response A X : Type}
  (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK) (codec : PqxdhServerAuthExperiment.Codec Reader Response)
  (route : RawCtxServerRouting.SenderDecoder) (checks : PqxdhServerAuthExperiment.Checks) {count : ℕ}
open PqxdhDeploymentIdealParams (Target)
open PqxdhDeploymentIdealTrace (Anomaly)

/-- On every outcome of the record world with the ideal environment of a target, under `Phase1ReadBack` and `Phase2ReadBack`, the Beacon-side anomaly implies that the transcript guess is the challenge ciphertext of the drawn parameters: owner `k`'s designating finish is its first successful finish, made before the selected raw accept (`earlyFinish_eq`), and its Phase 2 ciphertext is the one that the marked session's build response carries, which is written with the challenge ciphertext (`PqxdhDeploymentIdealBeacon.world_beacon`, `PqxdhDeploymentIdealBeacon.written_read`). -/
theorem anomaly_guess (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec) (t : Target count)
    (ensureInit : StateT A ProbComp Bool) (identityIndex : ℕ) (runtime : A) (serverKid : Std.U64)
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (adversary : OracleComp (PqxdhDeploymentInterface.ModeSpec mode) X) :
    ∀ result ∈ support (PqxdhRecordLiftWorld.run setup codec route
        (PqxdhDeploymentIdealEnv.envGD setup codec checks t ensureInit identityIndex runtime) setup.serverKeyId bounds
          mode adversary),
      ∀ value, result.1 = some value → Anomaly setup.source.crypto codec serverKid t value.2.1.2.transcript →
        guessCt codec t value.2.1.2.transcript = some value.2.2.backend.1.challenge := by
  intro result member value found anomaly
  obtain ⟨linked, early⟩ := anomaly
  obtain ⟨annotated, annotatedMember, sameValue, _⟩ := PqxdhDeploymentIdealProvenance.annotated_cover setup codec route
    _ setup.serverKeyId bounds mode adversary result member
  obtain ⟨_, _, _, prov, holds⟩ := PqxdhDeploymentIdealBeacon.world_beacon setup codec route checks t ensureInit
    identityIndex runtime setup.serverKeyId bounds mode adversary annotated annotatedMember value
    (by rw [sameValue]; exact found)
  have facts := PqxdhDeploymentIdealTrace.world_keyFacts setup codec route checks t ensureInit identityIndex runtime
    bounds mode adversary result member value found
  have marked := PqxdhDeploymentIdealTrace.keyFacts_marked setup codec checks phase1 serverKid t _ _ _ facts
    (.owner t.kem.val) linked
  obtain ⟨⟨s, c⟩, marks⟩ := Option.isSome_iff_exists.mp marked
  have selected := (prov.marked s c marks).1
  subst selected
  obtain ⟨-, -, pin, raw, ciphertext, published, pqKey, -, rawFound, ciphertextFound, -, -, -, link⟩ :=
    PqxdhDeploymentTranscript.designate_owner setup.source.crypto codec serverKid _ t.kem.val _ _ linked
  obtain ⟨response, -, -, builtFound, responseCiphertext, -⟩ := link
  obtain ⟨payload, built⟩ := PqxdhDeploymentKeyMatch.buildOf_mem _ _ response builtFound
  have written := holds.built _ c response marks ⟨payload, built⟩
  have same := PqxdhDeploymentIdealBeacon.written_read codec phase2 _ response written ciphertext responseCiphertext
  unfold guessCt
  rw [earlyFinish_eq t _ early, rawFound, Option.bind_some, ciphertextFound, Option.map_some, same]

end World

end BeaconcryptCore.Computational.PqxdhDeploymentIdealGuess

-- Axiom guards (generated)

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealGuess.relTriple_until_stop' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealGuess.relTriple_until_stop

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealGuess.lawEq_until_stop' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealGuess.lawEq_until_stop

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealGuess.cutAt_prefix' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealGuess.cutAt_prefix

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealGuess.acceptCount_cons' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealGuess.acceptCount_cons

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealGuess.cutAt_append' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealGuess.cutAt_append

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealGuess.cutAt_keeps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealGuess.cutAt_keeps

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealGuess.earlyFinish_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealGuess.earlyFinish_eq

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealGuess.guessCt_append' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealGuess.guessCt_append

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealGuess.anomaly_guess' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealGuess.anomaly_guess
