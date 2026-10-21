-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhDeploymentLaterKemTwoSided
import BeaconcryptCore.Computational.PqxdhDeploymentTargetRange

/-! LQ-F upstream, unit C4: the range of the public designation in the LQ-F later game (LQ-F upstream design-v2 section 4.2, critique F15). CE-9's `PqxdhDeploymentTargetRange.range_game_create` shows that, for a budget-respecting adversary, every designation `(session, k)` of any handle on any outcome of the common deployment experiment has `session < qAccept` and `k < qCreate`. The LQ-F game appends a post phase and the reveal, but the designation is computed from the run-phase ledger's transcript alone. The event "some designation of the transcript is out of range" reads only the ledger, so it ignores the caches, and `PqxdhDeploymentLaterServerGame.game_classical_event` gives it the same distribution at the end of the LQ-F game as at the end of the classical experiment, where it never happens. Hence:

- `range_game_create_later` and `range_game_later`: on every outcome of the LQ-F game of a run-phase budget-respecting adversary, with every post-run adversary, every designation `(session, k)` of any handle has `session < qAccept` and `k < qCreate` (so `k < qCreate + 1`).
- `eligibleL` and `eligible_designated_later`: the unbudgeted designation of a claim on an LQ-F outcome exists exactly when the budgeted designation does, so the budgeted eligibility of the LQ-F headlines loses no outcome.
- `designated_create_later`: the column `k = qCreate` of the target domain `Fin qAccept × Fin (qCreate + 1)` is never designated.
- `split_create_later` and `kem_transfer_server_create_two_sided`: the exact split of plain eligibility over the tight target domain `Fin qAccept × Fin qCreate`, and the two-sided exact-sum KEM transfer of the LQ-F game over that domain (the LQ-F form of `PqxdhDeploymentKemTwoSided.split_create` and `kem_transfer_create_two_sided`, with the per-target terms of `PqxdhDeploymentLaterKemTwoSided.kem_transfer_server_two_sided`), without the `qAccept` advantage and correctness terms of the never-designated column.

Premises: the approved Phase 1 and Phase 2 read-back contracts and the run-phase budget (through `range_game_create`); the transfer also uses `FunctionalDecapsulation` and inherits the per-target IND-CCA advantage and correctness error of `kem_transfer_server_two_sided`. No assumption, contract or advantage term is added. These are confidentiality statements: the event may read the post-run adversary's output, which depends on the reveal; no authentication is claimed. -/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc

set_option autoImplicit false

namespace BeaconcryptCore.Computational.PqxdhDeploymentLaterTargetRange
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhDeploymentInterface (Handle ModeSpec Mode Budget FreshBounds)
open PqxdhDeploymentLater (PostSpec)
open PqxdhDeploymentLaterServerGame (Reveal LaterState)
open PqxdhDeploymentLaterServerTransfer (happens designated decision observeGame)
open PqxdhDeploymentLaterServerCompile (compileServer)
open PqxdhDeploymentKemTransfer (Observed selectedKem)

variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response A X Out : Type}

/-- Range of the designation in the LQ-F game (LQ-F design-v2 F15): on every outcome of the LQ-F game of a run-phase budget-respecting adversary, with every post-run adversary, every designation `(session, k)` of any handle on the run-phase transcript has `session < qAccept` and `k < qCreate`. The event "some designation is out of range" reads only the ledger, so `PqxdhDeploymentLaterServerGame.game_classical_event` moves its probability to the classical experiment, where it is zero by `PqxdhDeploymentTargetRange.range_game_create`. Under the approved Phase 1 and Phase 2 read-back contracts. -/
theorem range_game_create_later (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (ensureInit : StateT A ProbComp Bool)
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec) (bounds : FreshBounds) (mode : Mode)
    (first : OracleComp (ModeSpec mode) X) (second : X → Reveal → OracleComp PostSpec Out) (budget : Budget)
    (respects : budget.Respects first) (runtime : A)
    (outcome : Option (PqxdhRegistrationJointServerBirth.ClientCreated Unit × Out × LaterState KemSK) × A)
    (reached : outcome ∈ support ((PqxdhDeploymentLaterServerGame.game setup codec checks route ensureInit 0 bounds mode
      first second).run runtime))
    (observed : Observed Out) (found : observeGame outcome.1 = some observed)
    (handle : Handle) (session k : Nat)
    (designatedAt : PqxdhDeploymentTranscript.designate setup.source.crypto codec setup.serverKeyId
      observed.2.1.transcript handle = some (session, k)) :
    session < budget.accept ∧ k < budget.create := by
  let outOfRange : Option (PqxdhRegistrationJointServerBirth.ClientCreated Unit × PqxdhDeploymentSecrecy.State KemSK) →
      Bool := fun result => result.any fun value => @decide (∃ handle session k,
        PqxdhDeploymentTranscript.designate setup.source.crypto codec setup.serverKeyId value.2.1.transcript handle =
          some (session, k) ∧ ¬ (session < budget.accept ∧ k < budget.create)) (Classical.propDecidable _)
  have classical : 𝒟[(fun outcome => outOfRange (outcome.1.map fun result => (result.1, result.2.2))) <$>
      (PqxdhDeploymentSecrecy.game setup codec checks route ensureInit 0 bounds mode first).run runtime] {true} = 0 := by
    rw [← prEvent_eq_evalDist_singleton _ true, OracleComp.prEvent_eq_zero_iff]
    intro value member hit
    rw [support_map] at member
    obtain ⟨classicalOutcome, classicalReached, rfl⟩ := member
    rcases resultEq : classicalOutcome.1 with _ | result
    · simp [resultEq, outOfRange] at hit
    · simp only [resultEq, Option.map_some, Option.any_some, outOfRange, decide_eq_true_eq] at hit
      obtain ⟨other, otherSession, otherK, otherDesignated, outside⟩ := hit
      exact outside (PqxdhDeploymentTargetRange.range_game_create setup codec checks route ensureInit phase1 phase2 bounds
        mode first budget respects runtime classicalOutcome classicalReached (result.2.1, result.2.2.1,
          result.2.2.2.produced) (by simp [PqxdhDeploymentKemTransfer.observeGame, resultEq]) other otherSession otherK
        otherDesignated)
  rw [← PqxdhDeploymentLaterServerGame.game_classical_event setup codec checks route ensureInit 0 bounds mode first
    second outOfRange (fun _ _ _ _ _ => rfl) runtime, ← prEvent_eq_evalDist_singleton _ true,
    OracleComp.prEvent_eq_zero_iff] at classical
  by_contra outside
  apply classical _ (by rw [support_map]; exact ⟨outcome, reached, rfl⟩)
  rcases resultEq : outcome.1 with _ | result
  · simp [resultEq, observeGame] at found
  · simp only [resultEq, observeGame, Option.map_some, Option.some.injEq] at found
    subst found
    simp only [resultEq, Option.map_some, Option.any_some, outOfRange, decide_eq_true_eq]
    exact ⟨handle, session, k, designatedAt, outside⟩

/-- Range of the designation in the LQ-F game at the headline's target domain `Fin qAccept × Fin (qCreate + 1)`: `range_game_create_later` with `k < qCreate + 1`. -/
theorem range_game_later (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (ensureInit : StateT A ProbComp Bool)
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec) (bounds : FreshBounds) (mode : Mode)
    (first : OracleComp (ModeSpec mode) X) (second : X → Reveal → OracleComp PostSpec Out) (budget : Budget)
    (respects : budget.Respects first) (runtime : A)
    (outcome : Option (PqxdhRegistrationJointServerBirth.ClientCreated Unit × Out × LaterState KemSK) × A)
    (reached : outcome ∈ support ((PqxdhDeploymentLaterServerGame.game setup codec checks route ensureInit 0 bounds mode
      first second).run runtime))
    (observed : Observed Out) (found : observeGame outcome.1 = some observed)
    (handle : Handle) (session k : Nat)
    (designatedAt : PqxdhDeploymentTranscript.designate setup.source.crypto codec setup.serverKeyId
      observed.2.1.transcript handle = some (session, k)) :
    session < budget.accept ∧ k < budget.capacity := by
  obtain ⟨sessionBound, kBound⟩ := range_game_create_later setup codec checks route ensureInit phase1 phase2 bounds mode
    first second budget respects runtime outcome reached observed found handle session k designatedAt
  exact ⟨sessionBound, Nat.lt_succ_of_lt kBound⟩

/-- The unbudgeted designation of a claim on an outcome of the LQ-F game: `designate` on the run-phase transcript, applied to the handle the claim names (the LQ-F form of `PqxdhDeploymentTargetRange.eligible`). -/
noncomputable def eligibleL (crypto : Pqxdh.Crypto) (codec : Codec Reader Response) (serverKid : Std.U64)
    (claim : Observed Out → Option Handle)
    (outcome : Option (PqxdhRegistrationJointServerBirth.ClientCreated Unit × Out × LaterState KemSK) × A) :
    Option (Nat × Nat) :=
  (observeGame outcome.1).bind fun observed =>
    (claim observed).bind (PqxdhDeploymentTranscript.designate crypto codec serverKid observed.2.1.transcript)

/-- On every outcome of the LQ-F game of a run-phase budget-respecting adversary, a claim is designated exactly when it is designated inside the budgeted target domain, so the budgeted eligibility of the LQ-F headlines loses no outcome (the LQ-F form of `PqxdhDeploymentTargetRange.eligible_designated`). -/
theorem eligible_designated_later (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (ensureInit : StateT A ProbComp Bool)
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec) (bounds : FreshBounds) (mode : Mode)
    (first : OracleComp (ModeSpec mode) X) (second : X → Reveal → OracleComp PostSpec Out) (budget : Budget)
    (respects : budget.Respects first) (runtime : A) (claim : Observed Out → Option Handle)
    (outcome : Option (PqxdhRegistrationJointServerBirth.ClientCreated Unit × Out × LaterState KemSK) × A)
    (reached : outcome ∈ support ((PqxdhDeploymentLaterServerGame.game setup codec checks route ensureInit 0 bounds mode
      first second).run runtime)) :
    (eligibleL setup.source.crypto codec setup.serverKeyId claim outcome).isSome =
      (designated setup.source.crypto codec setup.serverKeyId budget claim outcome).isSome := by
  unfold eligibleL designated PqxdhDeploymentKemTransfer.target
  cases found : observeGame outcome.1 with
  | none => rfl
  | some observed =>
      simp only [Option.bind_some]
      cases named : claim observed with
      | none => rfl
      | some handle =>
          simp only [Option.bind_some]
          cases chosen : PqxdhDeploymentTranscript.designate setup.source.crypto codec setup.serverKeyId
              observed.2.1.transcript handle with
          | none => simp [PqxdhDeploymentTranscript.designateIn, chosen]
          | some pair =>
              obtain ⟨sessionBound, kBound⟩ := range_game_later setup codec checks route ensureInit phase1 phase2 bounds
                mode first second budget respects runtime outcome reached observed found handle pair.1 pair.2 chosen
              rw [PqxdhDeploymentTargetRange.designateIn_range _ codec _ budget _ handle pair.1 pair.2 chosen sessionBound
                kBound]
              rfl

/-- On every outcome of the LQ-F game of a run-phase budget-respecting adversary, the KEM creation index of a designated target is below the create budget: the column `k = qCreate` of the target domain `Fin qAccept × Fin (qCreate + 1)` is never designated (the LQ-F form of `PqxdhDeploymentTargetRange.designated_create`). -/
theorem designated_create_later (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (ensureInit : StateT A ProbComp Bool)
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec) (bounds : FreshBounds) (mode : Mode)
    (first : OracleComp (ModeSpec mode) X) (second : X → Reveal → OracleComp PostSpec Out) (budget : Budget)
    (respects : budget.Respects first) (runtime : A) (claim : Observed Out → Option Handle)
    (outcome : Option (PqxdhRegistrationJointServerBirth.ClientCreated Unit × Out × LaterState KemSK) × A)
    (reached : outcome ∈ support ((PqxdhDeploymentLaterServerGame.game setup codec checks route ensureInit 0 bounds mode
      first second).run runtime))
    (g : Fin budget.accept × Fin budget.capacity)
    (chosen : designated setup.source.crypto codec setup.serverKeyId budget claim outcome = some g) :
    g.2.val < budget.create := by
  unfold designated PqxdhDeploymentKemTransfer.target at chosen
  obtain ⟨observed, found, named⟩ := Option.bind_eq_some_iff.mp chosen
  obtain ⟨handle, _, inside⟩ := Option.bind_eq_some_iff.mp named
  exact (range_game_create_later setup codec checks route ensureInit phase1 phase2 bounds mode first second budget
    respects runtime outcome reached observed found handle g.1.val g.2.val
    (PqxdhDeploymentKemTransfer.designateIn_some _ codec _ budget _ handle g inside)).2

/-- The exact split over the tight target domain for the LQ-F game (the LQ-F form of `PqxdhDeploymentKemTwoSided.split_create`): for a run-phase budget-respecting adversary and every post-run adversary, the probability that the LQ-F game ends with the event and the claim designated at all (plain eligibility) is the sum over `g` in `Fin qAccept × Fin qCreate`, with `k` read in `Fin (qCreate + 1)`, of the probability that it ends with the event and the claim designating `g`. The column `k = qCreate` is never designated (`designated_create_later`). -/
theorem split_create_later (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (ensureInit : StateT A ProbComp Bool)
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec) (bounds : FreshBounds) (mode : Mode)
    (first : OracleComp (ModeSpec mode) X) (second : X → Reveal → OracleComp PostSpec Out) (budget : Budget)
    (respects : budget.Respects first) (event : Observed Out → Bool) (claim : Observed Out → Option Handle)
    (runtime : A) :
    𝒟[(fun outcome => decide (happens event outcome = true ∧
        (eligibleL setup.source.crypto codec setup.serverKeyId claim outcome).isSome)) <$>
      (PqxdhDeploymentLaterServerGame.game setup codec checks route ensureInit 0 bounds mode first second).run runtime]
        {true} =
      ∑ g : Fin budget.accept × Fin budget.create,
        𝒟[(fun outcome => decide (happens event outcome = true ∧
          designated setup.source.crypto codec setup.serverKeyId budget claim outcome =
            some ((g.1, g.2.castSucc) : Fin budget.accept × Fin budget.capacity))) <$>
        (PqxdhDeploymentLaterServerGame.game setup codec checks route ensureInit 0 bounds mode first second).run
          runtime] {true} := by
  rw [PqxdhDeploymentKemTransfer.map_support_congr _ _
    (fun outcome => decide (happens event outcome = true ∧
      (designated setup.source.crypto codec setup.serverKeyId budget claim outcome).isSome))
    (fun outcome reached => by
      rw [eligible_designated_later setup codec checks route ensureInit phase1 phase2 bounds mode first second budget
        respects runtime claim outcome reached]),
    UniformTargetSelection.split, Fintype.sum_prod_type, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun session _ => PqxdhDeploymentKemTwoSided.sum_last_eq budget.create _ ?_
  rw [UniformTargetSelection.chance_eq, OracleComp.prEvent_eq_zero_iff]
  rintro outcome reached ⟨_, chosen⟩
  exact lt_irrefl _ (designated_create_later setup codec checks route ensureInit phase1 phase2 bounds mode first second
    budget respects runtime claim outcome reached _ chosen)

/-- Two-sided exact-sum KEM transfer of the LQ-F game over the tight target domain, with plain eligibility (the LQ-F form of `PqxdhDeploymentKemTwoSided.kem_transfer_create_two_sided`): the probability that the LQ-F game ends with the event and the claim designated at all, and the sum over `g` in `Fin qAccept × Fin qCreate`, with `k` read in `Fin (qCreate + 1)` through `Fin.castSucc`, of the probability that the logged opaque KEM-ideal branch of `g`'s decision returns `true`, differ by at most the sum over the same targets of one IND-CCA advantage of the proof-carrying adversary at the logged exposure plus one correctness error (the terms of `PqxdhDeploymentLaterKemTwoSided.kem_transfer_server_two_sided`). A confidentiality statement: the event may read the post-run adversary's output. -/
theorem kem_transfer_server_create_two_sided (setup : Setup baseSpec KemSK)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem)
    (codec : Codec Reader Response) (checks : Checks) (route : RawCtxServerRouting.SenderDecoder)
    (ensureInit : StateT A ProbComp Bool) (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec) (bounds : FreshBounds) (mode : Mode)
    (first : OracleComp (ModeSpec mode) X) (second : X → Reveal → OracleComp PostSpec Out) (budget : Budget)
    (respects : budget.Respects first) (event : Observed Out → Bool) (claim : Observed Out → Option Handle)
    (runtime : A) :
    |(𝒟[(fun outcome => decide (happens event outcome = true ∧
        (eligibleL setup.source.crypto codec setup.serverKeyId claim outcome).isSome)) <$>
      (PqxdhDeploymentLaterServerGame.game setup codec checks route ensureInit 0 bounds mode first second).run
        runtime] {true}).toReal -
      ∑ g : Fin budget.accept × Fin budget.create,
        (𝒟[PqxdhDeploymentLaterServerOpaque.opaqueBranch (Reader := Reader) setup codec checks ensureInit none
          (decision setup.source.crypto codec setup.serverKeyId budget event claim (g.1, g.2.castSucc))
          (compileServer setup codec route bounds mode first second) runtime budget.create
          (selectedKem budget (g.1, g.2.castSucc)) g.1.val false] {true}).toReal| ≤
      ∑ g : Fin budget.accept × Fin budget.create,
        (setup.kem.IND_CCA_Advantage (PqxdhInitializerSecrecy.runtimeOfImpl
            (PqxdhInitializerSecrecy.kemAmbientImpl setup.baseImpl))
          (PqxdhDeploymentLaterServerKemHop.certified setup ensureInit none
            (PqxdhDeploymentLaterServerCut.scanned setup codec checks
              (decision setup.source.crypto codec setup.serverKeyId budget event claim (g.1, g.2.castSucc))
              (compileServer setup codec route bounds mode first second) g.1.val)
            runtime budget.create (selectedKem budget (g.1, g.2.castSucc))).toINDCCA +
          PqxdhRegistrationJointKemRawGame.correctnessError setup) := by
  rw [split_create_later setup codec checks route ensureInit phase1 phase2 bounds mode first second budget respects
    event claim runtime]
  exact PqxdhDeploymentKemTwoSided.abs_sum_sub_le _ _ _ (fun _ => UniformTargetSelection.chance_ne_top _ _) fun g =>
    PqxdhDeploymentLaterKemTwoSided.kem_transfer_server_two_sided setup functional codec checks route ensureInit phase1
      phase2 bounds mode first second budget respects event claim (g.1, g.2.castSucc) runtime

end BeaconcryptCore.Computational.PqxdhDeploymentLaterTargetRange

-- Axiom guards (generated)

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterTargetRange.range_game_create_later' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterTargetRange.range_game_create_later

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterTargetRange.range_game_later' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterTargetRange.range_game_later

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterTargetRange.eligible_designated_later' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterTargetRange.eligible_designated_later

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterTargetRange.designated_create_later' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterTargetRange.designated_create_later

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterTargetRange.split_create_later' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterTargetRange.split_create_later

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterTargetRange.kem_transfer_server_create_two_sided' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterTargetRange.kem_transfer_server_create_two_sided
