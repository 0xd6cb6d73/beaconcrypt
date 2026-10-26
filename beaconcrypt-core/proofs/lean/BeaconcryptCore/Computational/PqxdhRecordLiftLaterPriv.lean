-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRecordLiftCtxPrivBills
import BeaconcryptCore.Computational.PqxdhRecordLiftLaterCtx

/-!
# Record-lift later `ctx_lift`, privacy half (items 4 and 5, stage S6, R6, item 4)

**Statement.** `later_ctx_priv_lift` proves `PqxdhRecordLiftLaterTargets.LaterCtxPrivLiftStatement` as defined, for the explicit reduction family `laterPrivReduction` and the explicit bills `laterPrivBills`: for every environment with `Frame`, every run-phase adversary within its budget, every reveal function, every post adversary within its post budget and every cache-free decision on the later view (or every Boolean event of it), in either observation mode, `laterIdealAuth` and `laterRandomRecords` (in mode P, `laterIdealRecords`) differ by at most the exact sum over the `hops n budget` target key indices of the per-key IND$ losses `privacyLoss`, each with coefficient one.

**Method: the privacy hybrid of an arbitrary World client.** The privacy track's hops (`PqxdhRecordLiftCtxPriv`) are stated for the frozen run-phase program; its three-mode link (`PqxdhRecordLiftCtxPrivLink.linked_schedule`) and the per-hop identity `PqxdhRecordLiftCtxPrivModes.hop_advantage` are schedule-level. This module restates the program-level wrappers for an arbitrary World client within the record budget: the three-mode link (`linkClientOf`, `link_of`), the privacy hybrids (`stepClientOf`, `gameOf` over `PqxdhRecordLiftCtxPriv.privModes`), the hybrid before and after a step as the challenger's replay and random games (`game_replay_of`, `game_random_of`, through `PqxdhRecordLiftLaterCtx.key_cut_of`, which holds in every mode), each hop exactly its `privacyLoss` (`hop_loss_of`), the last hybrid (`game_last_of`, through `PqxdhRecordLiftLaterCtx.ctxRunWithOf_congr`) and the telescope (`ctx_priv_loss_of`). The later target is `ctx_priv_loss_of` at the two-phase program.

**Bills.** Per category, a privacy link client of a compiled client is bounded by the client's CTX-ledger bill under the step reduction's per-service cost plus the decision's coins (`link_route_of`); every privacy adversary makes at most `bill .uniform + cost + 66 * bill .hash` uniform requests (two coins per random body and tag, 64 per private commitment fill), `bill .hash` shared hashes, one selected seal and `bill .raw` selected raw requests (`priv_step_bills_of`). `laterPrivBills` instantiates these with `PqxdhRecordLiftLaterCtx.laterCtxProgramBill`; its hash bill is the run-phase shared-hash total plus the `PostBudget` hash term (`laterPriv_hash_bill`).

**Contracts.** No theorem of this module has an assumption or contract hypothesis. `hop_loss_of`, `ctx_priv_loss_of`, `priv_step_bills_of`, `later_ctx_priv_lift_bool` and `later_ctx_priv_lift` use `aeadSeal_tag_length` of `Pqxdh.Crypto` (functional AEAD correctness, through the privacy track's replay-side and bill lemmas), the IND$ game as the advantage term of `privacyLoss` and the BLAKE2b random-oracle model as the world model; no `aead_open_seal`, no INT-CTXT; no other theorem uses a contract (per-theorem closure probe). New Claude work; the proofs of the client-level wrappers follow the privacy track's program-level proofs.
-/

open OracleComp OracleSpec ENNReal CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false

namespace BeaconcryptCore.Computational.PqxdhRecordLiftLaterPriv
open PqxdhRecordLiftInterface PqxdhRecordLiftIdeal PqxdhRecordLiftCtxHybrid PqxdhRecordLiftCtxLink
open PqxdhRecordLiftCtxPrivLink PqxdhRecordLiftCtxPriv PqxdhRecordLiftLaterWorlds PqxdhRecordLiftLaterCtx
open PqxdhRecordLiftCtxPrivModes (uniformBytes bytesSample)
open PqxdhDeploymentInterface (Mode ModeSpec FreshBounds Budget)
open PqxdhServerAuthExperiment (Setup Codec)
open PqxdhRecordLiftWorldCompiler (Label)
open PqxdhRecordLiftProtocol (schedule initialControl)
open PqxdhRecordLiftCtxProgramBounds (Weighted)
open PqxdhRecordLiftCtxProtocolBounds (BudgetKind categoryCost)
open CtxRomAuth AdaptiveCtxReceive
open AdaptiveCtxQueryBounds (SourceUniform SourceHash SourceSeal)
variable {n : Nat} {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response E X : Type}

/-! ### The link of one privacy step for an arbitrary World client -/

section Hops
variable (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)

/-- The key-free three-mode reduction client of one privacy step for an arbitrary World client: the whole compiled client under `PqxdhRecordLiftCtxPrivLink.reduction`, then the decision on the view with its coins forwarded through the reserved slot. -/
noncomputable def linkClientOf (target : Label n) (modes : Label n → KeyMode)
    (client : OracleComp (WorldSpec n) (Outcome E X)) (decision : View n E X → ProbComp Bool) :
    OracleComp PqxdhRecordLiftCtxPrivModes.Spec Bool := do
  let result ← (simulateQ (PqxdhRecordLiftCtxPrivLink.reduction target modes setup codec)
    (schedule codec.frameRead route client initialControl)).run
      (PqxdhRecordLiftCtxProtocol.erasePrivate PqxdhRecordLiftProtocol.initialPrivate)
  simulateQ (PqxdhRecordLiftCtxPrivLink.coinForward (RawCtxUniversalDecoder.decoder codec.frameRead))
    (decision (viewOf result.1 result.2.produced))

/-- **Link of one privacy step for an arbitrary World client.** The challenger's game in mode `sel`, with the world's sampler, against the key-free reduction client is the CTX world in which the selected coordinate's key is a fresh uniform key held by the challenger, in mode `sel`. -/
theorem link_of (target : Label n) (modes : Label n → KeyMode) (sel : KeyMode)
    (client : OracleComp (WorldSpec n) (Outcome E X)) (decision : View n E X → ProbComp Bool) :
    Prod.fst <$> PqxdhRecordLiftCtxPrivModes.sourceGame uniformBytes sel (RawCtxUniversalDecoder.decoder codec.frameRead)
        setup.source.crypto (linkClientOf setup codec route target modes client decision) =
      (do
        let key ← $ᵗ CtxKey
        let result ← ctxRunWithOf (selectedKey target key) (selectedModesM target sel modes) id setup codec route client
        decision (ctxView result)) := by
  simp only [PqxdhRecordLiftCtxPrivModes.sourceGame, map_bind]
  apply bind_congr
  intro key
  simp only [linkClientOf, simulateQ_bind, StateT.run_bind, map_bind, PqxdhRecordLiftCtxPrivLink.coinForward_program,
    Functor.map_map]
  have linked := PqxdhRecordLiftCtxPrivLink.linked_schedule target modes sel key setup codec
    (schedule codec.frameRead route client initialControl)
    (PqxdhRecordLiftCtxProtocol.erasePrivate PqxdhRecordLiftProtocol.initialPrivate)
    AdaptiveCtxDynamicKnownKeys.initialSource
  have worldRun := ctxInterpreterWith_schedule (selectedKey target key) (selectedModesM target sel modes) id setup codec
    (schedule codec.frameRead route client initialControl) CtxPrivate.initial
  rw [linkProj_initial, ← worldRun] at linked
  have mapped := congrArg (fun work => work >>= fun result =>
    decision (viewOf result.1 result.2.1.produced)) linked
  simp only [bind_map_left] at mapped
  refine Eq.trans ?_ (mapped.trans ?_)
  · simp only [id_map']
    rfl
  · rfl

/-- The three-mode client of privacy step `step` for an arbitrary World client. -/
noncomputable def stepClientOf (client : OracleComp (WorldSpec n) (Outcome E X)) (decision : View n E X → ProbComp Bool)
    (budget : Budget) (step : Fin (hops n budget)) : OracleComp PqxdhRecordLiftCtxPrivModes.Spec Bool :=
  linkClientOf setup codec route (PqxdhRecordLiftChainOrder.entryAt (positions := positions budget) step)
    (privModes (positions budget) step.val) client decision

/-- The game of privacy hybrid `cut` for an arbitrary World client. -/
noncomputable def gameOf (client : OracleComp (WorldSpec n) (Outcome E X)) (decision : View n E X → ProbComp Bool)
    (budget : Budget) (cut : Nat) : ProbComp Bool :=
  ctxRunOf (privModes (positions budget) cut) id setup codec route client >>= fun result => decision (ctxView result)

/-- The privacy hybrid before step `step` has the law of the challenger's replay game against the step client. -/
theorem game_replay_of (budget : Budget) (client : OracleComp (WorldSpec n) (Outcome E X))
    (records : RecordBounded budget client) (decision : View n E X → ProbComp Bool) (step : Fin (hops n budget)) :
    𝒟[gameOf setup codec route client decision budget step.val] =
      𝒟[Prod.fst <$> PqxdhRecordLiftCtxPrivModes.sourceGame uniformBytes .replay
        (RawCtxUniversalDecoder.decoder codec.frameRead) setup.source.crypto
        (stepClientOf setup codec route client decision budget step)] := by
  rw [stepClientOf, link_of _ _ _ _ (privModes (positions budget) step.val) .replay,
    selectedModesM_replay (n := n) (positions budget) step]
  exact key_cut_of _ _ id setup codec route budget client records decision

/-- The privacy hybrid after step `step` has the law of the challenger's random game against the step client. -/
theorem game_random_of (budget : Budget) (client : OracleComp (WorldSpec n) (Outcome E X))
    (records : RecordBounded budget client) (decision : View n E X → ProbComp Bool) (step : Fin (hops n budget)) :
    𝒟[gameOf setup codec route client decision budget (step.val + 1)] =
      𝒟[Prod.fst <$> PqxdhRecordLiftCtxPrivModes.sourceGame uniformBytes .random
        (RawCtxUniversalDecoder.decoder codec.frameRead) setup.source.crypto
        (stepClientOf setup codec route client decision budget step)] := by
  rw [stepClientOf, link_of _ _ _ _ (privModes (positions budget) step.val) .random,
    selectedModesM_random (n := n) (positions budget) step]
  exact key_cut_of _ _ id setup codec route budget client records decision

/-- **One privacy hop** for an arbitrary World client within the record budget: exactly the step's `privacyLoss`. -/
theorem hop_loss_of (budget : Budget) (client : OracleComp (WorldSpec n) (Outcome E X))
    (records : RecordBounded budget client) (decision : View n E X → ProbComp Bool) (step : Fin (hops n budget)) :
    ENNReal.ofReal ((gameOf setup codec route client decision budget step.val).boolDistance
        (gameOf setup codec route client decision budget (step.val + 1))) =
      privacyLoss (RawCtxUniversalDecoder.decoder codec.frameRead) setup.source.crypto
        (PqxdhRecordLiftCtxPrivModes.decisionClient bytesSample setup.source.crypto
          (stepClientOf setup codec route client decision budget step)) := by
  rw [PqxdhRecordLiftCtx.advantage_congr _ _ _ _ (game_replay_of setup codec route budget client records decision step)
    (game_random_of setup codec route budget client records decision step)]
  rw [PqxdhRecordLiftCtxPrivModes.hop_advantage]
  rfl

/-- The last privacy hybrid of an arbitrary World client within the record budget is its random-ciphertext world. -/
theorem game_last_of (budget : Budget) (client : OracleComp (WorldSpec n) (Outcome E X))
    (records : RecordBounded budget client) (decision : View n E X → ProbComp Bool) :
    (ctxRunOf (fun _ => .random) id setup codec route client >>= fun result => decision (ctxView result)) =
      gameOf setup codec route client decision budget (hops n budget) := by
  unfold gameOf
  rw [← ctxRunWithOf_tableKey, ← ctxRunWithOf_tableKey,
    ctxRunWithOf_congr tableKey tableKey (fun _ => .random) (privModes (positions budget) (hops n budget)) budget
      (fun _ _ _ _ => rfl) (fun label bounded => ((privModes_last _ label).mpr bounded).symm) id setup codec route client
      records]

/-- **The privacy telescope for an arbitrary World client within the record budget.** The integrity-ideal and random-ciphertext worlds differ, for every cache-free decision on the view, by at most the exact sum over the `hops n budget` indices of the per-key IND$ losses, each with coefficient one. -/
theorem ctx_priv_loss_of (budget : Budget) (client : OracleComp (WorldSpec n) (Outcome E X))
    (records : RecordBounded budget client) (decision : View n E X → ProbComp Bool) :
    ENNReal.ofReal
      ((ctxRunOf (fun _ => .replay) id setup codec route client >>= fun result => decision (ctxView result)).boolDistance
        (ctxRunOf (fun _ => .random) id setup codec route client >>= fun result => decision (ctxView result))) ≤
      ∑ step : Fin (hops n budget), privacyLoss (RawCtxUniversalDecoder.decoder codec.frameRead) setup.source.crypto
        (PqxdhRecordLiftCtxPrivModes.decisionClient bytesSample setup.source.crypto
          (stepClientOf setup codec route client decision budget step)) := by
  have firstGame : (ctxRunOf (fun _ => .replay) id setup codec route client >>= fun result =>
      decision (ctxView result)) = gameOf setup codec route client decision budget 0 := by
    unfold gameOf
    rw [privModes_zero]
  rw [firstGame, game_last_of setup codec route budget client records decision]
  have telescope := PqxdhComposition.finiteHybridBound_of_hop_bounds
    (gameOf setup codec route client decision budget) (hops n budget)
    (fun cut => (gameOf setup codec route client decision budget cut).boolDistance
      (gameOf setup codec route client decision budget (cut + 1))) (fun _ _ => le_refl _)
  calc ENNReal.ofReal ((gameOf setup codec route client decision budget 0).boolDistance
        (gameOf setup codec route client decision budget (hops n budget)))
      ≤ ENNReal.ofReal (∑ cut ∈ Finset.range (hops n budget),
          (gameOf setup codec route client decision budget cut).boolDistance
            (gameOf setup codec route client decision budget (cut + 1))) :=
        ENNReal.ofReal_le_ofReal telescope
    _ = ∑ cut ∈ Finset.range (hops n budget), ENNReal.ofReal
          ((gameOf setup codec route client decision budget cut).boolDistance
            (gameOf setup codec route client decision budget (cut + 1))) :=
        ENNReal.ofReal_sum_of_nonneg (fun _ _ => abs_nonneg _)
    _ = ∑ step : Fin (hops n budget), ENNReal.ofReal
          ((gameOf setup codec route client decision budget step.val).boolDistance
            (gameOf setup codec route client decision budget (step.val + 1))) :=
        (Fin.sum_univ_eq_sum_range (fun cut => ENNReal.ofReal
          ((gameOf setup codec route client decision budget cut).boolDistance
            (gameOf setup codec route client decision budget (cut + 1)))) _).symm
    _ = _ := Finset.sum_congr rfl (fun step _ => hop_loss_of setup codec route budget client records decision step)

end Hops

/-! ### Privacy bills for an arbitrary World client and the later privacy half -/

open PqxdhRecordLiftCtxPrivBills (UniformRoute KeyedRoute HashRoute TargetClass)
open PqxdhRecordLiftLaterTargets
open PqxdhDeploymentLater (PostSpec PostBudget)

/-- A privacy link client of an arbitrary World client is bounded in one category by the compiled client's bill under the step reduction's per-service cost, plus the decision's coins at their unit. -/
theorem link_route_of (target : Label n) (modes : Label n → KeyMode) (setup : Setup baseSpec KemSK)
    (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (client : OracleComp (WorldSpec n) (Outcome E X)) (decision : View n E X → ProbComp Bool)
    (predicate : PqxdhRecordLiftCtxPrivModes.Spec.Domain → Prop) [DecidablePred predicate]
    (cost : PqxdhRecordLiftProtocol.Service n → Nat) (programBound decisionCost decisionUnit : Nat)
    (step : ∀ query state, ((PqxdhRecordLiftCtxPrivLink.reduction target modes setup codec query).run state).IsQueryBoundP
      predicate (cost query))
    (program : Weighted cost (schedule codec.frameRead route client initialControl) programBound)
    (coins : ∀ view, (decision view).IsTotalQueryBound decisionCost)
    (coinStep : ∀ coin, predicate (.inr (PqxdhRecordLiftCtxPrivLink.publicCall
      (RawCtxUniversalDecoder.decoder codec.frameRead) (.inl (.inl coin)))) → 0 < decisionUnit) :
    (linkClientOf setup codec route target modes client decision).IsQueryBoundP predicate
      (programBound + decisionCost * decisionUnit) :=
  isQueryBoundP_bind (PqxdhRecordLiftCtxBills.run_bound (PqxdhRecordLiftCtxPrivLink.reduction target modes setup codec)
    predicate cost step _ programBound program _)
    (fun _ _ => PqxdhRecordLiftCtxPrivBills.coinForward_route _ predicate _ decisionCost decisionUnit (coins _) coinStep)

/-- The privacy adversaries of an arbitrary World client whose compiled program stays within `bill` in every CTX ledger make at most `bill .uniform + cost + 66 * bill .hash` uniform requests, `bill .hash` shared-hash requests, one selected seal and `bill .raw` selected raw requests. -/
theorem priv_step_bills_of (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (client : OracleComp (WorldSpec n) (Outcome E X))
    (bill : BudgetKind → Nat)
    (program : ∀ kind, Weighted (categoryCost kind) (schedule codec.frameRead route client initialControl) (bill kind))
    (decision : View n E X → ProbComp Bool) (cost : Nat) (coins : ∀ view, (decision view).IsTotalQueryBound cost)
    (budget : Budget) (step : Fin (hops n budget)) :
    let adversary := PqxdhRecordLiftCtxPrivModes.decisionClient bytesSample setup.source.crypto
      (stepClientOf setup codec route client decision budget step)
    adversary.IsQueryBoundP SourceUniform (bill .uniform + cost + 66 * bill .hash) ∧
      adversary.IsQueryBoundP SourceHash (bill .hash) ∧ adversary.IsQueryBoundP SourceSeal 1 ∧
      adversary.IsQueryBoundP IsRawQuery (bill .raw) := by
  intro adversary
  let target := PqxdhRecordLiftChainOrder.entryAt (positions := positions budget) step
  let modes : Label n → KeyMode := privModes (positions budget) step.val
  have uniform := link_route_of target modes setup codec route client decision UniformRoute _ _ cost 1
    (PqxdhRecordLiftCtxPrivBills.reduction_uniform target modes setup codec) (program .uniform) coins
    (fun _ _ => Nat.one_pos)
  have keyed := link_route_of target modes setup codec route client decision KeyedRoute _ _ cost 0
    (PqxdhRecordLiftCtxPrivBills.reduction_keyed target modes setup codec) (program .hash) coins
    (fun _ hit => by simp [KeyedRoute, PqxdhRecordLiftCtxPrivLink.publicCall, SourceUniform] at hit)
  have hash := link_route_of target modes setup codec route client decision HashRoute _ _ cost 0
    (PqxdhRecordLiftCtxPrivBills.reduction_hash target modes setup codec) (program .hash) coins
    (fun _ hit => by simp [HashRoute, PqxdhRecordLiftCtxPrivLink.publicCall, SourceUniform] at hit)
  have sealing := link_route_of target modes setup codec route client decision (TargetClass SourceSeal) _ _ cost 0
    (PqxdhRecordLiftCtxPrivBills.reduction_seal target modes setup codec)
    (schedule_target_seal target codec route client) coins (fun _ hit => by simp [TargetClass] at hit)
  have raw := link_route_of target modes setup codec route client decision (TargetClass IsRawQuery) _ _ cost 0
    (PqxdhRecordLiftCtxPrivBills.reduction_raw target modes setup codec) (program .raw) coins
    (fun _ hit => by simp [TargetClass] at hit)
  simp only [Nat.mul_one, Nat.mul_zero, Nat.add_zero] at uniform keyed hash sealing raw
  exact PqxdhRecordLiftCtxPrivBills.decision_budgets setup.source.crypto _ _ _ _ _ _ uniform keyed hash sealing raw

/-- The explicit later privacy bills: the two-phase program's coins plus the decision's coins plus 66 coins per keyed request, its shared hashes, one seal and the raw receives. -/
def laterPrivBills : LaterCtxBills where
  uniform input := laterCtxProgramBill .uniform input + input.base.decision + 66 * laterCtxProgramBill .hash input
  hash input := laterCtxProgramBill .hash input
  seals _ := 1
  raw input := laterCtxProgramBill .raw input

/-- The later privacy hash bill is the run-phase shared-hash total plus the post phase's shared-hash work. -/
theorem laterPriv_hash_bill (input : LaterBillInput) : laterPrivBills.hash input = laterSharedHashTotal input :=
  laterCtx_hash_bill input

section Final
variable (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
  (serverKid : Std.U64) (bounds : FreshBounds)

/-- The explicit later privacy reduction family: hop `step`'s ordinary one-key CTX adversary is the privacy step client of the compiled two-phase program, with the known-key work run inside and random-mode records drawn by the single-coin sampler. -/
noncomputable def laterPrivReduction : LaterCtxReduction n :=
  fun env mode reveal first second decision budget _ step =>
    PqxdhRecordLiftCtxPrivModes.decisionClient bytesSample setup.source.crypto
      (stepClientOf setup codec route
        (PqxdhRecordLiftLater.program env setup.source.crypto codec serverKid bounds mode reveal first second)
        decision budget step)

/-- Later `ctx_lift`, privacy half, Boolean form, with the explicit reductions and the explicit bills. -/
theorem later_ctx_priv_lift_bool (n : Nat) :
    LaterCtxPrivLiftBool setup codec route serverKid bounds n (laterPrivReduction setup codec route serverKid bounds)
      laterPrivBills := by
  intro E X Out R env startup allowance framed mode reveal first second budget post respects postRespects decision cost
    coins
  have program := fun kind => schedule_categories kind codec route _ _
    (later_world_categories kind env startup allowance framed setup.source.crypto codec serverKid bounds mode budget post
      reveal first second respects postRespects cost)
  refine ⟨?_, fun step => priv_step_bills_of setup codec route _ _ program decision cost coins budget step⟩
  simpa only [laterIdealAuth, laterRandomRecords, laterCtxRun, laterPrivReduction] using
    ctx_priv_loss_of setup codec route budget
      (PqxdhRecordLiftLater.program env setup.source.crypto codec serverKid bounds mode reveal first second)
      (later_recordBounded env setup.source.crypto codec serverKid bounds mode budget reveal first second respects)
      decision

/-- **Later `ctx_lift`, privacy half (R6, item 4), delivered.** `LaterCtxPrivLiftStatement` (Boolean and event forms) for the explicit reductions `laterPrivReduction` and bills `laterPrivBills`: in either observation mode, `laterIdealAuth` and `laterRandomRecords` (in mode P, `laterIdealRecords`) differ by at most the exact sum of the per-key IND$ losses, each with coefficient one. -/
theorem later_ctx_priv_lift (n : Nat) :
    LaterCtxPrivLiftStatement setup codec route serverKid bounds n (laterPrivReduction setup codec route serverKid bounds)
      laterPrivBills :=
  laterCtxPrivLiftStatement_of_bool setup codec route serverKid bounds n _ laterPrivBills
    (later_ctx_priv_lift_bool setup codec route serverKid bounds n)

end Final

end BeaconcryptCore.Computational.PqxdhRecordLiftLaterPriv

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftLaterPriv.link_of' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftLaterPriv.link_of

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftLaterPriv.game_replay_of' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftLaterPriv.game_replay_of

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftLaterPriv.game_random_of' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftLaterPriv.game_random_of

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftLaterPriv.hop_loss_of' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftLaterPriv.hop_loss_of

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftLaterPriv.game_last_of' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftLaterPriv.game_last_of

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftLaterPriv.ctx_priv_loss_of' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftLaterPriv.ctx_priv_loss_of

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftLaterPriv.link_route_of' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftLaterPriv.link_route_of

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftLaterPriv.priv_step_bills_of' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftLaterPriv.priv_step_bills_of

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftLaterPriv.laterPriv_hash_bill' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftLaterPriv.laterPriv_hash_bill

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftLaterPriv.later_ctx_priv_lift_bool' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftLaterPriv.later_ctx_priv_lift_bool

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftLaterPriv.later_ctx_priv_lift' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftLaterPriv.later_ctx_priv_lift
