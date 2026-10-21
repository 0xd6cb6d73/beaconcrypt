-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRecordLiftCtxBills
import BeaconcryptCore.Computational.PqxdhRecordLiftLaterTargets

/-!
# Record-lift later `ctx_lift`, integrity half (items 4 and 5, stage S6, R6, item 4)

**Statement.** `later_ctx_auth_lift` proves `PqxdhRecordLiftLaterTargets.LaterCtxAuthLiftTarget` as defined, for the explicit reduction family `laterCtxReduction` and the explicit bills `laterCtxBills`: for every environment with `Frame`, every run-phase adversary within its budget, every reveal function, every post adversary within its post budget and every cache-free decision on the later view (or every Boolean event of it), in either observation mode, the later chain-ideal world and the later integrity-ideal world `laterIdealAuth` differ by at most the exact sum over the `hops n budget` target key indices of the per-key integrity losses at the bills' hash and raw caps, each with coefficient one (the factor 2 on INT-CTXT stays inside `integrityLoss`), with zero refusal term.

**Method: the integrity hybrid of an arbitrary World client.** The CTX track's hop and telescope (`PqxdhRecordLiftCtx`) are stated for the frozen run-phase program, but their cores are schedule-level: the all-real source equality (`PqxdhRecordLiftCtxHybrid.schedule_bare` with `PqxdhRecordLiftProtocolHistory.initial_schedule_fresh` and `PqxdhRecordLiftCtxProtocol.schedule_admitted`), availability (`PqxdhRecordLiftCtxAvailability.certified_map` with `schedule_history`), the eager target key (`PqxdhRecordLiftKeyCut.table_eager`) and the link (`PqxdhRecordLiftCtxLink.linked_schedule`, `ctxInterpreterWith_schedule`) hold for every compiled client. This module restates the program-level wrappers for an arbitrary World client within the record budget: the all-real CTX world is the chain-ideal world (`allReal_bare_of`, `allReal_decision_of`), the lookup bill and availability (`world_lookups_of`, `schedule_lookups`, `schedule_map`, `schedule_congr`), explicit-key worlds and the last hybrid (`ctxRunWithOf`, `ctxRunWithOf_tableKey`, `ctxRunWithOf_congr`, `hybrid_last_of`), the selected-key law (`selected_table_of`, `key_cut_of`, stated with `𝒟` only: the existing eager law enters through `EvalDistEq.evalDist_eq` at a local discrete measurable space), the link (`linkClientOf`, `link_of`), one hop (`stepClientOf`, `gameOf`, `game_real_of`, `game_replay_of`, `hop_bound_of`) and the telescope (`ctx_auth_loss_of`). The proofs are the CTX track's, with the compiled client in place of the frozen program. The later target is `ctx_auth_loss_of` at the two-phase program, within the run budget's record part (`PqxdhRecordLiftLaterWorlds.later_recordBounded`).

**Bills.** A compiled client within a World-level bill stays within it in every CTX ledger (`schedule_categories`), seals each target coordinate at most once (`schedule_target_seal`), and its step clients respect the bill's uniform (64 per private replay-cache fill), shared-hash, seal (one) and raw caps (`link_route_of`, `step_bills_of`). The two-phase World program stays within `laterCtxProgramBill`, the run-phase `PqxdhRecordLiftCtxBills.programBill` plus the post phase's coin, hash and administrative effects (`later_world_categories`, from `PqxdhRecordLiftLater.program_effect_bound` and `program_record_bound`). Hence `laterCtxBills`, whose hash bill is the run-phase shared-hash total plus the post phase's shared-hash work, the `PostBudget` term of the hash route (`laterCtx_hash_bill`: `laterSharedHashTotal`), and whose raw bill is the run-phase one (`laterCtx_raw_bill`).

**Contracts.** No theorem of this module has an assumption or contract hypothesis. `hop_bound_of`, `ctx_auth_loss_of`, `later_ctx_auth_lift_bool` and `later_ctx_auth_lift` use, through `PqxdhRecordLiftCtxModeBounds.selected_integrity`, functional AEAD correctness (the fields `aead_open_seal` and `aeadSeal_tag_length` of `Pqxdh.Crypto`), the modified-nonce AEAD IND$ and INT-CTXT games as the advantage terms of `integrityLoss` and the BLAKE2b random-oracle model as the world model; `allReal_bare_of` and `allReal_decision_of` use `aeadSeal_tag_length` only (the CTX track's source equality); no other theorem uses a contract (per-theorem closure probe). New Claude work; the proofs of the client-level wrappers follow the CTX track's program-level proofs.
-/

open OracleComp OracleSpec ENNReal CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false

namespace BeaconcryptCore.Computational.PqxdhRecordLiftLaterCtx
open PqxdhRecordLiftInterface PqxdhRecordLiftIdeal PqxdhRecordLiftCtxHybrid PqxdhRecordLiftCtxLink
open PqxdhRecordLiftCtxAvailability PqxdhRecordLiftKeyCut PqxdhRecordLiftLaterWorlds
open PqxdhDeploymentInterface (Mode ModeSpec FreshBounds Budget)
open PqxdhServerAuthExperiment (Setup Codec)
open PqxdhRecordLiftWorldCompiler (Label)
open PqxdhRecordLiftProtocol (schedule initialControl)
open PqxdhRecordLiftChainTable (Table)
open PqxdhRecordLiftMaterialTable (Present)
open PqxdhRecordLiftCtxProgramBounds (Weighted)
open CtxRomAuth AdaptiveCtxReceive
variable {n : Nat} {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response E X : Type}

/-! ### The all-real CTX world of an arbitrary World client -/

/-- The all-real CTX world of an arbitrary World client erases exactly to its chain-ideal world: the complete client result and the counter-erased private state have the same law. -/
theorem allReal_bare_of (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (client : OracleComp (WorldSpec n) (Outcome E X)) :
    Prod.map id ctxBare <$> ctxRunOf (fun _ => .real) id setup codec route client =
      Prod.map id PqxdhRecordLiftCtxProtocol.erasePrivate <$> chainsOf (fun _ => true) setup codec route client := by
  rw [ctxRunOf, schedule_bare setup codec _ CtxPrivate.initial [] initial_unsealed
      (PqxdhRecordLiftProtocolHistory.initial_schedule_fresh codec.frameRead route client)
      (PqxdhRecordLiftCtxProtocol.schedule_admitted codec.frameRead route client initialControl), chainsOf]
  exact (PqxdhRecordLiftCtxProtocol.bare_schedule setup codec (fun _ => true) _
    PqxdhRecordLiftProtocol.initialPrivate).symm

/-- The all-real CTX world and the chain-ideal world of an arbitrary World client give the same law to every cache-free decision on the view. -/
theorem allReal_decision_of (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (client : OracleComp (WorldSpec n) (Outcome E X))
    (decision : View n E X → ProbComp Bool) :
    (ctxRunOf (fun _ => .real) id setup codec route client >>= fun result => decision (ctxView result)) =
      (chainsOf (fun _ => true) setup codec route client >>= fun result => decision (chainView result)) := by
  have same := congrArg (fun work => (fun result => viewOf result.1 result.2.produced) <$> work)
    (allReal_bare_of setup codec route client)
  simp only [Functor.map_map] at same
  have views : ctxView <$> ctxRunOf (fun _ => .real) id setup codec route client =
      chainView <$> chainsOf (fun _ => true) setup codec route client := same
  rw [← bind_map_left ctxView, ← bind_map_left chainView, views]

/-! ### Availability for an arbitrary World client -/

/-- A World client within the record budget has World lookup weight at most `positions budget`. -/
theorem world_lookups_of (budget : Budget) (client : OracleComp (WorldSpec n) (Outcome E X))
    (records : RecordBounded budget client) :
    Weighted worldLookups client (positions budget) := by
  have sends := PqxdhRecordLiftCtxProgramBounds.weighted_indicator (PqxdhRecordLiftBudget.WorldRecord .send) 1 _ _
    (records .send)
  have raws := PqxdhRecordLiftCtxProgramBounds.weighted_indicator (PqxdhRecordLiftBudget.WorldRecord .raw) 51 _ _
    (records .raw)
  have joint := PqxdhRecordLiftCtxProgramBounds.weighted_add _ _ _ _ _ sends raws
  have cost : (fun query => (if PqxdhRecordLiftBudget.WorldRecord .send query then 1 else 0) +
      (if PqxdhRecordLiftBudget.WorldRecord .raw query then 51 else 0)) = (worldLookups : (WorldSpec n).Domain → Nat) := by
    funext query
    rcases query with _ | _ | record
    · simp [worldLookups, PqxdhRecordLiftBudget.WorldRecord]
    · simp [worldLookups, PqxdhRecordLiftBudget.WorldRecord]
    · cases kind : PqxdhRecordLiftBudget.recordKind record <;>
        simp [worldLookups, PqxdhRecordLiftBudget.WorldRecord, kind]
  rw [cost] at joint
  simpa [positions, PqxdhRecordLiftBudget.recordBudget] using joint

/-- The compiled program of a World client within the record budget performs at most `positions budget` private lookups. -/
theorem schedule_lookups (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder) (budget : Budget)
    (client : OracleComp (WorldSpec n) (Outcome E X)) (records : RecordBounded budget client) :
    Weighted lookupCost (schedule codec.frameRead route client initialControl) (positions budget) :=
  PqxdhRecordLiftCtxProgramBounds.weighted_run worldLookups lookupCost _ _ _ _
    (world_lookups_of budget client records) (fun query control => handler_lookups codec.frameRead route query control)

/-- **Availability of an arbitrary compiled World client within the record budget.** A private interpreter simulated through a state map on every request touching only present coordinates within `positions budget` is simulated through it on the whole compiled client. -/
theorem schedule_map {σ τ : Type} (budget : Budget)
    (impl : QueryImpl (PqxdhRecordLiftProtocol.ServiceSpec n) (StateT σ ProbComp))
    (other : QueryImpl (PqxdhRecordLiftProtocol.ServiceSpec n) (StateT τ ProbComp))
    (map : σ → τ) (chainOf : σ → Table (Slot n)) (Inv : σ → Prop)
    (step : ∀ query state, Inv state → Touches (positions budget) (chainOf state) query →
      Prod.map id map <$> (impl query).run state = (other query).run (map state))
    (preserve : ∀ query state, Inv state → ∀ result ∈ support ((impl query).run state),
      Inv result.2 ∧ chainOf state ≤ chainOf result.2 ∧
        ∀ label ∈ lookupCoordinates query, Present (chainOf result.2) label)
    (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (client : OracleComp (WorldSpec n) (Outcome E X)) (records : RecordBounded budget client)
    (state : σ) (invariant : Inv state) :
    Prod.map id map <$> (simulateQ impl (schedule codec.frameRead route client initialControl)).run state =
    (simulateQ other (schedule codec.frameRead route client initialControl)).run (map state) :=
  certified_map (positions budget) impl other map chainOf Inv step preserve _ [] _ state
    (schedule_history codec.frameRead route client initialControl [] initial_ready).1
    (schedule_lookups codec route budget client records)
    history_empty (by simp) (fun _ member => by simp at member) invariant

/-- Two keyed implementations agreeing on every request at a present coordinate within `positions budget` give the same CTX world for an arbitrary World client within the record budget, from every state. -/
theorem schedule_congr (keyed other : QueryImpl (KeyedSpec n) (StateT (CtxPrivate n) ProbComp)) (budget : Budget)
    (keep : ∀ query state, ∀ result ∈ support ((keyed query).run state), result.2.base.chain = state.base.chain)
    (agree : ∀ query state, Present state.base.chain query.1 →
      PqxdhRecordLiftChainOrder.Bounded (positions budget) query.1 →
      (keyed query).run state = (other query).run state)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (client : OracleComp (WorldSpec n) (Outcome E X))
    (records : RecordBounded budget client) (state : CtxPrivate n) :
    (simulateQ (ctxInterpreterOf keyed replace setup codec) (schedule codec.frameRead route client initialControl)).run
        state =
      (simulateQ (ctxInterpreterOf other replace setup codec) (schedule codec.frameRead route client initialControl)).run
        state := by
  have mapped := schedule_map budget (ctxInterpreterOf keyed replace setup codec)
    (ctxInterpreterOf other replace setup codec) id (fun state => state.base.chain) (fun _ => True)
    (fun query state _ touches => by
      rw [Prod.map_id, id_map]
      exact ctxInterpreterOf_congr _ keyed other agree replace setup codec query state touches)
    (fun query state _ result supported => ⟨trivial, chain_step keyed keep replace setup codec query state result supported⟩)
    codec route client records state trivial
  rwa [Prod.map_id, id_map] at mapped

/-- The explicit-key CTX world of an arbitrary World client. -/
noncomputable def ctxRunWithOf (keyOf : KeyOf n) (modes : Label n → KeyMode) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (client : OracleComp (WorldSpec n) (Outcome E X)) : ProbComp (PqxdhRecordLiftIdeal.Client n E X × CtxPrivate n) :=
  (simulateQ (ctxInterpreterWith keyOf modes replace setup codec)
    (schedule codec.frameRead route client initialControl)).run CtxPrivate.initial

/-- With the table key, the explicit-key world is `ctxRunOf`. -/
theorem ctxRunWithOf_tableKey (modes : Label n → KeyMode) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (client : OracleComp (WorldSpec n) (Outcome E X)) :
    ctxRunWithOf tableKey modes replace setup codec route client = ctxRunOf modes replace setup codec route client := by
  have same : ctxInterpreterWith (tableKey (n := n)) modes replace setup codec = ctxInterpreter modes replace setup codec := by
    funext query
    cases query <;> rfl
  rw [ctxRunWithOf, same, ctxRunOf]

/-- Explicit-key CTX worlds of an arbitrary World client within the record budget whose keys and modes agree at every present coordinate within `positions budget` are equal. -/
theorem ctxRunWithOf_congr (keyOf other : KeyOf n) (modes otherModes : Label n → KeyMode) (budget : Budget)
    (sameKey : ∀ table label, Present table label → PqxdhRecordLiftChainOrder.Bounded (positions budget) label →
      keyOf table label = other table label)
    (sameMode : ∀ label, PqxdhRecordLiftChainOrder.Bounded (positions budget) label → modes label = otherModes label)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (client : OracleComp (WorldSpec n) (Outcome E X))
    (records : RecordBounded budget client) :
    ctxRunWithOf keyOf modes replace setup codec route client =
      ctxRunWithOf other otherModes replace setup codec route client := by
  unfold ctxRunWithOf
  rw [ctxInterpreterWith_of, ctxInterpreterWith_of]
  exact schedule_congr _ _ budget (keyedWith_chain keyOf modes _ _)
    (fun query state present bounded => keyedWith_congr keyOf other modes otherModes _ _ query state
      (sameKey _ _ present bounded) (sameMode _ bounded))
    replace setup codec route client records _

/-- **The last hybrid is the integrity-ideal world** for an arbitrary World client within the record budget. -/
theorem hybrid_last_of (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (budget : Budget) (client : OracleComp (WorldSpec n) (Outcome E X))
    (records : RecordBounded budget client) :
    ctxRunOf (hybridModes (positions budget) (hops n budget)) id setup codec route client =
      ctxRunOf (fun _ => .replay) id setup codec route client := by
  rw [← ctxRunWithOf_tableKey, ← ctxRunWithOf_tableKey]
  exact ctxRunWithOf_congr tableKey tableKey _ _ budget (fun _ _ _ _ => rfl)
    (fun label bounded => (hybridModes_last _ label).mpr bounded) id setup codec route client records

/-! ### The selected-key law for an arbitrary World client -/

/-- For an arbitrary World client within the record budget, the world that stores the supplied key in the target's entry and reads every key from the table is the world that stores it and keys the target with the supplied key directly. -/
theorem selected_table_of (modes : Label n → KeyMode) (target : Label n) (key : PqxdhSecretInputKdf.RootOutput)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (budget : Budget) (client : OracleComp (WorldSpec n) (Outcome E X))
    (records : RecordBounded budget client) :
    (simulateQ (world (keyedWith tableKey modes (RawCtxUniversalDecoder.decoder codec.frameRead) setup.source.crypto)
      (keyStore key) target replace setup codec) (schedule codec.frameRead route client initialControl)).run
        CtxPrivate.initial =
    (simulateQ (world (keyedWith (selectedKey target key) modes (RawCtxUniversalDecoder.decoder codec.frameRead)
      setup.source.crypto) (keyStore key) target replace setup codec)
      (schedule codec.frameRead route client initialControl)).run CtxPrivate.initial := by
  have mapped := schedule_map budget _ _ id (fun state : CtxPrivate n => state.base.chain) (KeyStored target key)
    (fun query state stored touches => by
      rw [Prod.map_id, id_map]
      exact world_selected_step modes target key replace setup codec _ query state stored touches)
    (fun query state stored result supported => world_preserve _ (keyedWith_chain tableKey modes _ _) target key
      replace setup codec query state stored result supported)
    codec route client records CtxPrivate.initial (initial_stored target key)
  rwa [Prod.map_id, id_map] at mapped

/-- **The selected-key law for an arbitrary World client.** For every mode assignment, coordinate and World client within the record budget, the CTX world followed by a decision on its view has the law of first sampling a uniform key and running the CTX world whose `target` coordinate is keyed with it. -/
theorem key_cut_of {Out : Type} [MeasurableSpace Out] (modes : Label n → KeyMode) (target : Label n)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (budget : Budget) (client : OracleComp (WorldSpec n) (Outcome E X))
    (records : RecordBounded budget client) (decision : View n E X → ProbComp Out) :
    𝒟[ctxRunOf modes replace setup codec route client >>= fun result => decision (ctxView result)] =
      𝒟[do
        let key ← $ᵗ CtxKey
        let result ← ctxRunWithOf (selectedKey target key) modes replace setup codec route client
        decision (ctxView result)] := by
  let : MeasurableSpace (PqxdhRecordLiftIdeal.Client n E X × CtxPrivate n) := ⊤
  have eager := (table_eager modes target replace setup codec
    (schedule codec.frameRead route client initialControl) CtxPrivate.initial).evalDist_eq
  have perKey : ∀ key : CtxKey, ((simulateQ (world (keyedWith tableKey modes
      (RawCtxUniversalDecoder.decoder codec.frameRead) setup.source.crypto) (keyStore key) target replace setup codec)
      (schedule codec.frameRead route client initialControl)).run CtxPrivate.initial >>= fun result =>
        decision (ctxView result)) =
      (ctxRunWithOf (selectedKey target key) modes replace setup codec route client >>= fun result =>
        decision (ctxView result)) := by
    intro key
    rw [← bind_map_left ctxView, ← bind_map_left ctxView, selected_table_of modes target key replace setup codec route
      budget client records, ctxView_map, stored_view, ← ctxView_map]
    rfl
  rw [← ctxRunWithOf_tableKey, ctxRunWithOf, evalDist_bind_of_discrete, eager, ← evalDist_bind_of_discrete, bind_assoc]
  simp only [perKey]

/-! ### The link of one hybrid step for an arbitrary World client -/

/-- The key-free reduction client of one hybrid step for an arbitrary World client: the whole compiled client under `PqxdhRecordLiftCtxLink.reduction`, then the decision on the view with its coins forwarded through the reserved slot. -/
noncomputable def linkClientOf (target : Label n) (modes : Label n → KeyMode) (setup : Setup baseSpec KemSK)
    (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (client : OracleComp (WorldSpec n) (Outcome E X)) (decision : View n E X → ProbComp Bool) :
    OracleComp PqxdhRecordLiftCtxModes.Spec Bool := do
  let result ← (simulateQ (reduction target modes setup codec) (schedule codec.frameRead route client initialControl)).run
    (PqxdhRecordLiftCtxProtocol.erasePrivate PqxdhRecordLiftProtocol.initialPrivate)
  simulateQ (coinForward (RawCtxUniversalDecoder.decoder codec.frameRead)) (decision (viewOf result.1 result.2.produced))

/-- Link of one hybrid step for an arbitrary World client: the challenger's real or replay game against the key-free reduction client is the CTX world in which the selected coordinate's key is a fresh uniform key held by the challenger, in the challenger's mode. -/
theorem link_of (target : Label n) (modes : Label n → KeyMode)
    (notRandom : ∀ label, label ≠ target → modes label ≠ .random) (real : Bool)
    (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (client : OracleComp (WorldSpec n) (Outcome E X)) (decision : View n E X → ProbComp Bool) :
    Prod.fst <$> PqxdhRecordLiftCtxModes.sourceGame real (RawCtxUniversalDecoder.decoder codec.frameRead)
        setup.source.crypto (linkClientOf target modes setup codec route client decision) =
      (do
        let key ← $ᵗ CtxKey
        let result ← ctxRunWithOf (selectedKey target key) (selectedModes target real modes) id setup codec route client
        decision (ctxView result)) := by
  simp only [PqxdhRecordLiftCtxModes.sourceGame, map_bind]
  apply bind_congr
  intro key
  simp only [linkClientOf, simulateQ_bind, StateT.run_bind, map_bind, coinForward_program, Functor.map_map]
  have linked := linked_schedule target modes notRandom real key setup codec
    (schedule codec.frameRead route client initialControl)
    (PqxdhRecordLiftCtxProtocol.erasePrivate PqxdhRecordLiftProtocol.initialPrivate)
    AdaptiveCtxDynamicKnownKeys.initialSource
  have worldRun := ctxInterpreterWith_schedule (selectedKey target key) (selectedModes target real modes) id setup codec
    (schedule codec.frameRead route client initialControl) CtxPrivate.initial
  rw [linkProj_initial, ← worldRun] at linked
  have mapped := congrArg (fun work => work >>= fun result =>
    decision (viewOf result.1 result.2.1.produced)) linked
  simp only [bind_map_left] at mapped
  refine Eq.trans ?_ (mapped.trans ?_)
  · simp only [id_map']
    rfl
  · rfl

/-! ### The hops and the telescope for an arbitrary World client -/

open PqxdhRecordLiftCtxModeBounds (UniformRoute PrivateRoute HashRoute TargetClass)
open AdaptiveCtxQueryBounds (SourceSeal)

section Hops
variable (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)

/-- The one-key adversary of hybrid step `step` for an arbitrary World client: the key-free link client of the step's coordinate under the modes before the step. -/
noncomputable def stepClientOf (client : OracleComp (WorldSpec n) (Outcome E X)) (decision : View n E X → ProbComp Bool)
    (budget : Budget) (step : Fin (hops n budget)) : OracleComp PqxdhRecordLiftCtxModes.Spec Bool :=
  linkClientOf (PqxdhRecordLiftChainOrder.entryAt (positions := positions budget) step)
    (hybridModes (positions budget) step.val) setup codec route client decision

/-- The game of hybrid `cut` for an arbitrary World client under a decision on the view. -/
noncomputable def gameOf (client : OracleComp (WorldSpec n) (Outcome E X)) (decision : View n E X → ProbComp Bool)
    (budget : Budget) (cut : Nat) : ProbComp Bool :=
  ctxRunOf (hybridModes (positions budget) cut) id setup codec route client >>= fun result => decision (ctxView result)

/-- The hybrid before step `step` has the law of the challenger's real game against the step client. -/
theorem game_real_of (budget : Budget) (client : OracleComp (WorldSpec n) (Outcome E X))
    (records : RecordBounded budget client) (decision : View n E X → ProbComp Bool) (step : Fin (hops n budget)) :
    𝒟[gameOf setup codec route client decision budget step.val] =
      𝒟[Prod.fst <$> PqxdhRecordLiftCtxModes.sourceGame true (RawCtxUniversalDecoder.decoder codec.frameRead)
        setup.source.crypto (stepClientOf setup codec route client decision budget step)] := by
  rw [stepClientOf, link_of _ (hybridModes (positions budget) step.val) (fun label _ => hybridModes_notRandom _ _ label),
    selectedModes_hybrid_real (n := n) (positions budget) step]
  exact key_cut_of _ _ id setup codec route budget client records decision

/-- The hybrid after step `step` has the law of the challenger's replay game against the step client. -/
theorem game_replay_of (budget : Budget) (client : OracleComp (WorldSpec n) (Outcome E X))
    (records : RecordBounded budget client) (decision : View n E X → ProbComp Bool) (step : Fin (hops n budget)) :
    𝒟[gameOf setup codec route client decision budget (step.val + 1)] =
      𝒟[Prod.fst <$> PqxdhRecordLiftCtxModes.sourceGame false (RawCtxUniversalDecoder.decoder codec.frameRead)
        setup.source.crypto (stepClientOf setup codec route client decision budget step)] := by
  rw [stepClientOf, link_of _ (hybridModes (positions budget) step.val) (fun label _ => hybridModes_notRandom _ _ label),
    selectedModes_hybrid_replay (n := n) (positions budget) step]
  exact key_cut_of _ _ id setup codec route budget client records decision

/-- **One hop** for an arbitrary World client within the record budget: the hybrids before and after step `step` differ by at most the step's integrity loss, at every hash and raw cap of its step client and every seal cap below `2^96`. -/
theorem hop_bound_of (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery) (budget : Budget)
    (client : OracleComp (WorldSpec n) (Outcome E X)) (records : RecordBounded budget client)
    (decision : View n E X → ProbComp Bool) (step : Fin (hops n budget)) (qHash qSeal qRaw : Nat)
    (hashBound : (stepClientOf setup codec route client decision budget step).IsQueryBoundP HashRoute qHash)
    (sealBound : (stepClientOf setup codec route client decision budget step).IsQueryBoundP (TargetClass SourceSeal)
      qSeal)
    (rawBound : (stepClientOf setup codec route client decision budget step).IsQueryBoundP (TargetClass IsRawQuery)
      qRaw)
    (small : qSeal < 2 ^ 96) :
    ENNReal.ofReal ((gameOf setup codec route client decision budget step.val).boolDistAdvantage
      (gameOf setup codec route client decision budget (step.val + 1))) ≤
      integrityLoss (RawCtxUniversalDecoder.decoder codec.frameRead) setup.source.crypto fallback
        (PqxdhRecordLiftCtxModes.decisionClient setup.source.crypto
          (stepClientOf setup codec route client decision budget step)) qHash qRaw := by
  rw [PqxdhRecordLiftCtx.advantage_congr _ _ _ _ (game_real_of setup codec route budget client records decision step)
    (game_replay_of setup codec route budget client records decision step)]
  exact PqxdhRecordLiftCtxModeBounds.selected_integrity _ _ fallback _ qHash qSeal qRaw hashBound sealBound rawBound small

/-- **The integrity telescope for an arbitrary World client within the record budget.** If every step client stays within the hash cap `qHash`, the raw cap `qRaw` and a seal cap below `2^96`, the chain-ideal and integrity-ideal worlds differ, for every cache-free decision on the view, by at most the exact sum over the `hops n budget` indices of the per-key integrity losses, each with coefficient one. -/
theorem ctx_auth_loss_of (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery) (budget : Budget)
    (client : OracleComp (WorldSpec n) (Outcome E X)) (records : RecordBounded budget client)
    (decision : View n E X → ProbComp Bool) (qHash qRaw : Nat)
    (stepBounds : ∀ step : Fin (hops n budget), ∃ qSeal,
      (stepClientOf setup codec route client decision budget step).IsQueryBoundP HashRoute qHash ∧
      (stepClientOf setup codec route client decision budget step).IsQueryBoundP (TargetClass SourceSeal) qSeal ∧
      qSeal < 2 ^ 96 ∧
      (stepClientOf setup codec route client decision budget step).IsQueryBoundP (TargetClass IsRawQuery) qRaw) :
    ENNReal.ofReal
      ((chainsOf (fun _ => true) setup codec route client >>= fun result => decision (chainView result)).boolDistAdvantage
        (ctxRunOf (fun _ => .replay) id setup codec route client >>= fun result => decision (ctxView result))) ≤
      ∑ step : Fin (hops n budget), integrityLoss (RawCtxUniversalDecoder.decoder codec.frameRead) setup.source.crypto
        fallback (PqxdhRecordLiftCtxModes.decisionClient setup.source.crypto
          (stepClientOf setup codec route client decision budget step)) qHash qRaw := by
  have firstGame : (chainsOf (fun _ => true) setup codec route client >>= fun result => decision (chainView result)) =
      gameOf setup codec route client decision budget 0 := by
    unfold gameOf
    rw [hybridModes_zero, allReal_decision_of]
  have lastGame : (ctxRunOf (fun _ => .replay) id setup codec route client >>= fun result =>
      decision (ctxView result)) = gameOf setup codec route client decision budget (hops n budget) := by
    unfold gameOf
    rw [hybrid_last_of setup codec route budget client records]
  rw [firstGame, lastGame]
  have telescope := PqxdhComposition.finiteHybridBound_of_hop_bounds
    (gameOf setup codec route client decision budget) (hops n budget)
    (fun cut => (gameOf setup codec route client decision budget cut).boolDistAdvantage
      (gameOf setup codec route client decision budget (cut + 1))) (fun _ _ => le_refl _)
  calc ENNReal.ofReal ((gameOf setup codec route client decision budget 0).boolDistAdvantage
        (gameOf setup codec route client decision budget (hops n budget)))
      ≤ ENNReal.ofReal (∑ cut ∈ Finset.range (hops n budget),
          (gameOf setup codec route client decision budget cut).boolDistAdvantage
            (gameOf setup codec route client decision budget (cut + 1))) :=
        ENNReal.ofReal_le_ofReal telescope
    _ = ∑ cut ∈ Finset.range (hops n budget), ENNReal.ofReal
          ((gameOf setup codec route client decision budget cut).boolDistAdvantage
            (gameOf setup codec route client decision budget (cut + 1))) :=
        ENNReal.ofReal_sum_of_nonneg (fun _ _ => abs_nonneg _)
    _ = ∑ step : Fin (hops n budget), ENNReal.ofReal
          ((gameOf setup codec route client decision budget step.val).boolDistAdvantage
            (gameOf setup codec route client decision budget (step.val + 1))) :=
        (Fin.sum_univ_eq_sum_range (fun cut => ENNReal.ofReal
          ((gameOf setup codec route client decision budget cut).boolDistAdvantage
            (gameOf setup codec route client decision budget (cut + 1)))) _).symm
    _ ≤ _ := Finset.sum_le_sum (fun step _ => by
          obtain ⟨qSeal, hashBound, sealBound, small, rawBound⟩ := stepBounds step
          exact hop_bound_of setup codec route fallback budget client records decision step qHash qSeal qRaw hashBound
            sealBound rawBound small)

end Hops

/-! ### Bills for an arbitrary World client -/

open PqxdhRecordLiftCtxProtocolBounds (BudgetKind categoryCost)
open PqxdhRecordLiftCtxProgramBounds (operationBill)
open PqxdhRecordLiftCtxProtocol (Bare)

/-- A World client within a World-level bill compiles to a service program within the same bill in that CTX ledger. -/
theorem schedule_categories (kind : BudgetKind) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (client : OracleComp (WorldSpec n) (Outcome E X)) (bill : Nat)
    (world : Weighted (PqxdhRecordLiftCtxBills.worldBill kind) client bill) :
    Weighted (categoryCost kind) (schedule codec.frameRead route client initialControl) bill :=
  PqxdhRecordLiftCtxProgramBounds.weighted_run (PqxdhRecordLiftCtxBills.worldBill kind) (categoryCost kind) _ _ _ _
    world (fun query control => PqxdhRecordLiftCtxBills.handler_categories kind codec.frameRead route query control)

/-- Every compiled World client seals each target coordinate at most once. -/
theorem schedule_target_seal (target : Label n) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (client : OracleComp (WorldSpec n) (Outcome E X)) :
    Weighted (PqxdhRecordLiftCtxBills.targetSeal target) (schedule codec.frameRead route client initialControl) 1 := by
  simpa using PqxdhRecordLiftCtxBills.fresh_target_seal target _ []
    (PqxdhRecordLiftProtocolHistory.initial_schedule_fresh codec.frameRead route client)

/-- A link client of an arbitrary World client is bounded in one category by the compiled client's bill under the step reduction's per-service cost, plus the decision's coins at their unit. -/
theorem link_route_of (target : Label n) (modes : Label n → KeyMode) (setup : Setup baseSpec KemSK)
    (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (client : OracleComp (WorldSpec n) (Outcome E X)) (decision : View n E X → ProbComp Bool)
    (predicate : PqxdhRecordLiftCtxModes.Spec.Domain → Prop) [DecidablePred predicate]
    (cost : PqxdhRecordLiftProtocol.Service n → Nat) (programBound decisionCost decisionUnit : Nat)
    (step : ∀ query state, ((reduction target modes setup codec query).run state).IsQueryBoundP predicate (cost query))
    (program : Weighted cost (schedule codec.frameRead route client initialControl) programBound)
    (coins : ∀ view, (decision view).IsTotalQueryBound decisionCost)
    (coinStep : ∀ coin, predicate (.inr (publicCall (RawCtxUniversalDecoder.decoder codec.frameRead)
      (.inl (.inl coin)))) → 0 < decisionUnit) :
    (linkClientOf target modes setup codec route client decision).IsQueryBoundP predicate
      (programBound + decisionCost * decisionUnit) :=
  isQueryBoundP_bind (PqxdhRecordLiftCtxBills.run_bound (reduction target modes setup codec) predicate cost step _
    programBound program _)
    (fun _ _ => PqxdhRecordLiftCtxBills.coinForward_route _ predicate _ decisionCost decisionUnit (coins _) coinStep)

/-- The step clients of an arbitrary World client whose compiled program stays within `bill` in every CTX ledger respect the uniform (with 64 per private replay-cache fill), shared-hash, seal and raw caps built from that bill. -/
theorem step_bills_of (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (client : OracleComp (WorldSpec n) (Outcome E X))
    (bill : BudgetKind → Nat)
    (program : ∀ kind, Weighted (categoryCost kind) (schedule codec.frameRead route client initialControl) (bill kind))
    (decision : View n E X → ProbComp Bool) (cost : Nat) (coins : ∀ view, (decision view).IsTotalQueryBound cost)
    (budget : Budget) (step : Fin (hops n budget)) :
    (∃ qUniform qPrivate, qUniform + 64 * qPrivate ≤ bill .uniform + cost + 64 * bill .hash ∧
      (stepClientOf setup codec route client decision budget step).IsQueryBoundP UniformRoute qUniform ∧
      (stepClientOf setup codec route client decision budget step).IsQueryBoundP PrivateRoute qPrivate) ∧
    (stepClientOf setup codec route client decision budget step).IsQueryBoundP HashRoute (bill .hash) ∧
    (stepClientOf setup codec route client decision budget step).IsQueryBoundP (TargetClass SourceSeal) 1 ∧
    (stepClientOf setup codec route client decision budget step).IsQueryBoundP (TargetClass IsRawQuery) (bill .raw) := by
  let target := PqxdhRecordLiftChainOrder.entryAt (positions := positions budget) step
  let modes : Label n → KeyMode := hybridModes (positions budget) step.val
  have uniform := link_route_of target modes setup codec route client decision UniformRoute _ _ cost 1
    (PqxdhRecordLiftCtxBills.reduction_uniform target modes setup codec) (program .uniform) coins
    (fun _ _ => Nat.one_pos)
  have privateFill := link_route_of target modes setup codec route client decision PrivateRoute _ _ cost 0
    (PqxdhRecordLiftCtxBills.reduction_private target modes setup codec) (program .hash) coins
    (fun _ hit => by simp [PrivateRoute, publicCall, AdaptiveCtxSharedReplayBounds.ModePrivate] at hit)
  have hash := link_route_of target modes setup codec route client decision HashRoute _ _ cost 0
    (PqxdhRecordLiftCtxBills.reduction_hash target modes setup codec) (program .hash) coins
    (fun _ hit => by simp [HashRoute, publicCall, AdaptiveCtxSharedReplayBounds.ModeHash,
      AdaptiveCtxQueryBounds.SourceWork, AdaptiveCtxQueryBounds.SourceUniform] at hit)
  have sealing := link_route_of target modes setup codec route client decision (TargetClass SourceSeal) _ _ cost 0
    (PqxdhRecordLiftCtxBills.reduction_seal target modes setup codec) (schedule_target_seal target codec route client)
    coins (fun _ hit => by simp [TargetClass] at hit)
  have raw := link_route_of target modes setup codec route client decision (TargetClass IsRawQuery) _ _ cost 0
    (PqxdhRecordLiftCtxBills.reduction_raw target modes setup codec) (program .raw) coins
    (fun _ hit => by simp [TargetClass] at hit)
  simp only [Nat.mul_one, Nat.mul_zero, Nat.add_zero] at uniform privateFill hash sealing raw
  exact ⟨⟨_, _, le_refl _, uniform, privateFill⟩, hash, sealing, raw⟩

/-! ### The later program's CTX bills and later `ctx_lift`, integrity half -/

open PqxdhRecordLiftLaterTargets
open PqxdhDeploymentLater (PostSpec PostBudget)

/-- The program-level bill of one CTX ledger for the two-phase program: the run-phase bill `PqxdhRecordLiftCtxBills.programBill` plus the post phase's coin, hash and administrative effects (`PqxdhRecordLiftLater.postCost`) at their per-effect bill. -/
def laterCtxProgramBill (kind : BudgetKind) (input : LaterBillInput) : Nat :=
  PqxdhRecordLiftCtxBills.programBill kind input.base +
    (PqxdhRecordLiftCtxBills.effectBill kind .coin * PqxdhRecordLiftLater.postCost input.base.allowance input.post .coin +
      PqxdhRecordLiftCtxBills.effectBill kind .hash * PqxdhRecordLiftLater.postCost input.base.allowance input.post .hash +
      PqxdhRecordLiftCtxBills.effectBill kind .administrative *
        PqxdhRecordLiftLater.postCost input.base.allowance input.post .administrative)

/-- The two-phase World program stays within `laterCtxProgramBill` in every CTX ledger, for every environment within its `Frame`, every run-phase adversary within its budget and every post adversary within its post budget. -/
theorem later_world_categories (kind : BudgetKind) {Out R : Type} (env : Environment n E) (startup : Nat)
    (allowance : Fin 14 → EffectKind → Nat) (framed : Frame env startup allowance) (crypto : Pqxdh.Crypto)
    (codec : Codec Reader Response) (serverKid : Std.U64) (bounds : FreshBounds) (mode : Mode) (budget : Budget)
    (post : PostBudget) (reveal : E → R) (first : OracleComp (ModeSpec mode) X) (second : X → R → OracleComp PostSpec Out)
    (respects : budget.Respects first) (postRespects : ∀ output disclosed, post.Respects (second output disclosed))
    (cost : Nat) :
    Weighted (PqxdhRecordLiftCtxBills.worldBill kind)
      (PqxdhRecordLiftLater.program env crypto codec serverKid bounds mode reveal first second)
      (laterCtxProgramBill kind ⟨⟨budget, startup, allowance, bounds, n, cost⟩, post⟩) := by
  have effect := fun effect : EffectKind => PqxdhRecordLiftCtxProgramBounds.weighted_indicator
    (PqxdhRecordLiftBudget.WorldEffect effect) (PqxdhRecordLiftCtxBills.effectBill kind effect) _ _
    (PqxdhRecordLiftLater.program_effect_bound env startup allowance framed crypto codec serverKid bounds mode
      ⟨budget, 0⟩ post reveal first second respects postRespects effect)
  have record := fun record : PqxdhRecordLiftBudget.RecordKind => PqxdhRecordLiftCtxProgramBounds.weighted_indicator
    (PqxdhRecordLiftBudget.WorldRecord record) (operationBill kind record) _ _
    (PqxdhRecordLiftLater.program_record_bound env crypto codec serverKid bounds mode budget reveal first second
      respects record)
  have joint := PqxdhRecordLiftCtxProgramBounds.weighted_add _ _ _ _ _
    (PqxdhRecordLiftCtxProgramBounds.weighted_add _ _ _ _ _ (PqxdhRecordLiftCtxProgramBounds.weighted_add _ _ _ _ _
      (PqxdhRecordLiftCtxProgramBounds.weighted_add _ _ _ _ _ (effect .coin) (effect .hash)) (effect .administrative))
      (record .send)) (record .raw)
  rw [PqxdhRecordLiftCtxBills.worldBill_split]
  refine PqxdhRecordLiftCtxProgramBounds.weighted_mono _ _ _ _ joint (le_of_eq ?_)
  simp only [laterCtxProgramBill, PqxdhRecordLiftCtxBills.programBill, PqxdhRecordLiftCtxBills.effectTotal,
    PqxdhRecordLiftBudget.recordBudget, Nat.mul_add]
  omega

/-- The explicit later CTX bills: the two-phase program's coins (with 64 per possible private replay-cache fill) plus the decision's coins, its shared hashes, one seal and the raw receives. -/
def laterCtxBills : LaterCtxBills where
  uniform input := laterCtxProgramBill .uniform input + input.base.decision + 64 * laterCtxProgramBill .hash input
  hash input := laterCtxProgramBill .hash input
  seals _ := 1
  raw input := laterCtxProgramBill .raw input

/-- **The hash route with the post phase.** The later hash bill is the run-phase shared-hash total plus the post phase's shared-hash work (`qHash₂`: the post BLAKE2b requests and the environment's class-six hash allowance per post HMAC request). -/
theorem laterCtx_hash_bill (input : LaterBillInput) : laterCtxBills.hash input = laterSharedHashTotal input := by
  have run := PqxdhRecordLiftCtxBills.hash_bill input.base
  simp only [PqxdhRecordLiftCtxBills.ctxBills] at run
  simp only [laterCtxBills, laterCtxProgramBill, laterSharedHashTotal, postHash, run, PqxdhRecordLiftCtxBills.effectBill]
  omega

/-- The later raw bill is the run-phase raw bill: the post phase makes no raw attempt. -/
theorem laterCtx_raw_bill (input : LaterBillInput) :
    laterCtxBills.raw input = PqxdhRecordLiftCtxBills.ctxBills.raw input.base := by
  simp only [laterCtxBills, laterCtxProgramBill, PqxdhRecordLiftCtxBills.ctxBills, PqxdhRecordLiftCtxBills.effectBill]
  omega

section Final
variable (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
  (serverKid : Std.U64) (bounds : FreshBounds)

/-- The explicit later CTX reduction family: hop `step`'s ordinary one-key CTX adversary is the step client of the compiled two-phase program, with the known-key work run inside. -/
noncomputable def laterCtxReduction : LaterCtxReduction n :=
  fun env mode reveal first second decision budget _ step =>
    PqxdhRecordLiftCtxModes.decisionClient setup.source.crypto
      (stepClientOf setup codec route
        (PqxdhRecordLiftLater.program env setup.source.crypto codec serverKid bounds mode reveal first second)
        decision budget step)

/-- Later `ctx_lift`, integrity half, Boolean form, with zero refusal term, the explicit reductions and the explicit bills. -/
theorem later_ctx_auth_lift_bool (n : Nat) (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery) :
    LaterCtxAuthLiftBool setup codec route serverKid bounds n fallback
      (laterCtxReduction setup codec route serverKid bounds) laterCtxBills laterNoTerm := by
  intro E X Out R env startup allowance framed mode reveal first second budget post respects postRespects decision cost
    coins
  have program := fun kind => schedule_categories kind codec route _ _
    (later_world_categories kind env startup allowance framed setup.source.crypto codec serverKid bounds mode budget post
      reveal first second respects postRespects cost)
  have stepBills := fun step : Fin (hops n budget) => step_bills_of setup codec route _ _ program decision cost coins
    budget step
  refine ⟨?_, fun step => ?_⟩
  · have bound := ctx_auth_loss_of setup codec route fallback budget
      (PqxdhRecordLiftLater.program env setup.source.crypto codec serverKid bounds mode reveal first second)
      (later_recordBounded env setup.source.crypto codec serverKid bounds mode budget reveal first second respects)
      decision _ _ (fun step => ⟨1, (stepBills step).2.1, (stepBills step).2.2.1, by norm_num,
        (stepBills step).2.2.2⟩)
    simpa only [laterNoTerm, add_zero, laterIdealChains, laterChains, laterIdealAuth, laterCtxRun, laterCtxBills,
      laterCtxReduction] using bound
  · obtain ⟨⟨qUniform, qPrivate, cap, uniformBound, privateBound⟩, hashBound, sealBound, rawBound⟩ := stepBills step
    have budgets := PqxdhRecordLiftCtxModeBounds.decision_budgets setup.source.crypto _ qUniform qPrivate _ _ _
      uniformBound privateBound hashBound sealBound rawBound
    exact ⟨budgets.1.mono cap, budgets.2.1, budgets.2.2.1, budgets.2.2.2⟩

/-- **Later `ctx_lift`, integrity half (R6, item 4), delivered.** `LaterCtxAuthLiftTarget` (Boolean and event forms, zero refusal term) for the explicit reductions `laterCtxReduction` and bills `laterCtxBills`, whose hash bill carries the post phase's shared-hash work (`laterCtx_hash_bill`). -/
theorem later_ctx_auth_lift (n : Nat) (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery) :
    LaterCtxAuthLiftTarget setup codec route serverKid bounds n fallback
      (laterCtxReduction setup codec route serverKid bounds) laterCtxBills :=
  laterCtxAuthLiftStatement_of_bool setup codec route serverKid bounds n fallback _ laterCtxBills laterNoTerm
    (later_ctx_auth_lift_bool setup codec route serverKid bounds n fallback)

end Final

end BeaconcryptCore.Computational.PqxdhRecordLiftLaterCtx

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftLaterCtx.allReal_bare_of' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftLaterCtx.allReal_bare_of

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftLaterCtx.allReal_decision_of' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftLaterCtx.allReal_decision_of

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftLaterCtx.world_lookups_of' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftLaterCtx.world_lookups_of

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftLaterCtx.schedule_lookups' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftLaterCtx.schedule_lookups

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftLaterCtx.schedule_map' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftLaterCtx.schedule_map

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftLaterCtx.schedule_congr' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftLaterCtx.schedule_congr

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftLaterCtx.ctxRunWithOf_tableKey' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftLaterCtx.ctxRunWithOf_tableKey

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftLaterCtx.ctxRunWithOf_congr' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftLaterCtx.ctxRunWithOf_congr

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftLaterCtx.hybrid_last_of' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftLaterCtx.hybrid_last_of

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftLaterCtx.selected_table_of' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftLaterCtx.selected_table_of

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftLaterCtx.key_cut_of' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftLaterCtx.key_cut_of

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftLaterCtx.link_of' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftLaterCtx.link_of

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftLaterCtx.game_real_of' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftLaterCtx.game_real_of

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftLaterCtx.game_replay_of' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftLaterCtx.game_replay_of

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftLaterCtx.hop_bound_of' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftLaterCtx.hop_bound_of

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftLaterCtx.ctx_auth_loss_of' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftLaterCtx.ctx_auth_loss_of

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftLaterCtx.schedule_categories' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftLaterCtx.schedule_categories

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftLaterCtx.schedule_target_seal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftLaterCtx.schedule_target_seal

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftLaterCtx.link_route_of' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftLaterCtx.link_route_of

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftLaterCtx.step_bills_of' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftLaterCtx.step_bills_of

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftLaterCtx.later_world_categories' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftLaterCtx.later_world_categories

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftLaterCtx.laterCtx_hash_bill' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftLaterCtx.laterCtx_hash_bill

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftLaterCtx.laterCtx_raw_bill' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftLaterCtx.laterCtx_raw_bill

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftLaterCtx.later_ctx_auth_lift_bool' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftLaterCtx.later_ctx_auth_lift_bool

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftLaterCtx.later_ctx_auth_lift' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftLaterCtx.later_ctx_auth_lift
