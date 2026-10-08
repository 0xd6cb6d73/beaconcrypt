-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRecordLiftCtx
import BeaconcryptCore.Computational.PqxdhRecordLiftCtxProtocolBounds

/-!
# Record-lift CTX bills and the integrity half of `ctx_lift` (items 4 and 5, stage S4, X4)

**Statement.** `ctxAuthLiftTarget`: with the explicit reduction family `PqxdhRecordLiftCtx.ctxReduction` and the explicit bills `ctxBills`, the zero-refusal integrity target `PqxdhRecordLiftIdeal.CtxAuthLiftTarget` holds in both forms; `ctxAuthLiftStatement` gives `CtxAuthLiftStatement` for every refusal term. The proof discharges the premise `StepBilled ctxBills` of `PqxdhRecordLiftCtx.ctxAuthLiftTarget_of_billed` (`stepBilled`).

**Program bills.** In each ledger of `PqxdhRecordLiftCtxProtocolBounds.categoryCost` (uniform: 64 per seed allocation, 76 per lookup, 1 per coin; hash: one per public hash, hidden opening or seal and caller-known send or receive; raw: one per hidden opening), every World request stays within its bill (`handler_categories`, through `PqxdhRecordLiftCtxProgramBounds.kernel_send` and `kernel_receive`), and the World program within `programBill` (`world_categories`, from `PqxdhRecordLiftBudget.program_bound` for coins, hashes and administrative capabilities and `program_record_bound` for sends and raw receives), so the compiled program does too (`program_categories`). The target coordinate is sealed at most once (`program_target_seal`, from `PqxdhRecordLiftProtocolHistory.program_fresh`), so the seal cap is one, below `2^96`.

**Step bills.** Per service, the step reduction of `PqxdhRecordLiftCtxLink` forwards coins and hashes one request each (`coinForward_route`, `hashForward_route`), draws at most 64 coins for an allocation (`allocate_total`) and 76 for a lookup (`bareLookup_total`), and routes at most one request for a hidden opening or seal (`opening_route`, `sealing_route`) and at most one hash for a caller-known send or receive (`PqxdhRecordLiftCtxProtocolBounds.knownRom_total`); `reduction_step` and its five instances give the uniform, hash, private replay-cache, target-seal and target-raw categories of `PqxdhRecordLiftCtxModeBounds`. `link_route` adds the decision's own coins. `ctxBills` charges the program's coins, the decision's coins and 64 coins per possible private replay-cache fill, the program's shared hashes (exactly `PqxdhRecordLiftIdeal.sharedHashTotal`, `hash_bill`), one seal and the raw receives.

**Scope.** No assumption or contract. The privacy half (`CtxPrivLiftStatement`) is a later stage; see `doc/impl/record-lift-ctx-hybrid.md`.
-/

open OracleComp OracleSpec ENNReal CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false

namespace BeaconcryptCore.Computational.PqxdhRecordLiftCtxBills
open PqxdhRecordLiftInterface PqxdhRecordLiftIdeal PqxdhRecordLiftCtxHybrid PqxdhRecordLiftCtxLink
open PqxdhRecordLiftCtxAvailability PqxdhRecordLiftCtx
open PqxdhDeploymentInterface (Mode ModeSpec FreshBounds Budget)
open PqxdhServerAuthExperiment (Setup Codec)
open PqxdhRecordLiftWorldCompiler (Label Owner)
open PqxdhRecordLiftCtxProtocolBounds (BudgetKind categoryCost)
open PqxdhRecordLiftCtxProgramBounds (Weighted weighted_bind weighted_mono weighted_indicator weighted_add
  weighted_run operationBill)
open CtxRomAuth AdaptiveCtxReceive
variable {n : Nat} {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response E X : Type}

/-! ### Weighted bounds -/

/-- A weighted bound survives a pointwise smaller cost. -/
theorem weighted_cost_mono {κ : Type} {spec : OracleSpec κ} {Result : Type} (cost larger : spec.Domain → Nat)
    (smaller : ∀ query, cost query ≤ larger query) (client : OracleComp spec Result) (bound : Nat)
    (bounded : Weighted larger client bound) : Weighted cost client bound := by
  induction client using OracleComp.inductionOn generalizing bound with
  | pure value => trivial
  | query_bind query next ih =>
      rw [Weighted, isQueryBound_query_bind_iff] at bounded ⊢
      refine ⟨(smaller query).trans bounded.1, fun reply => ?_⟩
      exact weighted_mono _ _ _ _ (ih reply _ (bounded.2 reply)) (by have := smaller query; omega)

/-- A service-level weighted bound runs through every stateful interpretation whose step is bounded by the step's cost. -/
theorem run_bound {κ τ : Type} {spec : OracleSpec κ} {target : OracleSpec τ} {State Result : Type}
    (impl : QueryImpl spec (StateT State (OracleComp target))) (predicate : τ → Prop) [DecidablePred predicate]
    (cost : spec.Domain → Nat)
    (step : ∀ query state, ((impl query).run state).IsQueryBoundP predicate (cost query))
    (client : OracleComp spec Result) (bound : Nat) (bounded : Weighted cost client bound) (state : State) :
    ((simulateQ impl client).run state).IsQueryBoundP predicate bound := by
  induction client using OracleComp.inductionOn generalizing state bound with
  | pure value => trivial
  | query_bind query next ih =>
      rw [Weighted, isQueryBound_query_bind_iff] at bounded
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
      exact (isQueryBoundP_bind (step query state)
        (fun result _ => ih result.1 _ (bounded.2 result.1) result.2)).mono (by omega)

/-! ### Service bills of the compiled program -/

/-- The bill of one restricted effect in one CTX ledger: a coin, a public hash, or the seed allocation (64 coins) an administrative capability may make. -/
def effectBill : BudgetKind → EffectKind → Nat
  | .uniform, .coin => 1
  | .uniform, .administrative => 64
  | .hash, .hash => 1
  | _, _ => 0

/-- The bill of one World request in one CTX ledger. -/
def worldBill (kind : BudgetKind) : (WorldSpec n).Domain → Nat
  | .inl _ => 0
  | .inr (.inl effect) => effectBill kind (effectKind effect)
  | .inr (.inr record) => operationBill kind (PqxdhRecordLiftBudget.recordKind record)

/-- The bill of one owner request: a send or a raw receive. -/
def ownerBill (kind : BudgetKind) (query : RawCtxMixedOwner.SourceSpec.Domain) : Nat :=
  if query.isLeft then operationBill kind .send else operationBill kind .raw

theorem query_categories (kind : BudgetKind) (query : PqxdhRecordLiftProtocol.Service n) :
    Weighted (categoryCost kind) ((liftM ((PqxdhRecordLiftProtocol.ServiceSpec n).query query) :
      OracleComp (PqxdhRecordLiftProtocol.ServiceSpec n) _)) (categoryCost kind query) := by
  simp [Weighted]

theorem publish_cost (kind : BudgetKind) (tag : PqxdhDeploymentInterface.FrameTag) :
    categoryCost kind (.publish tag : PqxdhRecordLiftProtocol.Service n) = 0 := by
  cases kind <;> rfl

theorem charge_cost (kind : BudgetKind) (effect : EffectKind) :
    categoryCost kind (.charge effect : PqxdhRecordLiftProtocol.Service n) = 0 := by
  cases kind <;> rfl

theorem ownerRun_categories (kind : BudgetKind) (tag : PqxdhDeploymentInterface.FrameTag) (sender : Std.U64)
    (decode : RawCtxReceive.FrameDecoder) (query : RawCtxMixedOwner.SourceSpec.Domain) (owner : Owner n) :
    Weighted (categoryCost kind) (PqxdhRecordLiftProtocol.ownerRun tag sender decode query owner)
      (ownerBill kind query) := by
  have step : Weighted (categoryCost kind) (PqxdhRecordLiftProtocol.ownerStep sender decode query owner)
      (ownerBill kind query) := by
    cases query with
    | inl plaintext =>
        simp only [PqxdhRecordLiftProtocol.ownerStep, PqxdhRecordLiftProtocol.ownerSend, ownerBill]
        split
        · trivial
        · exact weighted_mono _ _ _ _ (weighted_bind _ _ _ _ 0
            (PqxdhRecordLiftCtxProgramBounds.kernel_send kind _ _) (fun _ => trivial)) (by simp)
    | inr raw =>
        simp only [PqxdhRecordLiftProtocol.ownerStep, PqxdhRecordLiftProtocol.ownerReceive, ownerBill]
        split
        · trivial
        · split
          · trivial
          · split
            · exact weighted_mono _ _ _ _ (weighted_bind _ _ _ _ 0
                (PqxdhRecordLiftCtxProgramBounds.kernel_receive kind _ _ _) (fun _ => trivial)) (by simp)
            · trivial
  exact weighted_mono _ _ _ _ (weighted_bind _ _ _ _ 0 step (fun _ =>
    weighted_mono _ _ _ _ (weighted_bind _ _ _ 0 0 (by
      have single := query_categories kind (.publish tag : PqxdhRecordLiftProtocol.Service n)
      rwa [publish_cost] at single) (fun _ => trivial)) (by omega))) (by omega)

theorem resolve_categories (kind : BudgetKind) (role : Role) (ref : PqxdhRecordLiftInterface.KernelRef n) :
    Weighted (categoryCost kind) (PqxdhRecordLiftProtocol.resolve role ref) (effectBill kind .administrative) := by
  cases ref <;> cases kind <;> simp [PqxdhRecordLiftProtocol.resolve, Weighted, categoryCost, effectBill]

theorem capability_categories (kind : BudgetKind) (query : (CapabilitySpec n).Domain)
    (control : PqxdhRecordLiftProtocol.Control n) :
    Weighted (categoryCost kind) ((PqxdhRecordLiftProtocol.capability query).run control)
      (effectBill kind (effectKind (n := n) (.inr query))) := by
  cases query with
  | installServer keyId identity ref =>
      change Weighted (categoryCost kind) (PqxdhRecordLiftProtocol.installServer keyId identity ref control) _
      unfold PqxdhRecordLiftProtocol.installServer
      split
      · trivial
      · split
        · exact weighted_mono _ _ _ _ (weighted_bind _ _ _ _ 0 (resolve_categories kind _ _) (fun _ => trivial))
            (by simp [effectKind])
        · trivial
  | installBeacon owner shell ref =>
      change Weighted (categoryCost kind) (PqxdhRecordLiftProtocol.installBeacon owner shell ref control) _
      unfold PqxdhRecordLiftProtocol.installBeacon
      split
      · exact weighted_mono _ _ _ _ (weighted_bind _ _ _ _ 0 (resolve_categories kind _ _) (fun _ => trivial))
          (by simp [effectKind])
      · trivial
  | advanceOwner owner phase =>
      change Weighted (categoryCost kind) (PqxdhRecordLiftProtocol.capability (.advanceOwner owner phase) control) _
      simp only [PqxdhRecordLiftProtocol.capability]
      split
      · split <;> trivial
      · trivial
  | hash bytes =>
      cases kind <;> simp [PqxdhRecordLiftProtocol.capability, Weighted, categoryCost, effectBill, effectKind,
        StateT.run_lift]
  | _ => trivial

theorem effects_categories (kind : BudgetKind) (query : (EnvEffects n).Domain)
    (control : PqxdhRecordLiftProtocol.Control n) :
    Weighted (categoryCost kind) ((PqxdhRecordLiftProtocol.effects query).run control)
      (effectBill kind (effectKind query)) := by
  rcases query with coin | request
  · cases kind <;> simp [PqxdhRecordLiftProtocol.effects, Weighted, categoryCost, effectBill, effectKind,
      StateT.run_bind, StateT.run_lift]
  · simp only [PqxdhRecordLiftProtocol.effects, StateT.run_bind, StateT.run_lift, bind_assoc, pure_bind]
    have single := query_categories kind (.charge (effectKind (.inr request)) : PqxdhRecordLiftProtocol.Service n)
    rw [charge_cost] at single
    simpa only [Nat.zero_add] using weighted_bind _ _ _ 0 _ single (fun _ => capability_categories kind request control)

theorem serverStep_categories (kind : BudgetKind) (decode : RawCtxReceive.FrameDecoder)
    (route : RawCtxServerRouting.SenderDecoder) (query : RawCtxServerMixed.SourceSpec.Domain)
    (control : PqxdhRecordLiftProtocol.Control n) :
    Weighted (categoryCost kind) ((PqxdhRecordLiftProtocol.serverStep decode route query).run control)
      (if query.isLeft then operationBill kind .send else operationBill kind .raw) := by
  change Weighted (categoryCost kind) (PqxdhRecordLiftProtocol.serverStep decode route query control) _
  unfold PqxdhRecordLiftProtocol.serverStep
  cases existing : control.server with
  | none => cases query <;> trivial
  | some server =>
      dsimp only
      rcases query with ⟨plaintext, keyId⟩ | raw
      · dsimp only
        cases present : server.peers keyId with
        | none => trivial
        | some peer =>
            exact weighted_bind _ _ _ _ 0 (ownerRun_categories kind _ _ _ (.inl plaintext) _) (fun _ => trivial)
      · dsimp only
        cases routed : route raw with
        | none => trivial
        | some keyId =>
            dsimp only
            cases present : server.peers keyId with
            | none => trivial
            | some peer =>
                exact weighted_bind _ _ _ _ 0 (ownerRun_categories kind _ _ _ (.inr raw) _) (fun _ => trivial)

theorem beaconStep_categories (kind : BudgetKind) (decode : RawCtxReceive.FrameDecoder) (owner : Nat)
    (query : RawCtxMixedOwner.SourceSpec.Domain) (control : PqxdhRecordLiftProtocol.Control n) :
    Weighted (categoryCost kind) ((PqxdhRecordLiftProtocol.beaconStep decode owner query).run control)
      (ownerBill kind query) := by
  change Weighted (categoryCost kind) (PqxdhRecordLiftProtocol.beaconStep decode owner query control) _
  unfold PqxdhRecordLiftProtocol.beaconStep
  cases selected : control.owners[owner]? with
  | none => trivial
  | some phase =>
      cases phase with
      | inactive phase => cases query <;> trivial
      | established shell kernel =>
          exact weighted_mono _ _ _ _ (weighted_bind _ _ _ _ 0 (ownerRun_categories kind _ _ _ query _)
            (fun _ => trivial)) (by omega)

/-- One World request stays within its bill in every CTX ledger. -/
theorem handler_categories (kind : BudgetKind) (decode : RawCtxReceive.FrameDecoder)
    (route : RawCtxServerRouting.SenderDecoder) (query : (WorldSpec n).Domain)
    (control : PqxdhRecordLiftProtocol.Control n) :
    Weighted (categoryCost kind) ((PqxdhRecordLiftProtocol.handler decode route query).run control)
      (worldBill kind query) := by
  rcases query with created | query
  · change Weighted (categoryCost kind) (PqxdhRecordLiftProtocol.initializeServer created control) _
    unfold PqxdhRecordLiftProtocol.initializeServer
    split <;> trivial
  · rcases query with effect | record
    · exact effects_categories kind effect control
    · rcases record with (send | raw) | ⟨owner, plaintext | raw⟩
      · exact serverStep_categories kind decode route (.inl send) control
      · exact serverStep_categories kind decode route (.inr raw) control
      · exact beaconStep_categories kind decode owner (.inl plaintext) control
      · exact beaconStep_categories kind decode owner (.inr raw) control

/-- The program-level count of one kind of restricted effect: startup coins, the adversary's direct work and the environment's allowance over the outer command budget. -/
def effectTotal (input : BillInput) (effect : EffectKind) : Nat :=
  PqxdhRecordLiftBudget.startupCost input.startup effect +
    (PqxdhRecordLiftBudget.directCost input.budget input.fresh effect +
      Caps.envTotal ⟨input.budget, 0⟩ input.allowance effect)

/-- The program-level bill of one CTX ledger. -/
def programBill (kind : BudgetKind) (input : BillInput) : Nat :=
  effectBill kind .coin * effectTotal input .coin + effectBill kind .hash * effectTotal input .hash +
    effectBill kind .administrative * effectTotal input .administrative +
    operationBill kind .send * input.budget.sends + operationBill kind .raw * input.budget.receives

theorem worldBill_split (kind : BudgetKind) :
    (worldBill kind : (WorldSpec n).Domain → Nat) = fun query =>
      (if PqxdhRecordLiftBudget.WorldEffect .coin query then effectBill kind .coin else 0) +
      (if PqxdhRecordLiftBudget.WorldEffect .hash query then effectBill kind .hash else 0) +
      (if PqxdhRecordLiftBudget.WorldEffect .administrative query then effectBill kind .administrative else 0) +
      (if PqxdhRecordLiftBudget.WorldRecord .send query then operationBill kind .send else 0) +
      (if PqxdhRecordLiftBudget.WorldRecord .raw query then operationBill kind .raw else 0) := by
  funext query
  rcases query with _ | effect | record
  · simp [worldBill, PqxdhRecordLiftBudget.WorldEffect, PqxdhRecordLiftBudget.WorldRecord]
  · cases effectEq : effectKind effect <;>
      simp [worldBill, PqxdhRecordLiftBudget.WorldEffect, PqxdhRecordLiftBudget.WorldRecord, effectEq]
  · cases recordEq : PqxdhRecordLiftBudget.recordKind record <;>
      simp [worldBill, PqxdhRecordLiftBudget.WorldEffect, PqxdhRecordLiftBudget.WorldRecord, recordEq]

/-- The World program stays within the program-level bill of every CTX ledger. -/
theorem world_categories (kind : BudgetKind) {E X Reader Response : Type} (env : Environment n E) (startup : Nat)
    (allowance : Fin 14 → EffectKind → Nat) (framed : Frame env startup allowance) (crypto : Pqxdh.Crypto)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (serverKid : Std.U64) (bounds : FreshBounds)
    (mode : Mode) (budget : Budget) (adversary : OracleComp (ModeSpec mode) X) (respects : budget.Respects adversary)
    (cost : Nat) :
    Weighted (worldBill kind) (PqxdhRecordLiftInterface.program env crypto codec serverKid bounds mode adversary)
      (programBill kind ⟨budget, startup, allowance, bounds, n, cost⟩) := by
  have effect := fun effect : EffectKind => weighted_indicator (PqxdhRecordLiftBudget.WorldEffect effect)
    (effectBill kind effect) _ _ (PqxdhRecordLiftBudget.program_bound env startup allowance framed crypto codec
      serverKid bounds mode ⟨budget, 0⟩ adversary respects effect)
  have record := fun record : PqxdhRecordLiftBudget.RecordKind => weighted_indicator (PqxdhRecordLiftBudget.WorldRecord record)
    (operationBill kind record) _ _ (PqxdhRecordLiftBudget.program_record_bound env crypto codec serverKid bounds
      mode budget adversary respects record)
  have joint := weighted_add _ _ _ _ _ (weighted_add _ _ _ _ _ (weighted_add _ _ _ _ _
    (weighted_add _ _ _ _ _ (effect .coin) (effect .hash)) (effect .administrative)) (record .send)) (record .raw)
  rw [worldBill_split]
  simpa [programBill, effectTotal, PqxdhRecordLiftBudget.recordBudget] using joint

/-- The compiled protocol program stays within the program-level bill of every CTX ledger. -/
theorem program_categories (kind : BudgetKind) {E X Reader Response : Type} (env : Environment n E)
    (startup : Nat) (allowance : Fin 14 → EffectKind → Nat) (framed : Frame env startup allowance)
    (crypto : Pqxdh.Crypto) (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (serverKid : Std.U64) (bounds : FreshBounds) (mode : Mode)
    (budget : Budget) (adversary : OracleComp (ModeSpec mode) X) (respects : budget.Respects adversary)
    (cost : Nat) :
    Weighted (categoryCost kind) (PqxdhRecordLiftProtocol.program env crypto codec route serverKid bounds mode adversary)
      (programBill kind ⟨budget, startup, allowance, bounds, n, cost⟩) :=
  weighted_run (worldBill kind) (categoryCost kind) _ _ _ _
    (world_categories kind env startup allowance framed crypto codec serverKid bounds mode budget adversary
      respects cost)
    (fun query control => handler_categories kind codec.frameRead route query control)

/-! ### At most one seal at the target -/

/-- One unit per hidden seal at the target coordinate. -/
def targetSeal (target : Label n) : PqxdhRecordLiftProtocol.Service n → Nat
  | .sealing pending => if pending.material = target then 1 else 0
  | _ => 0

/-- Along a program whose seals are fresh against its seal history, the target is sealed at most once, and not at all once it is in the history. -/
theorem fresh_target_seal (target : Label n) {Result : Type}
    (client : OracleComp (PqxdhRecordLiftProtocol.ServiceSpec n) Result) (past : List (Label n))
    (fresh : (PqxdhRecordLiftProtocolHistory.annotated client past).AllQueriesSatisfy
      PqxdhRecordLiftProtocolHistory.Fresh) :
    Weighted (targetSeal target) client (if target ∈ past then 0 else 1) := by
  induction client using OracleComp.inductionOn generalizing past with
  | pure value => trivial
  | query_bind query next ih =>
      rw [PqxdhRecordLiftProtocolHistory.annotated_query_bind, allQueriesSatisfy_query_bind_iff] at fresh
      rw [Weighted, isQueryBound_query_bind_iff]
      cases query with
      | sealing pending =>
          by_cases same : pending.material = target
          · have absent : target ∉ past := same ▸ fresh.1
            have cost : targetSeal target (.sealing pending) = 1 := by simp [targetSeal, same]
            refine ⟨by rw [cost]; simp [absent], fun reply => ?_⟩
            have later := ih reply _ (fresh.2 reply)
            have inside : target ∈ past ++ PqxdhRecordLiftWorldProvenance.sealingCoordinates
                (.sealing pending : PqxdhRecordLiftProtocol.Service n) := by
              simp [PqxdhRecordLiftWorldProvenance.sealingCoordinates, same]
            rw [ite_eq_left inside] at later
            show Weighted (targetSeal target) (next reply) _
            rw [cost, ite_eq_right absent]
            exact later
          · have cost : targetSeal target (.sealing pending) = 0 := by simp [targetSeal, same]
            refine ⟨by rw [cost]; exact Nat.zero_le _, fun reply => ?_⟩
            have later := ih reply _ (fresh.2 reply)
            have member : target ∈ past ++ PqxdhRecordLiftWorldProvenance.sealingCoordinates
                (.sealing pending : PqxdhRecordLiftProtocol.Service n) ↔ target ∈ past := by
              simp only [PqxdhRecordLiftWorldProvenance.sealingCoordinates, List.mem_append, List.mem_singleton]
              exact ⟨fun found => found.elim id (fun equal => absurd equal.symm same), Or.inl⟩
            show Weighted (targetSeal target) (next reply) _
            rw [cost, Nat.sub_zero]
            simpa only [member] using later
      | _ =>
          refine ⟨Nat.zero_le _, fun reply => ?_⟩
          have later := ih reply _ (fresh.2 reply)
          show Weighted (targetSeal target) (next reply) _
          simpa only [PqxdhRecordLiftWorldProvenance.sealingCoordinates, List.append_nil, targetSeal,
            Nat.sub_zero] using later

/-- The compiled program seals the target at most once. -/
theorem program_target_seal (target : Label n) {E X Reader Response : Type} (env : Environment n E)
    (crypto : Pqxdh.Crypto) (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (serverKid : Std.U64) (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) :
    Weighted (targetSeal target) (PqxdhRecordLiftProtocol.program env crypto codec route serverKid bounds mode adversary)
      1 := by
  simpa using fresh_target_seal target _ []
    (PqxdhRecordLiftProtocolHistory.program_fresh env crypto codec route serverKid bounds mode adversary)

/-! ### The step reduction's requests per service -/

open PqxdhRecordLiftCtxModeBounds (UniformRoute PrivateRoute HashRoute TargetClass)
open PqxdhRecordLiftCtxProtocol (Bare)
open AdaptiveCtxQueryBounds (SourceUniform SourceHash SourceSeal)

/-- Forwarded coins issue one request per coin, each in a single category. -/
theorem coinForward_route {Result : Type} (decode : RawDecoder) (predicate : PqxdhRecordLiftCtxModes.Spec.Domain → Prop)
    [DecidablePred predicate] (work : ProbComp Result) (count step : Nat) (total : work.IsTotalQueryBound count)
    (each : ∀ coin, predicate (.inr (publicCall decode (.inl (.inl coin)))) → 0 < step) :
    (simulateQ (coinForward decode) work).IsQueryBoundP predicate (count * step) :=
  IsQueryBoundP.simulateQ_of_step_le_total total (fun coin => (isQueryBoundP_query_iff _ _ _).mpr (each coin))

/-- Forwarded public hashes issue one request per hash, each in a single category. -/
theorem hashForward_route {Result : Type} (decode : RawDecoder) (predicate : PqxdhRecordLiftCtxModes.Spec.Domain → Prop)
    [DecidablePred predicate] (work : OracleComp CtxRO Result) (count step : Nat) (total : work.IsTotalQueryBound count)
    (each : ∀ query, predicate (.inr (publicCall decode (.inl (.inr (.inl query))))) → 0 < step) :
    (simulateQ (hashForward decode) work).IsQueryBoundP predicate (count * step) :=
  IsQueryBoundP.simulateQ_of_step_le_total total (fun query => (isQueryBoundP_query_iff _ _ _).mpr (each query))

/-- A seed allocation draws at most 64 coins. -/
theorem allocate_total (slot : Slot n) (seeds : PqxdhRecordLiftLazyTable.State (PqxdhRecordLiftWorld.SeedSpec n)) :
    ((PqxdhRecordLiftLazyTable.impl slot).run seeds).IsTotalQueryBound 64 := by
  cases found : seeds.1 slot with
  | none =>
      rw [PqxdhRecordLiftLazyTable.run_miss slot seeds found]
      simp only [IsTotalQueryBound, isQueryBound_map_iff]
      exact PqxdhRecordLiftSeedCut.seed_bound
  | some seed =>
      rw [PqxdhRecordLiftLazyTable.run_hit slot seeds seed found]
      trivial

set_option maxRecDepth 2048 in
/-- An all-ideal bare lookup draws at most 76 coins. -/
theorem bareLookup_total (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (seeds : PqxdhRecordLiftChainTable.Seeds (Slot n))
    (coordinate : Label n) (table : PqxdhRecordLiftChainTable.Table (Slot n)) :
    ((PqxdhRecordLiftCtxOracle.bareLookup source seeds (fun _ => true) coordinate).run table).IsTotalQueryBound 76 := by
  change (PqxdhRecordLiftCtxOracle.bareLookup source seeds (fun _ => true) coordinate table).IsTotalQueryBound 76
  unfold PqxdhRecordLiftCtxOracle.bareLookup
  simp only [ite_true]
  split
  · trivial
  · have sampled : ($ᵗ PqxdhFullSecretInputKdf.FullOutput : ProbComp _).IsTotalQueryBound 76 :=
      CtxComputationalSecurity.uniformFixedBytes_isTotalQueryBound 76
    rw [bind_pure_comp]
    exact (isQueryBound_map_iff _ _ _ _ _).mpr sampled

/-- A hidden opening routes at most one raw request: to the challenger at the target, else to a known call. -/
theorem opening_route (target : Label n) (modes : Label n → KeyMode) (decode : RawDecoder)
    (table : PqxdhRecordLiftChainTable.Table (Slot n)) (seeds : PqxdhRecordLiftChainTable.Seeds (Slot n))
    (pending : PqxdhRecordLiftProtocol.Opening n) (predicate : PqxdhRecordLiftCtxModes.Spec.Domain → Prop)
    [DecidablePred predicate] (bound : Nat)
    (atTarget : ∀ request, IsRawQuery request → predicate (.inl request) → 0 < bound)
    (atOther : ∀ known : PqxdhRecordLiftCtxModes.KnownCall, IsRawQuery known.request → predicate (.inr known) → 0 < bound) :
    (simulateQ (routeKeyed target modes decode table) (hiddenOpening seeds table pending)).IsQueryBoundP
      predicate bound := by
  unfold hiddenOpening
  split
  · trivial
  · split
    · trivial
    · split
      · simp only [simulateQ_map, simulateQ_spec_query, isQueryBoundP_map_iff]
        unfold routeKeyed
        split
        · exact (isQueryBoundP_query_iff _ _ _).mpr (atTarget _ trivial)
        · exact (isQueryBoundP_query_iff _ _ _).mpr (atOther _ trivial)
      · trivial

/-- A hidden seal routes at most one seal request: to the challenger at the target, else to a known call. -/
theorem sealing_route (target : Label n) (modes : Label n → KeyMode) (decode : RawDecoder)
    (table : PqxdhRecordLiftChainTable.Table (Slot n)) (writer : RawCtxMixedShared.Writer)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (pending : PqxdhRecordLiftProtocol.Sealing n)
    (frames : PqxdhRecordLiftLoggedAdapters.Frames) (predicate : PqxdhRecordLiftCtxModes.Spec.Domain → Prop)
    [DecidablePred predicate] (bound : Nat)
    (atTarget : pending.material = target → ∀ request, SourceSeal request → predicate (.inl request) → 0 < bound)
    (atOther : ∀ known : PqxdhRecordLiftCtxModes.KnownCall, SourceSeal known.request → predicate (.inr known) → 0 < bound) :
    (simulateQ (routeKeyed target modes decode table)
      ((hiddenSealing writer table replace pending).run frames)).IsQueryBoundP predicate bound := by
  change (simulateQ (routeKeyed target modes decode table)
    (hiddenSealing writer table replace pending frames)).IsQueryBoundP predicate bound
  unfold hiddenSealing
  split
  · simp only [simulateQ_bind, simulateQ_spec_query]
    have first : (routeKeyed target modes decode table (pending.material, .inl (.inr (.inr
        (RawCtxSelectedMessageSealing.selectedInput (materialAt table pending.material).2 pending.sequence
          (replaceContext replace pending.context) (by assumption)))))).IsQueryBoundP predicate bound := by
      unfold routeKeyed
      split
      · rename_i same
        exact (isQueryBoundP_query_iff _ _ _).mpr (atTarget same _ trivial)
      · exact (isQueryBoundP_query_iff _ _ _).mpr (atOther _ trivial)
    refine (isQueryBoundP_bind first (fun reply _ => ?_)).mono (Nat.le_of_eq (Nat.add_zero bound))
    cases reply <;> simp
  · trivial

/-- The step reduction's requests in one category, per service: forwarded coins and hashes count `coinUnit` and `hashUnit` each, a hidden opening or seal at most one routed request. -/
theorem reduction_step (target : Label n) (modes : Label n → KeyMode)
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK) (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (predicate : PqxdhRecordLiftCtxModes.Spec.Domain → Prop) [DecidablePred predicate]
    (cost : PqxdhRecordLiftProtocol.Service n → Nat) (coinUnit hashUnit : Nat)
    (coinStep : ∀ coin, predicate (.inr (publicCall (RawCtxUniversalDecoder.decoder codec.frameRead)
      (.inl (.inl coin)))) → 0 < coinUnit)
    (hashStep : ∀ query, predicate (.inr (publicCall (RawCtxUniversalDecoder.decoder codec.frameRead)
      (.inl (.inr (.inl query))))) → 0 < hashUnit)
    (allocateCost : ∀ slot, 64 * coinUnit ≤ cost (.allocate slot))
    (coinCost : ∀ coin, coinUnit ≤ cost (.coin coin))
    (hashCost : ∀ bytes, hashUnit ≤ cost (.hash bytes))
    (lookupCost : ∀ coordinate, 76 * coinUnit ≤ cost (.lookup coordinate))
    (knownSendCost : ∀ kernel context, hashUnit ≤ cost (.knownSend kernel context))
    (knownReceiveCost : ∀ kernel target context, hashUnit ≤ cost (.knownReceive kernel target context))
    (openTarget : ∀ pending request, IsRawQuery request → predicate (.inl request) → 0 < cost (.opening pending))
    (openOther : ∀ pending (known : PqxdhRecordLiftCtxModes.KnownCall), IsRawQuery known.request →
      predicate (.inr known) → 0 < cost (.opening pending))
    (sealTarget : ∀ pending : PqxdhRecordLiftProtocol.Sealing n, pending.material = target → ∀ request,
      SourceSeal request → predicate (.inl request) → 0 < cost (.sealing pending))
    (sealOther : ∀ pending (known : PqxdhRecordLiftCtxModes.KnownCall), SourceSeal known.request →
      predicate (.inr known) → 0 < cost (.sealing pending))
    (query : PqxdhRecordLiftProtocol.Service n) (state : Bare n) :
    ((reduction target modes setup codec query).run state).IsQueryBoundP predicate (cost query) := by
  cases query with
  | allocate slot =>
      exact (isQueryBoundP_bind (coinForward_route _ predicate _ 64 coinUnit (allocate_total slot state.seeds)
        coinStep) (fun _ _ => isQueryBoundP_pure predicate _ 0)).mono (by have := allocateCost slot; omega)
  | coin coin =>
      exact (isQueryBoundP_bind ((isQueryBoundP_query_iff _ _ _).mpr
        (fun hit => Nat.lt_of_lt_of_le (coinStep coin hit) (coinCost coin)))
        (fun _ _ => isQueryBoundP_pure predicate _ 0)).mono (by omega)
  | hash bytes =>
      exact (isQueryBoundP_bind ((isQueryBoundP_query_iff _ _ _).mpr
        (fun hit => Nat.lt_of_lt_of_le (hashStep _ hit) (hashCost bytes)))
        (fun _ _ => isQueryBoundP_pure predicate _ 0)).mono (by omega)
  | charge kind => trivial
  | publish tag => trivial
  | lookup coordinate =>
      exact (isQueryBoundP_bind (coinForward_route _ predicate _ 76 coinUnit
        (bareLookup_total setup.source _ coordinate state.chain) coinStep)
        (fun _ _ => isQueryBoundP_pure predicate _ 0)).mono (by have := lookupCost coordinate; omega)
  | opening pending =>
      exact (isQueryBoundP_bind (opening_route target modes _ state.chain _ pending predicate (cost (.opening pending))
        (openTarget pending) (openOther pending)) (fun _ _ => isQueryBoundP_pure predicate _ 0)).mono (by omega)
  | sealing pending =>
      exact (isQueryBoundP_bind (sealing_route target modes _ state.chain codec.frameWrite id pending state.pending
        predicate (cost (.sealing pending)) (sealTarget pending) (sealOther pending)) (fun _ _ => isQueryBoundP_pure predicate _ 0)).mono (by omega)
  | knownSend kernel context =>
      exact (isQueryBoundP_bind (hashForward_route _ predicate _ 1 hashUnit
        (PqxdhRecordLiftCtxProtocolBounds.knownRom_total setup.source codec.frameWrite _ 1
          (PqxdhRecordLiftCtxProtocolBounds.known_send_hash kernel context) state.pending) hashStep)
        (fun _ _ => isQueryBoundP_pure predicate _ 0)).mono (by have := knownSendCost kernel context; omega)
  | knownReceive kernel target' context =>
      exact (isQueryBoundP_bind (hashForward_route _ predicate _ 1 hashUnit
        (PqxdhRecordLiftCtxProtocolBounds.knownRom_total setup.source codec.frameWrite _ 1
          (PqxdhRecordLiftCtxProtocolBounds.known_receive_hash kernel target' context) state.pending) hashStep)
        (fun _ _ => isQueryBoundP_pure predicate _ 0)).mono (by have := knownReceiveCost kernel target' context; omega)

/-! ### The step client's bills -/

section Client
variable (target : Label n) (modes : Label n → KeyMode) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
  (codec : PqxdhServerAuthExperiment.Codec Reader Response)

theorem reduction_uniform (query : PqxdhRecordLiftProtocol.Service n) (state : Bare n) :
    ((reduction target modes setup codec query).run state).IsQueryBoundP UniformRoute
      (categoryCost .uniform query) :=
  reduction_step target modes setup codec UniformRoute _ 1 0 (fun _ _ => Nat.one_pos)
    (fun _ hit => by simp [UniformRoute, publicCall, SourceUniform] at hit)
    (fun _ => le_refl _) (fun _ => le_refl _) (fun _ => Nat.zero_le _) (fun _ => le_refl _)
    (fun _ _ => Nat.zero_le _) (fun _ _ _ => Nat.zero_le _)
    (fun _ request raw hit => by cases request <;> simp_all [UniformRoute, SourceUniform, IsRawQuery])
    (fun _ known raw hit => by
      rcases known with ⟨⟨_, _, _, request⟩, _⟩
      cases request <;> simp_all [UniformRoute, SourceUniform, IsRawQuery])
    (fun _ _ request sealing hit => by
      rcases request with (_ | _ | _) | _ <;> simp_all [UniformRoute, SourceUniform, SourceSeal])
    (fun _ known sealing hit => by
      rcases known with ⟨⟨_, _, _, (_ | _ | _) | _⟩, _⟩ <;> simp_all [UniformRoute, SourceUniform, SourceSeal])
    query state

theorem reduction_hash (query : PqxdhRecordLiftProtocol.Service n) (state : Bare n) :
    ((reduction target modes setup codec query).run state).IsQueryBoundP HashRoute (categoryCost .hash query) :=
  reduction_step target modes setup codec HashRoute _ 0 1
    (fun _ hit => by simp [HashRoute, publicCall, AdaptiveCtxSharedReplayBounds.ModeHash,
      AdaptiveCtxQueryBounds.SourceWork, SourceUniform] at hit)
    (fun _ _ => Nat.one_pos)
    (fun _ => Nat.zero_le _) (fun _ => Nat.zero_le _) (fun _ => le_refl _) (fun _ => Nat.zero_le _)
    (fun _ _ => le_refl _) (fun _ _ _ => le_refl _)
    (fun _ _ _ _ => Nat.one_pos) (fun _ _ _ _ => Nat.one_pos) (fun _ _ _ _ _ => Nat.one_pos)
    (fun _ _ _ _ => Nat.one_pos) query state

theorem reduction_private (query : PqxdhRecordLiftProtocol.Service n) (state : Bare n) :
    ((reduction target modes setup codec query).run state).IsQueryBoundP PrivateRoute (categoryCost .hash query) :=
  reduction_step target modes setup codec PrivateRoute _ 0 0
    (fun _ hit => by simp [PrivateRoute, publicCall, AdaptiveCtxSharedReplayBounds.ModePrivate] at hit)
    (fun _ hit => by simp [PrivateRoute, publicCall, AdaptiveCtxSharedReplayBounds.ModePrivate] at hit)
    (fun _ => Nat.zero_le _) (fun _ => Nat.zero_le _) (fun _ => Nat.zero_le _) (fun _ => Nat.zero_le _)
    (fun _ _ => Nat.zero_le _) (fun _ _ _ => Nat.zero_le _)
    (fun _ _ _ _ => Nat.one_pos) (fun _ _ _ _ => Nat.one_pos) (fun _ _ _ _ _ => Nat.one_pos)
    (fun _ _ _ _ => Nat.one_pos) query state

theorem reduction_seal (query : PqxdhRecordLiftProtocol.Service n) (state : Bare n) :
    ((reduction target modes setup codec query).run state).IsQueryBoundP (TargetClass SourceSeal)
      (targetSeal target query) :=
  reduction_step target modes setup codec (TargetClass SourceSeal) _ 0 0
    (fun _ hit => by simp [TargetClass] at hit) (fun _ hit => by simp [TargetClass] at hit)
    (fun _ => Nat.zero_le _) (fun _ => Nat.zero_le _) (fun _ => Nat.zero_le _) (fun _ => Nat.zero_le _)
    (fun _ _ => Nat.zero_le _) (fun _ _ _ => Nat.zero_le _)
    (fun _ request raw hit => by cases request <;> simp_all [TargetClass, SourceSeal, IsRawQuery])
    (fun _ _ _ hit => by simp [TargetClass] at hit)
    (fun _ same _ _ _ => by simp [targetSeal, same])
    (fun _ _ _ hit => by simp [TargetClass] at hit) query state

theorem reduction_raw (query : PqxdhRecordLiftProtocol.Service n) (state : Bare n) :
    ((reduction target modes setup codec query).run state).IsQueryBoundP (TargetClass IsRawQuery)
      (categoryCost .raw query) :=
  reduction_step target modes setup codec (TargetClass IsRawQuery) _ 0 0
    (fun _ hit => by simp [TargetClass] at hit) (fun _ hit => by simp [TargetClass] at hit)
    (fun _ => Nat.zero_le _) (fun _ => Nat.zero_le _) (fun _ => Nat.zero_le _) (fun _ => Nat.zero_le _)
    (fun _ _ => Nat.zero_le _) (fun _ _ _ => Nat.zero_le _)
    (fun _ _ _ _ => Nat.one_pos) (fun _ _ _ hit => by simp [TargetClass] at hit)
    (fun _ _ request sealing hit => by
      rcases request with (_ | _ | _) | _ <;> simp_all [TargetClass, SourceSeal, IsRawQuery])
    (fun _ _ _ hit => by simp [TargetClass] at hit) query state

end Client

/-- A link client is bounded in one category by the program's bill under the step reduction's per-service cost, plus the decision's coins at their unit. -/
theorem link_route (target : Label n) (modes : Label n → KeyMode) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (env : Environment n E) (serverKid : Std.U64) (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) (decision : View n E X → ProbComp Bool)
    (predicate : PqxdhRecordLiftCtxModes.Spec.Domain → Prop) [DecidablePred predicate]
    (cost : PqxdhRecordLiftProtocol.Service n → Nat) (programBound decisionCost decisionUnit : Nat)
    (step : ∀ query state, ((reduction target modes setup codec query).run state).IsQueryBoundP predicate (cost query))
    (program : Weighted cost
      (PqxdhRecordLiftProtocol.program env setup.source.crypto codec route serverKid bounds mode adversary) programBound)
    (coins : ∀ view, (decision view).IsTotalQueryBound decisionCost)
    (coinStep : ∀ coin, predicate (.inr (publicCall (RawCtxUniversalDecoder.decoder codec.frameRead)
      (.inl (.inl coin)))) → 0 < decisionUnit) :
    (linkClient target modes setup codec route env serverKid bounds mode adversary decision).IsQueryBoundP predicate
      (programBound + decisionCost * decisionUnit) :=
  isQueryBoundP_bind (run_bound (reduction target modes setup codec) predicate cost step _ programBound program _)
    (fun _ _ => coinForward_route _ predicate _ decisionCost decisionUnit (coins _) coinStep)

/-- The explicit CTX bills: program-level coins (with 64 per possible private replay-cache fill) plus the decision's coins, shared hashes, one seal, and raw receives. -/
def ctxBills : CtxBills where
  uniform input := programBill .uniform input + input.decision + 64 * programBill .hash input
  hash input := programBill .hash input
  seals _ := 1
  raw input := programBill .raw input

/-- The hash bill is the world's shared-hash total. -/
theorem hash_bill (input : BillInput) : ctxBills.hash input = sharedHashTotal input := by
  simp [ctxBills, programBill, effectBill, effectTotal, operationBill, PqxdhRecordLiftCtxProgramBounds.lookupCost,
    PqxdhRecordLiftCtxProgramBounds.sealingCost, PqxdhRecordLiftCtxProgramBounds.openingCost,
    PqxdhRecordLiftBudget.startupCost, PqxdhRecordLiftBudget.directCost, sharedHashTotal]
  omega

section Final
variable (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK) (codec : PqxdhServerAuthExperiment.Codec Reader Response)
  (route : RawCtxServerRouting.SenderDecoder) (serverKid : Std.U64) (bounds : FreshBounds)

/-- Every step client respects the explicit CTX bills. -/
theorem stepBilled : StepBilled (n := n) setup codec route serverKid bounds ctxBills := by
  intro E X env startup allowance framed mode adversary budget respects decision cost coins step
  have program := fun kind => program_categories kind env startup allowance framed setup.source.crypto codec route
    serverKid bounds mode budget adversary respects cost
  let target := PqxdhRecordLiftChainOrder.entryAt (positions := positions budget) step
  let modes : Label n → KeyMode := hybridModes (positions budget) step.val
  have uniform := link_route target modes setup codec route env serverKid bounds mode adversary decision UniformRoute _ _ cost 1
    (reduction_uniform target modes setup codec) (program .uniform) coins (fun _ _ => Nat.one_pos)
  have privateFill := link_route target modes setup codec route env serverKid bounds mode adversary decision PrivateRoute _ _
    cost 0 (reduction_private target modes setup codec) (program .hash) coins
    (fun _ hit => by simp [PrivateRoute, publicCall, AdaptiveCtxSharedReplayBounds.ModePrivate] at hit)
  have hash := link_route target modes setup codec route env serverKid bounds mode adversary decision HashRoute _ _ cost 0
    (reduction_hash target modes setup codec) (program .hash) coins
    (fun _ hit => by simp [HashRoute, publicCall, AdaptiveCtxSharedReplayBounds.ModeHash,
      AdaptiveCtxQueryBounds.SourceWork, SourceUniform] at hit)
  have sealing := link_route target modes setup codec route env serverKid bounds mode adversary decision
    (TargetClass SourceSeal) _ _ cost 0 (reduction_seal target modes setup codec)
    (program_target_seal target env setup.source.crypto codec route serverKid bounds mode adversary) coins
    (fun _ hit => by simp [TargetClass] at hit)
  have raw := link_route target modes setup codec route env serverKid bounds mode adversary decision
    (TargetClass IsRawQuery) _ _ cost 0 (reduction_raw target modes setup codec) (program .raw) coins
    (fun _ hit => by simp [TargetClass] at hit)
  simp only [Nat.mul_one, Nat.mul_zero, Nat.add_zero] at uniform privateFill hash sealing raw
  exact ⟨⟨_, _, le_refl _, uniform, privateFill⟩, hash, sealing, by norm_num [ctxBills], raw⟩

/-- **`ctx_lift`, integrity half (H-5, item 4).** With the explicit reduction family `ctxReduction` and the explicit bills `ctxBills`, the zero-refusal integrity target holds in both forms. -/
theorem ctxAuthLiftTarget (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery) :
    CtxAuthLiftTarget setup codec route serverKid bounds n fallback (ctxReduction setup codec route serverKid bounds)
      ctxBills :=
  ctxAuthLiftTarget_of_billed setup codec route serverKid bounds fallback ctxBills
    (stepBilled setup codec route serverKid bounds)

/-- The integrity half of `ctx_lift` for every refusal term, both forms. -/
theorem ctxAuthLiftStatement (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery)
    (refusal : BillInput → ℝ≥0∞) :
    CtxAuthLiftStatement setup codec route serverKid bounds n fallback
      (ctxReduction setup codec route serverKid bounds) ctxBills refusal :=
  ctxAuthLiftStatement_of_bool setup codec route serverKid bounds n fallback _ ctxBills refusal
    (ctxAuthLiftBool_of_billed setup codec route serverKid bounds fallback ctxBills refusal
      (stepBilled setup codec route serverKid bounds))

end Final

end BeaconcryptCore.Computational.PqxdhRecordLiftCtxBills

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxBills.weighted_cost_mono' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxBills.weighted_cost_mono

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxBills.run_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxBills.run_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxBills.query_categories' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxBills.query_categories

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxBills.publish_cost' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxBills.publish_cost

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxBills.charge_cost' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxBills.charge_cost

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxBills.ownerRun_categories' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxBills.ownerRun_categories

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxBills.resolve_categories' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxBills.resolve_categories

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxBills.capability_categories' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxBills.capability_categories

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxBills.effects_categories' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxBills.effects_categories

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxBills.serverStep_categories' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxBills.serverStep_categories

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxBills.beaconStep_categories' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxBills.beaconStep_categories

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxBills.handler_categories' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxBills.handler_categories

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxBills.worldBill_split' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxBills.worldBill_split

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxBills.world_categories' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxBills.world_categories

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxBills.program_categories' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxBills.program_categories

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxBills.fresh_target_seal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxBills.fresh_target_seal

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxBills.program_target_seal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxBills.program_target_seal

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxBills.coinForward_route' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxBills.coinForward_route

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxBills.hashForward_route' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxBills.hashForward_route

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxBills.allocate_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxBills.allocate_total

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxBills.bareLookup_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxBills.bareLookup_total

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxBills.opening_route' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxBills.opening_route

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxBills.sealing_route' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxBills.sealing_route

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxBills.reduction_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxBills.reduction_step

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxBills.reduction_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxBills.reduction_uniform

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxBills.reduction_hash' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxBills.reduction_hash

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxBills.reduction_private' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxBills.reduction_private

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxBills.reduction_seal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxBills.reduction_seal

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxBills.reduction_raw' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxBills.reduction_raw

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxBills.link_route' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxBills.link_route

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxBills.hash_bill' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxBills.hash_bill

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxBills.stepBilled' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxBills.stepBilled

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxBills.ctxAuthLiftTarget' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxBills.ctxAuthLiftTarget

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxBills.ctxAuthLiftStatement' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxBills.ctxAuthLiftStatement
