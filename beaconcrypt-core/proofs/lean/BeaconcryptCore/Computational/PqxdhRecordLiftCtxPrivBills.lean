-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRecordLiftCtxPriv
import BeaconcryptCore.Computational.PqxdhRecordLiftCtxBills

/-!
# Record-lift CTX privacy bills and the privacy half of `ctx_lift` (items 4 and 5, stage S4)

**Statement.** `ctxPrivLiftStatement`: with the explicit reduction family `PqxdhRecordLiftCtxPriv.privReduction` and the explicit bills `privBills`, `PqxdhRecordLiftIdeal.CtxPrivLiftStatement` holds as defined, in both forms: in either observation mode, `idealAuth` and `randomRecords` (in mode P, `idealRecords`) differ, for every cache-free decision and every Boolean event, by at most the exact sum over the `hops n budget` target key indices of `privacyLoss` (the IND$ advantage of `AdaptiveCtxPrivacyGuard.viewReduction` of the hop's one-key adversary), each with coefficient one, and every hop's adversary respects the bills. The proof discharges the premise `StepBilled privBills` of `PqxdhRecordLiftCtxPriv.ctxPrivLiftStatement_of_billed` (`stepBilled`).

**Local bounds.** Random mode with the single-coin sampler draws one coin for the body and one for the tag (`bytesSample_total`) and at most 64 for the private commitment fill, and makes no shared-hash request for a seal (`seal_uniform`, `seal_hash`, `random_uniform_step`, `random_hash_step`). With `AdaptiveCtxSharedReplayBounds` for real and replay mode, every known call of any mode draws one coin per coin request, at most 66 per keyed request and at most one shared-hash request per non-coin request (`known_uniform_step`, `known_hash_step`). Through the three-mode reduction of `PqxdhRecordLiftCtxPrivModes` (`uniform_step`, `hash_step`, `target_step`), `decision_budgets` turns the client's route ledgers (`UniformRoute`, `KeyedRoute`, `HashRoute`, `TargetClass`) into the constructed one-key client's coin, shared-hash, selected-seal and selected-raw bounds.

**Step bills.** As for the integrity bills (`PqxdhRecordLiftCtxBills`, whose program-level ledgers `program_categories` and `program_target_seal` are reused unchanged), the privacy link reduction forwards each coin and public hash as one request (`coinForward_route`, `hashForward_route`), routes at most one request per hidden opening or seal (`opening_route`, `sealing_route`) and makes at most one hash per caller-known send or receive; `reduction_step` and its instances give the five route ledgers (`reduction_uniform`, `reduction_keyed`, `reduction_hash`, `reduction_seal`, `reduction_raw`), and `link_route` adds the decision's coins. `privBills` charges the program's coins and the decision's coins plus 66 coins per keyed request (bounded by the shared-hash ledger), the program's shared hashes (the world's shared-hash total, `hash_bill`), one seal (the target is sealed at most once) and the raw receives.

**Contracts.** No theorem of this module has an assumption or contract hypothesis; the contracts of the brief's H-7 list used by each theorem are listed in `doc/impl/record-lift-ctx-priv.md`. New Claude work, adapted from Claude's `PqxdhRecordLiftCtxBills` and `PqxdhRecordLiftCtxModeBounds`; nothing adapted from Codex WIP.
-/

open OracleComp OracleSpec ENNReal CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false

namespace BeaconcryptCore.Computational.PqxdhRecordLiftCtxPrivBills
open PqxdhRecordLiftInterface PqxdhRecordLiftIdeal PqxdhRecordLiftCtxHybrid
open PqxdhRecordLiftCtxPrivLink PqxdhRecordLiftCtxPriv
open PqxdhRecordLiftCtxPrivModes (KnownCall Spec knownLocal randomWith sealWith bytesSample bytesSample_eq)
open PqxdhDeploymentInterface (Mode ModeSpec FreshBounds Budget)
open PqxdhServerAuthExperiment (Setup Codec)
open PqxdhRecordLiftWorldCompiler (Label)
open CtxRomAuth AdaptiveCtxReceive AdaptiveCtxSharedHash
open AdaptiveCtxQueryBounds (SourceUniform SourceHash SourceSeal)
open AdaptiveCtxSharedReplayBounds (lift_hash_bound private_hash_bound lift_uniform_bound private_uniform_bound)
variable {n : Nat} {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response E X : Type}

/-! ### Local bounds of the single-coin random mode -/

/-- The single-coin sampler makes one coin query. -/
theorem bytesSample_total (length : Nat) : (bytesSample length).IsTotalQueryBound 1 := by
  rw [bytesSample_eq]
  simp only [IsTotalQueryBound, isQueryBound_map_iff]
  exact (isQueryBound_query_iff (spec := unifSpec) (256 ^ length - 1) 1 _ _).mpr Nat.one_pos


set_option backward.isDefEq.respectTransparency false in
/-- A single-coin random seal makes no shared-hash request. -/
theorem seal_hash (input : CtxSealInput) (entry : KeyEntry) :
    (sealWith bytesSample input entry).IsQueryBoundP (HashClass true) 0 := by
  unfold sealWith
  split
  · trivial
  · refine (isQueryBoundP_bind (lift_hash_bound _) (fun _ _ => (isQueryBoundP_bind (lift_hash_bound _)
      (fun _ _ => (isQueryBoundP_bind (private_hash_bound _ entry) (fun _ _ => isQueryBoundP_pure _ _ 0)))))).mono ?_
    simp

set_option backward.isDefEq.respectTransparency false in
/-- A single-coin random seal draws at most two coins and one private 64-byte fill. -/
theorem seal_uniform (input : CtxSealInput) (entry : KeyEntry) :
    (sealWith bytesSample input entry).IsQueryBoundP (HashClass false) 66 := by
  unfold sealWith
  split
  · trivial
  · exact (isQueryBoundP_bind (lift_uniform_bound _ 1 (bytesSample_total _)) (fun _ _ =>
      isQueryBoundP_bind (lift_uniform_bound _ 1 (bytesSample_total _)) (fun _ _ =>
        isQueryBoundP_bind (private_uniform_bound _ entry) (fun _ _ => isQueryBoundP_pure _ _ 0)))).mono (by omega)

set_option backward.isDefEq.respectTransparency false in
/-- Single-coin random mode makes one shared-hash request per public hash and none otherwise. -/
theorem random_hash_step (decode : RawDecoder) (query : ReceiveSpec.Domain) (entry : KeyEntry) :
    ((randomWith bytesSample decode query).run entry).IsQueryBoundP (HashClass true)
      (if SourceHash query then 1 else 0) := by
  rcases query with (coin | (hash | input)) | raw
  · simp only [randomWith, StateT.run, bind_pure_comp, isQueryBoundP_map_iff,
      SourceHash, ite_false, isQueryBoundP_query_iff, HashClass]
    decide
  · simp only [randomWith, StateT.run, bind_pure_comp, isQueryBoundP_map_iff,
      SourceHash, ite_true, isQueryBoundP_query_iff, HashClass]
    decide
  · simpa only [randomWith, StateT.run, SourceHash, ite_false] using seal_hash input entry
  · simp only [randomWith, StateT.run, AdaptiveCtxSharedReplay.localRaw, SourceHash, ite_false]
    split
    · trivial
    · simpa only [bind_pure_comp, isQueryBoundP_map_iff] using private_hash_bound _ _

set_option backward.isDefEq.respectTransparency false in
/-- Single-coin random mode draws one coin per coin request, at most 66 per seal and 64 per raw request. -/
theorem random_uniform_step (decode : RawDecoder) (query : ReceiveSpec.Domain) (entry : KeyEntry) :
    ((randomWith bytesSample decode query).run entry).IsQueryBoundP (HashClass false)
      (if SourceUniform query then 1 else if SourceHash query then 0 else 66) := by
  rcases query with (coin | (hash | input)) | raw
  · simp only [randomWith, StateT.run, bind_pure_comp, isQueryBoundP_map_iff,
      SourceUniform, ite_true, isQueryBoundP_query_iff, HashClass]
    decide
  · simp only [randomWith, StateT.run, bind_pure_comp, isQueryBoundP_map_iff,
      SourceUniform, SourceHash, ite_false, ite_true, isQueryBoundP_query_iff, HashClass]
    decide
  · simpa only [randomWith, StateT.run, SourceUniform, SourceHash, ite_false] using seal_uniform input entry
  · simp only [randomWith, StateT.run, AdaptiveCtxSharedReplay.localRaw, SourceUniform, SourceHash, ite_false]
    split
    · trivial
    · simpa only [bind_pure_comp, isQueryBoundP_map_iff] using
        (private_uniform_bound _ _).mono (by norm_num : (64 : Nat) ≤ 66)


/-! ### The three-mode reduction's requests -/

open AdaptiveCtxSharedTarget (ForwardClass forward_bound forward_hash_class forward_uniform_class forward_seal_class
  forward_raw_class)
open AdaptiveCtxDynamicKnownKeys (ReductionState initialReduction)

set_option backward.isDefEq.respectTransparency false in
/-- A known call's local program makes at most one shared-hash request, and none for a coin. -/
theorem known_hash_step (crypto : Pqxdh.Crypto) (call : KnownCall) (entry : KeyEntry) :
    ((knownLocal bytesSample crypto call).run entry).IsQueryBoundP (HashClass true)
      (if SourceUniform call.request then 0 else 1) := by
  rcases call with ⟨⟨slot, key, decode, request⟩, mode⟩
  cases mode
  · exact (AdaptiveCtxSharedReplayBounds.mode_hash_step true decode crypto key request entry).mono (by
      by_cases coin : SourceUniform request <;>
        simp [AdaptiveCtxSharedReplayBounds.ModeHash, AdaptiveCtxQueryBounds.SourceWork, coin])
  · exact (AdaptiveCtxSharedReplayBounds.mode_hash_step false decode crypto key request entry).mono (by
      rcases request with (_ | _ | _) | _ <;>
        simp [AdaptiveCtxSharedReplayBounds.ModeHash, SourceUniform, SourceHash])
  · exact (random_hash_step decode request entry).mono (by
      rcases request with (_ | _ | _) | _ <;> simp [SourceUniform, SourceHash])

set_option backward.isDefEq.respectTransparency false in
/-- A known call's local program draws one coin per coin request, at most 66 per seal or raw request and none per
public hash. -/
theorem known_uniform_step (crypto : Pqxdh.Crypto) (call : KnownCall) (entry : KeyEntry) :
    ((knownLocal bytesSample crypto call).run entry).IsQueryBoundP (HashClass false)
      (if SourceUniform call.request then 1 else if SourceHash call.request then 0 else 66) := by
  rcases call with ⟨⟨slot, key, decode, request⟩, mode⟩
  cases mode
  · exact (AdaptiveCtxSharedReplayBounds.mode_uniform_step true decode crypto key request entry).mono (by
      rcases request with (_ | _ | _) | _ <;>
        simp [AdaptiveCtxSharedReplayBounds.ModePrivate, SourceUniform, SourceHash])
  · exact (AdaptiveCtxSharedReplayBounds.mode_uniform_step false decode crypto key request entry).mono (by
      rcases request with (_ | _ | _) | _ <;>
        simp [AdaptiveCtxSharedReplayBounds.ModePrivate, SourceUniform, SourceHash])
  · exact random_uniform_step decode request entry

/-- Explicit coin requests: the selected challenger's and the known calls' coin requests. -/
def UniformRoute : Spec.Domain → Prop
  | .inl query => SourceUniform query
  | .inr known => SourceUniform known.request

/-- Keyed known requests (seals and raw requests of known calls), each drawing at most 66 coins. -/
def KeyedRoute : Spec.Domain → Prop
  | .inl _ => False
  | .inr known => ¬SourceUniform known.request ∧ ¬SourceHash known.request

/-- Requests that may issue one shared-hash request: selected public hashes and known calls other than coins. -/
def HashRoute : Spec.Domain → Prop
  | .inl query => SourceHash query
  | .inr known => ¬SourceUniform known.request

/-- Selected requests of one class. -/
def TargetClass (p : ReceiveSpec.Domain → Prop) : Spec.Domain → Prop
  | .inl query => p query
  | .inr _ => False

/-- Coin routes are decidable. -/
instance : DecidablePred UniformRoute := fun query => by
  cases query <;> unfold UniformRoute <;> infer_instance

/-- Keyed routes are decidable. -/
instance : DecidablePred KeyedRoute := fun query => by
  cases query <;> unfold KeyedRoute <;> infer_instance

/-- Hash routes are decidable. -/
instance : DecidablePred HashRoute := fun query => by
  cases query <;> unfold HashRoute <;> infer_instance

/-- Selected classes are decidable. -/
instance (p : ReceiveSpec.Domain → Prop) [DecidablePred p] : DecidablePred (TargetClass p) :=
  fun query => by cases query <;> unfold TargetClass <;> infer_instance

set_option backward.isDefEq.respectTransparency false in
/-- Known calls make no selected seal or raw request; every selected request keeps its class. -/
theorem target_step (crypto : Pqxdh.Crypto) (p : ReceiveSpec.Domain → Prop) [DecidablePred p]
    (unavailable : ForwardClass p = fun _ => False) (query : Spec.Domain) (state : ReductionState) :
    ((PqxdhRecordLiftCtxPrivModes.reductionImpl bytesSample crypto query).run state).IsQueryBoundP p
      (if TargetClass p query then 1 else 0) := by
  cases query with
  | inl selected =>
    simp only [PqxdhRecordLiftCtxPrivModes.reductionImpl, StateT.run, bind_pure_comp, isQueryBoundP_map_iff,
      TargetClass]
    exact (isQueryBoundP_query_iff p selected _).mpr (by intro hit; simp [hit])
  | inr known =>
    simp only [PqxdhRecordLiftCtxPrivModes.reductionImpl, StateT.run, bind_pure_comp, isQueryBoundP_map_iff,
      TargetClass, ite_false]
    apply forward_bound
    simp only [unavailable]
    exact isQueryBoundP_false _ 0

set_option backward.isDefEq.respectTransparency false in
/-- Every shared-hash request of the reduction is a selected public hash or a known call's hash. -/
theorem hash_step (crypto : Pqxdh.Crypto) (query : Spec.Domain) (state : ReductionState) :
    ((PqxdhRecordLiftCtxPrivModes.reductionImpl bytesSample crypto query).run state).IsQueryBoundP SourceHash
      (if HashRoute query then 1 else 0) := by
  cases query with
  | inl selected =>
    simp only [PqxdhRecordLiftCtxPrivModes.reductionImpl, StateT.run, bind_pure_comp, isQueryBoundP_map_iff,
      HashRoute]
    exact (isQueryBoundP_query_iff SourceHash selected _).mpr (by intro hit; simp [hit])
  | inr known =>
    simp only [PqxdhRecordLiftCtxPrivModes.reductionImpl, StateT.run, bind_pure_comp, isQueryBoundP_map_iff,
      HashRoute]
    apply forward_bound
    simp only [forward_hash_class]
    exact (known_hash_step crypto known _).mono (by by_cases coin : SourceUniform known.request <;> simp [coin])

set_option backward.isDefEq.respectTransparency false in
/-- Every coin request of the reduction is a selected coin, a known call's coin, or one of at most 66 coins of a keyed
known request. -/
theorem uniform_step (crypto : Pqxdh.Crypto) (query : Spec.Domain) (state : ReductionState) :
    ((PqxdhRecordLiftCtxPrivModes.reductionImpl bytesSample crypto query).run state).IsQueryBoundP SourceUniform
      (if UniformRoute query then 1 else if KeyedRoute query then 66 else 0) := by
  cases query with
  | inl selected =>
    simp only [PqxdhRecordLiftCtxPrivModes.reductionImpl, StateT.run, bind_pure_comp, isQueryBoundP_map_iff,
      UniformRoute, KeyedRoute, ite_false]
    exact (isQueryBoundP_query_iff SourceUniform selected _).mpr (by intro hit; simp [hit])
  | inr known =>
    simp only [PqxdhRecordLiftCtxPrivModes.reductionImpl, StateT.run, bind_pure_comp, isQueryBoundP_map_iff,
      UniformRoute, KeyedRoute]
    apply forward_bound
    simp only [forward_uniform_class]
    exact (known_uniform_step crypto known _).mono (by
      by_cases coin : SourceUniform known.request <;> by_cases hash : SourceHash known.request <;>
        simp [coin, hash])

/-- Keyed known requests are not explicit coin requests. -/
theorem keyed_not_uniform (query : Spec.Domain) (keyed : KeyedRoute query) : ¬UniformRoute query := by
  cases query with
  | inl _ => exact keyed.elim
  | inr known => exact keyed.1

/-- The constructed ordinary client's coin, shared-hash, selected-seal and selected-raw ledgers. -/
theorem decision_budgets (crypto : Pqxdh.Crypto) (client : OracleComp Spec Bool)
    (qUniform qKeyed qHash qSeal qRaw : Nat)
    (uniformBound : client.IsQueryBoundP UniformRoute qUniform)
    (keyedBound : client.IsQueryBoundP KeyedRoute qKeyed)
    (hashBound : client.IsQueryBoundP HashRoute qHash)
    (sealBound : client.IsQueryBoundP (TargetClass SourceSeal) qSeal)
    (rawBound : client.IsQueryBoundP (TargetClass IsRawQuery) qRaw) :
    (PqxdhRecordLiftCtxPrivModes.decisionClient bytesSample crypto client).IsQueryBoundP SourceUniform
        (qUniform + 66 * qKeyed) ∧
      (PqxdhRecordLiftCtxPrivModes.decisionClient bytesSample crypto client).IsQueryBoundP SourceHash qHash ∧
      (PqxdhRecordLiftCtxPrivModes.decisionClient bytesSample crypto client).IsQueryBoundP SourceSeal qSeal ∧
      (PqxdhRecordLiftCtxPrivModes.decisionClient bytesSample crypto client).IsQueryBoundP IsRawQuery qRaw := by
  simp only [PqxdhRecordLiftCtxPrivModes.decisionClient, PqxdhRecordLiftCtxPrivModes.wrapped, isQueryBoundP_map_iff]
  refine ⟨?_, hashBound.simulateQ_run_StateT_of_step (hash_step crypto) _,
    sealBound.simulateQ_run_StateT_of_step (target_step crypto _ forward_seal_class) _,
    rawBound.simulateQ_run_StateT_of_step (target_step crypto _ forward_raw_class) _⟩
  have vector := uniformBound.and_isQueryBound_pair keyedBound
  exact vector.simulateQ_run_of_step (mapBudget := fun budget : Nat × Nat => budget.1 + 66 * budget.2)
    (stepBudget := fun query _ => if UniformRoute query then 1 else if KeyedRoute query then 66 else 0)
    (combine := Nat.add)
    (fun stepBound restBound => isQueryBoundP_bind stepBound (fun result _ => restBound result))
    (fun query _ state _ => uniform_step crypto query state)
    (fun query budget allowed => by
      by_cases coins : UniformRoute query
      · have notKeyed : ¬KeyedRoute query := fun hit => keyed_not_uniform query hit coins
        simp only [coins, notKeyed, ite_true, ite_false] at allowed ⊢
        change 1 + (budget.1 - 1 + 66 * budget.2) = budget.1 + 66 * budget.2
        simp only [not_true_eq_false, false_or] at allowed
        omega
      · by_cases keyed : KeyedRoute query
        · simp only [coins, keyed, ite_true, ite_false] at allowed ⊢
          change 66 + (budget.1 + 66 * (budget.2 - 1)) = budget.1 + 66 * budget.2
          simp only [not_true_eq_false, false_or] at allowed
          omega
        · simp only [coins, keyed, ite_false]
          change 0 + (budget.1 + 66 * budget.2) = budget.1 + 66 * budget.2
          exact Nat.zero_add _) initialReduction

/-! ### The privacy reduction's requests per service -/

open PqxdhRecordLiftCtxBills (targetSeal program_target_seal programBill program_categories)
open PqxdhRecordLiftCtxProtocolBounds (BudgetKind categoryCost)
open PqxdhRecordLiftCtxProgramBounds (Weighted)
open PqxdhRecordLiftCtxProtocol (Bare)

/-- Forwarded coins issue one request per coin, each in a single category. -/
theorem coinForward_route {Result : Type} (decode : RawDecoder) (predicate : PqxdhRecordLiftCtxPrivModes.Spec.Domain → Prop)
    [DecidablePred predicate] (work : ProbComp Result) (count step : Nat) (total : work.IsTotalQueryBound count)
    (each : ∀ coin, predicate (.inr (publicCall decode (.inl (.inl coin)))) → 0 < step) :
    (simulateQ (coinForward decode) work).IsQueryBoundP predicate (count * step) :=
  IsQueryBoundP.simulateQ_of_step_le_total total (fun coin => (isQueryBoundP_query_iff _ _ _).mpr (each coin))

/-- Forwarded public hashes issue one request per hash, each in a single category. -/
theorem hashForward_route {Result : Type} (decode : RawDecoder) (predicate : PqxdhRecordLiftCtxPrivModes.Spec.Domain → Prop)
    [DecidablePred predicate] (work : OracleComp CtxRO Result) (count step : Nat) (total : work.IsTotalQueryBound count)
    (each : ∀ query, predicate (.inr (publicCall decode (.inl (.inr (.inl query))))) → 0 < step) :
    (simulateQ (hashForward decode) work).IsQueryBoundP predicate (count * step) :=
  IsQueryBoundP.simulateQ_of_step_le_total total (fun query => (isQueryBoundP_query_iff _ _ _).mpr (each query))

/-- A hidden opening routes at most one raw request: to the challenger at the target, else to a known call. -/
theorem opening_route (target : Label n) (modes : Label n → KeyMode) (decode : RawDecoder)
    (table : PqxdhRecordLiftChainTable.Table (Slot n)) (seeds : PqxdhRecordLiftChainTable.Seeds (Slot n))
    (pending : PqxdhRecordLiftProtocol.Opening n) (predicate : PqxdhRecordLiftCtxPrivModes.Spec.Domain → Prop)
    [DecidablePred predicate] (bound : Nat)
    (atTarget : ∀ request, IsRawQuery request → predicate (.inl request) → 0 < bound)
    (atOther : ∀ known : KnownCall, IsRawQuery known.request → predicate (.inr known) → 0 < bound) :
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
    (frames : PqxdhRecordLiftLoggedAdapters.Frames) (predicate : PqxdhRecordLiftCtxPrivModes.Spec.Domain → Prop)
    [DecidablePred predicate] (bound : Nat)
    (atTarget : pending.material = target → ∀ request, SourceSeal request → predicate (.inl request) → 0 < bound)
    (atOther : ∀ known : KnownCall, SourceSeal known.request → predicate (.inr known) → 0 < bound) :
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
    (predicate : PqxdhRecordLiftCtxPrivModes.Spec.Domain → Prop) [DecidablePred predicate]
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
    (openOther : ∀ pending (known : KnownCall), IsRawQuery known.request →
      predicate (.inr known) → 0 < cost (.opening pending))
    (sealTarget : ∀ pending : PqxdhRecordLiftProtocol.Sealing n, pending.material = target → ∀ request,
      SourceSeal request → predicate (.inl request) → 0 < cost (.sealing pending))
    (sealOther : ∀ pending (known : KnownCall), SourceSeal known.request →
      predicate (.inr known) → 0 < cost (.sealing pending))
    (query : PqxdhRecordLiftProtocol.Service n) (state : Bare n) :
    ((reduction target modes setup codec query).run state).IsQueryBoundP predicate (cost query) := by
  cases query with
  | allocate slot =>
      exact (isQueryBoundP_bind (coinForward_route _ predicate _ 64 coinUnit (PqxdhRecordLiftCtxBills.allocate_total slot state.seeds)
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
        (PqxdhRecordLiftCtxBills.bareLookup_total setup.source _ coordinate state.chain) coinStep)
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

/-- The privacy step reduction's explicit coin requests per service. -/
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

/-- The privacy step reduction's possible shared-hash requests per service. -/
theorem reduction_hash (query : PqxdhRecordLiftProtocol.Service n) (state : Bare n) :
    ((reduction target modes setup codec query).run state).IsQueryBoundP HashRoute (categoryCost .hash query) :=
  reduction_step target modes setup codec HashRoute _ 0 1
    (fun _ hit => by simp [HashRoute, publicCall, SourceUniform] at hit)
    (fun _ _ => Nat.one_pos)
    (fun _ => Nat.zero_le _) (fun _ => Nat.zero_le _) (fun _ => le_refl _) (fun _ => Nat.zero_le _)
    (fun _ _ => le_refl _) (fun _ _ _ => le_refl _)
    (fun _ _ _ _ => Nat.one_pos) (fun _ _ _ _ => Nat.one_pos) (fun _ _ _ _ _ => Nat.one_pos)
    (fun _ _ _ _ => Nat.one_pos) query state

/-- The privacy step reduction's keyed known requests per service: at most one per hidden opening or seal. -/
theorem reduction_keyed (query : PqxdhRecordLiftProtocol.Service n) (state : Bare n) :
    ((reduction target modes setup codec query).run state).IsQueryBoundP KeyedRoute (categoryCost .hash query) :=
  reduction_step target modes setup codec KeyedRoute _ 0 0
    (fun _ hit => by simp [KeyedRoute, publicCall, SourceUniform] at hit)
    (fun _ hit => by simp [KeyedRoute, publicCall, SourceUniform, SourceHash] at hit)
    (fun _ => Nat.zero_le _) (fun _ => Nat.zero_le _) (fun _ => Nat.zero_le _) (fun _ => Nat.zero_le _)
    (fun _ _ => Nat.zero_le _) (fun _ _ _ => Nat.zero_le _)
    (fun _ _ _ _ => Nat.one_pos) (fun _ _ _ _ => Nat.one_pos) (fun _ _ _ _ _ => Nat.one_pos)
    (fun _ _ _ _ => Nat.one_pos) query state

/-- The privacy step reduction's selected seals per service: only at the target coordinate. -/
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

/-- The privacy step reduction's selected raw requests per service: at most one per hidden opening. -/
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
    (predicate : PqxdhRecordLiftCtxPrivModes.Spec.Domain → Prop) [DecidablePred predicate]
    (cost : PqxdhRecordLiftProtocol.Service n → Nat) (programBound decisionCost decisionUnit : Nat)
    (step : ∀ query state, ((reduction target modes setup codec query).run state).IsQueryBoundP predicate (cost query))
    (program : Weighted cost
      (PqxdhRecordLiftProtocol.program env setup.source.crypto codec route serverKid bounds mode adversary) programBound)
    (coins : ∀ view, (decision view).IsTotalQueryBound decisionCost)
    (coinStep : ∀ coin, predicate (.inr (publicCall (RawCtxUniversalDecoder.decoder codec.frameRead)
      (.inl (.inl coin)))) → 0 < decisionUnit) :
    (linkClient target modes setup codec route env serverKid bounds mode adversary decision).IsQueryBoundP predicate
      (programBound + decisionCost * decisionUnit) :=
  isQueryBoundP_bind (PqxdhRecordLiftCtxBills.run_bound (reduction target modes setup codec) predicate cost step _ programBound program _)
    (fun _ _ => coinForward_route _ predicate _ decisionCost decisionUnit (coins _) coinStep)


/-- The explicit privacy bills: the program's coins plus the decision's coins plus 66 coins per keyed request (two for a
random-mode body and tag, 64 for a private 64-byte commitment fill), the program's shared hashes, one seal and the raw
receives. -/
def privBills : CtxBills where
  uniform input := programBill .uniform input + input.decision + 66 * programBill .hash input
  hash input := programBill .hash input
  seals _ := 1
  raw input := programBill .raw input

/-- The privacy hash bill is the world's shared-hash total, as for the integrity bills. -/
theorem hash_bill (input : BillInput) : privBills.hash input = sharedHashTotal input :=
  PqxdhRecordLiftCtxBills.hash_bill input

section Final
variable (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
  (serverKid : Std.U64) (bounds : FreshBounds)

/-- Every privacy reduction respects the explicit privacy bills. -/
theorem stepBilled : StepBilled (n := n) setup codec route serverKid bounds privBills := by
  intro E X env startup allowance framed mode adversary budget respects decision cost coins step
  have program := fun kind => program_categories kind env startup allowance framed setup.source.crypto codec route
    serverKid bounds mode budget adversary respects cost
  let target := PqxdhRecordLiftChainOrder.entryAt (positions := positions budget) step
  let modes : Label n → KeyMode := privModes (positions budget) step.val
  have uniform := link_route target modes setup codec route env serverKid bounds mode adversary decision UniformRoute _ _
    cost 1 (reduction_uniform target modes setup codec) (program .uniform) coins (fun _ _ => Nat.one_pos)
  have keyed := link_route target modes setup codec route env serverKid bounds mode adversary decision KeyedRoute _ _
    cost 0 (reduction_keyed target modes setup codec) (program .hash) coins
    (fun _ hit => by simp [KeyedRoute, publicCall, SourceUniform] at hit)
  have hash := link_route target modes setup codec route env serverKid bounds mode adversary decision HashRoute _ _
    cost 0 (reduction_hash target modes setup codec) (program .hash) coins
    (fun _ hit => by simp [HashRoute, publicCall, SourceUniform] at hit)
  have sealing := link_route target modes setup codec route env serverKid bounds mode adversary decision
    (TargetClass SourceSeal) _ _ cost 0 (reduction_seal target modes setup codec)
    (program_target_seal target env setup.source.crypto codec route serverKid bounds mode adversary) coins
    (fun _ hit => by simp [TargetClass] at hit)
  have raw := link_route target modes setup codec route env serverKid bounds mode adversary decision
    (TargetClass IsRawQuery) _ _ cost 0 (reduction_raw target modes setup codec) (program .raw) coins
    (fun _ hit => by simp [TargetClass] at hit)
  simp only [Nat.mul_one, Nat.mul_zero, Nat.add_zero] at uniform keyed hash sealing raw
  exact decision_budgets setup.source.crypto _ _ _ _ _ _ uniform keyed hash sealing raw

/-- **`ctx_lift`, privacy half (H-5, item 4).** With the explicit reduction family `privReduction` and the explicit
bills `privBills`, `CtxPrivLiftStatement` holds in both forms: in either observation mode, `idealAuth` and
`randomRecords` (in mode P, `idealRecords`) differ, for every cache-free decision and every Boolean event, by at most
the exact sum over the target key indices of the per-key IND$ losses, each with coefficient one. -/
theorem ctxPrivLiftStatement :
    CtxPrivLiftStatement setup codec route serverKid bounds n (privReduction setup codec route serverKid bounds)
      privBills :=
  ctxPrivLiftStatement_of_billed setup codec route serverKid bounds privBills
    (stepBilled setup codec route serverKid bounds)

end Final

end BeaconcryptCore.Computational.PqxdhRecordLiftCtxPrivBills

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxPrivBills.bytesSample_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxPrivBills.bytesSample_total

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxPrivBills.seal_hash' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxPrivBills.seal_hash

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxPrivBills.seal_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxPrivBills.seal_uniform

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxPrivBills.random_hash_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxPrivBills.random_hash_step

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxPrivBills.random_uniform_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxPrivBills.random_uniform_step

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxPrivBills.known_hash_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxPrivBills.known_hash_step

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxPrivBills.known_uniform_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxPrivBills.known_uniform_step

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxPrivBills.target_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxPrivBills.target_step

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxPrivBills.hash_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxPrivBills.hash_step

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxPrivBills.uniform_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxPrivBills.uniform_step

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxPrivBills.keyed_not_uniform' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxPrivBills.keyed_not_uniform

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxPrivBills.decision_budgets' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxPrivBills.decision_budgets

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxPrivBills.coinForward_route' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxPrivBills.coinForward_route

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxPrivBills.hashForward_route' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxPrivBills.hashForward_route

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxPrivBills.opening_route' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxPrivBills.opening_route

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxPrivBills.sealing_route' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxPrivBills.sealing_route

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxPrivBills.reduction_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxPrivBills.reduction_step

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxPrivBills.reduction_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxPrivBills.reduction_uniform

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxPrivBills.reduction_hash' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxPrivBills.reduction_hash

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxPrivBills.reduction_keyed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxPrivBills.reduction_keyed

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxPrivBills.reduction_seal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxPrivBills.reduction_seal

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxPrivBills.reduction_raw' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxPrivBills.reduction_raw

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxPrivBills.link_route' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxPrivBills.link_route

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxPrivBills.hash_bill' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxPrivBills.hash_bill

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxPrivBills.stepBilled' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxPrivBills.stepBilled

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxPrivBills.ctxPrivLiftStatement' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxPrivBills.ctxPrivLiftStatement
