import BeaconcryptCore.Computational.PqxdhServerAuthSourceCosts
import BeaconcryptCore.Computational.PqxdhServerAuthTailCosts
import BeaconcryptCore.Computational.PqxdhServerAuthPendingBudget

/-!
The entire original authentication body has an explicit uniform-query bound from actual eager generation, all primitive/base work and the adaptive source API. Pending-token consumption pays for builds; the original phase flag pays for one finish. The resulting bound instantiates the exact coefficient-one Gap-DH extractor, preserving all challenge, table and source query accounting without an opaque body-cost premise.
-/

open OracleComp OracleSpec
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhServerAuthBodyCosts
open PqxdhJointIdentity PqxdhJointGapDh PqxdhServerAuthExperiment PqxdhServerAuthGapDh
open PqxdhServerAuthSourceCosts PqxdhServerAuthTailCosts PqxdhServerAuthPendingBudget

variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}

/-- Forwarding uniform source work preserves every one of its direct uniform requests. -/
theorem familyCoins_uniform {α : Type} (work : ProbComp α) (count : Nat)
    (bounded : work.IsTotalQueryBound count) :
    (PqxdhServerAuthExperiment.familyCoins work).IsQueryBoundP IsCoinRoot count := by
  exact IsQueryBoundP.simulateQ_of_step bounded.isQueryBoundP
    (fun query _ => (isQueryBoundP_query_iff _ _ _).mpr (fun _ => Nat.one_pos))
    (fun _ absent => (absent trivial).elim)

set_option backward.isDefEq.respectTransparency false in
/-- The full cache computation is lifted as one source computation, preserving all result-dependent continuations. -/
theorem simulate_onCtx {κ α : Type} {spec : OracleSpec κ}
    (impl : QueryImpl spec (StateT (RawCtxSharedPrimitive.SharedState Unit) ProbComp))
    (work : OracleComp spec α) :
    simulateQ (fun query => onCtx (KemSK := KemSK) (impl query)) work =
      onCtx (simulateQ impl work) := by
  induction work using OracleComp.inductionOn with
  | pure value =>
      funext state
      simp [onCtx, familyCoins]
      rfl
  | query_bind query next ih =>
      rw [simulateQ_query_bind]
      simp only [ih]
      funext state
      change (onCtx (impl query) >>= fun value => onCtx (simulateQ impl (next value))).run state =
        (onCtx (simulateQ impl (spec.query query >>= next))).run state
      rw [StateT.run_bind]
      simp only [simulateQ_spec_query, onCtx, familyCoins, StateT.run,
        simulateQ_bind, bind_assoc, pure_bind]
      have expand : (impl query >>= fun value => simulateQ impl (next value)) ((), state.ctx) =
          ((impl query).run ((), state.ctx) >>= fun result => (simulateQ impl (next result.1)).run result.2) := rfl
      rw [expand, simulateQ_bind, bind_assoc]
      apply bind_congr
      rintro ⟨value, ⟨auxiliary, cache⟩⟩
      cases auxiliary
      rfl

/-- Lifting a complete primitive computation preserves its coin bound and all source state. -/
theorem liftCoins_uniform {α : Type} (work : ProbComp α) (count : Nat)
    (bounded : work.IsTotalQueryBound count) (state : GameState KemSK) :
    ((liftCoins work).run state).IsQueryBoundP IsCoinRoot count := by
  change (familyCoins work >>= fun value => pure (value, state)).IsQueryBoundP IsCoinRoot count
  rw [bind_pure_comp, isQueryBoundP_map_iff]
  exact familyCoins_uniform work count bounded

/-- Running a complete shared-cache operation counts its actual direct uniform work. -/
theorem onCtx_uniform {α : Type} (work : StateT (RawCtxSharedPrimitive.SharedState Unit) ProbComp α)
    (count : Nat) (bounded : ∀ cache, (work.run ((), cache)).IsTotalQueryBound count)
    (state : GameState KemSK) :
    ((onCtx work).run state).IsQueryBoundP IsCoinRoot count := by
  change (familyCoins (work.run ((), state.ctx)) >>= fun result =>
    pure (result.1, { state with ctx := result.2.2 })).IsQueryBoundP IsCoinRoot count
  rw [bind_pure_comp, isQueryBoundP_map_iff]
  exact familyCoins_uniform _ count (bounded state.ctx)

/-- Arbitrary original post-root execution through the actual cache lifts as one operation, so the one-hash bill remains 64 rather than paying the callback count. -/
theorem beacon_after_coins (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (prepared : PqxdhPhase2DhMetadata.Prepared Response) (root : Std.Array Std.U8 32#usize)
    (state : GameState KemSK) :
    ((simulateQ (fun query => onCtx (beaconNative setup codec query))
      (PqxdhPhase2DhRootConsumer.afterRoot codec.frameRead prepared root)).run state).IsQueryBoundP IsCoinRoot 64 := by
  rw [simulate_onCtx]
  exact onCtx_uniform _ 64 (fun cache => beacon_after_uniform setup codec prepared root ((), cache)) state

set_option backward.isDefEq.respectTransparency false in
/-- The complete source stage pays the actual single KEM decapsulation and single opening commitment. Its selected root request remains a family query, accounted by the outer table interpreter. -/
theorem stage_coins (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (beaconSeed : IdentitySeed) (caps : KemCaps) (bounded : KemBound setup caps)
    (publicValue : PublicChallenge) (control : pqxdh.BeaconInitSent) (identity : Unit)
    (oneTime : Unit ⊕ ScalarBytes) (kem : KemSK) (raw : Pqxdh.Bytes) (state : GameState KemSK) :
    ((simulateQ (stageImpl setup codec beaconSeed)
      (PqxdhPhase2DhStage.stage publicValue codec.frameRead control identity oneTime kem raw)).run state).IsQueryBoundP
        IsCoinRoot (caps.decapsCost + 64) := by
  have prefixEq : stageImpl setup codec beaconSeed ∘ₛ PqxdhPhase2DhStage.prefixLift =
      liftUnit (KemSK := KemSK) (PqxdhPhase2GapDhSource.prefixImpl setup.beaconDomain
        (beaconAuxUnit setup codec beaconSeed) (fun _ => pure ())) := by
    funext query
    simp only [QueryImpl.apply_compose, PqxdhPhase2DhStage.prefixLift, simulateQ_spec_query, stageImpl]
  unfold PqxdhPhase2DhStage.stage
  simp only [simulateQ_bind, ← QueryImpl.simulateQ_compose, prefixEq, simulateQ_liftUnit, StateT.run_bind]
  apply isQueryBoundP_bind (n := caps.decapsCost) (m := 64)
  · apply liftCoins_uniform
    simpa only [beaconPrefix, StateT.run'_eq, IsTotalQueryBound, isQueryBound_map_iff] using
      beacon_prefix_uniform setup codec beaconSeed caps bounded control identity oneTime kem raw ()
  · rintro ⟨(_ | prepared), current⟩ _
    · simp only [simulateQ_pure]; trivial
    · simp only [PqxdhPhase2DhRootConsumer.tail, PqxdhPhase2DhRootConsumer.root,
        simulateQ_bind, simulateQ_map, simulateQ_spec_query,
        PqxdhPhase2DhRootConsumer.rootLift, PqxdhPhase2DhStage.tailLift,
        stageImpl, beaconFamily, StateT.run_bind, record_run, pure_bind,
        bind_map_left]
      apply isQueryBoundP_bind (n := 0) (m := 64)
      · simp only [forwardFamily, StateT.run_lift, isQueryBoundP_query_bind_iff]
        exact ⟨Or.inl (by simp [IsCoinRoot]), fun _ => by trivial⟩
      · rintro ⟨(_ | value), after⟩ _
        · simp only [Option.map_none, simulateQ_pure]; trivial
        · simp only [Option.map_some, ← QueryImpl.simulateQ_compose]
          have nativeEq : stageImpl setup codec beaconSeed ∘ₛ (PqxdhPhase2DhStage.tailLift ∘ₛ
              PqxdhPhase2DhRootConsumer.nativeLift) = fun query => onCtx (KemSK := KemSK) (beaconNative setup codec query) := by
            funext query
            simp only [QueryImpl.apply_compose, PqxdhPhase2DhRootConsumer.nativeLift,
              PqxdhPhase2DhStage.tailLift, simulateQ_spec_query, stageImpl]
          rw [nativeEq]
          exact beacon_after_coins setup codec prepared _ after

/-- Only the original InitSent state incurs the complete decapsulation/opening bill. Every failed finish still consumes this one-shot opportunity. -/
theorem finish_coins (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (beaconSeed : IdentitySeed) (caps : KemCaps) (bounded : KemBound setup caps)
    (publicValue : PublicChallenge) (raw : Pqxdh.Bytes) (state : GameState KemSK) :
    ((finishOracle setup codec publicValue beaconSeed raw).run state).IsQueryBoundP IsCoinRoot
      ((caps.decapsCost + 64) * initSentFlag state) := by
  simp only [finishOracle, StateT.run_bind, StateT.run_get, pure_bind]
  cases phase : state.beacon.beacon.phase with
  | initSent control prekey oneTime kem =>
      simp only [initSentFlag, phase, Nat.mul_one]
      apply (isQueryBoundP_bind (m := 0)
        (stage_coins setup codec beaconSeed caps bounded publicValue control state.beacon.beacon.identity oneTime kem raw state)
        (fun result _ => by change (pure _ : OracleComp PqxdhJointDhExtractRoot.RootSpec _).IsQueryBoundP IsCoinRoot 0; trivial)).mono (by omega)
  | _ => simp only [phase, initSentFlag]; trivial

/-- The root consumer performs its real erasure/consume callbacks and one family derivation, but no direct random draw. -/
theorem client_coins (index : Nat) (binding : pqxdh.ServerBinding)
    (input : PqxdhServerRootPreparation.Inputs Reader ScalarBytes PeerEncoding) (state : GameState KemSK) :
    ((simulateQ (sessionImpl index) (PqxdhServerRelatedRootConsumer.client binding input)).run state).IsQueryBoundP IsCoinRoot 0 := by
  classical
  unfold PqxdhServerRelatedRootConsumer.client
  simp only [simulateQ_bind, simulateQ_spec_query, sessionImpl, pure_bind]
  split
  · simp only [simulateQ_pure]; trivial
  · simp only [simulateQ_bind, simulateQ_spec_query, sessionImpl, sessionFamily,
      StateT.run_bind, forwardFamily, StateT.run_lift, bind_assoc, pure_bind, record_run]
    rw [isQueryBoundP_query_bind_iff]
    refine ⟨Or.inl (by simp [IsCoinRoot]), fun root => ?_⟩
    cases root <;> simp only [simulateQ_bind, simulateQ_spec_query, sessionImpl,
      simulateQ_pure, StateT.run_bind]
    all_goals trivial

/-- An actual Server accept keeps all three signature verifications and the complete root/token continuation; its direct coin bill is the original scalar sampler plus one encapsulation. -/
theorem accept_coins (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (caps : KemCaps) (bounded : KemBound setup caps) (publicValue : PublicChallenge)
    (raw : Pqxdh.Bytes) (state : GameState KemSK) :
    ((acceptOracle setup codec checks publicValue raw).run state).IsQueryBoundP IsCoinRoot (32 + caps.encapsCost) := by
  simp only [acceptOracle, StateT.run_bind, StateT.run_get, pure_bind]
  apply (isQueryBoundP_bind (m := 0)
    (liftCoins_uniform _ _ (server_prefix_uniform setup codec checks caps bounded raw state.server.consumed) state) ?_).mono (by omega)
  rintro ⟨⟨(_ | input), consumed⟩, current⟩ _
  · simp only [StateT.run_set, pure_bind]; trivial
  · simp only [StateT.run_set, pure_bind, StateT.run_bind]
    apply isQueryBoundP_bind (n := 0) (m := 0) (client_coins _ _ _ _)
    rintro ⟨((_ | token) | error | _), after⟩ _
    all_goals trivial

/-- A present pending token pays for the actual whole build, including failures; absent or consumed handles execute no primitive work. -/
theorem build_coins (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (session : Nat) (payload : Option Pqxdh.Bytes) (state : GameState KemSK) :
    ((buildOracle setup codec checks session payload).run state).IsQueryBoundP IsCoinRoot
      (64 * slotWeight (state.pending session)) := by
  simp only [buildOracle, StateT.run_bind, StateT.run_get, pure_bind]
  cases found : state.pending session with
  | none => trivial
  | some token =>
      simp only [slotWeight, Nat.mul_one, StateT.run_bind]
      apply (isQueryBoundP_bind (m := 0)
        (liftCoins_uniform _ 64 (build_uniform setup codec checks token.pending token.root payload state.server ([], state.ctx)) state)
        (fun result _ => by trivial)).mono (by omega)

/-- A public BLAKE2b request has the same existing 64-byte miss allowance, including cache hits. -/
theorem hash_coins (bytes : Pqxdh.Bytes) (state : GameState KemSK) :
    ((hashOracle bytes).run state).IsQueryBoundP IsCoinRoot 64 := by
  change (familyCoins ((CtxRomAuth.ctxRandomOracle ((), bytes)).run state.ctx) >>= fun result =>
    pure (result.1, { state with ctx := result.2 })).IsQueryBoundP IsCoinRoot 64
  rw [bind_pure_comp, isQueryBoundP_map_iff]
  exact familyCoins_uniform _ 64 (CtxComputationalSecurity.ctxRandomOracle_total_query_bound ((), bytes) state.ctx)

/-- Actual direct uniform cost of one original capability, including stateful refusal. -/
def handlerCoinCost (caps : KemCaps) (query : ServerAuthSpec.Domain) (state : GameState KemSK) : Nat :=
  match query with
  | .inl _ => 1
  | .inr (.accept _) => 32 + caps.encapsCost
  | .inr (.build session _) => 64 * slotWeight (state.pending session)
  | .inr (.finish _) => (caps.decapsCost + 64) * initSentFlag state
  | .inr (.hash _) => 64
  | .inr (.hmac _ _) => 0
  | .inr (.reveal _) => 0

/-- Every original capability has its complete operational uniform bill, from arbitrary input state. -/
theorem handler_coins (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (beaconSeed : IdentitySeed) (caps : KemCaps) (bounded : KemBound setup caps)
    (publicValue : PublicChallenge) (query : ServerAuthSpec.Domain) (state : GameState KemSK) :
    ((authHandler setup codec checks publicValue beaconSeed query).run state).IsQueryBoundP IsCoinRoot
      (handlerCoinCost caps query state) := by
  rcases query with coin | query
  · simp only [authHandler, forwardFamily, StateT.run_lift, isQueryBoundP_query_bind_iff]
    exact ⟨Or.inr Nat.one_pos, fun _ => by trivial⟩
  cases query with
  | accept raw => exact accept_coins setup codec checks caps bounded publicValue raw state
  | build session payload => exact build_coins setup codec checks session payload state
  | finish raw => exact finish_coins setup codec beaconSeed caps bounded publicValue raw state
  | hash bytes => exact hash_coins bytes state
  | hmac key message => exact hmac_costs IsCoinRoot key message state
  | reveal keyId => trivial

/-- Original adversary coin requests require a separate explicit cap; the authentication budget alone does not bound them. -/
def IsAuthCoin (query : ServerAuthSpec.Domain) : Prop := query.isLeft = true
instance : DecidablePred IsAuthCoin := fun query => inferInstanceAs (Decidable (query.isLeft = true))

/-- The three external attempt classes which pay all actual direct source sampling. Builds use consumed pending tokens, and finish uses the original phase flag. -/
def coinClasses : Fin 3 → ServerAuthSpec.Domain → Prop := ![IsAuthCoin, IsAcceptQuery, IsHashQuery]
instance : ∀ i, DecidablePred (coinClasses i) :=
  Fin.cases (inferInstanceAs (DecidablePred IsAuthCoin))
    (Fin.cases (inferInstanceAs (DecidablePred IsAcceptQuery))
      (Fin.cases (inferInstanceAs (DecidablePred IsHashQuery)) (fun i => Fin.elim0 i)))

/-- Each remaining accept pays its full prefix and reserves one possible build. Existing tokens and the one-shot target phase retain their costs. -/
def coinPotential (caps : KemCaps) (budget : Fin 3 → Nat) (state : GameState KemSK) : Nat :=
  budget 0 + (32 + caps.encapsCost + 64) * budget 1 + 64 * budget 2 +
    64 * pendingCount state + (caps.decapsCost + 64) * initSentFlag state

/-- A current token's weight is part of the finite source registry; this consumes the already established operational invariant. -/
theorem pending_weight_le (setup : Setup baseSpec KemSK) (publicValue : PublicChallenge)
    (state : GameState KemSK) (valid : GameInv Reader Response setup publicValue state) (index : Nat) :
    slotWeight (state.pending index) ≤ pendingCount state := by
  cases found : state.pending index with
  | none => exact Nat.zero_le _
  | some token =>
      have cleared := pending_clear state.sessions state.pending index (valid.pendingBelow index token found)
      simp only [found, slotWeight] at cleared
      change 1 ≤ pendingSlots state.sessions state.pending
      omega

/-- Every original capability other than finish preserves the exact one-shot phase flag. -/
theorem handler_flag_quiet (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (beaconSeed : IdentitySeed) (publicValue : PublicChallenge) (query : ServerAuthSpec.Domain)
    (notFinish : ∀ raw, query ≠ .inr (.finish raw)) (state : GameState KemSK)
    (result : ServerAuthSpec.Range query × GameState KemSK)
    (supported : result ∈ support ((authHandler setup codec checks publicValue beaconSeed query).run state)) :
    initSentFlag result.2 = initSentFlag state := by
  unfold initSentFlag
  rw [(authHandler_step codec checks beaconSeed query state result supported).2.2.2.2 notFinish]

/-- The complete immediate cost is covered by the remaining external budget and actual retained tokens/phase. -/
theorem handler_cost_le (setup : Setup baseSpec KemSK) (caps : KemCaps)
    (publicValue : PublicChallenge) (query : ServerAuthSpec.Domain) (state : GameState KemSK)
    (valid : GameInv Reader Response setup publicValue state) (budget : Fin 3 → Nat)
    (positive : ∀ i, coinClasses i query → 0 < budget i) :
    handlerCoinCost caps query state ≤ coinPotential caps budget state := by
  have coinPos : IsAuthCoin query → 0 < budget 0 := positive 0
  have acceptPos : IsAcceptQuery query → 0 < budget 1 := positive 1
  have hashPos : IsHashQuery query → 0 < budget 2 := positive 2
  rcases query with coin | query
  · have pos := coinPos rfl
    simp only [handlerCoinCost, coinPotential]
    omega
  cases query with
  | accept raw =>
      have pos := acceptPos trivial
      have enough := Nat.mul_le_mul_left (32 + caps.encapsCost + 64) pos
      simp only [Nat.mul_one] at enough
      simp only [handlerCoinCost, coinPotential]
      omega
  | build index payload =>
      have enough := Nat.mul_le_mul_left 64 (pending_weight_le setup publicValue state valid index)
      simp only [handlerCoinCost, coinPotential]
      omega
  | finish raw => simp only [handlerCoinCost, coinPotential]; omega
  | hash bytes =>
      have enough := Nat.mul_le_mul_left 64 (hashPos trivial)
      simp only [Nat.mul_one] at enough
      simp only [handlerCoinCost, coinPotential]
      omega
  | hmac key message => exact Nat.zero_le _
  | reveal keyId => exact Nat.zero_le _

/-- Every supported complete source step pays its actual immediate bill and preserves enough potential for the entire adaptive continuation. -/
theorem handler_potential (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (beaconSeed : IdentitySeed) (caps : KemCaps) (publicValue : PublicChallenge)
    (query : ServerAuthSpec.Domain) (state : GameState KemSK)
    (valid : GameInv Reader Response setup publicValue state) (budget : Fin 3 → Nat)
    (positive : ∀ i, coinClasses i query → 0 < budget i)
    (result : ServerAuthSpec.Range query × GameState KemSK)
    (supported : result ∈ support ((authHandler setup codec checks publicValue beaconSeed query).run state)) :
    handlerCoinCost caps query state +
      coinPotential caps (fun i => if coinClasses i query then budget i - 1 else budget i) result.2 ≤
        coinPotential caps budget state := by
  have coinPos : IsAuthCoin query → 0 < budget 0 := positive 0
  have acceptPos : IsAcceptQuery query → 0 < budget 1 := positive 1
  have hashPos : IsHashQuery query → 0 < budget 2 := positive 2
  rcases query with coin | query
  · have same := forward_support _ _ _ supported
    have pos := coinPos rfl
    simp [handlerCoinCost, coinPotential, coinClasses, IsAuthCoin, IsAcceptQuery, IsHashQuery, same]
    omega
  cases query with
  | accept raw =>
      have flag := handler_flag_quiet setup codec checks beaconSeed publicValue (.inr (.accept raw)) (by intro; simp) state result supported
      have added := accept_pending_count setup codec checks publicValue raw state result supported
      have pos := acceptPos trivial
      have decrement : budget 1 - 1 + 1 = budget 1 := by omega
      simp only [handlerCoinCost, coinPotential]
      simp [coinClasses, IsAuthCoin, IsAcceptQuery, IsHashQuery, flag]
      nlinarith
  | build index payload =>
      have flag := handler_flag_quiet setup codec checks beaconSeed publicValue (.inr (.build index payload)) (by intro; simp) state result supported
      have consumed := build_pending_count setup codec checks publicValue index payload state valid result supported
      simp [handlerCoinCost, coinPotential, coinClasses, IsAuthCoin, IsAcceptQuery, IsHashQuery, flag]
      omega
  | finish raw =>
      have inactive := (finish_step codec beaconSeed raw state result supported).2.2.2.1
      have flag := initSentFlag_zero result.2 inactive
      have same := handler_pending_count_quiet setup codec checks publicValue beaconSeed (.inr (.finish raw)) (by simp [IsAcceptQuery]) (by intro; simp) state result supported
      simp [handlerCoinCost, coinPotential, coinClasses, IsAuthCoin, IsAcceptQuery, IsHashQuery, flag, same]
      omega
  | hash bytes =>
      have flag := handler_flag_quiet setup codec checks beaconSeed publicValue (.inr (.hash bytes)) (by intro; simp) state result supported
      have same := handler_pending_count_quiet setup codec checks publicValue beaconSeed (.inr (.hash bytes)) (by simp [IsAcceptQuery]) (by intro; simp) state result supported
      have pos := hashPos trivial
      simp [handlerCoinCost, coinPotential, coinClasses, IsAuthCoin, IsAcceptQuery, IsHashQuery, flag, same]
      omega
  | hmac key message =>
      have flag := handler_flag_quiet setup codec checks beaconSeed publicValue (.inr (.hmac key message)) (by intro; simp) state result supported
      have same := handler_pending_count_quiet setup codec checks publicValue beaconSeed (.inr (.hmac key message)) (by simp [IsAcceptQuery]) (by intro; simp) state result supported
      simp [handlerCoinCost, coinPotential, coinClasses, IsAuthCoin, IsAcceptQuery, IsHashQuery, flag, same]
  | reveal keyId =>
      have flag := handler_flag_quiet setup codec checks beaconSeed publicValue (.inr (.reveal keyId)) (by intro; simp) state result supported
      have same := handler_pending_count_quiet setup codec checks publicValue beaconSeed (.inr (.reveal keyId)) (by simp [IsAcceptQuery]) (by intro; simp) state result supported
      simp [handlerCoinCost, coinPotential, coinClasses, IsAuthCoin, IsAcceptQuery, IsHashQuery, flag, same]

/-- The entire adaptive original API pays its source-dependent potential. Arbitrarily repeated build/finish/reveal/HMAC calls do not require a separate uniform cap because their actual token/phase/family paths are retained. -/
theorem run_coins (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (beaconSeed : IdentitySeed) (caps : KemCaps) (bounded : KemBound setup caps)
    (publicValue : PublicChallenge) {α : Type} (work : OracleComp ServerAuthSpec α)
    (budget : Fin 3 → Nat) (queries : ∀ i, work.IsQueryBoundP (coinClasses i) (budget i))
    (state : GameState KemSK) (valid : GameInv Reader Response setup publicValue state) :
    ((simulateQ (authHandler setup codec checks publicValue beaconSeed) work).run state).IsQueryBoundP
      IsCoinRoot (coinPotential caps budget state) := by
  apply run_potential_invariant (authHandler setup codec checks publicValue beaconSeed)
    (GameInv Reader Response setup publicValue) coinClasses IsCoinRoot (coinPotential caps)
    (fun query before available invariant positive => ?_) work budget queries state valid
  exact ⟨handlerCoinCost caps query before,
    handler_coins setup codec checks beaconSeed caps bounded publicValue query before,
    handler_cost_le setup caps publicValue query before invariant available positive,
    fun result supported => ⟨(authHandler_step codec checks beaconSeed query before result supported).1 invariant,
      handler_potential setup codec checks beaconSeed caps publicValue query before invariant available positive result supported⟩⟩

/-- Closed direct-uniform allowance for the actual API after Phase 1, with empty Server tokens and one target finish. -/
def runCoinBudget (caps : KemCaps) (qCoin Q qHash : Nat) : Nat :=
  qCoin + (32 + caps.encapsCost + 64) * Q + 64 * qHash + caps.decapsCost + 64

/-- Complete source-body allowance: actual Beacon seed and one-time scalar generation, interpreted KEM keygen, and the full adaptive API. -/
def bodyCoinBudget (caps : KemCaps) (qCoin Q qHash : Nat) : Nat :=
  64 + caps.keygenCost + runCoinBudget caps qCoin Q qHash

/-- Empty source setup discharges the complete pending/phase potential; no caller-selected token or repeated-finish resource premise remains. -/
theorem initial_potential (setup : Setup baseSpec KemSK) (publicValue : PublicChallenge)
    (beacon : RawCtxBeaconLifecycle.State Unit (Unit ⊕ ScalarBytes) KemSK)
    (caps : KemCaps) (qCoin Q qHash : Nat) :
    coinPotential caps ![qCoin, Q, qHash] (initialGameState setup publicValue beacon) ≤
      runCoinBudget caps qCoin Q qHash := by
  have flag := initSentFlag_le (initialGameState setup publicValue beacon)
  have multiplied := Nat.mul_le_mul_left (caps.decapsCost + 64) flag
  simp only [Nat.mul_one] at multiplied
  simp [coinPotential, pending_initial, runCoinBudget]
  omega

/-- The concrete original source body discharges the previously explicit direct-coin premise. Honest generation, all KEM/base work, every attempted accept, spent builds, one-shot finish and adversary coins/hashes are included. -/
theorem body_coins (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (caps : KemCaps) (bounded : KemBound setup caps) (adversary : Adversary)
    (qCoin Q qHash : Nat)
    (coins : ∀ input, (adversary input).IsQueryBoundP IsAuthCoin qCoin)
    (accepts : ∀ input, (adversary input).IsQueryBoundP IsAcceptQuery Q)
    (hashes : ∀ input, (adversary input).IsQueryBoundP IsHashQuery qHash)
    (revealed : Option IdentitySeed) (publicValue : PublicChallenge) :
    (body setup codec checks adversary revealed publicValue).IsQueryBoundP IsCoinRoot
      (bodyCoinBudget caps qCoin Q qHash) := by
  unfold body
  refine (isQueryBoundP_bind (n := 32) (m := 32 + caps.keygenCost + runCoinBudget caps qCoin Q qHash)
    (familyCoins_uniform _ 32 (CtxComputationalSecurity.uniformFixedBytes_isTotalQueryBound 32)) fun beaconSeed _ => ?_).mono (by simp [bodyCoinBudget]; omega)
  refine (isQueryBoundP_bind (n := 32) (m := caps.keygenCost + runCoinBudget caps qCoin Q qHash)
    (familyCoins_uniform _ 32 (CtxComputationalSecurity.uniformFixedBytes_isTotalQueryBound 32)) fun oneTime _ => ?_).mono (by omega)
  refine isQueryBoundP_bind
    (familyCoins_uniform _ caps.keygenCost (keygen_uniform setup caps bounded)) fun keys _ => ?_
  refine (isQueryBoundP_bind (n := 0) (m := runCoinBudget caps qCoin Q qHash)
    (familyCoins_uniform _ 0 (phase1_uniform setup codec beaconSeed publicValue oneTime keys.1 keys.2))
    fun published member => ?_).mono (by omega)
  rw [isQueryBoundP_map_iff]
  have invariant := inv_initial setup codec beaconSeed publicValue oneTime keys.1 keys.2 published
    (coins_support _ published member)
  apply (run_coins setup codec checks beaconSeed caps bounded publicValue _ ![qCoin, Q, qHash]
    (fun i => ?_) _ invariant).mono (initial_potential setup publicValue published.2 caps qCoin Q qHash)
  fin_cases i
  · exact coins _
  · exact accepts _
  · exact hashes _

/-- The primitive work remains explicit: one keygen, at most Q encapsulations and one decapsulation, each with its own direct and interpreted base query counts. The other direct draws are 128 + qCoin + 96*Q + 64*qHash. -/
theorem body_budget_expanded (caps : KemCaps) (qCoin Q qHash : Nat) :
    bodyCoinBudget caps qCoin Q qHash =
      128 + qCoin + 96 * Q + 64 * qHash +
      caps.keygenUniform + Q * caps.encapsUniform + caps.decapsUniform +
      caps.baseUniform * (caps.keygenBase + Q * caps.encapsBase + caps.decapsBase) := by
  simp only [bodyCoinBudget, runCoinBudget, KemCaps.keygenCost, KemCaps.encapsCost, KemCaps.decapsCost]
  ring

/-- The exact B6 scan now has a complete source-derived uniform bill, with no opaque body resource premise. -/
theorem scan_uniform (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (caps : KemCaps) (bounded : KemBound setup caps) (adversary : Adversary)
    (qCoin Q qHash qH : Nat)
    (coins : ∀ input, (adversary input).IsQueryBoundP IsAuthCoin qCoin)
    (accepts : ∀ input, (adversary input).IsQueryBoundP IsAcceptQuery Q)
    (hashes : ∀ input, (adversary input).IsQueryBoundP IsHashQuery qHash)
    (rom : ∀ input, (adversary input).IsQueryBoundP IsRomQuery qH)
    (publicValue : PublicChallenge) :
    (scanClient setup codec checks adversary qH publicValue).IsQueryBoundP PqxdhJointGapDh.IsUniform
      (bodyCoinBudget caps qCoin Q qHash + 64 * (qH + Q + 1)) :=
  scanClient_uniform setup codec checks adversary qH Q _ rom accepts publicValue
    (body_coins setup codec checks caps bounded adversary qCoin Q qHash coins accepts hashes none publicValue)

/-- The same constructed B6 extractor has zero challenge signing, its full adaptive scan and final decision bill, and all real source/table randomness. -/
theorem reduction_resources (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (caps : KemCaps) (bounded : KemBound setup caps) (adversary : Adversary)
    (qCoin Q qHash qH : Nat)
    (coins : ∀ input, (adversary input).IsQueryBoundP IsAuthCoin qCoin)
    (accepts : ∀ input, (adversary input).IsQueryBoundP IsAcceptQuery Q)
    (hashes : ∀ input, (adversary input).IsQueryBoundP IsHashQuery qHash)
    (rom : ∀ input, (adversary input).IsQueryBoundP IsRomQuery qH)
    (publicValue : PublicChallenge) :
    (PqxdhJointGapDh.extractor (scanClient setup codec checks adversary qH) publicValue).IsQueryBoundP
        PqxdhJointGapDh.IsSigning 0 ∧
    (PqxdhJointGapDh.extractor (scanClient setup codec checks adversary qH) publicValue).IsQueryBoundP
        PqxdhJointGapDh.IsDecision (2 * qH * (Q + 1) + 2 * (Q + 1) * (qH + Q + 1) + qH) ∧
    (PqxdhJointGapDh.extractor (scanClient setup codec checks adversary qH) publicValue).IsQueryBoundP
        PqxdhJointGapDh.IsUniform (bodyCoinBudget caps qCoin Q qHash + 64 * (qH + Q + 1)) :=
  extractor_resources setup codec checks adversary qH Q _ rom accepts publicValue
    (body_coins setup codec checks caps bounded adversary qCoin Q qHash coins accepts hashes none publicValue)

/-- The ordinary challenger additionally draws its own 32-byte Server identity seed and 32-byte Beacon prekey scalar. -/
theorem reduction_game_uniform (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (caps : KemCaps) (bounded : KemBound setup caps) (adversary : Adversary)
    (qCoin Q qHash qH : Nat)
    (coins : ∀ input, (adversary input).IsQueryBoundP IsAuthCoin qCoin)
    (accepts : ∀ input, (adversary input).IsQueryBoundP IsAcceptQuery Q)
    (hashes : ∀ input, (adversary input).IsQueryBoundP IsHashQuery qHash)
    (rom : ∀ input, (adversary input).IsQueryBoundP IsRomQuery qH) :
    (PqxdhJointGapDh.game setup.joint setup.dh
      (PqxdhJointGapDh.extractor (scanClient setup codec checks adversary qH))).IsTotalQueryBound
        (64 + (bodyCoinBudget caps qCoin Q qHash + 64 * (qH + Q + 1))) :=
  PqxdhServerAuthGapDh.extractor_game_uniform setup codec checks adversary qH Q _ rom accepts
    (fun publicValue => body_coins setup codec checks caps bounded adversary qCoin Q qHash coins accepts hashes none publicValue)

/-- Expanded complete ordinary-game uniform accounting keeps every primitive base callback explicit. -/
theorem reduction_game_budget (caps : KemCaps) (qCoin Q qHash qH : Nat) :
    64 + (bodyCoinBudget caps qCoin Q qHash + 64 * (qH + Q + 1)) =
      256 + qCoin + 160 * Q + 64 * (qHash + qH) +
      caps.keygenUniform + Q * caps.encapsUniform + caps.decapsUniform +
      caps.baseUniform * (caps.keygenBase + Q * caps.encapsBase + caps.decapsBase) := by
  rw [body_budget_expanded]
  ring

end BeaconcryptCore.Computational.PqxdhServerAuthBodyCosts

/-! ## Checked theorem dependencies -/

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthBodyCosts.familyCoins_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthBodyCosts.familyCoins_uniform

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthBodyCosts.simulate_onCtx' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthBodyCosts.simulate_onCtx

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthBodyCosts.liftCoins_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthBodyCosts.liftCoins_uniform

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthBodyCosts.onCtx_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthBodyCosts.onCtx_uniform

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthBodyCosts.beacon_after_coins' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthBodyCosts.beacon_after_coins

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthBodyCosts.stage_coins' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthBodyCosts.stage_coins

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthBodyCosts.finish_coins' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthBodyCosts.finish_coins

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthBodyCosts.client_coins' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthBodyCosts.client_coins

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthBodyCosts.accept_coins' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthBodyCosts.accept_coins

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthBodyCosts.build_coins' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthBodyCosts.build_coins

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthBodyCosts.hash_coins' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthBodyCosts.hash_coins

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthBodyCosts.handler_coins' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthBodyCosts.handler_coins

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthBodyCosts.pending_weight_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthBodyCosts.pending_weight_le

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthBodyCosts.handler_flag_quiet' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthBodyCosts.handler_flag_quiet

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthBodyCosts.handler_cost_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthBodyCosts.handler_cost_le

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthBodyCosts.handler_potential' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthBodyCosts.handler_potential

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthBodyCosts.run_coins' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthBodyCosts.run_coins

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthBodyCosts.initial_potential' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthBodyCosts.initial_potential

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthBodyCosts.body_coins' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthBodyCosts.body_coins

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthBodyCosts.body_budget_expanded' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthBodyCosts.body_budget_expanded

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthBodyCosts.scan_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthBodyCosts.scan_uniform

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthBodyCosts.reduction_resources' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthBodyCosts.reduction_resources

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthBodyCosts.reduction_game_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthBodyCosts.reduction_game_uniform

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthBodyCosts.reduction_game_budget' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthBodyCosts.reduction_game_budget
