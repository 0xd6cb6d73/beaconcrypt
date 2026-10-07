-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhDeploymentServerAuth

/-! Bills of the deployment reductions `R_c` (CE-8). `Weights` gives, for one class of ServerAuth queries, an upper bound on the class indicator of each kind of query. One embedding step issues at most its `stepCost` in the class (`embed_weight`): a coin its coin weight; a local create the coins of the native constructor's two 32-byte draws and KEM generation (`localCreate_uniform`); a local bundle the coins of one 32-byte draw (`bundle_program_uniform`); an accept, build, HMAC, BLAKE2b or reveal its own weight; a finish the ServerAuth finish of the target, or the at most 69 callbacks of a local Beacon's finish (`native_owner_bound`), each with the decapsulation coins, one BLAKE2b query and one HMAC (`localCallbacks_weight`, `simulate_weighted`); a field read nothing. Freezing issues no new query (`freeze_bound`), and the compiled program meets the transported caps of the deployment budget (`compile_full_certified`), so `R_c` issues at most the transported sum of step costs (`reduction_weight`, closed form `sum_stepCost`). For accepts, finishes, BLAKE2b queries, random-oracle HMACs, coins and all queries this gives the caps `qAccept`, `qFinish`, `hashCap`, `romCap`, `coinCap` and `totalCap` (`reduction_caps`), and `ce_a1_billed` is theorem CE-A1 at those caps. The caps hold for every creation index `c` and every input. The HMAC, BLAKE2b and coin caps charge every local finish its full 69-callback allowance; they are upper bounds, not exact counts. -/
open OracleComp OracleSpec CoreModels Aeneas ENNReal
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhDeploymentServerAuthBills
open PqxdhServerAuthExperiment PqxdhServerAuthSourceCosts PqxdhJointIdentity
open PqxdhJointGapDh (ScalarBytes)
open PqxdhDeploymentInterface (FreshBounds ModeSpec Mode Budget)
open PqxdhDeploymentSecrecy (Ledger)
open PqxdhDeploymentCompile (Local)
open PqxdhDeploymentCompileSecrecy (compileFull)
open PqxdhRegistrationJointRevealCosts (SourceKind sourceKind)
open PqxdhDeploymentServerAuthEvent (SourceEntry)
open PqxdhDeploymentServerAuthEmbed (SourceSpec Owner Emb embed freezeImpl freeze dflt stopAt coins forward localCreate
  localBundle localCallbacks localRoot)
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response X Result : Type}

/-! ## Weighted simulation -/

/-- A stateless simulation in which every call issues at most `perCall` queries of a class issues at most `calls * perCall` of them for a program with at most `calls` calls. -/
theorem simulate_weighted {κ κ' α : Type} {spec : OracleSpec κ} {target : OracleSpec κ'}
    (impl : QueryImpl spec (OracleComp target)) (predicate : κ' → Prop) [DecidablePred predicate] (perCall : Nat)
    (step : ∀ query, (impl query).IsQueryBoundP predicate perCall) (program : OracleComp spec α) (calls : Nat)
    (bounded : program.IsTotalQueryBound calls) :
    (simulateQ impl program).IsQueryBoundP predicate (calls * perCall) := by
  induction program using OracleComp.inductionOn generalizing calls with
  | pure value => simp
  | query_bind query next ih =>
      rw [isTotalQueryBound_query_bind_iff] at bounded
      obtain ⟨positive, rest⟩ := bounded
      obtain ⟨fewer, rfl⟩ : ∃ fewer, calls = fewer + 1 := ⟨calls - 1, by omega⟩
      rw [simulateQ_query_bind]
      refine (isQueryBoundP_bind (step query) (fun reply _ => ih reply fewer (by simpa using rest reply))).mono ?_
      rw [Nat.succ_mul]
      omega

/-- Per-query weights of a class of ServerAuth queries: an upper bound for the class indicator of each kind of query. -/
structure Weights (predicate : ServerAuthSpec.Domain → Prop) [DecidablePred predicate] where
  coin : Nat
  accept : Nat
  build : Nat
  finish : Nat
  hmac : Nat
  hash : Nat
  reveal : Nat
  coin_le : ∀ count, (if predicate (.inl count) then 1 else 0) ≤ coin
  accept_le : ∀ raw, (if predicate (.inr (.accept raw)) then 1 else 0) ≤ accept
  build_le : ∀ session payload, (if predicate (.inr (.build session payload)) then 1 else 0) ≤ build
  finish_le : ∀ raw, (if predicate (.inr (.finish raw)) then 1 else 0) ≤ finish
  hmac_le : ∀ key message, (if predicate (.inr (.hmac key message)) then 1 else 0) ≤ hmac
  hash_le : ∀ bytes, (if predicate (.inr (.hash bytes)) then 1 else 0) ≤ hash
  reveal_le : ∀ keyId, (if predicate (.inr (.reveal keyId)) then 1 else 0) ≤ reveal

/-- One ServerAuth query issues at most its weight. -/
theorem query_weight (predicate : ServerAuthSpec.Domain → Prop) [DecidablePred predicate]
    (query : ServerAuthSpec.Domain) (weight : Nat) (bound : (if predicate query then 1 else 0) ≤ weight) {α : Type}
    (f : ServerAuthSpec.Range query → α) :
    (f <$> (ServerAuthSpec.query query : OracleComp ServerAuthSpec _) : OracleComp ServerAuthSpec α).IsQueryBoundP
      predicate weight := by
  rw [isQueryBoundP_map_iff, isQueryBoundP_query_iff]
  intro holds
  simp only [holds, ite_true] at bound
  omega

/-- A lifted ServerAuth query issues at most its weight. -/
theorem lift_weight {σ : Type} (predicate : ServerAuthSpec.Domain → Prop) [DecidablePred predicate]
    (query : ServerAuthSpec.Domain) (weight : Nat) (bound : (if predicate query then 1 else 0) ≤ weight) (state : σ) :
    ((StateT.lift (ServerAuthSpec.query query : OracleComp ServerAuthSpec _) : StateT σ (OracleComp ServerAuthSpec) _).run
      state).IsQueryBoundP predicate weight := by
  simp only [StateT.run_lift, bind_pure_comp]
  exact query_weight predicate query weight bound _

/-- Game coins for a computation with at most `calls` coin draws issue at most `calls` times the coin weight. -/
theorem coins_weight {α : Type} (predicate : ServerAuthSpec.Domain → Prop) [DecidablePred predicate]
    (weights : Weights predicate) (work : ProbComp α) (calls : Nat) (bounded : work.IsTotalQueryBound calls) :
    (coins work).IsQueryBoundP predicate (calls * weights.coin) :=
  simulate_weighted _ predicate weights.coin (fun count => by
    simpa using query_weight predicate (.inl count) weights.coin (weights.coin_le count) id) work calls bounded

/-- Every callback of a local Beacon's finish issues at most the decapsulation coins, one BLAKE2b query and one HMAC. -/
theorem localCallbacks_weight (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (caps : KemCaps)
    (bounded : KemBound setup caps) (predicate : ServerAuthSpec.Domain → Prop) [DecidablePred predicate]
    (weights : Weights predicate)
    (query : (PqxdhBeaconPhase2Publication.NativeSpec IdentitySeed ScalarBytes
      (PqxdhKemIndCca.MlKem768PublicKey × KemSK) IdentitySeed Response).Domain) :
    (localCallbacks setup codec query).IsQueryBoundP predicate
      (caps.decapsCost * weights.coin + weights.hash + weights.hmac) := by
  rcases query with query | ((request | (bytes | input)) | (input | request | response))
  · exact (coins_weight predicate weights _ _
      (PqxdhRegistrationSchedule.preparation_uniform setup codec caps bounded query)).mono (by omega)
  · exact (isQueryBoundP_pure _ _ _).mono (Nat.zero_le _)
  · exact (query_weight predicate (.inr (.hash bytes)) weights.hash (weights.hash_le bytes) _).mono (by omega)
  · exact (isQueryBoundP_pure _ _ _).mono (Nat.zero_le _)
  · exact (query_weight predicate (.inr (.hmac _ _)) weights.hmac (weights.hmac_le _ _) _).mono (by omega)
  · exact (isQueryBoundP_pure _ _ _).mono (Nat.zero_le _)
  · exact (isQueryBoundP_pure _ _ _).mono (Nat.zero_le _)

/-- A local Beacon's creation draws two 32-byte values and generates its KEM pair. -/
theorem localCreate_uniform (setup : Setup baseSpec KemSK) (caps : KemCaps) (bounded : KemBound setup caps)
    (pin : PqxdhBeaconPhase2Preparation.Word32) (keyId : Std.U64) :
    (localCreate setup pin keyId).IsTotalQueryBound (64 + caps.keygenCost) := by
  unfold localCreate
  apply (isTotalQueryBound_bind sampleSeed_uniform_bound (n₂ := 32 + caps.keygenCost) ?_).mono (by omega)
  intro identity
  apply isTotalQueryBound_bind PqxdhJointGapDh.sampleScalar_uniform
  intro prekey
  simpa only [bind_pure_comp, IsTotalQueryBound, isQueryBound_map_iff] using keygen_uniform setup caps bounded

/-- The ServerAuth queries of one embedding step of each source14 kind, in a class with the given weights: a coin its coin weight; a local create the coins of two 32-byte draws and a KEM generation; a local bundle the coins of one 32-byte draw; an accept, build, HMAC, BLAKE2b or reveal its own weight; a finish the ServerAuth finish of the target or the 69 callbacks of a local Beacon's finish, each with the decapsulation coins, one BLAKE2b query and one HMAC; a field read nothing. -/
def stepCost {predicate : ServerAuthSpec.Domain → Prop} [DecidablePred predicate] (weights : Weights predicate)
    (caps : KemCaps) : SourceKind → Nat :=
  Sum.elim ![weights.coin, (64 + caps.keygenCost) * weights.coin, 32 * weights.coin, weights.accept, weights.build,
    weights.finish + 69 * (caps.decapsCost * weights.coin + weights.hash + weights.hmac), weights.hmac, weights.hash,
    weights.reveal] (fun _ => 0)

/-- One embedding step issues at most its step cost in every weighted class. -/
theorem embed_weight (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (caps : KemCaps)
    (bounded : KemBound setup caps) (c : Nat) (input : AuthInput) (predicate : ServerAuthSpec.Domain → Prop)
    [DecidablePred predicate] (weights : Weights predicate) (query : (SourceSpec KemSK).Domain) (emb : Emb KemSK) :
    ((embed setup codec c input query).run emb).IsQueryBoundP predicate (stepCost weights caps (sourceKind query)) := by
  rcases query with (coin | request) | ⟨index, field⟩
  · exact lift_weight predicate (.inl coin) weights.coin (weights.coin_le coin) emb
  · cases request with
    | create pin keyId =>
        rw [PqxdhDeploymentServerAuthLocal.embed_create]
        split
        · exact (isQueryBoundP_pure _ _ _).mono (Nat.zero_le _)
        · rw [isQueryBoundP_map_iff]
          exact coins_weight predicate weights _ _ (localCreate_uniform setup caps bounded pin keyId)
    | bundle index =>
        rw [PqxdhDeploymentServerAuthLocal.embed_bundle]
        split
        · exact (isQueryBoundP_pure _ _ _).mono (Nat.zero_le _)
        · split
          · exact (isQueryBoundP_pure _ _ _).mono (Nat.zero_le _)
          · exact (isQueryBoundP_pure _ _ _).mono (Nat.zero_le _)
        · rw [isQueryBoundP_map_iff]
          exact coins_weight predicate weights _ _
            (PqxdhRegistrationSchedule.bundle_program_uniform setup codec index _)
    | accept raw => exact lift_weight predicate (.inr (.accept raw)) weights.accept (weights.accept_le raw) emb
    | build session payload =>
        exact lift_weight predicate (.inr (.build session payload)) weights.build (weights.build_le session payload) emb
    | finish index raw =>
        rw [PqxdhDeploymentServerAuthLocal.embed_finish]
        split
        · exact (isQueryBoundP_pure _ _ _).mono (Nat.zero_le _)
        · split
          · exact (query_weight predicate (.inr (.finish raw)) weights.finish (weights.finish_le raw) _).mono
              (Nat.le_add_right _ _)
          · exact (isQueryBoundP_pure _ _ _).mono (Nat.zero_le _)
        · rw [isQueryBoundP_map_iff]
          refine (simulate_weighted _ predicate _ (localCallbacks_weight setup codec caps bounded predicate weights) _ 69
            (PqxdhBeaconPhase2Bounds.native_owner_bound codec.frameRead raw _)).mono ?_
          exact Nat.le_add_left _ _
    | hmac key message =>
        exact lift_weight predicate (.inr (.hmac key message)) weights.hmac (weights.hmac_le key message) emb
    | hash bytes => exact lift_weight predicate (.inr (.hash bytes)) weights.hash (weights.hash_le bytes) emb
    | reveal keyId => exact lift_weight predicate (.inr (.reveal keyId)) weights.reveal (weights.reveal_le keyId) emb
  · exact isQueryBoundP_pure _ _ _

/-- Freezing a program issues at most its queries of each kind. -/
theorem freeze_bound {Result : Type} (stop : List (SourceEntry KemSK) → Prop) [DecidablePred stop]
    (program : OracleComp (SourceSpec KemSK) Result) (budget : SourceKind → Nat)
    (bounded : ∀ kind, program.IsQueryBoundP (fun request => sourceKind (KemSK := KemSK) request = kind) (budget kind))
    (kind : SourceKind) :
    (freeze dflt stop program).IsQueryBoundP (fun request => sourceKind (KemSK := KemSK) request = kind)
      (budget kind) := by
  have weighted := FinitePartitionQueryBounds.weighted_bound (sourceKind (KemSK := KemSK))
    (fun other => if other = kind then 1 else 0) budget (freezeImpl dflt stop)
    (fun request => sourceKind (KemSK := KemSK) request = kind) program bounded
    (fun query journal => by
      rw [PqxdhDeploymentServerAuthLocalize.freezeImpl_run]
      split
      · exact isQueryBoundP_pure _ _ _
      · rw [isQueryBoundP_map_iff, isQueryBoundP_query_iff]
        intro same
        simp [same]) []
  simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true] at weighted
  exact weighted

/-- `R_c` issues at most the step costs of the frozen compiled program's transported caps in every weighted class. -/
theorem reduction_weight (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (caps : KemCaps)
    (bounded : KemBound setup caps) (route : RawCtxServerRouting.SenderDecoder) (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) (budget : Budget) (respects : budget.Respects adversary) (c : Nat)
    (predicate : ServerAuthSpec.Domain → Prop) [DecidablePred predicate] (weights : Weights predicate)
    (input : AuthInput) :
    (PqxdhDeploymentServerAuth.reduction (KemSK := KemSK) setup codec route bounds mode adversary c input).IsQueryBoundP
      predicate (∑ kind, stepCost weights caps kind * PqxdhDeploymentCompileCaps.transported bounds budget kind) := by
  unfold PqxdhDeploymentServerAuth.reduction PqxdhDeploymentServerAuthEmbed.adversary
  rw [PqxdhServerAuthApiJournal.query_bound]
  exact FinitePartitionQueryBounds.weighted_bound (sourceKind (KemSK := KemSK)) (stepCost weights caps)
    (PqxdhDeploymentCompileCaps.transported bounds budget) (embed setup codec c input) predicate
    (freeze dflt (stopAt c) (compileFull setup codec route bounds mode adversary))
    (freeze_bound (stopAt c) _ _ (PqxdhDeploymentCompileCaps.compile_full_certified setup codec route bounds mode
      adversary budget respects))
    (fun query emb => embed_weight setup codec caps bounded c input predicate weights query emb) _


/-- The transported step costs in closed form. -/
theorem sum_stepCost {predicate : ServerAuthSpec.Domain → Prop} [DecidablePred predicate] (weights : Weights predicate)
    (caps : KemCaps) (bounds : FreshBounds) (budget : Budget) :
    ∑ kind, stepCost weights caps kind * PqxdhDeploymentCompileCaps.transported bounds budget kind =
      weights.coin * (budget.coin + budget.test + budget.freshBytes bounds) +
      (64 + caps.keygenCost) * weights.coin * budget.create + 32 * weights.coin * budget.bundle +
      weights.accept * budget.accept + weights.build * budget.build +
      (weights.finish + 69 * (caps.decapsCost * weights.coin + weights.hash + weights.hmac)) * budget.finish +
      weights.hmac * budget.hmac + weights.hash * (budget.hash + budget.sends + budget.receives + budget.test + budget.fresh) +
      weights.reveal * (budget.serverSend + budget.serverRaw + budget.test + budget.fresh) := by
  simp [Fintype.sum_sum_type, Fin.sum_univ_succ, stepCost, PqxdhDeploymentCompileCaps.transported]
  ring

/-- Accept queries: weight one on accepts. -/
def acceptWeights : Weights IsAcceptQuery where
  coin := 0
  accept := 1
  build := 0
  finish := 0
  hmac := 0
  hash := 0
  reveal := 0
  coin_le _ := by simp [IsAcceptQuery]
  accept_le _ := by simp [IsAcceptQuery]
  build_le _ _ := by simp [IsAcceptQuery]
  finish_le _ := by simp [IsAcceptQuery]
  hmac_le _ _ := by simp [IsAcceptQuery]
  hash_le _ := by simp [IsAcceptQuery]
  reveal_le _ := by simp [IsAcceptQuery]

/-- Finish queries: weight one on finishes. -/
def finishWeights : Weights PqxdhServerAuthJointIdentityDhBudget.IsFinish where
  coin := 0
  accept := 0
  build := 0
  finish := 1
  hmac := 0
  hash := 0
  reveal := 0
  coin_le _ := by simp [PqxdhServerAuthJointIdentityDhBudget.IsFinish]
  accept_le _ := by simp [PqxdhServerAuthJointIdentityDhBudget.IsFinish]
  build_le _ _ := by simp [PqxdhServerAuthJointIdentityDhBudget.IsFinish]
  finish_le _ := by simp [PqxdhServerAuthJointIdentityDhBudget.IsFinish]
  hmac_le _ _ := by simp [PqxdhServerAuthJointIdentityDhBudget.IsFinish]
  hash_le _ := by simp [PqxdhServerAuthJointIdentityDhBudget.IsFinish]
  reveal_le _ := by simp [PqxdhServerAuthJointIdentityDhBudget.IsFinish]

/-- BLAKE2b queries: weight one on BLAKE2b queries. -/
def hashWeights : Weights IsHashQuery where
  coin := 0
  accept := 0
  build := 0
  finish := 0
  hmac := 0
  hash := 1
  reveal := 0
  coin_le _ := by simp [IsHashQuery]
  accept_le _ := by simp [IsHashQuery]
  build_le _ _ := by simp [IsHashQuery]
  finish_le _ := by simp [IsHashQuery]
  hmac_le _ _ := by simp [IsHashQuery]
  hash_le _ := by simp [IsHashQuery]
  reveal_le _ := by simp [IsHashQuery]

/-- Random-oracle HMAC queries: weight one on HMACs. -/
def romWeights : Weights IsRomQuery where
  coin := 0
  accept := 0
  build := 0
  finish := 0
  hmac := 1
  hash := 0
  reveal := 0
  coin_le _ := by simp [IsRomQuery]
  accept_le _ := by simp [IsRomQuery]
  build_le _ _ := by simp [IsRomQuery]
  finish_le _ := by simp [IsRomQuery]
  hmac_le _ _ := by split_ifs <;> simp
  hash_le _ := by simp [IsRomQuery]
  reveal_le _ := by simp [IsRomQuery]

/-- Coin queries: weight one on coins. -/
def coinWeights : Weights PqxdhServerAuthBodyCosts.IsAuthCoin where
  coin := 1
  accept := 0
  build := 0
  finish := 0
  hmac := 0
  hash := 0
  reveal := 0
  coin_le _ := by split_ifs <;> simp
  accept_le _ := by simp [PqxdhServerAuthBodyCosts.IsAuthCoin]
  build_le _ _ := by simp [PqxdhServerAuthBodyCosts.IsAuthCoin]
  finish_le _ := by simp [PqxdhServerAuthBodyCosts.IsAuthCoin]
  hmac_le _ _ := by simp [PqxdhServerAuthBodyCosts.IsAuthCoin]
  hash_le _ := by simp [PqxdhServerAuthBodyCosts.IsAuthCoin]
  reveal_le _ := by simp [PqxdhServerAuthBodyCosts.IsAuthCoin]

/-- All queries: weight one everywhere. -/
def totalWeights : Weights (fun _ : ServerAuthSpec.Domain => True) where
  coin := 1
  accept := 1
  build := 1
  finish := 1
  hmac := 1
  hash := 1
  reveal := 1
  coin_le _ := by simp
  accept_le _ := by simp
  build_le _ _ := by simp
  finish_le _ := by simp
  hmac_le _ _ := by simp
  hash_le _ := by simp
  reveal_le _ := by simp

/-- `R_c`'s BLAKE2b cap at the transported deployment budget. -/
def hashCap (budget : Budget) : Nat :=
  (budget.hash + budget.sends + budget.receives + budget.test + budget.fresh) + 69 * budget.finish

/-- `R_c`'s random-oracle HMAC cap at the transported deployment budget. -/
def romCap (budget : Budget) : Nat := budget.hmac + 69 * budget.finish

/-- `R_c`'s coin cap at the transported deployment budget. -/
def coinCap (caps : KemCaps) (bounds : FreshBounds) (budget : Budget) : Nat :=
  (budget.coin + budget.test + budget.freshBytes bounds) + (64 + caps.keygenCost) * budget.create + 32 * budget.bundle +
    69 * caps.decapsCost * budget.finish

/-- `R_c`'s total query cap at the transported deployment budget. -/
def totalCap (caps : KemCaps) (bounds : FreshBounds) (budget : Budget) : Nat :=
  (budget.coin + budget.test + budget.freshBytes bounds) + (64 + caps.keygenCost) * budget.create + 32 * budget.bundle +
    budget.accept + budget.build + (1 + 69 * (caps.decapsCost + 2)) * budget.finish + budget.hmac +
    (budget.hash + budget.sends + budget.receives + budget.test + budget.fresh) +
    (budget.serverSend + budget.serverRaw + budget.test + budget.fresh)

/-- Bills of `R_c` from the deployment budget: for a budget-respecting adversary, `R_c` makes at most `qAccept` accepts, `qFinish` finishes, `hashCap` BLAKE2b queries, `romCap` random-oracle HMACs, `coinCap` coins and `totalCap` queries in all. -/
theorem reduction_caps (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (caps : KemCaps)
    (bounded : KemBound setup caps) (route : RawCtxServerRouting.SenderDecoder) (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) (budget : Budget) (respects : budget.Respects adversary) (c : Nat) :
    PqxdhDeploymentServerAuth.ReductionCaps
      (PqxdhDeploymentServerAuth.reduction (KemSK := KemSK) setup codec route bounds mode adversary c)
      (coinCap caps bounds budget) budget.accept (romCap budget) (hashCap budget) (totalCap caps bounds budget)
      budget.finish := by
  have weight := fun {predicate : ServerAuthSpec.Domain → Prop} [DecidablePred predicate]
      (weights : Weights predicate) (input : AuthInput) =>
    (reduction_weight setup codec caps bounded route bounds mode adversary budget respects c predicate weights input)
  refine ⟨⟨fun input => ?_, fun input => ?_, fun input => ?_⟩, fun input => ?_, fun input => ?_, fun input => ?_⟩
  · refine (weight acceptWeights input).mono (le_of_eq ?_)
    rw [sum_stepCost]
    simp [acceptWeights]
  · refine (weight romWeights input).mono (le_of_eq ?_)
    rw [sum_stepCost]
    simp [romWeights, romCap]
    ring
  · refine (weight hashWeights input).mono (le_of_eq ?_)
    rw [sum_stepCost]
    simp [hashWeights, hashCap]
    ring
  · refine (weight coinWeights input).mono (le_of_eq ?_)
    rw [sum_stepCost]
    simp [coinWeights, coinCap]
  · refine (isQueryBoundP_true_iff _ _).mp ((weight totalWeights input).mono (le_of_eq ?_))
    rw [sum_stepCost]
    simp [totalWeights, totalCap]
  · refine (weight finishWeights input).mono (le_of_eq ?_)
    rw [sum_stepCost]
    simp [finishWeights]


set_option linter.deprecated false in
/-- Theorem CE-A1 at the transported deployment budget: `PqxdhDeploymentServerAuth.ce_a1` with the query caps of every `R_c` discharged from the deployment budget (`reduction_caps`). For a budget-respecting adversary, the probability that some Beacon pinned to the constructed Server accepted with no session that matches it with that pin (`A1NoPinnedMatch`), on a run with `NoBundleFailure_c`, is at most the sum over the `qCreate` creation indices `c` of the Server-authentication bound of `R_c` at `Q = qAccept`, `qH = romCap`, `qHash = hashCap` and `qCoin = coinCap`, with every reduction's bills at those caps, `qTotal = totalCap` and `qFinish = qFinish`. -/
theorem ce_a1_billed (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks) (caps : KemCaps)
    (bounded : KemBound setup caps) (route : RawCtxServerRouting.SenderDecoder) {A : Type}
    (ensureInit : StateT A ProbComp Bool) (identityIndex : Nat)
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec)
    (frameBack : PqxdhServerAuthNegativeControl.FrameReadBack codec)
    (writable : PqxdhFirstBeaconRecordCanonical.ReadWritable codec.frameWrite codec.frameRead)
    (law : PqxdhServerAuthAssumptions.X25519ClassLaw setup.source.crypto)
    (spread : PqxdhServerAuthAssumptions.X25519ScalarSpread setup.source.crypto)
    (correct : PqxdhFullSecretInputKdf.SourceFullCorrect setup.source setup.hmac)
    (adapter : PqxdhEd25519EufCma.HasAttachedVerificationAdapter
      (fun identity => setup.source.crypto.verify identity.toList) setup.joint.verify)
    (bounds : FreshBounds) (mode : Mode) (adversary : OracleComp (ModeSpec mode) X) (budget : Budget)
    (respects : budget.Respects adversary) (runtime : A)
    (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery) (signatureFallback : PqxdhJointIdentity.Forgery) :
    (𝒟[(fun outcome => @decide (∃ c, PqxdhDeploymentServerAuth.A1NoPinnedMatch setup codec c outcome)
        (Classical.propDecidable _)) <$>
      (PqxdhDeploymentSecrecy.game setup codec checks route ensureInit identityIndex bounds mode adversary).run runtime]
        {true}).toReal ≤
      ∑ c : Fin budget.create, PqxdhDeploymentServerAuth.serverAuthBound setup codec checks caps
        (PqxdhDeploymentServerAuth.serverAuthAdversary setup codec route bounds mode adversary c)
        (coinCap caps bounds budget) budget.accept (romCap budget) (hashCap budget) fallback signatureFallback ∧
    ∀ c, PqxdhServerAuthCommonAuthentication.ReductionBills setup codec checks caps
      (PqxdhDeploymentServerAuth.serverAuthAdversary setup codec route bounds mode adversary c)
      (coinCap caps bounds budget) budget.accept (romCap budget) (hashCap budget) (totalCap caps bounds budget)
      budget.finish fallback signatureFallback :=
  PqxdhDeploymentServerAuth.ce_a1 setup codec checks caps bounded route ensureInit identityIndex phase1 phase2 frameBack
    writable law spread correct adapter bounds mode adversary budget respects runtime _ _ _ _ _ _
    (fun c => reduction_caps setup codec caps bounded route bounds mode adversary budget respects c) fallback
    signatureFallback


end BeaconcryptCore.Computational.PqxdhDeploymentServerAuthBills

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentServerAuthBills.simulate_weighted' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentServerAuthBills.simulate_weighted

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentServerAuthBills.query_weight' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentServerAuthBills.query_weight

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentServerAuthBills.lift_weight' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentServerAuthBills.lift_weight

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentServerAuthBills.coins_weight' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentServerAuthBills.coins_weight

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentServerAuthBills.localCallbacks_weight' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentServerAuthBills.localCallbacks_weight

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentServerAuthBills.localCreate_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentServerAuthBills.localCreate_uniform

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentServerAuthBills.embed_weight' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentServerAuthBills.embed_weight

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentServerAuthBills.freeze_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentServerAuthBills.freeze_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentServerAuthBills.reduction_weight' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentServerAuthBills.reduction_weight

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentServerAuthBills.sum_stepCost' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentServerAuthBills.sum_stepCost

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentServerAuthBills.reduction_caps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentServerAuthBills.reduction_caps

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentServerAuthBills.ce_a1_billed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentServerAuthBills.ce_a1_billed
