-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRecordLiftChainHybrid
import BeaconcryptCore.Computational.PqxdhRecordLiftCtxProgramBounds

/-! Query bills of the chain reductions (chain track C4): every explicit full76 observer of the ordered chain hybrid (`PqxdhRecordLiftChainHybrid.observerAt`) makes at most `observerBill input = 2 * programCoins input + 44 + input.decision` uniform queries, where `programCoins` is a closed expression in four fields of `PqxdhRecordLiftIdeal.BillInput`: the outer `Budget` (coins, test, fresh, hashes, sends, receives), the environment's startup coins, its per-class `Frame` allowance and the fresh-message bound. The decision's coin cost enters only through `observerBill`, and the slot count is not read. The bill is derived, not assumed: per-service uniform-draw costs (`coinCost`: a seed allocation 64, a lookup at most one full 76-byte reply, a coin 1, a shared-hash request 64, so a hidden opening, sealing or caller-known operation at most 64) for the private Protocol interpreter under every mixed policy and for both masked interpreters under every supplied child (`protocol_total`, `mask_total`, `seedMask_total`); per-world-request bills in every component ledger (`handler_weighted`, reusing `PqxdhRecordLiftCtxProgramBounds.kernel_send` and `kernel_receive`); the program's static caps from `PqxdhRecordLiftBudget.program_bound` and `program_record_bound` (`interface_weighted`, `program_weighted`, `program_coins`); and the scans that suspend the program at a cut (`lookupScan_*`, `seedScan_*`). The mixed policy's ideal draws are counted as lookups (76 each), so the cap covers every hybrid. No contract is used. -/
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhRecordLiftChainBills
open PqxdhRecordLiftInterface PqxdhRecordLiftProtocol PqxdhFullSecretInputKdf
open PqxdhRecordLiftChainState PqxdhRecordLiftChainTable
open PqxdhServerAuthExperiment (Setup Codec)
open Aeneas beaconcrypt_core ratchet ratchet.concrete
open PqxdhRecordLiftCtxProgramBounds (Weighted)
variable {n : Nat} {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response E X : Type}

/-! ### Weighted total-query transport -/

/-- A total query bound is the weighted bound with unit cost per query. -/
theorem weighted_of_total {κ A : Type} {spec : OracleSpec κ} (work : OracleComp spec A) (bound : Nat)
    (bounded : work.IsTotalQueryBound bound) : Weighted (fun _ => 1) work bound := bounded

/-- The weighted bound with unit cost per query is a total query bound. -/
theorem total_of_weighted {κ A : Type} {spec : OracleSpec κ} (work : OracleComp spec A) (bound : Nat)
    (bounded : Weighted (fun _ => 1) work bound) : work.IsTotalQueryBound bound := bounded

/-- Weighted costs are antitone in the per-query cost. -/
theorem weighted_cost_mono {κ A : Type} {spec : OracleSpec κ} (cost larger : spec.Domain → Nat)
    (client : OracleComp spec A) (bound : Nat) (bounded : Weighted larger client bound)
    (pointwise : ∀ query, cost query ≤ larger query) : Weighted cost client bound := by
  induction client using OracleComp.inductionOn generalizing bound with
  | pure result => trivial
  | query_bind query next ih =>
      rw [Weighted, isQueryBound_query_bind_iff] at bounded ⊢
      refine ⟨(pointwise query).trans bounded.1, fun reply => ?_⟩
      exact PqxdhRecordLiftCtxProgramBounds.weighted_mono _ _ _ _ (ih reply _ (bounded.2 reply))
        (Nat.sub_le_sub_left (pointwise query) _)

/-- Scaling a weighted cost scales the bound. -/
theorem weighted_scale {κ A : Type} {spec : OracleSpec κ} (cost : spec.Domain → Nat) (factor : Nat)
    (client : OracleComp spec A) (bound : Nat) (bounded : Weighted cost client bound) :
    Weighted (fun query => factor * cost query) client (factor * bound) := by
  induction client using OracleComp.inductionOn generalizing bound with
  | pure result => trivial
  | query_bind query next ih =>
      rw [Weighted, isQueryBound_query_bind_iff] at bounded ⊢
      refine ⟨Nat.mul_le_mul_left factor bounded.1, fun reply => ?_⟩
      rw [← Nat.mul_sub]
      exact ih reply _ (bounded.2 reply)

/-- Weighted structural costs transfer through a stateful probabilistic simulation whose every step is total-bounded by its cost. -/
theorem weighted_total {κ State A : Type} {spec : OracleSpec κ} (cost : spec.Domain → Nat)
    (impl : QueryImpl spec (StateT State ProbComp)) (client : OracleComp spec A) (bound : Nat)
    (bounded : Weighted cost client bound)
    (step : ∀ query state, ((impl query).run state).IsTotalQueryBound (cost query)) (state : State) :
    ((simulateQ impl client).run state).IsTotalQueryBound bound := by
  induction client using OracleComp.inductionOn generalizing state bound with
  | pure result => trivial
  | query_bind query next ih =>
      rw [Weighted, isQueryBound_query_bind_iff] at bounded
      rw [simulateQ_query_bind, StateT.run_bind]
      have liftStep : ((liftM (impl query) : StateT State ProbComp _).run state).IsTotalQueryBound (cost query) := by
        simpa [OracleComp.liftM_run_StateT, MonadLift.monadLift] using step query state
      exact (isTotalQueryBound_bind liftStep (fun reply => ih reply.1 _ (bounded.2 reply.1) reply.2)).mono
        (by omega)

/-- Counting coins issues exactly the original uniform queries. -/
theorem countCoin_total {A : Type} (work : ProbComp A) (bound : Nat) (bounded : work.IsTotalQueryBound bound)
    (count : Nat) : ((simulateQ PqxdhRecordLiftWorld.countCoin work).run count).IsTotalQueryBound bound := by
  apply weighted_total (fun _ => 1) _ work bound (weighted_of_total work bound bounded)
  intro query state
  simp only [PqxdhRecordLiftWorld.countCoin, StateT.run, IsTotalQueryBound, isQueryBound_map_iff]
  exact (isQueryBound_query_iff _ _ _ _).2 Nat.one_pos

/-! ### Native primitive bills -/

/-- Uniform-draw cost of one private service: a seed allocation draws 64 bytes, a lookup at most one full 76-byte reply, a coin one draw; a public hash, a hidden opening or sealing and a caller-known operation each make at most one shared-hash call of 64 bytes; charges and publication draw nothing. -/
def coinCost : Service n → Nat
  | .allocate _ => 64
  | .coin _ => 1
  | .lookup _ => 76
  | .charge _ | .publish _ => 0
  | _ => 64

/-- The service cost is the uniform ledger plus 64 per shared-hash call of `PqxdhRecordLiftCtxProtocolBounds.categoryCost`. -/
theorem coinCost_categories (query : Service n) :
    coinCost query = PqxdhRecordLiftCtxProtocolBounds.categoryCost .uniform query +
      64 * PqxdhRecordLiftCtxProtocolBounds.categoryCost .hash query := by
  cases query <;> rfl

/-- One counted native primitive call draws at most 64 bytes, and only for a shared-hash call. -/
theorem primitives_total (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (query : RawCtxMixedOwner.NativeSpec.Domain) (state : PqxdhRecordLiftWorld.Primitive) :
    ((PqxdhRecordLiftWorld.primitives setup codec query).run state).IsTotalQueryBound
      (64 * if RawCtxMixedOwner.callKind query = .hash then 1 else 0) := by
  simp only [PqxdhRecordLiftWorld.primitives, StateT.run, bind_pure_comp, IsTotalQueryBound,
    isQueryBound_map_iff]
  exact countCoin_total _ _ (PqxdhRecordLiftWorldBudget.primitive_uniform_bound setup codec query state.2) _

/-- A logged native program with at most `hashes` shared-hash calls draws at most `64 * hashes` bytes. -/
theorem logged_total {A : Type} (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (work : OracleComp RawCtxMixedOwner.NativeSpec A) (hashes : Nat)
    (bounded : work.IsQueryBoundP (fun query => RawCtxMixedOwner.callKind query = .hash) hashes)
    (state : PqxdhRecordLiftWorld.Primitive × PqxdhRecordLiftLoggedAdapters.Frames) :
    ((simulateQ (PqxdhRecordLiftLoggedAdapters.loggedNative (PqxdhRecordLiftWorld.primitives setup codec))
      work).run state).IsTotalQueryBound (64 * hashes) := by
  rcases state with ⟨primitive, frames⟩
  rw [PqxdhRecordLiftLoggedAdapters.program_logged]
  simp only [IsTotalQueryBound, isQueryBound_map_iff]
  apply weighted_total (fun query => 64 * if RawCtxMixedOwner.callKind query = .hash then 1 else 0)
    _ _ _ ?_ (primitives_total setup codec)
  apply weighted_cost_mono _ _ _ _ (PqxdhRecordLiftCtxProgramBounds.weighted_indicator _ 64 _ hashes
    (PqxdhDeploymentCompileBudget.logged_bound _ work hashes frames bounded))
  intro query
  split_ifs <;> simp

/-- A hidden opening makes at most one shared-hash call, including missing-material and malformed-input rejection. -/
theorem open_hash
    (pending : RawCtxInterpretedOpening.Opening RatchetChain RatchetChain RatchetMaterial RawCtxWholeOwner.OpenContext) :
    (simulateQ RawCtxMixedOwner.receiveAdapter (RawCtxWholeOwner.adapter
      (.inr (RawCtxInterpretedOpening.toNative pending)))).IsQueryBoundP
      (fun query => RawCtxMixedOwner.callKind query = .hash) 1 := by
  simp only [RawCtxMixedOwner.receiveAdapter, QueryImpl.simulateQ_compose]
  apply RawCtxMixedOwner.receiveLift_bound
  have bounded := (RawCtxSourceOpen.owner_primitive_bounds
    (.ReceiveOpenRequested (RawCtxInterpretedOpening.toNative pending))).2.1
  simp only [RawCtxOwnerOracle.program, bind_pure_comp, simulateQ_map, simulateQ_spec_query,
    isQueryBoundP_map_iff, RawCtxSourceOpen.ownerAdapter, QueryImpl.apply_compose] at bounded
  convert bounded using 1
  funext query
  rcases query with request | (bytes | input) <;>
    simp [RawCtxMixedOwner.receiveKind, RawCtxSourceOpen.openingPredicate]

/-- A hidden sealing makes at most one shared-hash call, including invalid-input rejection and writer failure. -/
theorem seal_hash
    (pending : RawCtxInterpretedSend.Seal RatchetMaterial RawCtxSourceSend.SealContext) :
    (simulateQ RawCtxMixedOwner.sendAdapter (RawCtxSourceSend.adapter
      (.inr (RawCtxInterpretedSend.nativeSeal pending)))).IsQueryBoundP
      (fun query => RawCtxMixedOwner.callKind query = .hash) 1 := by
  simp only [RawCtxMixedOwner.sendAdapter, QueryImpl.simulateQ_compose]
  apply RawCtxMixedOwner.sendLift_bound
  simp only [RawCtxSourceSend.adapter, bind_pure_comp, simulateQ_map, liftM,
    simulateQ_spec_query, isQueryBoundP_map_iff, RawCtxSourceSeal.nativeAdapter]
  have inner := RawCtxSourceSeal.sealInput_bound
    (RawCtxSourceSend.arguments (RawCtxInterpretedSend.nativeSeal pending)) .hash
  have bounded := RawCtxSourceSeal.sealLift_bound (fun query => decide (RawCtxSourceSeal.callKind query = .hash))
    _ 1 (by simpa only [decide_eq_true_eq] using inner)
  refine (isQueryBoundP_congr_pred
    (p' := fun query : RawCtxSourceSeal.NativeSpec.Domain =>
      RawCtxSourceSeal.sealingPredicate (fun query => decide (RawCtxSourceSeal.callKind query = .hash)) query = true)
    ?_).2 bounded
  intro query
  rcases query with request | (input | (bytes | frame)) <;>
    simp [RawCtxMixedOwner.sendKind, RawCtxSourceSeal.sealingPredicate, RawCtxSourceSeal.callKind]

/-! ### Per-service bills -/

/-- The persistent seed cache draws at most one 64-byte seed per allocation request. -/
theorem allocation_total (slot : Slot n)
    (state : PqxdhRecordLiftLazyTable.State (PqxdhRecordLiftWorld.SeedSpec n)) :
    ((PqxdhRecordLiftLazyTable.impl slot).run state).IsTotalQueryBound 64 := by
  cases found : state.1 slot with
  | none =>
      rw [PqxdhRecordLiftLazyTable.run_miss slot state found]
      simpa only [IsTotalQueryBound, isQueryBound_map_iff] using PqxdhRecordLiftSeedCut.seed_bound
  | some seed =>
      rw [PqxdhRecordLiftLazyTable.run_hit slot state seed found]
      trivial

set_option maxRecDepth 2048 in
/-- A mixed-policy lookup draws at most one full 76-byte reply: only an ideal miss samples. -/
theorem lookup_total (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (seeds : Seeds (Slot n)) (ideal : Coordinate (Slot n) → Bool) (coordinate : Coordinate (Slot n))
    (state : PqxdhRecordLiftChainCompiler.Execution (Slot n) PqxdhRecordLiftWorld.Primitive) :
    ((PqxdhRecordLiftChainOracle.lookup source seeds ideal coordinate).run state).IsTotalQueryBound 76 := by
  cases selected : ideal coordinate with
  | false =>
      rw [PqxdhRecordLiftChainOracle.lookup_real source seeds ideal coordinate state selected]
      exact isQueryBound_pure _ _ _ _
  | true =>
      cases found : state.1 coordinate with
      | none =>
          rw [PqxdhRecordLiftChainOracle.lookup_miss source seeds ideal coordinate state selected found]
          simpa only [IsTotalQueryBound, isQueryBound_map_iff] using
            CtxComputationalSecurity.uniformFixedBytes_isTotalQueryBound 76
      | some value =>
          rw [PqxdhRecordLiftChainOracle.lookup_hit source seeds ideal coordinate state selected value found]
          exact isQueryBound_pure _ _ _ _

/-- Every service of the private Protocol interpreter, under every mixed policy and from every private state, draws at most its `coinCost`. -/
theorem protocol_total (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (ideal : Coordinate (Slot n) → Bool) (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (query : Service n) (secret : Private n) :
    ((interpreter (PqxdhRecordLiftChainOracle.lookup source · ideal) setup codec query).run secret).IsTotalQueryBound
      (coinCost query) := by
  cases query with
  | allocate slot =>
      simp only [interpreter, sampled, StateT.run, bind_pure_comp, Functor.map_map, IsTotalQueryBound,
        isQueryBound_map_iff]
      exact countCoin_total _ 64 (allocation_total slot secret.seeds) _
  | coin coin =>
      simp only [interpreter, sampled, StateT.run, bind_pure_comp, IsTotalQueryBound, isQueryBound_map_iff]
      exact countCoin_total _ 1 ((isQueryBound_query_iff _ _ _ _).2 Nat.one_pos) _
  | hash bytes =>
      simp only [interpreter, sampled, StateT.run, bind_pure_comp, Functor.map_map, IsTotalQueryBound,
        isQueryBound_map_iff]
      exact countCoin_total _ 64 (CtxComputationalSecurity.ctxRandomOracle_total_query_bound ((), bytes) _) _
  | charge kind => trivial
  | lookup coordinate =>
      simp only [interpreter, withRecord, localInterpreter, PqxdhRecordLiftOpaqueDrivers.interpreter, StateT.run,
        bind_pure_comp, IsTotalQueryBound, isQueryBound_map_iff]
      change (((fun _ => ()) <$> PqxdhRecordLiftLoggedAdapters.liftLookup
        (PqxdhRecordLiftChainOracle.lookup source (cachedSeeds secret) ideal) coordinate :
          StateT (RecordState n) ProbComp Unit).run (recordState secret)).IsTotalQueryBound 76
      rw [StateT.run_map]
      simpa only [PqxdhRecordLiftLoggedAdapters.liftLookup, StateT.run, IsTotalQueryBound, isQueryBound_map_iff,
        recordState] using lookup_total source (cachedSeeds secret) ideal coordinate (secret.chain, secret.primitive)
  | opening pending =>
      simp only [interpreter, withRecord, localInterpreter, PqxdhRecordLiftOpaqueDrivers.interpreter, StateT.run,
        bind_pure_comp, IsTotalQueryBound, isQueryBound_map_iff, PqxdhRecordLiftNativeAdapters.receiveOpen,
        PqxdhRecordLiftWorldCompiler.receiveNative, QueryImpl.simulateQ_compose, recordNative]
      exact logged_total setup codec _ 1 (open_hash _) _
  | sealing pending =>
      simp only [interpreter, withRecord, localInterpreter, PqxdhRecordLiftOpaqueDrivers.interpreter, StateT.run,
        bind_pure_comp, IsTotalQueryBound, isQueryBound_map_iff, PqxdhRecordLiftNativeAdapters.sendSeal,
        PqxdhRecordLiftWorldCompiler.sendNative, QueryImpl.simulateQ_compose, recordNative]
      exact logged_total setup codec _ 1 (seal_hash _) _
  | knownSend kernel context =>
      simp only [interpreter, withRecord, primitiveWork, StateT.run, bind_pure_comp, IsTotalQueryBound,
        isQueryBound_map_iff, PqxdhRecordLiftWorldCompiler.sendNative, QueryImpl.simulateQ_compose, recordNative]
      exact logged_total setup codec _ 1 (PqxdhRecordLiftCtxProtocolBounds.known_send_hash kernel context) _
  | knownReceive kernel target context =>
      simp only [interpreter, withRecord, primitiveWork, StateT.run, bind_pure_comp, IsTotalQueryBound,
        isQueryBound_map_iff, PqxdhRecordLiftWorldCompiler.receiveNative, QueryImpl.simulateQ_compose, recordNative]
      exact logged_total setup codec _ 1 (PqxdhRecordLiftCtxProtocolBounds.known_receive_hash kernel target context) _
  | publish tag => trivial

set_option maxRecDepth 2048 in
/-- The counted full 76-byte sampler draws exactly 76 bytes. -/
theorem sample_total (primitive : PqxdhRecordLiftWorld.Primitive) :
    (PqxdhRecordLiftChainOracle.sample.run primitive).IsTotalQueryBound 76 := by
  simp only [PqxdhRecordLiftChainOracle.sample, StateT.run, bind_pure_comp, IsTotalQueryBound, isQueryBound_map_iff]
  exact countCoin_total _ 76 (CtxComputationalSecurity.uniformFixedBytes_isTotalQueryBound 76) _

set_option maxRecDepth 2048 in
/-- The parent-masked lookup draws at most one full 76-byte reply, for every supplied child. -/
theorem maskedLookup_total (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (seeds : Seeds (Slot n)) (ideal : Coordinate (Slot n) → Bool) (child : FullOutput)
    (coordinate : Coordinate (Slot n))
    (state : PqxdhRecordLiftProjectionCut.Mask (Slot n) × PqxdhRecordLiftWorld.Primitive) :
    ((PqxdhRecordLiftMaskedOracle.lookup source seeds ideal child coordinate).run state).IsTotalQueryBound 76 := by
  change (PqxdhRecordLiftMaskedOracle.lookup source seeds ideal child coordinate state).IsTotalQueryBound 76
  unfold PqxdhRecordLiftMaskedOracle.lookup
  split_ifs
  · exact isQueryBound_pure _ _ _ _
  · split
    · exact isQueryBound_pure _ _ _ _
    · simpa only [bind_pure_comp, IsTotalQueryBound, isQueryBound_map_iff] using sample_total _
  all_goals exact isQueryBound_pure _ _ _ _

/-- Every service of the parent-masked global interpreter draws at most its `coinCost`, for every supplied child. -/
theorem mask_total (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (ideal : Coordinate (Slot n) → Bool) (child : FullOutput) (setup : Setup baseSpec KemSK)
    (codec : Codec Reader Response) (query : Service n) (state : PqxdhRecordLiftGlobalMask.State n) :
    ((PqxdhRecordLiftGlobalMask.interpreter source ideal child setup codec query).run state).IsTotalQueryBound
      (coinCost query) := by
  cases query with
  | allocate slot =>
      simp only [PqxdhRecordLiftGlobalMask.interpreter, PqxdhRecordLiftGlobalMask.sampled, StateT.run,
        bind_pure_comp, Functor.map_map, IsTotalQueryBound, isQueryBound_map_iff]
      exact countCoin_total _ 64 (allocation_total slot state.seeds) _
  | coin coin =>
      simp only [PqxdhRecordLiftGlobalMask.interpreter, PqxdhRecordLiftGlobalMask.sampled, StateT.run,
        bind_pure_comp, IsTotalQueryBound, isQueryBound_map_iff]
      exact countCoin_total _ 1 ((isQueryBound_query_iff _ _ _ _).2 Nat.one_pos) _
  | hash bytes =>
      simp only [PqxdhRecordLiftGlobalMask.interpreter, PqxdhRecordLiftGlobalMask.sampled, StateT.run,
        bind_pure_comp, Functor.map_map, IsTotalQueryBound, isQueryBound_map_iff]
      exact countCoin_total _ 64 (CtxComputationalSecurity.ctxRandomOracle_total_query_bound ((), bytes) _) _
  | charge kind => trivial
  | lookup coordinate =>
      simp only [PqxdhRecordLiftGlobalMask.interpreter, PqxdhRecordLiftGlobalMask.withRecords,
        PqxdhRecordLiftGlobalMask.localInterpreter, PqxdhRecordLiftMaskedOracle.interpreter, StateT.run,
        bind_pure_comp, Functor.map_map, IsTotalQueryBound, isQueryBound_map_iff]
      exact maskedLookup_total source _ ideal child coordinate _
  | opening pending =>
      simp only [PqxdhRecordLiftGlobalMask.interpreter, PqxdhRecordLiftGlobalMask.withRecords,
        PqxdhRecordLiftGlobalMask.localInterpreter, PqxdhRecordLiftMaskedOracle.interpreter, StateT.run,
        bind_pure_comp, Functor.map_map, IsTotalQueryBound, isQueryBound_map_iff,
        PqxdhRecordLiftNativeAdapters.receiveOpen, PqxdhRecordLiftWorldCompiler.receiveNative,
        QueryImpl.simulateQ_compose, recordNative]
      exact logged_total setup codec _ 1 (open_hash _) _
  | sealing pending =>
      simp only [PqxdhRecordLiftGlobalMask.interpreter, PqxdhRecordLiftGlobalMask.withRecords,
        PqxdhRecordLiftGlobalMask.localInterpreter, PqxdhRecordLiftMaskedOracle.interpreter, StateT.run,
        bind_pure_comp, Functor.map_map, IsTotalQueryBound, isQueryBound_map_iff,
        PqxdhRecordLiftNativeAdapters.sendSeal, PqxdhRecordLiftWorldCompiler.sendNative,
        QueryImpl.simulateQ_compose, recordNative]
      exact logged_total setup codec _ 1 (seal_hash _) _
  | knownSend kernel context =>
      simp only [PqxdhRecordLiftGlobalMask.interpreter, PqxdhRecordLiftGlobalMask.nativeWork, StateT.run,
        bind_pure_comp, IsTotalQueryBound, isQueryBound_map_iff, PqxdhRecordLiftWorldCompiler.sendNative,
        QueryImpl.simulateQ_compose, recordNative]
      exact logged_total setup codec _ 1 (PqxdhRecordLiftCtxProtocolBounds.known_send_hash kernel context) _
  | knownReceive kernel target context =>
      simp only [PqxdhRecordLiftGlobalMask.interpreter, PqxdhRecordLiftGlobalMask.nativeWork, StateT.run,
        bind_pure_comp, IsTotalQueryBound, isQueryBound_map_iff, PqxdhRecordLiftWorldCompiler.receiveNative,
        QueryImpl.simulateQ_compose, recordNative]
      exact logged_total setup codec _ 1 (PqxdhRecordLiftCtxProtocolBounds.known_receive_hash kernel target context) _
  | publish tag => trivial

set_option maxRecDepth 2048 in
/-- Every service of the seed-masked global interpreter draws at most its `coinCost`, for every supplied child. -/
theorem seedMask_total (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (ideal : Coordinate (Slot n) → Bool) (filling : PqxdhSecretInputKdf.RootOutput) (child : FullOutput)
    (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (query : Service n)
    (state : PqxdhRecordLiftGlobalSeedCut.Mask n) :
    ((PqxdhRecordLiftGlobalSeedCut.interpreter source ideal filling child setup codec query).run
      state).IsTotalQueryBound (coinCost query) := by
  cases query with
  | allocate slot =>
      change (PqxdhRecordLiftGlobalSeedCut.allocate slot state).IsTotalQueryBound 64
      unfold PqxdhRecordLiftGlobalSeedCut.allocate
      split_ifs
      · exact isQueryBound_pure _ _ _ _
      · simpa only [PqxdhRecordLiftGlobalSeedCut.withPrivate, StateT.run, bind_pure_comp, Functor.map_map,
          IsTotalQueryBound, isQueryBound_map_iff, sampled] using
          countCoin_total _ 64 (allocation_total slot state.before.seeds) _
  | lookup coordinate =>
      change (PqxdhRecordLiftGlobalSeedCut.lookup source ideal filling child coordinate state).IsTotalQueryBound 76
      unfold PqxdhRecordLiftGlobalSeedCut.lookup
      split_ifs
      · split
        · exact isQueryBound_pure _ _ _ _
        · simpa only [bind_pure_comp, IsTotalQueryBound, isQueryBound_map_iff] using sample_total _
      all_goals exact isQueryBound_pure _ _ _ _
  | _ =>
      simp only [PqxdhRecordLiftGlobalSeedCut.interpreter, PqxdhRecordLiftGlobalSeedCut.withPrivate, StateT.run,
        bind_pure_comp, IsTotalQueryBound, isQueryBound_map_iff]
      exact protocol_total source ideal setup codec _ state.before

/-! ### Program bills -/

open PqxdhRecordLiftCtxProtocolBounds (BudgetKind categoryCost)
open PqxdhRecordLiftBudget (RecordKind recordKind WorldEffect WorldRecord)

/-- A single service request is billed by its own cost. -/
theorem weighted_service {A : Type} (cost : Service n → Nat) (query : Service n)
    (next : (ServiceSpec n).Range query → OracleComp (ServiceSpec n) A) (bound : Nat)
    (allowed : cost query ≤ bound) (rest : ∀ reply, Weighted cost (next reply) (bound - cost query)) :
    Weighted cost (((ServiceSpec n).query query : OracleComp (ServiceSpec n) _) >>= next) bound :=
  ⟨allowed, rest⟩

/-- The bill of one restricted environment effect in one component ledger: a coin is one uniform draw, a hidden installation at most one 64-byte seed allocation, a public hash one shared-hash request. -/
def effectBill (kind : BudgetKind) : (EnvEffects n).Domain → Nat
  | .inl _ => match kind with | .uniform => 1 | _ => 0
  | .inr (.installServer _ _ _) | .inr (.installBeacon _ _ _) => match kind with | .uniform => 64 | _ => 0
  | .inr (.hash _) => match kind with | .hash => 1 | _ => 0
  | .inr _ => 0

/-- The bill of one world request in one component ledger: initialization is free, effects pay `effectBill`, records pay the per-operation bill of `PqxdhRecordLiftCtxProgramBounds`. -/
def worldBill (kind : BudgetKind) : (WorldSpec n).Domain → Nat
  | .inl _ => 0
  | .inr (.inl effect) => effectBill kind effect
  | .inr (.inr record) => PqxdhRecordLiftCtxProgramBounds.operationBill kind (recordKind record)

/-- Hidden resolution costs at most one allocation. -/
theorem resolve_weighted (kind : BudgetKind) (role : Role) (ref : KernelRef n) :
    Weighted (categoryCost kind) (resolve role ref) (match kind with | .uniform => 64 | _ => 0) := by
  cases ref with
  | known kernel => trivial
  | hidden slot =>
      refine weighted_service _ (.allocate slot) _ _ ?_ (fun _ => trivial)
      cases kind <;> simp [categoryCost]

/-- Charging an effect counter costs nothing in any component ledger. -/
theorem charge_free (kind : BudgetKind) (effect : EffectKind) : categoryCost (n := n) kind (.charge effect) = 0 := by
  cases kind <;> rfl

/-- Every restricted environment effect stays within its bill in every component ledger. -/
theorem effects_weighted (kind : BudgetKind) (query : (EnvEffects n).Domain) (control : Control n) :
    Weighted (categoryCost kind) ((effects query).run control) (effectBill kind query) := by
  rcases query with coin | capability
  · simp only [effects, StateT.run_bind, StateT.run_lift, bind_assoc, pure_bind]
    refine (isQueryBound_query_bind_iff _ _ _ _ _).2 ⟨by rw [charge_free]; exact Nat.zero_le _, fun _ => ?_⟩
    refine (isQueryBound_query_bind_iff _ _ _ _ _).2 ⟨by cases kind <;> exact le_refl _, fun _ => trivial⟩
  · simp only [effects, StateT.run_bind, StateT.run_lift, bind_assoc, pure_bind]
    refine (isQueryBound_query_bind_iff _ _ _ _ _).2 ⟨by rw [charge_free]; exact Nat.zero_le _, fun _ => ?_⟩
    have free : ∀ query : (EnvEffects n).Domain, categoryCost (n := n) kind (.charge (effectKind query)) = 0 := by
      intro query; cases kind <;> rfl
    rw [free, Nat.sub_zero]
    cases capability with
    | peerPresent keyId => trivial
    | ownerPresent owner => trivial
    | appendOwner sender identity phase => trivial
    | advanceOwner owner phase =>
        simp only [capability, StateT.run]
        split
        · split_ifs <;> trivial
        · trivial
    | installServer keyId identity ref =>
        simp only [capability, installServer, StateT.run]
        split
        · trivial
        · split_ifs
          · refine PqxdhRecordLiftCtxProgramBounds.weighted_mono _ _ _ _
              (PqxdhRecordLiftCtxProgramBounds.weighted_bind _ _ _ _ 0 (resolve_weighted kind .server ref)
                (fun _ => trivial)) ?_
            cases kind <;> exact le_refl _
          · trivial
    | installBeacon owner shell ref =>
        simp only [capability, installBeacon, StateT.run]
        split_ifs
        · refine PqxdhRecordLiftCtxProgramBounds.weighted_mono _ _ _ _
            (PqxdhRecordLiftCtxProgramBounds.weighted_bind _ _ _ _ 0 (resolve_weighted kind .beacon ref)
              (fun _ => trivial)) ?_
          cases kind <;> exact le_refl _
        · trivial
    | hash bytes =>
        simp only [capability, StateT.run_lift]
        refine (isQueryBound_query_bind_iff _ _ _ _ _).2 ⟨by cases kind <;> exact le_refl _, fun _ => trivial⟩

/-- The literal per-record bill of one owner operation. -/
def ownerBill (kind : BudgetKind) (query : RawCtxMixedOwner.SourceSpec.Domain) : Nat :=
  PqxdhRecordLiftCtxProgramBounds.operationBill kind (match query with | .inl _ => .send | .inr _ => .raw)

/-- One owner operation followed by publication stays within its per-record bill, including empty sends, rejected raw input and every optional reply. -/
theorem ownerRun_weighted (kind : BudgetKind) (tag : PqxdhDeploymentInterface.FrameTag) (sender : Aeneas.Std.U64)
    (decode : RawCtxReceive.FrameDecoder) (query : RawCtxMixedOwner.SourceSpec.Domain)
    (owner : PqxdhRecordLiftWorldCompiler.Owner n) :
    Weighted (categoryCost kind) (ownerRun tag sender decode query owner) (ownerBill kind query) := by
  have published : ∀ {A : Type} (result : A), Weighted (categoryCost kind)
      ((liftM ((ServiceSpec n).query (.publish tag)) : OracleComp (ServiceSpec n) Unit) >>= fun _ => pure result) 0 := by
    intro A result
    exact (isQueryBound_query_bind_iff _ _ _ _ _).2 ⟨by cases kind <;> exact le_refl _, fun _ => trivial⟩
  unfold ownerRun
  rcases query with plaintext | raw
  · refine PqxdhRecordLiftCtxProgramBounds.weighted_mono _ _ _ _
      (PqxdhRecordLiftCtxProgramBounds.weighted_bind _ _ _ (ownerBill kind (.inl plaintext)) 0 ?_
        (fun result => published result)) (le_refl _)
    dsimp only [ownerStep, ownerSend]
    split_ifs
    · trivial
    · exact PqxdhRecordLiftCtxProgramBounds.weighted_mono _ _ _ _
        (PqxdhRecordLiftCtxProgramBounds.weighted_bind _ _ _ _ 0
          (PqxdhRecordLiftCtxProgramBounds.kernel_send kind owner.kernel _) (fun _ => trivial)) (by simp [ownerBill])
  · refine PqxdhRecordLiftCtxProgramBounds.weighted_mono _ _ _ _
      (PqxdhRecordLiftCtxProgramBounds.weighted_bind _ _ _ (ownerBill kind (.inr raw)) 0 ?_
        (fun result => published result)) (le_refl _)
    dsimp only [ownerStep, ownerReceive]
    split_ifs
    · trivial
    · split
      · trivial
      · split_ifs
        · exact PqxdhRecordLiftCtxProgramBounds.weighted_mono _ _ _ _
            (PqxdhRecordLiftCtxProgramBounds.weighted_bind _ _ _ _ 0
              (PqxdhRecordLiftCtxProgramBounds.kernel_receive kind owner.kernel _ _) (fun _ => trivial))
            (by simp [ownerBill])
        · trivial

/-- Every world request of the compiled protocol client stays within its bill in every component ledger, for every control state. -/
theorem handler_weighted (kind : BudgetKind) (decode : RawCtxReceive.FrameDecoder)
    (route : RawCtxServerRouting.SenderDecoder) (query : (WorldSpec n).Domain) (control : Control n) :
    Weighted (categoryCost kind) ((handler decode route query).run control) (worldBill kind query) := by
  rcases query with created | (effect | ((send | raw) | ⟨owner, plaintext | raw⟩))
  · simp only [handler, initializeServer, StateT.run]
    split <;> trivial
  · exact effects_weighted kind effect control
  · simp only [handler, serverStep, StateT.run]
    split
    · trivial
    · split
      · trivial
      · exact PqxdhRecordLiftCtxProgramBounds.weighted_mono _ _ _ _
          (PqxdhRecordLiftCtxProgramBounds.weighted_bind _ _ _ _ 0 (ownerRun_weighted kind _ _ _ _ _)
            (fun _ => trivial)) (by simp [ownerBill, worldBill, recordKind])
  · simp only [handler, serverStep, StateT.run]
    split
    · trivial
    · split
      · trivial
      · split
        · trivial
        · exact PqxdhRecordLiftCtxProgramBounds.weighted_mono _ _ _ _
            (PqxdhRecordLiftCtxProgramBounds.weighted_bind _ _ _ _ 0 (ownerRun_weighted kind _ _ _ _ _)
              (fun _ => trivial)) (by simp [ownerBill, worldBill, recordKind])
  · simp only [handler, beaconStep, StateT.run]
    split
    · trivial
    · trivial
    · exact PqxdhRecordLiftCtxProgramBounds.weighted_mono _ _ _ _
        (PqxdhRecordLiftCtxProgramBounds.weighted_bind _ _ _ _ 0 (ownerRun_weighted kind _ _ _ _ _)
          (fun _ => trivial)) (by simp [ownerBill, worldBill, recordKind])
  · simp only [handler, beaconStep, StateT.run]
    split
    · trivial
    · trivial
    · exact PqxdhRecordLiftCtxProgramBounds.weighted_mono _ _ _ _
        (PqxdhRecordLiftCtxProgramBounds.weighted_bind _ _ _ _ 0 (ownerRun_weighted kind _ _ _ _ _)
          (fun _ => trivial)) (by simp [ownerBill, worldBill, recordKind])

open PqxdhDeploymentInterface (Mode ModeSpec FreshBounds Budget)

/-- The finite number of restricted effects of one class that the frozen program can issue: startup coins, direct adversary, test, fresh and public-hash work, and the environment's allowance (`PqxdhRecordLiftBudget.program_bound`). -/
def effectTotal (input : PqxdhRecordLiftIdeal.BillInput) (kind : EffectKind) : Nat :=
  PqxdhRecordLiftBudget.startupCost input.startup kind +
    (PqxdhRecordLiftBudget.directCost input.budget input.fresh kind +
      Caps.envTotal ⟨input.budget, 0⟩ input.allowance kind)

/-- The bill of the whole compiled program in one component ledger, in the fields of the bill input. -/
def programBill (kind : BudgetKind) (input : PqxdhRecordLiftIdeal.BillInput) : Nat :=
  (match kind with | .uniform => 1 | _ => 0) * effectTotal input .coin +
    (match kind with | .hash => 1 | _ => 0) * effectTotal input .hash +
    (match kind with | .uniform => 64 | _ => 0) * effectTotal input .administrative +
    PqxdhRecordLiftCtxProgramBounds.operationBill kind .send * input.budget.sends +
    PqxdhRecordLiftCtxProgramBounds.operationBill kind .raw * input.budget.receives

/-- The world bill is dominated by the class indicators of `PqxdhRecordLiftBudget`. -/
theorem worldBill_classes (kind : BudgetKind) (query : (WorldSpec n).Domain) :
    worldBill kind query ≤
      ((((if WorldEffect .coin query then (match kind with | .uniform => 1 | _ => 0) else 0) +
        (if WorldEffect .hash query then (match kind with | .hash => 1 | _ => 0) else 0)) +
        (if WorldEffect .administrative query then (match kind with | .uniform => 64 | _ => 0) else 0)) +
        (if WorldRecord .send query then PqxdhRecordLiftCtxProgramBounds.operationBill kind .send else 0)) +
        (if WorldRecord .raw query then PqxdhRecordLiftCtxProgramBounds.operationBill kind .raw else 0) := by
  rcases query with created | (effect | record)
  · exact Nat.zero_le _
  · rcases effect with coin | capability
    · cases kind <;> simp [worldBill, effectBill, WorldEffect, WorldRecord, effectKind]
    · cases capability <;> cases kind <;> simp [worldBill, effectBill, WorldEffect, WorldRecord, effectKind]
  · rcases record with (send | raw) | ⟨owner, plaintext | raw⟩ <;>
      simp [worldBill, WorldEffect, WorldRecord, recordKind]

/-- The frozen interface program stays within `programBill` in every component ledger, for every environment within its `Frame` and every adversary within its budget. -/
theorem interface_weighted (kind : BudgetKind) (env : Environment n E) (startup : Nat)
    (allowance : Fin 14 → EffectKind → Nat) (framed : Frame env startup allowance) (crypto : Pqxdh.Crypto)
    (codec : Codec Reader Response) (serverKid : Aeneas.Std.U64) (bounds : FreshBounds) (mode : Mode)
    (budget : Budget) (adversary : OracleComp (ModeSpec mode) X) (respects : budget.Respects adversary)
    (cost : Nat) :
    Weighted (worldBill kind) (PqxdhRecordLiftInterface.program env crypto codec serverKid bounds mode adversary)
      (programBill kind ⟨budget, startup, allowance, bounds, n, cost⟩) := by
  have class_bound := fun effect : EffectKind =>
    PqxdhRecordLiftBudget.program_bound env startup allowance framed crypto codec serverKid bounds mode
      ⟨budget, 0⟩ adversary respects effect
  have combined := PqxdhRecordLiftCtxProgramBounds.weighted_add _ _ _ _ _
    (PqxdhRecordLiftCtxProgramBounds.weighted_add _ _ _ _ _
      (PqxdhRecordLiftCtxProgramBounds.weighted_add _ _ _ _ _
        (PqxdhRecordLiftCtxProgramBounds.weighted_add _ _ _ _ _
          (PqxdhRecordLiftCtxProgramBounds.weighted_indicator _ (match kind with | .uniform => 1 | _ => 0) _ _
            (class_bound .coin))
          (PqxdhRecordLiftCtxProgramBounds.weighted_indicator _ (match kind with | .hash => 1 | _ => 0) _ _
            (class_bound .hash)))
        (PqxdhRecordLiftCtxProgramBounds.weighted_indicator _ (match kind with | .uniform => 64 | _ => 0) _ _
          (class_bound .administrative)))
      (PqxdhRecordLiftCtxProgramBounds.weighted_indicator _ (PqxdhRecordLiftCtxProgramBounds.operationBill kind .send)
        _ _ (PqxdhRecordLiftBudget.program_record_bound env crypto codec serverKid bounds mode budget adversary
          respects .send)))
    (PqxdhRecordLiftCtxProgramBounds.weighted_indicator _ (PqxdhRecordLiftCtxProgramBounds.operationBill kind .raw)
      _ _ (PqxdhRecordLiftBudget.program_record_bound env crypto codec serverKid bounds mode budget adversary
        respects .raw))
  exact weighted_cost_mono _ _ _ _ combined (worldBill_classes kind)

/-- The compiled private-service program stays within `programBill` in every component ledger. -/
theorem program_weighted (kind : BudgetKind) (env : Environment n E) (startup : Nat)
    (allowance : Fin 14 → EffectKind → Nat) (framed : Frame env startup allowance) (crypto : Pqxdh.Crypto)
    (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder) (serverKid : Aeneas.Std.U64)
    (bounds : FreshBounds) (mode : Mode) (budget : Budget) (adversary : OracleComp (ModeSpec mode) X)
    (respects : budget.Respects adversary) (cost : Nat) :
    Weighted (categoryCost kind) (program env crypto codec route serverKid bounds mode adversary)
      (programBill kind ⟨budget, startup, allowance, bounds, n, cost⟩) :=
  PqxdhRecordLiftCtxProgramBounds.weighted_run _ _ _ _ _ initialControl
    (interface_weighted kind env startup allowance framed crypto codec serverKid bounds mode budget adversary
      respects cost)
    (handler_weighted kind codec.frameRead route)

/-- The uniform-draw bill of the whole compiled program: its uniform ledger plus 64 per shared-hash request. -/
def programCoins (input : PqxdhRecordLiftIdeal.BillInput) : Nat :=
  programBill .uniform input + 64 * programBill .hash input

/-- The closed form of the uniform-draw bill: one byte per coin effect, 64 per hash and per administrative effect, 140 per send (one lookup and one sealing) and 3940 per raw receive (51 lookups and one opening). -/
theorem programCoins_closed (input : PqxdhRecordLiftIdeal.BillInput) :
    programCoins input = effectTotal input .coin + 64 * effectTotal input .hash +
      64 * effectTotal input .administrative + 140 * input.budget.sends + 3940 * input.budget.receives := by
  simp only [programCoins, programBill, PqxdhRecordLiftCtxProgramBounds.operationBill,
    PqxdhRecordLiftCtxProgramBounds.lookupCost, PqxdhRecordLiftCtxProgramBounds.sealingCost,
    PqxdhRecordLiftCtxProgramBounds.openingCost]
  omega

/-- The compiled program's services draw at most `programCoins` uniform bytes in total on every path. -/
theorem program_coins (env : Environment n E) (startup : Nat)
    (allowance : Fin 14 → EffectKind → Nat) (framed : Frame env startup allowance) (crypto : Pqxdh.Crypto)
    (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder) (serverKid : Aeneas.Std.U64)
    (bounds : FreshBounds) (mode : Mode) (budget : Budget) (adversary : OracleComp (ModeSpec mode) X)
    (respects : budget.Respects adversary) (cost : Nat) :
    Weighted coinCost (program env crypto codec route serverKid bounds mode adversary)
      (programCoins ⟨budget, startup, allowance, bounds, n, cost⟩) := by
  have combined := PqxdhRecordLiftCtxProgramBounds.weighted_add _ _ _ _ _
    (program_weighted .uniform env startup allowance framed crypto codec route serverKid bounds mode budget
      adversary respects cost)
    (weighted_scale _ 64 _ _ (program_weighted .hash env startup allowance framed crypto codec route serverKid
      bounds mode budget adversary respects cost))
  exact weighted_cost_mono _ _ _ _ combined (fun query => (coinCost_categories query).le)

/-! ### Suspended prefixes -/

/-- Suspending a client at the first lookup of a coordinate cannot increase a weighted bound. -/
theorem lookupScan_weighted {A : Type} (cost : Service n → Nat) (target : Coordinate (Slot n))
    (client : OracleComp (ServiceSpec n) A) (bound : Nat) (bounded : Weighted cost client bound) :
    Weighted cost (PqxdhRecordLiftFirstLookup.scan target client) bound := by
  induction client using OracleComp.inductionOn generalizing bound with
  | pure result => trivial
  | query_bind query next ih =>
      rw [Weighted, isQueryBound_query_bind_iff] at bounded
      cases query with
      | lookup coordinate =>
          change Weighted cost (if coordinate = target then pure (.pending next) else
            (((ServiceSpec n).query (.lookup coordinate) : OracleComp (ServiceSpec n) Unit) >>=
              fun reply => PqxdhRecordLiftFirstLookup.scan target (next reply))) bound
          split_ifs with same
          · trivial
          · exact ⟨bounded.1, fun reply => ih reply _ (bounded.2 reply)⟩
      | _ =>
          change Weighted cost (((ServiceSpec n).query _ : OracleComp (ServiceSpec n) _) >>=
            fun reply => PqxdhRecordLiftFirstLookup.scan target (next reply)) bound
          exact ⟨bounded.1, fun reply => ih reply _ (bounded.2 reply)⟩

/-- The suspended continuation of a supported pending first-lookup cut inherits the client's weighted bound. -/
theorem lookupScan_pending {A State : Type} (cost : Service n → Nat) (target : Coordinate (Slot n))
    (impl : QueryImpl (ServiceSpec n) (StateT State ProbComp)) (client : OracleComp (ServiceSpec n) A)
    (bound : Nat) (bounded : Weighted cost client bound) (state : State)
    (next : Unit → OracleComp (ServiceSpec n) A) (after : State)
    (supported : (PqxdhRecordLiftFirstLookup.Cut.pending next, after) ∈
      support ((simulateQ impl (PqxdhRecordLiftFirstLookup.scan target client)).run state)) :
    Weighted cost (next ()) bound := by
  induction client using OracleComp.inductionOn generalizing state bound with
  | pure result =>
      change (PqxdhRecordLiftFirstLookup.Cut.pending next, after) ∈
        support ((simulateQ impl (pure (PqxdhRecordLiftFirstLookup.Cut.complete result))).run state) at supported
      simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff, Prod.mk.injEq, reduceCtorEq,
        false_and] at supported
  | query_bind query tail ih =>
      rw [Weighted, isQueryBound_query_bind_iff] at bounded
      cases query with
      | lookup coordinate =>
          change (PqxdhRecordLiftFirstLookup.Cut.pending next, after) ∈ support ((simulateQ impl
            (if coordinate = target then pure (.pending tail) else
              (((ServiceSpec n).query (.lookup coordinate) : OracleComp (ServiceSpec n) Unit) >>=
                fun reply => PqxdhRecordLiftFirstLookup.scan target (tail reply)))).run state) at supported
          split_ifs at supported with same
          · simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff, Prod.mk.injEq,
              PqxdhRecordLiftFirstLookup.Cut.pending.injEq] at supported
            rw [supported.1]
            exact PqxdhRecordLiftCtxProgramBounds.weighted_mono _ _ _ _ (bounded.2 ()) (Nat.sub_le _ _)
          · rw [simulateQ_query_bind, StateT.run_bind, mem_support_bind_iff] at supported
            obtain ⟨reply, _, member⟩ := supported
            exact PqxdhRecordLiftCtxProgramBounds.weighted_mono _ _ _ _
              (ih reply.1 _ (bounded.2 reply.1) reply.2 member) (Nat.sub_le _ _)
      | _ =>
          change (PqxdhRecordLiftFirstLookup.Cut.pending next, after) ∈ support ((simulateQ impl
            (((ServiceSpec n).query _ : OracleComp (ServiceSpec n) _) >>=
              fun reply => PqxdhRecordLiftFirstLookup.scan target (tail reply))).run state) at supported
          rw [simulateQ_query_bind, StateT.run_bind, mem_support_bind_iff] at supported
          obtain ⟨reply, _, member⟩ := supported
          exact PqxdhRecordLiftCtxProgramBounds.weighted_mono _ _ _ _
            (ih reply.1 _ (bounded.2 reply.1) reply.2 member) (Nat.sub_le _ _)

/-- Suspending a client at the first allocation of a slot cannot increase a weighted bound. -/
theorem seedScan_weighted {A : Type} (cost : Service n → Nat) (target : Slot n)
    (client : OracleComp (ServiceSpec n) A) (bound : Nat) (bounded : Weighted cost client bound) :
    Weighted cost (PqxdhRecordLiftGlobalSeedCut.scan target client) bound := by
  induction client using OracleComp.inductionOn generalizing bound with
  | pure result => trivial
  | query_bind query next ih =>
      rw [Weighted, isQueryBound_query_bind_iff] at bounded
      cases query with
      | allocate slot =>
          change Weighted cost (if slot = target then pure (.pending next) else
            (((ServiceSpec n).query (.allocate slot) : OracleComp (ServiceSpec n) Unit) >>=
              fun reply => PqxdhRecordLiftGlobalSeedCut.scan target (next reply))) bound
          split_ifs with same
          · trivial
          · exact ⟨bounded.1, fun reply => ih reply _ (bounded.2 reply)⟩
      | _ =>
          change Weighted cost (((ServiceSpec n).query _ : OracleComp (ServiceSpec n) _) >>=
            fun reply => PqxdhRecordLiftGlobalSeedCut.scan target (next reply)) bound
          exact ⟨bounded.1, fun reply => ih reply _ (bounded.2 reply)⟩

/-- The suspended continuation of a supported pending first-allocation cut inherits the client's weighted bound. -/
theorem seedScan_pending {A State : Type} (cost : Service n → Nat) (target : Slot n)
    (impl : QueryImpl (ServiceSpec n) (StateT State ProbComp)) (client : OracleComp (ServiceSpec n) A)
    (bound : Nat) (bounded : Weighted cost client bound) (state : State)
    (next : Unit → OracleComp (ServiceSpec n) A) (after : State)
    (supported : (PqxdhRecordLiftFirstLookup.Cut.pending next, after) ∈
      support ((simulateQ impl (PqxdhRecordLiftGlobalSeedCut.scan target client)).run state)) :
    Weighted cost (next ()) bound := by
  induction client using OracleComp.inductionOn generalizing state bound with
  | pure result =>
      change (PqxdhRecordLiftFirstLookup.Cut.pending next, after) ∈
        support ((simulateQ impl (pure (PqxdhRecordLiftFirstLookup.Cut.complete result))).run state) at supported
      simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff, Prod.mk.injEq, reduceCtorEq,
        false_and] at supported
  | query_bind query tail ih =>
      rw [Weighted, isQueryBound_query_bind_iff] at bounded
      cases query with
      | allocate slot =>
          change (PqxdhRecordLiftFirstLookup.Cut.pending next, after) ∈ support ((simulateQ impl
            (if slot = target then pure (.pending tail) else
              (((ServiceSpec n).query (.allocate slot) : OracleComp (ServiceSpec n) Unit) >>=
                fun reply => PqxdhRecordLiftGlobalSeedCut.scan target (tail reply)))).run state) at supported
          split_ifs at supported with same
          · simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff, Prod.mk.injEq,
              PqxdhRecordLiftFirstLookup.Cut.pending.injEq] at supported
            rw [supported.1]
            exact PqxdhRecordLiftCtxProgramBounds.weighted_mono _ _ _ _ (bounded.2 ()) (Nat.sub_le _ _)
          · rw [simulateQ_query_bind, StateT.run_bind, mem_support_bind_iff] at supported
            obtain ⟨reply, _, member⟩ := supported
            exact PqxdhRecordLiftCtxProgramBounds.weighted_mono _ _ _ _
              (ih reply.1 _ (bounded.2 reply.1) reply.2 member) (Nat.sub_le _ _)
      | _ =>
          change (PqxdhRecordLiftFirstLookup.Cut.pending next, after) ∈ support ((simulateQ impl
            (((ServiceSpec n).query _ : OracleComp (ServiceSpec n) _) >>=
              fun reply => PqxdhRecordLiftGlobalSeedCut.scan target (tail reply))).run state) at supported
          rw [simulateQ_query_bind, StateT.run_bind, mem_support_bind_iff] at supported
          obtain ⟨reply, _, member⟩ := supported
          exact PqxdhRecordLiftCtxProgramBounds.weighted_mono _ _ _ _
            (ih reply.1 _ (bounded.2 reply.1) reply.2 member) (Nat.sub_le _ _)

/-! ### Observer bills -/

/-- The bill of one chain reduction observer: the program's uniform-draw bill for the sampled prefix and again for the suffix, the retained 44 bytes (32 for a seed cut), and the decision's own coins. -/
def observerBill (input : PqxdhRecordLiftIdeal.BillInput) : Nat :=
  2 * programCoins input + 44 + input.decision

/-- The explicit chain bills of the delivered target. -/
def chainBills : PqxdhRecordLiftIdeal.ChainBills := ⟨observerBill⟩

/-- The parent-cut reduction observer of `PqxdhRecordLiftGlobalCut` for the frozen program and a chain decision draws at most the prefix bill, the retained 44 bytes, the suffix bill and the decision's coins. -/
theorem parentObserver_total (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (ideal : Coordinate (Slot n) → Bool) (route : RawCtxServerRouting.SenderDecoder) (env : Environment n E)
    (startup : Nat) (allowance : Fin 14 → EffectKind → Nat) (framed : Frame env startup allowance)
    (serverKid : Aeneas.Std.U64) (bounds : FreshBounds) (mode : Mode) (budget : Budget)
    (adversary : OracleComp (ModeSpec mode) X) (respects : budget.Respects adversary)
    (decision : PqxdhRecordLiftIdeal.View n E X → CtxRomAuth.CtxRO.QueryCache → ProbComp Bool) (cost : Nat)
    (decisionBound : ∀ view cache, (decision view cache).IsTotalQueryBound cost)
    (target : Coordinate (Slot n)) (context : Unit) (output : FullOutput) :
    (PqxdhRecordLiftGlobalCut.reductionObserver setup.source ideal setup codec target
      (program env setup.source.crypto codec route serverKid bounds mode adversary)
      (PqxdhRecordLiftChainHop.finish decision) context output).IsTotalQueryBound
        (programCoins ⟨budget, startup, allowance, bounds, n, cost⟩ +
          (44 + (programCoins ⟨budget, startup, allowance, bounds, n, cost⟩ + cost))) := by
  have weighted := program_coins env startup allowance framed setup.source.crypto codec route serverKid bounds
    mode budget adversary respects cost
  have prefixRun := weighted_total coinCost _ _ _ (lookupScan_weighted coinCost target _ _ weighted)
    (protocol_total setup.source ideal setup codec) initialPrivate
  have prefixBound : (PqxdhRecordLiftFirstLookup.sampledPrefix setup.source ideal setup codec target
      (program env setup.source.crypto codec route serverKid bounds mode adversary)).IsTotalQueryBound
        (programCoins ⟨budget, startup, allowance, bounds, n, cost⟩) := by
    rw [← isQueryBoundP_true_iff]
    exact PqxdhRecordLiftFirstLookup.sampledPrefix_bound setup.source ideal setup codec target _ (fun _ => True) _
      ((isQueryBoundP_true_iff _ _).mpr prefixRun)
  apply PqxdhRecordLiftGlobalCut.reductionObserver_bound _ _ _ _ _ _ _ _ _ prefixBound
  intro reached supported value child
  have member := PqxdhRecordLiftFirstLookupPrefix.sampled_support setup.source ideal setup codec target _ reached
    supported
  rcases reached with ⟨⟨cut, after⟩, missing⟩
  cases cut with
  | complete result =>
      exact (decisionBound _ _).mono (Nat.le_add_left _ _)
  | pending next =>
      exact isTotalQueryBound_bind
        (weighted_total coinCost _ (next ()) _
          (lookupScan_pending coinCost target _ _ _ weighted _ next after member)
          (mask_total setup.source ideal child setup codec) _)
        (fun _ => decisionBound _ _)

/-- The seed-cut reduction observer of `PqxdhRecordLiftGlobalSeedCut` for the frozen program and a chain decision draws at most the prefix bill, the retained 32 bytes, the suffix bill and the decision's coins. -/
theorem seedObserver_total (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (ideal : Coordinate (Slot n) → Bool) (route : RawCtxServerRouting.SenderDecoder) (env : Environment n E)
    (startup : Nat) (allowance : Fin 14 → EffectKind → Nat) (framed : Frame env startup allowance)
    (serverKid : Aeneas.Std.U64) (bounds : FreshBounds) (mode : Mode) (budget : Budget)
    (adversary : OracleComp (ModeSpec mode) X) (respects : budget.Respects adversary)
    (decision : PqxdhRecordLiftIdeal.View n E X → CtxRomAuth.CtxRO.QueryCache → ProbComp Bool) (cost : Nat)
    (decisionBound : ∀ view cache, (decision view cache).IsTotalQueryBound cost)
    (filling : PqxdhSecretInputKdf.RootOutput) (target : Slot n) (direction : Bool)
    (context : Unit) (output : FullOutput) :
    (PqxdhRecordLiftGlobalSeedCut.reductionObserver setup.source ideal filling setup codec target direction
      (program env setup.source.crypto codec route serverKid bounds mode adversary)
      (PqxdhRecordLiftChainHop.finish decision) context output).IsTotalQueryBound
        (programCoins ⟨budget, startup, allowance, bounds, n, cost⟩ +
          (32 + (programCoins ⟨budget, startup, allowance, bounds, n, cost⟩ + cost))) := by
  have weighted := program_coins env startup allowance framed setup.source.crypto codec route serverKid bounds
    mode budget adversary respects cost
  have prefixRun := weighted_total coinCost _ _ _ (seedScan_weighted coinCost target _ _ weighted)
    (protocol_total setup.source ideal setup codec) initialPrivate
  have prefixBound : (PqxdhRecordLiftGlobalSeedCut.sampledPrefix setup.source ideal setup codec target
      (program env setup.source.crypto codec route serverKid bounds mode adversary)).IsTotalQueryBound
        (programCoins ⟨budget, startup, allowance, bounds, n, cost⟩) := by
    rw [← isQueryBoundP_true_iff]
    exact PqxdhRecordLiftGlobalSeedCut.sampledPrefix_bound setup.source ideal setup codec target _ (fun _ => True) _
      ((isQueryBoundP_true_iff _ _).mpr prefixRun)
  apply PqxdhRecordLiftGlobalSeedCut.reductionObserver_bound _ _ _ _ _ _ _ _ _ _ _ prefixBound
  intro reached supported other child
  have member : reached.val ∈ support ((simulateQ (interpreter (PqxdhRecordLiftChainOracle.lookup setup.source ·
      ideal) setup codec) (PqxdhRecordLiftGlobalSeedCut.scan target
        (program env setup.source.crypto codec route serverKid bounds mode adversary))).run initialPrivate) := by
    rw [← PqxdhRecordLiftGlobalSeedCut.prefix_forget, support_map]
    exact ⟨reached, supported, rfl⟩
  rcases reached with ⟨⟨cut, after⟩, missing⟩
  cases cut with
  | complete result =>
      exact (decisionBound _ _).mono (Nat.le_add_left _ _)
  | pending next =>
      exact isTotalQueryBound_bind
        (weighted_total coinCost _ (next ()) _
          (seedScan_pending coinCost target _ _ _ weighted _ next after member)
          (seedMask_total setup.source ideal filling child setup codec) _)
        (fun _ => decisionBound _ _)

/-- Every observer of the ordered chain hybrid draws at most `observerBill` uniform bytes, for every environment within its `Frame`, every adversary within its budget and every decision within its coin cost. -/
theorem observerAt_total (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (env : Environment n E) (startup : Nat)
    (allowance : Fin 14 → EffectKind → Nat) (framed : Frame env startup allowance)
    (serverKid : Aeneas.Std.U64) (bounds : FreshBounds) (mode : Mode) (budget : Budget)
    (adversary : OracleComp (ModeSpec mode) X) (respects : budget.Respects adversary)
    (decision : PqxdhRecordLiftIdeal.View n E X → CtxRomAuth.CtxRO.QueryCache → ProbComp Bool) (cost : Nat)
    (decisionBound : ∀ view cache, (decision view cache).IsTotalQueryBound cost)
    (step : Fin (PqxdhRecordLiftIdeal.hops n budget)) (context : Unit) (output : FullOutput) :
    (PqxdhRecordLiftChainHybrid.observerAt setup codec route env serverKid bounds mode adversary decision budget step
      context output).IsTotalQueryBound (observerBill ⟨budget, startup, allowance, bounds, n, cost⟩) := by
  unfold PqxdhRecordLiftChainHybrid.observerAt PqxdhRecordLiftChainHop.hopObserver
  split_ifs
  · exact (seedObserver_total setup codec _ route env startup allowance framed serverKid bounds mode budget
      adversary respects decision cost decisionBound _ _ _ context output).mono (by simp only [observerBill]; omega)
  · exact (parentObserver_total setup codec _ route env startup allowance framed serverKid bounds mode budget
      adversary respects decision cost decisionBound _ context output).mono (by simp only [observerBill]; omega)

end BeaconcryptCore.Computational.PqxdhRecordLiftChainBills

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftChainBills.weighted_of_total' does not depend on any axioms -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftChainBills.weighted_of_total

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftChainBills.total_of_weighted' does not depend on any axioms -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftChainBills.total_of_weighted

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftChainBills.weighted_cost_mono' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftChainBills.weighted_cost_mono

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftChainBills.weighted_scale' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftChainBills.weighted_scale

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftChainBills.weighted_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftChainBills.weighted_total

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftChainBills.countCoin_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftChainBills.countCoin_total

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftChainBills.coinCost_categories' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftChainBills.coinCost_categories

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftChainBills.primitives_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftChainBills.primitives_total

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftChainBills.logged_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftChainBills.logged_total

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftChainBills.open_hash' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftChainBills.open_hash

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftChainBills.seal_hash' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftChainBills.seal_hash

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftChainBills.allocation_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftChainBills.allocation_total

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftChainBills.lookup_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftChainBills.lookup_total

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftChainBills.protocol_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftChainBills.protocol_total

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftChainBills.sample_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftChainBills.sample_total

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftChainBills.maskedLookup_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftChainBills.maskedLookup_total

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftChainBills.mask_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftChainBills.mask_total

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftChainBills.seedMask_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftChainBills.seedMask_total

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftChainBills.weighted_service' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftChainBills.weighted_service

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftChainBills.resolve_weighted' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftChainBills.resolve_weighted

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftChainBills.charge_free' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftChainBills.charge_free

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftChainBills.effects_weighted' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftChainBills.effects_weighted

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftChainBills.ownerRun_weighted' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftChainBills.ownerRun_weighted

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftChainBills.handler_weighted' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftChainBills.handler_weighted

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftChainBills.worldBill_classes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftChainBills.worldBill_classes

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftChainBills.interface_weighted' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftChainBills.interface_weighted

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftChainBills.program_weighted' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftChainBills.program_weighted

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftChainBills.programCoins_closed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftChainBills.programCoins_closed

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftChainBills.program_coins' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftChainBills.program_coins

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftChainBills.lookupScan_weighted' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftChainBills.lookupScan_weighted

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftChainBills.lookupScan_pending' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftChainBills.lookupScan_pending

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftChainBills.seedScan_weighted' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftChainBills.seedScan_weighted

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftChainBills.seedScan_pending' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftChainBills.seedScan_pending

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftChainBills.parentObserver_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftChainBills.parentObserver_total

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftChainBills.seedObserver_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftChainBills.seedObserver_total

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftChainBills.observerAt_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftChainBills.observerAt_total
