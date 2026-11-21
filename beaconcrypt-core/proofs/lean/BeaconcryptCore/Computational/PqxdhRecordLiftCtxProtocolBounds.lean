-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRecordLiftCtxProtocol
import BeaconcryptCore.Computational.PqxdhRecordLiftMixedRecords

/-! Actual global CTX service accounting retains the source's functional KDF work and separately charges every ordinary endpoint request, including public and caller-known work. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhRecordLiftCtxProtocolBounds
open PqxdhRecordLiftInterface PqxdhRecordLiftProtocol PqxdhRecordLiftCtxProtocol
open PqxdhRecordLiftCtxServices PqxdhRecordLiftLoggedAdapters
open CtxRomAuth AdaptiveCtxReceive AdaptiveCtxSharedModes AdaptiveCtxDynamicKnownKeys
variable {n : Nat} {Result Reader Response : Type}

/-- The entire source caller-known receive makes at most one hash request, including cached/future failure, commitment rejection and optional opening. -/
theorem known_receive_hash (kernel : ConcreteRatchetKernel) (target : Std.U64)
    (context : RawCtxWholeOwner.OpenContext) :
    (simulateQ RawCtxMixedOwner.receiveAdapter (simulateQ RawCtxWholeOwner.adapter
      (RawCtxOwnerOracle.receive kernel target context))).IsQueryBoundP
        (fun query => RawCtxMixedOwner.callKind query = .hash) 1 := by
  simp only [RawCtxMixedOwner.receiveAdapter, QueryImpl.simulateQ_compose, RawCtxOwnerOracle.receive]
  apply RawCtxMixedOwner.receiveLift_bound
  have bounded := (RawCtxSourceOpen.owner_primitive_bounds (RawCtxOwnerOracle.begin kernel target context)).2.1
  simp only [RawCtxSourceOpen.ownerAdapter, QueryImpl.simulateQ_compose] at bounded
  convert bounded using 1
  funext query
  rcases query with request | (bytes | input) <;>
    simp [RawCtxMixedOwner.receiveKind, RawCtxSourceOpen.openingPredicate]

/-- The entire source caller-known send makes at most one shared hash request, retaining both AEAD and writer work separately. -/
theorem known_send_hash (kernel : ConcreteRatchetKernel) (context : RawCtxSourceSend.SealContext) :
    (simulateQ RawCtxMixedOwner.sendAdapter (simulateQ RawCtxSourceSend.adapter
      (RawCtxSourceSend.send kernel context))).IsQueryBoundP
        (fun query => RawCtxMixedOwner.callKind query = .hash) 1 := by
  simp only [RawCtxMixedOwner.sendAdapter, QueryImpl.simulateQ_compose]
  apply RawCtxMixedOwner.sendLift_bound
  convert RawCtxSourceSeal.nativeAdapter_seal_bound _ 1
    (RawCtxSourceSend.selected_bounds kernel context).2 .hash using 1
  funext query
  rcases query with request | (input | (bytes | frame)) <;>
    simp [RawCtxMixedOwner.sendKind, RawCtxSourceSeal.category, RawCtxSourceSeal.sealingPredicate,
      RawCtxSourceSeal.callKind]

/-- Real KDF/AEAD and writer calls remain in the native program; the ROM presentation issues exactly its counted shared-hash requests. -/
theorem knownRom_total (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (writer : RawCtxMixedShared.Writer) (work : OracleComp RawCtxMixedOwner.NativeSpec Result)
    (bound : Nat) (bounded : work.IsQueryBoundP (fun query => RawCtxMixedOwner.callKind query = .hash) bound)
    (frames : Frames) :
    ((simulateQ (knownRom source writer) work).run frames).IsTotalQueryBound bound := by
  rw [← isQueryBoundP_true_iff]
  apply bounded.simulateQ_run_StateT_of_step
  rintro (request | (input | (input | (bytes | frame)))) before
  all_goals simp [knownRom, RawCtxMixedOwner.callKind, StateT.run, StateT.lift, OracleSpec.query]
  all_goals first
    | exact True.intro
    | exact (isQueryBoundP_query_iff (fun _ => True) ((), bytes) 1).mpr (by simp)

/-- Caller-known native work forwards one ordinary endpoint request per source hash and no request for its public functional primitive evaluation. -/
theorem knownProgram_total (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (writer : RawCtxMixedShared.Writer) (work : OracleComp RawCtxMixedOwner.NativeSpec Result)
    (bound : Nat) (bounded : work.IsQueryBoundP (fun query => RawCtxMixedOwner.callKind query = .hash) bound)
    (frames : Frames) :
    ((knownProgram source writer work).run frames).IsTotalQueryBound bound := by
  apply (knownRom_total source writer work bound bounded frames).simulateQ_of_step
  intro query
  simp [publicRom, QueryImpl.compose, RawCtxSelectedSealConsumer.liftSelected,
    AdaptiveCtxSharedTarget.forward, RawCtxSelectedMessageSealing.hashLift, IsTotalQueryBound]

/-- The actual persistent initial-seed service draws at most 64 bytes; every hit retains its previous answer and draws no bytes. -/
theorem allocation_total (slot : Slot n)
    (state : PqxdhRecordLiftLazyTable.State (PqxdhRecordLiftWorld.SeedSpec n)) :
    (simulateQ PqxdhRecordLiftCtxOracle.coinLift ((PqxdhRecordLiftLazyTable.impl slot).run state)).IsTotalQueryBound 64 := by
  cases found : state.1 slot with
  | none =>
      rw [PqxdhRecordLiftLazyTable.run_miss slot state found, simulateQ_map]
      simp only [IsTotalQueryBound, isQueryBound_map_iff]
      exact PqxdhRecordLiftSeedCut.seed_bound.simulateQ_of_step (by
        intro query
        simp [PqxdhRecordLiftCtxOracle.coinLift, IsTotalQueryBound])
  | some seed =>
      rw [PqxdhRecordLiftLazyTable.run_hit slot state seed found, simulateQ_pure]
      trivial

/-- Per-service endpoint cost, including all public and caller-known work. These are upper bounds; cache hits can cost less. -/
def serviceCost : Service n → Nat
  | .allocate _ => 64
  | .lookup _ => 76
  | .charge _ | .publish _ => 0
  | _ => 1

/-- Every one of the ten actual global CTX services has its explicit endpoint bill; no arbitrary native continuation is assigned a zero bound. -/
theorem service_total (slot : Nat) (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (ideal : PqxdhRecordLiftChainState.Coordinate (Slot n) → Bool)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (query : Service n) (state : Secret n) :
    ((ctxInterpreter slot source ideal codec query).run.run state).IsTotalQueryBound (serviceCost query) := by
  cases query with
  | lookup coordinate =>
      simpa only [ctxInterpreter, withLocal, ExceptT.run, ExceptT.mk, StateT.run, bind_pure_comp,
        IsTotalQueryBound, isQueryBound_map_iff, serviceCost] using
        PqxdhRecordLiftCtxOracle.interpreter_total slot source (seedAt state) ideal codec (.inl coordinate)
          (state.masked, state.pending)
  | opening pending =>
      simpa only [ctxInterpreter, withLocal, ExceptT.run, ExceptT.mk, StateT.run, bind_pure_comp,
        IsTotalQueryBound, isQueryBound_map_iff, serviceCost] using
        PqxdhRecordLiftCtxOracle.interpreter_total slot source (seedAt state) ideal codec (.inr (.inl pending))
          (state.masked, state.pending)
  | sealing pending =>
      simpa only [ctxInterpreter, withLocal, ExceptT.run, ExceptT.mk, StateT.run, bind_pure_comp,
        IsTotalQueryBound, isQueryBound_map_iff, serviceCost] using
        PqxdhRecordLiftCtxOracle.interpreter_total slot source (seedAt state) ideal codec (.inr (.inr pending))
          (state.masked, state.pending)
  | knownSend kernel context =>
      simpa only [ctxInterpreter, withKnown, ExceptT.run, ExceptT.mk, StateT.run, bind_pure_comp,
        IsTotalQueryBound, isQueryBound_map_iff, serviceCost] using
        knownProgram_total source codec.frameWrite _ 1 (known_send_hash kernel context) state.pending
  | knownReceive kernel target context =>
      simpa only [ctxInterpreter, withKnown, ExceptT.run, ExceptT.mk, StateT.run, bind_pure_comp,
        IsTotalQueryBound, isQueryBound_map_iff, serviceCost] using
        knownProgram_total source codec.frameWrite _ 1 (known_receive_hash kernel target context) state.pending
  | allocate allocated =>
      simpa only [ctxInterpreter, ExceptT.run, ExceptT.mk, StateT.run, bind_pure_comp,
        IsTotalQueryBound, isQueryBound_map_iff, serviceCost] using allocation_total allocated state.seeds
  | coin coin =>
      simp [ctxInterpreter, serviceCost, PqxdhRecordLiftCtxOracle.coinLift, StateT.run, IsTotalQueryBound]
  | hash bytes =>
      simp [ctxInterpreter, serviceCost, StateT.run, publicRom, QueryImpl.compose,
        RawCtxSelectedSealConsumer.liftSelected, AdaptiveCtxSharedTarget.forward,
        RawCtxSelectedMessageSealing.hashLift, IsTotalQueryBound]
  | charge kind => trivial
  | publish tag => trivial

/-- A weighted structural budget charges the stated cost at every possible adaptive service request. -/
def CostBound (cost : Service n → Nat) (client : OracleComp (ServiceSpec n) Result) (bound : Nat) : Prop :=
  client.IsQueryBound bound (fun query remaining => cost query ≤ remaining)
    (fun query remaining => remaining - cost query)

/-- Explicit service costs compose through every possible optional reply and stop, keeping the full private state in the continuation. -/
theorem schedule_total (slot : Nat) (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (ideal : PqxdhRecordLiftChainState.Coordinate (Slot n) → Bool)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (client : OracleComp (ServiceSpec n) Result) (bound : Nat)
    (bounded : CostBound serviceCost client bound) (state : Secret n) :
    ((simulateQ (ctxInterpreter slot source ideal codec) client).run.run state).IsTotalQueryBound bound := by
  induction client using OracleComp.inductionOn generalizing state bound with
  | pure result => trivial
  | query_bind query next ih =>
      rw [CostBound, isQueryBound_query_bind_iff] at bounded
      simp only [simulateQ_bind, simulateQ_spec_query, PqxdhRecordLiftCtxOracle.except_bind]
      have suffix : ∀ result : Except Unit ((ServiceSpec n).Range query) × Secret n,
          ((match result.1 with
            | .error error => pure (.error error, result.2)
            | .ok reply => (simulateQ (ctxInterpreter slot source ideal codec) (next reply)).run.run result.2) :
            OracleComp Spec (Except Unit Result × Secret n)).IsTotalQueryBound (bound - serviceCost query) := by
        rintro ⟨reply, after⟩
        cases reply with
        | error error => trivial
        | ok reply => exact ih reply _ (bounded.2 reply) after
      convert (isTotalQueryBound_bind (service_total slot source ideal codec query state) suffix).mono
        (show serviceCost query + (bound - serviceCost query) ≤ bound from by omega) using 1
      apply bind_congr
      rintro ⟨reply, after⟩
      cases reply <;> rfl

/-- The ordinary component keeps four independent query ledgers. -/
inductive BudgetKind where
  | uniform | hash | seal | raw
  deriving DecidableEq

def category : BudgetKind → Spec.Domain → Prop
  | .uniform => AdaptiveCtxDynamicKnownBounds.UniformRoute
  | .hash => AdaptiveCtxDynamicKnownBounds.HashRoute
  | .seal => AdaptiveCtxDynamicKnownBounds.TargetClass AdaptiveCtxQueryBounds.SourceSeal
  | .raw => AdaptiveCtxDynamicKnownBounds.TargetClass IsRawQuery

instance (kind : BudgetKind) : DecidablePred (category kind) := by
  cases kind <;> unfold category <;> infer_instance

/-- Explicit uniform-query forwarding cannot issue a hash, selected seal or selected verification query. -/
theorem uniform_other (kind : BudgetKind) (other : kind ≠ .uniform) (work : ProbComp Result) :
    (simulateQ PqxdhRecordLiftCtxOracle.coinLift work).IsQueryBoundP (category kind) 0 := by
  apply RawCtxSourceOpen.simulate_bound PqxdhRecordLiftCtxOracle.coinLift (fun _ => False)
    (category kind) work 0 (by simp)
  intro query
  cases kind <;> simp_all [PqxdhRecordLiftCtxOracle.coinLift, category,
    AdaptiveCtxDynamicKnownBounds.HashRoute, AdaptiveCtxDynamicKnownBounds.TargetClass,
    AdaptiveCtxQueryBounds.SourceHash, AdaptiveCtxQueryBounds.SourceSeal, IsRawQuery]

/-- Public-ROM forwarding adds no explicit uniform, selected sealing or selected verification request. Its cache draws remain inside the component's own ROM accounting. -/
theorem public_other (kind : BudgetKind) (other : kind ≠ .hash) (work : OracleComp CtxRO Result) :
    (simulateQ publicRom work).IsQueryBoundP (category kind) 0 := by
  apply RawCtxSourceOpen.simulate_bound publicRom (fun _ => False) (category kind) work 0 (by simp)
  intro query
  cases kind <;> simp_all [publicRom, QueryImpl.compose, RawCtxSelectedSealConsumer.liftSelected,
    AdaptiveCtxSharedTarget.forward, RawCtxSelectedMessageSealing.hashLift, category,
    AdaptiveCtxDynamicKnownBounds.UniformRoute, AdaptiveCtxDynamicKnownBounds.TargetClass,
    AdaptiveCtxQueryBounds.SourceUniform, AdaptiveCtxQueryBounds.SourceSeal, IsRawQuery]

set_option maxRecDepth 2048 in
/-- Every actual lookup branch, including an ideal miss, adds no non-uniform component query. Public real KDF work remains in the separate native ledger. -/
theorem lookup_other (kind : BudgetKind) (other : kind ≠ .uniform)
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (seeds : PqxdhRecordLiftChainTable.Seeds (Slot n))
    (ideal : PqxdhRecordLiftChainState.Coordinate (Slot n) → Bool)
    (coordinate : PqxdhRecordLiftChainState.Coordinate (Slot n))
    (masked : PqxdhRecordLiftProjectionCut.Mask (Slot n)) :
    ((PqxdhRecordLiftCtxOracle.keyLookup source seeds ideal coordinate).run masked).IsQueryBoundP (category kind) 0 := by
  change (PqxdhRecordLiftCtxOracle.keyLookup source seeds ideal coordinate masked).IsQueryBoundP (category kind) 0
  unfold PqxdhRecordLiftCtxOracle.keyLookup
  split
  · trivial
  · split
    · split
      · trivial
      · simpa only [bind_pure_comp, isQueryBoundP_map_iff] using
          uniform_other kind other ($ᵗ PqxdhFullSecretInputKdf.FullOutput)
    · trivial

/-- Separate endpoint ledger costs follow actual service categories. Unknown-key opening and sealing are each counted even when their optional reply rejects. -/
def categoryCost (kind : BudgetKind) : Service n → Nat := match kind with
  | .uniform => fun query => match query with
    | .allocate _ => 64
    | .lookup _ => 76
    | .coin _ => 1
    | _ => 0
  | .hash => fun query => match query with
    | .hash _ | .opening _ | .sealing _ | .knownSend _ _ | .knownReceive _ _ _ => 1
    | _ => 0
  | .seal => fun query => match query with | .sealing _ => 1 | _ => 0
  | .raw => fun query => match query with | .opening _ => 1 | _ => 0

/-- The complete hidden/known opening route contributes only its possible public hash or selected raw attempt, never a seal or explicit uniform request. -/
theorem opening_categories (kind : BudgetKind) (slot : Nat)
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (ideal : PqxdhRecordLiftChainState.Coordinate (Slot n) → Bool)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (pending : Opening n) (state : Secret n) :
    ((ctxInterpreter slot source ideal codec (.opening pending)).run.run state).IsQueryBoundP
      (category kind) (categoryCost kind (.opening pending)) := by
  cases kind with
  | uniform =>
      simpa only [ctxInterpreter, withLocal, PqxdhRecordLiftCtxOracle.interpreter, ExceptT.run,
        ExceptT.mk, StateT.run, bind_pure_comp, isQueryBoundP_map_iff, category, categoryCost] using
        (openingService_other slot codec.frameRead pending.context.frame.sender (seedAt state) state.masked pending).2
  | «seal» =>
      simpa only [ctxInterpreter, withLocal, PqxdhRecordLiftCtxOracle.interpreter, ExceptT.run,
        ExceptT.mk, StateT.run, bind_pure_comp, isQueryBoundP_map_iff, category, categoryCost] using
        (openingService_other slot codec.frameRead pending.context.frame.sender (seedAt state) state.masked pending).1
  | hash => exact (service_total slot source ideal codec (.opening pending) state).isQueryBoundP
  | raw => exact (service_total slot source ideal codec (.opening pending) state).isQueryBoundP

/-- Complete sealing, including endpoint refusal and writer None, contributes no selected opening or explicit uniform query. -/
theorem sealing_categories (kind : BudgetKind) (slot : Nat)
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (ideal : PqxdhRecordLiftChainState.Coordinate (Slot n) → Bool)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (pending : Sealing n) (state : Secret n) :
    ((ctxInterpreter slot source ideal codec (.sealing pending)).run.run state).IsQueryBoundP
      (category kind) (categoryCost kind (.sealing pending)) := by
  cases kind with
  | uniform =>
      simpa only [ctxInterpreter, withLocal, PqxdhRecordLiftCtxOracle.interpreter, ExceptT.run,
        ExceptT.mk, StateT.run, bind_pure_comp, isQueryBoundP_map_iff, category, categoryCost] using
        (sealingService_other source.crypto codec.frameWrite state.masked pending state.pending).2
  | raw =>
      simpa only [ctxInterpreter, withLocal, PqxdhRecordLiftCtxOracle.interpreter, ExceptT.run,
        ExceptT.mk, StateT.run, bind_pure_comp, isQueryBoundP_map_iff, category, categoryCost] using
        (sealingService_other source.crypto codec.frameWrite state.masked pending state.pending).1
  | hash => exact (service_total slot source ideal codec (.sealing pending) state).isQueryBoundP
  | «seal» => exact (service_total slot source ideal codec (.sealing pending) state).isQueryBoundP

/-- Complete caller-known native programs contribute their proved source hash cap and no selected seal/raw or explicit uniform request, while retaining all real functional calls. -/
theorem known_categories (kind : BudgetKind) (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (writer : RawCtxMixedShared.Writer) (work : OracleComp RawCtxMixedOwner.NativeSpec Result)
    (bound : Nat) (bounded : work.IsQueryBoundP (fun query => RawCtxMixedOwner.callKind query = .hash) bound)
    (state : Secret n) :
    ((withKnown (knownProgram source writer work)).run.run state).IsQueryBoundP (category kind)
      (if kind = .hash then bound else 0) := by
  by_cases isHash : kind = .hash
  · subst kind
    simpa only [withKnown, ExceptT.run, ExceptT.mk, StateT.run, bind_pure_comp,
      isQueryBoundP_map_iff, ite_true] using
      (knownProgram_total source writer work bound bounded state.pending).isQueryBoundP (p := category .hash)
  · simpa only [withKnown, knownProgram, ExceptT.run, ExceptT.mk, StateT.run,
      bind_pure_comp, isQueryBoundP_map_iff, isHash, ite_false] using
      public_other kind isHash ((simulateQ (knownRom source writer) work).run state.pending)

/-- Each global service obeys its separate uniform/hash/selected-seal/selected-raw cap under every supplied private state and every optional endpoint reply. -/
theorem service_categories (kind : BudgetKind) (slot : Nat)
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (ideal : PqxdhRecordLiftChainState.Coordinate (Slot n) → Bool)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (query : Service n) (state : Secret n) :
    ((ctxInterpreter slot source ideal codec query).run.run state).IsQueryBoundP
      (category kind) (categoryCost kind query) := by
  cases query with
  | opening pending => exact opening_categories kind slot source ideal codec pending state
  | sealing pending => exact sealing_categories kind slot source ideal codec pending state
  | knownSend kernel context =>
      have cost : categoryCost kind (.knownSend kernel context : Service n) = if kind = .hash then 1 else 0 := by
        cases kind <;> rfl
      rw [cost]
      exact known_categories kind source codec.frameWrite _ 1 (known_send_hash kernel context) state
  | knownReceive kernel target context =>
      have cost : categoryCost kind (.knownReceive kernel target context : Service n) = if kind = .hash then 1 else 0 := by
        cases kind <;> rfl
      rw [cost]
      exact known_categories kind source codec.frameWrite _ 1 (known_receive_hash kernel target context) state
  | allocate allocated =>
      by_cases selected : kind = .uniform
      · subst kind
        exact (service_total slot source ideal codec (.allocate allocated) state).isQueryBoundP
      · have cost : categoryCost kind (.allocate allocated : Service n) = 0 := by
          cases kind <;> simp_all [categoryCost]
        rw [cost]
        simpa only [ctxInterpreter, ExceptT.run, ExceptT.mk, StateT.run, bind_pure_comp,
          isQueryBoundP_map_iff] using
          uniform_other kind selected ((PqxdhRecordLiftLazyTable.impl allocated).run state.seeds)
  | lookup coordinate =>
      by_cases selected : kind = .uniform
      · subst kind
        exact (service_total slot source ideal codec (.lookup coordinate) state).isQueryBoundP
      · have cost : categoryCost kind (.lookup coordinate : Service n) = 0 := by
          cases kind <;> simp_all [categoryCost]
        rw [cost]
        simpa only [ctxInterpreter, withLocal, PqxdhRecordLiftCtxOracle.interpreter, ExceptT.run,
          ExceptT.mk, StateT.run, bind_pure_comp, isQueryBoundP_map_iff] using
          lookup_other kind selected source (seedAt state) ideal coordinate state.masked
  | coin coin =>
      cases kind <;> simp [ctxInterpreter, categoryCost, category, PqxdhRecordLiftCtxOracle.coinLift,
        ExceptT.run, ExceptT.mk, StateT.run, AdaptiveCtxDynamicKnownBounds.UniformRoute,
        AdaptiveCtxDynamicKnownBounds.HashRoute, AdaptiveCtxDynamicKnownBounds.TargetClass,
        AdaptiveCtxQueryBounds.SourceUniform, AdaptiveCtxQueryBounds.SourceHash,
        AdaptiveCtxQueryBounds.SourceSeal, IsRawQuery]
  | hash bytes =>
      by_cases selected : kind = .hash
      · subst kind
        exact (service_total slot source ideal codec (.hash bytes) state).isQueryBoundP
      · have cost : categoryCost kind (.hash bytes : Service n) = 0 := by
          cases kind <;> simp_all [categoryCost]
        rw [cost]
        simpa only [ctxInterpreter, ExceptT.run, ExceptT.mk, StateT.run, bind_pure_comp,
          isQueryBoundP_map_iff, simulateQ_spec_query] using
          public_other kind selected (CtxRO.query ((), bytes))
  | charge charged => cases kind <;> trivial
  | publish tag => cases kind <;> trivial

/-- Every category bill composes through arbitrary adaptive replies and explicit stops, retaining the complete private continuation state. -/
theorem schedule_categories (kind : BudgetKind) (slot : Nat)
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (ideal : PqxdhRecordLiftChainState.Coordinate (Slot n) → Bool)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (client : OracleComp (ServiceSpec n) Result) (bound : Nat)
    (bounded : CostBound (categoryCost kind) client bound) (state : Secret n) :
    ((simulateQ (ctxInterpreter slot source ideal codec) client).run.run state).IsQueryBoundP
      (category kind) bound := by
  induction client using OracleComp.inductionOn generalizing state bound with
  | pure result => trivial
  | query_bind query next ih =>
      rw [CostBound, isQueryBound_query_bind_iff] at bounded
      simp only [simulateQ_bind, simulateQ_spec_query, PqxdhRecordLiftCtxOracle.except_bind]
      have suffix : ∀ result : Except Unit ((ServiceSpec n).Range query) × Secret n,
          ((match result.1 with
            | .error error => pure (.error error, result.2)
            | .ok reply => (simulateQ (ctxInterpreter slot source ideal codec) (next reply)).run.run result.2) :
            OracleComp Spec (Except Unit Result × Secret n)).IsQueryBoundP
              (category kind) (bound - categoryCost kind query) := by
        rintro ⟨reply, after⟩
        cases reply with
        | error error => trivial
        | ok reply => exact ih reply _ (bounded.2 reply) after
      convert (isQueryBoundP_bind (service_categories kind slot source ideal codec query state)
        (fun result _ => suffix result)).mono
        (show categoryCost kind query + (bound - categoryCost kind query) ≤ bound from by omega) using 1
      apply bind_congr
      rintro ⟨reply, after⟩
      cases reply <;> rfl

/-- The constructed ordinary selected-key reduction retains four explicit ledgers, including every adaptive verification attempt and all public or caller-known hashing. -/
theorem reduction_budgets (slot : Nat) (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (ideal : PqxdhRecordLiftChainState.Coordinate (Slot n) → Bool)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (client : OracleComp (ServiceSpec n) Result) (state : Secret n) (others : ReductionState)
    (qUniform qHash qSeal qRaw : Nat)
    (uniformBound : CostBound (categoryCost .uniform) client qUniform)
    (hashBound : CostBound (categoryCost .hash) client qHash)
    (sealBound : CostBound (categoryCost .seal) client qSeal)
    (rawBound : CostBound (categoryCost .raw) client qRaw) :
    (reduction slot source ideal codec client state others).IsQueryBoundP AdaptiveCtxQueryBounds.SourceUniform qUniform ∧
    (reduction slot source ideal codec client state others).IsQueryBoundP AdaptiveCtxQueryBounds.SourceHash qHash ∧
    (reduction slot source ideal codec client state others).IsQueryBoundP AdaptiveCtxQueryBounds.SourceSeal qSeal ∧
    (reduction slot source ideal codec client state others).IsQueryBoundP IsRawQuery qRaw := by
  exact ⟨AdaptiveCtxDynamicKnownBounds.uniform_bound source.crypto _ qUniform
      (schedule_categories .uniform slot source ideal codec client qUniform uniformBound state) others,
    AdaptiveCtxDynamicKnownBounds.hash_bound source.crypto _ qHash
      (schedule_categories .hash slot source ideal codec client qHash hashBound state) others,
    AdaptiveCtxDynamicKnownBounds.target_bound source.crypto _ AdaptiveCtxSharedTarget.forward_seal_class _ qSeal
      (schedule_categories .seal slot source ideal codec client qSeal sealBound state) others,
    AdaptiveCtxDynamicKnownBounds.target_bound source.crypto _ AdaptiveCtxSharedTarget.forward_raw_class _ qRaw
      (schedule_categories .raw slot source ideal codec client qRaw rawBound state) others⟩

end BeaconcryptCore.Computational.PqxdhRecordLiftCtxProtocolBounds

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxProtocolBounds.known_receive_hash' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxProtocolBounds.known_receive_hash

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxProtocolBounds.known_send_hash' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxProtocolBounds.known_send_hash

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxProtocolBounds.knownRom_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxProtocolBounds.knownRom_total

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxProtocolBounds.knownProgram_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxProtocolBounds.knownProgram_total

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxProtocolBounds.allocation_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxProtocolBounds.allocation_total

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxProtocolBounds.service_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxProtocolBounds.service_total

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxProtocolBounds.schedule_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxProtocolBounds.schedule_total

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxProtocolBounds.uniform_other' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxProtocolBounds.uniform_other

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxProtocolBounds.public_other' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxProtocolBounds.public_other

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxProtocolBounds.lookup_other' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxProtocolBounds.lookup_other

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxProtocolBounds.opening_categories' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxProtocolBounds.opening_categories

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxProtocolBounds.sealing_categories' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxProtocolBounds.sealing_categories

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxProtocolBounds.known_categories' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxProtocolBounds.known_categories

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxProtocolBounds.service_categories' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxProtocolBounds.service_categories

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxProtocolBounds.schedule_categories' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxProtocolBounds.schedule_categories

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxProtocolBounds.reduction_budgets' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxProtocolBounds.reduction_budgets
