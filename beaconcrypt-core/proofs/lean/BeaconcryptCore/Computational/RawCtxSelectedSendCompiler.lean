import BeaconcryptCore.Computational.RawCtxSelectedReceiveCompiler
import BeaconcryptCore.Computational.RawCtxSelectedSendTrace

/-!
The complete source send is compiled with an explicit outer nonce stop and the original inner optional writer result. The native source consumes the same private derivation and original pending seal. The selected key is confined to the mathematical CTX interpreter; known-key aliases retain real native operations.
-/
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.refined ratchet.concrete
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RawCtxSelectedSendCompiler
open PqxdhSecretInputKdf PqxdhFullSecretInputKdf PqxdhJointKdfGame
open RawCtxSelectedMessageKey RawCtxSelectedMessageKdf RawCtxSelectedMessageDriver
open RawCtxSelectedParentTable RawCtxSelectedParentEntry
open RawCtxSelectedReceiveCompiler (State project evaluated)
variable {A : Type}

/-- The retained private KDF table does not change the actual native seal, commitment or optional writer. -/
theorem sealing_native (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (pending : SendSeal RawCtxSourceSend.SealContext) :
    RawCtxFunctionalFamily.sealing (A := A) source writer prior pending =
      Option.map (RawCtxSourceSend.encrypted (RawCtxSourceSend.arguments pending)) <$>
        simulateQ (RawCtxCanonicalSeal.sharedImpl source.crypto writer (RawCtxSourceHkdf.kdfImpl source))
          (RawCtxSourceSeal.sealInput (RawCtxSourceSend.arguments pending)) := by
  simp only [RawCtxFunctionalFamily.sealing, RawCtxFunctionalFamily.native, RawCtxFunctionalFamily.backend,
    QueryImpl.compose, RawCtxSourceSend.adapter, bind_pure_comp, RawCtxMixedOwner.sendAdapter]
  simp only [simulateQ_map, simulateQ_spec_query, QueryImpl.compose, RawCtxSourceSeal.nativeAdapter, ← QueryImpl.simulateQ_compose]
  congr 2
  funext query
  rcases query with input | (bytes | frame)
  all_goals simp only [QueryImpl.compose, RawCtxSourceSeal.sealLift, RawCtxMixedOwner.sendLift,
    RawCtxServerServices.nativeLift, RawCtxSelectiveKdfFamily.compiler, RawCtxRetainedTable.viewImpl,
    RawCtxCanonicalSeal.sharedImpl, RawCtxProtocolBackend.backend, simulateQ_spec_query]
  all_goals funext state
  all_goals rfl

/-- Before the explicitly tested selected-nonce stop, the original source sealing callback returns the same inner optional ciphertext and complete shared state. -/
theorem sealing_project (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (parent : Option Entry) (key target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (read : RawCtxReceive.FrameDecoder)
    (pending : RawCtxInterpretedSend.Seal Slot RawCtxSourceSend.SealContext) (state : State A)
    (fresh : ∀ value, pending.material = .hidden value → pending.context.associatedData.length = 153 →
      value ∉ state.2.selected.1.usedNonces) :
    (fun result => (some result.1, result.2)) <$>
      (sendServices source writer prior parent key target nonce next (.inr pending)).run (project state) =
      Prod.map id project <$> (evaluated source key read (RawCtxSelectedSealConsumer.sealing source.crypto writer pending)).run state := by
  simp only [sendServices, sealing_native, StateT.run_map]
  rw [RawCtxCanonicalSeal.shared_complete]
  have exactSource := congrArg (fun work => (fun result => (result.1, (state.1, result.2))) <$> work)
    (RawCtxSelectedSealConsumer.sealing_source (RawCtxUniversalDecoder.decoder read) source.crypto key writer pending state.2 fresh)
  simpa only [evaluated, project, StateT.run, Functor.map_map, Prod.map_def, id_eq] using exactSource.symm

noncomputable def deriveValue (prior : Prior) (parent : Option Entry) (target : RootOutput)
    (nonce : NonceOutput) (next : RootOutput) (request : SymmetricRatchetKdfRequest) : RatchetChain × Slot :=
  match parent with
  | none => RawCtxSelectedMessageKdf.step prior target nonce next request
  | some entry => RawCtxSelectedMessageKdf.later prior entry target nonce next request

noncomputable def service (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (prior : Prior) :
    QueryImpl (SendServices RawCtxSourceSend.SealContext RawCtxSourceSend.Encrypted)
      (OptionT (OracleComp AdaptiveCtxDynamicKnownKeys.Spec))
  | .inl address => pure (prior address)
  | .inr pending => OptionT.mk (RawCtxSelectedSealConsumer.sealing source.crypto writer pending)

noncomputable def send (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (parent : Option Entry) (target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (kernel : RawCtxSelectedMessageReveals.Kernel) (context : RawCtxSourceSend.SealContext) :=
  (simulateQ (service source writer prior) (RawCtxSelectedMessageDriver.send parent target nonce next kernel context)).run

/-- The compiled send uses the actual local derivation before its single optional selected/known seal. The outer option remains the nonce stop, not a fabricated writer failure. -/
theorem send_cases (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (parent : Option Entry) (target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (kernel : RawCtxSelectedMessageReveals.Kernel) (context : RawCtxSourceSend.SealContext) :
    send source writer prior parent target nonce next kernel context =
      match RawCtxInterpretedSend.normalBegin kernel context with
      | .exhausted entry _ => pure (some (entry, none))
      | .requested pending =>
        let ready := RawCtxInterpretedSend.ready pending (deriveValue prior parent target nonce next pending.request)
        Option.map (fun encrypted => (ready.advanced, encrypted)) <$>
          RawCtxSelectedSealConsumer.sealing source.crypto writer ready := by
  simp only [send, RawCtxSelectedMessageDriver.send, ← QueryImpl.simulateQ_compose, RawCtxInterpretedSend.send]
  cases started : RawCtxInterpretedSend.normalBegin kernel context with
  | exhausted entry actual => rfl
  | requested pending =>
    simp only [RawCtxInterpretedSend.program, simulateQ_bind, simulateQ_spec_query, simulateQ_pure,
      QueryImpl.compose, sendCompiler, ← QueryImpl.simulateQ_compose]
    change ((do
      let reply ← simulateQ (fun address => (pure (prior address) : OptionT (OracleComp AdaptiveCtxDynamicKnownKeys.Spec) FullOutput))
        (derive parent target nonce next pending.request)
      let sealed ← OptionT.mk (RawCtxSelectedSealConsumer.sealing source.crypto writer (RawCtxInterpretedSend.ready pending reply))
      pure ((RawCtxInterpretedSend.ready pending reply).advanced, sealed)).run) = _
    rw [derive_evaluated]
    simp only [pure_bind, OptionT.run_bind, OptionT.run_mk, OptionT.run_pure, Option.elimM]
    cases parent <;> simp only [deriveValue]
    all_goals rw [map_eq_bind_pure_comp]
    all_goals apply bind_congr
    all_goals intro reply; cases reply <;> rfl

def Repeated (pending : RawCtxInterpretedSend.Seal Slot RawCtxSourceSend.SealContext)
    (state : AdaptiveCtxDynamicKnownKeys.SourceState) : Prop :=
  ∃ value, pending.material = .hidden value ∧ pending.context.associatedData.length = 153 ∧ value ∈ state.selected.1.usedNonces

local instance (pending : RawCtxInterpretedSend.Seal Slot RawCtxSourceSend.SealContext)
    (state : AdaptiveCtxDynamicKnownKeys.SourceState) : Decidable (Repeated pending state) := by
  unfold Repeated
  cases pending.material with
  | hidden nonce => exact decidable_of_iff (pending.context.associatedData.length = 153 ∧ nonce ∈ state.selected.1.usedNonces) (by simp)
  | known material => exact decidable_of_iff False (by simp)

/-- The outer stop is exactly an actual repeated selected nonce. Every other branch is the original native optional seal and its full cache; no nonce-freshness premise is assumed. -/
theorem sealing_cases (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (parent : Option Entry) (key target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (read : RawCtxReceive.FrameDecoder)
    (pending : RawCtxInterpretedSend.Seal Slot RawCtxSourceSend.SealContext) (state : State A) :
    Prod.map id project <$> (evaluated source key read (RawCtxSelectedSealConsumer.sealing source.crypto writer pending)).run state =
      if Repeated pending state.2 then pure (none, project state)
      else (fun result => (some result.1, result.2)) <$>
        (sendServices source writer prior parent key target nonce next (.inr pending)).run (project state) := by
  classical
  split
  · obtain ⟨value, material, width, used⟩ := ‹Repeated pending state.2›
    change Prod.map id project <$> ((fun result => (result.1, (state.1, result.2))) <$>
      (simulateQ (AdaptiveCtxDynamicKnownKeys.sourceImpl true (RawCtxUniversalDecoder.decoder read) source.crypto key)
        (RawCtxSelectedSealConsumer.sealing source.crypto writer pending)).run state.2) = _
    rw [RawCtxSelectedSealConsumer.sealing_repeat (RawCtxUniversalDecoder.decoder read) source.crypto key writer pending value material width state.2 used]
    rfl
  · symm
    apply sealing_project
    intro value material width used
    exact ‹¬ Repeated pending state.2› ⟨value, material, width, used⟩

/-- Evaluating the actual private send derivation keeps the exact source pending seal and all private state before its original optional reply. -/
theorem source_cases (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (parent : Option Entry) (key target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (kernel : RawCtxSelectedMessageReveals.Kernel) (context : RawCtxSourceSend.SealContext) :
    simulateQ (sendServices (A := A) source writer prior parent key target nonce next)
      (RawCtxSelectedMessageDriver.send parent target nonce next kernel context) =
      match RawCtxInterpretedSend.normalBegin kernel context with
      | .exhausted entry _ => pure (entry, none)
      | .requested pending =>
        let ready := RawCtxInterpretedSend.ready pending (deriveValue prior parent target nonce next pending.request)
        (fun encrypted => (ready.advanced, encrypted)) <$>
          sendServices source writer prior parent key target nonce next (.inr ready) := by
  simp only [RawCtxSelectedMessageDriver.send, ← QueryImpl.simulateQ_compose, RawCtxInterpretedSend.send]
  cases started : RawCtxInterpretedSend.normalBegin kernel context with
  | exhausted entry actual => rfl
  | requested pending =>
    simp only [RawCtxInterpretedSend.program, simulateQ_bind, simulateQ_spec_query, simulateQ_pure,
      QueryImpl.compose, sendCompiler, ← QueryImpl.simulateQ_compose]
    change (do
      let reply ← simulateQ (fun address => (pure (prior address) : StateT (RawCtxSharedPrimitive.SharedState A) ProbComp FullOutput))
        (derive parent target nonce next pending.request)
      let sealed ← sendServices source writer prior parent key target nonce next (.inr (RawCtxInterpretedSend.ready pending reply))
      pure ((RawCtxInterpretedSend.ready pending reply).advanced, sealed)) = _
    rw [derive_evaluated]
    simp only [pure_bind, bind_pure_comp]
    rfl


/-- The stop test is computed from the actual pending source seal, including the retained-table derivation and its selected/known alias decision. -/
noncomputable def Stops (prior : Prior) (parent : Option Entry) (target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (kernel : RawCtxSelectedMessageReveals.Kernel) (context : RawCtxSourceSend.SealContext)
    (state : AdaptiveCtxDynamicKnownKeys.SourceState) : Prop :=
  match RawCtxInterpretedSend.normalBegin kernel context with
  | .exhausted _ _ => False
  | .requested pending => Repeated (RawCtxInterpretedSend.ready pending (deriveValue prior parent target nonce next pending.request)) state

noncomputable local instance (prior : Prior) (parent : Option Entry) (target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (kernel : RawCtxSelectedMessageReveals.Kernel) (context : RawCtxSourceSend.SealContext)
    (state : AdaptiveCtxDynamicKnownKeys.SourceState) : Decidable (Stops prior parent target nonce next kernel context state) := by
  unfold Stops
  cases RawCtxInterpretedSend.normalBegin kernel context <;> infer_instance

/-- One complete source send compiles without a freshness premise. Its only additional outcome is the explicitly tested repeated selected nonce; otherwise the original inner optional writer result and full source state are preserved. -/
theorem send_source (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (parent : Option Entry) (key target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (read : RawCtxReceive.FrameDecoder)
    (kernel : RawCtxSelectedMessageReveals.Kernel) (context : RawCtxSourceSend.SealContext) (state : State A) :
    Prod.map id project <$> (evaluated source key read (send source writer prior parent target nonce next kernel context)).run state =
      if Stops prior parent target nonce next kernel context state.2 then pure (none, project state)
      else (fun result => (some result.1, result.2)) <$>
        (simulateQ (sendServices source writer prior parent key target nonce next)
          (RawCtxSelectedMessageDriver.send parent target nonce next kernel context)).run (project state) := by
  rw [send_cases, source_cases]
  cases started : RawCtxInterpretedSend.normalBegin kernel context with
  | exhausted entry actual =>
    have clear : ¬ Stops prior parent target nonce next kernel context state.2 := by simp only [Stops, started, not_false_eq_true]
    simp only [ite_eq_right (fun h => (clear h).elim), StateT.run_pure, map_pure, project]
    rfl
  | requested pending =>
    have test : Stops prior parent target nonce next kernel context state.2 ↔ Repeated
        (RawCtxInterpretedSend.ready pending (deriveValue prior parent target nonce next pending.request)) state.2 := by simp only [Stops, started]
    simp only [test]
    rw [RawCtxSelectedReceiveCompiler.evaluated_map, StateT.run_map, Functor.map_map]
    let ready := RawCtxInterpretedSend.ready pending (deriveValue prior parent target nonce next pending.request)
    have sealResult := sealing_cases source writer prior parent key target nonce next read ready state
    have mapped := congrArg (fun work => (fun result => (Option.map (fun encrypted => (ready.advanced, encrypted)) result.1, result.2)) <$> work) sealResult
    dsimp only [ready] at mapped
    simp only [Functor.map_map, Prod.map_def, id_eq, StateT.run_map, apply_ite, map_pure, Option.map_none,
      Option.map_some] at mapped ⊢
    convert mapped using 1
    rfl


/-- Interpreting only private slots recovers the complete extracted native send, including the exact pending seal, optional writer reply and cache. The selected-nonce stop is the same explicit event. -/
theorem native_send (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (parent : Option Entry) (key target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (read : RawCtxReceive.FrameDecoder)
    (kernel : RawCtxSelectedMessageReveals.Kernel) (context : RawCtxSourceSend.SealContext) (state : State A) :
    (fun result => (Option.map (Prod.map (RawCtxSelectedMessageReveals.nativeKernel key) id) result.1, project result.2)) <$>
        (evaluated source key read (send source writer prior parent target nonce next kernel context)).run state =
      if Stops prior parent target nonce next kernel context state.2 then pure (none, project state)
      else (fun result => (some result.1, result.2)) <$>
        (simulateQ ((RawCtxFunctionalFamily.native source writer (privateTable prior parent target (response key nonce next))
            ∘ₛ RawCtxMixedOwner.sendAdapter) ∘ₛ RawCtxSourceSend.adapter)
          (RawCtxSourceSend.send (RawCtxSelectedMessageReveals.nativeKernel key kernel) context)).run (project state) := by
  rw [RawCtxSelectedMessageDriver.send_state]
  have mapped := congrArg (fun work => (fun result =>
    (Option.map (Prod.map (RawCtxSelectedMessageReveals.nativeKernel key) id) result.1, result.2)) <$> work)
      (send_source source writer prior parent key target nonce next read kernel context state)
  simp only [Functor.map_map, apply_ite, map_pure, Prod.map_def, id_eq, Option.map_none, Option.map_some] at mapped ⊢
  convert mapped using 1

/-- A local known-key seal pays one actual shared-ROM call; all selected-key operations remain inside the challenger. -/
theorem known_queries (c : Pqxdh.Crypto) (writer : RawCtxMixedShared.Writer) (input : RawCtxSourceSend.SealInput) :
    (RawCtxSelectedMessageSealing.known c writer input).IsTotalQueryBound 1 := by
  unfold RawCtxSelectedMessageSealing.known
  apply (RawCtxSelectedMessageSealing.hashLift_bound _ 1 (RawCtxCanonicalSeal.typedSource_query_bound c writer input)).simulateQ_of_step
  intro query
  cases query <;> simp [AdaptiveCtxSharedTarget.forward, IsTotalQueryBound]

/-- The pending seal makes at most one component query: a known shared-ROM lookup or a selected seal attempt, including a refused nonce. -/
theorem sealing_queries (c : Pqxdh.Crypto) (writer : RawCtxMixedShared.Writer)
    (pending : RawCtxInterpretedSend.Seal Slot RawCtxSourceSend.SealContext) :
    (RawCtxSelectedSealConsumer.sealing c writer pending).IsTotalQueryBound 1 := by
  simp only [RawCtxSelectedSealConsumer.sealing, IsTotalQueryBound, isQueryBound_map_iff]
  change (RawCtxSelectedSealConsumer.call c writer (RawCtxInterpretedArguments.sealArguments pending)).IsTotalQueryBound 1
  unfold RawCtxSelectedSealConsumer.call
  apply IsTotalQueryBound.simulateQ_of_step
  · cases material : pending.material with
    | known value =>
      simpa only [RawCtxInterpretedArguments.sealArguments, material, IsTotalQueryBound, isQueryBound_map_iff] using
        known_queries c writer ⟨value, pending.sequence, pending.context⟩
    | hidden value =>
      simp only [RawCtxInterpretedArguments.sealArguments, material, RawCtxSelectedMessageSealing.selected]
      split
      · simp [IsTotalQueryBound, bind_pure_comp]
      · trivial
  · intro query
    simp [RawCtxSelectedSealConsumer.liftSelected, IsTotalQueryBound]

/-- A complete compiled send has at most one component call, even on exhaustion, writer failure or selected-nonce refusal. The original private derivation is separately bounded by one retained-table lookup. -/
theorem send_queries (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (parent : Option Entry) (target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (kernel : RawCtxSelectedMessageReveals.Kernel) (context : RawCtxSourceSend.SealContext) :
    (send source writer prior parent target nonce next kernel context).IsTotalQueryBound 1 := by
  rw [send_cases]
  cases RawCtxInterpretedSend.normalBegin kernel context with
  | exhausted entry actual => trivial
  | requested pending =>
    simp only [IsTotalQueryBound, isQueryBound_map_iff]
    exact sealing_queries source.crypto writer _

end BeaconcryptCore.Computational.RawCtxSelectedSendCompiler

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedSendCompiler.sealing_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedSendCompiler.sealing_native

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedSendCompiler.sealing_project' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedSendCompiler.sealing_project

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedSendCompiler.send_cases' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedSendCompiler.send_cases

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedSendCompiler.sealing_cases' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedSendCompiler.sealing_cases

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedSendCompiler.source_cases' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedSendCompiler.source_cases

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedSendCompiler.send_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedSendCompiler.send_source

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedSendCompiler.native_send' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedSendCompiler.native_send

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedSendCompiler.known_queries' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedSendCompiler.known_queries

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedSendCompiler.sealing_queries' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedSendCompiler.sealing_queries

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedSendCompiler.send_queries' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedSendCompiler.send_queries
