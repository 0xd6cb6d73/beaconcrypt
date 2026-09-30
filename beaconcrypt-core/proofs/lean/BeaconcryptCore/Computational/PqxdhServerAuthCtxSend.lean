import BeaconcryptCore.Computational.PqxdhServerAuthCtxCalls
import BeaconcryptCore.Computational.RawCtxSelectedSendCompiler

/-! The selected factor's sending driver uses the ordinary CTX seal with an explicit nonce-refusal stop. Inner optional writer failure stays distinct from that stop and retains the original advanced state. Known-chain derivations and known-material seals stay real; no selected key is an executable argument. -/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.refined ratchet.concrete
set_option autoImplicit false

namespace BeaconcryptCore.Computational.PqxdhServerAuthCtxSend
open PqxdhSecretInputKdf PqxdhJointKdfGame
open PqxdhServerAuthCtxCalls (Chain Material Kernel Residual step interpret)
open RawCtxSelectedReceiveCompiler (State project evaluated)

abbrev Pending := RawCtxChainSend.Seal Chain Chain Material RawCtxSourceSend.SealContext

def sealing (pending : Pending) : RawCtxInterpretedSend.Seal Material RawCtxSourceSend.SealContext :=
  RawCtxChainSend.nativeSeal (fun _ => RawCtxSelectedChain.unusedChain)
    (fun _ => RawCtxSelectedChain.unusedChain) pending

noncomputable def handler (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (rest : Residual) : QueryImpl (RawCtxChainSend.SendSpec Chain Chain Material
      RawCtxSourceSend.SealContext RawCtxSourceSend.Encrypted)
      (OptionT (OracleComp AdaptiveCtxDynamicKnownKeys.Spec))
  | .inl chain => pure (step source rest chain)
  | .inr pending => OptionT.mk (RawCtxSelectedSealConsumer.sealing source.crypto writer (sealing pending))

noncomputable def send (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (rest : Residual) (entry : Kernel) (context : RawCtxSourceSend.SealContext) :=
  (simulateQ (handler source writer rest) (RawCtxChainSend.execute entry context)).run

/-- The literal sending program retains nonce refusal, optional writer failure and complete pre-seal advancement separately. -/
theorem send_cases (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (rest : Residual) (entry : Kernel) (context : RawCtxSourceSend.SealContext) :
    send source writer rest entry context =
      match RawCtxChainSend.normalBegin entry context with
      | .exhausted previous _ => pure (some (previous, none))
      | .requested pending =>
          let ready := RawCtxChainSend.ready pending (step source rest pending.request)
          Option.map (fun encrypted => (ready.advanced, encrypted)) <$>
            RawCtxSelectedSealConsumer.sealing source.crypto writer (sealing ready) := by
  unfold send RawCtxChainSend.execute
  cases begun : RawCtxChainSend.normalBegin entry context with
  | exhausted previous actual => rfl
  | requested pending =>
      simp only [RawCtxChainSend.program, simulateQ_bind, simulateQ_spec_query, simulateQ_map, handler,
        pure_bind, bind_pure_comp, OptionT.run_map]
      rfl

noncomputable def sourceSealing {A : Type} (source : FixedHkdfSha512NoSaltSource)
    (writer : RawCtxMixedShared.Writer) (key : RootOutput) (pending : Pending) :
    StateT (RawCtxSharedPrimitive.SharedState A) ProbComp (Option RawCtxSourceSend.Encrypted) :=
  let native := RawCtxInterpretedSend.nativeSeal
    (RawCtxInterpretedSend.mapSeal (RawCtxSelectedMessageKey.interpret key) (sealing pending))
  Option.map (RawCtxSourceSend.encrypted (RawCtxSourceSend.arguments native)) <$>
    simulateQ (RawCtxCanonicalSeal.sharedImpl source.crypto writer (RawCtxSourceHkdf.kdfImpl source))
      (RawCtxSourceSeal.sealInput (RawCtxSourceSend.arguments native))

/-- Before explicit selected-nonce refusal, the callback has the exact original native optional writer result and complete shared cache. -/
theorem sealing_project {A : Type} (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (key : RootOutput) (read : RawCtxReceive.FrameDecoder) (pending : Pending) (state : State A)
    (fresh : ∀ nonce, pending.material = .hidden nonce → pending.context.associatedData.length = 153 →
      nonce ∉ state.2.selected.1.usedNonces) :
    (fun result => (some result.1, result.2)) <$> (sourceSealing source writer key pending).run (project state) =
      Prod.map id project <$> (evaluated source key read
        (RawCtxSelectedSealConsumer.sealing source.crypto writer (sealing pending))).run state := by
  simp only [sourceSealing, StateT.run_map]
  rw [RawCtxCanonicalSeal.shared_complete]
  have exactSource := congrArg (fun work => (fun result => (result.1, (state.1, result.2))) <$> work)
    (RawCtxSelectedSealConsumer.sealing_source (RawCtxUniversalDecoder.decoder read) source.crypto key writer
      (sealing pending) state.2 fresh)
  simpa only [evaluated, project, StateT.run, Functor.map_map, Prod.map_def, id_eq] using exactSource.symm

/-- Only a reached selected-material seal with valid source AD can refuse a nonce already used by the selected challenger. -/
def Repeated (pending : Pending) (state : AdaptiveCtxDynamicKnownKeys.SourceState) : Prop :=
  ∃ nonce, pending.material = .hidden nonce ∧ pending.context.associatedData.length = 153 ∧
    nonce ∈ state.selected.1.usedNonces

noncomputable local instance (pending : Pending) (state : AdaptiveCtxDynamicKnownKeys.SourceState) :
    Decidable (Repeated pending state) := Classical.propDecidable _

/-- All rejected, known and fresh-selected cases retain the exact native reply; nonce refusal keeps the full cache/state and remains an outer stop. -/
theorem sealing_cases {A : Type} (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (key : RootOutput) (read : RawCtxReceive.FrameDecoder) (pending : Pending) (state : State A) :
    Prod.map id project <$> (evaluated source key read
      (RawCtxSelectedSealConsumer.sealing source.crypto writer (sealing pending))).run state =
      if Repeated pending state.2 then pure (none, project state) else
        (fun result => (some result.1, result.2)) <$> (sourceSealing source writer key pending).run (project state) := by
  classical
  split
  · obtain ⟨nonce, material, width, used⟩ := ‹Repeated pending state.2›
    change Prod.map id project <$> ((fun result => (result.1, (state.1, result.2))) <$>
      (simulateQ (AdaptiveCtxDynamicKnownKeys.sourceImpl true (RawCtxUniversalDecoder.decoder read) source.crypto key)
        (RawCtxSelectedSealConsumer.sealing source.crypto writer (sealing pending))).run state.2) = _
    rw [RawCtxSelectedSealConsumer.sealing_repeat (RawCtxUniversalDecoder.decoder read) source.crypto key writer
      (sealing pending) nonce material width state.2 used]
    rfl
  · symm
    apply sealing_project
    intro nonce material width used
    exact ‹¬ Repeated pending state.2› ⟨nonce, material, width, used⟩

noncomputable def sourceHandler {A : Type} (source : FixedHkdfSha512NoSaltSource)
    (writer : RawCtxMixedShared.Writer) (key : RootOutput) (rest : Residual) :
    QueryImpl (RawCtxChainSend.SendSpec Chain Chain Material
      RawCtxSourceSend.SealContext RawCtxSourceSend.Encrypted)
      (StateT (RawCtxSharedPrimitive.SharedState A) ProbComp)
  | .inl chain => pure (step source rest chain)
  | .inr pending => sourceSealing source writer key pending

/-- The actual source retains the exact pending advanced state before the optional seal and writer result. -/
theorem source_cases {A : Type} (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (key : RootOutput) (rest : Residual) (entry : Kernel) (context : RawCtxSourceSend.SealContext) :
    simulateQ (sourceHandler (A := A) source writer key rest) (RawCtxChainSend.execute entry context) =
      match RawCtxChainSend.normalBegin entry context with
      | .exhausted previous _ => pure (previous, none)
      | .requested pending =>
          let ready := RawCtxChainSend.ready pending (step source rest pending.request)
          (fun encrypted => (ready.advanced, encrypted)) <$> sourceSealing source writer key ready := by
  unfold RawCtxChainSend.execute
  cases begun : RawCtxChainSend.normalBegin entry context with
  | exhausted previous actual => rfl
  | requested pending =>
      simp only [RawCtxChainSend.program, simulateQ_bind, simulateQ_spec_query, simulateQ_map,
        sourceHandler, pure_bind, bind_pure_comp]

noncomputable def Stops (source : FixedHkdfSha512NoSaltSource) (rest : Residual)
    (entry : Kernel) (context : RawCtxSourceSend.SealContext)
    (state : AdaptiveCtxDynamicKnownKeys.SourceState) : Prop :=
  match RawCtxChainSend.normalBegin entry context with
  | .exhausted _ _ => False
  | .requested pending => Repeated (RawCtxChainSend.ready pending (step source rest pending.request)) state

noncomputable local instance (source : FixedHkdfSha512NoSaltSource) (rest : Residual)
    (entry : Kernel) (context : RawCtxSourceSend.SealContext)
    (state : AdaptiveCtxDynamicKnownKeys.SourceState) : Decidable (Stops source rest entry context state) :=
  Classical.propDecidable _

/-- The complete source send agrees before its explicit repeated-selected-nonce stop; no fresh-nonce premise is inserted into the protocol theorem. Inner optional writer failure retains the actual advanced kernel. -/
theorem send_source {A : Type} (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (key : RootOutput) (rest : Residual) (read : RawCtxReceive.FrameDecoder)
    (entry : Kernel) (context : RawCtxSourceSend.SealContext) (state : State A) :
    Prod.map id project <$> (evaluated source key read (send source writer rest entry context)).run state =
      if Stops source rest entry context state.2 then pure (none, project state)
      else (fun result => (some result.1, result.2)) <$>
        (simulateQ (sourceHandler source writer key rest) (RawCtxChainSend.execute entry context)).run (project state) := by
  rw [send_cases, source_cases]
  cases started : RawCtxChainSend.normalBegin entry context with
  | exhausted previous actual =>
    have clear : ¬ Stops source rest entry context state.2 := by simp only [Stops, started, not_false_eq_true]
    simp only [ite_eq_right (fun h => (clear h).elim), StateT.run_pure, map_pure, project]
    rfl
  | requested pending =>
    have test : Stops source rest entry context state.2 ↔ Repeated
        (RawCtxChainSend.ready pending (step source rest pending.request)) state.2 := by simp only [Stops, started]
    simp only [test]
    rw [RawCtxSelectedReceiveCompiler.evaluated_map, StateT.run_map, Functor.map_map]
    let ready := RawCtxChainSend.ready pending (step source rest pending.request)
    have sealResult := sealing_cases source writer key read ready state
    have mapped := congrArg (fun work => (fun result =>
      (Option.map (fun encrypted => (ready.advanced, encrypted)) result.1, result.2)) <$> work) sealResult
    dsimp only [ready] at mapped
    simp only [Functor.map_map, Prod.map_def, id_eq, StateT.run_map, apply_ite, map_pure,
      Option.map_none, Option.map_some] at mapped ⊢
    convert mapped using 1

/-- The original native source callback expands into the same actual sealing, commitment and optional writer interpreter. No writer-success premise is used. -/
theorem native_sealing {A : Type} (source : FixedHkdfSha512NoSaltSource)
    (writer : RawCtxMixedShared.Writer) (pending : SendSeal RawCtxSourceSend.SealContext) :
    RawCtxSourceChainHandles.sendNative (Auxiliary := A) source writer (.inr pending) =
      Option.map (RawCtxSourceSend.encrypted (RawCtxSourceSend.arguments pending)) <$>
        simulateQ (RawCtxCanonicalSeal.sharedImpl source.crypto writer (RawCtxSourceHkdf.kdfImpl source))
          (RawCtxSourceSeal.sealInput (RawCtxSourceSend.arguments pending)) := by
  simp only [RawCtxSourceChainHandles.sendNative, QueryImpl.compose, RawCtxSourceSend.adapter,
    bind_pure_comp, RawCtxMixedOwner.sendAdapter, simulateQ_map, simulateQ_spec_query,
    RawCtxSourceSeal.nativeAdapter, ← QueryImpl.simulateQ_compose, RawCtxCanonicalSeal.sharedImpl,
    RawCtxSourceMaterialLabels.nativeImpl]
  simp only [QueryImpl.simulateQ_compose]

/-- Interpreting marker materials yields the existing actual factor-side source sender, with complete state and optional writer effects. -/
theorem send_material {A : Type} (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (key : RootOutput) (rest : Residual) (entry : Kernel) (context : RawCtxSourceSend.SealContext) :
    simulateQ (RawCtxSelectedChain.sendLabels (Auxiliary := A) source writer
      (PqxdhServerAuthCtxMaterial.factor (PqxdhServerAuthCtxMaterial.output key rest)).1)
        (RawCtxChainSend.execute (interpret key entry) context) =
      (fun result => (interpret key result.1, result.2)) <$>
        simulateQ (sourceHandler source writer key rest) (RawCtxChainSend.execute entry context) := by
  apply RawCtxChainMaterialMap.send_execute (RawCtxSelectedMessageKey.interpret key)
    (sourceHandler source writer key rest) (RawCtxSelectedChain.sendLabels source writer
      (PqxdhServerAuthCtxMaterial.factor (PqxdhServerAuthCtxMaterial.output key rest)).1)
  · intro chain
    simp only [RawCtxSelectedChain.sendLabels, sourceHandler, map_pure, PqxdhServerAuthCtxCalls.step_source]
  · intro pending
    simp only [RawCtxSelectedChain.sendLabels, sourceHandler, native_sealing, sourceSealing]
    rfl

/-- The full source-factor sender and compiled CTX service have the same result and shared cache after material interpretation, except for the explicit selected-nonce refusal. -/
theorem factor_send {A : Type} (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (key : RootOutput) (rest : Residual) (read : RawCtxReceive.FrameDecoder)
    (entry : Kernel) (context : RawCtxSourceSend.SealContext) (state : State A) :
    (fun result => (Option.map (fun value => (interpret key value.1, value.2)) result.1, project result.2)) <$>
        (evaluated source key read (send source writer rest entry context)).run state =
      if Stops source rest entry context state.2 then pure (none, project state)
      else (fun result => (some result.1, result.2)) <$>
        (simulateQ (RawCtxSelectedChain.sendLabels source writer
          (PqxdhServerAuthCtxMaterial.factor (PqxdhServerAuthCtxMaterial.output key rest)).1)
            (RawCtxChainSend.execute (interpret key entry) context)).run (project state) := by
  have mapped := congrArg (fun work => (fun result =>
    (Option.map (fun value => (interpret key value.1, value.2)) result.1, result.2)) <$> work)
    (send_source source writer key rest read entry context state)
  rw [send_material, StateT.run_map]
  simpa only [Functor.map_map, Prod.map_def, id_eq, apply_ite, map_pure, Option.map_none, Option.map_some] using mapped

/-- A whole sending attempt uses at most one dynamic component query, including exhaustion, writer failure and nonce refusal. The separate source chain derivation still costs one real callback. -/
theorem send_bound (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (rest : Residual) (entry : Kernel) (context : RawCtxSourceSend.SealContext) :
    (send source writer rest entry context).IsTotalQueryBound 1 := by
  rw [send_cases]
  cases RawCtxChainSend.normalBegin entry context with
  | exhausted => trivial
  | requested pending =>
      simp only [IsTotalQueryBound, isQueryBound_map_iff]
      exact RawCtxSelectedSendCompiler.sealing_queries source.crypto writer _

/-- Sending contributes no selected raw-opening or uniform requests, including known local seals and nonce refusal. -/
theorem send_other (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (rest : Residual) (entry : Kernel) (context : RawCtxSourceSend.SealContext) :
    (send source writer rest entry context).IsQueryBoundP
        (AdaptiveCtxDynamicKnownBounds.TargetClass AdaptiveCtxReceive.IsRawQuery) 0 ∧
      (send source writer rest entry context).IsQueryBoundP AdaptiveCtxDynamicKnownBounds.UniformRoute 0 := by
  rw [send_cases]
  cases RawCtxChainSend.normalBegin entry context with
  | exhausted => exact ⟨by trivial, by trivial⟩
  | requested pending =>
      simp only [isQueryBoundP_map_iff]
      exact (RawCtxSelectedSealConsumer.sealing_bills source.crypto writer _).2.2

/-- Every complete receive contributes zero selected seal and uniform requests; known-chain deterministic work is unchanged. -/
theorem receive_other (source : FixedHkdfSha512NoSaltSource) (rest : Residual)
    (read : RawCtxReceive.FrameDecoder) (expected : Std.U64) (entry : Kernel)
    (target : Std.U64) (context : RawCtxWholeOwner.OpenContext) :
    (simulateQ (PqxdhServerAuthCtxCalls.receive source rest read expected)
      (RawCtxChainReceive.execute entry target context)).IsQueryBoundP
        (AdaptiveCtxDynamicKnownBounds.TargetClass AdaptiveCtxQueryBounds.SourceSeal) 0 ∧
      (simulateQ (PqxdhServerAuthCtxCalls.receive source rest read expected)
        (RawCtxChainReceive.execute entry target context)).IsQueryBoundP AdaptiveCtxDynamicKnownBounds.UniformRoute 0 := by
  constructor
  all_goals
    apply RawCtxSourceOpen.simulate_bound (PqxdhServerAuthCtxCalls.receive source rest read expected)
      (fun _ => False) _ _ 0 (isQueryBoundP_false _ 0)
    intro query
    cases query with
    | inl chain => trivial
    | inr pending =>
        simp only [ite_false]
        first
        | exact (RawCtxSelectedOpenConsumer.service_other 0 read expected (PqxdhServerAuthCtxCalls.opening pending)).1
        | exact (RawCtxSelectedOpenConsumer.service_other 0 read expected (PqxdhServerAuthCtxCalls.opening pending)).2

/-- Arbitrary raw delivery retains those zero selected-seal and uniform bills across all source parser and validation branches. -/
theorem raw_other {Metadata : Type} (source : FixedHkdfSha512NoSaltSource) (rest : Residual)
    (read : RawCtxReceive.FrameDecoder) (bytes : Pqxdh.Bytes)
    (owner : RawCtxChainOwner.State Kernel Metadata) :
    (PqxdhServerAuthCtxCalls.raw source rest read bytes owner).IsQueryBoundP
        (AdaptiveCtxDynamicKnownBounds.TargetClass AdaptiveCtxQueryBounds.SourceSeal) 0 ∧
      (PqxdhServerAuthCtxCalls.raw source rest read bytes owner).IsQueryBoundP AdaptiveCtxDynamicKnownBounds.UniformRoute 0 := by
  unfold PqxdhServerAuthCtxCalls.raw RawCtxChainOwner.rawReceive
  dsimp only [StateT.run]
  split
  · exact ⟨by trivial, by trivial⟩
  · split
    · exact ⟨by trivial, by trivial⟩
    · split
      · simp only [bind_pure_comp, isQueryBoundP_map_iff, PqxdhServerAuthCtxCalls.calls]
        exact receive_other source rest read _ owner.kernel _ _
      · exact ⟨by trivial, by trivial⟩

end BeaconcryptCore.Computational.PqxdhServerAuthCtxSend

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxSend.send_cases' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxSend.send_cases

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxSend.sealing_project' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxSend.sealing_project

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxSend.sealing_cases' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxSend.sealing_cases

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxSend.source_cases' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxSend.source_cases

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxSend.send_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxSend.send_source

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxSend.native_sealing' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxSend.native_sealing

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxSend.send_material' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxSend.send_material

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxSend.factor_send' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxSend.factor_send

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxSend.send_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxSend.send_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxSend.send_other' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxSend.send_other

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxSend.receive_other' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxSend.receive_other

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxSend.raw_other' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxSend.raw_other
