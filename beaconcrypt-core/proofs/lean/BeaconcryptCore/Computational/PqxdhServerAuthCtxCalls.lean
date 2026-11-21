import BeaconcryptCore.Computational.PqxdhServerAuthCtxMaterial
import BeaconcryptCore.Computational.RawCtxChainMaterialMap
import BeaconcryptCore.Computational.RawCtxSelectedOpenConsumer
import BeaconcryptCore.Computational.RawCtxSelectedSealConsumer
import BeaconcryptCore.Computational.RawCtxSelectedReceiveCompiler

/-!
The selected first-record factor is consumed with a private material marker. The executable callbacks receive the nonce and both known subsequent chain coordinates, but require no selected-message-key argument. Known chain requests keep their real fixed HKDF evaluation, and selected raw openings return the actual optional challenger plaintext through the original getters.
-/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.refined ratchet.concrete
set_option autoImplicit false

namespace BeaconcryptCore.Computational.PqxdhServerAuthCtxCalls
open PqxdhSecretInputKdf PqxdhFullSecretInputKdf PqxdhJointKdfGame
open RawCtxMaterialInterpretation RawCtxChainInterpretation

abbrev Chain := RawCtxSelectedChain.Slot
abbrev Material := RawCtxSelectedMessageKey.Slot
abbrev Kernel := RefinedRatchet Chain Chain Material
abbrev Residual := PqxdhServerAuthCtxMaterial.Residual

def interpret (key : RootOutput) (entry : Kernel) : RawCtxSelectedChain.Kernel :=
  mapRefined (RawCtxSelectedMessageKey.interpret key) entry

def initial (beacon : Bool) (other : RootOutput) : RustM Kernel :=
  RefinedRatchet.new Material (RawCtxSelectedInitialConstructor.sendSlot beacon other)
    (RawCtxSelectedInitialConstructor.receiveSlot beacon other)

/-- The actual initial zero-counter/empty-cache constructor does not require the selected material key. -/
theorem initial_source (beacon : Bool) (other key : RootOutput) :
    RawCtxSelectedInitialConstructor.initial beacon other = interpret key <$> initial beacon other := by
  exact from_counters_map (RawCtxSelectedMessageKey.interpret key)
      (RawCtxSelectedInitialConstructor.sendSlot beacon other)
      (RawCtxSelectedInitialConstructor.receiveSlot beacon other) 0#u64 0#u64

/-- The hidden first chain yields one material marker; later known chains use the actual production KDF. -/
noncomputable def step (source : FixedHkdfSha512NoSaltSource) (rest : Residual) : Chain → Chain × Material
  | .hidden => (.known (RawCtxFreshChainCut.concreteChain rest.2.1), .hidden rest.1)
  | .known chain =>
      let reply := RawCtxInterpretedReceive.decodeResponse
        (RawCtxSourceHkdf.response source.crypto (RawCtxChainSend.nativeRequest chain))
      (.known reply.1, .known reply.2)

/-- The literal decoded 108-byte factor gives the same joint response after material interpretation, including known byte aliases. -/
theorem step_source (source : FixedHkdfSha512NoSaltSource) (key : RootOutput) (rest : Residual)
    (chain : Chain) :
    RawCtxSelectedChain.step source (PqxdhServerAuthCtxMaterial.factor
        (PqxdhServerAuthCtxMaterial.output key rest)).1 chain =
      (fun reply => (reply.1, RawCtxSelectedMessageKey.interpret key reply.2)) (step source rest chain) := by
  cases chain with
  | hidden =>
      simp only [RawCtxSelectedChain.step, PqxdhServerAuthCtxMaterial.output_decoded, step]
  | known chain => rfl

/-- Filling only unread chain fields leaves the literal opening arguments intact. -/
def opening (pending : RawCtxInterpretedOpening.Opening Chain Chain Material RawCtxWholeOwner.OpenContext) :
    RawCtxInterpretedOpening.Opening RatchetChain RatchetChain Material RawCtxWholeOwner.OpenContext :=
  mapOpeningChains (fun _ => RawCtxSelectedChain.unusedChain)
    (fun _ => RawCtxSelectedChain.unusedChain) pending

noncomputable def receive (source : FixedHkdfSha512NoSaltSource) (rest : Residual)
    (read : RawCtxReceive.FrameDecoder) (expected : Std.U64) :
    QueryImpl (RawCtxChainReceive.ReceiveSpec Chain Chain Material RawCtxWholeOwner.OpenContext
      RawCtxWholeOwner.Decrypted) (OracleComp AdaptiveCtxDynamicKnownKeys.Spec)
  | .inl chain => pure (step source rest chain)
  | .inr pending => RawCtxSelectedOpenConsumer.service 0 read expected (opening pending)

/-- The chain-opaque source driver retains the actual raw target and immutable prepared context. -/
def Scope (target : Std.U64) (context : RawCtxWholeOwner.OpenContext) :
    RawCtxChainReceive.Effect Chain Chain Material RawCtxWholeOwner.OpenContext → Prop
  | .rejected _ actual => actual = context
  | .kdfRequested pending => pending.target = target ∧ pending.context = context
  | .openRequested pending => RawCtxInterpretedOpening.sequence pending = ok target ∧ pending.context = context

/-- Replacing unread chain coordinates changes neither target nor context. -/
theorem scope_chains (target : Std.U64) (context : RawCtxWholeOwner.OpenContext)
    (effect : RawCtxChainReceive.Effect Chain Chain Material RawCtxWholeOwner.OpenContext) :
    RawCtxSelectedReceiveScope.Scope target context (RawCtxChainReceive.nativeEffect
      (fun _ => RawCtxSelectedChain.unusedChain) (fun _ => RawCtxSelectedChain.unusedChain) effect) ↔
      Scope target context effect := by
  cases effect with
  | rejected => rfl
  | kdfRequested => rfl
  | openRequested pending =>
      simp only [RawCtxChainReceive.nativeEffect, RawCtxSelectedReceiveScope.Scope,
        opening_sequence_chains, Scope]
      rfl

/-- Every actual raw admission preserves the original decoded target and context. -/
theorem begin_scope (entry : Kernel) (target : Std.U64) (context : RawCtxWholeOwner.OpenContext) :
    Scope target context (RawCtxChainReceive.normalBegin entry target context) := by
  apply (scope_chains target context _).mp
  rw [← RawCtxChainReceive.normalBegin_native]
  exact RawCtxSelectedReceiveScope.begin_scope (RawCtxSelectedMessageKey.interpret
    ⟨List.replicate 32 (0 : UInt8), by simp⟩) _ target context

/-- Every actual typed reply preserves that scope before the next callback. -/
theorem resume_scope
    (pending : RawCtxChainReceive.Kdf Chain Chain Material RawCtxWholeOwner.OpenContext)
    (reply : Chain × Material) :
    Scope pending.target pending.context (RawCtxChainReceive.normalResume pending reply) := by
  apply (scope_chains pending.target pending.context _).mp
  rw [← RawCtxChainReceive.normalResume_native]
  exact RawCtxSelectedReceiveScope.resume_scope _ _

/-- State projection is required only on the actual source target and raw context, including rejected openings. -/
theorem program_projection {Small Large : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (project : Large → Small)
    (original : QueryImpl (RawCtxChainReceive.ReceiveSpec Chain Chain Material RawCtxWholeOwner.OpenContext
      RawCtxWholeOwner.Decrypted) (StateT Small m))
    (compiled : QueryImpl (RawCtxChainReceive.ReceiveSpec Chain Chain Material RawCtxWholeOwner.OpenContext
      RawCtxWholeOwner.Decrypted) (StateT Large m))
    (target : Std.U64) (context : RawCtxWholeOwner.OpenContext)
    (deriveMap : ∀ request state, (original (.inl request)).run (project state) =
      Prod.map id project <$> (compiled (.inl request)).run state)
    (openMap : ∀ pending state, RawCtxInterpretedOpening.sequence pending = ok target → pending.context = context →
      (original (.inr pending)).run (project state) = Prod.map id project <$> (compiled (.inr pending)).run state)
    (effect : RawCtxChainReceive.Effect Chain Chain Material RawCtxWholeOwner.OpenContext)
    (inScope : Scope target context effect) (state : Large) :
    (simulateQ original (RawCtxChainReceive.program effect)).run (project state) =
      Prod.map id project <$> (simulateQ compiled (RawCtxChainReceive.program effect)).run state := by
  generalize hdepth : RawCtxChainReceive.effectRank effect = depth
  induction depth using Nat.strong_induction_on generalizing effect state with
  | h depth ih =>
    cases effect with
    | rejected entry actual => simp only [RawCtxChainReceive.program, simulateQ_pure, StateT.run_pure, map_pure]; rfl
    | openRequested pending =>
      simp only [RawCtxChainReceive.program, simulateQ_bind, simulateQ_spec_query, simulateQ_pure, StateT.run_bind, StateT.run_pure]
      rw [openMap pending state inScope.1 inScope.2]
      simp only [bind_map_left, map_bind, map_pure, Prod.map_def, id_eq]
    | kdfRequested pending =>
      simp only [RawCtxChainReceive.program, simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
      rw [deriveMap pending.request state]
      simp only [bind_map_left, map_bind, Prod.map_def, id_eq]
      apply bind_congr
      intro result
      exact ih _ (hdepth ▸ RawCtxChainReceive.normalResume_rank pending result.1) _
        (by simpa only [inScope.1, inScope.2] using resume_scope pending result.1) result.2 rfl

open RawCtxSelectedReceiveCompiler (State project evaluated)

noncomputable def sourceReceive {A : Type} (source : FixedHkdfSha512NoSaltSource)
    (key : RootOutput) (rest : Residual) :
    QueryImpl (RawCtxChainReceive.ReceiveSpec Chain Chain Material RawCtxWholeOwner.OpenContext
      RawCtxWholeOwner.Decrypted) (StateT (RawCtxSharedPrimitive.SharedState A) ProbComp)
  | .inl chain => pure (step source rest chain)
  | .inr pending => simulateQ (RawCtxSharedPrimitive.nativeImpl source.crypto (RawCtxSourceHkdf.kdfImpl source))
      (RawCtxSourceOpen.ownerAdapter (.inr (RawCtxInterpretedOpening.toNative
        (RawCtxInterpretedOpening.mapOpening (RawCtxSelectedMessageKey.interpret key) (opening pending)))))

/-- The reached native callback and its actual optional API plaintext are the selected or known CTX service with only bookkeeping erased. -/
theorem opening_project {A : Type} (source : FixedHkdfSha512NoSaltSource) (key : RootOutput)
    (rest : Residual) (read : RawCtxReceive.FrameDecoder) (expected : Std.U64)
    (pending : RawCtxInterpretedOpening.Opening Chain Chain Material RawCtxWholeOwner.OpenContext)
    (state : State A)
    (nonempty : pending.context.raw.isEmpty = false) (decoded : read pending.context.raw = some pending.context.frame)
    (valid : RawCtxReceive.ValidFrame expected pending.context.associatedData pending.context.frame)
    (prepared : RawCtxInterpretedOpening.sequence pending = ok pending.context.frame.sequence) :
    (sourceReceive source key rest (.inr pending)).run (project state) =
      Prod.map id project <$> (evaluated source key read (receive source rest read expected (.inr pending))).run state := by
  obtain ⟨slices, parsed⟩ : ∃ slices, RawCtxFrameDecoding.fromPayload pending.context.frame.payload = some slices := by
    simp only [RawCtxFrameDecoding.fromPayload, ite_eq_right (show ¬ pending.context.frame.payload.length ≤ 80 by have := valid.2.1; omega)]
    exact ⟨_, rfl⟩
  simp only [sourceReceive, receive, project, evaluated, StateT.run, Functor.map_map, Prod.map_def, id_eq]
  apply RawCtxSelectedOpenConsumer.service_source 0 read expected key source.crypto (RawCtxSourceHkdf.kdfImpl source)
    (opening pending) state.1 state.2 nonempty decoded valid _ slices parsed
  change RawCtxInterpretedOpening.sequence (mapOpeningChains _ _ pending) = ok pending.context.frame.sequence
  rw [opening_sequence_chains]
  exact prepared

/-- Every marker KDF response is retained exactly and uses no CTX oracle call; known-chain HKDF work remains the real pure source operation. -/
theorem derive_project {A : Type} (source : FixedHkdfSha512NoSaltSource) (key : RootOutput)
    (rest : Residual) (read : RawCtxReceive.FrameDecoder) (expected : Std.U64)
    (chain : Chain) (state : State A) :
    (sourceReceive source key rest (.inl chain)).run (project state) =
      Prod.map id project <$> (evaluated source key read (receive source rest read expected (.inl chain))).run state := by
  rfl

/-- The complete reached receive loop preserves cached and future paths, all source state and the actual optional plaintext, with no acceptance premise. -/
theorem receive_project {A : Type} (source : FixedHkdfSha512NoSaltSource) (key : RootOutput)
    (rest : Residual) (read : RawCtxReceive.FrameDecoder) (expected : Std.U64)
    (entry : Kernel) (context : RawCtxWholeOwner.OpenContext) (state : State A)
    (nonempty : context.raw.isEmpty = false) (decoded : read context.raw = some context.frame)
    (valid : RawCtxReceive.ValidFrame expected context.associatedData context.frame) :
    (simulateQ (sourceReceive source key rest)
      (RawCtxChainReceive.execute entry context.frame.sequence context)).run (project state) =
      Prod.map id project <$> (evaluated source key read
        (simulateQ (receive source rest read expected)
          (RawCtxChainReceive.execute entry context.frame.sequence context))).run state := by
  rw [← RawCtxSelectedReceiveCompiler.evaluated_program]
  apply program_projection project (sourceReceive source key rest)
    (fun query => evaluated source key read (receive source rest read expected query)) context.frame.sequence context
  · exact derive_project source key rest read expected
  · intro pending before sequence same
    exact opening_project source key rest read expected pending before (same ▸ nonempty)
      (same ▸ decoded) (same ▸ valid) (by simpa only [same] using sequence)
  · exact begin_scope entry context.frame.sequence context

/-- The concrete value-side callback matches the existing source primitive handler, with both omitted chain fields unread by the adapter. -/
noncomputable def valueReceive {A : Type} (source : FixedHkdfSha512NoSaltSource) (key : RootOutput)
    (rest : Residual) : QueryImpl (RawCtxChainReceive.ReceiveSpec Chain Chain RatchetMaterial
      RawCtxWholeOwner.OpenContext RawCtxWholeOwner.Decrypted)
      (StateT (RawCtxSharedPrimitive.SharedState A) ProbComp)
  | .inl chain => pure (RawCtxSelectedChain.step source
      (PqxdhServerAuthCtxMaterial.factor (PqxdhServerAuthCtxMaterial.output key rest)).1 chain)
  | .inr pending => simulateQ (RawCtxSharedPrimitive.nativeImpl source.crypto (RawCtxSourceHkdf.kdfImpl source))
      (RawCtxSourceOpen.ownerAdapter (.inr (RawCtxInterpretedOpening.toNative
        (mapOpeningChains (fun _ => RawCtxSelectedChain.unusedChain)
          (fun _ => RawCtxSelectedChain.unusedChain) pending))))

/-- Interpreting the private material marker gives the complete actual factor-side driver, without equality or independence assumptions on known keys. -/
theorem receive_material {A : Type} (source : FixedHkdfSha512NoSaltSource) (key : RootOutput)
    (rest : Residual) (entry : Kernel) (target : Std.U64) (context : RawCtxWholeOwner.OpenContext) :
    simulateQ (valueReceive (A := A) source key rest)
        (RawCtxChainReceive.execute (interpret key entry) target context) =
      (fun result => (interpret key result.1, result.2)) <$>
        simulateQ (sourceReceive source key rest) (RawCtxChainReceive.execute entry target context) := by
  apply RawCtxChainMaterialMap.receive_execute (RawCtxSelectedMessageKey.interpret key)
    (sourceReceive source key rest) (valueReceive source key rest)
  · intro chain
    simp only [valueReceive, sourceReceive, map_pure, step_source]
  · rintro ⟨kernel, context, prepared⟩
    cases prepared <;> rfl

/-- The actual full factor-side receive is the executable selected/known CTX client after interpreting only its private material slots and projecting component bookkeeping. -/
theorem receive_source {A : Type} (source : FixedHkdfSha512NoSaltSource) (key : RootOutput)
    (rest : Residual) (read : RawCtxReceive.FrameDecoder) (expected : Std.U64)
    (entry : Kernel) (context : RawCtxWholeOwner.OpenContext) (state : State A)
    (nonempty : context.raw.isEmpty = false) (decoded : read context.raw = some context.frame)
    (valid : RawCtxReceive.ValidFrame expected context.associatedData context.frame) :
    (simulateQ (valueReceive source key rest)
      (RawCtxChainReceive.execute (interpret key entry) context.frame.sequence context)).run (project state) =
      (fun result => ((interpret key result.1.1, result.1.2), project result.2)) <$>
        (evaluated source key read (simulateQ (receive source rest read expected)
          (RawCtxChainReceive.execute entry context.frame.sequence context))).run state := by
  rw [receive_material, StateT.run_map, receive_project source key rest read expected entry context state nonempty decoded valid]
  simp only [Functor.map_map, Prod.map_def, id_eq]

/-- Actual derivations make zero component queries and the reached optional opening makes at most one. -/
theorem receive_callback_bound (source : FixedHkdfSha512NoSaltSource) (rest : Residual)
    (read : RawCtxReceive.FrameDecoder) (expected : Std.U64)
    (query : (RawCtxChainReceive.ReceiveSpec Chain Chain Material RawCtxWholeOwner.OpenContext
      RawCtxWholeOwner.Decrypted).Domain) :
    (receive source rest read expected query).IsTotalQueryBound (if query.isRight = true then 1 else 0) := by
  cases query with
  | inl chain => trivial
  | inr pending => exact RawCtxSelectedOpenConsumer.service_total 0 read expected (opening pending)

/-- Each complete receive attempt has at most one dynamic CTX call, including every rejection path; its distinct source KDF allowance remains at most 51. -/
theorem receive_bound (source : FixedHkdfSha512NoSaltSource) (rest : Residual)
    (read : RawCtxReceive.FrameDecoder) (expected : Std.U64) (entry : Kernel)
    (target : Std.U64) (context : RawCtxWholeOwner.OpenContext) :
    (simulateQ (receive source rest read expected)
      (RawCtxChainReceive.execute entry target context)).IsTotalQueryBound 1 := by
  have bounded := RawCtxSourceOpen.simulate_bound (receive source rest read expected)
    (fun query => query.isRight = true) (fun _ => True)
    (RawCtxChainReceive.execute entry target context) 1
    (RawCtxChainReceiveBounds.program_open_bound _)
    (fun query => by simpa only [IsTotalQueryBound, IsQueryBoundP, not_true_eq_false, false_or, ite_true]
      using receive_callback_bound source rest read expected query)
  simpa only [IsTotalQueryBound, IsQueryBoundP, not_true_eq_false, false_or, ite_true] using bounded

noncomputable def calls (source : FixedHkdfSha512NoSaltSource) (rest : Residual)
    (read : RawCtxReceive.FrameDecoder) :
    RawCtxChainOwner.Calls Kernel (OracleComp AdaptiveCtxDynamicKnownKeys.Spec) where
  receive entry target context := simulateQ (receive source rest read context.frame.sender)
    (RawCtxChainReceive.execute entry target context)
  send entry _ := pure (entry, none)

noncomputable def valueCalls {A : Type} (source : FixedHkdfSha512NoSaltSource) (key : RootOutput)
    (rest : Residual) : RawCtxChainOwner.Calls RawCtxSelectedChain.Kernel
      (StateT (RawCtxSharedPrimitive.SharedState A) ProbComp) where
  receive entry target context := simulateQ (valueReceive source key rest)
    (RawCtxChainReceive.execute entry target context)
  send entry _ := pure (entry, none)

def mapOwner {Metadata : Type} (key : RootOutput) (owner : RawCtxChainOwner.State Kernel Metadata) :
    RawCtxChainOwner.State RawCtxSelectedChain.Kernel Metadata :=
  ⟨interpret key owner.kernel, owner.expectedSender, owner.associatedData, owner.metadata, owner.rawAttempts⟩

noncomputable def raw {Metadata : Type} (source : FixedHkdfSha512NoSaltSource) (rest : Residual)
    (read : RawCtxReceive.FrameDecoder) (bytes : Pqxdh.Bytes)
    (owner : RawCtxChainOwner.State Kernel Metadata) :=
  (RawCtxChainOwner.rawReceive (calls source rest read) read bytes).run owner

set_option backward.isDefEq.respectTransparency false in
/-- The actual raw owner prelude discharges all reached-opening conditions. Its complete result includes parser/validation rejection, rollback, successful consumption and the incremented raw-attempt count. -/
theorem raw_source {A Metadata : Type} (source : FixedHkdfSha512NoSaltSource) (key : RootOutput)
    (rest : Residual) (read : RawCtxReceive.FrameDecoder) (bytes : Pqxdh.Bytes)
    (owner : RawCtxChainOwner.State Kernel Metadata) (state : State A) :
    ((RawCtxChainOwner.rawReceive (valueCalls source key rest) read bytes).run (mapOwner key owner)).run (project state) =
      (fun result => ((result.1.1, mapOwner key result.1.2), project result.2)) <$>
        (evaluated source key read (raw source rest read bytes owner)).run state := by
  unfold raw RawCtxChainOwner.rawReceive
  simp only [StateT.run, mapOwner]
  by_cases empty : bytes.isEmpty = true
  · simp only [empty, ite_true, evaluated, simulateQ_pure, StateT.run_pure, map_pure, project]
    rfl
  · simp only [empty, Bool.false_eq_true, ite_false]
    cases decoded : read bytes with
    | none =>
      simp only [evaluated, simulateQ_pure, StateT.run_pure, map_pure, project]
      rfl
    | some frame =>
      dsimp only
      by_cases valid : RawCtxReceive.ValidFrame owner.expectedSender owner.associatedData frame
      · simp only [valid, ite_true, bind_pure_comp, calls, valueCalls]
        rw [RawCtxSelectedReceiveCompiler.evaluated_map]
        change (RawCtxChainOwner.publish (mapOwner key owner) <$>
          simulateQ (valueReceive source key rest) (RawCtxChainReceive.execute (interpret key owner.kernel)
            frame.sequence ⟨bytes, frame, owner.associatedData⟩)).run (project state) =
          (fun result => ((result.1.1, mapOwner key result.1.2), project result.2)) <$>
            (RawCtxChainOwner.publish owner <$> evaluated source key read
              (simulateQ (receive source rest read frame.sender)
                (RawCtxChainReceive.execute owner.kernel frame.sequence
                  ⟨bytes, frame, owner.associatedData⟩))).run state
        rw [StateT.run_map,
          receive_source source key rest read frame.sender owner.kernel
            ⟨bytes, frame, owner.associatedData⟩ state (by simpa using empty) decoded ⟨rfl, valid.2⟩,
          StateT.run_map]
        simp only [Functor.map_map]
        rfl
      · simp only [valid, ite_false, evaluated, simulateQ_pure, StateT.run_pure, map_pure, project]
        rfl

/-- The raw-attempt cap is one dynamic call even for arbitrary invalid bytes and all optional replies. It counts attempts, not successful openings. -/
theorem raw_bound {Metadata : Type} (source : FixedHkdfSha512NoSaltSource) (rest : Residual)
    (read : RawCtxReceive.FrameDecoder) (bytes : Pqxdh.Bytes)
    (owner : RawCtxChainOwner.State Kernel Metadata) :
    (raw source rest read bytes owner).IsTotalQueryBound 1 := by
  unfold raw RawCtxChainOwner.rawReceive
  dsimp only [StateT.run]
  split
  · trivial
  · split
    · trivial
    · split
      · simp only [bind_pure_comp, IsTotalQueryBound, isQueryBound_map_iff, calls]
        exact receive_bound source rest read _ owner.kernel _ _
      · trivial

end BeaconcryptCore.Computational.PqxdhServerAuthCtxCalls

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxCalls.initial_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxCalls.initial_source

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxCalls.step_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxCalls.step_source

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxCalls.scope_chains' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxCalls.scope_chains

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxCalls.begin_scope' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxCalls.begin_scope

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxCalls.resume_scope' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxCalls.resume_scope

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxCalls.program_projection' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxCalls.program_projection

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxCalls.opening_project' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxCalls.opening_project

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxCalls.derive_project' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxCalls.derive_project

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxCalls.receive_project' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxCalls.receive_project

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxCalls.receive_material' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxCalls.receive_material

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxCalls.receive_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxCalls.receive_source

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxCalls.receive_callback_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxCalls.receive_callback_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxCalls.receive_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxCalls.receive_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxCalls.raw_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxCalls.raw_source

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxCalls.raw_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxCalls.raw_bound
