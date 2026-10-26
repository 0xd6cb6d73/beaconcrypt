import BeaconcryptCore.Computational.RawCtxSelectedSendCompiler

/-!
The original mixed owner uses the key-free selected receive and send programs. Every raw delivery retains the actual optional opening result and publication; every send retains the empty-input gate, exact source derivation and optional writer result. The sole outer stop is the actual selected sealing nonce refusal. The compiler's state is the full private owner, while the source equation retains all ambient source state and the shared cache.
-/
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.refined ratchet.concrete
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RawCtxSelectedOwnerCompiler
open PqxdhSecretInputKdf PqxdhFullSecretInputKdf PqxdhJointKdfGame
open RawCtxSelectedParentTable RawCtxSelectedParentEntry
open RawCtxSelectedReceiveCompiler (State project evaluated)
open RawCtxSelectedMessageDriver
variable {A Metadata : Type}

abbrev Kernel := RawCtxSelectedMessageReveals.Kernel
abbrev Base := OracleComp AdaptiveCtxDynamicKnownKeys.Spec

private theorem state_map_apply {X Y σ : Type} {m : Type → Type*} [Monad m] [LawfulMonad m]
    (f : X → Y) (work : StateT σ m X) (state : σ) :
    (f <$> work) state = (fun result => (f result.1, result.2)) <$> work state := by
  change (f <$> work).run state = _
  rw [StateT.run_map]
  rfl

noncomputable def calls (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (parent : Option Entry) (target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (read : RawCtxReceive.FrameDecoder) : RawCtxChainOwner.Calls Kernel (OptionT Base) where
  receive kernel sequence context := OptionT.mk (some <$>
    RawCtxSelectedReceiveCompiler.receive prior parent target nonce next read context.frame.sender kernel sequence context)
  send kernel context := OptionT.mk (RawCtxSelectedSendCompiler.send source writer prior parent target nonce next kernel context)

noncomputable def originalCalls (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (parent : Option Entry) (key target : RootOutput) (nonce : NonceOutput) (next : RootOutput) :
    RawCtxChainOwner.Calls Kernel (StateT (RawCtxSharedPrimitive.SharedState A) ProbComp) :=
  RawCtxSelectedMessageFamily.calls (receiveServices source writer prior parent key target nonce next)
    (sendServices source writer prior parent key target nonce next) parent target nonce next

noncomputable def owner (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (parent : Option Entry) (target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (read : RawCtxReceive.FrameDecoder) (sender : Std.U64) (query : RawCtxMixedOwner.SourceSpec.Domain)
    (before : RawCtxChainOwner.State Kernel Metadata) :
    Base (Option (RawCtxMixedOwner.SourceSpec.Range query × RawCtxChainOwner.State Kernel Metadata)) :=
  ((RawCtxChainOwner.ownerImpl (calls source writer prior parent target nonce next read) sender read query).run before).run

/-- The original raw owner has no selected nonce-stop branch. It preserves the received optional plaintext and the complete published owner. -/
theorem raw_cases (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (parent : Option Entry) (target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (read : RawCtxReceive.FrameDecoder) (sender : Std.U64) (raw : Pqxdh.Bytes)
    (before : RawCtxChainOwner.State Kernel Metadata) :
    owner source writer prior parent target nonce next read sender (.inr raw) before =
      some <$> RawCtxSelectedReceiveCompiler.raw prior parent target nonce next read raw before := by
  unfold owner RawCtxChainOwner.ownerImpl RawCtxSelectedReceiveCompiler.raw RawCtxChainOwner.rawReceive
  simp only [StateT.run]
  split
  · rfl
  · split
    · rfl
    · split
      · simp only [calls, RawCtxSelectedReceiveCompiler.calls, bind_pure_comp, OptionT.run_map,
          OptionT.run_mk, Functor.map_map, Option.map_some]
      · rfl

/-- The source send gate precedes the same actual derivation and optional seal; the outer stop never becomes an ordinary writer failure. -/
theorem send_cases (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (parent : Option Entry) (target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (read : RawCtxReceive.FrameDecoder) (sender : Std.U64) (plaintext : Pqxdh.Bytes)
    (before : RawCtxChainOwner.State Kernel Metadata) :
    owner source writer prior parent target nonce next read sender (.inl plaintext) before =
      if plaintext.isEmpty then pure (some (none, before)) else
        Option.map (fun result => (result.2, { before with kernel := result.1 })) <$>
          RawCtxSelectedSendCompiler.send source writer prior parent target nonce next before.kernel
            ⟨plaintext, before.expectedSender, sender, before.associatedData⟩ := by
  unfold owner RawCtxChainOwner.ownerImpl RawCtxChainOwner.sendOwner
  simp only [StateT.run]
  split
  · rfl
  · simp only [calls, OptionT.run_bind, OptionT.run_mk, OptionT.run_pure, map_eq_bind_pure_comp]
    apply bind_congr
    intro reply
    cases reply <;> rfl

/-- Every raw API attempt compiles to its complete unchanged native-material owner result and source state, with no parser or success premise. -/
theorem raw_source (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (parent : Option Entry) (key target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (read : RawCtxReceive.FrameDecoder) (sender : Std.U64) (raw : Pqxdh.Bytes)
    (before : RawCtxChainOwner.State Kernel Metadata) (state : State A) :
    Prod.map id project <$> (evaluated source key read
      (owner source writer prior parent target nonce next read sender (.inr raw) before)).run state =
      (fun result => (some result.1, result.2)) <$>
        ((RawCtxChainOwner.ownerImpl (originalCalls source writer prior parent key target nonce next) sender read (.inr raw)).run before).run
          (project state) := by
  rw [raw_cases, RawCtxSelectedReceiveCompiler.evaluated_map, StateT.run_map]
  simp only [RawCtxChainOwner.ownerImpl, originalCalls]
  rw [RawCtxSelectedReceiveCompiler.raw_source]
  simp only [Functor.map_map, Prod.map_def, id_eq]


/-- Only the source's actual nonempty send may reach a selected-nonce refusal. Raw deliveries and rejected empty sends do not stop the reduction. -/
noncomputable def Stops (prior : Prior) (parent : Option Entry) (target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (sender : Std.U64) (query : RawCtxMixedOwner.SourceSpec.Domain) (before : RawCtxChainOwner.State Kernel Metadata)
    (state : AdaptiveCtxDynamicKnownKeys.SourceState) : Prop :=
  match query with
  | .inr _ => False
  | .inl plaintext => plaintext.isEmpty = false ∧
      RawCtxSelectedSendCompiler.Stops prior parent target nonce next before.kernel
        ⟨plaintext, before.expectedSender, sender, before.associatedData⟩ state

noncomputable local instance (prior : Prior) (parent : Option Entry) (target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (sender : Std.U64) (query : RawCtxMixedOwner.SourceSpec.Domain) (before : RawCtxChainOwner.State Kernel Metadata)
    (state : AdaptiveCtxDynamicKnownKeys.SourceState) : Decidable (Stops prior parent target nonce next sender query before state) :=
  Classical.propDecidable _

set_option backward.isDefEq.respectTransparency false in
/-- Complete send-owner simulation retains the actual source empty-input gate and owner publication. The stopped branch is precisely the pending selected nonce refusal, not a source rejection. -/
theorem send_source (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (parent : Option Entry) (key target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (read : RawCtxReceive.FrameDecoder) (sender : Std.U64) (plaintext : Pqxdh.Bytes)
    (before : RawCtxChainOwner.State Kernel Metadata) (state : State A) :
    Prod.map id project <$> (evaluated source key read
      (owner source writer prior parent target nonce next read sender (.inl plaintext) before)).run state =
      if Stops prior parent target nonce next sender (.inl plaintext) before state.2 then pure (none, project state)
      else (fun result => (some result.1, result.2)) <$>
        ((RawCtxChainOwner.ownerImpl (originalCalls source writer prior parent key target nonce next) sender read (.inl plaintext)).run before).run
          (project state) := by
  rw [send_cases]
  simp only [RawCtxChainOwner.ownerImpl]
  unfold RawCtxChainOwner.sendOwner
  by_cases empty : plaintext.isEmpty = true
  · have clear : ¬ Stops prior parent target nonce next sender (.inl plaintext) before state.2 := by simp only [Stops, empty, Bool.true_eq_false, false_and, not_false_eq_true]
    rw [ite_eq_right (fun h => (clear h).elim)]
    simp only [empty, ite_true, StateT.run]
    rfl
  · have nonempty : plaintext.isEmpty = false := Bool.eq_false_iff.mpr empty
    have test : Stops prior parent target nonce next sender (.inl plaintext) before state.2 ↔
        RawCtxSelectedSendCompiler.Stops prior parent target nonce next before.kernel
          ⟨plaintext, before.expectedSender, sender, before.associatedData⟩ state.2 := by simp only [Stops, nonempty, true_and]
    simp only [nonempty, Bool.false_eq_true, ite_false, originalCalls,
      RawCtxSelectedMessageFamily.calls, StateT.run, bind_pure_comp]
    rw [RawCtxSelectedReceiveCompiler.evaluated_map]
    have mapped := congrArg (fun work => (fun result =>
      (Option.map (fun value => (value.2, { before with kernel := value.1 })) result.1, result.2)) <$> work)
      (RawCtxSelectedSendCompiler.send_source source writer prior parent key target nonce next read before.kernel
        ⟨plaintext, before.expectedSender, sender, before.associatedData⟩ state)
    simp only [state_map_apply, Functor.map_map, Prod.map_def, id_eq, apply_ite, map_pure,
      Option.map_none, Option.map_some] at mapped ⊢
    split
    · have stopped := test.mp ‹Stops prior parent target nonce next sender (.inl plaintext) before state.2›
      simp only [stopped, ite_true, StateT.run] at mapped
      convert mapped using 1
    · have running := fun h => ‹¬ Stops prior parent target nonce next sender (.inl plaintext) before state.2› (test.mpr h)
      simp only [ite_eq_right (fun h => (running h).elim), StateT.run] at mapped
      convert mapped using 1

set_option backward.isDefEq.respectTransparency false in
/-- The same original mixed API query is compiled for every raw/send schedule. All actual owner state and original source state are retained until the explicit selected-nonce stop. -/
theorem owner_source (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (parent : Option Entry) (key target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (read : RawCtxReceive.FrameDecoder) (sender : Std.U64) (query : RawCtxMixedOwner.SourceSpec.Domain)
    (before : RawCtxChainOwner.State Kernel Metadata) (state : State A) :
    Prod.map id project <$> (evaluated source key read
      (owner source writer prior parent target nonce next read sender query before)).run state =
      if Stops prior parent target nonce next sender query before state.2 then pure (none, project state)
      else (fun result => (some result.1, result.2)) <$>
        ((RawCtxChainOwner.ownerImpl (originalCalls source writer prior parent key target nonce next) sender read query).run before).run
          (project state) := by
  cases query with
  | inl plaintext => exact send_source source writer prior parent key target nonce next read sender plaintext before state
  | inr raw =>
    have clear : ¬ Stops prior parent target nonce next sender (.inr raw) before state.2 := by simp only [Stops, not_false_eq_true]
    rw [ite_eq_right (fun h => (clear h).elim)]
    exact raw_source source writer prior parent key target nonce next read sender raw before state

/-- Every mixed source owner request has at most one dynamic component call; parser rejection and empty sends remain inside the counted API attempt. -/
theorem owner_queries (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (parent : Option Entry) (target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (read : RawCtxReceive.FrameDecoder) (sender : Std.U64) (query : RawCtxMixedOwner.SourceSpec.Domain)
    (before : RawCtxChainOwner.State Kernel Metadata) :
    (owner source writer prior parent target nonce next read sender query before).IsTotalQueryBound 1 := by
  cases query with
  | inr raw =>
    rw [raw_cases]
    simpa only [IsTotalQueryBound, isQueryBound_map_iff] using
      RawCtxSelectedReceiveCompiler.raw_queries prior parent target nonce next read raw before
  | inl plaintext =>
    rw [send_cases]
    split
    · trivial
    · simp only [IsTotalQueryBound, isQueryBound_map_iff]
      exact RawCtxSelectedSendCompiler.send_queries source writer prior parent target nonce next before.kernel _


/-- The unchanged material owner is the complete extracted native owner after private slot interpretation; both concrete call equations are discharged by the source driver. -/
theorem original_native (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (parent : Option Entry) (key target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (read : RawCtxReceive.FrameDecoder) (sender : Std.U64) (query : RawCtxMixedOwner.SourceSpec.Domain)
    (before : RawCtxChainOwner.State Kernel Metadata) :
    simulateQ (RawCtxFunctionalFamily.native (A := A) source writer
      (privateTable prior parent target (RawCtxSelectedMessageKdf.response key nonce next)))
      ((RawCtxMixedOwner.ownerImpl sender read query).run
        (RawCtxChainOwner.nativeState (RawCtxSelectedMessageReveals.nativeKernel key) before)) =
      Prod.map id (RawCtxChainOwner.nativeState (RawCtxSelectedMessageReveals.nativeKernel key)) <$>
        (RawCtxChainOwner.ownerImpl (originalCalls source writer prior parent key target nonce next) sender read query).run before := by
  apply RawCtxChainOwner.owner_native
  · exact RawCtxSelectedMessageDriver.receive_source source writer prior parent key target nonce next
  · exact RawCtxSelectedMessageDriver.send_source source writer prior parent key target nonce next

/-- Every original extracted mixed-owner API request has the same complete native state and optional reply through the key-free CTX compiler, except at the explicitly retained selected nonce-stop branch. -/
theorem native_owner (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (parent : Option Entry) (key target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (read : RawCtxReceive.FrameDecoder) (sender : Std.U64) (query : RawCtxMixedOwner.SourceSpec.Domain)
    (before : RawCtxChainOwner.State Kernel Metadata) (state : State A) :
    (fun result => (Option.map (Prod.map id (RawCtxChainOwner.nativeState (RawCtxSelectedMessageReveals.nativeKernel key))) result.1,
        project result.2)) <$>
      (evaluated source key read (owner source writer prior parent target nonce next read sender query before)).run state =
      if Stops prior parent target nonce next sender query before state.2 then pure (none, project state)
      else (fun result => (some result.1, result.2)) <$>
        (simulateQ (RawCtxFunctionalFamily.native source writer
          (privateTable prior parent target (RawCtxSelectedMessageKdf.response key nonce next)))
          ((RawCtxMixedOwner.ownerImpl sender read query).run
            (RawCtxChainOwner.nativeState (RawCtxSelectedMessageReveals.nativeKernel key) before))).run (project state) := by
  rw [original_native]
  have mapped := congrArg (fun work => (fun result =>
    (Option.map (Prod.map id (RawCtxChainOwner.nativeState (RawCtxSelectedMessageReveals.nativeKernel key))) result.1, result.2)) <$> work)
      (owner_source source writer prior parent key target nonce next read sender query before state)
  simp only [StateT.run_map, Functor.map_map, Prod.map_def, id_eq, apply_ite, map_pure, Option.map_none, Option.map_some] at mapped ⊢
  convert mapped using 1

end BeaconcryptCore.Computational.RawCtxSelectedOwnerCompiler

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedOwnerCompiler.raw_cases' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedOwnerCompiler.raw_cases

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedOwnerCompiler.send_cases' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedOwnerCompiler.send_cases

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedOwnerCompiler.raw_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedOwnerCompiler.raw_source

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedOwnerCompiler.send_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedOwnerCompiler.send_source

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedOwnerCompiler.owner_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedOwnerCompiler.owner_source

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedOwnerCompiler.owner_queries' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedOwnerCompiler.owner_queries

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedOwnerCompiler.original_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedOwnerCompiler.original_native

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedOwnerCompiler.native_owner' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedOwnerCompiler.native_owner
