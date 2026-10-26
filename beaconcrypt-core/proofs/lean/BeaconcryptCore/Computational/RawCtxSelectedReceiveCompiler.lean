import BeaconcryptCore.Computational.RawCtxSelectedReceiveScope
import BeaconcryptCore.Computational.RawCtxSelectedMessageFamily
import BeaconcryptCore.Computational.RawCtxSelectedOpenConsumer

/-!
The selected-message receive callback is compiled to the ordinary dynamic CTX interface. Derivations retain the prior table and exact selected address; openings return challenger-produced optional plaintext. Source equality retains complete ratchet output and shared-cache effects, and requires only the raw context facts established by the actual owner prelude.
-/
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.refined ratchet.concrete
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RawCtxSelectedReceiveCompiler
open PqxdhSecretInputKdf PqxdhFullSecretInputKdf PqxdhJointKdfGame
open RawCtxSelectedMessageKey RawCtxSelectedMessageKdf RawCtxSelectedMessageDriver
open RawCtxSelectedParentTable RawCtxSelectedParentEntry
variable {A : Type}

/-- The retained private table cannot change a source opening: the original native hash/open interpreter is used on its actual pending input. -/
theorem opening_native (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (pending : ReceiveOpen RawCtxWholeOwner.OpenContext) :
    RawCtxFunctionalFamily.opening (A := A) source writer prior pending =
      simulateQ (RawCtxSharedPrimitive.nativeImpl source.crypto (RawCtxSourceHkdf.kdfImpl source))
        (RawCtxSourceOpen.ownerAdapter (.inr pending)) := by
  simp only [RawCtxFunctionalFamily.opening, RawCtxFunctionalFamily.native, RawCtxFunctionalFamily.backend, QueryImpl.compose, RawCtxSourceOpen.ownerAdapter, ← QueryImpl.simulateQ_compose]
  simp only [RawCtxWholeOwner.adapter]
  split
  · rfl
  · simp only [simulateQ_bind, simulateQ_spec_query, simulateQ_pure]
    congr 1
    simp only [QueryImpl.compose, RawCtxMixedOwner.receiveAdapter, RawCtxSourceOpen.nativeAdapter]
    simp only [← QueryImpl.simulateQ_compose]
    congr 1
    funext query
    cases query <;> simp [QueryImpl.compose, RawCtxMixedOwner.receiveLift, RawCtxSourceOpen.openLift, RawCtxServerServices.nativeLift, RawCtxSelectiveKdfFamily.compiler, RawCtxRetainedTable.viewImpl, RawCtxProtocolBackend.backend, OracleSpec.query]
    all_goals funext state
    all_goals first | rfl | simp [RawCtxServerServices.backendImpl, RawCtxMixedShared.sharedImpl, RawCtxMixedShared.sharedAdapter, RawCtxSharedPrimitive.nativeImpl, QueryImpl.compose, OracleSpec.query]
    rfl

noncomputable def service (prior : Prior) (read : RawCtxReceive.FrameDecoder) (expected : Std.U64) :
    QueryImpl (ReceiveServices RawCtxWholeOwner.OpenContext RawCtxWholeOwner.Decrypted)
      (OracleComp AdaptiveCtxDynamicKnownKeys.Spec)
  | .inl address => pure (prior address)
  | .inr pending => RawCtxSelectedOpenConsumer.service 0 read expected pending

noncomputable def compiler (prior : Prior) (parent : Option Entry) (target : RootOutput)
    (nonce : NonceOutput) (next : RootOutput) (read : RawCtxReceive.FrameDecoder) (expected : Std.U64) :=
  service prior read expected ∘ₛ receiveCompiler parent target nonce next (Context := RawCtxWholeOwner.OpenContext) (Plaintext := RawCtxWholeOwner.Decrypted)

abbrev State (A : Type) := A × AdaptiveCtxDynamicKnownKeys.SourceState

def project (state : State A) : RawCtxSharedPrimitive.SharedState A := (state.1, state.2.cache)

noncomputable def evaluated (source : FixedHkdfSha512NoSaltSource) (key : RootOutput)
    (read : RawCtxReceive.FrameDecoder) {Result : Type}
    (work : OracleComp AdaptiveCtxDynamicKnownKeys.Spec Result) : StateT (State A) ProbComp Result :=
  fun state => (fun result => (result.1, (state.1, result.2))) <$>
    (simulateQ (AdaptiveCtxDynamicKnownKeys.sourceImpl true (RawCtxUniversalDecoder.decoder read) source.crypto key) work).run state.2

/-- The original opening is obtained by erasing only the added CTX bookkeeping, preserving its real optional plaintext and complete shared cache before source finish. -/
theorem opening_project (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (parent : Option Entry) (key target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (read : RawCtxReceive.FrameDecoder) (expected : Std.U64)
    (pending : RawCtxInterpretedOpening.Opening RatchetChain RatchetChain Slot RawCtxWholeOwner.OpenContext)
    (state : State A)
    (nonempty : pending.context.raw.isEmpty = false) (decoded : read pending.context.raw = some pending.context.frame)
    (valid : RawCtxReceive.ValidFrame expected pending.context.associatedData pending.context.frame)
    (prepared : RawCtxInterpretedOpening.sequence pending = ok pending.context.frame.sequence) :
    (receiveServices source writer prior parent key target nonce next (.inr pending)).run (project state) =
      Prod.map id project <$> (evaluated source key read (service prior read expected (.inr pending))).run state := by
  obtain ⟨slices, parsed⟩ : ∃ slices, RawCtxFrameDecoding.fromPayload pending.context.frame.payload = some slices := by
    simp only [RawCtxFrameDecoding.fromPayload, ite_eq_right (show ¬ pending.context.frame.payload.length ≤ 80 by have := valid.2.1; omega)]
    exact ⟨_, rfl⟩
  simp only [receiveServices, opening_native, project, evaluated, service, StateT.run, Functor.map_map, Prod.map_def, id_eq]
  exact RawCtxSelectedOpenConsumer.service_source 0 read expected key source.crypto (RawCtxSourceHkdf.kdfImpl source)
    pending state.1 state.2 nonempty decoded valid prepared slices parsed

/-- Prior-table replies are identical in the source and CTX compiler and add no primitive effect; every lookup remains explicit in the driver. -/
theorem derive_project (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (parent : Option Entry) (key target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (read : RawCtxReceive.FrameDecoder) (expected : Std.U64) (request : SymmetricRatchetKdfRequest) (state : State A) :
    ((receiveServices source writer prior parent key target nonce next ∘ₛ receiveCompiler parent target nonce next) (.inl request)).run (project state) =
      Prod.map id project <$> (evaluated source key read (compiler prior parent target nonce next read expected (.inl request))).run state := by
  simp only [compiler, QueryImpl.compose, receiveCompiler, ← QueryImpl.simulateQ_compose]
  change (simulateQ (fun address => (pure (prior address) : StateT (RawCtxSharedPrimitive.SharedState A) ProbComp FullOutput)) (derive parent target nonce next request)).run (project state) =
    Prod.map id project <$> (evaluated source key read (simulateQ (fun address => (pure (prior address) : OracleComp AdaptiveCtxDynamicKnownKeys.Spec FullOutput)) (derive parent target nonce next request))).run state
  rw [derive_evaluated, derive_evaluated]
  rfl

/-- The complete opaque receive driver, including cached/future paths and all failures, uses the exact challenger optional plaintext and original native finish; no accepted-opening premise is used. -/
theorem receive_project (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (parent : Option Entry) (key target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (read : RawCtxReceive.FrameDecoder) (expected : Std.U64) (kernel : RawCtxSelectedMessageReveals.Kernel)
    (context : RawCtxWholeOwner.OpenContext) (state : State A)
    (nonempty : context.raw.isEmpty = false) (decoded : read context.raw = some context.frame)
    (valid : RawCtxReceive.ValidFrame expected context.associatedData context.frame) :
    (simulateQ (receiveServices source writer prior parent key target nonce next)
      (RawCtxSelectedMessageDriver.receive parent target nonce next kernel context.frame.sequence context)).run (project state) =
      Prod.map id project <$> (simulateQ (fun query => evaluated source key read
        (compiler prior parent target nonce next read expected query))
        (RawCtxInterpretedReceive.receive kernel context.frame.sequence context)).run state := by
  simp only [RawCtxSelectedMessageDriver.receive, ← QueryImpl.simulateQ_compose, RawCtxInterpretedReceive.receive]
  apply RawCtxSelectedReceiveScope.program_projection
  · exact derive_project source writer prior parent key target nonce next read expected
  · intro pending before sequence contextEq
    simpa only [QueryImpl.compose, receiveCompiler, simulateQ_spec_query, compiler, contextEq] using
      opening_project source writer prior parent key target nonce next read expected pending before
        (contextEq ▸ nonempty) (contextEq ▸ decoded) (contextEq ▸ valid) (by simpa only [contextEq] using sequence)
  · exact RawCtxSelectedReceiveScope.begin_scope (interpret key) kernel context.frame.sequence context

/-- Interpreting the saved key-free program retains every component reply and its full CTX state throughout the continuation. -/
theorem evaluated_program {ι Result : Type} {spec : OracleSpec ι}
    (source : FixedHkdfSha512NoSaltSource) (key : RootOutput) (read : RawCtxReceive.FrameDecoder)
    (lower : QueryImpl spec (OracleComp AdaptiveCtxDynamicKnownKeys.Spec)) (client : OracleComp spec Result) :
    simulateQ (fun query => evaluated (A := A) source key read (lower query)) client =
      evaluated source key read (simulateQ lower client) := by
  funext state
  induction client using OracleComp.inductionOn generalizing state with
  | pure value => rfl
  | query_bind query continuation ih =>
    change ((simulateQ (fun query => evaluated (A := A) source key read (lower query))
      ((spec.query query) >>= continuation)).run state) = _
    rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
    simp only [evaluated, simulateQ_bind, simulateQ_spec_query]
    change ((fun result => (result.1, (state.1, result.2))) <$>
      (simulateQ (AdaptiveCtxDynamicKnownKeys.sourceImpl true (RawCtxUniversalDecoder.decoder read) source.crypto key) (lower query)).run state.2) >>= (fun result =>
        (simulateQ (fun query => evaluated source key read (lower query)) (continuation result.1)).run result.2) =
      (fun result => (result.1, (state.1, result.2))) <$>
        ((simulateQ (AdaptiveCtxDynamicKnownKeys.sourceImpl true (RawCtxUniversalDecoder.decoder read) source.crypto key) (lower query)).run state.2 >>= fun result =>
          (simulateQ (AdaptiveCtxDynamicKnownKeys.sourceImpl true (RawCtxUniversalDecoder.decoder read) source.crypto key) (simulateQ lower (continuation result.1))).run result.2)
    simp only [bind_map_left, map_bind]
    exact bind_congr fun result => ih result.1 (state.1, result.2)

noncomputable def receive (prior : Prior) (parent : Option Entry) (target : RootOutput)
    (nonce : NonceOutput) (next : RootOutput) (read : RawCtxReceive.FrameDecoder) (expected : Std.U64)
    (kernel : RawCtxSelectedMessageReveals.Kernel) (sequence : Std.U64) (context : RawCtxWholeOwner.OpenContext) :=
  simulateQ (service prior read expected) (RawCtxSelectedMessageDriver.receive parent target nonce next kernel sequence context)

/-- One executable compiled receive has no selected-message-key input; its native interpretation preserves the complete output and actual shared cache. -/
theorem receive_source (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (parent : Option Entry) (key target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (read : RawCtxReceive.FrameDecoder) (expected : Std.U64) (kernel : RawCtxSelectedMessageReveals.Kernel)
    (context : RawCtxWholeOwner.OpenContext) (state : State A)
    (nonempty : context.raw.isEmpty = false) (decoded : read context.raw = some context.frame)
    (valid : RawCtxReceive.ValidFrame expected context.associatedData context.frame) :
    (simulateQ (receiveServices source writer prior parent key target nonce next)
      (RawCtxSelectedMessageDriver.receive parent target nonce next kernel context.frame.sequence context)).run (project state) =
      Prod.map id project <$> (evaluated source key read
        (receive prior parent target nonce next read expected kernel context.frame.sequence context)).run state := by
  rw [receive_project source writer prior parent key target nonce next read expected kernel context state nonempty decoded valid,
    evaluated_program]
  simp only [receive, RawCtxSelectedMessageDriver.receive, ← QueryImpl.simulateQ_compose, compiler]

/-- Mapping a public or private source result adds no component call and retains complete CTX state. -/
theorem evaluated_map {X Y : Type} (source : FixedHkdfSha512NoSaltSource) (key : RootOutput)
    (read : RawCtxReceive.FrameDecoder) (f : X → Y) (work : OracleComp AdaptiveCtxDynamicKnownKeys.Spec X) :
    evaluated (A := A) source key read (f <$> work) = f <$> evaluated source key read work := by
  funext state
  change (fun result => (result.1, (state.1, result.2))) <$>
    (simulateQ (AdaptiveCtxDynamicKnownKeys.sourceImpl true (RawCtxUniversalDecoder.decoder read) source.crypto key) (f <$> work)).run state.2 = _
  change _ = (f <$> evaluated source key read work).run state
  simp only [simulateQ_map, StateT.run_map, Functor.map_map]
  change _ = (fun p => (f p.1, p.2)) <$> ((fun result => (result.1, (state.1, result.2))) <$>
    (simulateQ (AdaptiveCtxDynamicKnownKeys.sourceImpl true (RawCtxUniversalDecoder.decoder read) source.crypto key) work).run state.2)
  simp only [Functor.map_map]

noncomputable def calls (prior : Prior) (parent : Option Entry) (target : RootOutput)
    (nonce : NonceOutput) (next : RootOutput) (read : RawCtxReceive.FrameDecoder) :
    RawCtxChainOwner.Calls RawCtxSelectedMessageReveals.Kernel (OracleComp AdaptiveCtxDynamicKnownKeys.Spec) where
  receive kernel sequence context := receive prior parent target nonce next read context.frame.sender kernel sequence context
  -- This receive-only adapter has no reachable send branch.
  send kernel _ := pure (kernel, none)

noncomputable def raw {Metadata : Type} (prior : Prior) (parent : Option Entry) (target : RootOutput)
    (nonce : NonceOutput) (next : RootOutput) (read : RawCtxReceive.FrameDecoder) (bytes : Pqxdh.Bytes)
    (owner : RawCtxChainOwner.State RawCtxSelectedMessageReveals.Kernel Metadata) :=
  (RawCtxChainOwner.rawReceive (calls prior parent target nonce next read) read bytes).run owner

/-- Every arbitrary raw delivery, including parser and validation rejection, compiles to the same optional plaintext and complete owner/cache result. Reached-frame side conditions are derived from the actual source prelude. -/
theorem raw_source {Metadata : Type} (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (parent : Option Entry) (key target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (read : RawCtxReceive.FrameDecoder) (bytes : Pqxdh.Bytes)
    (owner : RawCtxChainOwner.State RawCtxSelectedMessageReveals.Kernel Metadata) (state : State A) :
    ((RawCtxChainOwner.rawReceive
      (RawCtxSelectedMessageFamily.calls (receiveServices source writer prior parent key target nonce next)
        (sendServices source writer prior parent key target nonce next) parent target nonce next)
      read bytes).run owner).run (project state) =
      Prod.map id project <$> (evaluated source key read (raw prior parent target nonce next read bytes owner)).run state := by
  unfold raw RawCtxChainOwner.rawReceive
  simp only [StateT.run]
  by_cases empty : bytes.isEmpty = true
  · simp only [empty, ite_true, evaluated, simulateQ_pure, StateT.run_pure, map_pure, project]
    rfl
  · simp only [empty, Bool.false_eq_true, ite_false]
    cases decoded : read bytes with
    | none =>
      simp only [evaluated, simulateQ_pure, StateT.run_pure, map_pure, project]
      rfl
    | some frame =>
      by_cases valid : RawCtxReceive.ValidFrame owner.expectedSender owner.associatedData frame
      · simp only [valid, ite_true, bind_pure_comp, RawCtxSelectedMessageFamily.calls, calls]
        rw [evaluated_map]
        change (RawCtxChainOwner.publish owner <$> simulateQ (receiveServices source writer prior parent key target nonce next)
          (RawCtxSelectedMessageDriver.receive parent target nonce next owner.kernel frame.sequence ⟨bytes, frame, owner.associatedData⟩)).run (project state) = _
        rw [StateT.run_map, receive_source source writer prior parent key target nonce next read frame.sender owner.kernel
          ⟨bytes, frame, owner.associatedData⟩ state (by simpa using empty) decoded ⟨rfl, valid.2⟩]
        change _ = Prod.map id project <$> (RawCtxChainOwner.publish owner <$>
          evaluated source key read (receive prior parent target nonce next read frame.sender owner.kernel frame.sequence
            ⟨bytes, frame, owner.associatedData⟩)).run state
        rw [StateT.run_map]
        simp only [Functor.map_map]
        rfl
      · simp only [valid, ite_false, evaluated, simulateQ_pure, StateT.run_pure, map_pure, project]
        rfl

/-- The actual extracted native raw receive equals the key-free CTX program after interpreting only the private material slots and erasing added component bookkeeping; every owner and ambient source field is retained. -/
theorem native_raw {Metadata : Type} (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (parent : Option Entry) (key target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (read : RawCtxReceive.FrameDecoder) (bytes : Pqxdh.Bytes)
    (owner : RawCtxChainOwner.State RawCtxSelectedMessageReveals.Kernel Metadata) (state : State A) :
    (simulateQ (RawCtxFunctionalFamily.native source writer
        (privateTable prior parent target (response key nonce next)) ∘ₛ RawCtxMixedOwner.receiveAdapter)
      ((RawCtxWholeOwner.rawReceive read bytes).run
        (RawCtxChainOwner.nativeState (RawCtxSelectedMessageReveals.nativeKernel key) owner))).run (project state) =
      (fun result => ((result.1.1,
        RawCtxChainOwner.nativeState (RawCtxSelectedMessageReveals.nativeKernel key) result.1.2), project result.2)) <$>
        (evaluated source key read (raw prior parent target nonce next read bytes owner)).run state := by
  have original := congrArg (fun work => work.run (project state))
    (RawCtxChainOwner.rawReceive_native (RawCtxSelectedMessageReveals.nativeKernel key)
      (RawCtxSelectedMessageFamily.calls (receiveServices source writer prior parent key target nonce next)
        (sendServices source writer prior parent key target nonce next) parent target nonce next)
      (RawCtxFunctionalFamily.native source writer (privateTable prior parent target (response key nonce next)) ∘ₛ RawCtxMixedOwner.receiveAdapter)
      (RawCtxSelectedMessageDriver.receive_source source writer prior parent key target nonce next) read bytes owner)
  rw [StateT.run_map, raw_source] at original
  simpa only [Functor.map_map, Prod.map_def, id_eq] using original

/-- Private-table lookup adds no CTX query, while a reached opening has at most one dynamic selected/known-key call, including all optional failures. -/
theorem service_queries (prior : Prior) (read : RawCtxReceive.FrameDecoder) (expected : Std.U64)
    (query : (ReceiveServices RawCtxWholeOwner.OpenContext RawCtxWholeOwner.Decrypted).Domain) :
    (service prior read expected query).IsTotalQueryBound (if query.isLeft = false then 1 else 0) := by
  cases query with
  | inl address => trivial
  | inr pending => exact RawCtxSelectedOpenConsumer.service_total 0 read expected pending

/-- The complete compiled receive makes at most one CTX call under every typed reply. Its separate source private-lookup allowance remains 51. -/
theorem receive_queries (prior : Prior) (parent : Option Entry) (target : RootOutput)
    (nonce : NonceOutput) (next : RootOutput) (read : RawCtxReceive.FrameDecoder) (expected : Std.U64)
    (kernel : RawCtxSelectedMessageReveals.Kernel) (sequence : Std.U64) (context : RawCtxWholeOwner.OpenContext) :
    (receive prior parent target nonce next read expected kernel sequence context).IsTotalQueryBound 1 := by
  have bounded := RawCtxSourceOpen.simulate_bound (service prior read expected) (fun query => query.isLeft = false) (fun _ => True)
    (RawCtxSelectedMessageDriver.receive parent target nonce next kernel sequence context) 1
    (RawCtxSelectedMessageDriverBounds.receive_open parent target nonce next kernel sequence context)
    (fun query => by simpa only [IsTotalQueryBound, IsQueryBoundP, not_true_eq_false, false_or, ite_true] using service_queries prior read expected query)
  simpa only [receive, IsTotalQueryBound, IsQueryBoundP, not_true_eq_false, false_or, ite_true] using bounded

/-- Every arbitrary raw attempt is counted, while parser rejection can only reduce its one-call CTX allowance. -/
theorem raw_queries {Metadata : Type} (prior : Prior) (parent : Option Entry) (target : RootOutput)
    (nonce : NonceOutput) (next : RootOutput) (read : RawCtxReceive.FrameDecoder) (bytes : Pqxdh.Bytes)
    (owner : RawCtxChainOwner.State RawCtxSelectedMessageReveals.Kernel Metadata) :
    (raw prior parent target nonce next read bytes owner).IsTotalQueryBound 1 := by
  unfold raw RawCtxChainOwner.rawReceive
  simp only [StateT.run]
  split
  · trivial
  · split
    · trivial
    · split
      · simp only [calls, bind_pure_comp, IsTotalQueryBound, isQueryBound_map_iff]
        exact receive_queries prior parent target nonce next read _ owner.kernel _ _
      · trivial

end BeaconcryptCore.Computational.RawCtxSelectedReceiveCompiler

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedReceiveCompiler.opening_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedReceiveCompiler.opening_native

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedReceiveCompiler.opening_project' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedReceiveCompiler.opening_project

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedReceiveCompiler.derive_project' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedReceiveCompiler.derive_project

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedReceiveCompiler.receive_project' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedReceiveCompiler.receive_project

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedReceiveCompiler.evaluated_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedReceiveCompiler.evaluated_program

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedReceiveCompiler.receive_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedReceiveCompiler.receive_source

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedReceiveCompiler.evaluated_map' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedReceiveCompiler.evaluated_map

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedReceiveCompiler.raw_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedReceiveCompiler.raw_source

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedReceiveCompiler.native_raw' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedReceiveCompiler.native_raw

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedReceiveCompiler.service_queries' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedReceiveCompiler.service_queries

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedReceiveCompiler.receive_queries' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedReceiveCompiler.receive_queries

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedReceiveCompiler.raw_queries' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedReceiveCompiler.raw_queries
