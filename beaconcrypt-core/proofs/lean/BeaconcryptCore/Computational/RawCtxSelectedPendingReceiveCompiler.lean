import BeaconcryptCore.Computational.RawCtxSelectedReceiveCompiler
import BeaconcryptCore.Computational.RawCtxForwardOwnerScope

/-!
A receive saved at a private derivation resumes its existing effect, rollback entry, skipped slots and raw context. The compiler executes only the remaining derivations and optional opening; it does not repeat admission or already executed prefix callbacks. The executable compiler has no selected-message-key argument; that key is supplied to its mathematical source and CTX interpretations. Global source nonexposure and arbitrary input-state aliases are separate obligations.
-/
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.refined ratchet.concrete
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RawCtxSelectedPendingReceiveCompiler
open PqxdhSecretInputKdf PqxdhFullSecretInputKdf PqxdhJointKdfGame
open RawCtxSelectedMessageKey RawCtxSelectedMessageKdf RawCtxSelectedMessageDriver
open RawCtxSelectedParentTable RawCtxSelectedParentEntry
open RawCtxSelectedReceiveCompiler (State project evaluated)
variable {A : Type}

noncomputable def effect (prior : Prior) (parent : Option Entry) (target : RootOutput)
    (nonce : NonceOutput) (next : RootOutput) (read : RawCtxReceive.FrameDecoder) (expected : Std.U64)
    (pending : RawCtxInterpretedReceive.Effect Slot RawCtxWholeOwner.OpenContext) :=
  simulateQ (RawCtxSelectedReceiveCompiler.compiler prior parent target nonce next read expected)
    (RawCtxInterpretedReceive.program (Plaintext := RawCtxWholeOwner.Decrypted) pending)

/-- The complete remaining receive effect preserves the actual optional plaintext, every cached/staged slot, rollback entry and source cache. Reached-opening facts are restricted to the unchanged admitted raw context. -/
theorem effect_source (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (parent : Option Entry) (key target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (read : RawCtxReceive.FrameDecoder) (expected : Std.U64)
    (context : RawCtxWholeOwner.OpenContext)
    (pending : RawCtxInterpretedReceive.Effect Slot RawCtxWholeOwner.OpenContext) (state : State A)
    (nonempty : context.raw.isEmpty = false) (decoded : read context.raw = some context.frame)
    (valid : RawCtxReceive.ValidFrame expected context.associatedData context.frame)
    (inScope : RawCtxSelectedReceiveScope.Scope context.frame.sequence context pending) :
    (simulateQ (receiveServices source writer prior parent key target nonce next ∘ₛ receiveCompiler parent target nonce next)
      (RawCtxInterpretedReceive.program (Plaintext := RawCtxWholeOwner.Decrypted) pending)).run (project state) =
      Prod.map id project <$> (evaluated source key read (effect prior parent target nonce next read expected pending)).run state := by
  unfold effect
  rw [← RawCtxSelectedReceiveCompiler.evaluated_program]
  apply RawCtxSelectedReceiveScope.program_projection
  · exact RawCtxSelectedReceiveCompiler.derive_project source writer prior parent key target nonce next read expected
  · intro opening before sequence contextEq
    simpa only [QueryImpl.compose, receiveCompiler, simulateQ_spec_query, RawCtxSelectedReceiveCompiler.compiler, contextEq] using
      RawCtxSelectedReceiveCompiler.opening_project source writer prior parent key target nonce next read expected opening before
        (contextEq ▸ nonempty) (contextEq ▸ decoded) (contextEq ▸ valid) (by simpa only [contextEq] using sequence)
  · exact inScope

private theorem program_interpreted {Material Context Plaintext : Type} {m : Type → Type*}
    [Monad m] [LawfulMonad m] (value : Material → RatchetMaterial)
    (labels : QueryImpl (RawCtxInterpretedReceive.ReceiveSpec Material Context Plaintext) m)
    (native : QueryImpl (RawCtxOwnerOracle.ReceiveSpec Context Plaintext) m)
    (kdf : ∀ request, RawCtxInterpretedReceive.decodeResponse <$> native (.inl request) =
      (fun reply => (reply.1, value reply.2)) <$> labels (.inl request))
    (opening : ∀ pending, native (.inr (RawCtxInterpretedOpening.toNative
      (RawCtxInterpretedOpening.mapOpening value pending))) = labels (.inr pending))
    (pending : RawCtxInterpretedReceive.Effect Material Context) :
    simulateQ native (RawCtxOwnerOracle.program
      (RawCtxInterpretedReceive.nativeEffect (RawCtxInterpretedReceive.mapEffect value pending))) =
      (fun result => (ConcreteRatchetKernel.mk (RawCtxMaterialInterpretation.mapRefined value result.1), result.2)) <$>
        simulateQ labels (RawCtxInterpretedReceive.program pending) := by
  rw [RawCtxInterpretedReceive.program_native, simulateQ_map, ← QueryImpl.simulateQ_compose]
  have mapped := RawCtxInterpretedReceive.program_map value labels
    (native ∘ₛ RawCtxInterpretedReceive.nativeAdapter) ?_ ?_ pending
  · rw [mapped, Functor.map_map]
  · simpa only [QueryImpl.compose, RawCtxInterpretedReceive.nativeAdapter, simulateQ_map,
      simulateQ_spec_query] using kdf
  · simpa only [QueryImpl.compose, RawCtxInterpretedReceive.nativeAdapter,
      simulateQ_spec_query] using opening

/-- The remaining effect is the actual native program with the selected private response and retained predecessor priority. Every native callback is instantiated here; no callback simulation premise is required. -/
theorem native_effect (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (parent : Option Entry) (key target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (pending : RawCtxInterpretedReceive.Effect Slot RawCtxWholeOwner.OpenContext) :
    simulateQ ((RawCtxFunctionalFamily.native (A := A) source writer
        (privateTable prior parent target (response key nonce next)) ∘ₛ RawCtxMixedOwner.receiveAdapter) ∘ₛ RawCtxWholeOwner.adapter)
      (RawCtxOwnerOracle.program (RawCtxInterpretedReceive.nativeEffect
        (RawCtxInterpretedReceive.mapEffect (interpret key) pending))) =
      (fun result => (RawCtxSelectedMessageReveals.nativeKernel key result.1, result.2)) <$>
        simulateQ (receiveServices source writer prior parent key target nonce next ∘ₛ receiveCompiler parent target nonce next)
          (RawCtxInterpretedReceive.program pending) := by
  rw [← RawCtxFunctionalFamily.receive_handler]
  apply program_interpreted (interpret key)
  · intro request
    simp only [RawCtxMaterialPositions.bareReceiveImpl]
    exact (receive_derive (A := A) source writer prior parent key target nonce next request).symm
  · exact fun opening => (simulateQ_spec_query
      (receiveServices (A := A) source writer prior parent key target nonce next) (.inr opening)).symm

/-- The actual remaining native receive and the executable dynamic CTX effect preserve the complete result and source state. The key appears only in this mathematical interpretation. -/
theorem native_effect_source (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (parent : Option Entry) (key target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (read : RawCtxReceive.FrameDecoder) (expected : Std.U64) (context : RawCtxWholeOwner.OpenContext)
    (pending : RawCtxInterpretedReceive.Effect Slot RawCtxWholeOwner.OpenContext) (state : State A)
    (nonempty : context.raw.isEmpty = false) (decoded : read context.raw = some context.frame)
    (valid : RawCtxReceive.ValidFrame expected context.associatedData context.frame)
    (inScope : RawCtxSelectedReceiveScope.Scope context.frame.sequence context pending) :
    (simulateQ ((RawCtxFunctionalFamily.native source writer
        (privateTable prior parent target (response key nonce next)) ∘ₛ RawCtxMixedOwner.receiveAdapter) ∘ₛ RawCtxWholeOwner.adapter)
      (RawCtxOwnerOracle.program (RawCtxInterpretedReceive.nativeEffect
        (RawCtxInterpretedReceive.mapEffect (interpret key) pending)))).run (project state) =
      (fun result => ((RawCtxSelectedMessageReveals.nativeKernel key result.1.1, result.1.2), project result.2)) <$>
        (evaluated source key read (effect prior parent target nonce next read expected pending)).run state := by
  rw [native_effect, StateT.run_map,
    effect_source source writer prior parent key target nonce next read expected context pending state nonempty decoded valid inScope]
  simp only [Functor.map_map, Prod.map_def, id_eq]

/-- A saved predecessor response is retained as known material. The later private derivation, rather than this resume step, selects any hidden child message material. -/
noncomputable def resume (prior : Prior) (parent : Option Entry) (target : RootOutput)
    (nonce : NonceOutput) (next : RootOutput) (read : RawCtxReceive.FrameDecoder) (expected : Std.U64)
    (pending : RawCtxInterpretedReceive.Kdf RatchetMaterial RawCtxWholeOwner.OpenContext)
    (reply : RatchetChain × RatchetMaterial) :=
  effect prior parent target nonce next read expected
    (RawCtxInterpretedReceive.normalResume (RawCtxInterpretedReceive.mapKdf Slot.known pending)
      (reply.1, Slot.known reply.2))

/-- Keeping the entire saved state and supplied predecessor response known reconstructs the actual source continuation for every selected key, including coincidental byte aliases. -/
theorem known_resume (key : RootOutput)
    (pending : RawCtxInterpretedReceive.Kdf RatchetMaterial RawCtxWholeOwner.OpenContext)
    (reply : RatchetChain × RatchetMaterial) :
    RawCtxInterpretedReceive.mapEffect (interpret key)
      (RawCtxInterpretedReceive.normalResume (RawCtxInterpretedReceive.mapKdf Slot.known pending)
        (reply.1, Slot.known reply.2)) = RawCtxInterpretedReceive.normalResume pending reply := by
  simpa only [known_receive, interpret, Prod.mk.eta] using
    (RawCtxInterpretedReceive.normalResume_map (interpret key)
      (RawCtxInterpretedReceive.mapKdf Slot.known pending) (reply.1, Slot.known reply.2)).symm

/-- The saved native receive resumes once with its actual retained response, then follows every remaining derivation and optional opening. The exact admitted context is enough; no successful-opening or honest-ciphertext premise is used. -/
theorem resume_source (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (parent : Option Entry) (key target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (read : RawCtxReceive.FrameDecoder) (expected : Std.U64)
    (pending : RawCtxInterpretedReceive.Kdf RatchetMaterial RawCtxWholeOwner.OpenContext)
    (reply : RatchetChain × RatchetMaterial) (state : State A)
    (nonempty : pending.context.raw.isEmpty = false)
    (decoded : read pending.context.raw = some pending.context.frame)
    (valid : RawCtxReceive.ValidFrame expected pending.context.associatedData pending.context.frame)
    (targetEq : pending.target = pending.context.frame.sequence) :
    (simulateQ ((RawCtxFunctionalFamily.native source writer
        (privateTable prior parent target (response key nonce next)) ∘ₛ RawCtxMixedOwner.receiveAdapter) ∘ₛ RawCtxWholeOwner.adapter)
      (RawCtxOwnerOracle.program (RawCtxInterpretedReceive.nativeEffect
        (RawCtxInterpretedReceive.normalResume pending reply)))).run (project state) =
      (fun result => ((RawCtxSelectedMessageReveals.nativeKernel key result.1.1, result.1.2), project result.2)) <$>
        (evaluated source key read (resume prior parent target nonce next read expected pending reply)).run state := by
  simpa only [known_resume, resume] using native_effect_source source writer prior parent key target nonce next
    read expected pending.context
    (RawCtxInterpretedReceive.normalResume (RawCtxInterpretedReceive.mapKdf Slot.known pending)
      (reply.1, Slot.known reply.2)) state nonempty decoded valid
    (by simpa only [RawCtxInterpretedReceive.mapKdf, targetEq] using
      (RawCtxSelectedReceiveScope.resume_scope (RawCtxInterpretedReceive.mapKdf Slot.known pending)
        (reply.1, Slot.known reply.2)))

/-- The remainder pays each source private lookup and the optional opening separately. The bound holds for every typed reply, including rejected and repeated queries. -/
theorem effect_services (parent : Option Entry) (target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (pending : RawCtxInterpretedReceive.Effect Slot RawCtxWholeOwner.OpenContext) (selected : Bool) :
    (simulateQ (receiveCompiler (Plaintext := RawCtxWholeOwner.Decrypted) parent target nonce next)
      (RawCtxInterpretedReceive.program pending)).IsQueryBoundP (fun query => query.isLeft = selected)
      (if selected then RawCtxSelectedMessageDriverBounds.cost pending else 1) := by
  apply RawCtxSourceOpen.simulate_bound (receiveCompiler parent target nonce next)
    (fun query => query.isLeft = selected) (fun query => query.isLeft = selected)
  · cases selected with
    | false => simpa only [Bool.false_eq_true, ite_false, RawCtxSelectedMessageDriverBounds.right_pred] using
        RawCtxInterpretedReceive.program_open_bound (Plaintext := RawCtxWholeOwner.Decrypted) pending
    | true => exact RawCtxSelectedMessageDriverBounds.program_cost pending
  · exact fun query => RawCtxSelectedMessageDriverBounds.receive_callback parent target nonce next query selected

/-- Every compiled remainder makes at most one dynamic CTX call; the separate private-lookup bill above retains all source derivation work. -/
theorem effect_queries (prior : Prior) (parent : Option Entry) (target : RootOutput)
    (nonce : NonceOutput) (next : RootOutput) (read : RawCtxReceive.FrameDecoder) (expected : Std.U64)
    (pending : RawCtxInterpretedReceive.Effect Slot RawCtxWholeOwner.OpenContext) :
    (effect prior parent target nonce next read expected pending).IsTotalQueryBound 1 := by
  have bounded := RawCtxSourceOpen.simulate_bound
    (RawCtxSelectedReceiveCompiler.service prior read expected) (fun query => query.isLeft = false) (fun _ => True)
    (simulateQ (receiveCompiler parent target nonce next) (RawCtxInterpretedReceive.program pending)) 1
    (effect_services parent target nonce next pending false)
    (fun query => by simpa only [IsTotalQueryBound, IsQueryBoundP, not_true_eq_false, false_or, ite_true] using
      RawCtxSelectedReceiveCompiler.service_queries prior read expected query)
  simpa only [effect, RawCtxSelectedReceiveCompiler.compiler, ← QueryImpl.simulateQ_compose,
    IsTotalQueryBound, IsQueryBoundP, not_true_eq_false, false_or, ite_true] using bounded

/-- The exact source-owned descriptor supplies every opening condition for its remaining native program. This consumes the literal carried-descriptor certificate rather than a replacement receive context. -/
theorem owner_resume_source {Metadata Result : Type}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (parent : Option Entry) (key target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (read : RawCtxReceive.FrameDecoder) (before : RawCtxForwardOwner.Owner Metadata)
    (outside : core.option.Option RawCtxWholeOwner.Decrypted → OracleComp RawCtxForwardOwner.SourceSpec Result)
    (pending : RawCtxChainReceive.Kdf RatchetChain RatchetChain RatchetMaterial RawCtxWholeOwner.OpenContext)
    (reply : RatchetChain × RatchetMaterial) (state : State A)
    (admitted : RawCtxForwardOwnerScope.Valid read (.receive before outside pending)) :
    (simulateQ ((RawCtxFunctionalFamily.native source writer
        (privateTable prior parent target (response key nonce next)) ∘ₛ RawCtxMixedOwner.receiveAdapter) ∘ₛ RawCtxWholeOwner.adapter)
      (RawCtxOwnerOracle.program (RawCtxInterpretedReceive.nativeEffect
        (RawCtxChainReceive.nativeEffect id id (RawCtxChainReceive.normalResume pending reply))))).run (project state) =
      (fun result => ((RawCtxSelectedMessageReveals.nativeKernel key result.1.1, result.1.2), project result.2)) <$>
        (evaluated source key read (resume prior parent target nonce next read before.expectedSender
          (RawCtxChainReceive.nativeKdf id id pending) reply)).run state := by
  rw [← RawCtxChainReceive.normalResume_native id id pending reply]
  exact resume_source source writer prior parent key target nonce next read before.expectedSender
      (RawCtxChainReceive.nativeKdf id id pending) reply state admitted.1 admitted.2.1
      (by simpa only [RawCtxChainReceive.nativeKdf, admitted.2.2.2.1] using admitted.2.2.1) admitted.2.2.2.2

/-- Resuming an already issued predecessor request does not repeat that request; the remaining CTX allowance is one for every callback outcome. -/
theorem resume_queries (prior : Prior) (parent : Option Entry) (target : RootOutput)
    (nonce : NonceOutput) (next : RootOutput) (read : RawCtxReceive.FrameDecoder) (expected : Std.U64)
    (pending : RawCtxInterpretedReceive.Kdf RatchetMaterial RawCtxWholeOwner.OpenContext)
    (reply : RatchetChain × RatchetMaterial) :
    (resume prior parent target nonce next read expected pending reply).IsTotalQueryBound 1 :=
  effect_queries prior parent target nonce next read expected _

/-- The source counter pays every remaining private lookup after the supplied response. The consumed predecessor request is subtracted exactly once. -/
theorem resume_prior (parent : Option Entry) (target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (pending : RawCtxInterpretedReceive.Kdf RatchetMaterial RawCtxWholeOwner.OpenContext)
    (reply : RatchetChain × RatchetMaterial) :
    (simulateQ (receiveCompiler (Plaintext := RawCtxWholeOwner.Decrypted) parent target nonce next)
      (RawCtxInterpretedReceive.program
        (RawCtxInterpretedReceive.normalResume (RawCtxInterpretedReceive.mapKdf Slot.known pending)
          (reply.1, Slot.known reply.2)))).IsQueryBoundP (fun query => query.isLeft = true)
      (max 1 pending.remaining.val - 1) := by
  apply (effect_services parent target nonce next _ true).mono
  have consumed := RawCtxSelectedMessageDriverBounds.resume_cost
    (RawCtxInterpretedReceive.mapKdf Slot.known pending) (reply.1, Slot.known reply.2)
  exact Nat.le_sub_of_add_le consumed

/-- The supplied full 76-byte predecessor response is decoded once into its retained message material and selected child chain. The executable continuation has no selected child message-key argument. Relating this supplied response to the selected source cut remains the caller's source-correspondence obligation. -/
theorem owner_parent_source {Metadata Result : Type}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (parent : Entry) (key target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (read : RawCtxReceive.FrameDecoder) (before : RawCtxForwardOwner.Owner Metadata)
    (outside : core.option.Option RawCtxWholeOwner.Decrypted → OracleComp RawCtxForwardOwner.SourceSpec Result)
    (pending : RawCtxChainReceive.Kdf RatchetChain RatchetChain RatchetMaterial RawCtxWholeOwner.OpenContext)
    (state : State A) (admitted : RawCtxForwardOwnerScope.Valid read (.receive before outside pending)) :
    (simulateQ ((RawCtxFunctionalFamily.native source writer
        (privateTable prior (some parent) target (response key nonce next)) ∘ₛ RawCtxMixedOwner.receiveAdapter) ∘ₛ RawCtxWholeOwner.adapter)
      (RawCtxOwnerOracle.program (RawCtxOwnerOracle.resume
        (RawCtxInterpretedReceive.nativeKdf (RawCtxChainReceive.nativeKdf id id pending))
        (RawCtxKdfRequestTable.fullResponse (realize parent target))))).run (project state) =
      (fun result => ((RawCtxSelectedMessageReveals.nativeKernel key result.1.1, result.1.2), project result.2)) <$>
        (evaluated source key read (resume prior (some parent) target nonce next read before.expectedSender
          (RawCtxChainReceive.nativeKdf id id pending)
          (RawCtxFreshChainCut.concreteChain target, RawCtxFreshChainCut.concreteMaterial parent.material))).run state := by
  rw [RawCtxInterpretedReceive.normalResume_native, RawCtxSelectedParentEntry.decoded_response]
  exact resume_source source writer prior (some parent) key target nonce next read before.expectedSender
    (RawCtxChainReceive.nativeKdf id id pending)
    (RawCtxFreshChainCut.concreteChain target, RawCtxFreshChainCut.concreteMaterial parent.material)
    state admitted.1 admitted.2.1
    (by simpa only [RawCtxChainReceive.nativeKdf, admitted.2.2.2.1] using admitted.2.2.1) admitted.2.2.2.2

end BeaconcryptCore.Computational.RawCtxSelectedPendingReceiveCompiler

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedPendingReceiveCompiler.effect_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedPendingReceiveCompiler.effect_source

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedPendingReceiveCompiler.native_effect' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedPendingReceiveCompiler.native_effect

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedPendingReceiveCompiler.native_effect_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedPendingReceiveCompiler.native_effect_source

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedPendingReceiveCompiler.known_resume' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedPendingReceiveCompiler.known_resume

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedPendingReceiveCompiler.resume_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedPendingReceiveCompiler.resume_source

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedPendingReceiveCompiler.effect_services' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedPendingReceiveCompiler.effect_services

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedPendingReceiveCompiler.effect_queries' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedPendingReceiveCompiler.effect_queries

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedPendingReceiveCompiler.owner_resume_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedPendingReceiveCompiler.owner_resume_source

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedPendingReceiveCompiler.resume_queries' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedPendingReceiveCompiler.resume_queries

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedPendingReceiveCompiler.resume_prior' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedPendingReceiveCompiler.resume_prior

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedPendingReceiveCompiler.owner_parent_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedPendingReceiveCompiler.owner_parent_source
