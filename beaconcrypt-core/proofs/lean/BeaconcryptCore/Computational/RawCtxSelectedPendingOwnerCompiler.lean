import BeaconcryptCore.Computational.RawCtxSelectedPendingReceiveCompiler
import BeaconcryptCore.Computational.RawCtxSelectedPendingSendCompiler
import BeaconcryptCore.Computational.RawCtxSelectedParentNativeCompiler
import BeaconcryptCore.Computational.RawCtxQuietOwnerTails
import BeaconcryptCore.Computational.RawCtxSelectedFamilyNativeContext

/-!
The saved owner frame completes its actual pending receive or seal, publishes the complete owner and evaluates its original zero-query outer continuation. Its selected-message representation retains the native chain values and labels only message material; the saved predecessor's chain marker belongs to a separate earlier representation.
-/
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.refined ratchet.concrete
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RawCtxSelectedPendingOwnerCompiler
open PqxdhSecretInputKdf PqxdhFullSecretInputKdf PqxdhJointKdfGame
open RawCtxSelectedMessageKey RawCtxSelectedMessageKdf RawCtxSelectedMessageDriver
open RawCtxSelectedParentTable RawCtxSelectedParentEntry
open RawCtxSelectedReceiveCompiler (State project evaluated)
variable {A Metadata Result : Type}

/-- The original retained-parent interpreter with the selected child response is the actual native receive backend used by the message compiler. The entire source shared state is retained. -/
theorem receive_handler (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (parent : Entry) (key target : RootOutput) (nonce : NonceOutput) (next : RootOutput) :
    RawCtxSelectedParentSource.nativeReceive (Auxiliary := A) source writer
      (RawCtxSelectedParentPrivatePatch.privatePatch prior target (response key nonce next)) parent target =
      (((RawCtxFunctionalFamily.native source writer
        (privateTable prior (some parent) target (response key nonce next)) ∘ₛ RawCtxMixedOwner.receiveAdapter) ∘ₛ
        RawCtxWholeOwner.adapter) ∘ₛ RawCtxInterpretedReceive.nativeAdapter) := by
  rw [← RawCtxFunctionalFamily.receive_handler]
  funext query
  cases query
  all_goals simp only [QueryImpl.compose, RawCtxInterpretedReceive.nativeAdapter,
    simulateQ_map, simulateQ_spec_query, RawCtxMaterialPositions.bareReceiveImpl,
    RawCtxSelectedParentSource.nativeReceive, RawCtxFunctionalFamily.execute,
    RawCtxSelectedParentSource.response, privateTable, map_pure]
  simp only [RawCtxSelectedReceiveCompiler.opening_native, RawCtxSourceChainHandles.receiveNative,
    RawCtxSourceMaterialLabels.nativeImpl, QueryImpl.compose, RawCtxSourceOpen.ownerAdapter,
    ← QueryImpl.simulateQ_compose]
  simp only [RawCtxMixedOwner.receiveAdapter, QueryImpl.simulateQ_compose]
  rw [← QueryImpl.simulateQ_compose, RawCtxMixedShared.shared_receive]

/-- Removing only the native kernel wrapper connects the retained-parent source directly to the complete opaque message-material remainder. -/
theorem retained_effect (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (parent : Entry) (key target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (pending : RawCtxInterpretedReceive.Effect Slot RawCtxWholeOwner.OpenContext) :
    simulateQ (RawCtxSelectedParentSource.nativeReceive (Auxiliary := A) source writer
      (RawCtxSelectedParentPrivatePatch.privatePatch prior target (response key nonce next)) parent target)
      (RawCtxInterpretedReceive.program (RawCtxInterpretedReceive.mapEffect (interpret key) pending)) =
      (fun result => (RawCtxMaterialInterpretation.mapRefined (interpret key) result.1, result.2)) <$>
        simulateQ (receiveServices source writer prior (some parent) key target nonce next ∘ₛ
          receiveCompiler (some parent) target nonce next) (RawCtxInterpretedReceive.program pending) := by
  have native := congrArg
    (fun work : StateT (RawCtxSharedPrimitive.SharedState A) ProbComp
      (ConcreteRatchetKernel × core.option.Option RawCtxWholeOwner.Decrypted) =>
      (fun result => (result.1.refined, result.2)) <$> work)
    (RawCtxSelectedPendingReceiveCompiler.native_effect source writer prior (some parent) key target nonce next pending)
  simpa only [RawCtxInterpretedReceive.program_native, simulateQ_map,
    ← QueryImpl.simulateQ_compose, ← receive_handler, Functor.map_map,
    RawCtxSelectedMessageReveals.nativeKernel, Prod.mk.eta, Functor.map_id, id_map'] using native

/-- Erasing the private pending-query envelope preserves the exact original retained-parent source program from an arbitrary reached effect. -/
theorem pending_program (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (parent : Entry) (target : RootOutput)
    (pending : RawCtxChainReceive.Effect RatchetChain RatchetChain RatchetMaterial RawCtxWholeOwner.OpenContext) :
    simulateQ (RawCtxSelectedParentNativeCompiler.pending (Auxiliary := A) source writer prior parent target)
      (simulateQ RawCtxPendingOwnerQueries.receiveForward (RawCtxPendingReceiveQueries.program pending)) =
      simulateQ (RawCtxSelectedParentSource.nativeReceive source writer prior parent target)
        (RawCtxInterpretedReceive.program (RawCtxChainReceive.nativeEffect id id pending)) := by
  rw [← QueryImpl.simulateQ_compose, ← RawCtxReachedParentSource.view_native]
  congr 1
  funext query
  cases query <;> simp [QueryImpl.compose, RawCtxSelectedParentNativeCompiler.pending,
    RawCtxPendingOwnerQueries.receiveForward, RawCtxPendingOwnerQueries.erase,
    RawCtxSelectedParentNativeCompiler.original, RawCtxReachedParentSource.chainView,
    RawCtxReachedParentCut.viewHandler, RawCtxReachedParentCut.compiler,
    RawCtxRetainedTable.viewImpl, OracleSpec.query]

/-- The actual retained-parent interpreter resumes the supplied response and preserves the complete source result and cache under the key-free remainder compiler. -/
theorem retained_resume_source (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (parent : Entry) (key target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (read : RawCtxReceive.FrameDecoder) (expected : Std.U64)
    (pending : RawCtxInterpretedReceive.Kdf RatchetMaterial RawCtxWholeOwner.OpenContext)
    (reply : RatchetChain × RatchetMaterial) (state : State A)
    (nonempty : pending.context.raw.isEmpty = false)
    (decoded : read pending.context.raw = some pending.context.frame)
    (valid : RawCtxReceive.ValidFrame expected pending.context.associatedData pending.context.frame)
    (targetEq : pending.target = pending.context.frame.sequence) :
    (simulateQ (RawCtxSelectedParentSource.nativeReceive source writer
      (RawCtxSelectedParentPrivatePatch.privatePatch prior target (response key nonce next)) parent target)
      (RawCtxInterpretedReceive.program (RawCtxInterpretedReceive.normalResume pending reply))).run (project state) =
      (fun result => ((RawCtxMaterialInterpretation.mapRefined (interpret key) result.1.1, result.1.2), project result.2)) <$>
        (evaluated source key read (RawCtxSelectedPendingReceiveCompiler.resume prior (some parent) target nonce next read expected pending reply)).run state := by
  rw [← RawCtxSelectedPendingReceiveCompiler.known_resume key pending reply, retained_effect, StateT.run_map]
  rw [RawCtxSelectedPendingReceiveCompiler.effect_source source writer prior (some parent) key target nonce next
    read expected pending.context _ state nonempty decoded valid
    (by simpa only [RawCtxInterpretedReceive.mapKdf, targetEq] using
      (RawCtxSelectedReceiveScope.resume_scope (RawCtxInterpretedReceive.mapKdf Slot.known pending)
        (reply.1, Slot.known reply.2)))]
  simp only [Functor.map_map, Prod.map_def, id_eq, RawCtxSelectedPendingReceiveCompiler.resume]

noncomputable def quietValue (client : OracleComp RawCtxPendingOwnerTails.SourceSpec Result)
    (quiet : client.IsTotalQueryBound 0) : Result := (RawCtxQuietOwnerTails.zero_pure client quiet).choose

/-- The retained zero-query continuation has its actual original return value; it is not replaced by an arbitrary observer. -/
theorem quiet_value (client : OracleComp RawCtxPendingOwnerTails.SourceSpec Result)
    (quiet : client.IsTotalQueryBound 0) : client = pure (quietValue client quiet) :=
  (RawCtxQuietOwnerTails.zero_pure client quiet).choose_spec

/-- The actual owner compiler preserves every owner field when the source continuation has no query. -/
theorem quiet_program {Chain : Type} (sender : Std.U64) (read : RawCtxReceive.FrameDecoder)
    (client : OracleComp RawCtxPendingOwnerTails.SourceSpec Result) (quiet : client.IsTotalQueryBound 0)
    (before : RawCtxPendingOwnerTails.Owner Chain Metadata) :
    RawCtxPendingOwnerTails.program sender read client before = pure (quietValue client quiet, before) := by
  exact congrArg (fun work => RawCtxPendingOwnerTails.program sender read work before) (quiet_value client quiet)

def knownOwner (before : RawCtxPendingOwnerTails.Owner RatchetChain Metadata) :
    RawCtxChainOwner.State RawCtxSelectedMessageReveals.Kernel Metadata :=
  RawCtxGenericOwnerMap.mapOwner (RawCtxMaterialInterpretation.mapRefined Slot.known) before

noncomputable def receive (prior : Prior) (parent : Entry) (target : RootOutput)
    (nonce : NonceOutput) (next : RootOutput) (read : RawCtxReceive.FrameDecoder)
    (before : RawCtxPendingOwnerTails.Owner RatchetChain Metadata)
    (outside : core.option.Option RawCtxWholeOwner.Decrypted → OracleComp RawCtxPendingOwnerTails.SourceSpec Result)
    (pending : RawCtxChainReceive.Kdf RatchetChain RatchetChain RatchetMaterial RawCtxWholeOwner.OpenContext)
    (reply : RatchetChain × RatchetMaterial)
    (quiet : ∀ reply, (outside reply).IsTotalQueryBound 0) :=
  (fun result => let published := RawCtxChainOwner.publish (knownOwner before) result
    (quietValue (outside published.1) (quiet published.1), published.2)) <$>
    RawCtxSelectedPendingReceiveCompiler.resume prior (some parent) target nonce next read before.expectedSender
      (RawCtxChainReceive.nativeKdf id id pending) reply

/-- The exact saved receive tail preserves owner publication, attempt counting, its actual quiet outside return and every source/cache field. -/
theorem receive_source (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (parent : Entry) (key target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (read : RawCtxReceive.FrameDecoder) (sender : Std.U64)
    (before : RawCtxPendingOwnerTails.Owner RatchetChain Metadata)
    (outside : core.option.Option RawCtxWholeOwner.Decrypted → OracleComp RawCtxPendingOwnerTails.SourceSpec Result)
    (pending : RawCtxChainReceive.Kdf RatchetChain RatchetChain RatchetMaterial RawCtxWholeOwner.OpenContext)
    (reply : RatchetChain × RatchetMaterial) (state : State A)
    (quiet : ∀ reply, (outside reply).IsTotalQueryBound 0)
    (admitted : RawCtxForwardOwnerScope.Valid read (.receive before outside pending)) :
    (simulateQ (RawCtxSelectedParentNativeCompiler.pending source writer
      (RawCtxSelectedParentPrivatePatch.privatePatch prior target (response key nonce next)) parent target)
      (RawCtxPendingOwnerTails.receiveTail sender read before outside pending reply)).run (project state) =
      (fun result => ((result.1.1, RawCtxGenericOwnerMap.mapOwner
        (RawCtxMaterialInterpretation.mapRefined (interpret key)) result.1.2), project result.2)) <$>
        (evaluated source key read (receive prior parent target nonce next read before outside pending reply quiet)).run state := by
  simp only [RawCtxPendingOwnerTails.receiveTail, simulateQ_bind, pending_program,
    ← RawCtxChainReceive.normalResume_native, StateT.run_bind, id_eq, Prod.mk.eta]
  rw [retained_resume_source source writer prior parent key target nonce next read before.expectedSender
    (RawCtxChainReceive.nativeKdf id id pending) reply state admitted.1 admitted.2.1
    (by simpa only [RawCtxChainReceive.nativeKdf, admitted.2.2.2.1] using admitted.2.2.1) admitted.2.2.2.2]
  simp only [bind_map_left, receive, RawCtxSelectedReceiveCompiler.evaluated_map, StateT.run_map, Functor.map_map]
  simp only [RawCtxPendingOwnerTails.receiveRest, quiet_program sender read _ (quiet _),
    simulateQ_pure, StateT.run_pure, bind_pure_comp]
  rfl

/-- Complete known owner state reconstructs its original fields for every selected key, including cached aliases. -/
theorem known_owner (key : RootOutput) (before : RawCtxPendingOwnerTails.Owner RatchetChain Metadata) :
    RawCtxGenericOwnerMap.mapOwner (RawCtxMaterialInterpretation.mapRefined (interpret key)) (knownOwner before) = before := by
  cases before
  simp only [knownOwner, RawCtxGenericOwnerMap.mapOwner, known_kernel]

noncomputable def send (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (before : RawCtxPendingOwnerTails.Owner RatchetChain Metadata)
    (outside : Option RawCtxSourceSend.Encrypted → OracleComp RawCtxPendingOwnerTails.SourceSpec Result)
    (pending : RawCtxChainSend.Kdf RatchetChain RatchetChain RatchetMaterial RawCtxSourceSend.SealContext)
    (reply : RatchetChain × RatchetMaterial) (quiet : ∀ reply, (outside reply).IsTotalQueryBound 0) :=
  let ready := RawCtxChainSend.ready pending reply
  (fun sealed => (quietValue (outside sealed) (quiet sealed), knownOwner {before with kernel := ready.advanced})) <$>
    RawCtxSelectedPendingSendCompiler.sealing source.crypto writer (RawCtxChainSend.nativeSeal id id ready)

/-- The complete saved send preserves the actual optional writer result and advanced owner, including writer failure, before its original quiet continuation returns. -/
theorem send_source (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (parent : Entry) (key target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (read : RawCtxReceive.FrameDecoder) (sender : Std.U64)
    (before : RawCtxPendingOwnerTails.Owner RatchetChain Metadata)
    (outside : Option RawCtxSourceSend.Encrypted → OracleComp RawCtxPendingOwnerTails.SourceSpec Result)
    (pending : RawCtxChainSend.Kdf RatchetChain RatchetChain RatchetMaterial RawCtxSourceSend.SealContext)
    (reply : RatchetChain × RatchetMaterial) (state : State A)
    (quiet : ∀ reply, (outside reply).IsTotalQueryBound 0) :
    (simulateQ (RawCtxSelectedParentNativeCompiler.pending source writer
      (RawCtxSelectedParentPrivatePatch.privatePatch prior target (response key nonce next)) parent target)
      (RawCtxPendingOwnerTails.sendTail sender read before outside pending reply)).run (project state) =
      (fun result => ((result.1.1, RawCtxGenericOwnerMap.mapOwner
        (RawCtxMaterialInterpretation.mapRefined (interpret key)) result.1.2), project result.2)) <$>
        (evaluated source key read (send source writer before outside pending reply quiet)).run state := by
  simp only [RawCtxPendingOwnerTails.sendTail, simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
  simp only [RawCtxSelectedParentNativeCompiler.pending, QueryImpl.compose,
    RawCtxPendingOwnerQueries.erase, simulateQ_spec_query, RawCtxSelectedParentNativeCompiler.original,
    RawCtxSelectedParentSource.nativeSend]
  rw [RawCtxSelectedPendingSendCompiler.source_seal source writer
    (privateTable prior (some parent) target (response key nonce next)),
    RawCtxSelectedPendingSendCompiler.sealing_source source writer prior (some parent) key target nonce next read]
  simp only [send, RawCtxSelectedReceiveCompiler.evaluated_map, StateT.run_map, Functor.map_map,
    RawCtxPendingOwnerTails.sendRest, quiet_program sender read _ (quiet _), simulateQ_pure, StateT.run_pure, bind_pure_comp]
  simp only [known_owner, Prod.map_def, id_eq]

/-- The retained predecessor address is the literal request address of the saved owner descriptor. -/
def entry (context : RawCtxSelectedFamilyContext.OwnerContext Metadata Result)
    (value : PqxdhOrderedChainHybrids.Material) : Entry :=
  ⟨RawCtxSelectedFamilyContext.ownerAddress context, value⟩

noncomputable def owner (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (target : RootOutput) (nonce : NonceOutput) (next : RootOutput) (read : RawCtxReceive.FrameDecoder)
    (context : RawCtxSelectedFamilyContext.OwnerContext Metadata Result) (value : PqxdhOrderedChainHybrids.Material)
    (quiet : RawCtxQuietOwnerTails.Quiet context) :=
  match context with
  | .receive before outside pending => receive prior (entry context value) target nonce next read before outside pending
      (RawCtxFreshChainCut.concreteChain target, RawCtxFreshChainCut.concreteMaterial value) quiet
  | .send before outside pending => send source writer before outside pending
      (RawCtxFreshChainCut.concreteChain target, RawCtxFreshChainCut.concreteMaterial value) quiet

/-- Both actual owner-frame alternatives consume their own full predecessor response, complete publication and exact source continuation. The retained private address is derived from that same descriptor. -/
theorem owner_source (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (key target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (read : RawCtxReceive.FrameDecoder) (sender : Std.U64)
    (context : RawCtxSelectedFamilyContext.OwnerContext Metadata Result) (value : PqxdhOrderedChainHybrids.Material)
    (state : State A) (quiet : RawCtxQuietOwnerTails.Quiet context)
    (admitted : RawCtxForwardOwnerScope.Valid read context) :
    (simulateQ (RawCtxSelectedParentNativeCompiler.pending source writer
      (RawCtxSelectedParentPrivatePatch.privatePatch prior target (response key nonce next)) (entry context value) target)
      ((RawCtxSelectedFamilyContext.ownerFrame sender read context).2
        (RawCtxSelectedFamilyNativeContext.ownerReply sender read context (realize (entry context value) target)))).run
      (project state) =
      (fun result => ((result.1.1, RawCtxGenericOwnerMap.mapOwner
        (RawCtxMaterialInterpretation.mapRefined (interpret key)) result.1.2), project result.2)) <$>
        (evaluated source key read (owner source writer prior target nonce next read context value quiet)).run state := by
  cases context
  all_goals simp only [owner, RawCtxSelectedFamilyContext.ownerFrame,
    RawCtxSelectedFamilyNativeContext.ownerReply, RawCtxSelectedParentEntry.decoded_response]
  case receive before outside pending =>
    exact receive_source source writer prior (entry (.receive before outside pending) value) key target nonce next
      read sender before outside pending (RawCtxFreshChainCut.concreteChain target, RawCtxFreshChainCut.concreteMaterial value)
      state quiet admitted
  case send before outside pending =>
    exact send_source source writer prior (entry (.send before outside pending) value) key target nonce next
      read sender before outside pending (RawCtxFreshChainCut.concreteChain target, RawCtxFreshChainCut.concreteMaterial value)
      state quiet

/-- Complete owner publication and its actual zero-query outside continuation add no dynamic calls to the one-call receive/seal allowance. Private lookup and earlier prefix work retain their separate source bills. -/
theorem owner_queries (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (target : RootOutput) (nonce : NonceOutput) (next : RootOutput) (read : RawCtxReceive.FrameDecoder)
    (context : RawCtxSelectedFamilyContext.OwnerContext Metadata Result) (value : PqxdhOrderedChainHybrids.Material)
    (quiet : RawCtxQuietOwnerTails.Quiet context) :
    (owner source writer prior target nonce next read context value quiet).IsTotalQueryBound 1 := by
  cases context
  all_goals simp only [owner, receive, send, IsTotalQueryBound, isQueryBound_map_iff]
  case receive before outside pending => exact RawCtxSelectedPendingReceiveCompiler.resume_queries prior _ target nonce next read before.expectedSender _ _
  case send before outside pending => exact RawCtxSelectedPendingSendCompiler.sealing_queries source.crypto writer _

end BeaconcryptCore.Computational.RawCtxSelectedPendingOwnerCompiler

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedPendingOwnerCompiler.receive_handler' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedPendingOwnerCompiler.receive_handler

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedPendingOwnerCompiler.retained_effect' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedPendingOwnerCompiler.retained_effect

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedPendingOwnerCompiler.pending_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedPendingOwnerCompiler.pending_program

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedPendingOwnerCompiler.retained_resume_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedPendingOwnerCompiler.retained_resume_source

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedPendingOwnerCompiler.quiet_value' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedPendingOwnerCompiler.quiet_value

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedPendingOwnerCompiler.quiet_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedPendingOwnerCompiler.quiet_program

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedPendingOwnerCompiler.receive_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedPendingOwnerCompiler.receive_source

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedPendingOwnerCompiler.known_owner' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedPendingOwnerCompiler.known_owner

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedPendingOwnerCompiler.send_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedPendingOwnerCompiler.send_source

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedPendingOwnerCompiler.owner_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedPendingOwnerCompiler.owner_source

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedPendingOwnerCompiler.owner_queries' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedPendingOwnerCompiler.owner_queries
