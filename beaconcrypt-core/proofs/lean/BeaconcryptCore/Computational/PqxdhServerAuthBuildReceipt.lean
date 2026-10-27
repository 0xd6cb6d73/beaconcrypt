import BeaconcryptCore.Computational.PqxdhServerAuthBuildProgramBounds
import BeaconcryptCore.Computational.PqxdhServerAuthFinishReceipt

/-! Actual registration sealing requests preserve their source binding context through the complete builder. Component production precedes the optional frame writer, so later receipt statements retain that writer's failure branch explicitly. -/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.refined ratchet.concrete PqxdhRefinement
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhServerAuthBuildReceipt
open PqxdhJointKdfGame
open PqxdhServerAuthCtxCalls (Chain Material Kernel Residual)
open PqxdhServerAuthBuildProgram
open PqxdhPhase2LocalMatching (KeyIdBound)

/-- The actual send admission retains its caller's complete seal context. -/
theorem requested_context (entry : Kernel) (context : RawCtxSourceSend.SealContext)
    (pending : RawCtxChainSend.Kdf Chain Chain Material RawCtxSourceSend.SealContext)
    (admitted : RawCtxChainSend.normalBegin entry context = .requested pending) :
    pending.context = context := by
  have begun := RawCtxChainSend.normalBegin_exact entry context
  rw [admitted] at begun
  simp only [RawCtxChainSend.beginSend, Bind.bind, Aeneas.Std.bind] at begun
  repeat' split at begun
  all_goals simp_all only [RustM.ok.injEq, reduceCtorEq]
  all_goals cases begun
  all_goals rfl

def Forbidden (allowed : RawCtxSourceSend.SealContext → Prop) : Spec.Domain → Prop
  | .inl pending => ¬ allowed pending.context
  | .inr _ => False

noncomputable instance (allowed : RawCtxSourceSend.SealContext → Prop) :
    DecidablePred (Forbidden allowed) := Classical.decPred _

/-- Every sealing request of the real send driver carries the complete caller context, independently of its KDF and optional writer replies. -/
theorem send_context (source : FixedHkdfSha512NoSaltSource) (rest : Residual)
    (entry : Kernel) (context : RawCtxSourceSend.SealContext)
    (allowed : RawCtxSourceSend.SealContext → Prop) (valid : allowed context) :
    ((PqxdhServerAuthCtxBuildSettlement.calls (fun entry _ _ => pure (entry, .None))
      source rest sealQuery).send entry context).IsQueryBoundP (Forbidden allowed) 0 := by
  unfold PqxdhServerAuthCtxBuildSettlement.calls RawCtxChainSend.execute
  cases begun : RawCtxChainSend.normalBegin entry context with
  | exhausted previous actual => simp [begun, RawCtxChainSend.program]
  | requested pending =>
      have same := requested_context entry context pending begun
      simp [begun, RawCtxChainSend.program, simulateQ_bind, simulateQ_map,
        PqxdhServerAuthCtxBuildSettlement.labels, sealQuery,
        RawCtxChainSend.ready, Forbidden, same, valid]

variable {Metadata PeerMetadata Consumed : Type}
open PqxdhServerRegistrationPublication (AuxSpec Response registrationWitness firstContext)
open PqxdhInitialGenericPublication (State)

/-- The full initialized tail preserves its literal first-record context through erasure and both optional writers. -/
theorem after_context (source : FixedHkdfSha512NoSaltSource) (rest : Residual)
    (candidate : pqxdh.ServerRegistrationCandidate) (authenticated : Pqxdh.Bytes)
    (entry : Kernel) (metadata : PeerMetadata) (state : State Kernel Metadata PeerMetadata Consumed)
    (allowed : RawCtxSourceSend.SealContext → Prop) (valid : allowed (firstContext candidate authenticated)) :
    (PqxdhInitialGenericPublication.afterInitialization
      (PqxdhServerAuthCtxBuildSettlement.calls (fun entry _ _ => pure (entry, .None)) source rest sealQuery)
      auxQuery candidate authenticated entry metadata state).IsQueryBoundP (Forbidden allowed) 0 := by
  unfold PqxdhInitialGenericPublication.afterInitialization
  refine (isQueryBoundP_bind (send_context source rest entry _ allowed valid)
    (m := 0) (fun sent _ => ?_)).mono (by omega)
  simp only [auxQuery, isQueryBoundP_query_bind_iff]
  refine ⟨by simp [Forbidden], fun _ => ?_⟩
  cases sent.2 with
  | none => trivial
  | some encrypted =>
      rw [isQueryBoundP_query_bind_iff]
      refine ⟨by simp [Forbidden], fun written => ?_⟩
      cases written <;> trivial

/-- Each reached candidate seal carries the exact eight-byte assigned-key binding, through every admission and allocation branch. -/
theorem candidate_bound (source : FixedHkdfSha512NoSaltSource) (rest : Residual)
    (initial : RustM Kernel) (candidate : pqxdh.ServerRegistrationCandidate) (data : Option Pqxdh.Bytes)
    (metadata : PeerMetadata) (state : State Kernel Metadata PeerMetadata Consumed) :
    (PqxdhInitialGenericBuilder.candidate
      (PqxdhServerAuthCtxBuildSettlement.calls (fun entry _ _ => pure (entry, .None)) source rest sealQuery)
      auxQuery initial candidate data metadata state).IsQueryBoundP (Forbidden KeyIdBound) 0 := by
  unfold PqxdhInitialGenericBuilder.candidate
  simp only [auxQuery, isQueryBoundP_query_bind_iff]
  refine ⟨by simp [Forbidden], fun valid => ?_⟩
  cases valid <;> simp only [Bool.not_false, Bool.not_true, Bool.false_eq_true, ite_true, ite_false]
  · trivial
  rw [isQueryBoundP_query_bind_iff]
  refine ⟨by simp [Forbidden], fun reserved => ?_⟩
  cases reserved <;> simp only [Bool.not_false, Bool.not_true, Bool.false_eq_true, ite_true, ite_false]
  · trivial
  cases initial <;> simp only [PqxdhInitialGenericBuilder.continueRust]
  case ok entry =>
    split
    · trivial
    · split
      · rw [isQueryBoundP_query_bind_iff]
        refine ⟨by simp [Forbidden], fun allocated => ?_⟩
        cases allocated <;> simp only [Bool.not_false, Bool.not_true, Bool.false_eq_true, ite_true, ite_false]
        · trivial
        cases binding : candidate.key_id_binding
        case ok bytes =>
          rw [isQueryBoundP_map_iff]
          simpa [Forbidden] using
            after_context source rest candidate _ entry metadata state KeyIdBound
              (PqxdhPhase2LocalMatching.firstContext_bound candidate bytes binding
                (data.getD registrationWitness)).1
        all_goals trivial
      · trivial
  all_goals trivial

/-- The complete next-ID, pending-token binding and peer-availability gates preserve the actual bound-context property. -/
theorem build_bound (source : FixedHkdfSha512NoSaltSource) (rest : Residual)
    (initial : RustM Kernel) (pending : pqxdh.PendingServerRegistration) (data : Option Pqxdh.Bytes)
    (metadata : PeerMetadata) (state : State Kernel Metadata PeerMetadata Consumed) :
    (PqxdhServerAuthSendFactor.genericBuild
      (PqxdhServerAuthCtxBuildSettlement.calls (fun entry _ _ => pure (entry, .None)) source rest sealQuery)
      auxQuery initial pending data metadata state).IsQueryBoundP (Forbidden KeyIdBound) 0 := by
  unfold PqxdhServerAuthSendFactor.genericBuild
  cases pqxdh.server_next_key_id state.control <;> simp only [PqxdhInitialGenericBuilder.continueRust]
  case ok next =>
    cases next with
    | Err => trivial
    | Ok key =>
      cases prepared : pqxdh.server_prepare_commit state.control pending
          ⟨state.server.identity, state.identityKeyId⟩
          (if (state.server.peers key).isSome then .Occupied else .Available) <;>
        simp only [prepared]
      case ok value =>
        cases value with
        | Err => trivial
        | Ok candidate => exact candidate_bound source rest initial candidate data metadata state
      all_goals trivial
  all_goals trivial

/-- The concrete builder issues no sealing request without the source's assigned-key binding. This is a syntactic all-reply property, with no success or selected-key premise. -/
theorem program_bound (source : FixedHkdfSha512NoSaltSource) (rest : Residual)
    (pending : pqxdh.PendingServerRegistration) (data : Option Pqxdh.Bytes)
    (metadata : PeerMetadata) (state : PqxdhServerRegistrationPublication.State Metadata PeerMetadata Consumed) :
    (program source rest pending data metadata state).IsQueryBoundP (Forbidden KeyIdBound) 0 := by
  rw [program, isQueryBoundP_map_iff]
  exact build_bound source rest _ pending data metadata _

open CtxRomAuth
open RawCtxSelectedAuthenticationObserver (monitor)

/-- The precise source metadata for a produced component seal. A cryptographic production can precede a failed frame writer; successful writing records the same context in the actual source log. -/
def FrameOrigin (writer : RawCtxMixedShared.Writer) (log : Log)
    (context : RawCtxSourceSend.SealContext) (sequence : Std.U64) (entry : CtxSuccessfulSeal) : Prop :=
  PqxdhPhase2LocalMatching.Records entry context ∧
    entry.input.context.ad.seq = sequence.val ∧
    entry.input.context.ad.sid = context.senderId.val ∧
    (writer ⟨sequence, context.senderId, entry.record.encode⟩ = none ∨ context ∈ log)

/-- Every newly recorded selected seal comes from this actual sealing callback, with its optional frame-writer result retained. -/
theorem sealer_receipt (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (pending : PqxdhServerAuthCtxSend.Pending) (beforeLog afterLog : Log)
    (before after : RawCtxSelectedAuthenticationObserver.State)
    (result : Option (Option RawCtxSourceSend.Encrypted))
    (supported : ((result, afterLog), after) ∈ support
      (monitor ((sealer source writer pending).run.run beforeLog) before))
    (entry : CtxSuccessfulSeal) (found : entry ∈ after.seals) :
    entry ∈ before.seals ∨ FrameOrigin writer afterLog pending.context pending.sequence entry := by
  rw [sealer_run, RawCtxSelectedAcceptedRecord.monitor_map, support_map] at supported
  obtain ⟨⟨value, observed⟩, reached, equal⟩ := supported
  have history : observed = after := congrArg Prod.snd equal
  have logSame := congrArg (fun outcome => outcome.1.2) equal
  dsimp only at logSame
  rcases RawCtxSelectedSealReceipt.sealing_provenance source.crypto writer
    (PqxdhServerAuthCtxSend.sealing pending) before observed value reached entry
    (history.symm ▸ found) with old | produced
  · exact Or.inl old
  · obtain ⟨nonce, width, record, _, entrySame, completed, _⟩ := produced
    right
    rw [← logSame, completed, entrySame]
    refine ⟨⟨rfl, rfl, rfl⟩, rfl, rfl, ?_⟩
    cases written : writer ⟨pending.sequence, pending.context.senderId, record.encode⟩ with
    | none => exact Or.inl rfl
    | some encoded => exact Or.inr (by simp [PqxdhServerAuthCtxSend.sealing,
        RawCtxChainSend.nativeSeal, written])

/-- The actual optional sealer retains the complete old context log on every reply, including refusal and frame-writer failure. -/
theorem sealer_prefix (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (pending : PqxdhServerAuthCtxSend.Pending) (beforeLog afterLog : Log)
    (before after : RawCtxSelectedAuthenticationObserver.State)
    (result : Option (Option RawCtxSourceSend.Encrypted))
    (supported : ((result, afterLog), after) ∈ support
      (monitor ((sealer source writer pending).run.run beforeLog) before)) :
    beforeLog.IsPrefix afterLog := by
  rw [sealer_run, RawCtxSelectedAcceptedRecord.monitor_map, support_map] at supported
  obtain ⟨⟨value, observed⟩, _, equal⟩ := supported
  have logSame := congrArg (fun outcome => outcome.1.2) equal
  dsimp only at logSame
  rw [← logSame]
  rcases value with (_ | encrypted)
  · exact List.prefix_rfl
  · cases encrypted
    · exact List.prefix_rfl
    · exact ⟨[pending.context], rfl⟩

/-- Source receipts cover only selected component seals. Known-key aliases remain in their original separate interface. -/
def Receipts (writer : RawCtxMixedShared.Writer) (earlier : List CtxSuccessfulSeal) (log : Log)
    (observer : RawCtxSelectedAuthenticationObserver.State) : Prop :=
  ∀ entry ∈ observer.seals, entry ∈ earlier ∨ ∃ context sequence,
    KeyIdBound context ∧ FrameOrigin writer log context sequence entry

/-- A reached source-bound sealer preserves every prior receipt and supplies the exact origin of each new component seal. -/
theorem sealer_preserves (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (pending : PqxdhServerAuthCtxSend.Pending) (bound : KeyIdBound pending.context)
    (beforeLog afterLog : Log) (before after : RawCtxSelectedAuthenticationObserver.State)
    (earlier : List CtxSuccessfulSeal) (valid : Receipts writer earlier beforeLog before)
    (result : Option (Option RawCtxSourceSend.Encrypted))
    (supported : ((result, afterLog), after) ∈ support
      (monitor ((sealer source writer pending).run.run beforeLog) before)) :
    beforeLog.IsPrefix afterLog ∧ Receipts writer earlier afterLog after := by
  have retained := sealer_prefix source writer pending beforeLog afterLog before after result supported
  refine ⟨retained, ?_⟩
  intro entry found
  rcases sealer_receipt source writer pending beforeLog afterLog before after result supported entry found with old | produced
  · rcases valid entry old with old | ⟨context, sequence, bound, fields, seq, sender, publication⟩
    · exact Or.inl old
    · exact Or.inr ⟨context, sequence, bound, fields, seq, sender,
        publication.imp_right (fun member => retained.subset member)⟩
  · exact Or.inr ⟨pending.context, pending.sequence, bound, produced⟩

variable {Reader WireResponse : Type}
open PqxdhServerAuthExperiment (Codec Checks)

/-- Actual auxiliary callbacks add no receipt and keep the complete source log; a reached bound sealing request supplies its own production receipt. -/
theorem compiler_receipts (source : FixedHkdfSha512NoSaltSource) (codec : Codec Reader WireResponse)
    (checks : Checks) (query : Spec.Domain) (bound : ¬ Forbidden KeyIdBound query)
    (beforeLog afterLog : Log) (before after : RawCtxSelectedAuthenticationObserver.State)
    (earlier : List CtxSuccessfulSeal) (valid : Receipts codec.frameWrite earlier beforeLog before)
    (result : Option (Spec.Range query))
    (supported : ((result, afterLog), after) ∈ support
      (monitor ((compiler source codec checks query).run.run beforeLog) before)) :
    beforeLog.IsPrefix afterLog ∧ Receipts codec.frameWrite earlier afterLog after := by
  cases query with
  | inl pending =>
      exact sealer_preserves source codec.frameWrite pending (by simpa [Forbidden] using bound)
        beforeLog afterLog before after earlier valid result supported
  | inr auxiliary =>
      cases auxiliary <;> simp only [compiler, impl, PqxdhServerAuthCtxNative.aux,
        OptionT.run_lift, pure_bind, StateT.run_pure, monitor, simulateQ_pure,
        mem_support_pure_iff] at supported
      all_goals cases supported
      all_goals exact ⟨List.prefix_rfl, valid⟩

private theorem monitor_bind {X Y : Type} (work : OracleComp AdaptiveCtxDynamicKnownKeys.Spec X)
    (next : X → OracleComp AdaptiveCtxDynamicKnownKeys.Spec Y)
    (state : RawCtxSelectedAuthenticationObserver.State) :
    monitor (work >>= next) state =
      (do let result ← monitor work state; monitor (next result.1) result.2) := by
  simp only [monitor, simulateQ_bind, StateT.run_bind]

/-- Arbitrary auxiliary and sealing continuations retain all old receipts and attribute every newly produced seal before returning, including an outer refusal. -/
theorem interpreted_receipts {Result : Type}
    (source : FixedHkdfSha512NoSaltSource) (codec : Codec Reader WireResponse) (checks : Checks)
    (work : OracleComp Spec Result) (bounded : work.IsQueryBoundP (Forbidden KeyIdBound) 0)
    (beforeLog afterLog : Log) (before after : RawCtxSelectedAuthenticationObserver.State)
    (earlier : List CtxSuccessfulSeal) (valid : Receipts codec.frameWrite earlier beforeLog before)
    (result : Option Result)
    (supported : ((result, afterLog), after) ∈ support
      (monitor ((simulateQ (compiler source codec checks) work).run.run beforeLog) before)) :
    beforeLog.IsPrefix afterLog ∧ Receipts codec.frameWrite earlier afterLog after := by
  induction work using OracleComp.inductionOn generalizing beforeLog afterLog before after result with
  | pure value =>
      simp only [simulateQ_pure, OptionT.run_pure, StateT.run_pure, monitor,
        simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at supported
      cases supported
      exact ⟨List.prefix_rfl, valid⟩
  | query_bind query next ih =>
      rw [isQueryBoundP_query_bind_iff] at bounded
      simp only [simulateQ_bind, simulateQ_spec_query, OptionT.run_bind, Option.elimM,
        StateT.run_bind] at supported
      rw [monitor_bind] at supported
      simp only [mem_support_bind_iff] at supported
      obtain ⟨⟨⟨value, middleLog⟩, middle⟩, reached, continued⟩ := supported
      have bound : ¬ Forbidden KeyIdBound query := bounded.1.resolve_right (by omega)
      have step := compiler_receipts source codec checks query bound beforeLog middleLog before middle
        earlier valid value reached
      cases value with
      | none =>
          simp only [Option.elim_none, StateT.run_pure, monitor, simulateQ_pure,
            StateT.run_pure, mem_support_pure_iff] at continued
          cases continued
          exact step
      | some value =>
          have tail := ih value (by simpa only [ite_eq_right bound] using bounded.2 value)
            middleLog afterLog middle after step.2 result continued
          exact ⟨step.1.trans tail.1, tail.2⟩

/-- The complete concrete builder supplies the receipt invariant from its actual source binding construction, for arbitrary initial observer history and all optional outcomes. Every newly produced receipt refers to this builder's reached log or exact failed frame writer. -/
theorem compiled_receipts (source : FixedHkdfSha512NoSaltSource) (codec : Codec Reader WireResponse)
    (checks : Checks) (rest : Residual) (pending : pqxdh.PendingServerRegistration)
    (data : Option Pqxdh.Bytes) (metadata : PeerMetadata)
    (state : PqxdhServerRegistrationPublication.State Metadata PeerMetadata Consumed)
    (beforeLog afterLog : Log) (before after : RawCtxSelectedAuthenticationObserver.State)
    (result : Option (RustM (Option Response × PqxdhServerRegistrationPublication.State Metadata PeerMetadata Consumed)))
    (supported : ((result, afterLog), after) ∈ support
      (monitor ((compiled source codec checks rest pending data metadata state).run.run beforeLog) before)) :
    beforeLog.IsPrefix afterLog ∧ Receipts codec.frameWrite before.seals afterLog after := by
  exact interpreted_receipts source codec checks (program source rest pending data metadata state)
    (program_bound source rest pending data metadata state) beforeLog afterLog before after before.seals
    (fun _ member => Or.inl member) result supported

/-- An actually decoded accepted match cannot select the failed-frame-writer alternative. The same source context is logged and fixes all accepted registration fields. No wire-byte canonicity or session identity follows from this local match. -/
theorem matched_receipt (writer : RawCtxMixedShared.Writer) (read : RawCtxReceive.FrameDecoder)
    (writable : PqxdhFirstBeaconRecordCanonical.ReadWritable writer read)
    (candidate : pqxdh.BeaconRegistrationCandidate) (kernel : ConcreteRatchetKernel)
    (staged : PqxdhBeaconPhase2Publication.Staged)
    (success : PqxdhBeaconPhase2Publication.afterOpening candidate kernel (.Some staged.opened) = some staged)
    (bytes : Pqxdh.Bytes) (target : CtxUnclaimedAcceptance.Target)
    (delivery : PqxdhPhase2LocalMatching.LocalTarget read bytes candidate staged.opened target)
    (entry : CtxSuccessfulSeal) (same : target.toLegacy.sameFullTupleAsSuccessfulSeal entry)
    (plaintext : staged.opened.plaintext = entry.input.plaintext)
    (log : Log) (context : RawCtxSourceSend.SealContext) (sequence : Std.U64)
    (bound : KeyIdBound context) (origin : FrameOrigin writer log context sequence entry) :
    context ∈ log ∧
      PqxdhPhase2LocalMatching.acceptedFields staged = PqxdhPhase2LocalMatching.sealedFields context := by
  obtain ⟨records, seq, sender, publication⟩ := origin
  obtain ⟨encoded, written⟩ := PqxdhServerAuthFinishReceipt.matched_writable writer read writable bytes
    candidate staged.opened target delivery entry same sequence context.senderId seq sender
  refine ⟨?_, PqxdhServerAuthFinishReceipt.matched_fields candidate kernel staged success read bytes target
    delivery entry same plaintext context records bound⟩
  exact publication.resolve_left (by rw [written]; exact Option.some_ne_none encoded)

end BeaconcryptCore.Computational.PqxdhServerAuthBuildReceipt

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthBuildReceipt.requested_context' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthBuildReceipt.requested_context

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthBuildReceipt.send_context' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthBuildReceipt.send_context

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthBuildReceipt.after_context' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthBuildReceipt.after_context

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthBuildReceipt.candidate_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthBuildReceipt.candidate_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthBuildReceipt.build_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthBuildReceipt.build_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthBuildReceipt.program_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthBuildReceipt.program_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthBuildReceipt.sealer_receipt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthBuildReceipt.sealer_receipt

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthBuildReceipt.sealer_prefix' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthBuildReceipt.sealer_prefix

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthBuildReceipt.sealer_preserves' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthBuildReceipt.sealer_preserves

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthBuildReceipt.compiler_receipts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthBuildReceipt.compiler_receipts

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthBuildReceipt.interpreted_receipts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthBuildReceipt.interpreted_receipts

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthBuildReceipt.compiled_receipts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthBuildReceipt.compiled_receipts

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthBuildReceipt.matched_receipt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthBuildReceipt.matched_receipt
