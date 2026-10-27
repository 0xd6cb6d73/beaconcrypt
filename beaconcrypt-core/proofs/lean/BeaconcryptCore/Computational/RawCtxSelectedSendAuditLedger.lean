import BeaconcryptCore.Computational.RawCtxSelectedFamilySendEvents
import BeaconcryptCore.Computational.RawCtxSelectedSendCompiler
import BeaconcryptCore.Computational.RawCtxSelectedSendLedger
import BeaconcryptCore.Computational.RawCtxSelectedFamilyCompiler

/-!
The selected component nonce ledger is traced to the original send's actual event trailer. No nonce uniqueness premise is used: repeated selected nonces remain explicit outcomes, and failed serialization retains its attempted seal.
-/
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.refined ratchet.concrete
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RawCtxSelectedSendAuditLedger
open PqxdhSecretInputKdf PqxdhFullSecretInputKdf PqxdhJointKdfGame
open RawCtxSelectedParentTable RawCtxSelectedParentEntry RawCtxSelectedMessageDriver
open RawCtxSelectedDriverAudit
open AdaptiveCtxDynamicKnownKeys
variable {Owner : Type}

/-- Every new selected nonce in the actual compiled send comes from a seal in that same source send's precise audit trailer. -/
theorem send_used (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (parent : Option Entry) (key target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (read : RawCtxReceive.FrameDecoder) (owner : Owner)
    (entry : RawCtxSelectedMessageReveals.Kernel) (context : RawCtxSourceSend.SealContext)
    (before after : SourceState) (reply : Option (RawCtxSelectedMessageReveals.Kernel × Option RawCtxSourceSend.Encrypted))
    (supported : (reply, after) ∈ support ((simulateQ
      (sourceImpl true (RawCtxUniversalDecoder.decoder read) source.crypto key)
      (RawCtxSelectedSendCompiler.send source writer prior parent target nonce next entry context)).run before)) :
    ∀ value ∈ after.selected.1.usedNonces, value ∈ before.selected.1.usedNonces ∨
      ∃ occurrence, Event.sealing occurrence ∈ RawCtxSelectedSendEvents.events prior parent target nonce next owner entry context ∧
        RawCtxSelectedSendTrace.nonce occurrence.pending = some value := by
  rw [RawCtxSelectedSendCompiler.send_cases] at supported
  cases started : RawCtxInterpretedSend.normalBegin entry context with
  | exhausted kernel exhausted =>
      simp only [started, simulateQ_pure, StateT.run_pure, mem_support_pure_iff, Prod.mk.injEq] at supported
      rcases supported with ⟨_, rfl⟩
      exact fun _ used => Or.inl used
  | requested request =>
      simp only [started, simulateQ_map, StateT.run_map, support_map] at supported
      obtain ⟨result, reached, equal⟩ := supported
      have state := congrArg Prod.snd equal
      dsimp only at state
      subst after
      intro value used
      rcases RawCtxSelectedSendTrace.scalar_used (RawCtxUniversalDecoder.decoder read) source.crypto key writer
          (RawCtxInterpretedSend.ready request (RawCtxSelectedSendCompiler.deriveValue prior parent target nonce next request.request))
          before result.2 result.1 reached value used with old | current
      · exact Or.inl old
      · refine Or.inr ⟨⟨owner, entry, _⟩, ?_, current⟩
        simp only [RawCtxSelectedSendEvents.events, started]
        exact List.mem_cons_of_mem _ (List.mem_singleton_self _)

/-- Appending the actual source event trailer preserves the complete component nonce-to-source-occurrence invariant, including compiler refusal and failed serialization. -/
theorem send_tracked (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (parent : Option Entry) (key target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (read : RawCtxReceive.FrameDecoder) (owner : Owner)
    (entry : RawCtxSelectedMessageReveals.Kernel) (context : RawCtxSourceSend.SealContext)
    (history : List (Event Owner)) (before after : SourceState)
    (reply : Option (RawCtxSelectedMessageReveals.Kernel × Option RawCtxSourceSend.Encrypted))
    (tracked : RawCtxSelectedSendTrace.Tracked before (RawCtxSourceEventRecorder.seals history))
    (supported : (reply, after) ∈ support ((simulateQ
      (sourceImpl true (RawCtxUniversalDecoder.decoder read) source.crypto key)
      (RawCtxSelectedSendCompiler.send source writer prior parent target nonce next entry context)).run before)) :
    RawCtxSelectedSendTrace.Tracked after (RawCtxSourceEventRecorder.seals
      (history ++ RawCtxSelectedSendEvents.events prior parent target nonce next owner entry context)) := by
  intro value used
  rcases send_used source writer prior parent key target nonce next read owner entry context before after reply supported value used with old | current
  · obtain ⟨earlier, found, same⟩ := tracked value old
    exact ⟨earlier, (RawCtxSourceEventRecorder.mem_seals _ _).mpr
      (List.mem_append_left _ ((RawCtxSourceEventRecorder.mem_seals history earlier).mp found)), same⟩
  · obtain ⟨occurrence, found, same⟩ := current
    exact ⟨occurrence, (RawCtxSourceEventRecorder.mem_seals _ _).mpr (List.mem_append_right _ found), same⟩

/-- The actual source send's refusal predicate has a selected nonce in its original pending seal and the reached component ledger. -/
theorem stop_current (prior : Prior) (parent : Option Entry) (target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (owner : Owner) (entry : RawCtxSelectedMessageReveals.Kernel) (context : RawCtxSourceSend.SealContext)
    (state : SourceState) (stopped : RawCtxSelectedSendCompiler.Stops prior parent target nonce next entry context state) :
    ∃ value occurrence, Event.sealing occurrence ∈ RawCtxSelectedSendEvents.events prior parent target nonce next owner entry context ∧
      RawCtxSelectedSendTrace.nonce occurrence.pending = some value ∧ value ∈ state.selected.1.usedNonces := by
  cases started : RawCtxInterpretedSend.normalBegin entry context with
  | exhausted kernel exhausted =>
      simp only [RawCtxSelectedSendCompiler.Stops, started] at stopped
  | requested request =>
      simp only [RawCtxSelectedSendCompiler.Stops, started, RawCtxSelectedSendCompiler.Repeated] at stopped
      obtain ⟨value, material, width, used⟩ := stopped
      refine ⟨value, ⟨owner, entry, RawCtxInterpretedSend.ready request
        (RawCtxSelectedSendCompiler.deriveValue prior parent target nonce next request.request)⟩, ?_, ?_, used⟩
      · simp only [RawCtxSelectedSendEvents.events, started]
        exact List.mem_cons_of_mem _ (List.mem_singleton_self _)
      · simp [RawCtxSelectedSendTrace.nonce, material, width]

/-- A refusal has a matching earlier occurrence in the existing source audit and a current occurrence in the actual new source trailer. Earlier and current entries may have equal values; their provenance remains separated between the old history and the new trailer. -/
theorem stopped_pair (prior : Prior) (parent : Option Entry) (target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (owner : Owner) (entry : RawCtxSelectedMessageReveals.Kernel) (context : RawCtxSourceSend.SealContext)
    (history : List (Event Owner)) (state : SourceState)
    (tracked : RawCtxSelectedSendTrace.Tracked state (RawCtxSourceEventRecorder.seals history))
    (stopped : RawCtxSelectedSendCompiler.Stops prior parent target nonce next entry context state) :
    ∃ value earlier current, Event.sealing earlier ∈ history ∧
      Event.sealing current ∈ RawCtxSelectedSendEvents.events prior parent target nonce next owner entry context ∧
      RawCtxSelectedSendTrace.nonce earlier.pending = some value ∧
      RawCtxSelectedSendTrace.nonce current.pending = some value := by
  obtain ⟨value, current, found, selected, used⟩ := stop_current prior parent target nonce next owner entry context state stopped
  obtain ⟨earlier, old, same⟩ := tracked value used
  exact ⟨value, earlier, current, (RawCtxSourceEventRecorder.mem_seals history earlier).mp old, found, same, selected⟩

/-- The complete concrete receive compiler makes no selected sealing query, for all cached/future reply paths. -/
theorem receive_quiet (prior : Prior) (parent : Option Entry) (target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (read : RawCtxReceive.FrameDecoder) (expected : Std.U64) (entry : RawCtxSelectedMessageReveals.Kernel)
    (sequence : Std.U64) (context : RawCtxWholeOwner.OpenContext) :
    (RawCtxSelectedReceiveCompiler.receive prior parent target nonce next read expected entry sequence context).IsQueryBoundP
      (AdaptiveCtxDynamicKnownBounds.TargetClass AdaptiveCtxQueryBounds.SourceSeal) 0 := by
  unfold RawCtxSelectedReceiveCompiler.receive
  apply (isQueryBoundP_false (RawCtxSelectedMessageDriver.receive parent target nonce next entry sequence context) 0).simulateQ_of_step
    (fun _ impossible => False.elim impossible)
  intro query _
  cases query with
  | inl address => trivial
  | inr pending => exact (RawCtxSelectedOpenConsumer.service_other 0 read expected pending).1

/-- Cached and future receive execution preserves the actual component nonce ledger through every opening result and rejection. -/
theorem receive_ledger (source : FixedHkdfSha512NoSaltSource) (key : RootOutput)
    (prior : Prior) (parent : Option Entry) (target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (read : RawCtxReceive.FrameDecoder) (expected : Std.U64) (entry : RawCtxSelectedMessageReveals.Kernel)
    (sequence : Std.U64) (context : RawCtxWholeOwner.OpenContext) (before : SourceState)
    (result : (RawCtxSelectedMessageReveals.Kernel × core.option.Option RawCtxWholeOwner.Decrypted) × SourceState)
    (supported : result ∈ support ((simulateQ (sourceImpl true (RawCtxUniversalDecoder.decoder read) source.crypto key)
      (RawCtxSelectedReceiveCompiler.receive prior parent target nonce next read expected entry sequence context)).run before)) :
    result.2.selected.1.usedNonces = before.selected.1.usedNonces :=
  RawCtxSelectedSendLedger.program_nonseal (RawCtxUniversalDecoder.decoder read) source.crypto key _
    (receive_quiet prior parent target nonce next read expected entry sequence context) before result supported

/-- Caller coins, public commitment hashes and real public HKDF cannot invoke selected sealing. -/
theorem public_quiet (source : FixedHkdfSha512NoSaltSource) (query : RawCtxServerServices.PublicSpec.Domain) :
    (RawCtxSelectedFamilyCompiler.publicWork source query).IsQueryBoundP
      (AdaptiveCtxDynamicKnownBounds.TargetClass AdaptiveCtxQueryBounds.SourceSeal) 0 := by
  rcases query with coin | (bytes | request)
  · exact (isQueryBoundP_query_iff _ _ 0).mpr (by simp [AdaptiveCtxDynamicKnownBounds.TargetClass, AdaptiveCtxQueryBounds.SourceSeal])
  · simp only [RawCtxSelectedFamilyCompiler.publicWork, isQueryBoundP_map_iff]
    exact (isQueryBoundP_query_iff _ _ 0).mpr (by simp [AdaptiveCtxDynamicKnownBounds.TargetClass, AdaptiveCtxQueryBounds.SourceSeal])
  · trivial

/-- The actual public interface retains the selected nonce ledger while executing its original shared hash, uniform and fixed-HKDF effects. -/
theorem public_ledger (source : FixedHkdfSha512NoSaltSource) (key : RootOutput) (read : RawCtxReceive.FrameDecoder)
    (query : RawCtxServerServices.PublicSpec.Domain) (before : SourceState)
    (result : RawCtxServerServices.PublicSpec.Range query × SourceState)
    (supported : result ∈ support ((simulateQ (sourceImpl true (RawCtxUniversalDecoder.decoder read) source.crypto key)
      (RawCtxSelectedFamilyCompiler.publicWork source query)).run before)) :
    result.2.selected.1.usedNonces = before.selected.1.usedNonces :=
  RawCtxSelectedSendLedger.program_nonseal (RawCtxUniversalDecoder.decoder read) source.crypto key _
    (public_quiet source query) before result supported

/-- Raw parser rejection and admitted cached/future receives all make zero selected sealing requests. -/
theorem raw_quiet {Metadata : Type} (prior : Prior) (parent : Option Entry) (target : RootOutput)
    (nonce : NonceOutput) (next : RootOutput) (read : RawCtxReceive.FrameDecoder) (bytes : Pqxdh.Bytes)
    (owner : RawCtxChainOwner.State RawCtxSelectedMessageReveals.Kernel Metadata) :
    (RawCtxSelectedReceiveCompiler.raw prior parent target nonce next read bytes owner).IsQueryBoundP
      (AdaptiveCtxDynamicKnownBounds.TargetClass AdaptiveCtxQueryBounds.SourceSeal) 0 := by
  unfold RawCtxSelectedReceiveCompiler.raw RawCtxChainOwner.rawReceive
  simp only [StateT.run]
  split
  · trivial
  · split
    · trivial
    · split
      · simp only [RawCtxSelectedReceiveCompiler.calls, bind_pure_comp, isQueryBoundP_map_iff]
        exact receive_quiet prior parent target nonce next read _ owner.kernel _ _
      · trivial

end BeaconcryptCore.Computational.RawCtxSelectedSendAuditLedger

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedSendAuditLedger.send_used' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedSendAuditLedger.send_used
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedSendAuditLedger.send_tracked' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedSendAuditLedger.send_tracked
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedSendAuditLedger.stop_current' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedSendAuditLedger.stop_current
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedSendAuditLedger.stopped_pair' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedSendAuditLedger.stopped_pair
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedSendAuditLedger.receive_quiet' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedSendAuditLedger.receive_quiet
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedSendAuditLedger.receive_ledger' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedSendAuditLedger.receive_ledger
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedSendAuditLedger.public_quiet' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedSendAuditLedger.public_quiet
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedSendAuditLedger.public_ledger' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedSendAuditLedger.public_ledger
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedSendAuditLedger.raw_quiet' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedSendAuditLedger.raw_quiet
