import BeaconcryptCore.Computational.RawCtxRetainedNativeCycles
import BeaconcryptCore.Computational.RawCtxSelectedSourceSendInputs

/-!
Directional source certificates are transported into the exact augmented execution used by the selected-nonce comparison. Its effective private table includes the selected response and retained-parent priority. The history is the existing source-event ledger; no independent run or replacement history is introduced.
-/
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.refined ratchet.concrete
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RawCtxNonceHistoryPaths
open PqxdhSecretInputKdf PqxdhFullSecretInputKdf PqxdhJointKdfGame
open RawCtxSelectedParentTable RawCtxSelectedParentEntry RawCtxSelectedMessageStopping
variable {AD PT CT A M P I D K Result : Type} {S B : Nat}

def Good (prior : Prior) (cr : Ratchet.Crypto RatchetChain RatchetMaterial AD PT CT)
    (sendOrigin receiveOrigin : RatchetChain) (selected : RawCtxProtocolReveals.Owner S B)
    (key : RootOutput) (entry : RawCtxSelectedFamilyLiveCompiler.Front M P I D K S B) : Prop :=
  ∀ kernel, RawCtxProtocolReveals.selectedKernel selected
      (RawCtxSelectedMessageReveals.nativeState key entry).1 = some kernel →
    RoleReachable (withInterpreter cr (RawCtxFunctionalFamily.execute prior)) sendOrigin receiveOrigin kernel

/-- The complete normal selected-material interpreter retains source directional origins under its actual effective private table, including the retained predecessor. -/
theorem normal_reachable (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (parent : Option Entry) (key target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (cr : Ratchet.Crypto RatchetChain RatchetMaterial AD PT CT) (sendOrigin receiveOrigin : RatchetChain)
    (selected : RawCtxProtocolReveals.Owner S B)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (read : RawCtxReceive.FrameDecoder)
    (client : OracleComp (RawCtxProtocolReveals.SourceSpec S B) Result)
    (before : RawCtxSelectedFamilyNonceCoupling.SourceFull M P I D K A S B)
    (result : Result × RawCtxSelectedFamilyNonceCoupling.SourceFull M P I D K A S B)
    (supported : result ∈ support ((simulateQ (normal
      (sourceRecord source writer prior parent key target nonce next sender route read) key) client).run before))
    (initial : Good (RawCtxSelectedMessageDriver.privateTable prior parent target
      (RawCtxSelectedMessageKdf.response key nonce next)) cr sendOrigin receiveOrigin selected key before.1) :
    Good (RawCtxSelectedMessageDriver.privateTable prior parent target
      (RawCtxSelectedMessageKdf.response key nonce next)) cr sendOrigin receiveOrigin selected key result.2.1 := by
  apply RawCtxRetainedNativeCycles.source_reachable source writer
    (RawCtxSelectedMessageDriver.privateTable prior parent target (RawCtxSelectedMessageKdf.response key nonce next))
    cr sendOrigin receiveOrigin selected sender route read client
    (RawCtxSelectedMessageReveals.nativeState key before.1) before.2 (nativeOutput key result) _ initial
  rw [native_schedule, support_map]
  exact ⟨result, supported, rfl⟩

/-- The original optional callback preserves those same source origins, including a withheld reveal and its retained observation. -/
theorem original_reachable (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (parent : Option Entry) (key target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (cr : Ratchet.Crypto RatchetChain RatchetMaterial AD PT CT) (sendOrigin receiveOrigin : RatchetChain)
    (selected : RawCtxProtocolReveals.Owner S B)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (read : RawCtxReceive.FrameDecoder)
    (query : (RawCtxProtocolReveals.SourceSpec S B).Domain)
    (before : RawCtxSelectedFamilyNonceCoupling.SourceFull M P I D K A S B)
    (result : Option ((RawCtxProtocolReveals.SourceSpec S B).Range query) × RawCtxSelectedFamilyNonceCoupling.SourceFull M P I D K A S B)
    (supported : result ∈ support ((RawCtxSelectedFamilyNonceCoupling.original
      source writer prior parent key target nonce next sender route read query).run before))
    (initial : Good (RawCtxSelectedMessageDriver.privateTable prior parent target
      (RawCtxSelectedMessageKdf.response key nonce next)) cr sendOrigin receiveOrigin selected key before.1) :
    Good (RawCtxSelectedMessageDriver.privateTable prior parent target
      (RawCtxSelectedMessageKdf.response key nonce next)) cr sendOrigin receiveOrigin selected key result.2.1 := by
  cases query with
  | inl request =>
      simp only [RawCtxSelectedFamilyNonceCoupling.original, stopping, OptionT.run_mk, StateT.run, support_map] at supported
      obtain ⟨reply, reached, rfl⟩ := supported
      apply normal_reachable source writer prior parent key target nonce next cr sendOrigin receiveOrigin selected
        sender route read ((RawCtxProtocolReveals.SourceSpec S B).query (.inl request)) before
        (reply.1, ((reply.2.1, RawCtxSelectedMessageFamily.tick before.1.2), reply.2.2)) _ initial
      simp only [simulateQ_spec_query, normal, StateT.run, support_map]
      exact ⟨reply, reached, rfl⟩
  | inr request =>
      simp only [RawCtxSelectedFamilyNonceCoupling.original, stopping, OptionT.run_mk, StateT.run, mem_support_pure_iff] at supported
      subst result
      exact initial

/-- The exact augmented callback used by nonce accounting preserves source origins even when it executes the refused send and retains the original cache. -/
theorem augmented_reachable (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (parent : Option Entry) (key target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (cr : Ratchet.Crypto RatchetChain RatchetMaterial AD PT CT) (sendOrigin receiveOrigin : RatchetChain)
    (selected : RawCtxProtocolReveals.Owner S B)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (read : RawCtxReceive.FrameDecoder)
    (query : (RawCtxProtocolReveals.SourceSpec S B).Domain)
    (before : RawCtxSelectedFamilyNonceCoupling.Full M P I D K A S B)
    (result : Option ((RawCtxProtocolReveals.SourceSpec S B).Range query) × RawCtxSelectedFamilyNonceCoupling.Full M P I D K A S B)
    (supported : result ∈ support ((RawCtxSelectedFamilyNonceCoupling.augmented
      source writer prior parent key target nonce next sender route read query).run before))
    (initial : Good (RawCtxSelectedMessageDriver.privateTable prior parent target
      (RawCtxSelectedMessageKdf.response key nonce next)) cr sendOrigin receiveOrigin selected key before.1) :
    Good (RawCtxSelectedMessageDriver.privateTable prior parent target
      (RawCtxSelectedMessageKdf.response key nonce next)) cr sendOrigin receiveOrigin selected key result.2.1 := by
  apply original_reachable source writer prior parent key target nonce next cr sendOrigin receiveOrigin selected
    sender route read query (RawCtxSelectedFamilyNonceCoupling.project before)
    (result.1, RawCtxSelectedFamilyNonceCoupling.project result.2) _ initial
  rw [← RawCtxSelectedFamilyNonceCoupling.augmented_step, support_map]
  exact ⟨result, supported, rfl⟩

open RawCtxSelectedDriverAudit RawCtxSelectedRoleAuditLedger

private theorem owner_fields {Owner Metadata : Type} (prior : Prior) (parent : Option Entry) (target : RootOutput)
    (nonce : NonceOutput) (next : RootOutput) (label : Owner) (sender : Std.U64)
    (query : RawCtxMixedOwner.SourceSpec.Domain)
    (entry : RawCtxChainOwner.State RawCtxSelectedOwnerCompiler.Kernel Metadata)
    (occurrence : RawCtxSelectedSendTrace.Occurrence Owner)
    (found : Event.sealing occurrence ∈ ownerEvents prior parent target nonce next label sender query entry) :
    occurrence.owner = label ∧ occurrence.entry = entry.kernel := by
  cases query with
  | inr raw => simp only [ownerEvents, List.not_mem_nil] at found
  | inl plaintext =>
      dsimp only [ownerEvents] at found
      split at found
      · exact False.elim (List.not_mem_nil found)
      · have fields := RawCtxSelectedSendEvents.sealing_routed prior parent target nonce next label entry.kernel
          ⟨plaintext, entry.expectedSender, sender, entry.associatedData⟩ occurrence found
        exact ⟨fields.1, fields.2.1⟩


/-- Every recorded seal names the exact pre-call owner lookup, including Beacon phase and Server peer admission. -/
theorem event_lookup (prior : Prior) (parent : Option Entry) (target : RootOutput)
    (nonce : NonceOutput) (next : RootOutput) (sender : M → Std.U64)
    (query : (RawCtxProtocolReveals.SourceSpec S B).Domain)
    (entry : RawCtxSelectedFamilyLiveCompiler.Front M P I D K S B)
    (occurrence : RawCtxSelectedSendTrace.Occurrence (RawCtxProtocolReveals.Owner S B))
    (found : Event.sealing occurrence ∈ RawCtxSelectedLiveAuditLedger.events prior parent target nonce next sender query entry) :
    RawCtxGenericRoleFamily.selectedKernel occurrence.owner entry.1 = some occurrence.entry := by
  cases query with
  | inr request => simp only [RawCtxSelectedLiveAuditLedger.events, List.not_mem_nil] at found
  | inl request =>
      rcases request with ⟨index, request⟩ | (⟨index, request⟩ | request)
      · cases request with
        | inr raw => simp only [RawCtxSelectedLiveAuditLedger.events, familyEvents, serverEvents, List.not_mem_nil] at found
        | inl request =>
            rcases request with ⟨plaintext, kid⟩
            cases associated : RawCtxGenericServer.peerAssociatedData (entry.1.1 index).server kid with
            | none => simp only [RawCtxSelectedLiveAuditLedger.events, familyEvents, serverEvents, associated, List.not_mem_nil] at found
            | some ad =>
                cases peerFound : (entry.1.1 index).server.peers kid with
                | none => simp only [RawCtxSelectedLiveAuditLedger.events, familyEvents, serverEvents, associated, peerFound, List.not_mem_nil] at found
                | some peer =>
                    simp only [RawCtxSelectedLiveAuditLedger.events, familyEvents, serverEvents, associated, peerFound] at found
                    have fields := owner_fields prior parent target nonce next
                      (RawCtxProtocolReveals.Owner.server index kid) (sender (entry.1.1 index).server.metadata)
                      (.inl plaintext) (RawCtxGenericServer.selectedOwner kid ad peer (entry.1.1 index).rawAttempts)
                      occurrence found
                    simp only [fields.1, fields.2, RawCtxGenericRoleFamily.selectedKernel, peerFound, Option.map_some, RawCtxGenericServer.selectedOwner]
      · cases phase : (entry.1.2 index).beacon.phase
        case established control ad kernel =>
          simp only [RawCtxSelectedLiveAuditLedger.events, familyEvents, beaconEvents, phase] at found
          have fields := owner_fields prior parent target nonce next (RawCtxProtocolReveals.Owner.beacon index)
            (entry.1.2 index).beacon.identityKeyId request (RawCtxGenericBeacon.selected (entry.1.2 index) control ad kernel)
            occurrence found
          simp only [fields.1, fields.2, RawCtxGenericRoleFamily.selectedKernel, phase, RawCtxGenericBeacon.selected]
        all_goals simp only [RawCtxSelectedLiveAuditLedger.events, familyEvents, beaconEvents, phase, List.not_mem_nil] at found
      · simp only [RawCtxSelectedLiveAuditLedger.events, familyEvents, List.not_mem_nil] at found

/-- A seal's actual pre-call kernel inherits its selected owner's source certificate; owner labels are taken from dispatch, never inferred from key bytes. -/
theorem event_reachable (prior retained : Prior) (parent : Option Entry) (key target : RootOutput)
    (nonce : NonceOutput) (next : RootOutput)
    (cr : Ratchet.Crypto RatchetChain RatchetMaterial AD PT CT) (sendOrigin receiveOrigin : RatchetChain)
    (selected : RawCtxProtocolReveals.Owner S B) (sender : M → Std.U64)
    (query : (RawCtxProtocolReveals.SourceSpec S B).Domain)
    (entry : RawCtxSelectedFamilyLiveCompiler.Front M P I D K S B)
    (initial : Good retained cr sendOrigin receiveOrigin selected key entry)
    (occurrence : RawCtxSelectedSendTrace.Occurrence (RawCtxProtocolReveals.Owner S B))
    (found : Event.sealing occurrence ∈ RawCtxSelectedLiveAuditLedger.events prior parent target nonce next sender query entry)
    (owned : occurrence.owner = selected) :
    RoleReachable (withInterpreter cr (RawCtxFunctionalFamily.execute retained)) sendOrigin receiveOrigin
      (RawCtxSelectedMessageReveals.nativeKernel key occurrence.entry) := by
  apply initial (RawCtxSelectedMessageReveals.nativeKernel key occurrence.entry)
  simp only [RawCtxSelectedMessageReveals.nativeState, ← owned, RawCtxGenericRoleFamily.native_selected,
    event_lookup prior parent target nonce next sender query entry occurrence found, Option.map_some]

def HistoryGood (prior : Prior) (cr : Ratchet.Crypto RatchetChain RatchetMaterial AD PT CT)
    (sendOrigin receiveOrigin : RatchetChain) (selected : RawCtxProtocolReveals.Owner S B)
    (key : RootOutput) (history : List (Event (RawCtxProtocolReveals.Owner S B))) : Prop :=
  ∀ occurrence, Event.sealing occurrence ∈ history → occurrence.owner = selected →
    RoleReachable (withInterpreter cr (RawCtxFunctionalFamily.execute prior)) sendOrigin receiveOrigin
      (RawCtxSelectedMessageReveals.nativeKernel key occurrence.entry)

/-- One literal nonce-event callback preserves current source paths and adds only actual pre-call source path certificates to the existing history. -/
theorem history_step (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (parent : Option Entry) (key target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (cr : Ratchet.Crypto RatchetChain RatchetMaterial AD PT CT) (sendOrigin receiveOrigin : RatchetChain)
    (selected : RawCtxProtocolReveals.Owner S B)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (read : RawCtxReceive.FrameDecoder)
    (query : (RawCtxProtocolReveals.SourceSpec S B).Domain)
    (before : RawCtxSelectedLiveAuditLedger.State M P I D K A S B)
    (result : Option ((RawCtxProtocolReveals.SourceSpec S B).Range query) × RawCtxSelectedLiveAuditLedger.State M P I D K A S B)
    (supported : result ∈ support ((RawCtxSelectedLiveAuditLedger.observed
      source writer prior parent key target nonce next sender route read query).run before))
    (initial : Good (RawCtxSelectedMessageDriver.privateTable prior parent target
      (RawCtxSelectedMessageKdf.response key nonce next)) cr sendOrigin receiveOrigin selected key before.2.1)
    (history : HistoryGood (RawCtxSelectedMessageDriver.privateTable prior parent target
      (RawCtxSelectedMessageKdf.response key nonce next)) cr sendOrigin receiveOrigin selected key before.1) :
    Good (RawCtxSelectedMessageDriver.privateTable prior parent target
      (RawCtxSelectedMessageKdf.response key nonce next)) cr sendOrigin receiveOrigin selected key result.2.2.1 ∧
    HistoryGood (RawCtxSelectedMessageDriver.privateTable prior parent target
      (RawCtxSelectedMessageKdf.response key nonce next)) cr sendOrigin receiveOrigin selected key result.2.1 := by
  simp only [RawCtxSelectedLiveAuditLedger.observed, StateT.run, support_map] at supported
  obtain ⟨reply, reached, rfl⟩ := supported
  refine ⟨augmented_reachable source writer prior parent key target nonce next cr sendOrigin receiveOrigin selected
    sender route read query before.2 reply reached initial, ?_⟩
  intro occurrence found owned
  rcases List.mem_append.mp found with old | current
  · exact history occurrence old owned
  · exact event_reachable prior _ parent key target nonce next cr sendOrigin receiveOrigin selected
      sender query before.2.1 initial occurrence current owned

/-- The complete adaptive nonce-event execution preserves every original source state and attributes its entire history to the same directional origins. -/
theorem history_program (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (parent : Option Entry) (key target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (cr : Ratchet.Crypto RatchetChain RatchetMaterial AD PT CT) (sendOrigin receiveOrigin : RatchetChain)
    (selected : RawCtxProtocolReveals.Owner S B)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (read : RawCtxReceive.FrameDecoder)
    (client : OracleComp (RawCtxSelectedFamilyNonceCoupling.Optional (RawCtxProtocolReveals.SourceSpec S B)) Result)
    (before : RawCtxSelectedLiveAuditLedger.State M P I D K A S B)
    (result : Result × RawCtxSelectedLiveAuditLedger.State M P I D K A S B)
    (supported : result ∈ support ((simulateQ (RawCtxSelectedLiveAuditLedger.observed
      source writer prior parent key target nonce next sender route read) client).run before))
    (initial : Good (RawCtxSelectedMessageDriver.privateTable prior parent target
      (RawCtxSelectedMessageKdf.response key nonce next)) cr sendOrigin receiveOrigin selected key before.2.1)
    (history : HistoryGood (RawCtxSelectedMessageDriver.privateTable prior parent target
      (RawCtxSelectedMessageKdf.response key nonce next)) cr sendOrigin receiveOrigin selected key before.1) :
    Good (RawCtxSelectedMessageDriver.privateTable prior parent target
      (RawCtxSelectedMessageKdf.response key nonce next)) cr sendOrigin receiveOrigin selected key result.2.2.1 ∧
    HistoryGood (RawCtxSelectedMessageDriver.privateTable prior parent target
      (RawCtxSelectedMessageKdf.response key nonce next)) cr sendOrigin receiveOrigin selected key result.2.1 := by
  induction client using OracleComp.inductionOn generalizing before result with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at supported
      simpa only [supported] using And.intro initial history
  | query_bind query continuation ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at supported
      obtain ⟨reply, reached, tail⟩ := supported
      have step := history_step source writer prior parent key target nonce next cr sendOrigin receiveOrigin selected
        sender route read query before reply reached initial history
      exact ih reply.1 reply.2 result tail step.1 step.2

/-- Every send in the exact nonce-event history has its chronological source path under the explicit initial-state certificate. The initial private history is empty. -/
theorem sealing_path (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (parent : Option Entry) (key target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (cr : Ratchet.Crypto RatchetChain RatchetMaterial AD PT CT) (sendOrigin receiveOrigin : RatchetChain)
    (selected : RawCtxProtocolReveals.Owner S B)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (read : RawCtxReceive.FrameDecoder)
    (client : OracleComp (RawCtxSelectedFamilyNonceCoupling.Optional (RawCtxProtocolReveals.SourceSpec S B)) Result)
    (before : RawCtxSelectedFamilyNonceCoupling.Full M P I D K A S B)
    (result : Result × RawCtxSelectedLiveAuditLedger.State M P I D K A S B)
    (supported : result ∈ support ((simulateQ (RawCtxSelectedLiveAuditLedger.observed
      source writer prior parent key target nonce next sender route read) client).run ([], before)))
    (initial : Good (RawCtxSelectedMessageDriver.privateTable prior parent target
      (RawCtxSelectedMessageKdf.response key nonce next)) cr sendOrigin receiveOrigin selected key before.1)
    (occurrence : RawCtxSelectedSendTrace.Occurrence (RawCtxProtocolReveals.Owner S B))
    (found : Event.sealing occurrence ∈ result.2.1) (owned : occurrence.owner = selected) :
    RawCtxSourceSendPath.Path (RawCtxSelectedQueryTrace.rootVector sendOrigin)
      (RawCtxSelectedMessageReveals.nativeKernel key occurrence.entry)
      (RawCtxRetainedFunctionalPath.table (RawCtxSelectedMessageDriver.privateTable prior parent target
        (RawCtxSelectedMessageKdf.response key nonce next))) := by
  apply RawCtxRetainedFunctionalPath.reachable_path _ cr sendOrigin receiveOrigin
  exact (history_program source writer prior parent key target nonce next cr sendOrigin receiveOrigin selected
    sender route read client ([], before) result supported initial
    (fun _ impossible => False.elim (List.not_mem_nil impossible))).2 occurrence found owned

end BeaconcryptCore.Computational.RawCtxNonceHistoryPaths

/-- info: 'BeaconcryptCore.Computational.RawCtxNonceHistoryPaths.normal_reachable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxNonceHistoryPaths.normal_reachable
/-- info: 'BeaconcryptCore.Computational.RawCtxNonceHistoryPaths.original_reachable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxNonceHistoryPaths.original_reachable
/-- info: 'BeaconcryptCore.Computational.RawCtxNonceHistoryPaths.augmented_reachable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxNonceHistoryPaths.augmented_reachable
/-- info: 'BeaconcryptCore.Computational.RawCtxNonceHistoryPaths.event_lookup' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxNonceHistoryPaths.event_lookup
/-- info: 'BeaconcryptCore.Computational.RawCtxNonceHistoryPaths.event_reachable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxNonceHistoryPaths.event_reachable
/-- info: 'BeaconcryptCore.Computational.RawCtxNonceHistoryPaths.history_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxNonceHistoryPaths.history_step
/-- info: 'BeaconcryptCore.Computational.RawCtxNonceHistoryPaths.history_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxNonceHistoryPaths.history_program
/-- info: 'BeaconcryptCore.Computational.RawCtxNonceHistoryPaths.sealing_path' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxNonceHistoryPaths.sealing_path
