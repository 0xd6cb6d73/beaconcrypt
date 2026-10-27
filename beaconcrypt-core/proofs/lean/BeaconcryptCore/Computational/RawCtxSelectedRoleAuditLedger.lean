import BeaconcryptCore.Computational.RawCtxSelectedSendAuditLedger

/-!
Original owner and role admission determines the actual send trailer that can change the selected component nonce ledger. Raw parser, routing and phase rejection remain ordinary operations with their complete component state.
-/
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.refined ratchet.concrete
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RawCtxSelectedRoleAuditLedger
open PqxdhSecretInputKdf PqxdhFullSecretInputKdf PqxdhJointKdfGame
open RawCtxSelectedParentTable RawCtxSelectedParentEntry RawCtxSelectedMessageDriver
open RawCtxSelectedDriverAudit
open AdaptiveCtxDynamicKnownKeys
open RawCtxSelectedOwnerCompiler (Kernel)
variable {Owner Metadata : Type}

noncomputable def ownerEvents (prior : Prior) (parent : Option Entry) (target : RootOutput)
    (nonce : NonceOutput) (next : RootOutput) (label : Owner) (sender : Std.U64)
    (query : RawCtxMixedOwner.SourceSpec.Domain) (entry : RawCtxChainOwner.State Kernel Metadata) : List (Event Owner) :=
  match query with
  | .inr _ => []
  | .inl plaintext => if plaintext.isEmpty then [] else
      RawCtxSelectedSendEvents.events prior parent target nonce next label entry.kernel
        ⟨plaintext, entry.expectedSender, sender, entry.associatedData⟩

def UsedBy (events : List (Event Owner)) (before after : SourceState) : Prop :=
  ∀ value ∈ after.selected.1.usedNonces, value ∈ before.selected.1.usedNonces ∨
    ∃ occurrence, Event.sealing occurrence ∈ events ∧ RawCtxSelectedSendTrace.nonce occurrence.pending = some value

/-- Original empty-send admission and arbitrary raw delivery cannot manufacture a selected nonce; every added nonce has its actual source send trailer. -/
theorem owner_used (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (parent : Option Entry) (key target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (read : RawCtxReceive.FrameDecoder) (label : Owner) (sender : Std.U64)
    (query : RawCtxMixedOwner.SourceSpec.Domain) (entry : RawCtxChainOwner.State Kernel Metadata)
    (before after : SourceState) (reply : Option (RawCtxMixedOwner.SourceSpec.Range query × RawCtxChainOwner.State Kernel Metadata))
    (supported : (reply, after) ∈ support ((simulateQ (sourceImpl true (RawCtxUniversalDecoder.decoder read) source.crypto key)
      (RawCtxSelectedOwnerCompiler.owner source writer prior parent target nonce next read sender query entry)).run before)) :
    UsedBy (ownerEvents prior parent target nonce next label sender query entry) before after := by
  cases query with
  | inl plaintext =>
      rw [RawCtxSelectedOwnerCompiler.send_cases] at supported
      by_cases empty : plaintext.isEmpty = true
      · simp only [empty, ite_true, simulateQ_pure, StateT.run_pure, mem_support_pure_iff, Prod.mk.injEq] at supported
        rcases supported with ⟨_, rfl⟩
        exact fun _ used => Or.inl used
      · simp only [empty, Bool.false_eq_true, ite_false, simulateQ_map, StateT.run_map, support_map] at supported
        obtain ⟨result, reached, equal⟩ := supported
        have state := congrArg Prod.snd equal
        dsimp only at state
        subst after
        simpa only [UsedBy, ownerEvents, empty, Bool.false_eq_true, ite_false] using
          RawCtxSelectedSendAuditLedger.send_used source writer prior parent key target nonce next read label entry.kernel
            ⟨plaintext, entry.expectedSender, sender, entry.associatedData⟩ before result.2 result.1 reached
  | inr raw =>
      rw [RawCtxSelectedOwnerCompiler.raw_cases] at supported
      simp only [simulateQ_map, StateT.run_map, support_map] at supported
      obtain ⟨result, reached, equal⟩ := supported
      have state := congrArg Prod.snd equal
      dsimp only at state
      subst after
      have unchanged := RawCtxSelectedSendLedger.program_nonseal (RawCtxUniversalDecoder.decoder read) source.crypto key _
        (RawCtxSelectedSendAuditLedger.raw_quiet prior parent target nonce next read raw entry) before result reached
      intro value used
      exact Or.inl (unchanged ▸ used)

variable {I D K M P : Type}

noncomputable def beaconEvents (prior : Prior) (parent : Option Entry) (target : RootOutput)
    (nonce : NonceOutput) (next : RootOutput) (label : Owner)
    (query : RawCtxMixedOwner.SourceSpec.Domain) (entry : RawCtxGenericRoleStorage.BeaconState Kernel I D K) : List (Event Owner) :=
  match entry.beacon.phase with
  | .established control ad kernel => ownerEvents prior parent target nonce next label entry.beacon.identityKeyId query
      (RawCtxGenericBeacon.selected entry control ad kernel)
  | _ => []

/-- Every actual Beacon phase retains the ledger, with new nonces attributable only to its established owner's admitted send. -/
theorem beacon_used (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (parent : Option Entry) (key target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (read : RawCtxReceive.FrameDecoder) (label : Owner) (query : RawCtxMixedOwner.SourceSpec.Domain)
    (entry : RawCtxGenericRoleStorage.BeaconState Kernel I D K) (before after : SourceState)
    (reply : Option (RawCtxMixedOwner.SourceSpec.Range query × RawCtxGenericRoleStorage.BeaconState Kernel I D K))
    (supported : (reply, after) ∈ support ((simulateQ (sourceImpl true (RawCtxUniversalDecoder.decoder read) source.crypto key)
      (RawCtxSelectedRoleCompiler.beacon source writer prior parent target nonce next read query entry)).run before)) :
    UsedBy (beaconEvents prior parent target nonce next label query entry) before after := by
  rw [RawCtxSelectedRoleCompiler.beacon_cases] at supported
  cases phase : entry.beacon.phase
  case established control ad kernel =>
    simp only [phase, simulateQ_map, StateT.run_map, support_map] at supported
    obtain ⟨result, reached, equal⟩ := supported
    have state := congrArg Prod.snd equal
    dsimp only at state
    subst after
    simpa only [beaconEvents, phase] using owner_used source writer prior parent key target nonce next read label
      entry.beacon.identityKeyId query (RawCtxGenericBeacon.selected entry control ad kernel) before result.2 result.1 reached
  all_goals
    simp only [phase, simulateQ_pure, StateT.run_pure, mem_support_pure_iff, Prod.mk.injEq] at supported
    rcases supported with ⟨_, rfl⟩
    exact fun _ used => Or.inl used

/-- The actual Server raw path makes no selected sealing request, including failed route, AD and repeated peer lookups. -/
theorem server_raw_quiet (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (parent : Option Entry) (target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (read : RawCtxReceive.FrameDecoder)
    (raw : Pqxdh.Bytes) (entry : RawCtxGenericRoleStorage.ServerState Kernel M P) :
    (RawCtxSelectedRoleCompiler.server source writer prior parent target nonce next sender route read (.inr raw) entry).IsQueryBoundP
      (AdaptiveCtxDynamicKnownBounds.TargetClass AdaptiveCtxQueryBounds.SourceSeal) 0 := by
  rw [RawCtxSelectedRoleCompiler.server_raw_cases]
  split
  · trivial
  · split
    · trivial
    · split
      · trivial
      · rw [isQueryBoundP_map_iff, RawCtxSelectedOwnerCompiler.raw_cases, isQueryBoundP_map_iff]
        exact RawCtxSelectedSendAuditLedger.raw_quiet prior parent target nonce next read raw _

noncomputable def serverEvents (prior : Prior) (parent : Option Entry) (target : RootOutput)
    (nonce : NonceOutput) (next : RootOutput) (label : Std.U64 → Owner) (sender : M → Std.U64)
    (query : RawCtxServerMixed.SourceSpec.Domain) (entry : RawCtxGenericRoleStorage.ServerState Kernel M P) : List (Event Owner) :=
  match query with
  | .inr _ => []
  | .inl (plaintext, kid) => match RawCtxGenericServer.peerAssociatedData entry.server kid with
    | none => []
    | some ad => match entry.server.peers kid with
      | none => []
      | some peer => ownerEvents prior parent target nonce next (label kid) (sender entry.server.metadata) (.inl plaintext)
          (RawCtxGenericServer.selectedOwner kid ad peer entry.rawAttempts)

/-- The complete original Server operation attributes every added nonce to the send admitted by its actual selected-peer and AD lookups. -/
theorem server_used (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (parent : Option Entry) (key target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (label : Std.U64 → Owner) (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (read : RawCtxReceive.FrameDecoder)
    (query : RawCtxServerMixed.SourceSpec.Domain) (entry : RawCtxGenericRoleStorage.ServerState Kernel M P)
    (before after : SourceState)
    (reply : Option (RawCtxServerMixed.SourceSpec.Range query × RawCtxGenericRoleStorage.ServerState Kernel M P))
    (supported : (reply, after) ∈ support ((simulateQ (sourceImpl true (RawCtxUniversalDecoder.decoder read) source.crypto key)
      (RawCtxSelectedRoleCompiler.server source writer prior parent target nonce next sender route read query entry)).run before)) :
    UsedBy (serverEvents prior parent target nonce next label sender query entry) before after := by
  cases query with
  | inl request =>
      rcases request with ⟨plaintext, kid⟩
      rw [RawCtxSelectedRoleCompiler.server_send_cases] at supported
      cases adFound : RawCtxGenericServer.peerAssociatedData entry.server kid with
      | none =>
          simp only [adFound, simulateQ_pure, StateT.run_pure, mem_support_pure_iff, Prod.mk.injEq] at supported
          rcases supported with ⟨_, rfl⟩
          exact fun _ used => Or.inl used
      | some ad =>
          simp only [adFound] at supported
          cases found : entry.server.peers kid with
          | none =>
              simp only [found, simulateQ_pure, StateT.run_pure, mem_support_pure_iff, Prod.mk.injEq] at supported
              rcases supported with ⟨_, rfl⟩
              exact fun _ used => Or.inl used
          | some peer =>
              simp only [found, simulateQ_map, StateT.run_map, support_map] at supported
              obtain ⟨result, reached, equal⟩ := supported
              have state := congrArg Prod.snd equal
              dsimp only at state
              subst after
              simpa only [serverEvents, adFound, found] using owner_used source writer prior parent key target nonce next read
                (label kid) (sender entry.server.metadata) (.inl plaintext)
                (RawCtxGenericServer.selectedOwner kid ad peer entry.rawAttempts) before result.2 result.1 reached
  | inr raw =>
      have unchanged := RawCtxSelectedSendLedger.program_nonseal (RawCtxUniversalDecoder.decoder read) source.crypto key _
        (server_raw_quiet source writer prior parent target nonce next sender route read raw entry) before (reply, after) supported
      intro value used
      exact Or.inl (unchanged ▸ used)

variable {S B : Nat}

noncomputable def familyEvents (prior : Prior) (parent : Option Entry) (target : RootOutput)
    (nonce : NonceOutput) (next : RootOutput) (sender : M → Std.U64)
    (query : (RawCtxProtocolRoles.SourceSpec S B).Domain)
    (entry : RawCtxGenericRoleFamily.Roles Kernel M P I D K S B) : List (Event (RawCtxProtocolReveals.Owner S B)) :=
  match query with
  | .inl ⟨index, request⟩ => serverEvents prior parent target nonce next (.server index) sender request (entry.1 index)
  | .inr (.inl ⟨index, request⟩) => beaconEvents prior parent target nonce next (.beacon index) request (entry.2 index)
  | .inr (.inr _) => []

/-- The actual finite family supplies owner labels from its original dispatch; every new component nonce belongs to that operation's concrete admitted send. -/
theorem family_used (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (parent : Option Entry) (key target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (read : RawCtxReceive.FrameDecoder)
    (query : (RawCtxProtocolRoles.SourceSpec S B).Domain)
    (entry : RawCtxGenericRoleFamily.Roles Kernel M P I D K S B) (before after : SourceState)
    (reply : Option ((RawCtxProtocolRoles.SourceSpec S B).Range query × RawCtxGenericRoleFamily.Roles Kernel M P I D K S B))
    (supported : (reply, after) ∈ support ((simulateQ (sourceImpl true (RawCtxUniversalDecoder.decoder read) source.crypto key)
      (RawCtxSelectedFamilyCompiler.family source writer prior parent target nonce next sender route read query entry)).run before)) :
    UsedBy (familyEvents prior parent target nonce next sender query entry) before after := by
  rw [RawCtxSelectedFamilyCompiler.family_cases] at supported
  rcases query with ⟨index, request⟩ | (⟨index, request⟩ | request)
  · simp only [simulateQ_map, StateT.run_map, support_map] at supported
    obtain ⟨result, reached, equal⟩ := supported
    have state := congrArg Prod.snd equal
    dsimp only at state
    subst after
    exact server_used source writer prior parent key target nonce next (RawCtxProtocolReveals.Owner.server index : Std.U64 → RawCtxProtocolReveals.Owner S B) sender route read request (entry.1 index)
      before result.2 result.1 reached
  · simp only [simulateQ_map, StateT.run_map, support_map] at supported
    obtain ⟨result, reached, equal⟩ := supported
    have state := congrArg Prod.snd equal
    dsimp only at state
    subst after
    exact beacon_used source writer prior parent key target nonce next read (RawCtxProtocolReveals.Owner.beacon index : RawCtxProtocolReveals.Owner S B) request (entry.2 index)
      before result.2 result.1 reached
  · simp only [simulateQ_map, StateT.run_map, support_map] at supported
    obtain ⟨result, reached, equal⟩ := supported
    have state := congrArg Prod.snd equal
    dsimp only at state
    subst after
    have unchanged := RawCtxSelectedSendAuditLedger.public_ledger source key read request before result reached
    intro value used
    exact Or.inl (unchanged ▸ used)

/-- Appending source trailers preserves the component nonce invariant without treating repeated equal events as distinct values. -/
theorem tracked {Owner : Type} (events history : List (Event Owner)) (before after : SourceState)
    (used : UsedBy events before after)
    (previous : RawCtxSelectedSendTrace.Tracked before (RawCtxSourceEventRecorder.seals history)) :
    RawCtxSelectedSendTrace.Tracked after (RawCtxSourceEventRecorder.seals (history ++ events)) := by
  intro value present
  rcases used value present with old | current
  · obtain ⟨earlier, found, same⟩ := previous value old
    exact ⟨earlier, (RawCtxSourceEventRecorder.mem_seals _ _).mpr
      (List.mem_append_left _ ((RawCtxSourceEventRecorder.mem_seals history earlier).mp found)), same⟩
  · obtain ⟨occurrence, found, same⟩ := current
    exact ⟨occurrence, (RawCtxSourceEventRecorder.mem_seals _ _).mpr (List.mem_append_right _ found), same⟩

def RepeatedEvent (events : List (Event Owner)) (state : SourceState) : Prop :=
  ∃ value occurrence, Event.sealing occurrence ∈ events ∧
    RawCtxSelectedSendTrace.nonce occurrence.pending = some value ∧ value ∈ state.selected.1.usedNonces

/-- The actual owner refusal belongs to a nonempty admitted source send and a nonce already in the component ledger. -/
theorem owner_stopped (prior : Prior) (parent : Option Entry) (target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (label : Owner) (sender : Std.U64) (query : RawCtxMixedOwner.SourceSpec.Domain)
    (entry : RawCtxChainOwner.State Kernel Metadata) (state : SourceState)
    (stopped : RawCtxSelectedOwnerCompiler.Stops prior parent target nonce next sender query entry state) :
    RepeatedEvent (ownerEvents prior parent target nonce next label sender query entry) state := by
  cases query with
  | inr raw => exact False.elim stopped
  | inl plaintext =>
      obtain ⟨nonempty, actual⟩ := stopped
      simpa only [RepeatedEvent, ownerEvents, nonempty, Bool.false_eq_true, ite_false] using
        RawCtxSelectedSendAuditLedger.stop_current prior parent target nonce next label entry.kernel
          ⟨plaintext, entry.expectedSender, sender, entry.associatedData⟩ state actual

/-- An actual Beacon refusal comes from its reached established sending owner, with the same source trailer and ledger. -/
theorem beacon_stopped (prior : Prior) (parent : Option Entry) (target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (label : Owner) (query : RawCtxMixedOwner.SourceSpec.Domain)
    (entry : RawCtxGenericRoleStorage.BeaconState Kernel I D K) (state : SourceState)
    (stopped : RawCtxSelectedRoleCompiler.BeaconStops prior parent target nonce next query entry state) :
    RepeatedEvent (beaconEvents prior parent target nonce next label query entry) state := by
  cases phase : entry.beacon.phase
  case established control ad kernel =>
    simp only [RawCtxSelectedRoleCompiler.BeaconStops, phase] at stopped
    simpa only [beaconEvents, phase] using owner_stopped prior parent target nonce next label entry.beacon.identityKeyId query
      (RawCtxGenericBeacon.selected entry control ad kernel) state stopped
  all_goals
    simp only [RawCtxSelectedRoleCompiler.BeaconStops, phase] at stopped

/-- Server refusal retains the actual sender, AD and selected-peer route that admitted its current send. -/
theorem server_stopped (prior : Prior) (parent : Option Entry) (target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (label : Std.U64 → Owner) (sender : M → Std.U64) (query : RawCtxServerMixed.SourceSpec.Domain)
    (entry : RawCtxGenericRoleStorage.ServerState Kernel M P) (state : SourceState)
    (stopped : RawCtxSelectedRoleCompiler.ServerStops prior parent target nonce next sender query entry state) :
    RepeatedEvent (serverEvents prior parent target nonce next label sender query entry) state := by
  cases query with
  | inr raw => exact False.elim stopped
  | inl request =>
      rcases request with ⟨plaintext, kid⟩
      cases adFound : RawCtxGenericServer.peerAssociatedData entry.server kid with
      | none => simp only [RawCtxSelectedRoleCompiler.ServerStops, adFound] at stopped
      | some ad =>
          cases found : entry.server.peers kid with
          | none => simp only [RawCtxSelectedRoleCompiler.ServerStops, adFound, found] at stopped
          | some peer =>
              simp only [RawCtxSelectedRoleCompiler.ServerStops, adFound, found] at stopped
              simpa only [serverEvents, adFound, found] using owner_stopped prior parent target nonce next (label kid)
                (sender entry.server.metadata) (.inl plaintext) (RawCtxGenericServer.selectedOwner kid ad peer entry.rawAttempts) state stopped

/-- Every actual family refusal has a current source send occurrence whose nonce was already present before that same operation. -/
theorem family_stopped (prior : Prior) (parent : Option Entry) (target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (sender : M → Std.U64) (query : (RawCtxProtocolRoles.SourceSpec S B).Domain)
    (entry : RawCtxGenericRoleFamily.Roles Kernel M P I D K S B) (state : SourceState)
    (stopped : RawCtxSelectedFamilyCompiler.Stops prior parent target nonce next sender query entry state) :
    RepeatedEvent (familyEvents prior parent target nonce next sender query entry) state := by
  rcases query with ⟨index, request⟩ | (⟨index, request⟩ | request)
  · exact server_stopped prior parent target nonce next
      (RawCtxProtocolReveals.Owner.server index : Std.U64 → RawCtxProtocolReveals.Owner S B)
      sender request (entry.1 index) state stopped
  · exact beacon_stopped prior parent target nonce next (RawCtxProtocolReveals.Owner.beacon index : RawCtxProtocolReveals.Owner S B)
      request (entry.2 index) state stopped
  · exact False.elim stopped

end BeaconcryptCore.Computational.RawCtxSelectedRoleAuditLedger

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedRoleAuditLedger.owner_used' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedRoleAuditLedger.owner_used
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedRoleAuditLedger.beacon_used' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedRoleAuditLedger.beacon_used
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedRoleAuditLedger.server_raw_quiet' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedRoleAuditLedger.server_raw_quiet
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedRoleAuditLedger.server_used' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedRoleAuditLedger.server_used
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedRoleAuditLedger.family_used' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedRoleAuditLedger.family_used
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedRoleAuditLedger.tracked' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedRoleAuditLedger.tracked
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedRoleAuditLedger.owner_stopped' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedRoleAuditLedger.owner_stopped
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedRoleAuditLedger.beacon_stopped' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedRoleAuditLedger.beacon_stopped
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedRoleAuditLedger.server_stopped' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedRoleAuditLedger.server_stopped
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedRoleAuditLedger.family_stopped' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedRoleAuditLedger.family_stopped
