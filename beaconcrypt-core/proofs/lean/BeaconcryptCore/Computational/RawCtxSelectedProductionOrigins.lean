import BeaconcryptCore.Computational.RawCtxSelectedSealReceipt

/-!
Actual source send dispatch attributes successful selected productions to the original owner, peer route and private entry state. These are source-origin receipts, not a claim that equal CTX fields identify an installation or symbolic session. Writer failure and cryptographic production remain distinct.
-/
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.refined ratchet.concrete
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RawCtxSelectedProductionOrigins
open PqxdhSecretInputKdf PqxdhFullSecretInputKdf PqxdhJointKdfGame
open RawCtxSelectedParentTable RawCtxSelectedParentEntry RawCtxSelectedMessageKey
open RawCtxSelectedAuthenticationObserver RawCtxSelectedSealReceipt RawCtxSelectedAcceptedRecord
open CtxRomAuth
variable {M P I D K : Type}

/-- The exact private send capability and result giving rise to a selected successful seal. An initial arbitrary receipt list is kept separate by consuming the actual before/after observer below. -/
noncomputable def Produced (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (parent : Option Entry) (target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (kernel : RawCtxSelectedMessageReveals.Kernel) (context : RawCtxSourceSend.SealContext)
    (result : Option (RawCtxSelectedMessageReveals.Kernel × Option RawCtxSourceSend.Encrypted))
    (entry : CtxSuccessfulSeal) : Prop :=
  ∃ pending, RawCtxInterpretedSend.normalBegin kernel context = .requested pending ∧
    let ready := RawCtxInterpretedSend.ready pending
      (RawCtxSelectedSendCompiler.deriveValue prior parent target nonce next pending.request)
    ∃ (actualNonce : NonceOutput) (width : ready.context.associatedData.length = 281) (record : CtxRomRecord),
      ready.material = .hidden actualNonce ∧
      entry = ⟨RawCtxSelectedMessageSealing.selectedInput actualNonce ready.sequence ready.context width, record⟩ ∧
      result = some (ready.advanced, (writer ⟨ready.sequence, ready.context.senderId, record.encode⟩).map
        (RawCtxInterpretedArguments.encrypted (RawCtxInterpretedArguments.sealArguments ready)))

/-- The complete actual send supplies the production capability; existing receipts retain their original prefix provenance. -/
theorem send_produced (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (parent : Option Entry) (target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (kernel : RawCtxSelectedMessageReveals.Kernel) (context : RawCtxSourceSend.SealContext)
    (before after : State) (result : Option (RawCtxSelectedMessageReveals.Kernel × Option RawCtxSourceSend.Encrypted))
    (supported : (result, after) ∈ support (monitor
      (RawCtxSelectedSendCompiler.send source writer prior parent target nonce next kernel context) before))
    (entry : CtxSuccessfulSeal) (found : entry ∈ after.seals) :
    entry ∈ before.seals ∨ Produced writer prior parent target nonce next kernel context result entry ∧
      after = {before with seals := entry :: before.seals} := by
  rcases send_provenance source writer prior parent target nonce next kernel context before after result supported entry found with earlier | produced
  · exact Or.inl earlier
  · obtain ⟨pending, started, value, width, record, hidden, same, returned, history⟩ := produced
    exact Or.inr ⟨⟨pending, started, value, width, record, hidden, same, returned⟩, history⟩

/-- The actual mixed-owner send gate attributes every new production to its original private kernel, authenticated AD, sender and target, retaining the exact owner publication. -/
theorem owner_send (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (parent : Option Entry) (target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (read : RawCtxReceive.FrameDecoder) (sender : Std.U64) (plaintext : Pqxdh.Bytes)
    (owner : RawCtxChainOwner.State RawCtxSelectedMessageReveals.Kernel P)
    (before after : State)
    (result : Option (Option RawCtxSourceSend.Encrypted × RawCtxChainOwner.State RawCtxSelectedMessageReveals.Kernel P))
    (supported : (result, after) ∈ support (monitor
      (RawCtxSelectedOwnerCompiler.owner source writer prior parent target nonce next read sender (.inl plaintext) owner) before))
    (entry : CtxSuccessfulSeal) (found : entry ∈ after.seals) :
    entry ∈ before.seals ∨ plaintext.isEmpty = false ∧
      ∃ sendResult, Produced writer prior parent target nonce next owner.kernel
        ⟨plaintext, owner.expectedSender, sender, owner.associatedData⟩ sendResult entry ∧
        result = sendResult.map (fun sent => (sent.2, {owner with kernel := sent.1})) ∧
        after = {before with seals := entry :: before.seals} := by
  rw [RawCtxSelectedOwnerCompiler.send_cases] at supported
  split at supported
  · simp only [monitor, simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at supported
    have unchanged : after = before := congrArg Prod.snd supported
    exact Or.inl (unchanged ▸ found)
  · rename_i nonempty
    simp only [monitor_map, support_map, Set.mem_image] at supported
    obtain ⟨actual, reached, equal⟩ := supported
    have state : actual.2 = after := congrArg Prod.snd equal
    have recorded : entry ∈ actual.2.seals := state.symm ▸ found
    rcases send_produced source writer prior parent target nonce next owner.kernel
      ⟨plaintext, owner.expectedSender, sender, owner.associatedData⟩ before actual.2 actual.1 reached entry recorded with earlier | produced
    · exact Or.inl earlier
    · exact Or.inr ⟨Bool.eq_false_iff.mpr nonempty, actual.1, produced.1,
        (congrArg Prod.fst equal).symm, state.symm.trans produced.2⟩

noncomputable def OwnerProduced (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (parent : Option Entry) (target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (sender : Std.U64) (plaintext : Pqxdh.Bytes)
    (owner : RawCtxChainOwner.State RawCtxSelectedMessageReveals.Kernel P)
    (result : Option (Option RawCtxSourceSend.Encrypted × RawCtxChainOwner.State RawCtxSelectedMessageReveals.Kernel P))
    (entry : CtxSuccessfulSeal) : Prop :=
  plaintext.isEmpty = false ∧ ∃ sendResult,
    Produced writer prior parent target nonce next owner.kernel
      ⟨plaintext, owner.expectedSender, sender, owner.associatedData⟩ sendResult entry ∧
    result = sendResult.map (fun sent => (sent.2, {owner with kernel := sent.1}))

noncomputable def BeaconProduced (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (parent : Option Entry) (target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (plaintext : Pqxdh.Bytes) (beacon : RawCtxGenericRoleStorage.BeaconState RawCtxSelectedMessageReveals.Kernel I D K)
    (result : Option (Option RawCtxSourceSend.Encrypted × RawCtxGenericRoleStorage.BeaconState RawCtxSelectedMessageReveals.Kernel I D K))
    (entry : CtxSuccessfulSeal) : Prop :=
  match beacon.beacon.phase with
  | .established control ad kernel => ∃ owned,
      OwnerProduced writer prior parent target nonce next beacon.beacon.identityKeyId plaintext
        (RawCtxGenericBeacon.selected beacon control ad kernel) owned entry ∧
      result = owned.map (fun reply => (reply.1, RawCtxGenericBeacon.reinstall beacon control ad reply.2))
  | _ => False

/-- A new Beacon production comes from its actual established owner and exact reinstallation; inactive phases cannot manufacture a sealing receipt. -/
theorem beacon_send (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (parent : Option Entry) (target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (read : RawCtxReceive.FrameDecoder) (plaintext : Pqxdh.Bytes)
    (beacon : RawCtxGenericRoleStorage.BeaconState RawCtxSelectedMessageReveals.Kernel I D K)
    (before after : State)
    (result : Option (Option RawCtxSourceSend.Encrypted × RawCtxGenericRoleStorage.BeaconState RawCtxSelectedMessageReveals.Kernel I D K))
    (supported : (result, after) ∈ support (monitor
      (RawCtxSelectedRoleCompiler.beacon source writer prior parent target nonce next read (.inl plaintext) beacon) before))
    (entry : CtxSuccessfulSeal) (found : entry ∈ after.seals) :
    entry ∈ before.seals ∨ BeaconProduced writer prior parent target nonce next plaintext beacon result entry ∧
      after = {before with seals := entry :: before.seals} := by
  rw [RawCtxSelectedRoleCompiler.beacon_cases] at supported
  cases phase : beacon.beacon.phase
  case established control ad kernel =>
    simp only [phase, monitor_map, support_map, Set.mem_image] at supported
    obtain ⟨actual, reached, equal⟩ := supported
    have state : actual.2 = after := congrArg Prod.snd equal
    have recorded : entry ∈ actual.2.seals := state.symm ▸ found
    rcases owner_send source writer prior parent target nonce next read beacon.beacon.identityKeyId plaintext
      (RawCtxGenericBeacon.selected beacon control ad kernel) before actual.2 actual.1 reached entry recorded with earlier | produced
    · exact Or.inl earlier
    · obtain ⟨nonempty, sent, produced, published, history⟩ := produced
      refine Or.inr ⟨?_, state.symm.trans history⟩
      simp only [BeaconProduced, phase]
      exact ⟨actual.1, ⟨nonempty, sent, produced, published⟩, (congrArg Prod.fst equal).symm⟩
  all_goals simp only [phase, monitor, simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at supported
  all_goals have unchanged : after = before := congrArg Prod.snd supported
  all_goals exact Or.inl (unchanged ▸ found)

noncomputable def ServerProduced (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (parent : Option Entry) (target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (sender : M → Std.U64) (plaintext : Pqxdh.Bytes) (kid : Std.U64)
    (server : RawCtxGenericRoleStorage.ServerState RawCtxSelectedMessageReveals.Kernel M P)
    (result : Option (Option RawCtxSourceSend.Encrypted × RawCtxGenericRoleStorage.ServerState RawCtxSelectedMessageReveals.Kernel M P))
    (entry : CtxSuccessfulSeal) : Prop :=
  match RawCtxGenericServer.peerAssociatedData server.server kid with
  | none => False
  | some ad => match server.server.peers kid with
    | none => False
    | some peer => ∃ owned,
        OwnerProduced writer prior parent target nonce next (sender server.server.metadata) plaintext
          (RawCtxGenericServer.selectedOwner kid ad peer server.rawAttempts) owned entry ∧
        result = owned.map (fun reply =>
          (reply.1, ⟨RawCtxGenericServer.putPeer server.server kid peer reply.2.kernel, reply.2.rawAttempts⟩))

/-- A new Server production follows the actual AD and peer lookups, preserves the metadata-derived sender and republishes precisely that peer. The requested target ID is not equated with any registration assignment. -/
theorem server_send (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (parent : Option Entry) (target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (read : RawCtxReceive.FrameDecoder)
    (plaintext : Pqxdh.Bytes) (kid : Std.U64)
    (server : RawCtxGenericRoleStorage.ServerState RawCtxSelectedMessageReveals.Kernel M P)
    (before after : State)
    (result : Option (Option RawCtxSourceSend.Encrypted × RawCtxGenericRoleStorage.ServerState RawCtxSelectedMessageReveals.Kernel M P))
    (supported : (result, after) ∈ support (monitor
      (RawCtxSelectedRoleCompiler.server source writer prior parent target nonce next sender route read (.inl (plaintext, kid)) server) before))
    (entry : CtxSuccessfulSeal) (found : entry ∈ after.seals) :
    entry ∈ before.seals ∨ ServerProduced writer prior parent target nonce next sender plaintext kid server result entry ∧
      after = {before with seals := entry :: before.seals} := by
  rw [RawCtxSelectedRoleCompiler.server_send_cases] at supported
  cases adFound : RawCtxGenericServer.peerAssociatedData server.server kid with
  | none =>
    simp only [adFound, monitor, simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at supported
    have unchanged : after = before := congrArg Prod.snd supported
    exact Or.inl (unchanged ▸ found)
  | some ad =>
    cases peerFound : server.server.peers kid with
    | none =>
      simp only [adFound, peerFound, monitor, simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at supported
      have unchanged : after = before := congrArg Prod.snd supported
      exact Or.inl (unchanged ▸ found)
    | some peer =>
      simp only [adFound, peerFound, monitor_map, support_map, Set.mem_image] at supported
      obtain ⟨actual, reached, equal⟩ := supported
      have state : actual.2 = after := congrArg Prod.snd equal
      have recorded : entry ∈ actual.2.seals := state.symm ▸ found
      rcases owner_send source writer prior parent target nonce next read (sender server.server.metadata) plaintext
        (RawCtxGenericServer.selectedOwner kid ad peer server.rawAttempts) before actual.2 actual.1 reached entry recorded with earlier | produced
      · exact Or.inl earlier
      · obtain ⟨nonempty, sent, produced, published, history⟩ := produced
        refine Or.inr ⟨?_, state.symm.trans history⟩
        simp only [ServerProduced, adFound, peerFound]
        exact ⟨actual.1, ⟨nonempty, sent, produced, published⟩, (congrArg Prod.fst equal).symm⟩

/-- The actual complete cached/future receive never issues a selected sealing call, regardless of parser context, stale material or its actual optional opening reply. -/
theorem receive_no_seals (prior : Prior) (parent : Option Entry) (target : RootOutput)
    (nonce : NonceOutput) (next : RootOutput) (read : RawCtxReceive.FrameDecoder) (expected : Std.U64)
    (kernel : RawCtxSelectedMessageReveals.Kernel) (sequence : Std.U64) (context : RawCtxWholeOwner.OpenContext) :
    (RawCtxSelectedReceiveCompiler.receive prior parent target nonce next read expected kernel sequence context).IsQueryBoundP
      (AdaptiveCtxDynamicKnownBounds.TargetClass AdaptiveCtxQueryBounds.SourceSeal) 0 := by
  simp only [RawCtxSelectedReceiveCompiler.receive, RawCtxSelectedMessageDriver.receive,
    ← QueryImpl.simulateQ_compose, RawCtxInterpretedReceive.receive]
  change (simulateQ (RawCtxSelectedReceiveCompiler.compiler prior parent target nonce next read expected)
    (RawCtxInterpretedReceive.program (Plaintext := RawCtxWholeOwner.Decrypted)
      (RawCtxInterpretedReceive.normalBegin kernel sequence context))).IsQueryBoundP _ 0
  rw [RawCtxSelectedReceiveReceipt.program_terminal]
  cases RawCtxSelectedReceiveReceipt.terminal prior parent target nonce next
      (RawCtxInterpretedReceive.normalBegin kernel sequence context) with
  | rejected final => trivial
  | opening pending =>
    simpa only [isQueryBoundP_map_iff] using (RawCtxSelectedOpenConsumer.service_other 0 read expected pending).1

/-- Every actual raw owner path, including all malformed-input and validation rejection paths, preserves the selected seal prefix. Its verification attempts remain separately counted. -/
theorem raw_no_seals (prior : Prior) (parent : Option Entry) (target : RootOutput)
    (nonce : NonceOutput) (next : RootOutput) (read : RawCtxReceive.FrameDecoder) (bytes : Pqxdh.Bytes)
    (owner : RawCtxChainOwner.State RawCtxSelectedMessageReveals.Kernel P) :
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
        exact receive_no_seals prior parent target nonce next read _ owner.kernel _ _
      · trivial

/-- The actual mixed owner's raw dispatcher introduces no selected seal. -/
theorem owner_raw_no_seals (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (parent : Option Entry) (target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (read : RawCtxReceive.FrameDecoder) (sender : Std.U64) (bytes : Pqxdh.Bytes)
    (owner : RawCtxChainOwner.State RawCtxSelectedMessageReveals.Kernel P) :
    (RawCtxSelectedOwnerCompiler.owner source writer prior parent target nonce next read sender (.inr bytes) owner).IsQueryBoundP
      (AdaptiveCtxDynamicKnownBounds.TargetClass AdaptiveCtxQueryBounds.SourceSeal) 0 := by
  rw [RawCtxSelectedOwnerCompiler.raw_cases, isQueryBoundP_map_iff]
  exact raw_no_seals prior parent target nonce next read bytes owner

/-- The actual Beacon raw dispatcher retains all prior sealing receipts even for inactive phases and rejected inputs. -/
theorem beacon_raw_no_seals (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (parent : Option Entry) (target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (read : RawCtxReceive.FrameDecoder) (bytes : Pqxdh.Bytes)
    (beacon : RawCtxGenericRoleStorage.BeaconState RawCtxSelectedMessageReveals.Kernel I D K) :
    (RawCtxSelectedRoleCompiler.beacon source writer prior parent target nonce next read (.inr bytes) beacon).IsQueryBoundP
      (AdaptiveCtxDynamicKnownBounds.TargetClass AdaptiveCtxQueryBounds.SourceSeal) 0 := by
  rw [RawCtxSelectedRoleCompiler.beacon_cases]
  cases beacon.beacon.phase
  case established control ad kernel =>
    simpa only [isQueryBoundP_map_iff] using owner_raw_no_seals source writer prior parent target nonce next read
      beacon.beacon.identityKeyId bytes (RawCtxGenericBeacon.selected beacon control ad kernel)
  all_goals trivial

/-- Header routing, both actual Server lookups and all raw receive callbacks add no selected seal. This does not discard known-key verification or public hash costs. -/
theorem server_raw_no_seals (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (parent : Option Entry) (target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (read : RawCtxReceive.FrameDecoder)
    (bytes : Pqxdh.Bytes) (server : RawCtxGenericRoleStorage.ServerState RawCtxSelectedMessageReveals.Kernel M P) :
    (RawCtxSelectedRoleCompiler.server source writer prior parent target nonce next sender route read (.inr bytes) server).IsQueryBoundP
      (AdaptiveCtxDynamicKnownBounds.TargetClass AdaptiveCtxQueryBounds.SourceSeal) 0 := by
  rw [RawCtxSelectedRoleCompiler.server_raw_cases]
  split
  · trivial
  · split
    · trivial
    · split
      · trivial
      · simpa only [isQueryBoundP_map_iff] using owner_raw_no_seals source writer prior parent target nonce next read
          (sender server.server.metadata) bytes _

abbrev Roles (M P I D K : Type) (S B : Nat) :=
  RawCtxGenericRoleFamily.Roles RawCtxSelectedMessageReveals.Kernel M P I D K S B

noncomputable def FamilyProduced {S B : Nat} (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (parent : Option Entry) (target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (sender : M → Std.U64) (query : (RawCtxProtocolRoles.SourceSpec S B).Domain)
    (roles : Roles M P I D K S B)
    (result : Option ((RawCtxProtocolRoles.SourceSpec S B).Range query × Roles M P I D K S B))
    (entry : CtxSuccessfulSeal) : Prop :=
  match query with
  | .inl ⟨index, .inl (plaintext, kid)⟩ => ∃ actual,
      ServerProduced writer prior parent target nonce next sender plaintext kid (roles.1 index) actual entry ∧
      result = actual.map (fun reply => (reply.1, (Function.update roles.1 index reply.2, roles.2)))
  | .inr (.inl ⟨index, .inl plaintext⟩) => ∃ actual,
      BeaconProduced writer prior parent target nonce next plaintext (roles.2 index) actual entry ∧
      result = actual.map (fun reply => (reply.1, (roles.1, Function.update roles.2 index reply.2)))
  | _ => False

/-- Every new successful selected seal in one original family request has the exact indexed Server or Beacon send origin and full indexed publication. All other roles and prior receipts remain unchanged. -/
theorem family_produced {S B : Nat} (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (parent : Option Entry) (target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (read : RawCtxReceive.FrameDecoder)
    (query : (RawCtxProtocolRoles.SourceSpec S B).Domain) (roles : Roles M P I D K S B)
    (before after : State) (result : Option ((RawCtxProtocolRoles.SourceSpec S B).Range query × Roles M P I D K S B))
    (supported : (result, after) ∈ support (monitor
      (RawCtxSelectedFamilyCompiler.family source writer prior parent target nonce next sender route read query roles) before))
    (entry : CtxSuccessfulSeal) (found : entry ∈ after.seals) :
    entry ∈ before.seals ∨ FamilyProduced writer prior parent target nonce next sender query roles result entry ∧
      after = {before with seals := entry :: before.seals} := by
  rw [RawCtxSelectedFamilyCompiler.family_cases] at supported
  rcases query with ⟨index, (⟨plaintext, kid⟩ | raw)⟩ | (⟨index, (plaintext | raw)⟩ | publicQuery)
  case inl.inl =>
    simp only [monitor_map, support_map, Set.mem_image] at supported
    obtain ⟨actual, reached, equal⟩ := supported
    have state : actual.2 = after := congrArg Prod.snd equal
    have recorded : entry ∈ actual.2.seals := state.symm ▸ found
    rcases server_send source writer prior parent target nonce next sender route read plaintext kid
      (roles.1 index) before actual.2 actual.1 reached entry recorded with earlier | produced
    · exact Or.inl earlier
    · exact Or.inr ⟨⟨actual.1, produced.1, (congrArg Prod.fst equal).symm⟩, state.symm.trans produced.2⟩
  case inr.inl.inl =>
    simp only [monitor_map, support_map, Set.mem_image] at supported
    obtain ⟨actual, reached, equal⟩ := supported
    have state : actual.2 = after := congrArg Prod.snd equal
    have recorded : entry ∈ actual.2.seals := state.symm ▸ found
    rcases beacon_send source writer prior parent target nonce next read plaintext
      (roles.2 index) before actual.2 actual.1 reached entry recorded with earlier | produced
    · exact Or.inl earlier
    · exact Or.inr ⟨⟨actual.1, produced.1, (congrArg Prod.fst equal).symm⟩, state.symm.trans produced.2⟩
  case inl.inr =>
    have unchanged : after.seals = before.seals := by
      apply monitor_seals _ _ before (result, after) supported
      simpa only [isQueryBoundP_map_iff] using server_raw_no_seals source writer prior parent target nonce next sender route read raw (roles.1 index)
    exact Or.inl (unchanged ▸ found)
  case inr.inl.inr =>
    have unchanged : after.seals = before.seals := by
      apply monitor_seals _ _ before (result, after) supported
      simpa only [isQueryBoundP_map_iff] using beacon_raw_no_seals source writer prior parent target nonce next read raw (roles.2 index)
    exact Or.inl (unchanged ▸ found)
  case inr.inr =>
    have unchanged : after.seals = before.seals := by
      apply monitor_seals _ _ before (result, after) supported
      simp only [isQueryBoundP_map_iff]
      rcases publicQuery with coin | (hash | request)
      all_goals simp [RawCtxSelectedFamilyCompiler.publicWork,
        AdaptiveCtxDynamicKnownBounds.TargetClass, AdaptiveCtxQueryBounds.SourceSeal]
    exact Or.inl (unchanged ▸ found)

end BeaconcryptCore.Computational.RawCtxSelectedProductionOrigins

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedProductionOrigins.send_produced' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedProductionOrigins.send_produced
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedProductionOrigins.owner_send' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedProductionOrigins.owner_send
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedProductionOrigins.beacon_send' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedProductionOrigins.beacon_send
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedProductionOrigins.server_send' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedProductionOrigins.server_send
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedProductionOrigins.receive_no_seals' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedProductionOrigins.receive_no_seals
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedProductionOrigins.raw_no_seals' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedProductionOrigins.raw_no_seals
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedProductionOrigins.owner_raw_no_seals' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedProductionOrigins.owner_raw_no_seals
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedProductionOrigins.beacon_raw_no_seals' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedProductionOrigins.beacon_raw_no_seals
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedProductionOrigins.server_raw_no_seals' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedProductionOrigins.server_raw_no_seals
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedProductionOrigins.family_produced' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedProductionOrigins.family_produced
