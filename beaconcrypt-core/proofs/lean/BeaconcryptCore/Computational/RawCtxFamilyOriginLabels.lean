import BeaconcryptCore.Computational.RawCtxGenericFamilyLive

/-!
Established family record operations preserve the origin label attached to each original owner. The proof retains actual optional replies, source routing and all shared state; it is an invariant of the original no-install record interface. Initial installation is a separate source constructor obligation.
-/
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.refined ratchet.concrete
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RawCtxFamilyOriginLabels
variable {Kernel Label State M P I D K Result : Type} {S B : Nat}

/-- Original owner raw validation and publication retain the same kernel label on every supported reply. -/
theorem raw (label : Kernel → Label) (calls : RawCtxChainOwner.Calls Kernel (StateT State ProbComp))
    (preserved : ∀ entry target context state result,
      result ∈ support ((calls.receive entry target context).run state) → label result.1.1 = label entry)
    (decode : RawCtxReceive.FrameDecoder) (bytes : Pqxdh.Bytes) (entry : RawCtxChainOwner.State Kernel M)
    (state : State) (result : (core.option.Option RawCtxWholeOwner.Decrypted × RawCtxChainOwner.State Kernel M) × State)
    (supported : result ∈ support (((RawCtxChainOwner.rawReceive calls decode bytes).run entry).run state)) :
    label result.1.2.kernel = label entry.kernel := by
  unfold RawCtxChainOwner.rawReceive at supported
  simp only [StateT.run] at supported
  split at supported
  · change result ∈ support (pure (RawCtxChainOwner.publish entry (entry.kernel, .None), state)) at supported
    simp only [mem_support_pure_iff] at supported
    subst result
    rfl
  · cases decoded : decode bytes with
    | none =>
      simp only [decoded] at supported
      change result ∈ support (pure (RawCtxChainOwner.publish entry (entry.kernel, .None), state)) at supported
      simp only [mem_support_pure_iff] at supported
      subst result
      rfl
    | some frame =>
      simp only [decoded] at supported
      split at supported
      · simp only [bind_pure_comp] at supported
        change result ∈ support ((fun reply => (RawCtxChainOwner.publish entry reply.1, reply.2)) <$>
          (calls.receive entry.kernel frame.sequence ⟨bytes, frame, entry.associatedData⟩).run state) at supported
        rw [support_map] at supported
        obtain ⟨reply, reached, rfl⟩ := supported
        exact preserved _ _ _ _ reply reached
      · change result ∈ support (pure (RawCtxChainOwner.publish entry (entry.kernel, .None), state)) at supported
        simp only [mem_support_pure_iff] at supported
        subst result
        rfl

/-- Source send rejection and advanced optional publication preserve the callback's original kernel label. -/
theorem send (label : Kernel → Label) (calls : RawCtxChainOwner.Calls Kernel (StateT State ProbComp))
    (preserved : ∀ entry context state result,
      result ∈ support ((calls.send entry context).run state) → label result.1.1 = label entry)
    (sender : Std.U64) (plaintext : Pqxdh.Bytes) (entry : RawCtxChainOwner.State Kernel M)
    (state : State) (result : (Option RawCtxSourceSend.Encrypted × RawCtxChainOwner.State Kernel M) × State)
    (supported : result ∈ support (((RawCtxChainOwner.sendOwner calls sender plaintext).run entry).run state)) :
    label result.1.2.kernel = label entry.kernel := by
  unfold RawCtxChainOwner.sendOwner at supported
  simp only [StateT.run] at supported
  split at supported
  · change result ∈ support (pure ((none, entry), state)) at supported
    simp only [mem_support_pure_iff] at supported
    subst result
    rfl
  · simp only [bind_pure_comp] at supported
    change result ∈ support ((fun reply => ((reply.1.2, {entry with kernel := reply.1.1}), reply.2)) <$>
      (calls.send entry.kernel ⟨plaintext, entry.expectedSender, sender, entry.associatedData⟩).run state) at supported
    rw [support_map] at supported
    obtain ⟨reply, reached, rfl⟩ := supported
    exact preserved _ _ _ reply reached

/-- The original mixed owner API preserves its kernel label on every supported complete reply. -/
theorem owner (label : Kernel → Label) (calls : RawCtxChainOwner.Calls Kernel (StateT State ProbComp))
    (receivePreserved : ∀ entry target context state result,
      result ∈ support ((calls.receive entry target context).run state) → label result.1.1 = label entry)
    (sendPreserved : ∀ entry context state result,
      result ∈ support ((calls.send entry context).run state) → label result.1.1 = label entry)
    (sender : Std.U64) (decode : RawCtxReceive.FrameDecoder) (query : RawCtxMixedOwner.SourceSpec.Domain)
    (entry : RawCtxChainOwner.State Kernel M) (state : State)
    (result : (RawCtxMixedOwner.SourceSpec.Range query × RawCtxChainOwner.State Kernel M) × State)
    (supported : result ∈ support (((RawCtxChainOwner.ownerImpl calls sender decode query).run entry).run state)) :
    label result.1.2.kernel = label entry.kernel := by
  cases query with
  | inl plaintext => exact send label calls sendPreserved sender plaintext entry state result supported
  | inr bytes => exact raw label calls receivePreserved decode bytes entry state result supported

def serverLabel (label : Kernel → Label) (peer : Std.U64)
    (state : RawCtxGenericRoleStorage.ServerState Kernel M P) : Option Label :=
  (state.server.peers peer).map (fun value => label value.kernel)

private theorem put_label (label : Kernel → Label)
    (entry : RawCtxGenericRoleStorage.ServerState Kernel M P) (selected peer : Std.U64)
    (before : RawCtxGenericRoleStorage.Peer Kernel P) (after : Kernel) (attempts : Nat)
    (found : entry.server.peers selected = some before) (preserved : label after = label before.kernel) :
    serverLabel label peer ⟨RawCtxGenericServer.putPeer entry.server selected before after, attempts⟩ =
      serverLabel label peer entry := by
  by_cases same : peer = selected
  · subst peer
    simp only [serverLabel, RawCtxGenericServer.putPeer, Function.update_self, found, Option.map_some, preserved]
  · simp only [serverLabel, RawCtxGenericServer.putPeer, Function.update_of_ne same]

/-- Original Server routing and raw publication preserve every selected peer label, including rejected and absent-peer paths. -/
theorem server_raw (label : Kernel → Label) (calls : RawCtxChainOwner.Calls Kernel (StateT State ProbComp))
    (preserved : ∀ entry target context state result,
      result ∈ support ((calls.receive entry target context).run state) → label result.1.1 = label entry)
    (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder) (bytes : Pqxdh.Bytes)
    (entry : RawCtxGenericRoleStorage.ServerState Kernel M P) (state : State)
    (result : (core.option.Option RawCtxWholeOwner.Decrypted × RawCtxGenericRoleStorage.ServerState Kernel M P) × State)
    (supported : result ∈ support ((RawCtxGenericServer.rawServer calls route decode bytes entry).run state))
    (peer : Std.U64) : serverLabel label peer result.1.2 = serverLabel label peer entry := by
  unfold RawCtxGenericServer.rawServer at supported
  cases routed : route bytes with
  | none =>
      simp only [routed] at supported
      change result ∈ support (pure ((.None, {entry with rawAttempts := entry.rawAttempts + 1}), state)) at supported
      simp only [mem_support_pure_iff] at supported
      subst result
      rfl
  | some selected =>
      simp only [routed] at supported
      cases associated : RawCtxGenericServer.peerAssociatedData entry.server selected with
      | none =>
          simp only [associated] at supported
          change result ∈ support (pure ((.None, {entry with rawAttempts := entry.rawAttempts + 1}), state)) at supported
          simp only [mem_support_pure_iff] at supported
          subst result
          rfl
      | some ad =>
          simp only [associated] at supported
          cases found : entry.server.peers selected with
          | none =>
              simp only [found] at supported
              change result ∈ support (pure ((.None, {entry with rawAttempts := entry.rawAttempts + 1}), state)) at supported
              simp only [mem_support_pure_iff] at supported
              subst result
              rfl
          | some original =>
              simp only [found, bind_pure_comp, StateT.run_map, support_map] at supported
              obtain ⟨reply, reached, rfl⟩ := supported
              apply put_label label entry selected peer original reply.1.2.kernel reply.1.2.rawAttempts found
              exact raw label calls preserved decode bytes (RawCtxGenericServer.selectedOwner selected ad original entry.rawAttempts) state reply reached

/-- Original Server sends preserve every peer label after empty-input rejection or complete optional sealing and publication. -/
theorem server_send (label : Kernel → Label) (calls : RawCtxChainOwner.Calls Kernel (StateT State ProbComp))
    (preserved : ∀ entry context state result,
      result ∈ support ((calls.send entry context).run state) → label result.1.1 = label entry)
    (sender : M → Std.U64) (plaintext : Pqxdh.Bytes) (selected : Std.U64)
    (entry : RawCtxGenericRoleStorage.ServerState Kernel M P) (state : State)
    (result : (Option RawCtxSourceSend.Encrypted × RawCtxGenericRoleStorage.ServerState Kernel M P) × State)
    (supported : result ∈ support ((RawCtxGenericServer.sendServer calls sender plaintext selected entry).run state))
    (peer : Std.U64) : serverLabel label peer result.1.2 = serverLabel label peer entry := by
  unfold RawCtxGenericServer.sendServer at supported
  cases associated : RawCtxGenericServer.peerAssociatedData entry.server selected with
  | none =>
      simp only [associated] at supported
      change result ∈ support (pure ((none, entry), state)) at supported
      simp only [mem_support_pure_iff] at supported
      subst result
      rfl
  | some ad =>
      simp only [associated] at supported
      cases found : entry.server.peers selected with
      | none =>
          simp only [found] at supported
          change result ∈ support (pure ((none, entry), state)) at supported
          simp only [mem_support_pure_iff] at supported
          subst result
          rfl
      | some original =>
          simp only [found, bind_pure_comp, StateT.run_map, support_map] at supported
          obtain ⟨reply, reached, rfl⟩ := supported
          apply put_label label entry selected peer original reply.1.2.kernel reply.1.2.rawAttempts found
          exact send label calls preserved (sender entry.server.metadata) plaintext
            (RawCtxGenericServer.selectedOwner selected ad original entry.rawAttempts) state reply reached

/-- Every original Server request retains all peer labels on the full supported reply and shared state. -/
theorem server (label : Kernel → Label) (calls : RawCtxChainOwner.Calls Kernel (StateT State ProbComp))
    (receivePreserved : ∀ entry target context state result,
      result ∈ support ((calls.receive entry target context).run state) → label result.1.1 = label entry)
    (sendPreserved : ∀ entry context state result,
      result ∈ support ((calls.send entry context).run state) → label result.1.1 = label entry)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (query : RawCtxServerMixed.SourceSpec.Domain) (entry : RawCtxGenericRoleStorage.ServerState Kernel M P) (state : State)
    (result : (RawCtxServerMixed.SourceSpec.Range query × RawCtxGenericRoleStorage.ServerState Kernel M P) × State)
    (supported : result ∈ support (((RawCtxGenericServer.serverImpl calls sender route decode query).run entry).run state))
    (peer : Std.U64) : serverLabel label peer result.1.2 = serverLabel label peer entry := by
  cases query with
  | inl request => exact server_send label calls sendPreserved sender request.1 request.2 entry state result supported peer
  | inr bytes => exact server_raw label calls receivePreserved route decode bytes entry state result supported peer

def beaconLabel (label : Kernel → Label) (entry : RawCtxGenericRoleStorage.BeaconState Kernel I D K) : Option Label :=
  match entry.beacon.phase with
  | .established _ _ kernel => some (label kernel)
  | _ => none

/-- Established Beacon operations preserve the installed label, and every inactive phase remains without an installed owner. -/
theorem beacon (label : Kernel → Label) (calls : RawCtxChainOwner.Calls Kernel (StateT State ProbComp))
    (receivePreserved : ∀ entry target context state result,
      result ∈ support ((calls.receive entry target context).run state) → label result.1.1 = label entry)
    (sendPreserved : ∀ entry context state result,
      result ∈ support ((calls.send entry context).run state) → label result.1.1 = label entry)
    (decode : RawCtxReceive.FrameDecoder) (query : RawCtxMixedOwner.SourceSpec.Domain)
    (entry : RawCtxGenericRoleStorage.BeaconState Kernel I D K) (state : State)
    (result : (RawCtxMixedOwner.SourceSpec.Range query × RawCtxGenericRoleStorage.BeaconState Kernel I D K) × State)
    (supported : result ∈ support (((RawCtxGenericBeacon.impl calls decode query).run entry).run state)) :
    beaconLabel label result.1.2 = beaconLabel label entry := by
  cases phase : entry.beacon.phase
  case established control ad kernel =>
    simp only [RawCtxGenericBeacon.impl, StateT.run, phase, bind_pure_comp] at supported
    change result ∈ support ((fun reply => ((reply.1.1, RawCtxGenericBeacon.reinstall entry control ad reply.1.2), reply.2)) <$>
      ((RawCtxChainOwner.ownerImpl calls entry.beacon.identityKeyId decode query).run
        (RawCtxGenericBeacon.selected entry control ad kernel)).run state) at supported
    rw [support_map] at supported
    obtain ⟨reply, reached, rfl⟩ := supported
    simp only [beaconLabel, RawCtxGenericBeacon.reinstall, phase]
    exact congrArg some (owner label calls receivePreserved sendPreserved entry.beacon.identityKeyId decode query
      (RawCtxGenericBeacon.selected entry control ad kernel) state reply reached)
  all_goals
    cases query <;> simp only [RawCtxGenericBeacon.impl, StateT.run, phase, RawCtxGenericBeacon.rejected] at supported
    all_goals
      change result ∈ support (pure _) at supported
      simp only [mem_support_pure_iff] at supported
      subst result
      rfl

def familyLabel (label : Kernel → Label) (selected : RawCtxProtocolReveals.Owner S B)
    (entry : RawCtxGenericRoleFamily.Roles Kernel M P I D K S B) : Option Label :=
  (RawCtxGenericRoleFamily.selectedKernel selected entry).map label

private theorem family_beacon (label : Kernel → Label) (index : Fin B)
    (entry : RawCtxGenericRoleFamily.Roles Kernel M P I D K S B) :
    familyLabel label (.beacon index) entry = beaconLabel label (entry.2 index) := by
  cases phase : (entry.2 index).beacon.phase <;> simp only [familyLabel, RawCtxGenericRoleFamily.selectedKernel, beaconLabel, phase,
    Option.map_none, Option.map_some]

/-- Every original finite-family request preserves the label of every owner at its original index, through all shared effects and optional replies. -/
theorem family (label : Kernel → Label) (calls : RawCtxChainOwner.Calls Kernel (StateT State ProbComp))
    (receivePreserved : ∀ entry target context state result,
      result ∈ support ((calls.receive entry target context).run state) → label result.1.1 = label entry)
    (sendPreserved : ∀ entry context state result,
      result ∈ support ((calls.send entry context).run state) → label result.1.1 = label entry)
    (publicCalls : QueryImpl RawCtxServerServices.PublicSpec (StateT State ProbComp))
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (query : (RawCtxProtocolRoles.SourceSpec S B).Domain)
    (entry : RawCtxGenericRoleFamily.Roles Kernel M P I D K S B) (state : State)
    (result : ((RawCtxProtocolRoles.SourceSpec S B).Range query × RawCtxGenericRoleFamily.Roles Kernel M P I D K S B) × State)
    (supported : result ∈ support (((RawCtxGenericFamilyFrontend.impl calls publicCalls sender route decode query).run entry).run state))
    (selected : RawCtxProtocolReveals.Owner S B) : familyLabel label selected result.1.2 = familyLabel label selected entry := by
  rcases query with ⟨index, request⟩ | (⟨index, request⟩ | request)
  case inl =>
    simp only [RawCtxGenericFamilyFrontend.impl, StateT.run, bind_pure_comp] at supported
    change result ∈ support ((fun reply => ((reply.1.1, (Function.update entry.1 index reply.1.2, entry.2)), reply.2)) <$>
      ((RawCtxGenericServer.serverImpl calls sender route decode request).run (entry.1 index)).run state) at supported
    rw [support_map] at supported
    obtain ⟨reply, reached, rfl⟩ := supported
    cases selected with
    | server selected peer =>
        by_cases same : selected = index
        · subst selected
          simpa only [familyLabel, RawCtxGenericRoleFamily.selectedKernel, Function.update_self, Option.map_map, serverLabel,
            Function.comp_def] using server label calls receivePreserved sendPreserved sender route decode request (entry.1 index) state reply reached peer
        · simp only [familyLabel, RawCtxGenericRoleFamily.selectedKernel, Function.update_of_ne same]
    | beacon _ => rfl
  case inr.inl =>
    simp only [RawCtxGenericFamilyFrontend.impl, StateT.run, bind_pure_comp] at supported
    change result ∈ support ((fun reply => ((reply.1.1, (entry.1, Function.update entry.2 index reply.1.2)), reply.2)) <$>
      ((RawCtxGenericBeacon.impl calls decode request).run (entry.2 index)).run state) at supported
    rw [support_map] at supported
    obtain ⟨reply, reached, rfl⟩ := supported
    cases selected with
    | server _ _ => rfl
    | beacon selected =>
        by_cases same : selected = index
        · subst selected
          simp only [family_beacon, Function.update_self]
          exact beacon label calls receivePreserved sendPreserved decode request (entry.2 index) state reply reached
        · simp only [familyLabel, RawCtxGenericRoleFamily.selectedKernel, Function.update_of_ne same]
  case inr.inr =>
    simp only [RawCtxGenericFamilyFrontend.impl, StateT.run, bind_pure_comp] at supported
    change result ∈ support ((fun reply => ((reply.1, entry), reply.2)) <$> (publicCalls request).run state) at supported
    rw [support_map] at supported
    obtain ⟨reply, reached, rfl⟩ := supported
    rfl

/-- Original LIVE reads append the actual optional reply and history position without replacing any installed origin; non-read source effects preserve all owner labels. -/
theorem live (label : Kernel → Label) (calls : RawCtxChainOwner.Calls Kernel (StateT State ProbComp))
    (receivePreserved : ∀ entry target context state result,
      result ∈ support ((calls.receive entry target context).run state) → label result.1.1 = label entry)
    (sendPreserved : ∀ entry context state result,
      result ∈ support ((calls.send entry context).run state) → label result.1.1 = label entry)
    (publicCalls : QueryImpl RawCtxServerServices.PublicSpec (StateT State ProbComp))
    (reader : QueryImpl (RawCtxGenericFamilyRead.ReadSpec Kernel S B) (StateT State ProbComp))
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (query : (RawCtxProtocolReveals.SourceSpec S B).Domain)
    (entry : RawCtxGenericFamilyLive.State Kernel M P I D K S B) (state : State)
    (result : ((RawCtxProtocolReveals.SourceSpec S B).Range query × RawCtxGenericFamilyLive.State Kernel M P I D K S B) × State)
    (supported : result ∈ support (((RawCtxGenericFamilyLive.impl calls publicCalls reader sender route decode query).run entry).run state))
    (selected : RawCtxProtocolReveals.Owner S B) : familyLabel label selected result.1.2.1 = familyLabel label selected entry.1 := by
  cases query with
  | inl request =>
      simp only [RawCtxGenericFamilyLive.impl, StateT.run, bind_pure_comp] at supported
      change result ∈ support ((fun reply => ((reply.1.1, (reply.1.2, RawCtxProtocolReveals.tick entry.2)), reply.2)) <$>
        ((RawCtxGenericFamilyFrontend.impl calls publicCalls sender route decode request).run entry.1).run state) at supported
      rw [support_map] at supported
      obtain ⟨reply, reached, rfl⟩ := supported
      exact family label calls receivePreserved sendPreserved publicCalls sender route decode request entry.1 state reply reached selected
  | inr request =>
      simp only [RawCtxGenericFamilyLive.impl, StateT.run, bind_pure_comp] at supported
      change result ∈ support ((fun reply => ((reply.1, (entry.1, RawCtxProtocolReveals.note ⟨request, reply.1⟩ entry.2)), reply.2)) <$>
        (reader (request, RawCtxGenericRoleFamily.selectedKernel (RawCtxGenericFamilyRead.requestOwner request) entry.1)).run state) at supported
      rw [support_map] at supported
      obtain ⟨reply, reached, rfl⟩ := supported
      rfl

/-- Every supported complete adaptive original LIVE schedule preserves the selected owner's label from its actual initial installed state, retaining the entire final reply, family, history and shared state. -/
theorem schedule (label : Kernel → Label) (calls : RawCtxChainOwner.Calls Kernel (StateT State ProbComp))
    (receivePreserved : ∀ entry target context state result,
      result ∈ support ((calls.receive entry target context).run state) → label result.1.1 = label entry)
    (sendPreserved : ∀ entry context state result,
      result ∈ support ((calls.send entry context).run state) → label result.1.1 = label entry)
    (publicCalls : QueryImpl RawCtxServerServices.PublicSpec (StateT State ProbComp))
    (reader : QueryImpl (RawCtxGenericFamilyRead.ReadSpec Kernel S B) (StateT State ProbComp))
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp (RawCtxProtocolReveals.SourceSpec S B) Result)
    (entry : RawCtxGenericFamilyLive.State Kernel M P I D K S B) (state : State)
    (result : (Result × RawCtxGenericFamilyLive.State Kernel M P I D K S B) × State)
    (supported : result ∈ support (((simulateQ (RawCtxGenericFamilyLive.impl calls publicCalls reader sender route decode) client).run entry).run state))
    (selected : RawCtxProtocolReveals.Owner S B) : familyLabel label selected result.1.2.1 = familyLabel label selected entry.1 := by
  induction client using OracleComp.inductionOn generalizing entry state result with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at supported
      subst result
      rfl
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query] at supported
      change result ∈ support ((((RawCtxGenericFamilyLive.impl calls publicCalls reader sender route decode query).run entry).run state) >>= fun reply =>
        ((simulateQ (RawCtxGenericFamilyLive.impl calls publicCalls reader sender route decode) (next reply.1.1)).run reply.1.2).run reply.2) at supported
      rw [mem_support_bind_iff] at supported
      obtain ⟨reply, head, tail⟩ := supported
      exact (ih reply.1.1 reply.1.2 reply.2 result tail).trans
        (live label calls receivePreserved sendPreserved publicCalls reader sender route decode query entry state reply head selected)

end BeaconcryptCore.Computational.RawCtxFamilyOriginLabels

/-- info: 'BeaconcryptCore.Computational.RawCtxFamilyOriginLabels.raw' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxFamilyOriginLabels.raw

/-- info: 'BeaconcryptCore.Computational.RawCtxFamilyOriginLabels.send' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxFamilyOriginLabels.send

/-- info: 'BeaconcryptCore.Computational.RawCtxFamilyOriginLabels.owner' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxFamilyOriginLabels.owner

/-- info: 'BeaconcryptCore.Computational.RawCtxFamilyOriginLabels.server_raw' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxFamilyOriginLabels.server_raw

/-- info: 'BeaconcryptCore.Computational.RawCtxFamilyOriginLabels.server_send' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxFamilyOriginLabels.server_send

/-- info: 'BeaconcryptCore.Computational.RawCtxFamilyOriginLabels.server' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxFamilyOriginLabels.server

/-- info: 'BeaconcryptCore.Computational.RawCtxFamilyOriginLabels.beacon' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxFamilyOriginLabels.beacon

/-- info: 'BeaconcryptCore.Computational.RawCtxFamilyOriginLabels.family' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxFamilyOriginLabels.family

/-- info: 'BeaconcryptCore.Computational.RawCtxFamilyOriginLabels.live' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxFamilyOriginLabels.live

/-- info: 'BeaconcryptCore.Computational.RawCtxFamilyOriginLabels.schedule' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxFamilyOriginLabels.schedule
