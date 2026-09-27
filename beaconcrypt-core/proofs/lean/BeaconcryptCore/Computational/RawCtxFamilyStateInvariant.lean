import BeaconcryptCore.Computational.RawCtxGenericFamilyLive

/-!
The original no-install family frontend transports a kernel predicate indexed by the actual shared state. Every callback retains its complete reply and state, while the shared-state relation lets untouched owners retain monotone properties. The concrete source consumer must discharge the callback contracts from its actual interpreter; no security or cost conclusion is inferred here.
-/
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.refined ratchet.concrete
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RawCtxFamilyStateInvariant
variable {Kernel State M P I D K Result : Type} {S B : Nat}

structure Rules (calls : RawCtxChainOwner.Calls Kernel (StateT State ProbComp))
    (le : State → State → Prop) (valid : Kernel → State → Prop) : Prop where
  refl : ∀ state, le state state
  trans : ∀ before middle after, le before middle → le middle after → le before after
  mono : ∀ kernel before after, le before after → valid kernel before → valid kernel after
  receive : ∀ entry target context state result,
    result ∈ support ((calls.receive entry target context).run state) →
      le state result.2 ∧ (valid entry state → valid result.1.1 result.2)
  send : ∀ entry context state result,
    result ∈ support ((calls.send entry context).run state) →
      le state result.2 ∧ (valid entry state → valid result.1.1 result.2)

def Holds (valid : Kernel → State → Prop) (kernel : Option Kernel) (state : State) : Prop :=
  ∀ value, kernel = some value → valid value state

private theorem holds_mono {calls : RawCtxChainOwner.Calls Kernel (StateT State ProbComp)}
    {le : State → State → Prop} {valid : Kernel → State → Prop} (rules : Rules calls le valid)
    (kernel : Option Kernel) (before after : State) (step : le before after) :
    Holds valid kernel before → Holds valid kernel after := fun h value present => rules.mono value before after step (h value present)

/-- Raw admission and publication preserve the shared-state relation and the active owner's predicate. -/
theorem raw (calls : RawCtxChainOwner.Calls Kernel (StateT State ProbComp))
    (le : State → State → Prop) (valid : Kernel → State → Prop) (rules : Rules calls le valid)
    (decode : RawCtxReceive.FrameDecoder) (bytes : Pqxdh.Bytes) (entry : RawCtxChainOwner.State Kernel M)
    (state : State) (result : (core.option.Option RawCtxWholeOwner.Decrypted × RawCtxChainOwner.State Kernel M) × State)
    (supported : result ∈ support (((RawCtxChainOwner.rawReceive calls decode bytes).run entry).run state)) :
    le state result.2 ∧ (valid entry.kernel state → valid result.1.2.kernel result.2) := by
  unfold RawCtxChainOwner.rawReceive at supported
  simp only [StateT.run] at supported
  split at supported
  · change result ∈ support (pure (RawCtxChainOwner.publish entry (entry.kernel, .None), state)) at supported
    simp only [mem_support_pure_iff] at supported
    subst result
    exact ⟨rules.refl _, id⟩
  · cases decoded : decode bytes with
    | none =>
      simp only [decoded] at supported
      change result ∈ support (pure (RawCtxChainOwner.publish entry (entry.kernel, .None), state)) at supported
      simp only [mem_support_pure_iff] at supported
      subst result
      exact ⟨rules.refl _, id⟩
    | some frame =>
      simp only [decoded] at supported
      split at supported
      · simp only [bind_pure_comp] at supported
        change result ∈ support ((RawCtxChainOwner.publish entry <$>
          calls.receive entry.kernel frame.sequence ⟨bytes, frame, entry.associatedData⟩).run state) at supported
        rw [StateT.run_map, support_map] at supported
        obtain ⟨reply, reached, rfl⟩ := supported
        exact rules.receive _ _ _ _ reply reached
      · change result ∈ support (pure (RawCtxChainOwner.publish entry (entry.kernel, .None), state)) at supported
        simp only [mem_support_pure_iff] at supported
        subst result
        exact ⟨rules.refl _, id⟩

/-- Every original send attempt preserves the relation and active predicate, including empty rejection and failed sealing. -/
theorem send (calls : RawCtxChainOwner.Calls Kernel (StateT State ProbComp))
    (le : State → State → Prop) (valid : Kernel → State → Prop) (rules : Rules calls le valid)
    (sender : Std.U64) (plaintext : Pqxdh.Bytes) (entry : RawCtxChainOwner.State Kernel M)
    (state : State) (result : (Option RawCtxSourceSend.Encrypted × RawCtxChainOwner.State Kernel M) × State)
    (supported : result ∈ support (((RawCtxChainOwner.sendOwner calls sender plaintext).run entry).run state)) :
    le state result.2 ∧ (valid entry.kernel state → valid result.1.2.kernel result.2) := by
  unfold RawCtxChainOwner.sendOwner at supported
  simp only [StateT.run] at supported
  split at supported
  · change result ∈ support (pure ((none, entry), state)) at supported
    simp only [mem_support_pure_iff] at supported
    subst result
    exact ⟨rules.refl _, id⟩
  · simp only [bind_pure_comp] at supported
    change result ∈ support (((fun reply => (reply.2, {entry with kernel := reply.1})) <$>
      calls.send entry.kernel ⟨plaintext, entry.expectedSender, sender, entry.associatedData⟩).run state) at supported
    rw [StateT.run_map, support_map] at supported
    obtain ⟨reply, reached, rfl⟩ := supported
    exact rules.send _ _ _ reply reached

/-- The original mixed owner API retains the actual shared-state relation and active predicate. -/
theorem owner (calls : RawCtxChainOwner.Calls Kernel (StateT State ProbComp))
    (le : State → State → Prop) (valid : Kernel → State → Prop) (rules : Rules calls le valid)
    (sender : Std.U64) (decode : RawCtxReceive.FrameDecoder) (query : RawCtxMixedOwner.SourceSpec.Domain)
    (entry : RawCtxChainOwner.State Kernel M) (state : State)
    (result : (RawCtxMixedOwner.SourceSpec.Range query × RawCtxChainOwner.State Kernel M) × State)
    (supported : result ∈ support (((RawCtxChainOwner.ownerImpl calls sender decode query).run entry).run state)) :
    le state result.2 ∧ (valid entry.kernel state → valid result.1.2.kernel result.2) := by
  cases query with
  | inl plaintext => exact send calls le valid rules sender plaintext entry state result supported
  | inr bytes => exact raw calls le valid rules decode bytes entry state result supported

def serverKernel (peer : Std.U64) (entry : RawCtxGenericRoleStorage.ServerState Kernel M P) : Option Kernel :=
  (entry.server.peers peer).map (fun value => value.kernel)

private theorem put_holds (calls : RawCtxChainOwner.Calls Kernel (StateT State ProbComp))
    (le : State → State → Prop) (valid : Kernel → State → Prop) (rules : Rules calls le valid)
    (entry : RawCtxGenericRoleStorage.ServerState Kernel M P) (selected peer : Std.U64)
    (before : RawCtxGenericRoleStorage.Peer Kernel P) (after : Kernel) (attempts : Nat)
    (state nextState : State) (found : entry.server.peers selected = some before)
    (extension : le state nextState) (preserved : valid before.kernel state → valid after nextState) :
    Holds valid (serverKernel peer entry) state →
      Holds valid (serverKernel peer ⟨RawCtxGenericServer.putPeer entry.server selected before after, attempts⟩) nextState := by
  by_cases same : peer = selected
  · subst peer
    simp only [serverKernel, RawCtxGenericServer.putPeer, Function.update_self, found, Option.map_some]
    intro initial kernel present
    cases Option.some.inj present
    exact preserved (initial before.kernel rfl)
  · simp only [serverKernel, RawCtxGenericServer.putPeer, Function.update_of_ne same]
    exact holds_mono rules _ _ _ extension

/-- Original Server receive routing preserves every peer predicate while retaining callback state growth. -/
theorem server_raw (calls : RawCtxChainOwner.Calls Kernel (StateT State ProbComp))
    (le : State → State → Prop) (valid : Kernel → State → Prop) (rules : Rules calls le valid)
    (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder) (bytes : Pqxdh.Bytes)
    (entry : RawCtxGenericRoleStorage.ServerState Kernel M P) (state : State)
    (result : (core.option.Option RawCtxWholeOwner.Decrypted × RawCtxGenericRoleStorage.ServerState Kernel M P) × State)
    (supported : result ∈ support ((RawCtxGenericServer.rawServer calls route decode bytes entry).run state))
    (peer : Std.U64) : le state result.2 ∧
      (Holds valid (serverKernel peer entry) state → Holds valid (serverKernel peer result.1.2) result.2) := by
  unfold RawCtxGenericServer.rawServer at supported
  cases routed : route bytes with
  | none =>
      simp only [routed] at supported
      change result ∈ support (pure ((.None, {entry with rawAttempts := entry.rawAttempts + 1}), state)) at supported
      simp only [mem_support_pure_iff] at supported
      subst result
      exact ⟨rules.refl _, id⟩
  | some selected =>
      simp only [routed] at supported
      cases associated : RawCtxGenericServer.peerAssociatedData entry.server selected with
      | none =>
          simp only [associated] at supported
          change result ∈ support (pure ((.None, {entry with rawAttempts := entry.rawAttempts + 1}), state)) at supported
          simp only [mem_support_pure_iff] at supported
          subst result
          exact ⟨rules.refl _, id⟩
      | some ad =>
          simp only [associated] at supported
          cases found : entry.server.peers selected with
          | none =>
              simp only [found] at supported
              change result ∈ support (pure ((.None, {entry with rawAttempts := entry.rawAttempts + 1}), state)) at supported
              simp only [mem_support_pure_iff] at supported
              subst result
              exact ⟨rules.refl _, id⟩
          | some original =>
              simp only [found, bind_pure_comp, StateT.run_map, support_map] at supported
              obtain ⟨reply, reached, rfl⟩ := supported
              have step := raw calls le valid rules decode bytes
                (RawCtxGenericServer.selectedOwner selected ad original entry.rawAttempts) state reply reached
              exact ⟨step.1, put_holds calls le valid rules entry selected peer original
                reply.1.2.kernel reply.1.2.rawAttempts state reply.2 found step.1 step.2⟩

/-- Every Server send preserves the selected and untouched peer predicates under the same actual shared-state extension. -/
theorem server_send (calls : RawCtxChainOwner.Calls Kernel (StateT State ProbComp))
    (le : State → State → Prop) (valid : Kernel → State → Prop) (rules : Rules calls le valid)
    (sender : M → Std.U64) (plaintext : Pqxdh.Bytes) (selected : Std.U64)
    (entry : RawCtxGenericRoleStorage.ServerState Kernel M P) (state : State)
    (result : (Option RawCtxSourceSend.Encrypted × RawCtxGenericRoleStorage.ServerState Kernel M P) × State)
    (supported : result ∈ support ((RawCtxGenericServer.sendServer calls sender plaintext selected entry).run state))
    (peer : Std.U64) : le state result.2 ∧
      (Holds valid (serverKernel peer entry) state → Holds valid (serverKernel peer result.1.2) result.2) := by
  unfold RawCtxGenericServer.sendServer at supported
  cases associated : RawCtxGenericServer.peerAssociatedData entry.server selected with
  | none =>
      simp only [associated] at supported
      change result ∈ support (pure ((none, entry), state)) at supported
      simp only [mem_support_pure_iff] at supported
      subst result
      exact ⟨rules.refl _, id⟩
  | some ad =>
      simp only [associated] at supported
      cases found : entry.server.peers selected with
      | none =>
          simp only [found] at supported
          change result ∈ support (pure ((none, entry), state)) at supported
          simp only [mem_support_pure_iff] at supported
          subst result
          exact ⟨rules.refl _, id⟩
      | some original =>
          simp only [found, bind_pure_comp, StateT.run_map, support_map] at supported
          obtain ⟨reply, reached, rfl⟩ := supported
          have step := send calls le valid rules (sender entry.server.metadata) plaintext
            (RawCtxGenericServer.selectedOwner selected ad original entry.rawAttempts) state reply reached
          exact ⟨step.1, put_holds calls le valid rules entry selected peer original
            reply.1.2.kernel reply.1.2.rawAttempts state reply.2 found step.1 step.2⟩

/-- Each original Server request preserves every selected peer predicate and actual state extension. -/
theorem server (calls : RawCtxChainOwner.Calls Kernel (StateT State ProbComp))
    (le : State → State → Prop) (valid : Kernel → State → Prop) (rules : Rules calls le valid)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (query : RawCtxServerMixed.SourceSpec.Domain) (entry : RawCtxGenericRoleStorage.ServerState Kernel M P) (state : State)
    (result : (RawCtxServerMixed.SourceSpec.Range query × RawCtxGenericRoleStorage.ServerState Kernel M P) × State)
    (supported : result ∈ support (((RawCtxGenericServer.serverImpl calls sender route decode query).run entry).run state))
    (peer : Std.U64) : le state result.2 ∧
      (Holds valid (serverKernel peer entry) state → Holds valid (serverKernel peer result.1.2) result.2) := by
  cases query with
  | inl request => exact server_send calls le valid rules sender request.1 request.2 entry state result supported peer
  | inr bytes => exact server_raw calls le valid rules route decode bytes entry state result supported peer

def beaconKernel (entry : RawCtxGenericRoleStorage.BeaconState Kernel I D K) : Option Kernel :=
  match entry.beacon.phase with
  | .established _ _ kernel => some kernel
  | _ => none

/-- Established Beacon operations preserve their state-indexed kernel predicate; inactive phases remain absent. -/
theorem beacon (calls : RawCtxChainOwner.Calls Kernel (StateT State ProbComp))
    (le : State → State → Prop) (valid : Kernel → State → Prop) (rules : Rules calls le valid)
    (decode : RawCtxReceive.FrameDecoder) (query : RawCtxMixedOwner.SourceSpec.Domain)
    (entry : RawCtxGenericRoleStorage.BeaconState Kernel I D K) (state : State)
    (result : (RawCtxMixedOwner.SourceSpec.Range query × RawCtxGenericRoleStorage.BeaconState Kernel I D K) × State)
    (supported : result ∈ support (((RawCtxGenericBeacon.impl calls decode query).run entry).run state)) :
    le state result.2 ∧
      (Holds valid (beaconKernel entry) state → Holds valid (beaconKernel result.1.2) result.2) := by
  cases phase : entry.beacon.phase
  case established control ad kernel =>
    simp only [RawCtxGenericBeacon.impl, StateT.run, phase, bind_pure_comp] at supported
    change result ∈ support (((fun reply =>
      (reply.1, RawCtxGenericBeacon.reinstall entry control ad reply.2)) <$>
        (RawCtxChainOwner.ownerImpl calls entry.beacon.identityKeyId decode query).run
          (RawCtxGenericBeacon.selected entry control ad kernel)).run state) at supported
    rw [StateT.run_map, support_map] at supported
    obtain ⟨reply, reached, rfl⟩ := supported
    have step := owner calls le valid rules entry.beacon.identityKeyId decode query
      (RawCtxGenericBeacon.selected entry control ad kernel) state reply reached
    refine ⟨step.1, ?_⟩
    simp only [beaconKernel, RawCtxGenericBeacon.reinstall, phase]
    intro initial value present
    cases Option.some.inj present
    exact step.2 (initial kernel rfl)
  all_goals
    cases query <;> simp only [RawCtxGenericBeacon.impl, StateT.run, phase, RawCtxGenericBeacon.rejected] at supported
    all_goals
      change result ∈ support (pure _) at supported
      simp only [mem_support_pure_iff] at supported
      subst result
      exact ⟨rules.refl _, id⟩

private theorem selected_beacon (index : Fin B)
    (entry : RawCtxGenericRoleFamily.Roles Kernel M P I D K S B) :
    RawCtxGenericRoleFamily.selectedKernel (.beacon index) entry = beaconKernel (entry.2 index) := by
  cases phase : (entry.2 index).beacon.phase <;>
    simp only [RawCtxGenericRoleFamily.selectedKernel, beaconKernel, phase]

/-- Every original finite-family request preserves a selected owner's predicate under the full callback state relation. -/
theorem family (calls : RawCtxChainOwner.Calls Kernel (StateT State ProbComp))
    (le : State → State → Prop) (valid : Kernel → State → Prop) (rules : Rules calls le valid)
    (publicCalls : QueryImpl RawCtxServerServices.PublicSpec (StateT State ProbComp))
    (publicPreserved : ∀ query state result, result ∈ support ((publicCalls query).run state) → le state result.2)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (query : (RawCtxProtocolRoles.SourceSpec S B).Domain)
    (entry : RawCtxGenericRoleFamily.Roles Kernel M P I D K S B) (state : State)
    (result : ((RawCtxProtocolRoles.SourceSpec S B).Range query × RawCtxGenericRoleFamily.Roles Kernel M P I D K S B) × State)
    (supported : result ∈ support (((RawCtxGenericFamilyFrontend.impl calls publicCalls sender route decode query).run entry).run state))
    (selected : RawCtxProtocolReveals.Owner S B) : le state result.2 ∧
      (Holds valid (RawCtxGenericRoleFamily.selectedKernel selected entry) state →
        Holds valid (RawCtxGenericRoleFamily.selectedKernel selected result.1.2) result.2) := by
  rcases query with ⟨index, request⟩ | (⟨index, request⟩ | request)
  case inl =>
    simp only [RawCtxGenericFamilyFrontend.impl, StateT.run, bind_pure_comp] at supported
    change result ∈ support (((fun reply =>
      (reply.1, (Function.update entry.1 index reply.2, entry.2))) <$>
        (RawCtxGenericServer.serverImpl calls sender route decode request).run (entry.1 index)).run state) at supported
    rw [StateT.run_map, support_map] at supported
    obtain ⟨reply, reached, rfl⟩ := supported
    have extension := (server calls le valid rules sender route decode request (entry.1 index) state reply reached 0#u64).1
    refine ⟨extension, ?_⟩
    cases selected with
    | server selected peer =>
        by_cases same : selected = index
        · subst selected
          simpa only [RawCtxGenericRoleFamily.selectedKernel, Function.update_self, serverKernel] using
            (server calls le valid rules sender route decode request (entry.1 index) state reply reached peer).2
        · simp only [RawCtxGenericRoleFamily.selectedKernel, Function.update_of_ne same]
          exact holds_mono rules _ _ _ extension
    | beacon _ => exact holds_mono rules _ _ _ extension
  case inr.inl =>
    simp only [RawCtxGenericFamilyFrontend.impl, StateT.run, bind_pure_comp] at supported
    change result ∈ support (((fun reply =>
      (reply.1, (entry.1, Function.update entry.2 index reply.2))) <$>
        (RawCtxGenericBeacon.impl calls decode request).run (entry.2 index)).run state) at supported
    rw [StateT.run_map, support_map] at supported
    obtain ⟨reply, reached, rfl⟩ := supported
    have step := beacon calls le valid rules decode request (entry.2 index) state reply reached
    refine ⟨step.1, ?_⟩
    cases selected with
    | server _ _ => exact holds_mono rules _ _ _ step.1
    | beacon selected =>
        by_cases same : selected = index
        · subst selected
          simpa only [selected_beacon, Function.update_self] using step.2
        · simp only [RawCtxGenericRoleFamily.selectedKernel, Function.update_of_ne same]
          exact holds_mono rules _ _ _ step.1
  case inr.inr =>
    simp only [RawCtxGenericFamilyFrontend.impl, StateT.run, bind_pure_comp] at supported
    change result ∈ support (((fun reply => (reply, entry)) <$> publicCalls request).run state) at supported
    rw [StateT.run_map, support_map] at supported
    obtain ⟨reply, reached, rfl⟩ := supported
    have extension := publicPreserved _ _ _ reached
    exact ⟨extension, holds_mono rules _ _ _ extension⟩

/-- Original live reads retain the same family and exact reply history while the shared-state relation preserves its selected predicate. -/
theorem live (calls : RawCtxChainOwner.Calls Kernel (StateT State ProbComp))
    (le : State → State → Prop) (valid : Kernel → State → Prop) (rules : Rules calls le valid)
    (publicCalls : QueryImpl RawCtxServerServices.PublicSpec (StateT State ProbComp))
    (publicPreserved : ∀ query state result, result ∈ support ((publicCalls query).run state) → le state result.2)
    (reader : QueryImpl (RawCtxGenericFamilyRead.ReadSpec Kernel S B) (StateT State ProbComp))
    (readPreserved : ∀ query state result, result ∈ support ((reader query).run state) → le state result.2)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (query : (RawCtxProtocolReveals.SourceSpec S B).Domain)
    (entry : RawCtxGenericFamilyLive.State Kernel M P I D K S B) (state : State)
    (result : ((RawCtxProtocolReveals.SourceSpec S B).Range query × RawCtxGenericFamilyLive.State Kernel M P I D K S B) × State)
    (supported : result ∈ support (((RawCtxGenericFamilyLive.impl calls publicCalls reader sender route decode query).run entry).run state))
    (selected : RawCtxProtocolReveals.Owner S B) : le state result.2 ∧
      (Holds valid (RawCtxGenericRoleFamily.selectedKernel selected entry.1) state →
        Holds valid (RawCtxGenericRoleFamily.selectedKernel selected result.1.2.1) result.2) := by
  cases query with
  | inl request =>
      simp only [RawCtxGenericFamilyLive.impl, StateT.run, bind_pure_comp] at supported
      change result ∈ support (((fun reply =>
        (reply.1, (reply.2, RawCtxProtocolReveals.tick entry.2))) <$>
          (RawCtxGenericFamilyFrontend.impl calls publicCalls sender route decode request).run entry.1).run state) at supported
      rw [StateT.run_map, support_map] at supported
      obtain ⟨reply, reached, rfl⟩ := supported
      exact family calls le valid rules publicCalls publicPreserved sender route decode request entry.1 state reply reached selected
  | inr request =>
      simp only [RawCtxGenericFamilyLive.impl, StateT.run, bind_pure_comp] at supported
      change result ∈ support (((fun reply : (RawCtxGenericFamilyRead.ReadSpec Kernel S B).Range
          (request, RawCtxGenericRoleFamily.selectedKernel
            (RawCtxGenericFamilyRead.requestOwner request) entry.1) =>
        (reply, (entry.1, RawCtxProtocolReveals.note ⟨request, reply⟩ entry.2))) <$>
          reader (request,
            RawCtxGenericRoleFamily.selectedKernel (RawCtxGenericFamilyRead.requestOwner request) entry.1)).run state) at supported
      rw [StateT.run_map, support_map] at supported
      obtain ⟨reply, reached, rfl⟩ := supported
      have extension := readPreserved _ _ _ reached
      exact ⟨extension, holds_mono rules _ _ _ extension⟩

/-- The complete adaptive original LIVE schedule preserves the selected state-indexed predicate and every earlier shared-state relation. -/
theorem schedule (calls : RawCtxChainOwner.Calls Kernel (StateT State ProbComp))
    (le : State → State → Prop) (valid : Kernel → State → Prop) (rules : Rules calls le valid)
    (publicCalls : QueryImpl RawCtxServerServices.PublicSpec (StateT State ProbComp))
    (publicPreserved : ∀ query state result, result ∈ support ((publicCalls query).run state) → le state result.2)
    (reader : QueryImpl (RawCtxGenericFamilyRead.ReadSpec Kernel S B) (StateT State ProbComp))
    (readPreserved : ∀ query state result, result ∈ support ((reader query).run state) → le state result.2)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp (RawCtxProtocolReveals.SourceSpec S B) Result)
    (entry : RawCtxGenericFamilyLive.State Kernel M P I D K S B) (state : State)
    (result : (Result × RawCtxGenericFamilyLive.State Kernel M P I D K S B) × State)
    (supported : result ∈ support (((simulateQ (RawCtxGenericFamilyLive.impl calls publicCalls reader sender route decode) client).run entry).run state))
    (selected : RawCtxProtocolReveals.Owner S B) : le state result.2 ∧
      (Holds valid (RawCtxGenericRoleFamily.selectedKernel selected entry.1) state →
        Holds valid (RawCtxGenericRoleFamily.selectedKernel selected result.1.2.1) result.2) := by
  induction client using OracleComp.inductionOn generalizing entry state result with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at supported
      subst result
      exact ⟨rules.refl _, id⟩
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query] at supported
      change result ∈ support ((((RawCtxGenericFamilyLive.impl calls publicCalls reader sender route decode query).run entry).run state) >>= fun reply =>
        ((simulateQ (RawCtxGenericFamilyLive.impl calls publicCalls reader sender route decode) (next reply.1.1)).run reply.1.2).run reply.2) at supported
      rw [mem_support_bind_iff] at supported
      obtain ⟨reply, head, tail⟩ := supported
      have first := live calls le valid rules publicCalls publicPreserved reader readPreserved sender route decode
        query entry state reply head selected
      have later := ih reply.1.1 reply.1.2 reply.2 result tail
      exact ⟨rules.trans state reply.2 result.2 first.1 later.1, fun initial => later.2 (first.2 initial)⟩

end BeaconcryptCore.Computational.RawCtxFamilyStateInvariant

/-- info: 'BeaconcryptCore.Computational.RawCtxFamilyStateInvariant.raw' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxFamilyStateInvariant.raw

/-- info: 'BeaconcryptCore.Computational.RawCtxFamilyStateInvariant.send' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxFamilyStateInvariant.send

/-- info: 'BeaconcryptCore.Computational.RawCtxFamilyStateInvariant.owner' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxFamilyStateInvariant.owner

/-- info: 'BeaconcryptCore.Computational.RawCtxFamilyStateInvariant.server_raw' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxFamilyStateInvariant.server_raw

/-- info: 'BeaconcryptCore.Computational.RawCtxFamilyStateInvariant.server_send' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxFamilyStateInvariant.server_send

/-- info: 'BeaconcryptCore.Computational.RawCtxFamilyStateInvariant.server' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxFamilyStateInvariant.server

/-- info: 'BeaconcryptCore.Computational.RawCtxFamilyStateInvariant.beacon' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxFamilyStateInvariant.beacon

/-- info: 'BeaconcryptCore.Computational.RawCtxFamilyStateInvariant.family' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxFamilyStateInvariant.family

/-- info: 'BeaconcryptCore.Computational.RawCtxFamilyStateInvariant.live' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxFamilyStateInvariant.live

/-- info: 'BeaconcryptCore.Computational.RawCtxFamilyStateInvariant.schedule' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxFamilyStateInvariant.schedule
