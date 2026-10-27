import BeaconcryptCore.Computational.RawCtxSelectedSendAddress
import BeaconcryptCore.Computational.LiveApplicationObservation
import BeaconcryptCore.Computational.PqxdhLaterChallengeGeneratedPrefix
/-! Exact pre-request state and sending-input provenance at an inside-challenge callback, retaining the original saved descriptor. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhLaterChallengeInsideState
open PqxdhInitialPostContext RawCtxForwardTags PqxdhFirstRecordConfidentiality
variable {ι M P I D K X Response Shared Result Origin : Type} {extra : OracleSpec ι} {S B : Nat}

/-- A literal saved record descriptor for the specified original request and complete pre-request frontend/trace. -/
def FromRecord (request : (RawCtxProtocolReveals.SourceSpec S B).Domain) (before : NativeFront M P I D K S B) (trace : PqxdhInitialOriginPost.Trace Origin S B)
    (context : PqxdhInitialOriginContext.Context extra M P I D K Result Origin S B) : Prop :=
  ∃ outside inner, context = ⟨.inl (.record request before outside inner), trace, none⟩

private theorem record_shape (sender : M → Std.U64)
    (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (request : (RawCtxProtocolReveals.SourceSpec S B).Domain)
    (before : NativeFront M P I D K S B) (trace : PqxdhInitialOriginPost.Trace Origin S B)
    (outside : (RawCtxProtocolReveals.SourceSpec S B).Range request → OracleComp (PostSpec extra S B) Result)
    (after : (RawCtxProtocolReveals.SourceSpec S B).Range request → NativeFront M P I D K S B → PqxdhInitialOriginPost.Trace Origin S B →
      OracleComp (PqxdhInitialOriginForwardPost.Spec extra M P I D K X Response Shared Result Origin S B) (Result × (NativeFront M P I D K S B × PqxdhInitialOriginPost.Trace Origin S B)))
    (later : ∀ reply updated saved, All (FromRecord request before trace) (after reply updated saved)) :
    All (FromRecord request before trace) (PqxdhInitialOriginForwardPost.record sender route decode request before trace outside after) := by
  apply bind_all
  · apply lift_all (fun _ => True) (FromRecord request before trace)
      (fun inner => ⟨.inl (.record request before outside inner), trace, none⟩)
      (fun inner _ => ⟨outside, inner, rfl⟩)
    exact PqxdhLaterChallengeCapture.all_true _
  · exact fun result => later result.1 _ _

set_option backward.isDefEq.respectTransparency false in
private theorem challenge_shape (mark : PqxdhBeaconPhase2Shared.Secrets Shared → Origin) (sender : M → Std.U64)
    (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (owner : RawCtxProtocolReveals.Owner S B) (number : Std.U64) (bit : Bool) (left right : Pqxdh.Bytes)
    (equal : left.length = right.length) (current : PqxdhRecordConfidentialityChallenge.State)
    (unused : current.pair = none) (before : NativeFront M P I D K S B) (trace : PqxdhInitialOriginPost.Trace Origin S B) :
    All (FromRecord (LiveApplicationObservation.sendRequest owner (if bit then right else left)) before trace) (PqxdhInitialOriginForwardPost.program (X := X) (Response := Response) mark sender route decode
      ((PqxdhRecordConfidentialityChallenge.handler (extra := extra) owner number bit (.inr (left, right))).run current) before trace) := by
  rw [PqxdhRecordConfidentialityChallenge.challenge_step owner number bit left right equal current unused]
  rw [← bind_pure_comp]
  cases owner <;> simp only [PqxdhRecordConfidentialityChallenge.send, PqxdhRecordConfidentialityChallenge.sendRequest]
  all_goals rw [PqxdhInitialOriginForwardPost.program_query]
  all_goals apply record_shape sender route decode
  all_goals exact fun _ _ _ => trivial

/-- The exact admitted equal-length challenge and its source send request, retaining the original owner and chosen plaintext. -/
def FromChallenge (owner : RawCtxProtocolReveals.Owner S B) (bit : Bool) (query : (AdvSpec extra S B).Domain)
    (before : NativeFront M P I D K S B) (trace : PqxdhInitialOriginPost.Trace Origin S B)
    (context : PqxdhInitialOriginContext.Context extra M P I D K Result Origin S B) : Prop :=
  ∃ left right, query = .inr (left, right) ∧ left.length = right.length ∧
    FromRecord (LiveApplicationObservation.sendRequest owner (if bit then right else left)) before trace context

/-- Every descriptor generated inside the admitted challenge retains that very request and complete pre-request frontend/trace. -/
theorem inside_shape (mark : PqxdhBeaconPhase2Shared.Secrets Shared → Origin) (sender : M → Std.U64)
    (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (owner : RawCtxProtocolReveals.Owner S B) (number : Std.U64) (bit : Bool)
    (details : PqxdhLaterChallengeCapture.Details extra M P I D K Origin S B)
    (classified : PqxdhLaterChallengeSavedClassification.phase (some details) = .inside)
    (before : NativeFront M P I D K S B) (trace : PqxdhInitialOriginPost.Trace Origin S B) :
    All (FromChallenge owner bit details.request.query before trace) (PqxdhInitialOriginForwardPost.program (X := X) (Response := Response) mark sender route decode
      ((PqxdhRecordConfidentialityChallenge.handler owner number bit details.request.query).run details.request.before) before trace) := by
  rcases details with ⟨⟨query, current, next⟩, callback⟩
  cases used : current.pair with
  | some pair => simp only [PqxdhLaterChallengeSavedClassification.phase, used, reduceCtorEq] at classified
  | none =>
      rcases query with request | ⟨left, right⟩
      · simp only [PqxdhLaterChallengeSavedClassification.phase, used, reduceCtorEq] at classified
      · by_cases equal : left.length = right.length
        · apply RawCtxForwardTags.mono _ _ _ _ (challenge_shape mark sender route decode owner number bit left right equal current used before trace)
          exact fun _ actual => ⟨left, right, rfl, equal, actual⟩
        · simp only [PqxdhLaterChallengeSavedClassification.phase, used, equal, ite_false, reduceCtorEq] at classified

/-- The actual supported inside-callback scan returns the literal descriptor with its source-derived pre-request state. -/
theorem cut_shape {State : Type} (mark : PqxdhBeaconPhase2Shared.Secrets Shared → Origin) (sender : M → Std.U64)
    (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (owner : RawCtxProtocolReveals.Owner S B) (number : Std.U64) (bit : Bool)
    (details : PqxdhLaterChallengeCapture.Details extra M P I D K Origin S B)
    (classified : PqxdhLaterChallengeSavedClassification.phase (some details) = .inside)
    (selected : (Base extra RatchetChain I D K X Response Shared S B).Domain → State → Bool)
    (selection : ∀ query state, selected query state = true → PqxdhInitialOriginForwardPost.selected query = true)
    (impl : QueryImpl (Base extra RatchetChain I D K X Response Shared S B) (StateT State ProbComp))
    (front : NativeFront M P I D K S B) (trace : PqxdhInitialOriginPost.Trace Origin S B) (state reached : State)
    (cut : RawCtxForwardScan.Cut.pending details.callback reached ∈ support
      (RawCtxForwardScan.scan PqxdhInitialOriginForwardPost.selected selected selection impl
        (PqxdhInitialOriginForwardPost.program mark sender route decode
          ((PqxdhRecordConfidentialityChallenge.handler owner number bit details.request.query).run details.request.before) front trace)
        (PqxdhInitialOriginForwardPost.program_covered mark sender route decode
          ((PqxdhRecordConfidentialityChallenge.handler owner number bit details.request.query).run details.request.before) front trace) state)) :
    FromChallenge owner bit details.request.query front trace details.callback := by
  exact scan_all PqxdhInitialOriginForwardPost.selected selected selection impl (FromChallenge owner bit details.request.query front trace) _ _
    (inside_shape mark sender route decode owner number bit details classified front trace) state reached details.callback cut

private theorem admitted_address (kernel : RawCtxPendingOwnerQueries.Kernel RatchetChain)
    (context : RawCtxSourceSend.SealContext)
    (pending : RawCtxChainSend.Kdf RatchetChain RatchetChain RatchetMaterial RawCtxSourceSend.SealContext)
    (admitted : RawCtxChainSend.normalBegin kernel context = .requested pending) :
    RawCtxSelectedPendingCut.requestAddress pending.request = RawCtxSelectedPendingCut.requestAddress kernel.send_chain := by
  have actual := RawCtxChainSend.normalBegin_native id id kernel context
  rw [admitted] at actual
  exact RawCtxSelectedSendAddress.admitted_address (RawCtxChainInterpretation.mapChains id id kernel) context (RawCtxChainSend.nativeKdf id id pending) actual

private theorem owner_send_address {Metadata : Type} (sender : Std.U64) (read : RawCtxReceive.FrameDecoder)
    (before : RawCtxForwardOwner.Owner Metadata) (plaintext : Pqxdh.Bytes) :
    All (fun context => RawCtxSelectedFamilyContext.ownerAddress context = RawCtxSelectedPendingCut.requestAddress before.kernel.send_chain)
      (RawCtxForwardOwner.program sender read (RawCtxForwardOwner.SourceSpec.query (.inl (.inl plaintext))) before) := by
  change All _ (if plaintext.isEmpty then pure (none, before) else
    RawCtxForwardOwner.send before pure (fun result => pure (result.2, { before with kernel := result.1 }))
      (RawCtxChainSend.normalBegin before.kernel ⟨plaintext, before.expectedSender, sender, before.associatedData⟩))
  split
  · trivial
  · cases begun : RawCtxChainSend.normalBegin before.kernel (⟨plaintext, before.expectedSender, sender, before.associatedData⟩ : RawCtxSourceSend.SealContext) with
    | exhausted entry context => trivial
    | requested pending =>
        rw [RawCtxForwardOwner.send, query_all]
        refine ⟨?_, ?_⟩
        · intro tag same
          cases same
          exact admitted_address before.kernel _ pending begun
        · intro reply
          exact ⟨(fun _ impossible => by cases impossible), fun _ => trivial⟩

private theorem server_send_address (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder)
    (read : RawCtxReceive.FrameDecoder) (before : RawCtxForwardServer.State M P) (plaintext : Pqxdh.Bytes) (peerId : Std.U64) :
    All (fun context => ∃ peer, before.server.peers peerId = some peer ∧
      RawCtxSelectedFamilyContext.serverAddress context = RawCtxSelectedPendingCut.requestAddress peer.kernel.send_chain)
      (RawCtxForwardServer.program sender route read (RawCtxForwardServer.SourceSpec.query (.inl (plaintext, peerId))) before) := by
  change All _ (match before.server.peers peerId with
    | none => pure (none, before)
    | some peer => RawCtxForwardServer.owner sender read (.inl plaintext) before peerId peer pure
        (fun reply updated => pure (reply, updated)))
  cases found : before.server.peers peerId with
  | none => trivial
  | some peer =>
      unfold RawCtxForwardServer.owner
      apply bind_all
      · apply map_all (fun context => RawCtxSelectedFamilyContext.ownerAddress context = RawCtxSelectedPendingCut.requestAddress peer.kernel.send_chain)
        · exact fun _ address => ⟨peer, rfl, address⟩
        · exact owner_send_address _ _ _ _
      · exact fun _ => trivial

/-- The family-layer form of the existing source send request. -/
def familySendRequest (owner : RawCtxProtocolReveals.Owner S B) (plaintext : Pqxdh.Bytes) :
    (RawCtxForwardFamily.SourceSpec S B).Domain := match owner with
  | .server index peer => .inl ⟨index, .inl (plaintext, peer)⟩
  | .beacon index => .inr (.inl ⟨index, .inl plaintext⟩)

private theorem family_send_address (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder)
    (read : RawCtxReceive.FrameDecoder) (before : RawCtxForwardFamily.State M P I D K S B)
    (owner : RawCtxProtocolReveals.Owner S B) (plaintext : Pqxdh.Bytes) :
    All (fun context => ∃ kernel, RawCtxGenericRoleFamily.selectedKernel owner before = some kernel ∧
      RawCtxSelectedFamilyContext.familyAddress context = RawCtxSelectedPendingCut.requestAddress kernel.send_chain)
      (RawCtxForwardFamily.program sender route read (liftM ((RawCtxForwardFamily.SourceSpec S B).query (familySendRequest owner plaintext))) before) := by
  cases owner with
  | server index peerId =>
      change All _ (RawCtxForwardFamily.server sender route read (.inl (plaintext, peerId)) before index pure
        (fun reply updated => pure (reply, updated)))
      unfold RawCtxForwardFamily.server
      apply bind_all
      · apply map_all (fun context => ∃ peer, (before.1 index).server.peers peerId = some peer ∧
          RawCtxSelectedFamilyContext.serverAddress context = RawCtxSelectedPendingCut.requestAddress peer.kernel.send_chain)
        · rintro context ⟨peer, found, address⟩
          exact ⟨peer.kernel, by simp only [RawCtxGenericRoleFamily.selectedKernel, found, Option.map_some], address⟩
        · exact server_send_address _ _ _ _ _ _
      · exact fun _ => trivial
  | beacon index =>
      change All _ (RawCtxForwardFamily.beacon read (.inl plaintext) before index pure
        (fun reply updated => pure (reply, updated)))
      cases active : (before.2 index).beacon.phase <;> simp only [RawCtxForwardFamily.beacon, active]
      all_goals try trivial
      rename_i control associatedData kernel
      apply bind_all
      · apply map_all (fun context => RawCtxSelectedFamilyContext.ownerAddress context = RawCtxSelectedPendingCut.requestAddress kernel.send_chain)
        · exact fun _ address => ⟨kernel, by simp only [RawCtxGenericRoleFamily.selectedKernel, active], address⟩
        · exact owner_send_address _ _ _ _
      · exact fun _ => trivial


private theorem live_send_address (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder)
    (read : RawCtxReceive.FrameDecoder) (before : RawCtxForwardLive.State M P I D K S B)
    (owner : RawCtxProtocolReveals.Owner S B) (plaintext : Pqxdh.Bytes) :
    All (fun context => ∃ kernel, RawCtxGenericRoleFamily.selectedKernel owner before.1 = some kernel ∧
      RawCtxSelectedFamilyContext.address context = RawCtxSelectedPendingCut.requestAddress kernel.send_chain)
      (RawCtxForwardLive.program sender route read (liftM ((RawCtxForwardLive.SourceSpec S B).query
        (LiveApplicationObservation.sendRequest owner plaintext))) before) := by
  have request : LiveApplicationObservation.sendRequest owner plaintext = .inl (familySendRequest owner plaintext) := by cases owner <;> rfl
  rw [request]
  change All _ (RawCtxForwardLive.family sender route read (familySendRequest owner plaintext) before pure
    (fun reply updated => pure (reply, updated)))
  unfold RawCtxForwardLive.family
  apply bind_all
  · apply lift_all (fun context => ∃ kernel, RawCtxGenericRoleFamily.selectedKernel owner before.1 = some kernel ∧
      RawCtxSelectedFamilyContext.familyAddress context = RawCtxSelectedPendingCut.requestAddress kernel.send_chain)
    · exact fun _ actual => actual
    · exact family_send_address _ _ _ _ _ _
  · exact fun _ => trivial

/-- The actual requested owner exists and its pre-request send chain supplies the saved descriptor address. -/
def AtAddress (owner : RawCtxProtocolReveals.Owner S B) (before : NativeFront M P I D K S B)
    (context : PqxdhInitialOriginContext.Context extra M P I D K Result Origin S B) : Prop :=
  ∃ kernel, RawCtxGenericRoleFamily.selectedKernel owner before.roles.1 = some kernel ∧
    PqxdhInitialBuilderContext.address context.original = RawCtxSelectedPendingCut.requestAddress kernel.send_chain

private theorem record_address (sender : M → Std.U64)
    (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (owner : RawCtxProtocolReveals.Owner S B) (plaintext : Pqxdh.Bytes)
    (before : NativeFront M P I D K S B) (trace : PqxdhInitialOriginPost.Trace Origin S B)
    (outside : (RawCtxProtocolReveals.SourceSpec S B).Range (LiveApplicationObservation.sendRequest owner plaintext) →
      OracleComp (PostSpec extra S B) Result)
    (after : (RawCtxProtocolReveals.SourceSpec S B).Range (LiveApplicationObservation.sendRequest owner plaintext) →
      NativeFront M P I D K S B → PqxdhInitialOriginPost.Trace Origin S B →
      OracleComp (PqxdhInitialOriginForwardPost.Spec extra M P I D K X Response Shared Result Origin S B)
        (Result × (NativeFront M P I D K S B × PqxdhInitialOriginPost.Trace Origin S B)))
    (later : ∀ reply updated saved, All (AtAddress owner before) (after reply updated saved)) :
    All (AtAddress owner before) (PqxdhInitialOriginForwardPost.record sender route decode
      (LiveApplicationObservation.sendRequest owner plaintext) before trace outside after) := by
  apply bind_all
  · apply lift_all (fun context => ∃ kernel, RawCtxGenericRoleFamily.selectedKernel owner before.roles.1 = some kernel ∧
      RawCtxSelectedFamilyContext.address context = RawCtxSelectedPendingCut.requestAddress kernel.send_chain)
    · exact fun _ actual => actual
    · exact live_send_address _ _ _ _ _ _
  · exact fun result => later result.1 _ _

set_option backward.isDefEq.respectTransparency false in
private theorem challenge_address (mark : PqxdhBeaconPhase2Shared.Secrets Shared → Origin) (sender : M → Std.U64)
    (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (owner : RawCtxProtocolReveals.Owner S B) (number : Std.U64) (bit : Bool) (left right : Pqxdh.Bytes)
    (equal : left.length = right.length) (current : PqxdhRecordConfidentialityChallenge.State)
    (unused : current.pair = none) (before : NativeFront M P I D K S B) (trace : PqxdhInitialOriginPost.Trace Origin S B) :
    All (AtAddress owner before) (PqxdhInitialOriginForwardPost.program (X := X) (Response := Response) mark sender route decode
      ((PqxdhRecordConfidentialityChallenge.handler (extra := extra) owner number bit (.inr (left, right))).run current) before trace) := by
  rw [PqxdhRecordConfidentialityChallenge.challenge_step owner number bit left right equal current unused]
  rw [← bind_pure_comp]
  cases owner <;> simp only [PqxdhRecordConfidentialityChallenge.send, PqxdhRecordConfidentialityChallenge.sendRequest]
  all_goals rw [PqxdhInitialOriginForwardPost.program_query]
  all_goals apply record_address sender route decode
  all_goals exact fun _ _ _ => trivial

/-- The actual challenge callback selects a present owner kernel and exactly its old sending input, through all original Server/Beacon admission paths. -/
theorem inside_address (mark : PqxdhBeaconPhase2Shared.Secrets Shared → Origin) (sender : M → Std.U64)
    (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (owner : RawCtxProtocolReveals.Owner S B) (number : Std.U64) (bit : Bool)
    (details : PqxdhLaterChallengeCapture.Details extra M P I D K Origin S B)
    (classified : PqxdhLaterChallengeSavedClassification.phase (some details) = .inside)
    (before : NativeFront M P I D K S B) (trace : PqxdhInitialOriginPost.Trace Origin S B) :
    All (AtAddress owner before) (PqxdhInitialOriginForwardPost.program (X := X) (Response := Response) mark sender route decode
      ((PqxdhRecordConfidentialityChallenge.handler owner number bit details.request.query).run details.request.before) before trace) := by
  rcases details with ⟨⟨query, current, next⟩, callback⟩
  cases used : current.pair with
  | some pair => simp only [PqxdhLaterChallengeSavedClassification.phase, used, reduceCtorEq] at classified
  | none =>
      rcases query with request | ⟨left, right⟩
      · simp only [PqxdhLaterChallengeSavedClassification.phase, used, reduceCtorEq] at classified
      · by_cases equal : left.length = right.length
        · exact challenge_address mark sender route decode owner number bit left right equal current used before trace
        · simp only [PqxdhLaterChallengeSavedClassification.phase, used, equal, ite_false, reduceCtorEq] at classified

/-- The supported inside-callback cut has the actual pre-request send-chain address; no sampled or reconstructed owner is substituted. -/
theorem cut_address {State : Type} (mark : PqxdhBeaconPhase2Shared.Secrets Shared → Origin) (sender : M → Std.U64)
    (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (owner : RawCtxProtocolReveals.Owner S B) (number : Std.U64) (bit : Bool)
    (details : PqxdhLaterChallengeCapture.Details extra M P I D K Origin S B)
    (classified : PqxdhLaterChallengeSavedClassification.phase (some details) = .inside)
    (selected : (Base extra RatchetChain I D K X Response Shared S B).Domain → State → Bool)
    (selection : ∀ query state, selected query state = true → PqxdhInitialOriginForwardPost.selected query = true)
    (impl : QueryImpl (Base extra RatchetChain I D K X Response Shared S B) (StateT State ProbComp))
    (front : NativeFront M P I D K S B) (trace : PqxdhInitialOriginPost.Trace Origin S B) (state reached : State)
    (cut : RawCtxForwardScan.Cut.pending details.callback reached ∈ support
      (RawCtxForwardScan.scan PqxdhInitialOriginForwardPost.selected selected selection impl
        (PqxdhInitialOriginForwardPost.program mark sender route decode
          ((PqxdhRecordConfidentialityChallenge.handler owner number bit details.request.query).run details.request.before) front trace)
        (PqxdhInitialOriginForwardPost.program_covered mark sender route decode
          ((PqxdhRecordConfidentialityChallenge.handler owner number bit details.request.query).run details.request.before) front trace) state)) :
    AtAddress owner front details.callback := by
  exact scan_all PqxdhInitialOriginForwardPost.selected selected selection impl (AtAddress owner front) _ _
    (inside_address mark sender route decode owner number bit details classified front trace) state reached details.callback cut

/-- Full material interpretation preserves the monitor selected-input predicate; it changes no sending-chain field. -/
theorem selected_projection {A N C : Type} (key target : PqxdhSecretInputKdf.RootOutput)
    (owner : RawCtxProtocolReveals.Owner S B) (state : InsState M P I D K A N C S B) :
    PqxdhLaterChallengeMonitor.Selected target owner state ↔
      ∀ kernel, RawCtxGenericRoleFamily.selectedKernel owner (PqxdhSelectedFirstRecord.frontOf key state.1.1).roles.1 = some kernel →
        RawCtxSelectedPendingCut.requestAddress kernel.send_chain = RawCtxSelectedParentPrivatePatch.targetAddress target := by
  simp only [PqxdhLaterChallengeMonitor.Selected, PqxdhSelectedFirstRecord.frontOf,
    PqxdhSelectedFirstRecord.rolesOf_roles, RawCtxGenericRoleFamily.map_selected]
  cases found : RawCtxGenericRoleFamily.selectedKernel owner state.1.1.roles.1 <;> simp only [Option.map_none, Option.map_some, reduceCtorEq, false_implies, implies_true, Option.some.injEq, forall_eq']
  rfl

/-- A callback at its retained parent input cannot be selected at a distinct child input. The alias inequality and complete frontend projection are explicit. -/
theorem parent_unselected {A N C : Type} (key target : PqxdhSecretInputKdf.RootOutput)
    (owner : RawCtxProtocolReveals.Owner S B) (front : NativeFront M P I D K S B)
    (context : PqxdhInitialOriginContext.Context extra M P I D K Result Origin S B)
    (actual : AtAddress owner front context) (state : InsState M P I D K A N C S B)
    (displayed : PqxdhSelectedFirstRecord.frontOf key state.1.1 = front)
    (separate : RawCtxSelectedParentPrivatePatch.targetAddress target ≠ PqxdhInitialBuilderContext.address context.original) :
    ¬ PqxdhLaterChallengeMonitor.Selected target owner state := by
  intro selected
  obtain ⟨kernel, found, address⟩ := actual
  have chosen := (selected_projection key target owner state).mp selected
  rw [displayed] at chosen
  exact separate ((chosen kernel found).symm.trans address.symm)

/-- At an inside parent callback, the exact projected request state records false outside the parent/child alias event. This is not an exclusion of the original successful target event. -/
theorem inside_marker {A N C : Type} (key target : PqxdhSecretInputKdf.RootOutput)
    (owner : RawCtxProtocolReveals.Owner S B) (front : NativeFront M P I D K S B)
    (details : PqxdhLaterChallengeCapture.Details extra M P I D K Bool S B)
    (classified : PqxdhLaterChallengeSavedClassification.phase (some details) = .inside)
    (actual : AtAddress owner front details.callback) (state : InsState M P I D K A N C S B)
    (displayed : PqxdhSelectedFirstRecord.frontOf key state.1.1 = front)
    (separate : RawCtxSelectedParentPrivatePatch.targetAddress target ≠ PqxdhInitialBuilderContext.address details.callback.original) :
    PqxdhLaterChallengeMonitor.record target owner details.request.query details.request.before (state, none) = some false := by
  rw [PqxdhLaterChallengeSavedClassification.inside_record target owner details state classified]
  simp only [parent_unselected key target owner front details.callback actual state displayed separate, decide_false]

end BeaconcryptCore.Computational.PqxdhLaterChallengeInsideState

/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeInsideState.inside_shape' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeInsideState.inside_shape

/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeInsideState.cut_shape' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeInsideState.cut_shape

/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeInsideState.inside_address' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeInsideState.inside_address

/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeInsideState.cut_address' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeInsideState.cut_address

/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeInsideState.selected_projection' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeInsideState.selected_projection

/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeInsideState.parent_unselected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeInsideState.parent_unselected

/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeInsideState.inside_marker' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeInsideState.inside_marker
