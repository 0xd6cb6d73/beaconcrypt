import BeaconcryptCore.Computational.RawCtxForwardFirstCut
import BeaconcryptCore.Computational.PqxdhLaterChallengeGeneratedInside

/-! The original admitted challenge callback can stop only at its first KDF call, retaining the entire incoming source state and whole callback continuation. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhLaterChallengeInsideFirst
open PqxdhInitialPostContext RawCtxForwardTags RawCtxForwardFirstCut PqxdhFirstRecordConfidentiality
open PqxdhLaterChallengeInsideState (familySendRequest)
variable {ι M P I D K X Response Shared Result Origin : Type} {extra : OracleSpec ι} {S B : Nat}

private theorem owner_first {Metadata : Type} (sender : Std.U64) (read : RawCtxReceive.FrameDecoder)
    (before : RawCtxForwardOwner.Owner Metadata) (plaintext : Pqxdh.Bytes) :
    First (RawCtxForwardOwner.program sender read (RawCtxForwardOwner.SourceSpec.query (.inl (.inl plaintext))) before) := by
  change First (if plaintext.isEmpty then pure (none, before) else
    RawCtxForwardOwner.send before pure (fun result => pure (result.2, { before with kernel := result.1 }))
      (RawCtxChainSend.normalBegin before.kernel ⟨plaintext, before.expectedSender, sender, before.associatedData⟩))
  split
  · trivial
  · cases RawCtxChainSend.normalBegin before.kernel (⟨plaintext, before.expectedSender, sender, before.associatedData⟩ : RawCtxSourceSend.SealContext) with
    | exhausted entry context => trivial
    | requested pending => exact fun _ => ⟨(fun _ impossible => by cases impossible), fun _ => trivial⟩

private theorem server_first (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder)
    (read : RawCtxReceive.FrameDecoder) (before : RawCtxForwardServer.State M P) (plaintext : Pqxdh.Bytes) (peerId : Std.U64) :
    First (RawCtxForwardServer.program sender route read (RawCtxForwardServer.SourceSpec.query (.inl (plaintext, peerId))) before) := by
  change First (match before.server.peers peerId with
    | none => pure (none, before)
    | some peer => RawCtxForwardServer.owner sender read (.inl plaintext) before peerId peer pure
        (fun reply updated => pure (reply, updated)))
  cases before.server.peers peerId with
  | none => trivial
  | some peer =>
      simp only [RawCtxForwardServer.owner, bind_pure_comp]
      exact map_first _ _ (mapTags_first _ _ (owner_first _ _ _ _))

private theorem family_first (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder)
    (read : RawCtxReceive.FrameDecoder) (before : RawCtxForwardFamily.State M P I D K S B)
    (owner : RawCtxProtocolReveals.Owner S B) (plaintext : Pqxdh.Bytes) :
    First (RawCtxForwardFamily.program sender route read
      (liftM ((RawCtxForwardFamily.SourceSpec S B).query (familySendRequest owner plaintext))) before) := by
  cases owner with
  | server index peerId =>
      change First (RawCtxForwardFamily.server sender route read (.inl (plaintext, peerId)) before index pure
        (fun reply updated => pure (reply, updated)))
      simp only [RawCtxForwardFamily.server, bind_pure_comp]
      exact map_first _ _ (mapTags_first _ _ (server_first _ _ _ _ _ _))
  | beacon index =>
      change First (RawCtxForwardFamily.beacon read (.inl plaintext) before index pure
        (fun reply updated => pure (reply, updated)))
      cases active : (before.2 index).beacon.phase <;> simp only [RawCtxForwardFamily.beacon, active, bind_pure_comp]
      all_goals first | exact map_first _ _ (mapTags_first _ _ (owner_first _ _ _ _)) | trivial

private theorem live_first (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder)
    (read : RawCtxReceive.FrameDecoder) (before : RawCtxForwardLive.State M P I D K S B)
    (owner : RawCtxProtocolReveals.Owner S B) (plaintext : Pqxdh.Bytes) :
    First (RawCtxForwardLive.program sender route read (liftM ((RawCtxForwardLive.SourceSpec S B).query
      (LiveApplicationObservation.sendRequest owner plaintext))) before) := by
  have request : LiveApplicationObservation.sendRequest owner plaintext = .inl (familySendRequest owner plaintext) := by cases owner <;> rfl
  rw [request]
  change First (RawCtxForwardLive.family sender route read (familySendRequest owner plaintext) before pure
    (fun reply updated => pure (reply, updated)))
  simp only [RawCtxForwardLive.family, bind_pure_comp]
  exact map_first _ _ (lift_first _ _ (family_first _ _ _ _ _ _))

private theorem record_first (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder)
    (decode : RawCtxReceive.FrameDecoder) (owner : RawCtxProtocolReveals.Owner S B) (plaintext : Pqxdh.Bytes)
    (before : NativeFront M P I D K S B) (trace : PqxdhInitialOriginPost.Trace Origin S B)
    (outside : (RawCtxProtocolReveals.SourceSpec S B).Range (LiveApplicationObservation.sendRequest owner plaintext) →
      OracleComp (PostSpec extra S B) Result)
    (after : (RawCtxProtocolReveals.SourceSpec S B).Range (LiveApplicationObservation.sendRequest owner plaintext) →
      NativeFront M P I D K S B → PqxdhInitialOriginPost.Trace Origin S B →
        Result × (NativeFront M P I D K S B × PqxdhInitialOriginPost.Trace Origin S B)) :
    First (PqxdhInitialOriginForwardPost.record (X := X) (Response := Response) (Shared := Shared)
      sender route decode (LiveApplicationObservation.sendRequest owner plaintext) before trace outside
      (fun reply front history => pure (after reply front history))) := by
  simp only [PqxdhInitialOriginForwardPost.record, bind_pure_comp]
  exact map_first _ _ (lift_first _ _ (live_first _ _ _ _ _ _))

set_option backward.isDefEq.respectTransparency false in
private theorem challenge_first (mark : PqxdhBeaconPhase2Shared.Secrets Shared → Origin) (sender : M → Std.U64)
    (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (owner : RawCtxProtocolReveals.Owner S B) (number : Std.U64) (bit : Bool) (left right : Pqxdh.Bytes)
    (equal : left.length = right.length) (current : PqxdhRecordConfidentialityChallenge.State)
    (unused : current.pair = none) (before : NativeFront M P I D K S B) (trace : PqxdhInitialOriginPost.Trace Origin S B) :
    First (PqxdhInitialOriginForwardPost.program (X := X) (Response := Response) mark sender route decode
      ((PqxdhRecordConfidentialityChallenge.handler (extra := extra) owner number bit (.inr (left, right))).run current) before trace) := by
  rw [PqxdhRecordConfidentialityChallenge.challenge_step owner number bit left right equal current unused]
  rw [← bind_pure_comp]
  cases owner <;> simp only [PqxdhRecordConfidentialityChallenge.send, PqxdhRecordConfidentialityChallenge.sendRequest]
  all_goals rw [PqxdhInitialOriginForwardPost.program_query]
  case server index peer =>
    exact record_first sender route decode (.server index peer) (if bit then right else left) before trace _ _
  case beacon index =>
    exact record_first sender route decode (.beacon index) (if bit then right else left) before trace _ _

/-- Every admitted original challenge callback can carry a pending descriptor only at its first KDF query, through both source dispatch directions. -/
theorem inside_first (mark : PqxdhBeaconPhase2Shared.Secrets Shared → Origin) (sender : M → Std.U64)
    (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (owner : RawCtxProtocolReveals.Owner S B) (number : Std.U64) (bit : Bool)
    (details : PqxdhLaterChallengeCapture.Details extra M P I D K Origin S B)
    (classified : PqxdhLaterChallengeSavedClassification.phase (some details) = .inside)
    (before : NativeFront M P I D K S B) (trace : PqxdhInitialOriginPost.Trace Origin S B) :
    First (PqxdhInitialOriginForwardPost.program (X := X) (Response := Response) mark sender route decode
      ((PqxdhRecordConfidentialityChallenge.handler owner number bit details.request.query).run details.request.before) before trace) := by
  rcases details with ⟨⟨query, current, next⟩, callback⟩
  cases used : current.pair with
  | some pair => simp only [PqxdhLaterChallengeSavedClassification.phase, used, reduceCtorEq] at classified
  | none =>
      rcases query with request | ⟨left, right⟩
      · simp only [PqxdhLaterChallengeSavedClassification.phase, used, reduceCtorEq] at classified
      · by_cases equal : left.length = right.length
        · exact challenge_first mark sender route decode owner number bit left right equal current used before trace
        · simp only [PqxdhLaterChallengeSavedClassification.phase, used, equal, ite_false, reduceCtorEq] at classified


/-- The actual inside callback stops before any primitive execution. Its complete incoming state is unchanged and its saved frame is exactly the whole original callback program. -/
theorem cut_start {State : Type} (mark : PqxdhBeaconPhase2Shared.Secrets Shared → Origin) (sender : M → Std.U64)
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
    reached = state ∧
      (simulateQ (PqxdhInitialOriginPost.compiler (X := X) (Response := Response) mark sender route decode)
        ((PqxdhRecordConfidentialityChallenge.handler owner number bit details.request.query).run details.request.before)).run (front, trace) =
      (((Base extra RatchetChain I D K X Response Shared S B).query
        (PqxdhInitialOriginContext.frame mark sender route decode details.callback).1 : OracleComp (Base extra RatchetChain I D K X Response Shared S B) _) >>=
        (PqxdhInitialOriginContext.frame mark sender route decode details.callback).2) := by
  simpa only [PqxdhInitialOriginForwardPost.program_erase] using
    (RawCtxForwardFirstCut.cut_start PqxdhInitialForwardPost.selected selected selection impl
      (PqxdhInitialOriginContext.frame mark sender route decode) _ _
      (PqxdhInitialOriginForwardPost.program_sound mark sender route decode _ front trace)
      (inside_first mark sender route decode owner number bit details classified front trace) state reached details.callback cut)


end BeaconcryptCore.Computational.PqxdhLaterChallengeInsideFirst

/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeInsideFirst.inside_first' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeInsideFirst.inside_first
/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeInsideFirst.cut_start' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeInsideFirst.cut_start
