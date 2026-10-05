import BeaconcryptCore.Computational.PqxdhLaterChallengeCapture

/-! Retain the actual initial Builder and splice the captured adaptive wrapper after its original reply. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhLaterChallengeBuilderCapture
open PqxdhInitialPostContext PqxdhInitialBuilderContext RawCtxForwardAnnotation
open PqxdhLaterChallengeCapture
variable {ι M P I D K X Response Shared Origin Value Result : Type} {extra : OracleSpec ι} {S B : Nat}

private theorem map_plain {α : Type}
    (changeTag : PqxdhInitialOriginContext.Context extra M P I D K Value Origin S B →
      PqxdhInitialOriginContext.Context extra M P I D K Result Origin S B)
    (work : OracleComp (Base extra RatchetChain I D K X Response Shared S B) α) :
    mapTags changeTag (simulateQ PqxdhInitialOriginForwardBuilder.plain work) =
      simulateQ PqxdhInitialOriginForwardBuilder.plain work := by
  rw [mapTags, ← QueryImpl.simulateQ_compose]
  rfl

private noncomputable def continueWith
    (mark : PqxdhBeaconPhase2Shared.Secrets Shared → Origin)
    (sender : M → U64) (route : RawCtxServerRouting.SenderDecoder) (read : RawCtxReceive.FrameDecoder)
    (next : Value → OracleComp (PostSpec extra S B) Result)
    (work : OracleComp (PqxdhInitialOriginForwardBuilder.Spec extra M P I D K X Response Shared Value Origin S B)
      (Value × (NativeFront M P I D K S B × PqxdhInitialOriginPost.Trace Origin S B))) := do
  let result ← mapTags (append next) work
  PqxdhInitialOriginForwardPost.program mark sender route read (next result.1) result.2.1 result.2.2

private theorem continue_plain_bind {α : Type}
    (mark : PqxdhBeaconPhase2Shared.Secrets Shared → Origin)
    (sender : M → U64) (route : RawCtxServerRouting.SenderDecoder) (read : RawCtxReceive.FrameDecoder)
    (next : Value → OracleComp (PostSpec extra S B) Result)
    (work : OracleComp (Base extra RatchetChain I D K X Response Shared S B) α)
    (following : α → OracleComp (PqxdhInitialOriginForwardBuilder.Spec extra M P I D K X Response Shared Value Origin S B)
      (Value × (NativeFront M P I D K S B × PqxdhInitialOriginPost.Trace Origin S B))) :
    continueWith mark sender route read next (simulateQ PqxdhInitialOriginForwardBuilder.plain work >>= following) =
      simulateQ PqxdhInitialOriginForwardBuilder.plain work >>= fun reply => continueWith mark sender route read next (following reply) := by
  simp only [continueWith, mapTags, simulateQ_bind, bind_assoc, ← QueryImpl.simulateQ_compose]
  rfl

variable (mark : PqxdhBeaconPhase2Shared.Secrets Shared → Origin) (origin : Origin)
    (sender : M → U64) (route : RawCtxServerRouting.SenderDecoder) (read : RawCtxReceive.FrameDecoder)
    (index : Fin S) (before : NativeFront M P I D K S B) (trace : PqxdhInitialOriginPost.Trace Origin S B)
    (outside : BuildResult → OracleComp (PostSpec extra S B) Value)
    (next : Value → OracleComp (PostSpec extra S B) Result)

private theorem finished_append
    (result : RustM (Option PqxdhServerRegistrationPublication.Response × PqxdhInitialOriginForwardBuilder.Publication M P)) :
    continueWith mark sender route read next
      (PqxdhInitialOriginForwardBuilder.finished (X := X) (Response := Response) mark origin sender route read index before trace outside result) =
      PqxdhInitialOriginForwardBuilder.finished mark origin sender route read index before trace (fun reply => outside reply >>= next) result := by
  unfold continueWith PqxdhInitialOriginForwardBuilder.finished PqxdhInitialOriginForwardBuilder.post
  exact program_append mark sender route read _ next _ _

private theorem publication_append
    (candidate : pqxdh.ServerRegistrationCandidate) (authenticated : Pqxdh.Bytes) (metadata : P)
    (result : PqxdhInitialPendingPost.KernelOf RatchetChain × Option RawCtxSourceSend.Encrypted) :
    continueWith mark sender route read next
      (PqxdhInitialOriginForwardBuilder.publication (X := X) (Response := Response) mark origin sender route read index before trace candidate authenticated metadata outside result) =
      PqxdhInitialOriginForwardBuilder.publication mark origin sender route read index before trace candidate authenticated metadata (fun reply => outside reply >>= next) result := by
  simp only [PqxdhInitialOriginForwardBuilder.publication, continue_plain_bind, finished_append]

private theorem send_append
    (candidate : pqxdh.ServerRegistrationCandidate) (authenticated : Pqxdh.Bytes) (metadata : P)
    (kernel : PqxdhInitialPendingPost.KernelOf RatchetChain) :
    continueWith mark sender route read next
      (PqxdhInitialOriginForwardBuilder.send (X := X) (Response := Response) mark origin sender route read index before trace candidate authenticated metadata outside kernel) =
      PqxdhInitialOriginForwardBuilder.send mark origin sender route read index before trace candidate authenticated metadata (fun reply => outside reply >>= next) kernel := by
  unfold PqxdhInitialOriginForwardBuilder.send
  split
  · exact publication_append mark origin sender route read index before trace outside next _ _ _ _
  · simp only [continueWith, mapTags, simulateQ_bind, simulateQ_spec_query, bind_assoc]
    exact bind_congr fun reply => bind_congr fun sealed =>
      publication_append mark origin sender route read index before trace outside next _ _ _ _

private theorem candidate_append
    (initial : RustM (PqxdhInitialPendingPost.KernelOf RatchetChain))
    (pending : pqxdh.ServerRegistrationCandidate) (data : Option Pqxdh.Bytes) (metadata : P) :
    continueWith mark sender route read next
      (PqxdhInitialOriginForwardBuilder.candidate (X := X) (Response := Response) mark origin sender route read index before trace initial pending data metadata outside) =
      PqxdhInitialOriginForwardBuilder.candidate mark origin sender route read index before trace initial pending data metadata (fun reply => outside reply >>= next) := by
  simp only [PqxdhInitialOriginForwardBuilder.candidate, continue_plain_bind]
  refine bind_congr fun valid => ?_
  cases valid <;> simp only [Bool.not_false, Bool.not_true, Bool.false_eq_true, ite_true, ite_false, finished_append, continue_plain_bind]
  refine bind_congr fun reserved => ?_
  cases reserved <;> simp only [Bool.not_false, Bool.not_true, Bool.false_eq_true, ite_true, ite_false, finished_append]
  cases initial <;> simp only [finished_append]
  split
  · exact finished_append mark origin sender route read index before trace outside next _
  · split
    · rw [continue_plain_bind]
      refine bind_congr fun allocated => ?_
      cases allocated <;> simp only [Bool.not_false, Bool.not_true, Bool.false_eq_true, ite_true, ite_false, finished_append]
      cases pending.key_id_binding <;> simp only [finished_append, send_append]
    · exact finished_append mark origin sender route read index before trace outside next _

private theorem used_append
    (initial : RustM (PqxdhInitialPendingPost.KernelOf RatchetChain))
    (pending : PqxdhRegistrationInputs.UsedInput) (data : Option Pqxdh.Bytes) (metadata : P) :
    continueWith mark sender route read next
      (PqxdhInitialOriginForwardBuilder.used (X := X) (Response := Response) mark origin sender route read index before trace initial pending data metadata outside) =
      PqxdhInitialOriginForwardBuilder.used mark origin sender route read index before trace initial pending data metadata (fun reply => outside reply >>= next) := by
  unfold PqxdhInitialOriginForwardBuilder.used
  dsimp only
  split
  all_goals first
    | exact finished_append mark origin sender route read index before trace outside next _
    | split <;> first
      | exact finished_append mark origin sender route read index before trace outside next _
      | exact candidate_append mark origin sender route read index before trace outside next _ _ _ _

/-- Every initial Builder path splices the actual outside continuation before the same annotated Post program. The complete query tree, optional publication and installation trace are unchanged. -/
theorem builder_append (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (initial : RustM (PqxdhInitialPendingPost.KernelOf RatchetChain)) (metadata : P)
    (ready : PqxdhPrivateAcceptedRoot.Ready) :
    (do let result ← mapTags (append next)
          (PqxdhInitialOriginForwardBuilder.program (X := X) (Response := Response) source mark origin sender route read initial index metadata ready outside before trace)
        PqxdhInitialOriginForwardPost.program mark sender route read (next result.1) result.2.1 result.2.2) =
      PqxdhInitialOriginForwardBuilder.program source mark origin sender route read initial index metadata ready (fun reply => outside reply >>= next) before trace := by
  unfold PqxdhInitialOriginForwardBuilder.program
  exact used_append mark origin sender route read _ _ trace outside next _ _ _ _

/-- The initial Builder is retained literally. A later descriptor additionally carries the actual wrapper request, while an initial Builder descriptor is explicitly distinguished. -/
noncomputable def capturedBuilder (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (initial : RustM (PqxdhInitialPendingPost.KernelOf RatchetChain)) (metadata : P)
    (ready : PqxdhPrivateAcceptedRoot.Ready)
    (owner : RawCtxProtocolReveals.Owner S B) (number : U64) (bit : Bool)
    (adversary : BuildResult → OracleComp (PqxdhFirstRecordConfidentiality.AdvSpec extra S B) Bool) :
    OracleComp (RawCtxForwardAnnotation.Spec
      (PqxdhInitialOriginContext.Context extra M P I D K Bool Origin S B × Option (Details extra M P I D K Origin S B))
      (Base extra RatchetChain I D K X Response Shared S B))
      (Bool × (NativeFront M P I D K S B × PqxdhInitialOriginPost.Trace Origin S B)) := do
  let built ← mapTags
    (fun context => (append (fun reply => wrapped owner number bit (adversary reply) PqxdhRecordConfidentialityChallenge.initial) context, none))
    (PqxdhInitialOriginForwardBuilder.program source mark origin sender route read initial index metadata ready pure before trace)
  mapTags (fun context => (context.1, some context.2))
    (captured mark sender route read owner number bit (adversary built.1) PqxdhRecordConfidentialityChallenge.initial built.2.1 built.2.2)

/-- Erasing the generated capture yields the original complete Builder and literal left-or-right Post wrapper as an exact annotated program equality. -/
theorem builder_erase (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (initial : RustM (PqxdhInitialPendingPost.KernelOf RatchetChain)) (metadata : P)
    (ready : PqxdhPrivateAcceptedRoot.Ready)
    (owner : RawCtxProtocolReveals.Owner S B) (number : U64) (bit : Bool)
    (adversary : BuildResult → OracleComp (PqxdhFirstRecordConfidentiality.AdvSpec extra S B) Bool) :
    mapTags Prod.fst (capturedBuilder (X := X) (Response := Response) mark origin sender route read index before trace source initial metadata ready owner number bit adversary) =
      PqxdhInitialOriginForwardBuilder.program source mark origin sender route read initial index metadata ready
        (fun reply => wrapped owner number bit (adversary reply) PqxdhRecordConfidentialityChallenge.initial) before trace := by
  simp only [capturedBuilder, tags_bind, tags_compose]
  change (do
    let built ← mapTags (append (fun reply => wrapped owner number bit (adversary reply) PqxdhRecordConfidentialityChallenge.initial))
      (PqxdhInitialOriginForwardBuilder.program source mark origin sender route read initial index metadata ready pure before trace)
    mapTags Prod.fst (captured mark sender route read owner number bit (adversary built.1)
      PqxdhRecordConfidentialityChallenge.initial built.2.1 built.2.2)) = _
  simp only [captured_erase]
  exact builder_append mark origin sender route read index before trace pure
    (fun reply => wrapped owner number bit (adversary reply) PqxdhRecordConfidentialityChallenge.initial)
    source initial metadata ready

/-- Coverage is supplied by exact erasure to the existing Builder compiler, for every possible source reply. -/
theorem builder_covered (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (initial : RustM (PqxdhInitialPendingPost.KernelOf RatchetChain)) (metadata : P)
    (ready : PqxdhPrivateAcceptedRoot.Ready)
    (owner : RawCtxProtocolReveals.Owner S B) (number : U64) (bit : Bool)
    (adversary : BuildResult → OracleComp (PqxdhFirstRecordConfidentiality.AdvSpec extra S B) Bool) :
    RawCtxForwardCoverage.Covered PqxdhInitialForwardPost.selected
      (capturedBuilder (X := X) (Response := Response) mark origin sender route read index before trace source initial metadata ready owner number bit adversary) := by
  rw [← covered_tags Prod.fst, builder_erase]
  exact PqxdhInitialOriginForwardBuilder.program_covered source mark origin sender route read initial index metadata ready _ before trace

private theorem carriedSelection {A N C : Type} (depth : Nat)
    (query : (Base extra RatchetChain I D K X Response Shared S B).Domain)
    (state : PqxdhInitialNativeLog.State A N C)
    (chosen : PqxdhInitialNativePrefix.selected (extra := extra) depth query state = true) :
    PqxdhInitialForwardPost.selected query = true := by
  cases query with
  | inl query => exact RawCtxFirstParentPrefix.selected_private depth query state.1 chosen
  | inr query => cases chosen

/-- Execute the unchanged carried-prefix scanner over the constructed wrapper captures and the original complete native callback interpreter. -/
noncomputable def capturedCarried {A N C : Type}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (initial : RustM (PqxdhInitialPendingPost.KernelOf RatchetChain)) (metadata : P)
    (ready : PqxdhPrivateAcceptedRoot.Ready)
    (owner : RawCtxProtocolReveals.Owner S B) (number : U64) (bit : Bool)
    (adversary : BuildResult → OracleComp (PqxdhFirstRecordConfidentiality.AdvSpec extra S B) Bool)
    (depth stage : Nat)
    (external : QueryImpl (PqxdhInitialNativeLog.External extra RatchetChain I D K X Response Shared)
      (PqxdhInitialBeaconAmbient.Ambient A N C)) (state : PqxdhInitialNativeLog.State A N C) :=
  RawCtxForwardScan.scan PqxdhInitialForwardPost.selected (PqxdhInitialNativePrefix.selected (extra := extra) depth)
    (carriedSelection depth) (PqxdhInitialNativeLog.handler source writer stage external)
    (capturedBuilder mark origin sender route read index before trace source initial metadata ready owner number bit adversary)
    (builder_covered mark origin sender route read index before trace source initial metadata ready owner number bit adversary) state

/-- The original actual carried sampler is the exact metadata projection of the captured sampler, preserving complete and pending branches and the entire reached native state. -/
theorem carried_erase {A N C : Type}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (initial : RustM (PqxdhInitialPendingPost.KernelOf RatchetChain)) (metadata : P)
    (ready : PqxdhPrivateAcceptedRoot.Ready)
    (owner : RawCtxProtocolReveals.Owner S B) (number : U64) (bit : Bool)
    (adversary : BuildResult → OracleComp (PqxdhFirstRecordConfidentiality.AdvSpec extra S B) Bool)
    (depth stage : Nat)
    (external : QueryImpl (PqxdhInitialNativeLog.External extra RatchetChain I D K X Response Shared)
      (PqxdhInitialBeaconAmbient.Ambient A N C)) (state : PqxdhInitialNativeLog.State A N C) :
    cutMap Prod.fst <$> capturedCarried mark origin sender route read index before trace source writer initial metadata ready owner number bit adversary depth stage external state =
      PqxdhInitialNativeCarried.carried source writer mark sender route read
        ⟨initial, index, metadata, ready,
          (fun reply => wrapped owner number bit (adversary reply) PqxdhRecordConfidentialityChallenge.initial), before, trace, origin⟩
        depth stage external state := by
  unfold capturedCarried PqxdhInitialNativeCarried.carried PqxdhInitialNativeCarried.code
  rw [native_scan_tags]
  simp only [builder_erase]

/-- The same captured source scanner uses the original shared-ROM callback compiler, retaining its local audit and private state. -/
noncomputable def sharedCarried {A N C : Type}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (stage : Nat)
    (pre : QueryImpl (PqxdhBeaconPhase2Shared.Spec I D K X Response Shared)
      (StateT (PqxdhNativeSharedPrefix.ExternalState A N C) ProbComp))
    (application : Response → PqxdhNativeSharedPrefix.LocalCallback A N C (Option Pqxdh.Bytes))
    (initializer : PqxdhBeaconPhase2Shared.Secrets Shared →
      PqxdhNativeSharedPrefix.LocalCallback A N C PqxdhInitialNativeAudit.InitialReply)
    (selector : QueryImpl extra (StateT (PqxdhNativeSharedPrefix.ExternalState A N C) ProbComp))
    (aux : QueryImpl PqxdhServerRegistrationPublication.AuxSpec (StateT (PqxdhNativeSharedPrefix.ExternalState A N C) ProbComp))
    (initial : RustM (PqxdhInitialPendingPost.KernelOf RatchetChain)) (metadata : P)
    (ready : PqxdhPrivateAcceptedRoot.Ready)
    (owner : RawCtxProtocolReveals.Owner S B) (number : U64) (bit : Bool)
    (adversary : BuildResult → OracleComp (PqxdhFirstRecordConfidentiality.AdvSpec extra S B) Bool)
    (depth : Nat) (state : PqxdhNativeSharedPrefix.Local A N C) :=
  RawCtxSharedPrefixScan.scan PqxdhInitialForwardPost.selected (PqxdhNativeSharedPrefix.selected depth)
    (fun query state chosen => PqxdhNativeSharedPrefix.native_selection depth query (PqxdhNativeSharedPrefix.attach state ∅) chosen)
    (PqxdhNativeSharedPrefix.compiler source writer stage pre application initializer selector aux)
    (capturedBuilder mark origin sender route read index before trace source initial metadata ready owner number bit adversary)
    (builder_covered mark origin sender route read index before trace source initial metadata ready owner number bit adversary) state

/-- Metadata erasure commutes with the full shared source sampler before any ROM evaluation or projection of private state. -/
theorem shared_erase {A N C : Type}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (stage : Nat)
    (pre : QueryImpl (PqxdhBeaconPhase2Shared.Spec I D K X Response Shared)
      (StateT (PqxdhNativeSharedPrefix.ExternalState A N C) ProbComp))
    (application : Response → PqxdhNativeSharedPrefix.LocalCallback A N C (Option Pqxdh.Bytes))
    (initializer : PqxdhBeaconPhase2Shared.Secrets Shared →
      PqxdhNativeSharedPrefix.LocalCallback A N C PqxdhInitialNativeAudit.InitialReply)
    (selector : QueryImpl extra (StateT (PqxdhNativeSharedPrefix.ExternalState A N C) ProbComp))
    (aux : QueryImpl PqxdhServerRegistrationPublication.AuxSpec (StateT (PqxdhNativeSharedPrefix.ExternalState A N C) ProbComp))
    (initial : RustM (PqxdhInitialPendingPost.KernelOf RatchetChain)) (metadata : P)
    (ready : PqxdhPrivateAcceptedRoot.Ready)
    (owner : RawCtxProtocolReveals.Owner S B) (number : U64) (bit : Bool)
    (adversary : BuildResult → OracleComp (PqxdhFirstRecordConfidentiality.AdvSpec extra S B) Bool)
    (depth : Nat) (state : PqxdhNativeSharedPrefix.Local A N C) :
    cutMap Prod.fst <$> sharedCarried mark origin sender route read index before trace source writer stage pre application initializer selector aux
      initial metadata ready owner number bit adversary depth state =
      PqxdhNativeSharedPrefix.carried source writer stage pre application initializer selector aux mark sender route read
        ⟨initial, index, metadata, ready,
          (fun reply => wrapped owner number bit (adversary reply) PqxdhRecordConfidentialityChallenge.initial), before, trace, origin⟩
        depth state := by
  unfold sharedCarried PqxdhNativeSharedPrefix.carried PqxdhInitialNativeCarried.code
  rw [scan_tags]
  simp only [builder_erase]

/-- An initial Builder cut has no wrapper request; every later cut carries the callback-local descriptor composed with its actual remaining wrapper. -/
noncomputable def JoinedCapture (owner : RawCtxProtocolReveals.Owner S B) (number : U64) (bit : Bool)
    (tag : PqxdhInitialOriginContext.Context extra M P I D K Bool Origin S B × Option (Details extra M P I D K Origin S B)) : Prop :=
  match tag.2 with
  | none => True
  | some details => Joined owner number bit (tag.1, details)

/-- The complete original Builder and adaptive wrapper establish descriptor composition before scanning or interpreting any callback. -/
theorem builder_joined (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (initial : RustM (PqxdhInitialPendingPost.KernelOf RatchetChain)) (metadata : P)
    (ready : PqxdhPrivateAcceptedRoot.Ready)
    (owner : RawCtxProtocolReveals.Owner S B) (number : U64) (bit : Bool)
    (adversary : BuildResult → OracleComp (PqxdhFirstRecordConfidentiality.AdvSpec extra S B) Bool) :
    RawCtxForwardTags.All (JoinedCapture owner number bit)
      (capturedBuilder (X := X) (Response := Response) mark origin sender route read index before trace source initial metadata ready owner number bit adversary) := by
  unfold capturedBuilder
  refine RawCtxForwardTags.bind_all _ _ _ ?_ ?_
  · refine RawCtxForwardTags.map_all (fun _ => True) (JoinedCapture owner number bit) _ ?_ _ (all_true _)
    intro context _
    trivial
  · intro result
    refine RawCtxForwardTags.map_all (Joined owner number bit) (JoinedCapture owner number bit) _ ?_ _
      (captured_joined mark sender route read owner number bit (adversary result.1) PqxdhRecordConfidentialityChallenge.initial result.2.1 result.2.2)
    intro context valid
    exact valid

/-- Every supported shared-ROM cut carries the actual Builder-or-wrapper composition certificate supplied by the source syntax. -/
theorem shared_joined {A N C : Type}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (stage : Nat)
    (pre : QueryImpl (PqxdhBeaconPhase2Shared.Spec I D K X Response Shared)
      (StateT (PqxdhNativeSharedPrefix.ExternalState A N C) ProbComp))
    (application : Response → PqxdhNativeSharedPrefix.LocalCallback A N C (Option Pqxdh.Bytes))
    (initializer : PqxdhBeaconPhase2Shared.Secrets Shared →
      PqxdhNativeSharedPrefix.LocalCallback A N C PqxdhInitialNativeAudit.InitialReply)
    (selector : QueryImpl extra (StateT (PqxdhNativeSharedPrefix.ExternalState A N C) ProbComp))
    (aux : QueryImpl PqxdhServerRegistrationPublication.AuxSpec (StateT (PqxdhNativeSharedPrefix.ExternalState A N C) ProbComp))
    (initial : RustM (PqxdhInitialPendingPost.KernelOf RatchetChain)) (metadata : P)
    (ready : PqxdhPrivateAcceptedRoot.Ready)
    (owner : RawCtxProtocolReveals.Owner S B) (number : U64) (bit : Bool)
    (adversary : BuildResult → OracleComp (PqxdhFirstRecordConfidentiality.AdvSpec extra S B) Bool)
    (depth : Nat) (state : PqxdhNativeSharedPrefix.Local A N C)
    (context : PqxdhInitialOriginContext.Context extra M P I D K Bool Origin S B)
    (details : Option (Details extra M P I D K Origin S B)) (reached : PqxdhNativeSharedPrefix.Local A N C)
    (supported : RawCtxForwardScan.Cut.pending (context, details) reached ∈ support
      (sharedCarried mark origin sender route read index before trace source writer stage pre application initializer selector aux
        initial metadata ready owner number bit adversary depth state)) :
    JoinedCapture owner number bit (context, details) := by
  exact shared_scan_all _ _ _ _ _ _ _
    (builder_joined mark origin sender route read index before trace source initial metadata ready owner number bit adversary)
    _ _ _ supported

end BeaconcryptCore.Computational.PqxdhLaterChallengeBuilderCapture

/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeBuilderCapture.builder_append' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeBuilderCapture.builder_append
/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeBuilderCapture.builder_erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeBuilderCapture.builder_erase
/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeBuilderCapture.builder_covered' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeBuilderCapture.builder_covered
/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeBuilderCapture.carried_erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeBuilderCapture.carried_erase
/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeBuilderCapture.shared_erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeBuilderCapture.shared_erase
/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeBuilderCapture.builder_joined' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeBuilderCapture.builder_joined
/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeBuilderCapture.shared_joined' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeBuilderCapture.shared_joined
