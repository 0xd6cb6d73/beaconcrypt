import BeaconcryptCore.Computational.PqxdhLaterChallengeBuilderCapture

/-! The actual initial Builder emits its own descriptor with the literal continuation; later wrapper captures remain distinguished by their request metadata. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhLaterChallengeBuilderContinuation
open PqxdhInitialPostContext PqxdhInitialBuilderContext RawCtxForwardAnnotation RawCtxForwardTags
open PqxdhLaterChallengeCapture
variable {ι M P I D K X Response Shared Origin Result : Type} {extra : OracleSpec ι} {S B : Nat}

/-- Only the actually constructed Builder descriptor is constrained; all its source fields and private trace are retained. -/
noncomputable def BuilderOutside (outside : BuildResult → OracleComp (PostSpec extra S B) Result)
    (context : PqxdhInitialOriginContext.Context extra M P I D K Result Origin S B) : Prop :=
  ∃ saved, context.original = .inr saved ∧ saved.outside = outside

private theorem plain_all {Value Answer : Type}
    (predicate : PqxdhInitialOriginContext.Context extra M P I D K Result Origin S B → Prop)
    (client : OracleComp (Base extra RatchetChain I D K X Response Shared S B) Value)
    (after : Value → OracleComp (PqxdhInitialOriginForwardBuilder.Spec extra M P I D K X Response Shared Result Origin S B) Answer)
    (later : ∀ value, All predicate (after value)) :
    All predicate (simulateQ PqxdhInitialOriginForwardBuilder.plain client >>= after) := by
  induction client using OracleComp.inductionOn with
  | pure value => exact later value
  | query_bind query outside ih => exact ⟨(fun _ impossible => by cases impossible), fun reply => ih reply⟩

variable (mark : PqxdhBeaconPhase2Shared.Secrets Shared → Origin) (origin : Origin)
    (sender : M → U64) (route : RawCtxServerRouting.SenderDecoder) (read : RawCtxReceive.FrameDecoder)
    (index : Fin S) (before : NativeFront M P I D K S B) (trace : PqxdhInitialOriginPost.Trace Origin S B)

private theorem finished_pure
    (result : RustM (Option PqxdhServerRegistrationPublication.Response × PqxdhInitialOriginForwardBuilder.Publication M P)) :
    All (BuilderOutside (extra := extra) pure) (PqxdhInitialOriginForwardBuilder.finished (X := X) (Response := Response)
      mark origin sender route read index before trace pure result) := by
  trivial

private theorem publication_pure
    (candidate : pqxdh.ServerRegistrationCandidate) (authenticated : Pqxdh.Bytes) (metadata : P)
    (result : PqxdhInitialPendingPost.KernelOf RatchetChain × Option RawCtxSourceSend.Encrypted) :
    All (BuilderOutside (extra := extra) pure) (PqxdhInitialOriginForwardBuilder.publication (X := X) (Response := Response)
      mark origin sender route read index before trace candidate authenticated metadata pure result) := by
  exact plain_all _ _ _ (fun value => finished_pure mark origin sender route read index before trace (.ok value))

private theorem send_pure
    (candidate : pqxdh.ServerRegistrationCandidate) (authenticated : Pqxdh.Bytes) (metadata : P)
    (kernel : PqxdhInitialPendingPost.KernelOf RatchetChain) :
    All (BuilderOutside (extra := extra) pure) (PqxdhInitialOriginForwardBuilder.send (X := X) (Response := Response)
      mark origin sender route read index before trace candidate authenticated metadata pure kernel) := by
  unfold PqxdhInitialOriginForwardBuilder.send
  split
  case h_2 =>
    exact ⟨(fun tag same => by cases same; exact ⟨_, rfl, rfl⟩), fun reply =>
      ⟨(fun _ impossible => by cases impossible), fun sealed =>
        publication_pure mark origin sender route read index before trace candidate authenticated metadata _⟩⟩
  exact publication_pure mark origin sender route read index before trace candidate authenticated metadata _

private theorem candidate_pure
    (initial : RustM (PqxdhInitialPendingPost.KernelOf RatchetChain))
    (pending : pqxdh.ServerRegistrationCandidate) (data : Option Pqxdh.Bytes) (metadata : P) :
    All (BuilderOutside (extra := extra) pure) (PqxdhInitialOriginForwardBuilder.candidate (X := X) (Response := Response)
      mark origin sender route read index before trace initial pending data metadata pure) := by
  unfold PqxdhInitialOriginForwardBuilder.candidate
  refine plain_all _ _ _ fun valid => ?_
  cases valid <;> simp only [Bool.not_false, Bool.not_true, Bool.false_eq_true, ite_true, ite_false, finished_pure]
  refine plain_all _ _ _ fun reserved => ?_
  cases reserved <;> simp only [Bool.not_false, Bool.not_true, Bool.false_eq_true, ite_true, ite_false, finished_pure]
  cases initial <;> simp only [finished_pure]
  split <;> first | exact finished_pure mark origin sender route read index before trace _ | skip
  split <;> first | exact finished_pure mark origin sender route read index before trace _ | skip
  refine plain_all _ _ _ fun allocated => ?_
  cases allocated <;> simp only [Bool.not_false, Bool.not_true, Bool.false_eq_true, ite_true, ite_false, finished_pure]
  cases pending.key_id_binding <;> simp only [finished_pure, send_pure]

private theorem used_pure
    (initial : RustM (PqxdhInitialPendingPost.KernelOf RatchetChain))
    (pending : PqxdhRegistrationInputs.UsedInput) (data : Option Pqxdh.Bytes) (metadata : P) :
    All (BuilderOutside (extra := extra) pure) (PqxdhInitialOriginForwardBuilder.used (X := X) (Response := Response)
      mark origin sender route read index before trace initial pending data metadata pure) := by
  unfold PqxdhInitialOriginForwardBuilder.used
  dsimp only
  split <;> first | exact finished_pure mark origin sender route read index before trace _ | skip
  split <;> first | exact finished_pure mark origin sender route read index before trace _ | exact candidate_pure mark origin sender route read index before trace _ _ _ _

/-- Before the wrapper starts, the complete original Builder can save only its literal Builder continuation. Every admission, diagnostic and writer branch is retained. -/
theorem builder_pure (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (initial : RustM (PqxdhInitialPendingPost.KernelOf RatchetChain)) (metadata : P)
    (ready : PqxdhPrivateAcceptedRoot.Ready) :
    All (BuilderOutside (extra := extra) pure) (PqxdhInitialOriginForwardBuilder.program (X := X) (Response := Response)
      source mark origin sender route read initial index metadata ready pure before trace) := by
  exact used_pure mark origin sender route read index _ trace initial _ _ metadata

/-- Appending the original wrapper to an actual initial Builder retains that literal wrapper as its outside continuation. -/
theorem append_pure
    (next : BuildResult → OracleComp (PostSpec extra S B) Result)
    (context : PqxdhInitialOriginContext.Context extra M P I D K BuildResult Origin S B)
    (valid : BuilderOutside pure context) :
    BuilderOutside next (append next context) := by
  obtain ⟨saved, same, source⟩ := valid
  simp only [BuilderOutside, append, same, source, pure_bind]
  exact ⟨_, rfl, rfl⟩

/-- An absent request is the actual initial Builder with the original adversary continuation. A present request carries its exact callback and remaining wrapper. -/
noncomputable def Continuation (owner : RawCtxProtocolReveals.Owner S B) (number : U64) (bit : Bool)
    (adversary : BuildResult → OracleComp (PqxdhFirstRecordConfidentiality.AdvSpec extra S B) Bool)
    (tag : PqxdhInitialOriginContext.Context extra M P I D K Bool Origin S B × Option (Details extra M P I D K Origin S B)) : Prop :=
  match tag.2 with
  | none => BuilderOutside (fun reply => wrapped owner number bit (adversary reply) PqxdhRecordConfidentialityChallenge.initial) tag.1
  | some details => Joined owner number bit (tag.1, details)

/-- Every descriptor of the actual complete Builder and adaptive Post carries its source-generated continuation, including the initial Builder case with no wrapper request. -/
theorem captured_continuation (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (initial : RustM (PqxdhInitialPendingPost.KernelOf RatchetChain)) (metadata : P)
    (ready : PqxdhPrivateAcceptedRoot.Ready)
    (owner : RawCtxProtocolReveals.Owner S B) (number : U64) (bit : Bool)
    (adversary : BuildResult → OracleComp (PqxdhFirstRecordConfidentiality.AdvSpec extra S B) Bool) :
    All (Continuation owner number bit adversary)
      (PqxdhLaterChallengeBuilderCapture.capturedBuilder (X := X) (Response := Response) mark origin sender route read index before trace
        source initial metadata ready owner number bit adversary) := by
  unfold PqxdhLaterChallengeBuilderCapture.capturedBuilder
  refine bind_all _ _ _ ?_ ?_
  case refine_1 =>
    refine map_all (BuilderOutside pure) (Continuation owner number bit adversary) _ ?_ _
      (builder_pure mark origin sender route read index before trace source initial metadata ready)
    exact fun context valid => append_pure _ context valid
  exact fun value => map_all (Joined owner number bit) (Continuation owner number bit adversary)
    (fun context => (context.1, some context.2)) (fun _ valid => valid) _
    (captured_joined mark sender route read owner number bit (adversary value.1)
      PqxdhRecordConfidentialityChallenge.initial value.2.1 value.2.2)

/-- The complete shared-ROM scanner returns that exact source-generated Builder or wrapper continuation, including failed publication paths. -/
theorem shared_continuation {A N C : Type}
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
      (PqxdhLaterChallengeBuilderCapture.sharedCarried mark origin sender route read index before trace source writer stage pre application initializer selector aux
        initial metadata ready owner number bit adversary depth state)) :
    Continuation owner number bit adversary (context, details) := by
  exact shared_scan_all _ _ _ _ _ _ _
    (captured_continuation mark origin sender route read index before trace source initial metadata ready owner number bit adversary)
    _ _ _ supported


end BeaconcryptCore.Computational.PqxdhLaterChallengeBuilderContinuation

/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeBuilderContinuation.builder_pure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeBuilderContinuation.builder_pure
/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeBuilderContinuation.append_pure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeBuilderContinuation.append_pure
/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeBuilderContinuation.captured_continuation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeBuilderContinuation.captured_continuation
/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeBuilderContinuation.shared_continuation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeBuilderContinuation.shared_continuation
