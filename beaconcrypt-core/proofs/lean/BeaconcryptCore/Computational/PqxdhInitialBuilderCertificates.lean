import BeaconcryptCore.Computational.PqxdhInitialPostCertificates
import BeaconcryptCore.Computational.PqxdhInitialForwardBuilder
import BeaconcryptCore.Computational.RawCtxForwardCosts

/-!
The complete accepted builder constructs each pending descriptor together with the same original outside post allowance. Its first-send descriptor retains the actual bounded post continuation; all later descriptors inherit the checked post certificate. The original seven builder callbacks and sixty-seven callbacks per post request also bound the annotated syntax without hiding descriptor construction as free local work.
-/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.refined ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhInitialBuilderCertificates
open PqxdhInitialPostContext PqxdhInitialBuilderContext RawCtxForwardTags
variable {ι M P I D K X Response Shared Result : Type} {extra : OracleSpec ι} {S B : Nat}

def Fits (qPost : Nat) : PqxdhInitialBuilderContext.Context extra M P I D K Result S B → Prop
  | .inl context => PqxdhInitialPostCertificates.Fits qPost context
  | .inr context => ∀ reply, (context.outside reply).IsTotalQueryBound qPost

private theorem post_fits (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder)
    (decode : RawCtxReceive.FrameDecoder) (client : OracleComp (PostSpec extra S B) Result)
    (qPost : Nat) (bounded : client.IsTotalQueryBound qPost) (before : NativeFront M P I D K S B) :
    All (Fits qPost) (PqxdhInitialForwardBuilder.post (X := X) (Response := Response) (Shared := Shared)
      sender route decode client before) := by
  exact map_all (PqxdhInitialPostCertificates.Fits qPost) (Fits qPost) Sum.inl (fun _ valid => valid) _
    (PqxdhInitialPostCertificates.program_fits sender route decode client qPost bounded before)

private theorem finished_fits (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder)
    (decode : RawCtxReceive.FrameDecoder) (index : Fin S) (before : NativeFront M P I D K S B)
    (outside : BuildResult → OracleComp (PostSpec extra S B) Result)
    (qPost : Nat) (bounded : ∀ reply, (outside reply).IsTotalQueryBound qPost)
    (result : RustM (Option PqxdhServerRegistrationPublication.Response × PqxdhInitialForwardBuilder.Publication M P)) :
    All (Fits qPost) (PqxdhInitialForwardBuilder.finished (X := X) (Response := Response) (Shared := Shared)
      sender route decode index before outside result) :=
  post_fits sender route decode _ qPost (bounded _) _

private theorem plain_fits {Value : Type}
    (client : OracleComp (Base extra RatchetChain I D K X Response Shared S B) Value)
    (after : Value → OracleComp (PqxdhInitialForwardBuilder.Spec extra M P I D K X Response Shared Result S B)
      (Result × NativeFront M P I D K S B))
    (qPost : Nat) (later : ∀ value, All (Fits qPost) (after value)) :
    All (Fits qPost) (simulateQ PqxdhInitialForwardBuilder.plain client >>= after) := by
  induction client using OracleComp.inductionOn with
  | pure value => exact later value
  | query_bind query outside ih =>
      exact ⟨(fun _ impossible => by cases impossible), fun reply => ih reply⟩

private theorem publication_fits (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder)
    (decode : RawCtxReceive.FrameDecoder) (index : Fin S) (before : NativeFront M P I D K S B)
    (candidate : pqxdh.ServerRegistrationCandidate) (authenticated : Pqxdh.Bytes) (metadata : P)
    (outside : BuildResult → OracleComp (PostSpec extra S B) Result)
    (qPost : Nat) (bounded : ∀ reply, (outside reply).IsTotalQueryBound qPost)
    (result : PqxdhInitialPendingPost.KernelOf RatchetChain × Option RawCtxSourceSend.Encrypted) :
    All (Fits qPost) (PqxdhInitialForwardBuilder.publication (X := X) (Response := Response) (Shared := Shared)
      sender route decode index before candidate authenticated metadata outside result) := by
  apply plain_fits
  exact fun value => finished_fits sender route decode index before outside qPost bounded (.ok value)

private theorem send_fits (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder)
    (decode : RawCtxReceive.FrameDecoder) (index : Fin S) (before : NativeFront M P I D K S B)
    (candidate : pqxdh.ServerRegistrationCandidate) (authenticated : Pqxdh.Bytes) (metadata : P)
    (outside : BuildResult → OracleComp (PostSpec extra S B) Result)
    (qPost : Nat) (bounded : ∀ reply, (outside reply).IsTotalQueryBound qPost)
    (kernel : PqxdhInitialPendingPost.KernelOf RatchetChain) :
    All (Fits qPost) (PqxdhInitialForwardBuilder.send (X := X) (Response := Response) (Shared := Shared)
      sender route decode index before candidate authenticated metadata outside kernel) := by
  unfold PqxdhInitialForwardBuilder.send
  cases start : RawCtxChainSend.normalBegin kernel (PqxdhServerRegistrationPublication.firstContext candidate authenticated) with
  | exhausted entry context => exact publication_fits sender route decode index before candidate authenticated metadata outside qPost bounded _
  | requested pending =>
      exact ⟨(fun tag same => by cases same; exact bounded), fun reply =>
        ⟨(fun _ impossible => by cases impossible), fun sealed =>
          publication_fits sender route decode index before candidate authenticated metadata outside qPost bounded _⟩⟩

private theorem candidate_fits (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder)
    (decode : RawCtxReceive.FrameDecoder) (index : Fin S) (before : NativeFront M P I D K S B)
    (initial : RustM (PqxdhInitialPendingPost.KernelOf RatchetChain))
    (candidate : pqxdh.ServerRegistrationCandidate) (data : Option Pqxdh.Bytes) (metadata : P)
    (outside : BuildResult → OracleComp (PostSpec extra S B) Result)
    (qPost : Nat) (bounded : ∀ reply, (outside reply).IsTotalQueryBound qPost) :
    All (Fits qPost) (PqxdhInitialForwardBuilder.candidate (X := X) (Response := Response) (Shared := Shared)
      sender route decode index before initial candidate data metadata outside) := by
  unfold PqxdhInitialForwardBuilder.candidate
  apply plain_fits
  intro valid
  cases valid
  · exact finished_fits sender route decode index before outside qPost bounded _
  · simp only [Bool.not_true, Bool.false_eq_true, if_false]
    apply plain_fits
    intro reserved
    cases reserved
    · exact finished_fits sender route decode index before outside qPost bounded _
    · simp only [Bool.not_true, Bool.false_eq_true, if_false]
      cases initial with
      | fail error => exact finished_fits sender route decode index before outside qPost bounded _
      | div => exact finished_fits sender route decode index before outside qPost bounded _
      | ok kernel =>
          dsimp only
          split
          · exact finished_fits sender route decode index before outside qPost bounded _
          · split
            · apply plain_fits
              intro allocated
              cases allocated
              · exact finished_fits sender route decode index before outside qPost bounded _
              · simp only [Bool.not_true, Bool.false_eq_true, if_false]
                cases binding : candidate.key_id_binding with
                | fail error => exact finished_fits sender route decode index before outside qPost bounded _
                | div => exact finished_fits sender route decode index before outside qPost bounded _
                | ok binding => exact send_fits sender route decode index before candidate _ metadata outside qPost bounded kernel
            · exact finished_fits sender route decode index before outside qPost bounded _

private theorem used_fits (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder)
    (decode : RawCtxReceive.FrameDecoder) (index : Fin S) (before : NativeFront M P I D K S B)
    (initial : RustM (PqxdhInitialPendingPost.KernelOf RatchetChain))
    (pending : PqxdhRegistrationInputs.UsedInput) (data : Option Pqxdh.Bytes) (metadata : P)
    (outside : BuildResult → OracleComp (PostSpec extra S B) Result)
    (qPost : Nat) (bounded : ∀ reply, (outside reply).IsTotalQueryBound qPost) :
    All (Fits qPost) (PqxdhInitialForwardBuilder.used (X := X) (Response := Response) (Shared := Shared)
      sender route decode index before initial pending data metadata outside) := by
  unfold PqxdhInitialForwardBuilder.used
  dsimp only
  cases nextResult : pqxdh.server_next_key_id (PqxdhInitialPendingBuilder.selected sender index before).control with
  | fail error => exact finished_fits sender route decode index before outside qPost bounded _
  | div => exact finished_fits sender route decode index before outside qPost bounded _
  | ok value =>
      cases value with
      | Err error => exact finished_fits sender route decode index before outside qPost bounded _
      | Ok key =>
          dsimp only
          cases preparation : PqxdhRegistrationInputs.prepare
            (PqxdhInitialPendingBuilder.selected sender index before).control pending
            ⟨(PqxdhInitialPendingBuilder.selected sender index before).server.identity,
              (PqxdhInitialPendingBuilder.selected sender index before).identityKeyId⟩
            (if ((PqxdhInitialPendingBuilder.selected sender index before).server.peers key).isSome
              then pqxdh.KeyIdAvailability.Occupied else .Available) with
          | fail error => exact finished_fits sender route decode index before outside qPost bounded _
          | div => exact finished_fits sender route decode index before outside qPost bounded _
          | ok prepared =>
              cases prepared with
              | Err error => exact finished_fits sender route decode index before outside qPost bounded _
              | Ok prepared => exact candidate_fits sender route decode index before initial prepared data metadata outside qPost bounded

/-- Every descriptor in the complete accepted builder and post source retains its actual original outside allowance, including the first private send before publication. -/
theorem program_fits (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (initial : RustM (PqxdhInitialPendingPost.KernelOf RatchetChain)) (index : Fin S) (metadata : P)
    (ready : PqxdhPrivateAcceptedRoot.Ready) (outside : BuildResult → OracleComp (PostSpec extra S B) Result)
    (qPost : Nat) (bounded : ∀ reply, (outside reply).IsTotalQueryBound qPost)
    (before : NativeFront M P I D K S B) :
    All (Fits qPost) (PqxdhInitialForwardBuilder.program (X := X) (Response := Response) (Shared := Shared)
      source sender route decode initial index metadata ready outside before) :=
  used_fits sender route decode index _ initial _ ready.application metadata outside qPost bounded

/-- The annotated source has exactly the original callback bill; retaining finite descriptors is still explicit local bookkeeping rather than free computation. -/
theorem program_total (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (initial : RustM (PqxdhInitialPendingPost.KernelOf RatchetChain)) (index : Fin S) (metadata : P)
    (ready : PqxdhPrivateAcceptedRoot.Ready) (outside : BuildResult → OracleComp (PostSpec extra S B) Result)
    (qPost : Nat) (bounded : ∀ reply, (outside reply).IsTotalQueryBound qPost)
    (before : NativeFront M P I D K S B) :
    (PqxdhInitialForwardBuilder.program (X := X) (Response := Response) (Shared := Shared)
      source sender route decode initial index metadata ready outside before).IsTotalQueryBound (7 + qPost * 67) := by
  apply (isQueryBoundP_true_iff _ _).mp
  apply (RawCtxForwardCosts.erase_class (fun _ => True) _ _).mp
  rw [PqxdhInitialForwardBuilder.program_erase]
  exact (PqxdhInitialPendingSourceBounds.sequence_total source initial sender route decode index metadata ready outside qPost bounded before).isQueryBoundP

/-- A supported scan through the actual first builder and every later post operation returns its own source-bounded descriptor. -/
theorem carried_fits {State : Type}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (initialKernel : RustM (PqxdhInitialPendingPost.KernelOf RatchetChain)) (index : Fin S) (metadata : P)
    (ready : PqxdhPrivateAcceptedRoot.Ready) (outside : BuildResult → OracleComp (PostSpec extra S B) Result)
    (qPost : Nat) (bounded : ∀ reply, (outside reply).IsTotalQueryBound qPost)
    (before : NativeFront M P I D K S B)
    (chosen : (Base extra RatchetChain I D K X Response Shared S B).Domain → State → Bool)
    (selection : ∀ query state, chosen query state = true → PqxdhInitialForwardPost.selected query = true)
    (impl : QueryImpl (Base extra RatchetChain I D K X Response Shared S B) (StateT State ProbComp))
    (initial reached : State) (context : PqxdhInitialBuilderContext.Context extra M P I D K Result S B)
    (supported : RawCtxForwardScan.Cut.pending context reached ∈ support
      (RawCtxForwardScan.scan PqxdhInitialForwardPost.selected chosen selection impl
        (PqxdhInitialForwardBuilder.program source sender route decode initialKernel index metadata ready outside before)
        (PqxdhInitialForwardBuilder.program_covered source sender route decode initialKernel index metadata ready outside before) initial)) :
    Fits qPost context :=
  scan_all PqxdhInitialForwardPost.selected chosen selection impl (Fits qPost) _
    (PqxdhInitialForwardBuilder.program_covered source sender route decode initialKernel index metadata ready outside before)
    (program_fits source sender route decode initialKernel index metadata ready outside qPost bounded before)
    initial reached context supported

end BeaconcryptCore.Computational.PqxdhInitialBuilderCertificates

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialBuilderCertificates.program_fits' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialBuilderCertificates.program_fits
/-- info: 'BeaconcryptCore.Computational.PqxdhInitialBuilderCertificates.program_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialBuilderCertificates.program_total
/-- info: 'BeaconcryptCore.Computational.PqxdhInitialBuilderCertificates.carried_fits' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialBuilderCertificates.carried_fits
