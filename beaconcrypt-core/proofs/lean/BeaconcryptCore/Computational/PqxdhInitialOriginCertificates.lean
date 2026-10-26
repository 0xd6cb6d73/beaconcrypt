import BeaconcryptCore.Computational.PqxdhInitialOriginForwardBuilder
import BeaconcryptCore.Computational.PqxdhInitialBuilderCertificates

/-!
The actual origin-aware source carries its original remaining post allowance and quiet pending completion together with the full installation/publication trace. The resource certificate is proved for its own constructed descriptor under every source reply, without replacing that descriptor by a same-frame witness.
-/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.refined ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhInitialOriginCertificates
open PqxdhInitialPostContext PqxdhInitialBuilderContext RawCtxForwardTags
open PqxdhInitialPostCertificates (LiveQuiet)
variable {ι M P I D K X Response Shared Result Origin : Type} {extra : OracleSpec ι} {S B : Nat}

def Fits (qPost : Nat) (context : PqxdhInitialOriginContext.Context extra M P I D K Result Origin S B) : Prop :=
  PqxdhInitialBuilderCertificates.Fits qPost context.original

/-- Increasing the original remaining source allowance preserves the complete carried certificate and its metadata. -/
theorem fits_mono (small large : Nat) (below : small ≤ large)
    (context : PqxdhInitialOriginContext.Context extra M P I D K Result Origin S B) :
    Fits small context → Fits large context := by
  rcases context with ⟨original, trace, origin⟩
  cases original with
  | inl context => exact PqxdhInitialPostCertificates.fits_mono small large below context
  | inr context => exact fun valid reply => (valid reply).mono below

private theorem record_fits (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder)
    (decode : RawCtxReceive.FrameDecoder) (request : (RawCtxProtocolReveals.SourceSpec S B).Domain)
    (before : NativeFront M P I D K S B) (trace : PqxdhInitialOriginPost.Trace Origin S B)
    (outside : (RawCtxProtocolReveals.SourceSpec S B).Range request → OracleComp (PostSpec extra S B) Result)
    (after : (RawCtxProtocolReveals.SourceSpec S B).Range request → NativeFront M P I D K S B → PqxdhInitialOriginPost.Trace Origin S B →
      OracleComp (PqxdhInitialOriginForwardPost.Spec extra M P I D K X Response Shared Result Origin S B) (Result × (NativeFront M P I D K S B × PqxdhInitialOriginPost.Trace Origin S B)))
    (qPost : Nat) (bounded : ∀ reply, (outside reply).IsTotalQueryBound qPost)
    (later : ∀ reply updated saved, All (Fits qPost) (after reply updated saved)) :
    All (Fits qPost) (PqxdhInitialOriginForwardPost.record sender route decode request before trace outside after) := by
  apply bind_all
  · apply lift_all LiveQuiet (Fits qPost)
      (fun inner => ⟨.inl (.record request before outside inner), trace, none⟩)
      (fun inner valid => ⟨bounded, valid⟩)
    exact PqxdhInitialPostCertificates.live_quiet sender route decode
      ((RawCtxProtocolReveals.SourceSpec S B).query request : OracleComp (RawCtxProtocolReveals.SourceSpec S B) _)
      ⟨Nat.zero_lt_one, fun _ => True.intro⟩ before.roles
  · exact fun result => later result.1 _ _

private theorem plain_fits {Value : Type}
    (client : OracleComp (Base extra RatchetChain I D K X Response Shared S B) Value)
    (after : Value → OracleComp (PqxdhInitialOriginForwardPost.Spec extra M P I D K X Response Shared Result Origin S B)
      (Result × (NativeFront M P I D K S B × PqxdhInitialOriginPost.Trace Origin S B)))
    (qPost : Nat) (later : ∀ value, All (Fits qPost) (after value)) :
    All (Fits qPost) (simulateQ PqxdhInitialOriginForwardPost.plain client >>= after) := by
  induction client using OracleComp.inductionOn with
  | pure value => exact later value
  | query_bind query outside ih =>
      exact ⟨(fun _ impossible => by cases impossible), fun reply => ih reply⟩

set_option backward.isDefEq.respectTransparency false in
private theorem finish_fits (mark : PqxdhBeaconPhase2Shared.Secrets Shared → Origin) (decode : RawCtxReceive.FrameDecoder)
    (index : Fin B) (raw : Pqxdh.Bytes) (before : NativeFront M P I D K S B) (trace : PqxdhInitialOriginPost.Trace Origin S B)
    (outside : Option Pqxdh.Bytes → OracleComp (PostSpec extra S B) Result)
    (after : Option Pqxdh.Bytes → NativeFront M P I D K S B → PqxdhInitialOriginPost.Trace Origin S B →
      OracleComp (PqxdhInitialOriginForwardPost.Spec extra M P I D K X Response Shared Result Origin S B) (Result × (NativeFront M P I D K S B × PqxdhInitialOriginPost.Trace Origin S B)))
    (qPost : Nat) (bounded : ∀ reply, (outside reply).IsTotalQueryBound qPost)
    (later : ∀ reply updated saved, All (Fits qPost) (after reply updated saved)) :
    All (Fits qPost) (PqxdhInitialOriginForwardPost.finish mark decode index raw before trace outside after) := by
  unfold PqxdhInitialOriginForwardPost.finish
  cases phase : (before.roles.1.2 index).beacon.phase
  case initSent control prekey oneTime kem =>
    dsimp only
    rw [QueryImpl.simulateQ_compose]
    apply plain_fits
    intro prepared
    cases prepared with
    | none => exact later _ _ _
    | some prepared =>
        apply plain_fits
        intro kernel
        cases kernel with
        | none => exact later _ _ _
        | some kernel =>
            apply plain_fits
            intro application
            cases application with
            | none => exact later _ _ _
            | some application =>
                apply bind_all
                · unfold PqxdhInitialOriginForwardPost.ownerLift
                  apply lift_all RawCtxQuietOwnerTails.Quiet (Fits qPost)
                    (fun inner => ⟨.inl (.finish index before control
                      (PqxdhBeaconPhase2Shared.clearedMetadata prepared.metadata) outside inner), trace, some (mark prepared.root)⟩)
                    (fun inner valid => ⟨bounded, valid⟩)
                  apply lift_all RawCtxQuietOwnerTails.Quiet RawCtxQuietOwnerTails.Quiet id (fun _ valid => valid)
                  apply RawCtxForwardOwnerCertificates.program_quiet
                  exact ⟨Nat.zero_lt_one, fun _ => True.intro⟩
                · exact fun result => later _ _ _
  all_goals exact later _ _ _

/-- Every descriptor carried by the actual complete bounded post schedule retains the exact source outside continuation and its residual allowance. -/
theorem post_fits (mark : PqxdhBeaconPhase2Shared.Secrets Shared → Origin) (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder)
    (decode : RawCtxReceive.FrameDecoder) (client : OracleComp (PostSpec extra S B) Result)
    (qPost : Nat) (bounded : client.IsTotalQueryBound qPost) (before : NativeFront M P I D K S B) (trace : PqxdhInitialOriginPost.Trace Origin S B) :
    All (Fits qPost) (PqxdhInitialOriginForwardPost.program (X := X) (Response := Response) (Shared := Shared)
      mark sender route decode client before trace) := by
  induction client using OracleComp.inductionOn generalizing qPost before trace with
  | pure value => trivial
  | query_bind request outside ih =>
      rw [isTotalQueryBound_query_bind_iff] at bounded
      have later : ∀ reply (updated : NativeFront M P I D K S B) (saved : PqxdhInitialOriginPost.Trace Origin S B), All (Fits qPost)
          (PqxdhInitialOriginForwardPost.program (X := X) (Response := Response) (Shared := Shared)
            mark sender route decode (outside reply) updated saved) := by
        intro reply updated saved
        exact mono _ _ (fits_mono (qPost - 1) qPost (Nat.sub_le _ _)) _
          (ih reply (qPost - 1) (bounded.2 reply) updated saved)
      rw [PqxdhInitialOriginForwardPost.program_query]
      rcases request with (request | request) | request
      · exact record_fits sender route decode request before trace outside _ qPost
          (fun reply => (bounded.2 reply).mono (Nat.sub_le _ _)) later
      · exact plain_fits _ _ qPost (fun reply => later reply before trace)
      · cases request with
        | finish index raw =>
            exact finish_fits mark decode index raw before trace outside _ qPost
              (fun reply => (bounded.2 reply).mono (Nat.sub_le _ _)) later

private theorem finished_fits (mark : PqxdhBeaconPhase2Shared.Secrets Shared → Origin) (origin : Origin) (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder)
    (decode : RawCtxReceive.FrameDecoder) (index : Fin S) (before : NativeFront M P I D K S B) (trace : PqxdhInitialOriginPost.Trace Origin S B)
    (outside : BuildResult → OracleComp (PostSpec extra S B) Result)
    (qPost : Nat) (bounded : ∀ reply, (outside reply).IsTotalQueryBound qPost)
    (result : RustM (Option PqxdhServerRegistrationPublication.Response × PqxdhInitialOriginForwardBuilder.Publication M P)) :
    All (Fits qPost) (PqxdhInitialOriginForwardBuilder.finished (X := X) (Response := Response) (Shared := Shared)
      mark origin sender route decode index before trace outside result) :=
  post_fits mark sender route decode _ qPost (bounded _) _ _

private theorem builder_plain_fits {Value : Type}
    (client : OracleComp (Base extra RatchetChain I D K X Response Shared S B) Value)
    (after : Value → OracleComp (PqxdhInitialOriginForwardBuilder.Spec extra M P I D K X Response Shared Result Origin S B)
      (Result × (NativeFront M P I D K S B × PqxdhInitialOriginPost.Trace Origin S B)))
    (qPost : Nat) (later : ∀ value, All (Fits qPost) (after value)) :
    All (Fits qPost) (simulateQ PqxdhInitialOriginForwardBuilder.plain client >>= after) := by
  induction client using OracleComp.inductionOn with
  | pure value => exact later value
  | query_bind query outside ih =>
      exact ⟨(fun _ impossible => by cases impossible), fun reply => ih reply⟩

private theorem publication_fits (mark : PqxdhBeaconPhase2Shared.Secrets Shared → Origin) (origin : Origin) (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder)
    (decode : RawCtxReceive.FrameDecoder) (index : Fin S) (before : NativeFront M P I D K S B) (trace : PqxdhInitialOriginPost.Trace Origin S B)
    (candidate : pqxdh.ServerRegistrationCandidate) (authenticated : Pqxdh.Bytes) (metadata : P)
    (outside : BuildResult → OracleComp (PostSpec extra S B) Result)
    (qPost : Nat) (bounded : ∀ reply, (outside reply).IsTotalQueryBound qPost)
    (result : PqxdhInitialPendingPost.KernelOf RatchetChain × Option RawCtxSourceSend.Encrypted) :
    All (Fits qPost) (PqxdhInitialOriginForwardBuilder.publication (X := X) (Response := Response) (Shared := Shared)
      mark origin sender route decode index before trace candidate authenticated metadata outside result) := by
  apply builder_plain_fits
  exact fun value => finished_fits mark origin sender route decode index before trace outside qPost bounded (.ok value)

private theorem send_fits (mark : PqxdhBeaconPhase2Shared.Secrets Shared → Origin) (origin : Origin) (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder)
    (decode : RawCtxReceive.FrameDecoder) (index : Fin S) (before : NativeFront M P I D K S B) (trace : PqxdhInitialOriginPost.Trace Origin S B)
    (candidate : pqxdh.ServerRegistrationCandidate) (authenticated : Pqxdh.Bytes) (metadata : P)
    (outside : BuildResult → OracleComp (PostSpec extra S B) Result)
    (qPost : Nat) (bounded : ∀ reply, (outside reply).IsTotalQueryBound qPost)
    (kernel : PqxdhInitialPendingPost.KernelOf RatchetChain) :
    All (Fits qPost) (PqxdhInitialOriginForwardBuilder.send (X := X) (Response := Response) (Shared := Shared)
      mark origin sender route decode index before trace candidate authenticated metadata outside kernel) := by
  unfold PqxdhInitialOriginForwardBuilder.send
  cases start : RawCtxChainSend.normalBegin kernel (PqxdhServerRegistrationPublication.firstContext candidate authenticated) with
  | exhausted entry context => exact publication_fits mark origin sender route decode index before trace candidate authenticated metadata outside qPost bounded _
  | requested pending =>
      exact ⟨(fun tag same => by cases same; exact bounded), fun reply =>
        ⟨(fun _ impossible => by cases impossible), fun sealed =>
          publication_fits mark origin sender route decode index before trace candidate authenticated metadata outside qPost bounded _⟩⟩

private theorem candidate_fits (mark : PqxdhBeaconPhase2Shared.Secrets Shared → Origin) (origin : Origin) (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder)
    (decode : RawCtxReceive.FrameDecoder) (index : Fin S) (before : NativeFront M P I D K S B) (trace : PqxdhInitialOriginPost.Trace Origin S B)
    (initial : RustM (PqxdhInitialPendingPost.KernelOf RatchetChain))
    (candidate : pqxdh.ServerRegistrationCandidate) (data : Option Pqxdh.Bytes) (metadata : P)
    (outside : BuildResult → OracleComp (PostSpec extra S B) Result)
    (qPost : Nat) (bounded : ∀ reply, (outside reply).IsTotalQueryBound qPost) :
    All (Fits qPost) (PqxdhInitialOriginForwardBuilder.candidate (X := X) (Response := Response) (Shared := Shared)
      mark origin sender route decode index before trace initial candidate data metadata outside) := by
  unfold PqxdhInitialOriginForwardBuilder.candidate
  apply builder_plain_fits
  intro valid
  cases valid
  · exact finished_fits mark origin sender route decode index before trace outside qPost bounded _
  · simp only [Bool.not_true, Bool.false_eq_true, ite_false]
    apply builder_plain_fits
    intro reserved
    cases reserved
    · exact finished_fits mark origin sender route decode index before trace outside qPost bounded _
    · simp only [Bool.not_true, Bool.false_eq_true, ite_false]
      cases initial with
      | fail error => exact finished_fits mark origin sender route decode index before trace outside qPost bounded _
      | div => exact finished_fits mark origin sender route decode index before trace outside qPost bounded _
      | ok kernel =>
          dsimp only
          split
          · exact finished_fits mark origin sender route decode index before trace outside qPost bounded _
          · split
            · apply builder_plain_fits
              intro allocated
              cases allocated
              · exact finished_fits mark origin sender route decode index before trace outside qPost bounded _
              · simp only [Bool.not_true, Bool.false_eq_true, ite_false]
                cases binding : candidate.key_id_binding with
                | fail error => exact finished_fits mark origin sender route decode index before trace outside qPost bounded _
                | div => exact finished_fits mark origin sender route decode index before trace outside qPost bounded _
                | ok binding => exact send_fits mark origin sender route decode index before trace candidate _ metadata outside qPost bounded kernel
            · exact finished_fits mark origin sender route decode index before trace outside qPost bounded _

private theorem used_fits (mark : PqxdhBeaconPhase2Shared.Secrets Shared → Origin) (origin : Origin) (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder)
    (decode : RawCtxReceive.FrameDecoder) (index : Fin S) (before : NativeFront M P I D K S B) (trace : PqxdhInitialOriginPost.Trace Origin S B)
    (initial : RustM (PqxdhInitialPendingPost.KernelOf RatchetChain))
    (pending : PqxdhRegistrationInputs.UsedInput) (data : Option Pqxdh.Bytes) (metadata : P)
    (outside : BuildResult → OracleComp (PostSpec extra S B) Result)
    (qPost : Nat) (bounded : ∀ reply, (outside reply).IsTotalQueryBound qPost) :
    All (Fits qPost) (PqxdhInitialOriginForwardBuilder.used (X := X) (Response := Response) (Shared := Shared)
      mark origin sender route decode index before trace initial pending data metadata outside) := by
  unfold PqxdhInitialOriginForwardBuilder.used
  dsimp only
  cases nextResult : pqxdh.server_next_key_id (PqxdhInitialPendingBuilder.selected sender index before).control with
  | fail error => exact finished_fits mark origin sender route decode index before trace outside qPost bounded _
  | div => exact finished_fits mark origin sender route decode index before trace outside qPost bounded _
  | ok value =>
      cases value with
      | Err error => exact finished_fits mark origin sender route decode index before trace outside qPost bounded _
      | Ok key =>
          dsimp only
          cases preparation : PqxdhRegistrationInputs.prepare
            (PqxdhInitialPendingBuilder.selected sender index before).control pending
            ⟨(PqxdhInitialPendingBuilder.selected sender index before).server.identity,
              (PqxdhInitialPendingBuilder.selected sender index before).identityKeyId⟩
            (if ((PqxdhInitialPendingBuilder.selected sender index before).server.peers key).isSome
              then pqxdh.KeyIdAvailability.Occupied else .Available) with
          | fail error => exact finished_fits mark origin sender route decode index before trace outside qPost bounded _
          | div => exact finished_fits mark origin sender route decode index before trace outside qPost bounded _
          | ok prepared =>
              cases prepared with
              | Err error => exact finished_fits mark origin sender route decode index before trace outside qPost bounded _
              | Ok prepared => exact candidate_fits mark origin sender route decode index before trace initial prepared data metadata outside qPost bounded

/-- Every descriptor in the complete accepted builder and post source retains its actual original outside allowance, including the first private send before publication. -/
theorem program_fits (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (mark : PqxdhBeaconPhase2Shared.Secrets Shared → Origin) (origin : Origin) (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (initial : RustM (PqxdhInitialPendingPost.KernelOf RatchetChain)) (index : Fin S) (metadata : P)
    (ready : PqxdhPrivateAcceptedRoot.Ready) (outside : BuildResult → OracleComp (PostSpec extra S B) Result)
    (qPost : Nat) (bounded : ∀ reply, (outside reply).IsTotalQueryBound qPost)
    (before : NativeFront M P I D K S B) (trace : PqxdhInitialOriginPost.Trace Origin S B) :
    All (Fits qPost) (PqxdhInitialOriginForwardBuilder.program (X := X) (Response := Response) (Shared := Shared)
      source mark origin sender route decode initial index metadata ready outside before trace) :=
  used_fits mark origin sender route decode index _ trace initial _ ready.application metadata outside qPost bounded

/-- The complete origin-aware source keeps the original seven builder callbacks and sixty-seven callbacks per remaining post request. -/
theorem program_total (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (mark : PqxdhBeaconPhase2Shared.Secrets Shared → Origin) (origin : Origin)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (initial : RustM (PqxdhInitialPendingPost.KernelOf RatchetChain)) (index : Fin S) (metadata : P)
    (ready : PqxdhPrivateAcceptedRoot.Ready) (outside : BuildResult → OracleComp (PostSpec extra S B) Result)
    (qPost : Nat) (bounded : ∀ reply, (outside reply).IsTotalQueryBound qPost)
    (before : NativeFront M P I D K S B) (trace : PqxdhInitialOriginPost.Trace Origin S B) :
    (PqxdhInitialOriginForwardBuilder.program (X := X) (Response := Response) (Shared := Shared)
      source mark origin sender route decode initial index metadata ready outside before trace).IsTotalQueryBound (7 + qPost * 67) := by
  apply (isQueryBoundP_true_iff _ _).mp
  apply (RawCtxForwardCosts.erase_class (fun _ => True) _ _).mp
  rw [PqxdhInitialOriginForwardBuilder.program_erase]
  exact (PqxdhInitialOriginPost.sequence_total source initial mark origin sender route decode index metadata ready outside qPost bounded (before, trace)).isQueryBoundP

/-- A supported executable full-source scan returns its own resource-certified descriptor with its actual origin and publication metadata. -/
theorem carried_fits {State : Type}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (mark : PqxdhBeaconPhase2Shared.Secrets Shared → Origin) (origin : Origin)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (initialKernel : RustM (PqxdhInitialPendingPost.KernelOf RatchetChain)) (index : Fin S) (metadata : P)
    (ready : PqxdhPrivateAcceptedRoot.Ready) (outside : BuildResult → OracleComp (PostSpec extra S B) Result)
    (qPost : Nat) (bounded : ∀ reply, (outside reply).IsTotalQueryBound qPost)
    (before : NativeFront M P I D K S B) (trace : PqxdhInitialOriginPost.Trace Origin S B)
    (chosen : (Base extra RatchetChain I D K X Response Shared S B).Domain → State → Bool)
    (selection : ∀ query state, chosen query state = true → PqxdhInitialForwardPost.selected query = true)
    (impl : QueryImpl (Base extra RatchetChain I D K X Response Shared S B) (StateT State ProbComp))
    (initial reached : State) (context : PqxdhInitialOriginContext.Context extra M P I D K Result Origin S B)
    (supported : RawCtxForwardScan.Cut.pending context reached ∈ support
      (RawCtxForwardScan.scan PqxdhInitialForwardPost.selected chosen selection impl
        (PqxdhInitialOriginForwardBuilder.program source mark origin sender route decode initialKernel index metadata ready outside before trace)
        (PqxdhInitialOriginForwardBuilder.program_covered source mark origin sender route decode initialKernel index metadata ready outside before trace) initial)) :
    Fits qPost context :=
  scan_all PqxdhInitialForwardPost.selected chosen selection impl (Fits qPost) _
    (PqxdhInitialOriginForwardBuilder.program_covered source mark origin sender route decode initialKernel index metadata ready outside before trace)
    (program_fits source mark origin sender route decode initialKernel index metadata ready outside qPost bounded before trace)
    initial reached context supported

end BeaconcryptCore.Computational.PqxdhInitialOriginCertificates

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialOriginCertificates.fits_mono' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialOriginCertificates.fits_mono
/-- info: 'BeaconcryptCore.Computational.PqxdhInitialOriginCertificates.post_fits' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialOriginCertificates.post_fits
/-- info: 'BeaconcryptCore.Computational.PqxdhInitialOriginCertificates.program_fits' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialOriginCertificates.program_fits
/-- info: 'BeaconcryptCore.Computational.PqxdhInitialOriginCertificates.program_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialOriginCertificates.program_total
/-- info: 'BeaconcryptCore.Computational.PqxdhInitialOriginCertificates.carried_fits' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialOriginCertificates.carried_fits
