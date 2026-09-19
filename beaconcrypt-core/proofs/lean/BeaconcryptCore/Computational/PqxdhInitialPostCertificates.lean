import BeaconcryptCore.Computational.PqxdhInitialForwardPost
import BeaconcryptCore.Computational.PqxdhInitialPendingSourceBounds
import BeaconcryptCore.Computational.RawCtxForwardLiveCertificates

/-!
The complete post source carries its remaining original query allowance in every selected descriptor. A record descriptor retains the quiet inner single-request context, and a first-receive descriptor retains its quiet owner context. The original outside post continuation is bounded under every reply; the certificate is proved for the descriptor actually constructed at the source query.
-/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.refined ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhInitialPostCertificates
open PqxdhInitialPostContext RawCtxForwardTags
variable {ι M P I D K X Response Shared Result : Type} {extra : OracleSpec ι} {S B : Nat}

def LiveQuiet {Value : Type} : RawCtxSelectedFamilyContext.Context M P I D K Value S B → Prop
  | .family _ _ outside inner => (∀ reply, (outside reply).IsTotalQueryBound 0) ∧ RawCtxQuietFamilyTails.Quiet inner

def Fits (qPost : Nat) : PqxdhInitialPostContext.Context extra M P I D K Result S B → Prop
  | .record _ _ outside inner => (∀ reply, (outside reply).IsTotalQueryBound qPost) ∧ LiveQuiet inner
  | .finish _ _ _ _ outside inner => (∀ reply, (outside reply).IsTotalQueryBound qPost) ∧ RawCtxQuietOwnerTails.Quiet inner

/-- Increasing only the original remaining post allowance preserves the carried quiet completion certificate. -/
theorem fits_mono (small large : Nat) (below : small ≤ large)
    (context : PqxdhInitialPostContext.Context extra M P I D K Result S B) :
    Fits small context → Fits large context := by
  cases context <;> exact fun valid => ⟨fun reply => (valid.1 reply).mono below, valid.2⟩

private theorem live_zero (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder)
    (decode : RawCtxReceive.FrameDecoder) (client : OracleComp (RawCtxProtocolReveals.SourceSpec S B) Result)
    (bounded : client.IsTotalQueryBound 0) (before : RawCtxSelectedFamilyContext.NativeLive M P I D K S B) :
    All LiveQuiet (RawCtxForwardLive.program sender route decode client before) := by
  obtain ⟨value, rfl⟩ := RawCtxQuietOwnerTails.zero_pure client bounded
  trivial

/-- The single original record request retains only quiet owner, family and LIVE continuations inside its descriptor. -/
theorem live_quiet (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder)
    (decode : RawCtxReceive.FrameDecoder) (client : OracleComp (RawCtxProtocolReveals.SourceSpec S B) Result)
    (bounded : client.IsTotalQueryBound 1) (before : RawCtxSelectedFamilyContext.NativeLive M P I D K S B) :
    All LiveQuiet (RawCtxForwardLive.program sender route decode client before) := by
  induction client using OracleComp.inductionOn generalizing before with
  | pure value => trivial
  | query_bind request outside ih =>
      have quiet : ∀ reply, (outside reply).IsTotalQueryBound 0 := by
        simpa only [IsTotalQueryBound, isQueryBound_query_bind_iff, Nat.sub_self, zero_lt_one, true_and] using bounded
      rw [RawCtxForwardLive.program_query]
      cases request with
      | inl request =>
          unfold RawCtxForwardLive.family
          apply bind_all
          · apply lift_all RawCtxQuietFamilyTails.Quiet LiveQuiet
              (fun inner => RawCtxSelectedFamilyContext.Context.family request before.2 outside inner)
              (fun inner valid => ⟨quiet, valid⟩)
            exact RawCtxForwardRoleCertificates.family_quiet sender route decode
              ((RawCtxForwardFamily.SourceSpec S B).query request : OracleComp (RawCtxForwardFamily.SourceSpec S B) _)
              ⟨Nat.zero_lt_one, fun _ => True.intro⟩ before.1
          · intro result
            exact live_zero sender route decode _ (quiet result.1) _
      | inr request =>
          exact ⟨(fun _ impossible => by cases impossible),
            fun reply => live_zero sender route decode _ (quiet reply) _⟩

private theorem record_fits (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder)
    (decode : RawCtxReceive.FrameDecoder) (request : (RawCtxProtocolReveals.SourceSpec S B).Domain)
    (before : NativeFront M P I D K S B)
    (outside : (RawCtxProtocolReveals.SourceSpec S B).Range request → OracleComp (PostSpec extra S B) Result)
    (after : (RawCtxProtocolReveals.SourceSpec S B).Range request → NativeFront M P I D K S B →
      OracleComp (PqxdhInitialForwardPost.Spec extra M P I D K X Response Shared Result S B) (Result × NativeFront M P I D K S B))
    (qPost : Nat) (bounded : ∀ reply, (outside reply).IsTotalQueryBound qPost)
    (later : ∀ reply updated, All (Fits qPost) (after reply updated)) :
    All (Fits qPost) (PqxdhInitialForwardPost.record sender route decode request before outside after) := by
  apply bind_all
  · apply lift_all LiveQuiet (Fits qPost)
      (fun inner => PqxdhInitialPostContext.Context.record request before outside inner)
      (fun inner valid => ⟨bounded, valid⟩)
    exact live_quiet sender route decode
      ((RawCtxProtocolReveals.SourceSpec S B).query request : OracleComp (RawCtxProtocolReveals.SourceSpec S B) _)
      ⟨Nat.zero_lt_one, fun _ => True.intro⟩ before.roles
  · exact fun result => later result.1 _

private theorem plain_fits {Value : Type}
    (client : OracleComp (Base extra RatchetChain I D K X Response Shared S B) Value)
    (after : Value → OracleComp (PqxdhInitialForwardPost.Spec extra M P I D K X Response Shared Result S B)
      (Result × NativeFront M P I D K S B))
    (qPost : Nat) (later : ∀ value, All (Fits qPost) (after value)) :
    All (Fits qPost) (simulateQ PqxdhInitialForwardPost.plain client >>= after) := by
  induction client using OracleComp.inductionOn with
  | pure value => exact later value
  | query_bind query outside ih =>
      exact ⟨(fun _ impossible => by cases impossible), fun reply => ih reply⟩

set_option backward.isDefEq.respectTransparency false in
private theorem finish_fits (decode : RawCtxReceive.FrameDecoder)
    (index : Fin B) (raw : Pqxdh.Bytes) (before : NativeFront M P I D K S B)
    (outside : Option Pqxdh.Bytes → OracleComp (PostSpec extra S B) Result)
    (after : Option Pqxdh.Bytes → NativeFront M P I D K S B →
      OracleComp (PqxdhInitialForwardPost.Spec extra M P I D K X Response Shared Result S B) (Result × NativeFront M P I D K S B))
    (qPost : Nat) (bounded : ∀ reply, (outside reply).IsTotalQueryBound qPost)
    (later : ∀ reply updated, All (Fits qPost) (after reply updated)) :
    All (Fits qPost) (PqxdhInitialForwardPost.finish decode index raw before outside after) := by
  unfold PqxdhInitialForwardPost.finish
  cases phase : (before.roles.1.2 index).beacon.phase
  case initSent control prekey oneTime kem =>
    dsimp only
    rw [QueryImpl.simulateQ_compose]
    apply plain_fits
    intro prepared
    cases prepared with
    | none => exact later _ _
    | some prepared =>
        apply plain_fits
        intro kernel
        cases kernel with
        | none => exact later _ _
        | some kernel =>
            apply plain_fits
            intro application
            cases application with
            | none => exact later _ _
            | some application =>
                apply bind_all
                · unfold PqxdhInitialForwardPost.ownerLift
                  apply lift_all RawCtxQuietOwnerTails.Quiet (Fits qPost)
                    (fun inner => PqxdhInitialPostContext.Context.finish index before control
                      (PqxdhBeaconPhase2Shared.clearedMetadata prepared.metadata) outside inner)
                    (fun inner valid => ⟨bounded, valid⟩)
                  apply lift_all RawCtxQuietOwnerTails.Quiet RawCtxQuietOwnerTails.Quiet id (fun _ valid => valid)
                  apply RawCtxForwardOwnerCertificates.program_quiet
                  exact ⟨Nat.zero_lt_one, fun _ => True.intro⟩
                · exact fun result => later _ _
  all_goals exact later _ _

/-- Every descriptor carried by the actual complete bounded post schedule retains the exact source outside continuation and its residual allowance. -/
theorem program_fits (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder)
    (decode : RawCtxReceive.FrameDecoder) (client : OracleComp (PostSpec extra S B) Result)
    (qPost : Nat) (bounded : client.IsTotalQueryBound qPost) (before : NativeFront M P I D K S B) :
    All (Fits qPost) (PqxdhInitialForwardPost.program (X := X) (Response := Response) (Shared := Shared)
      sender route decode client before) := by
  induction client using OracleComp.inductionOn generalizing qPost before with
  | pure value => trivial
  | query_bind request outside ih =>
      rw [isTotalQueryBound_query_bind_iff] at bounded
      have later : ∀ reply (updated : NativeFront M P I D K S B), All (Fits qPost)
          (PqxdhInitialForwardPost.program (X := X) (Response := Response) (Shared := Shared)
            sender route decode (outside reply) updated) := by
        intro reply updated
        exact mono _ _ (fits_mono (qPost - 1) qPost (Nat.sub_le _ _)) _
          (ih reply (qPost - 1) (bounded.2 reply) updated)
      rw [PqxdhInitialForwardPost.program_query]
      rcases request with (request | request) | request
      · exact record_fits sender route decode request before outside _ qPost
          (fun reply => (bounded.2 reply).mono (Nat.sub_le _ _)) later
      · exact plain_fits _ _ qPost (fun reply => later reply before)
      · cases request with
        | finish index raw =>
            exact finish_fits decode index raw before outside _ qPost
              (fun reply => (bounded.2 reply).mono (Nat.sub_le _ _)) later

/-- A supported executable full-post scan returns its own resource-certified descriptor; no equal-frame replacement or bounded ambient continuation is assumed. -/
theorem carried_fits {State : Type}
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder)
    (decode : RawCtxReceive.FrameDecoder) (client : OracleComp (PostSpec extra S B) Result)
    (qPost : Nat) (bounded : client.IsTotalQueryBound qPost) (before : NativeFront M P I D K S B)
    (chosen : (Base extra RatchetChain I D K X Response Shared S B).Domain → State → Bool)
    (selection : ∀ query state, chosen query state = true → PqxdhInitialForwardPost.selected query = true)
    (impl : QueryImpl (Base extra RatchetChain I D K X Response Shared S B) (StateT State ProbComp))
    (initial reached : State) (context : PqxdhInitialPostContext.Context extra M P I D K Result S B)
    (supported : RawCtxForwardScan.Cut.pending context reached ∈ support
      (RawCtxForwardScan.scan PqxdhInitialForwardPost.selected chosen selection impl
        (PqxdhInitialForwardPost.program sender route decode client before)
        (PqxdhInitialForwardPost.program_covered sender route decode client before) initial)) :
    Fits qPost context :=
  scan_all PqxdhInitialForwardPost.selected chosen selection impl (Fits qPost) _
    (PqxdhInitialForwardPost.program_covered sender route decode client before)
    (program_fits sender route decode client qPost bounded before) initial reached context supported

end BeaconcryptCore.Computational.PqxdhInitialPostCertificates

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialPostCertificates.fits_mono' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialPostCertificates.fits_mono
/-- info: 'BeaconcryptCore.Computational.PqxdhInitialPostCertificates.live_quiet' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialPostCertificates.live_quiet
/-- info: 'BeaconcryptCore.Computational.PqxdhInitialPostCertificates.program_fits' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialPostCertificates.program_fits
/-- info: 'BeaconcryptCore.Computational.PqxdhInitialPostCertificates.carried_fits' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialPostCertificates.carried_fits
