import BeaconcryptCore.Computational.PqxdhLaterChallengeSavedMonitor

/-! Saved callbacks preserve logical properties of the actual outside program on every oracle reply path. No interpreted prefix probability is reconstructed. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhLaterSavedOutsideSupport
open PqxdhInitialPostContext RawCtxForwardTags
variable {ι M P I D K X Response Shared Result Origin : Type} {extra : OracleSpec ι} {S B : Nat}

/-- Every reply to the retained source request has an outside program whose returned values satisfy the property. This concerns returned values, not the interpreted state or its distribution. -/
def Returns (property : Result → Prop)
    (context : PqxdhInitialOriginContext.Context extra M P I D K Result Origin S B) : Prop :=
  match context.original with
  | .inl (.record _ _ outside _) => ∀ reply value, value ∈ support (outside reply) → property value
  | .inl (.finish _ _ _ _ outside _) => ∀ reply value, value ∈ support (outside reply) → property value
  | .inr builder => ∀ reply value, value ∈ support (builder.outside reply) → property value

private theorem record_returns (property : Result → Prop) (sender : M → Std.U64)
    (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (request : (RawCtxProtocolReveals.SourceSpec S B).Domain)
    (before : NativeFront M P I D K S B) (trace : PqxdhInitialOriginPost.Trace Origin S B)
    (outside : (RawCtxProtocolReveals.SourceSpec S B).Range request → OracleComp (PostSpec extra S B) Result)
    (after : (RawCtxProtocolReveals.SourceSpec S B).Range request → NativeFront M P I D K S B → PqxdhInitialOriginPost.Trace Origin S B →
      OracleComp (PqxdhInitialOriginForwardPost.Spec extra M P I D K X Response Shared Result Origin S B) (Result × (NativeFront M P I D K S B × PqxdhInitialOriginPost.Trace Origin S B)))
    (valid : ∀ reply value, value ∈ support (outside reply) → property value)
    (later : ∀ reply updated saved, All (Returns property) (after reply updated saved)) :
    All (Returns property) (PqxdhInitialOriginForwardPost.record sender route decode request before trace outside after) := by
  apply bind_all
  · apply lift_all (fun _ => True) (Returns property)
      (fun inner => ⟨.inl (.record request before outside inner), trace, none⟩)
      (fun _ _ => valid)
    exact PqxdhLaterChallengeCapture.all_true _
  · exact fun result => later result.1 _ _

private theorem plain_returns {Value : Type} (property : Result → Prop)
    (client : OracleComp (Base extra RatchetChain I D K X Response Shared S B) Value)
    (after : Value → OracleComp (PqxdhInitialOriginForwardPost.Spec extra M P I D K X Response Shared Result Origin S B)
      (Result × (NativeFront M P I D K S B × PqxdhInitialOriginPost.Trace Origin S B)))
    (later : ∀ value, All (Returns property) (after value)) :
    All (Returns property) (simulateQ PqxdhInitialOriginForwardPost.plain client >>= after) := by
  induction client using OracleComp.inductionOn with
  | pure value => exact later value
  | query_bind query outside ih =>
      exact ⟨(fun _ impossible => by cases impossible), fun reply => ih reply⟩

set_option backward.isDefEq.respectTransparency false in
private theorem finish_returns (property : Result → Prop) (mark : PqxdhBeaconPhase2Shared.Secrets Shared → Origin) (decode : RawCtxReceive.FrameDecoder)
    (index : Fin B) (raw : Pqxdh.Bytes) (before : NativeFront M P I D K S B) (trace : PqxdhInitialOriginPost.Trace Origin S B)
    (outside : Option Pqxdh.Bytes → OracleComp (PostSpec extra S B) Result)
    (after : Option Pqxdh.Bytes → NativeFront M P I D K S B → PqxdhInitialOriginPost.Trace Origin S B →
      OracleComp (PqxdhInitialOriginForwardPost.Spec extra M P I D K X Response Shared Result Origin S B) (Result × (NativeFront M P I D K S B × PqxdhInitialOriginPost.Trace Origin S B)))
    (valid : ∀ reply value, value ∈ support (outside reply) → property value)
    (later : ∀ reply updated saved, All (Returns property) (after reply updated saved)) :
    All (Returns property) (PqxdhInitialOriginForwardPost.finish mark decode index raw before trace outside after) := by
  unfold PqxdhInitialOriginForwardPost.finish
  cases phase : (before.roles.1.2 index).beacon.phase
  case initSent control prekey oneTime kem =>
    dsimp only
    rw [QueryImpl.simulateQ_compose]
    apply plain_returns property
    intro prepared
    cases prepared with
    | none => exact later _ _ _
    | some prepared =>
        apply plain_returns property
        intro kernel
        cases kernel with
        | none => exact later _ _ _
        | some kernel =>
            apply plain_returns property
            intro application
            cases application with
            | none => exact later _ _ _
            | some application =>
                apply bind_all
                · unfold PqxdhInitialOriginForwardPost.ownerLift
                  apply lift_all (fun _ => True) (Returns property)
                    (fun inner => ⟨.inl (.finish index before control
                      (PqxdhBeaconPhase2Shared.clearedMetadata prepared.metadata) outside inner), trace, some (mark prepared.root)⟩)
                    (fun _ _ => valid)
                  exact PqxdhLaterChallengeCapture.all_true _
                · exact fun result => later _ _ _
  all_goals exact later _ _ _

/-- Every descriptor generated by the original complete Post program preserves any property of all its possible returned values. This is a structural source fact, with no interpreted-prefix or secrecy premise. -/
theorem program_returns (property : Result → Prop)
    (mark : PqxdhBeaconPhase2Shared.Secrets Shared → Origin) (sender : M → Std.U64)
    (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp (PostSpec extra S B) Result)
    (valid : ∀ value, value ∈ support client → property value)
    (before : NativeFront M P I D K S B) (trace : PqxdhInitialOriginPost.Trace Origin S B) :
    All (Returns property) (PqxdhInitialOriginForwardPost.program (X := X) (Response := Response) (Shared := Shared)
      mark sender route decode client before trace) := by
  induction client using OracleComp.inductionOn generalizing before trace with
  | pure value => trivial
  | query_bind request outside ih =>
      have nextValid : ∀ reply value, value ∈ support (outside reply) → property value :=
        fun reply value supported => valid value ((mem_support_bind_iff _ _ _).2
          ⟨reply, mem_support_query request reply, supported⟩)
      have later := fun reply updated saved => ih reply (nextValid reply) updated saved
      rw [PqxdhInitialOriginForwardPost.program_query]
      rcases request with (request | request) | request
      · exact record_returns property sender route decode request before trace outside _ nextValid later
      · exact plain_returns property _ _ (fun reply => later reply before trace)
      · cases request with
        | finish index raw =>
            exact finish_returns property mark decode index raw before trace outside _ nextValid later

/-- A supported actual Post cut carries the outside-return property of its original complete callback. The whole reached state stays in the scan premise. -/
theorem scan_returns {State : Type} (property : Result → Prop)
    (mark : PqxdhBeaconPhase2Shared.Secrets Shared → Origin) (sender : M → Std.U64)
    (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (selected : (Base extra RatchetChain I D K X Response Shared S B).Domain → State → Bool)
    (selection : ∀ query state, selected query state = true → PqxdhInitialOriginForwardPost.selected query = true)
    (impl : QueryImpl (Base extra RatchetChain I D K X Response Shared S B) (StateT State ProbComp))
    (client : OracleComp (PostSpec extra S B) Result)
    (valid : ∀ value, value ∈ support client → property value)
    (before : NativeFront M P I D K S B) (trace : PqxdhInitialOriginPost.Trace Origin S B)
    (state reached : State) (context : PqxdhInitialOriginContext.Context extra M P I D K Result Origin S B)
    (supported : RawCtxForwardScan.Cut.pending context reached ∈ support
      (RawCtxForwardScan.scan PqxdhInitialOriginForwardPost.selected selected selection impl
        (PqxdhInitialOriginForwardPost.program mark sender route decode client before trace)
        (PqxdhInitialOriginForwardPost.program_covered mark sender route decode client before trace) state)) :
    Returns property context :=
  RawCtxForwardTags.scan_all PqxdhInitialOriginForwardPost.selected selected selection impl (Returns property) _
    (PqxdhInitialOriginForwardPost.program_covered mark sender route decode client before trace)
    (program_returns property mark sender route decode client valid before trace) state reached context supported

end BeaconcryptCore.Computational.PqxdhLaterSavedOutsideSupport

/-- info: 'BeaconcryptCore.Computational.PqxdhLaterSavedOutsideSupport.program_returns' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterSavedOutsideSupport.program_returns
/-- info: 'BeaconcryptCore.Computational.PqxdhLaterSavedOutsideSupport.scan_returns' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterSavedOutsideSupport.scan_returns
