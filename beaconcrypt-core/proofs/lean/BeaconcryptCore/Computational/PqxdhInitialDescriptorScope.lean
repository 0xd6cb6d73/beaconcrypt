import BeaconcryptCore.Computational.RawCtxForwardRoleScope
import BeaconcryptCore.Computational.PqxdhInitialOriginForwardBuilder

/-!
The concrete origin-aware registration builder and its complete adaptive post schedule carry the actual raw admission certificate into every retained receive descriptor. The certificate is derived from source construction before the selected private response; it is not a condition imposed on arbitrary saved contexts.
-/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.refined ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhInitialDescriptorScope
open PqxdhInitialPostContext PqxdhInitialBuilderContext RawCtxForwardTags
variable {ι M P I D K X Response Shared Result Origin : Type} {extra : OracleSpec ι} {S B : Nat}

def PostValid (read : RawCtxReceive.FrameDecoder) : PqxdhInitialPostContext.Context extra M P I D K Result S B → Prop
  | .record _ _ _ inner => RawCtxForwardRoleScope.LiveValid read inner
  | .finish _ _ _ _ _ inner => RawCtxForwardOwnerScope.Valid read inner

def BuilderValid (read : RawCtxReceive.FrameDecoder) : PqxdhInitialBuilderContext.Context extra M P I D K Result S B → Prop
  | .inl context => PostValid read context
  | .inr _ => True

def Valid (read : RawCtxReceive.FrameDecoder)
    (context : PqxdhInitialOriginContext.Context extra M P I D K Result Origin S B) : Prop :=
  BuilderValid read context.original

private theorem record_valid (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder)
    (read : RawCtxReceive.FrameDecoder) (request : (RawCtxProtocolReveals.SourceSpec S B).Domain)
    (before : NativeFront M P I D K S B) (trace : PqxdhInitialOriginPost.Trace Origin S B)
    (outside : (RawCtxProtocolReveals.SourceSpec S B).Range request → OracleComp (PostSpec extra S B) Result)
    (after : (RawCtxProtocolReveals.SourceSpec S B).Range request → NativeFront M P I D K S B → PqxdhInitialOriginPost.Trace Origin S B →
      OracleComp (PqxdhInitialOriginForwardPost.Spec extra M P I D K X Response Shared Result Origin S B) (Result × (NativeFront M P I D K S B × PqxdhInitialOriginPost.Trace Origin S B)))
    (later : ∀ reply updated saved, All (Valid read) (after reply updated saved)) :
    All (Valid read) (PqxdhInitialOriginForwardPost.record sender route read request before trace outside after) := by
  apply bind_all
  · apply lift_all (RawCtxForwardRoleScope.LiveValid read) (Valid read)
      (fun inner => ⟨.inl (.record request before outside inner), trace, none⟩) (fun _ valid => valid)
    exact RawCtxForwardRoleScope.live_valid sender route read _ _
  · exact fun result => later result.1 _ _

private theorem plain_valid {Value : Type}
    (read : RawCtxReceive.FrameDecoder)
    (client : OracleComp (Base extra RatchetChain I D K X Response Shared S B) Value)
    (after : Value → OracleComp (PqxdhInitialOriginForwardPost.Spec extra M P I D K X Response Shared Result Origin S B)
      (Result × (NativeFront M P I D K S B × PqxdhInitialOriginPost.Trace Origin S B)))
    (later : ∀ value, All (Valid read) (after value)) :
    All (Valid read) (simulateQ PqxdhInitialOriginForwardPost.plain client >>= after) := by
  induction client using OracleComp.inductionOn with
  | pure value => exact later value
  | query_bind query outside ih =>
      exact ⟨(fun _ impossible => by cases impossible), fun reply => ih reply⟩

set_option backward.isDefEq.respectTransparency false in
private theorem finish_valid (mark : PqxdhBeaconPhase2Shared.Secrets Shared → Origin) (read : RawCtxReceive.FrameDecoder)
    (index : Fin B) (raw : Pqxdh.Bytes) (before : NativeFront M P I D K S B) (trace : PqxdhInitialOriginPost.Trace Origin S B)
    (outside : Option Pqxdh.Bytes → OracleComp (PostSpec extra S B) Result)
    (after : Option Pqxdh.Bytes → NativeFront M P I D K S B → PqxdhInitialOriginPost.Trace Origin S B →
      OracleComp (PqxdhInitialOriginForwardPost.Spec extra M P I D K X Response Shared Result Origin S B) (Result × (NativeFront M P I D K S B × PqxdhInitialOriginPost.Trace Origin S B)))
    (later : ∀ reply updated saved, All (Valid read) (after reply updated saved)) :
    All (Valid read) (PqxdhInitialOriginForwardPost.finish mark read index raw before trace outside after) := by
  unfold PqxdhInitialOriginForwardPost.finish
  cases phase : (before.roles.1.2 index).beacon.phase
  case initSent control prekey oneTime kem =>
    dsimp only
    rw [QueryImpl.simulateQ_compose]
    apply plain_valid read
    intro prepared
    cases prepared with
    | none => exact later _ _ _
    | some prepared =>
        apply plain_valid read
        intro kernel
        cases kernel with
        | none => exact later _ _ _
        | some kernel =>
            apply plain_valid read
            intro application
            cases application with
            | none => exact later _ _ _
            | some application =>
                apply bind_all
                · unfold PqxdhInitialOriginForwardPost.ownerLift
                  apply lift_all (RawCtxForwardOwnerScope.Valid read) (Valid read)
                    (fun inner => ⟨.inl (.finish index before control
                      (PqxdhBeaconPhase2Shared.clearedMetadata prepared.metadata) outside inner), trace, some (mark prepared.root)⟩)
                    (fun _ valid => valid)
                  apply lift_all (RawCtxForwardOwnerScope.Valid read) (RawCtxForwardOwnerScope.Valid read) id (fun _ valid => valid)
                  exact RawCtxForwardOwnerScope.program_valid _ _ _ _
                · exact fun result => later _ _ _
  all_goals exact later _ _ _

/-- The entire original Post program constructs certified descriptors under every adaptive record, reveal, selector and attempted Beacon finish, preserving actual installation origins. -/
theorem post_valid (mark : PqxdhBeaconPhase2Shared.Secrets Shared → Origin)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder)
    (read : RawCtxReceive.FrameDecoder) (client : OracleComp (PostSpec extra S B) Result)
    (before : NativeFront M P I D K S B) (trace : PqxdhInitialOriginPost.Trace Origin S B) :
    All (Valid read) (PqxdhInitialOriginForwardPost.program (X := X) (Response := Response) (Shared := Shared)
      mark sender route read client before trace) := by
  induction client using OracleComp.inductionOn generalizing before trace with
  | pure value => trivial
  | query_bind request outside ih =>
      rw [PqxdhInitialOriginForwardPost.program_query]
      rcases request with (request | request) | request
      · exact record_valid sender route read request before trace outside _ ih
      · exact plain_valid read _ _ (fun reply => ih reply before trace)
      · cases request with
        | finish index raw => exact finish_valid mark read index raw before trace outside _ ih

private theorem finished_valid (mark : PqxdhBeaconPhase2Shared.Secrets Shared → Origin) (origin : Origin) (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder)
    (read : RawCtxReceive.FrameDecoder) (index : Fin S) (before : NativeFront M P I D K S B) (trace : PqxdhInitialOriginPost.Trace Origin S B)
    (outside : BuildResult → OracleComp (PostSpec extra S B) Result)
    (result : RustM (Option PqxdhServerRegistrationPublication.Response × PqxdhInitialOriginForwardBuilder.Publication M P)) :
    All (Valid read) (PqxdhInitialOriginForwardBuilder.finished (X := X) (Response := Response) (Shared := Shared)
      mark origin sender route read index before trace outside result) :=
  post_valid mark sender route read _ _ _

private theorem publication_valid (mark : PqxdhBeaconPhase2Shared.Secrets Shared → Origin) (origin : Origin) (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder)
    (read : RawCtxReceive.FrameDecoder) (index : Fin S) (before : NativeFront M P I D K S B) (trace : PqxdhInitialOriginPost.Trace Origin S B)
    (candidate : pqxdh.ServerRegistrationCandidate) (authenticated : Pqxdh.Bytes) (metadata : P)
    (outside : BuildResult → OracleComp (PostSpec extra S B) Result)
    (result : PqxdhInitialPendingPost.KernelOf RatchetChain × Option RawCtxSourceSend.Encrypted) :
    All (Valid read) (PqxdhInitialOriginForwardBuilder.publication (X := X) (Response := Response) (Shared := Shared)
      mark origin sender route read index before trace candidate authenticated metadata outside result) := by
  apply plain_valid read
  exact fun value => finished_valid mark origin sender route read index before trace outside (.ok value)

private theorem send_valid (mark : PqxdhBeaconPhase2Shared.Secrets Shared → Origin) (origin : Origin) (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder)
    (read : RawCtxReceive.FrameDecoder) (index : Fin S) (before : NativeFront M P I D K S B) (trace : PqxdhInitialOriginPost.Trace Origin S B)
    (candidate : pqxdh.ServerRegistrationCandidate) (authenticated : Pqxdh.Bytes) (metadata : P)
    (outside : BuildResult → OracleComp (PostSpec extra S B) Result)
    (kernel : PqxdhInitialPendingPost.KernelOf RatchetChain) :
    All (Valid read) (PqxdhInitialOriginForwardBuilder.send (X := X) (Response := Response) (Shared := Shared)
      mark origin sender route read index before trace candidate authenticated metadata outside kernel) := by
  unfold PqxdhInitialOriginForwardBuilder.send
  cases start : RawCtxChainSend.normalBegin kernel (PqxdhServerRegistrationPublication.firstContext candidate authenticated) with
  | exhausted entry context => exact publication_valid mark origin sender route read index before trace candidate authenticated metadata outside _
  | requested pending =>
      exact ⟨(fun tag same => by cases same; trivial), fun reply =>
        ⟨(fun _ impossible => by cases impossible), fun sealed =>
          publication_valid mark origin sender route read index before trace candidate authenticated metadata outside _⟩⟩

private theorem candidate_valid (mark : PqxdhBeaconPhase2Shared.Secrets Shared → Origin) (origin : Origin) (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder)
    (read : RawCtxReceive.FrameDecoder) (index : Fin S) (before : NativeFront M P I D K S B) (trace : PqxdhInitialOriginPost.Trace Origin S B)
    (initial : RustM (PqxdhInitialPendingPost.KernelOf RatchetChain))
    (candidate : pqxdh.ServerRegistrationCandidate) (data : Option Pqxdh.Bytes) (metadata : P)
    (outside : BuildResult → OracleComp (PostSpec extra S B) Result) :
    All (Valid read) (PqxdhInitialOriginForwardBuilder.candidate (X := X) (Response := Response) (Shared := Shared)
      mark origin sender route read index before trace initial candidate data metadata outside) := by
  unfold PqxdhInitialOriginForwardBuilder.candidate
  apply plain_valid read
  intro valid
  cases valid
  · exact finished_valid mark origin sender route read index before trace outside _
  · simp only [Bool.not_true, Bool.false_eq_true, ite_false]
    apply plain_valid read
    intro reserved
    cases reserved
    · exact finished_valid mark origin sender route read index before trace outside _
    · simp only [Bool.not_true, Bool.false_eq_true, ite_false]
      cases initial with
      | fail error => exact finished_valid mark origin sender route read index before trace outside _
      | div => exact finished_valid mark origin sender route read index before trace outside _
      | ok kernel =>
          dsimp only
          split
          · exact finished_valid mark origin sender route read index before trace outside _
          · split
            · apply plain_valid read
              intro allocated
              cases allocated
              · exact finished_valid mark origin sender route read index before trace outside _
              · simp only [Bool.not_true, Bool.false_eq_true, ite_false]
                cases binding : candidate.key_id_binding with
                | fail error => exact finished_valid mark origin sender route read index before trace outside _
                | div => exact finished_valid mark origin sender route read index before trace outside _
                | ok binding => exact send_valid mark origin sender route read index before trace candidate _ metadata outside kernel
            · exact finished_valid mark origin sender route read index before trace outside _

private theorem used_valid (mark : PqxdhBeaconPhase2Shared.Secrets Shared → Origin) (origin : Origin) (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder)
    (read : RawCtxReceive.FrameDecoder) (index : Fin S) (before : NativeFront M P I D K S B) (trace : PqxdhInitialOriginPost.Trace Origin S B)
    (initial : RustM (PqxdhInitialPendingPost.KernelOf RatchetChain))
    (pending : PqxdhRegistrationInputs.UsedInput) (data : Option Pqxdh.Bytes) (metadata : P)
    (outside : BuildResult → OracleComp (PostSpec extra S B) Result) :
    All (Valid read) (PqxdhInitialOriginForwardBuilder.used (X := X) (Response := Response) (Shared := Shared)
      mark origin sender route read index before trace initial pending data metadata outside) := by
  unfold PqxdhInitialOriginForwardBuilder.used
  dsimp only
  cases nextResult : pqxdh.server_next_key_id (PqxdhInitialPendingBuilder.selected sender index before).control with
  | fail error => exact finished_valid mark origin sender route read index before trace outside _
  | div => exact finished_valid mark origin sender route read index before trace outside _
  | ok value =>
      cases value with
      | Err error => exact finished_valid mark origin sender route read index before trace outside _
      | Ok key =>
          dsimp only
          cases preparation : PqxdhRegistrationInputs.prepare
            (PqxdhInitialPendingBuilder.selected sender index before).control pending
            ⟨(PqxdhInitialPendingBuilder.selected sender index before).server.identity,
              (PqxdhInitialPendingBuilder.selected sender index before).identityKeyId⟩
            (if ((PqxdhInitialPendingBuilder.selected sender index before).server.peers key).isSome
              then pqxdh.KeyIdAvailability.Occupied else .Available) with
          | fail error => exact finished_valid mark origin sender route read index before trace outside _
          | div => exact finished_valid mark origin sender route read index before trace outside _
          | ok prepared =>
              cases prepared with
              | Err error => exact finished_valid mark origin sender route read index before trace outside _
              | Ok prepared => exact candidate_valid mark origin sender route read index before trace initial prepared data metadata outside

/-- Every descriptor in the complete accepted builder and post source retains its raw receive admission certificate, including all post branches after the first private send. -/
theorem program_valid (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (mark : PqxdhBeaconPhase2Shared.Secrets Shared → Origin) (origin : Origin) (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (read : RawCtxReceive.FrameDecoder)
    (initial : RustM (PqxdhInitialPendingPost.KernelOf RatchetChain)) (index : Fin S) (metadata : P)
    (ready : PqxdhPrivateAcceptedRoot.Ready) (outside : BuildResult → OracleComp (PostSpec extra S B) Result)
    (before : NativeFront M P I D K S B) (trace : PqxdhInitialOriginPost.Trace Origin S B) :
    All (Valid read) (PqxdhInitialOriginForwardBuilder.program (X := X) (Response := Response) (Shared := Shared)
      source mark origin sender route read initial index metadata ready outside before trace) :=
  used_valid mark origin sender route read index _ trace initial _ ready.application metadata outside

/-- A supported executable full-source scan returns its own raw-admission-certified descriptor with its actual origin and publication metadata. -/
theorem carried_valid {State : Type}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (mark : PqxdhBeaconPhase2Shared.Secrets Shared → Origin) (origin : Origin)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (read : RawCtxReceive.FrameDecoder)
    (initialKernel : RustM (PqxdhInitialPendingPost.KernelOf RatchetChain)) (index : Fin S) (metadata : P)
    (ready : PqxdhPrivateAcceptedRoot.Ready) (outside : BuildResult → OracleComp (PostSpec extra S B) Result)
    (before : NativeFront M P I D K S B) (trace : PqxdhInitialOriginPost.Trace Origin S B)
    (chosen : (Base extra RatchetChain I D K X Response Shared S B).Domain → State → Bool)
    (selection : ∀ query state, chosen query state = true → PqxdhInitialForwardPost.selected query = true)
    (impl : QueryImpl (Base extra RatchetChain I D K X Response Shared S B) (StateT State ProbComp))
    (initial reached : State) (context : PqxdhInitialOriginContext.Context extra M P I D K Result Origin S B)
    (supported : RawCtxForwardScan.Cut.pending context reached ∈ support
      (RawCtxForwardScan.scan PqxdhInitialForwardPost.selected chosen selection impl
        (PqxdhInitialOriginForwardBuilder.program source mark origin sender route read initialKernel index metadata ready outside before trace)
        (PqxdhInitialOriginForwardBuilder.program_covered source mark origin sender route read initialKernel index metadata ready outside before trace) initial)) :
    Valid read context :=
  scan_all PqxdhInitialForwardPost.selected chosen selection impl (Valid read) _
    (PqxdhInitialOriginForwardBuilder.program_covered source mark origin sender route read initialKernel index metadata ready outside before trace)
    (program_valid source mark origin sender route read initialKernel index metadata ready outside before trace)
    initial reached context supported

end BeaconcryptCore.Computational.PqxdhInitialDescriptorScope

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialDescriptorScope.post_valid' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialDescriptorScope.post_valid

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialDescriptorScope.program_valid' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialDescriptorScope.program_valid

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialDescriptorScope.carried_valid' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialDescriptorScope.carried_valid
