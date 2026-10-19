import BeaconcryptCore.Computational.PqxdhInitialNativeAuditCarried
import BeaconcryptCore.Computational.PqxdhInitialStoppedDisclosure

/-!
The exact descriptor constructed by the full source carries its actual saved disclosure history. Each original read can add one32-byte value, while record operations, initializer attempts, publication and selectors preserve that history. The carried history bound is derived from the original bounded source client, including the first-builder prefix; it is not assumed for an arbitrary same-frame descriptor.
-/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.PqxdhInitialHistoryBudget
open PqxdhInitialPostContext RawCtxForwardTags PqxdhInitialOriginContext
open PqxdhInitialBuilderContext (BuildResult)
variable {ι M P I D K X Response Shared Result Origin : Type} {extra : OracleSpec ι} {S B : Nat}

def knownLength (prior : List RatchetChain) (history : RawCtxProtocolReveals.History S B) : Nat :=
  (RawCtxFamilyFreshnessProxy.knownInputs prior history).length

def SavedBound (prior : List RatchetChain) (cap : Nat) (context : Context extra M P I D K Result Origin S B) : Prop :=
  knownLength prior (PqxdhInitialStoppedDisclosure.history context) ≤ cap

private theorem all_true {Tag Value κ : Type} {base : OracleSpec κ}
    (client : OracleComp (RawCtxForwardAnnotation.Spec Tag base) Value) : All (fun _ => True) client := by
  induction client using OracleComp.inductionOn with
  | pure _ => trivial
  | query_bind _ _ ih => exact ⟨fun _ _ => True.intro, ih⟩

private theorem record_bound (prior : List RatchetChain) (cap : Nat)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (request : (RawCtxProtocolReveals.SourceSpec S B).Domain) (before : NativeFront M P I D K S B)
    (trace : PqxdhInitialOriginPost.Trace Origin S B)
    (outside : (RawCtxProtocolReveals.SourceSpec S B).Range request → OracleComp (PostSpec extra S B) Result)
    (after : (RawCtxProtocolReveals.SourceSpec S B).Range request → NativeFront M P I D K S B → PqxdhInitialOriginPost.Trace Origin S B →
      OracleComp (PqxdhInitialOriginForwardPost.Spec extra M P I D K X Response Shared Result Origin S B)
        (Result × (NativeFront M P I D K S B × PqxdhInitialOriginPost.Trace Origin S B)))
    (available : knownLength prior before.roles.2 + 1 ≤ cap)
    (later : ∀ reply updated saved, knownLength prior updated.roles.2 ≤ knownLength prior before.roles.2 + 1 →
      All (SavedBound prior cap) (after reply updated saved)) :
    All (SavedBound prior cap) (PqxdhInitialOriginForwardPost.record sender route decode request before trace outside after) := by
  cases request with
  | inl request =>
      have single : RawCtxForwardLive.program sender route decode
          ((RawCtxProtocolReveals.SourceSpec S B).query (.inl request) : OracleComp (RawCtxProtocolReveals.SourceSpec S B) _) before.roles =
          RawCtxForwardLive.family sender route decode request before.roles pure (fun reply updated => pure (reply, updated)) := rfl
      unfold PqxdhInitialOriginForwardPost.record
      rw [single]
      simp only [RawCtxForwardLive.family, RawCtxForwardAnnotationLift.lift, simulateQ_bind, simulateQ_pure]
      simp only [pure_bind, bind_assoc]
      apply bind_all
      · apply lift_all (fun inner => knownLength prior (RawCtxFamilyStoppedResources.history inner) ≤ cap)
          (SavedBound prior cap) (fun inner => ⟨.inl (.record (.inl request) before outside inner), trace, none⟩)
          (fun _ valid => valid)
        apply lift_all (fun _ => True) _ (fun inner => RawCtxSelectedFamilyContext.Context.family request before.roles.2 pure inner)
          (fun _ _ => (Nat.le_add_right _ 1).trans available) _ (all_true _)
      · intro result
        exact later _ _ _ (Nat.le_add_right _ 1)
  | inr request =>
      exact ⟨(fun _ impossible => by cases impossible), fun reply =>
        later _ _ _ (RawCtxFamilyFreshnessProxy.knownInputs_note_length prior before.roles.2 ⟨request, reply⟩)⟩

private theorem plain_bound {Value : Type} (prior : List RatchetChain) (cap : Nat)
    (client : OracleComp (Base extra RatchetChain I D K X Response Shared S B) Value)
    (after : Value → OracleComp (PqxdhInitialOriginForwardPost.Spec extra M P I D K X Response Shared Result Origin S B)
      (Result × (NativeFront M P I D K S B × PqxdhInitialOriginPost.Trace Origin S B)))
    (later : ∀ value, All (SavedBound prior cap) (after value)) :
    All (SavedBound prior cap) (simulateQ PqxdhInitialOriginForwardPost.plain client >>= after) := by
  induction client using OracleComp.inductionOn with
  | pure value => exact later value
  | query_bind query outside ih => exact ⟨(fun _ impossible => by cases impossible), fun reply => ih reply⟩

private theorem finish_bound (prior : List RatchetChain) (cap : Nat)
    (mark : PqxdhBeaconPhase2Shared.Secrets Shared → Origin) (decode : RawCtxReceive.FrameDecoder)
    (index : Fin B) (raw : Pqxdh.Bytes) (before : NativeFront M P I D K S B) (trace : PqxdhInitialOriginPost.Trace Origin S B)
    (outside : Option Pqxdh.Bytes → OracleComp (PostSpec extra S B) Result)
    (after : Option Pqxdh.Bytes → NativeFront M P I D K S B → PqxdhInitialOriginPost.Trace Origin S B →
      OracleComp (PqxdhInitialOriginForwardPost.Spec extra M P I D K X Response Shared Result Origin S B)
        (Result × (NativeFront M P I D K S B × PqxdhInitialOriginPost.Trace Origin S B)))
    (available : knownLength prior before.roles.2 ≤ cap)
    (later : ∀ reply updated saved, knownLength prior updated.roles.2 = knownLength prior before.roles.2 →
      All (SavedBound prior cap) (after reply updated saved)) :
    All (SavedBound prior cap) (PqxdhInitialOriginForwardPost.finish mark decode index raw before trace outside after) := by
  unfold PqxdhInitialOriginForwardPost.finish
  cases phase : (before.roles.1.2 index).beacon.phase
  case initSent control prekey oneTime kem =>
    dsimp only
    rw [QueryImpl.simulateQ_compose]
    apply plain_bound
    intro prepared
    cases prepared with
    | none => exact later _ _ _ rfl
    | some prepared =>
        apply plain_bound
        intro kernel
        cases kernel with
        | none => exact later _ _ _ rfl
        | some kernel =>
            apply plain_bound
            intro application
            cases application with
            | none => exact later _ _ _ rfl
            | some application =>
                apply bind_all
                · unfold PqxdhInitialOriginForwardPost.ownerLift
                  apply lift_all (fun _ => True) (SavedBound prior cap)
                    (fun inner => ⟨.inl (.finish index before control
                      (PqxdhBeaconPhase2Shared.clearedMetadata prepared.metadata) outside inner), trace, some (mark prepared.root)⟩)
                    (fun _ _ => available) _ (all_true _)
                · exact fun result => later _ _ _ rfl
  all_goals exact later _ _ _ rfl

/-- The actual full post client constructs only descriptors whose saved disclosed-value count is bounded by its original initial history and source request allowance. -/
theorem post_bound (prior : List RatchetChain) (cap : Nat)
    (mark : PqxdhBeaconPhase2Shared.Secrets Shared → Origin) (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder)
    (decode : RawCtxReceive.FrameDecoder) (client : OracleComp (PostSpec extra S B) Result)
    (qPost : Nat) (bounded : client.IsTotalQueryBound qPost) (before : NativeFront M P I D K S B)
    (trace : PqxdhInitialOriginPost.Trace Origin S B) (available : knownLength prior before.roles.2 + qPost ≤ cap) :
    All (SavedBound prior cap) (PqxdhInitialOriginForwardPost.program (X := X) (Response := Response) (Shared := Shared)
      mark sender route decode client before trace) := by
  induction client using OracleComp.inductionOn generalizing qPost before trace with
  | pure value => trivial
  | query_bind request outside ih =>
      rw [isTotalQueryBound_query_bind_iff] at bounded
      have later : ∀ reply (updated : NativeFront M P I D K S B) (saved : PqxdhInitialOriginPost.Trace Origin S B),
          knownLength prior updated.roles.2 ≤ knownLength prior before.roles.2 + 1 →
          All (SavedBound prior cap) (PqxdhInitialOriginForwardPost.program (X := X) (Response := Response) (Shared := Shared)
            mark sender route decode (outside reply) updated saved) := by
        intro reply updated saved growth
        exact ih reply (qPost - 1) (bounded.2 reply) updated saved (by omega)
      rw [PqxdhInitialOriginForwardPost.program_query]
      rcases request with (request | request) | request
      · exact record_bound prior cap sender route decode request before trace outside _ (by omega) later
      · exact plain_bound prior cap _ _ (fun reply => later reply before trace (Nat.le_add_right _ 1))
      · cases request with
        | finish index raw =>
            apply finish_bound prior cap mark decode index raw before trace outside _ (by omega)
            intro reply updated saved unchanged
            exact later reply updated saved (by omega)

private theorem finished_bound (prior : List RatchetChain) (cap : Nat) (mark : PqxdhBeaconPhase2Shared.Secrets Shared → Origin) (origin : Origin) (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder)
    (decode : RawCtxReceive.FrameDecoder) (index : Fin S) (before : NativeFront M P I D K S B) (trace : PqxdhInitialOriginPost.Trace Origin S B)
    (outside : BuildResult → OracleComp (PostSpec extra S B) Result)
    (qPost : Nat) (bounded : ∀ reply, (outside reply).IsTotalQueryBound qPost)
    (available : knownLength prior before.roles.2 + qPost ≤ cap)
    (result : RustM (Option PqxdhServerRegistrationPublication.Response × PqxdhInitialOriginForwardBuilder.Publication M P)) :
    All (SavedBound prior cap) (PqxdhInitialOriginForwardBuilder.finished (X := X) (Response := Response) (Shared := Shared)
      mark origin sender route decode index before trace outside result) :=
by
  apply post_bound prior cap mark sender route decode _ qPost (bounded _) _ _
  cases result <;> exact available

private theorem builder_plain_bound {Value : Type} (prior : List RatchetChain) (cap : Nat)
    (client : OracleComp (Base extra RatchetChain I D K X Response Shared S B) Value)
    (after : Value → OracleComp (PqxdhInitialOriginForwardBuilder.Spec extra M P I D K X Response Shared Result Origin S B)
      (Result × (NativeFront M P I D K S B × PqxdhInitialOriginPost.Trace Origin S B)))
    (later : ∀ value, All (SavedBound prior cap) (after value)) :
    All (SavedBound prior cap) (simulateQ PqxdhInitialOriginForwardBuilder.plain client >>= after) := by
  induction client using OracleComp.inductionOn with
  | pure value => exact later value
  | query_bind query outside ih =>
      exact ⟨(fun _ impossible => by cases impossible), fun reply => ih reply⟩

private theorem publication_bound (prior : List RatchetChain) (cap : Nat) (mark : PqxdhBeaconPhase2Shared.Secrets Shared → Origin) (origin : Origin) (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder)
    (decode : RawCtxReceive.FrameDecoder) (index : Fin S) (before : NativeFront M P I D K S B) (trace : PqxdhInitialOriginPost.Trace Origin S B)
    (candidate : pqxdh.ServerRegistrationCandidate) (authenticated : Pqxdh.Bytes) (metadata : P)
    (outside : BuildResult → OracleComp (PostSpec extra S B) Result)
    (qPost : Nat) (bounded : ∀ reply, (outside reply).IsTotalQueryBound qPost)
    (available : knownLength prior before.roles.2 + qPost ≤ cap)
    (result : PqxdhInitialPendingPost.KernelOf RatchetChain × Option RawCtxSourceSend.Encrypted) :
    All (SavedBound prior cap) (PqxdhInitialOriginForwardBuilder.publication (X := X) (Response := Response) (Shared := Shared)
      mark origin sender route decode index before trace candidate authenticated metadata outside result) := by
  apply builder_plain_bound prior cap
  exact fun value => finished_bound prior cap mark origin sender route decode index before trace outside qPost bounded available (.ok value)

private theorem send_bound (prior : List RatchetChain) (cap : Nat) (mark : PqxdhBeaconPhase2Shared.Secrets Shared → Origin) (origin : Origin) (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder)
    (decode : RawCtxReceive.FrameDecoder) (index : Fin S) (before : NativeFront M P I D K S B) (trace : PqxdhInitialOriginPost.Trace Origin S B)
    (candidate : pqxdh.ServerRegistrationCandidate) (authenticated : Pqxdh.Bytes) (metadata : P)
    (outside : BuildResult → OracleComp (PostSpec extra S B) Result)
    (qPost : Nat) (bounded : ∀ reply, (outside reply).IsTotalQueryBound qPost)
    (available : knownLength prior before.roles.2 + qPost ≤ cap)
    (kernel : PqxdhInitialPendingPost.KernelOf RatchetChain) :
    All (SavedBound prior cap) (PqxdhInitialOriginForwardBuilder.send (X := X) (Response := Response) (Shared := Shared)
      mark origin sender route decode index before trace candidate authenticated metadata outside kernel) := by
  unfold PqxdhInitialOriginForwardBuilder.send
  cases start : RawCtxChainSend.normalBegin kernel (PqxdhServerRegistrationPublication.firstContext candidate authenticated) with
  | exhausted entry context => exact publication_bound prior cap mark origin sender route decode index before trace candidate authenticated metadata outside qPost bounded available _
  | requested pending =>
      exact ⟨(fun tag same => by cases same; exact (Nat.le_add_right _ qPost).trans available), fun reply =>
        ⟨(fun _ impossible => by cases impossible), fun sealed =>
          publication_bound prior cap mark origin sender route decode index before trace candidate authenticated metadata outside qPost bounded available _⟩⟩

private theorem candidate_bound (prior : List RatchetChain) (cap : Nat) (mark : PqxdhBeaconPhase2Shared.Secrets Shared → Origin) (origin : Origin) (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder)
    (decode : RawCtxReceive.FrameDecoder) (index : Fin S) (before : NativeFront M P I D K S B) (trace : PqxdhInitialOriginPost.Trace Origin S B)
    (initial : RustM (PqxdhInitialPendingPost.KernelOf RatchetChain))
    (candidate : pqxdh.ServerRegistrationCandidate) (data : Option Pqxdh.Bytes) (metadata : P)
    (outside : BuildResult → OracleComp (PostSpec extra S B) Result)
    (qPost : Nat) (bounded : ∀ reply, (outside reply).IsTotalQueryBound qPost)
    (available : knownLength prior before.roles.2 + qPost ≤ cap) :
    All (SavedBound prior cap) (PqxdhInitialOriginForwardBuilder.candidate (X := X) (Response := Response) (Shared := Shared)
      mark origin sender route decode index before trace initial candidate data metadata outside) := by
  unfold PqxdhInitialOriginForwardBuilder.candidate
  apply builder_plain_bound prior cap
  intro valid
  cases valid
  · exact finished_bound prior cap mark origin sender route decode index before trace outside qPost bounded available _
  · simp only [Bool.not_true, Bool.false_eq_true, ite_false]
    apply builder_plain_bound prior cap
    intro reserved
    cases reserved
    · exact finished_bound prior cap mark origin sender route decode index before trace outside qPost bounded available _
    · simp only [Bool.not_true, Bool.false_eq_true, ite_false]
      cases initial with
      | fail error => exact finished_bound prior cap mark origin sender route decode index before trace outside qPost bounded available _
      | div => exact finished_bound prior cap mark origin sender route decode index before trace outside qPost bounded available _
      | ok kernel =>
          dsimp only
          split
          · exact finished_bound prior cap mark origin sender route decode index before trace outside qPost bounded available _
          · split
            · apply builder_plain_bound prior cap
              intro allocated
              cases allocated
              · exact finished_bound prior cap mark origin sender route decode index before trace outside qPost bounded available _
              · simp only [Bool.not_true, Bool.false_eq_true, ite_false]
                cases binding : candidate.key_id_binding with
                | fail error => exact finished_bound prior cap mark origin sender route decode index before trace outside qPost bounded available _
                | div => exact finished_bound prior cap mark origin sender route decode index before trace outside qPost bounded available _
                | ok binding => exact send_bound prior cap mark origin sender route decode index before trace candidate _ metadata outside qPost bounded available kernel
            · exact finished_bound prior cap mark origin sender route decode index before trace outside qPost bounded available _

private theorem used_bound (prior : List RatchetChain) (cap : Nat) (mark : PqxdhBeaconPhase2Shared.Secrets Shared → Origin) (origin : Origin) (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder)
    (decode : RawCtxReceive.FrameDecoder) (index : Fin S) (before : NativeFront M P I D K S B) (trace : PqxdhInitialOriginPost.Trace Origin S B)
    (initial : RustM (PqxdhInitialPendingPost.KernelOf RatchetChain))
    (pending : PqxdhRegistrationInputs.UsedInput) (data : Option Pqxdh.Bytes) (metadata : P)
    (outside : BuildResult → OracleComp (PostSpec extra S B) Result)
    (qPost : Nat) (bounded : ∀ reply, (outside reply).IsTotalQueryBound qPost)
    (available : knownLength prior before.roles.2 + qPost ≤ cap) :
    All (SavedBound prior cap) (PqxdhInitialOriginForwardBuilder.used (X := X) (Response := Response) (Shared := Shared)
      mark origin sender route decode index before trace initial pending data metadata outside) := by
  unfold PqxdhInitialOriginForwardBuilder.used
  dsimp only
  cases nextResult : pqxdh.server_next_key_id (PqxdhInitialPendingBuilder.selected sender index before).control with
  | fail error => exact finished_bound prior cap mark origin sender route decode index before trace outside qPost bounded available _
  | div => exact finished_bound prior cap mark origin sender route decode index before trace outside qPost bounded available _
  | ok value =>
      cases value with
      | Err error => exact finished_bound prior cap mark origin sender route decode index before trace outside qPost bounded available _
      | Ok key =>
          dsimp only
          cases preparation : PqxdhRegistrationInputs.prepare
            (PqxdhInitialPendingBuilder.selected sender index before).control pending
            ⟨(PqxdhInitialPendingBuilder.selected sender index before).server.identity,
              (PqxdhInitialPendingBuilder.selected sender index before).identityKeyId⟩
            (if ((PqxdhInitialPendingBuilder.selected sender index before).server.peers key).isSome
              then pqxdh.KeyIdAvailability.Occupied else .Available) with
          | fail error => exact finished_bound prior cap mark origin sender route decode index before trace outside qPost bounded available _
          | div => exact finished_bound prior cap mark origin sender route decode index before trace outside qPost bounded available _
          | ok prepared =>
              cases prepared with
              | Err error => exact finished_bound prior cap mark origin sender route decode index before trace outside qPost bounded available _
              | Ok prepared => exact candidate_bound prior cap mark origin sender route decode index before trace initial prepared data metadata outside qPost bounded available

/-- Every descriptor constructed by the original first-builder and complete post schedule inherits its actual initial disclosed-value count plus the bounded original request allowance. -/
theorem program_bound (prior : List RatchetChain) (cap : Nat) (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (mark : PqxdhBeaconPhase2Shared.Secrets Shared → Origin) (origin : Origin) (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (initial : RustM (PqxdhInitialPendingPost.KernelOf RatchetChain)) (index : Fin S) (metadata : P)
    (ready : PqxdhPrivateAcceptedRoot.Ready) (outside : BuildResult → OracleComp (PostSpec extra S B) Result)
    (qPost : Nat) (bounded : ∀ reply, (outside reply).IsTotalQueryBound qPost)
    (before : NativeFront M P I D K S B) (trace : PqxdhInitialOriginPost.Trace Origin S B)
    (available : knownLength prior before.roles.2 + qPost ≤ cap) :
    All (SavedBound prior cap) (PqxdhInitialOriginForwardBuilder.program (X := X) (Response := Response) (Shared := Shared)
      source mark origin sender route decode initial index metadata ready outside before trace) :=
  used_bound prior cap mark origin sender route decode index _ trace initial _ ready.application metadata outside qPost bounded available


variable {A N C : Type}

/-- An actual supported audited source cut carries its own bounded saved disclosure history, including the precise inner LIVE history on record paths. -/
theorem carried_bound (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (pre : QueryImpl (PqxdhBeaconPhase2Shared.Spec I D K X Response Shared) (PqxdhInitialBeaconAmbient.Ambient A N C))
    (application : Response → PqxdhInitialBeaconAmbient.Ambient A N C (Option Pqxdh.Bytes))
    (initial : PqxdhBeaconPhase2Shared.Secrets Shared → PqxdhInitialBeaconAmbient.Ambient A N C PqxdhInitialNativeAudit.InitialReply)
    (selector : QueryImpl extra (PqxdhInitialBeaconAmbient.Ambient A N C))
    (aux : QueryImpl PqxdhServerRegistrationPublication.AuxSpec (PqxdhInitialBeaconAmbient.Ambient A N C))
    (mark : PqxdhBeaconPhase2Shared.Secrets Shared → Origin) (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder)
    (decode : RawCtxReceive.FrameDecoder) (execution : PqxdhInitialNativeCarried.Execution extra M P I D K Result Origin S B)
    (depth stage qPost : Nat) (bounded : ∀ reply, (execution.outside reply).IsTotalQueryBound qPost)
    (prior : List RatchetChain) (state reached : PqxdhInitialNativeAudit.State A N C)
    (context : Context extra M P I D K Result Origin S B)
    (supported : RawCtxForwardScan.Cut.pending context reached ∈ support
      (PqxdhInitialNativeAuditCarried.carried source writer pre application initial selector aux mark sender route decode execution depth stage state)) :
    knownLength prior (PqxdhInitialStoppedDisclosure.history context) ≤ knownLength prior execution.before.roles.2 + qPost :=
  scan_all _ _ _ _ (SavedBound prior (knownLength prior execution.before.roles.2 + qPost)) _ _
    (program_bound prior _ source mark execution.origin sender route decode execution.initial execution.index execution.metadata
      execution.ready execution.outside qPost bounded execution.before execution.trace (le_refl _)) state reached context supported

def seed (prior : List RatchetChain) (context : Context extra M P I D K Result Origin S B)
    (earlier : List PqxdhSecretInputKdf.RootOutput) : List PqxdhSecretInputKdf.RootOutput :=
  RawCtxFamilyFreshnessProxy.knownInputs prior (PqxdhInitialStoppedDisclosure.history context) ++ earlier

/-- The exact stopped observer seed includes every value in its actual saved disclosure history and retains the entire earlier audit. -/
theorem seed_includes (prior : List RatchetChain) (context : Context extra M P I D K Result Origin S B)
    (earlier : List PqxdhSecretInputKdf.RootOutput) :
    RawCtxFamilyFreshnessProxy.knownInputs prior (PqxdhInitialStoppedDisclosure.history context) ⊆ seed prior context earlier ∧
      earlier ⊆ seed prior context earlier := by
  exact ⟨List.subset_append_left _ _, List.subset_append_right _ _⟩

/-- The actual source history and chronological callback audit together give a computed complete initial-candidate cap for the stopped cryptographic observer. -/
theorem carried_seed (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (pre : QueryImpl (PqxdhBeaconPhase2Shared.Spec I D K X Response Shared) (PqxdhInitialBeaconAmbient.Ambient A N C))
    (application : Response → PqxdhInitialBeaconAmbient.Ambient A N C (Option Pqxdh.Bytes))
    (initial : PqxdhBeaconPhase2Shared.Secrets Shared → PqxdhInitialBeaconAmbient.Ambient A N C PqxdhInitialNativeAudit.InitialReply)
    (selector : QueryImpl extra (PqxdhInitialBeaconAmbient.Ambient A N C))
    (aux : QueryImpl PqxdhServerRegistrationPublication.AuxSpec (PqxdhInitialBeaconAmbient.Ambient A N C))
    (mark : PqxdhBeaconPhase2Shared.Secrets Shared → Origin) (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder)
    (decode : RawCtxReceive.FrameDecoder) (execution : PqxdhInitialNativeCarried.Execution extra M P I D K Result Origin S B)
    (depth stage qPost : Nat) (bounded : ∀ reply, (execution.outside reply).IsTotalQueryBound qPost)
    (prior : List RatchetChain) (state reached : PqxdhInitialNativeAudit.State A N C)
    (context : Context extra M P I D K Result Origin S B)
    (supported : RawCtxForwardScan.Cut.pending context reached ∈ support
      (PqxdhInitialNativeAuditCarried.carried source writer pre application initial selector aux mark sender route decode execution depth stage state)) :
    (seed prior context reached.2).length ≤ knownLength prior execution.before.roles.2 + qPost + state.2.length + 3 * (7 + qPost * 67) := by
  have history := carried_bound source writer pre application initial selector aux mark sender route decode execution
    depth stage qPost bounded prior state reached context supported
  obtain ⟨added, same, count⟩ := PqxdhInitialNativeAuditCarried.carried_audit source writer pre application initial selector aux
    mark sender route decode execution depth stage qPost bounded state (.pending context reached) supported
  change reached.2 = state.2 ++ added at same
  simp only [knownLength] at history ⊢
  simp only [seed, same, List.length_append]
  omega

end BeaconcryptCore.Computational.PqxdhInitialHistoryBudget

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialHistoryBudget.post_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialHistoryBudget.post_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialHistoryBudget.program_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialHistoryBudget.program_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialHistoryBudget.carried_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialHistoryBudget.carried_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialHistoryBudget.seed_includes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialHistoryBudget.seed_includes

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialHistoryBudget.carried_seed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialHistoryBudget.carried_seed
