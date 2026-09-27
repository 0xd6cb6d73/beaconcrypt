import BeaconcryptCore.Computational.RawCtxForwardOwnerCertificates
import BeaconcryptCore.Computational.RawCtxSelectedReceiveScope

/-!
Saved receive descriptors inherit their raw bytes, decoded frame, validation and target from the actual owner prelude. These certificates hold at every annotated node and for every typed reply, before any selected KDF or opening succeeds. They concern the literal descriptor retained by the source scanner.
-/
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.refined ratchet.concrete
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RawCtxForwardOwnerScope
open RawCtxForwardOwner RawCtxForwardTags RawCtxSelectedFamilyContext
variable {Metadata Result : Type}

/-- Exact source admission facts needed to compile a saved receive tail to raw CTX. Send descriptors do not consume this raw receive interface. -/
def Valid (read : RawCtxReceive.FrameDecoder) : OwnerContext Metadata Result → Prop
  | .receive before _ pending => pending.context.raw.isEmpty = false ∧
      read pending.context.raw = some pending.context.frame ∧
      RawCtxReceive.ValidFrame before.expectedSender before.associatedData pending.context.frame ∧
      pending.context.associatedData = before.associatedData ∧ pending.target = pending.context.frame.sequence
  | .send _ _ _ => True

abbrev Scope (target : Std.U64) (context : RawCtxWholeOwner.OpenContext)
    (effect : RawCtxChainReceive.Effect RatchetChain RatchetChain RatchetMaterial RawCtxWholeOwner.OpenContext) :=
  RawCtxSelectedReceiveScope.Scope target context (RawCtxChainReceive.nativeEffect id id effect)

/-- Actual admission carries the original decoded target and context, including all cached and rejecting branches. -/
theorem begin_scope (kernel : RawCtxPendingOwnerQueries.Kernel RatchetChain)
    (target : Std.U64) (context : RawCtxWholeOwner.OpenContext) :
    Scope target context (RawCtxChainReceive.normalBegin kernel target context) := by
  unfold Scope
  rw [← RawCtxChainReceive.normalBegin_native]
  exact RawCtxSelectedReceiveScope.begin_scope id _ _ _

/-- Every complete typed derivation reply keeps the target and raw context before the next source effect. -/
theorem resume_scope
    (pending : RawCtxChainReceive.Kdf RatchetChain RatchetChain RatchetMaterial RawCtxWholeOwner.OpenContext)
    (reply : RatchetChain × RatchetMaterial) :
    Scope pending.target pending.context (RawCtxChainReceive.normalResume pending reply) := by
  unfold Scope
  rw [← RawCtxChainReceive.normalResume_native]
  exact RawCtxSelectedReceiveScope.resume_scope (RawCtxChainReceive.nativeKdf id id pending) reply

/-- Every receive descriptor constructed during the actual skipped-key loop retains the admitted raw context and decoded target under every reply. -/
theorem receive_valid (read : RawCtxReceive.FrameDecoder)
    (before : Owner Metadata)
    (outside : core.option.Option RawCtxWholeOwner.Decrypted → OracleComp SourceSpec Result)
    (after : (RawCtxPendingOwnerQueries.Kernel RatchetChain × core.option.Option RawCtxWholeOwner.Decrypted) →
      OracleComp (Spec Metadata Result) (Result × Owner Metadata))
    (later : ∀ result, All (Valid read) (after result))
    (context : RawCtxWholeOwner.OpenContext)
    (nonempty : context.raw.isEmpty = false) (decoded : read context.raw = some context.frame)
    (valid : RawCtxReceive.ValidFrame before.expectedSender before.associatedData context.frame)
    (associated : context.associatedData = before.associatedData)
    (effect : RawCtxChainReceive.Effect RatchetChain RatchetChain RatchetMaterial RawCtxWholeOwner.OpenContext)
    (inScope : Scope context.frame.sequence context effect) :
    All (Valid read) (receive before outside after effect) := by
  generalize depth : RawCtxChainReceive.effectRank effect = count
  induction count using Nat.strong_induction_on generalizing effect with
  | h count ih =>
    cases effect with
    | rejected entry actual => simpa only [receive] using later (entry, .None)
    | openRequested pending =>
        rw [receive, query_all]
        exact ⟨(fun _ impossible => by cases impossible), fun _ => later _⟩
    | kdfRequested pending =>
        change pending.target = context.frame.sequence ∧ pending.context = context at inScope
        rw [receive, query_all]
        refine ⟨?_, ?_⟩
        · intro tag same
          cases same
          simp only [Valid, inScope.1, inScope.2]
          exact ⟨nonempty, decoded, valid, associated, True.intro⟩
        · intro reply
          exact ih _ (depth ▸ RawCtxChainReceive.normalResume_rank pending reply) _
            (by simpa only [inScope.1, inScope.2] using resume_scope pending reply) rfl

/-- A saved send uses no raw receive premise; its full sealing continuation preserves the certificates of later operations. -/
theorem send_valid (read : RawCtxReceive.FrameDecoder)
    (before : Owner Metadata)
    (outside : Option RawCtxSourceSend.Encrypted → OracleComp SourceSpec Result)
    (after : (RawCtxPendingOwnerQueries.Kernel RatchetChain × Option RawCtxSourceSend.Encrypted) →
      OracleComp (Spec Metadata Result) (Result × Owner Metadata))
    (later : ∀ result, All (Valid read) (after result))
    (start : RawCtxChainSend.Start RatchetChain RatchetChain RatchetMaterial RawCtxSourceSend.SealContext) :
    All (Valid read) (send before outside after start) := by
  cases start with
  | exhausted entry context => simpa only [send] using later (entry, none)
  | requested pending =>
      rw [send, query_all]
      refine ⟨fun tag same => by cases same; trivial, fun reply => ?_⟩
      rw [query_all]
      exact ⟨(fun _ impossible => by cases impossible), fun _ => later _⟩

/-- Every literal descriptor in an arbitrary adaptive owner source program has the raw admission facts required by the CTX receive interface. These are derived from the actual parser and validation branches. -/
theorem program_valid (sender : Std.U64) (read : RawCtxReceive.FrameDecoder)
    (client : OracleComp SourceSpec Result) (state : Owner Metadata) :
    All (Valid read) (program sender read client state) := by
  induction client using OracleComp.inductionOn generalizing state with
  | pure value => trivial
  | query_bind query outside ih =>
      rw [program_query]
      rcases query with (plaintext | raw) | publicQuery
      all_goals dsimp only
      · split
        · exact ih _ _
        · exact send_valid read _ _ _ (fun result => ih result.2 _) _
      · by_cases empty : raw.isEmpty = true
        · simp only [empty, ite_true]
          exact ih _ _
        · simp only [empty, Bool.false_eq_true, ite_false]
          cases decoded : read raw with
          | none => exact ih _ _
          | some frame =>
              by_cases valid : RawCtxReceive.ValidFrame state.expectedSender state.associatedData frame
              · simp only [valid, ite_true]
                exact receive_valid read _ _ _ (fun result => ih (RawCtxChainOwner.publish state result).1 _)
                  ⟨raw, frame, state.associatedData⟩ (by simpa using empty) decoded valid rfl _
                  (begin_scope state.kernel frame.sequence ⟨raw, frame, state.associatedData⟩)
              · simp only [valid, ite_false]
                exact ih _ _
      · rw [query_all]
        exact ⟨(fun _ impossible => by cases impossible), fun reply => ih reply state⟩

/-- A supported source scan returns the very descriptor carrying the raw admission certificate; no equal-frame replacement or success premise is needed. -/
theorem carried_valid {State : Type} (sender : Std.U64) (read : RawCtxReceive.FrameDecoder)
    (client : OracleComp SourceSpec Result) (before : Owner Metadata)
    (chosen : Base.Domain → State → Bool)
    (selection : ∀ query state, chosen query state = true → RawCtxPendingMixedPrefix.ownerSelected query = true)
    (impl : QueryImpl Base (StateT State ProbComp)) (initial reached : State)
    (context : OwnerContext Metadata Result)
    (supported : RawCtxForwardScan.Cut.pending context reached ∈ support
      (RawCtxForwardScan.scan RawCtxPendingMixedPrefix.ownerSelected chosen selection impl
        (program sender read client before) (program_covered sender read client before) initial)) :
    Valid read context :=
  scan_all RawCtxPendingMixedPrefix.ownerSelected chosen selection impl (Valid read) _
    (program_covered sender read client before) (program_valid sender read client before) initial reached context supported

end BeaconcryptCore.Computational.RawCtxForwardOwnerScope

/-- info: 'BeaconcryptCore.Computational.RawCtxForwardOwnerScope.begin_scope' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxForwardOwnerScope.begin_scope

/-- info: 'BeaconcryptCore.Computational.RawCtxForwardOwnerScope.resume_scope' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxForwardOwnerScope.resume_scope

/-- info: 'BeaconcryptCore.Computational.RawCtxForwardOwnerScope.receive_valid' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxForwardOwnerScope.receive_valid

/-- info: 'BeaconcryptCore.Computational.RawCtxForwardOwnerScope.send_valid' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxForwardOwnerScope.send_valid

/-- info: 'BeaconcryptCore.Computational.RawCtxForwardOwnerScope.program_valid' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxForwardOwnerScope.program_valid

/-- info: 'BeaconcryptCore.Computational.RawCtxForwardOwnerScope.carried_valid' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxForwardOwnerScope.carried_valid
