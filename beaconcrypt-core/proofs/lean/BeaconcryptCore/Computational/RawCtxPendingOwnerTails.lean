import BeaconcryptCore.Computational.RawCtxPendingQueryTails

/-!
Every selected KDF occurrence in the actual mixed source schedule has a concrete original receive or send tail: complete pending resume/seal, exact owner publication, then the unchanged external source client. The pre-draw owner and that source client are retained separately from the new reply. Whole source induction discharges callback-origin obligations for arbitrary native or private-label chain payloads. Supported original cuts therefore derive the tail rather than assuming an arbitrary function on unavailable bytes can be retagged.

These are source syntax and provenance laws, not a fresh-input or security conclusion. A consuming native/label simulation must still preserve these concrete tails under its actual primitive interface and retained lookup. Snapshots, persistence and restoration are excluded.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.refined ratchet.concrete
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RawCtxPendingOwnerTails
open RawCtxPendingOwnerQueries

abbrev Owner (Chain Metadata : Type) := RawCtxChainOwner.State (Kernel Chain) Metadata
abbrev SourceSpec := RawCtxSelectedPublicTrace.SourceSpec

noncomputable def program {Chain Metadata Result : Type}
    (sender : Std.U64) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp SourceSpec Result) (state : Owner Chain Metadata) :
    OracleComp (Spec Chain) (Result × Owner Chain Metadata) :=
  (simulateQ (compiler sender decode) client).run state

noncomputable def receiveRest {Chain Metadata Result : Type}
    (sender : Std.U64) (decode : RawCtxReceive.FrameDecoder) (before : Owner Chain Metadata)
    (outside : core.option.Option RawCtxWholeOwner.Decrypted → OracleComp SourceSpec Result)
    (result : Kernel Chain × core.option.Option RawCtxWholeOwner.Decrypted) :
    OracleComp (Spec Chain) (Result × Owner Chain Metadata) :=
  let published := RawCtxChainOwner.publish before result
  program sender decode (outside published.1) published.2

noncomputable def receiveTail {Chain Metadata Result : Type}
    (sender : Std.U64) (decode : RawCtxReceive.FrameDecoder) (before : Owner Chain Metadata)
    (outside : core.option.Option RawCtxWholeOwner.Decrypted → OracleComp SourceSpec Result)
    (pending : RawCtxChainReceive.Kdf Chain Chain RatchetMaterial RawCtxWholeOwner.OpenContext)
    (reply : Chain × RatchetMaterial) : OracleComp (Spec Chain) (Result × Owner Chain Metadata) :=
  simulateQ receiveForward (RawCtxPendingReceiveQueries.program (RawCtxChainReceive.normalResume pending reply)) >>=
    receiveRest sender decode before outside

noncomputable def sendRest {Chain Metadata Result : Type}
    (sender : Std.U64) (decode : RawCtxReceive.FrameDecoder) (before : Owner Chain Metadata)
    (outside : Option RawCtxSourceSend.Encrypted → OracleComp SourceSpec Result)
    (result : Kernel Chain × Option RawCtxSourceSend.Encrypted) :
    OracleComp (Spec Chain) (Result × Owner Chain Metadata) :=
  program sender decode (outside result.2) {before with kernel := result.1}

noncomputable def sendTail {Chain Metadata Result : Type}
    (sender : Std.U64) (decode : RawCtxReceive.FrameDecoder) (before : Owner Chain Metadata)
    (outside : Option RawCtxSourceSend.Encrypted → OracleComp SourceSpec Result)
    (pending : RawCtxChainSend.Kdf Chain Chain RatchetMaterial RawCtxSourceSend.SealContext)
    (reply : Chain × RatchetMaterial) : OracleComp (Spec Chain) (Result × Owner Chain Metadata) := do
  let ready := RawCtxChainSend.ready pending reply
  let sealed ← (Spec Chain).query (.inr (.inl (.inr ready)))
  sendRest sender decode before outside (ready.advanced, sealed)

inductive Tail {Chain Metadata Result : Type} (sender : Std.U64) (decode : RawCtxReceive.FrameDecoder) :
    (query : (Spec Chain).Domain) →
      ((Spec Chain).Range query → OracleComp (Spec Chain) (Result × Owner Chain Metadata)) → Prop where
  | receive (before : Owner Chain Metadata)
      (outside : core.option.Option RawCtxWholeOwner.Decrypted → OracleComp SourceSpec Result)
      (pending : RawCtxChainReceive.Kdf Chain Chain RatchetMaterial RawCtxWholeOwner.OpenContext) :
      Tail sender decode (.inl (.inl pending)) (receiveTail sender decode before outside pending)
  | send (before : Owner Chain Metadata)
      (outside : Option RawCtxSourceSend.Encrypted → OracleComp SourceSpec Result)
      (pending : RawCtxChainSend.Kdf Chain Chain RatchetMaterial RawCtxSourceSend.SealContext) :
      Tail sender decode (.inr (.inl (.inl pending))) (sendTail sender decode before outside pending)

/-- The actual public source query completes before its original adaptive continuation receives the reply. -/
theorem program_query {Chain Metadata Result : Type}
    (sender : Std.U64) (decode : RawCtxReceive.FrameDecoder) (query : SourceSpec.Domain)
    (outside : SourceSpec.Range query → OracleComp SourceSpec Result) (state : Owner Chain Metadata) :
    program sender decode (SourceSpec.query query >>= outside) state =
      (do let result ← (compiler sender decode query).run state
          program sender decode (outside result.1) result.2) := rfl

noncomputable def receiveProgram {Chain Metadata Result : Type}
    (sender : Std.U64) (decode : RawCtxReceive.FrameDecoder) (before : Owner Chain Metadata)
    (outside : core.option.Option RawCtxWholeOwner.Decrypted → OracleComp SourceSpec Result)
    (effect : RawCtxChainReceive.Effect Chain Chain RatchetMaterial RawCtxWholeOwner.OpenContext) :
    OracleComp (Spec Chain) (Result × Owner Chain Metadata) :=
  simulateQ receiveForward (RawCtxPendingReceiveQueries.program effect) >>=
    receiveRest sender decode before outside

/-- A reached original receive KDF is followed by its whole resume, owner publication and original source continuation. -/
theorem receive_requested {Chain Metadata Result : Type}
    (sender : Std.U64) (decode : RawCtxReceive.FrameDecoder) (before : Owner Chain Metadata)
    (outside : core.option.Option RawCtxWholeOwner.Decrypted → OracleComp SourceSpec Result)
    (pending : RawCtxChainReceive.Kdf Chain Chain RatchetMaterial RawCtxWholeOwner.OpenContext) :
    receiveProgram sender decode before outside (.kdfRequested pending) =
      (((Spec Chain).query (.inl (.inl pending)) : OracleComp (Spec Chain) (Chain × RatchetMaterial)) >>=
        receiveTail sender decode before outside pending) := by
  simp only [receiveProgram, RawCtxPendingReceiveQueries.program, simulateQ_bind,
    simulateQ_spec_query, receiveForward, bind_assoc]
  rfl

/-- A completed receive opening publishes its exact optional reply before the original outer client continues. -/
theorem receive_opening {Chain Metadata Result : Type}
    (sender : Std.U64) (decode : RawCtxReceive.FrameDecoder) (before : Owner Chain Metadata)
    (outside : core.option.Option RawCtxWholeOwner.Decrypted → OracleComp SourceSpec Result)
    (pending : RawCtxInterpretedOpening.Opening Chain Chain RatchetMaterial RawCtxWholeOwner.OpenContext) :
    receiveProgram sender decode before outside (.openRequested pending) =
      (((Spec Chain).query (.inl (.inr pending)) : OracleComp (Spec Chain) (core.option.Option RawCtxWholeOwner.Decrypted)) >>=
        fun reply => receiveRest sender decode before outside (RawCtxChainReceive.normalFinish pending reply)) := by
  simp only [receiveProgram, RawCtxPendingReceiveQueries.program, simulateQ_bind,
    simulateQ_spec_query, simulateQ_pure, receiveForward, bind_assoc, pure_bind]
  rfl

/-- Receive rejection retains the original kernel and publishes one failed original attempt. -/
theorem receive_rejected {Chain Metadata Result : Type}
    (sender : Std.U64) (decode : RawCtxReceive.FrameDecoder) (before : Owner Chain Metadata)
    (outside : core.option.Option RawCtxWholeOwner.Decrypted → OracleComp SourceSpec Result)
    (entry : Kernel Chain) (context : RawCtxWholeOwner.OpenContext) :
    receiveProgram sender decode before outside (.rejected entry context) =
      receiveRest sender decode before outside (entry, .None) := by
  simp only [receiveProgram, RawCtxPendingReceiveQueries.program, simulateQ_pure, pure_bind]

noncomputable def sendProgram {Chain Metadata Result : Type}
    (sender : Std.U64) (decode : RawCtxReceive.FrameDecoder) (before : Owner Chain Metadata)
    (outside : Option RawCtxSourceSend.Encrypted → OracleComp SourceSpec Result)
    (start : RawCtxChainSend.Start Chain Chain RatchetMaterial RawCtxSourceSend.SealContext) :
    OracleComp (Spec Chain) (Result × Owner Chain Metadata) :=
  simulateQ sendForward (RawCtxPendingOwnerQueries.sendProgram start) >>=
    sendRest sender decode before outside

/-- The actual send KDF precedes the complete advanced sealing tail and unchanged outer source client. -/
theorem send_requested {Chain Metadata Result : Type}
    (sender : Std.U64) (decode : RawCtxReceive.FrameDecoder) (before : Owner Chain Metadata)
    (outside : Option RawCtxSourceSend.Encrypted → OracleComp SourceSpec Result)
    (pending : RawCtxChainSend.Kdf Chain Chain RatchetMaterial RawCtxSourceSend.SealContext) :
    sendProgram sender decode before outside (.requested pending) =
      (((Spec Chain).query (.inr (.inl (.inl pending))) : OracleComp (Spec Chain) (Chain × RatchetMaterial)) >>=
        sendTail sender decode before outside pending) := by
  simp only [sendProgram, RawCtxPendingOwnerQueries.sendProgram, simulateQ_bind,
    simulateQ_spec_query, simulateQ_pure, sendForward, bind_assoc, pure_bind]
  rfl

open RawCtxQueryOccurrence

set_option backward.isDefEq.respectTransparency false in
/-- Every selected occurrence in the actual mixed source schedule has an original receive or send tail and its unchanged public source continuation. -/
theorem program_tail {Chain Metadata Result : Type}
    (sender : Std.U64) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp SourceSpec Result) (state : Owner Chain Metadata)
    (query : (Spec Chain).Domain)
    (next : (Spec Chain).Range query → OracleComp (Spec Chain) (Result × Owner Chain Metadata))
    (occurs : Occurs query next (program sender decode client state))
    (selected : RawCtxPendingMixedPrefix.ownerSelected query = true) : Tail sender decode query next := by
  induction client using OracleComp.inductionOn generalizing state query next with
  | pure value => exact (pure_impossible query next (value, state) occurs).elim
  | query_bind request outside ih =>
      rw [program_query] at occurs
      rcases request with (plaintext | raw) | externalRequest
      · simp only [compiler, RawCtxChainOwner.ownerImpl, RawCtxChainOwner.sendOwner, StateT.run] at occurs
        by_cases empty : plaintext.isEmpty = true
        · simp only [empty, ite_true, pure_bind] at occurs
          exact ih none state query next occurs selected
        · simp only [empty, Bool.false_eq_true, ite_false, calls, bind_assoc, pure_bind] at occurs
          exact RawCtxPendingQueryTails.send_occurs (sendRest sender decode state outside)
            (Tail sender decode)
            (fun result innerQuery innerNext innerOccurs innerSelected =>
              ih result.2 {state with kernel := result.1} innerQuery innerNext innerOccurs innerSelected)
            (fun pending => Tail.send state outside pending)
            (RawCtxChainSend.normalBegin state.kernel ⟨plaintext, state.expectedSender, sender, state.associatedData⟩)
            query next occurs selected
      · simp only [compiler, RawCtxChainOwner.ownerImpl, RawCtxChainOwner.rawReceive, StateT.run] at occurs
        by_cases empty : raw.isEmpty = true
        · simp only [empty, ite_true, pure_bind] at occurs
          exact ih .None (RawCtxChainOwner.publish state (state.kernel, .None)).2 query next occurs selected
        · simp only [empty, Bool.false_eq_true, ite_false] at occurs
          cases decoded : decode raw with
          | none =>
              simp only [decoded, pure_bind] at occurs
              exact ih .None (RawCtxChainOwner.publish state (state.kernel, .None)).2 query next occurs selected
          | some frame =>
              simp only [decoded] at occurs
              by_cases valid : RawCtxReceive.ValidFrame state.expectedSender state.associatedData frame
              · simp only [valid, ite_true, calls, bind_assoc, pure_bind] at occurs
                exact RawCtxPendingQueryTails.receive_occurs (receiveRest sender decode state outside)
                  (Tail sender decode)
                  (fun result innerQuery innerNext innerOccurs innerSelected =>
                    ih (RawCtxChainOwner.publish state result).1 (RawCtxChainOwner.publish state result).2
                      innerQuery innerNext innerOccurs innerSelected)
                  (fun pending => Tail.receive state outside pending)
                  (RawCtxChainReceive.normalBegin state.kernel frame.sequence ⟨raw, frame, state.associatedData⟩)
                  query next occurs selected
              · simp only [valid, ite_false, pure_bind] at occurs
                exact ih .None (RawCtxChainOwner.publish state (state.kernel, .None)).2 query next occurs selected
      · simp only [compiler, StateT.run, publicForward, bind_assoc, pure_bind] at occurs
        rcases query_cases query (.inr (.inr externalRequest)) next
          (fun reply => program sender decode (outside reply) state) occurs with same | ⟨reply, later⟩
        · have sameQuery := congrArg Sigma.fst same
          change query = .inr (.inr externalRequest) at sameQuery
          rw [sameQuery] at selected
          cases selected
        · exact ih reply state query next later selected

/-- Every supported original mixed KDF cut derives its exact concrete source tail, with no supplied retagging or callback-origin premise. -/
theorem reached_tail {Chain Metadata Result State : Type}
    (sender : Std.U64) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp SourceSpec Result) (owner : Owner Chain Metadata)
    (impl : QueryImpl (Spec Chain) (StateT State ProbComp)) (index : Nat) (state reached : State)
    (query : (Spec Chain).Domain)
    (next : (Spec Chain).Range query → OracleComp (Spec Chain) (Result × Owner Chain Metadata))
    (supported : (RawCtxPendingMixedPrefix.Stopped.pending query next, reached) ∈
      support (RawCtxPendingMixedPrefix.scan RawCtxPendingMixedPrefix.ownerSelected impl
        (program sender decode client owner) index state)) : Tail sender decode query next := by
  exact program_tail sender decode client owner query next
    (RawCtxQueryOccurrence.scan_occurs _ impl _ index state reached query next supported)
    (RawCtxPendingMixedPrefix.pending_selected _ impl _ index state reached query next supported)

end BeaconcryptCore.Computational.RawCtxPendingOwnerTails

/-- info: 'BeaconcryptCore.Computational.RawCtxPendingOwnerTails.program_query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxPendingOwnerTails.program_query

/-- info: 'BeaconcryptCore.Computational.RawCtxPendingOwnerTails.receive_requested' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxPendingOwnerTails.receive_requested

/-- info: 'BeaconcryptCore.Computational.RawCtxPendingOwnerTails.receive_opening' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxPendingOwnerTails.receive_opening

/-- info: 'BeaconcryptCore.Computational.RawCtxPendingOwnerTails.receive_rejected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxPendingOwnerTails.receive_rejected

/-- info: 'BeaconcryptCore.Computational.RawCtxPendingOwnerTails.send_requested' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxPendingOwnerTails.send_requested

/-- info: 'BeaconcryptCore.Computational.RawCtxPendingOwnerTails.program_tail' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxPendingOwnerTails.program_tail

/-- info: 'BeaconcryptCore.Computational.RawCtxPendingOwnerTails.reached_tail' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxPendingOwnerTails.reached_tail
