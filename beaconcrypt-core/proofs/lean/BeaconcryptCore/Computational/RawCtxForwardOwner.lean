import BeaconcryptCore.Computational.RawCtxForwardCoverage

/-!
The owner interpreter constructs each saved receive/send descriptor directly before issuing its original private query. Original source outside clients are retained as data, while their already compiled continuations run after the exact pending completion and publication. Erasure and descriptor soundness are operational source correspondence laws; no function equality is inverted and no source-context witness is chosen.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.refined ratchet.concrete
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RawCtxForwardOwner
open RawCtxSelectedFamilyContext RawCtxForwardAnnotation

abbrev Base := RawCtxPendingOwnerQueries.Spec RatchetChain
abbrev Spec (Metadata Result : Type) := RawCtxForwardAnnotation.Spec (OwnerContext Metadata Result) Base
abbrev Owner (Metadata : Type) := RawCtxPendingOwnerTails.Owner RatchetChain Metadata
abbrev SourceSpec := RawCtxSelectedPublicTrace.SourceSpec

noncomputable def receive {Metadata Result : Type}
    (before : Owner Metadata)
    (outside : core.option.Option RawCtxWholeOwner.Decrypted → OracleComp SourceSpec Result)
    (after : (RawCtxPendingOwnerQueries.Kernel RatchetChain × core.option.Option RawCtxWholeOwner.Decrypted) →
      OracleComp (Spec Metadata Result) (Result × Owner Metadata))
    (effect : RawCtxChainReceive.Effect RatchetChain RatchetChain RatchetMaterial RawCtxWholeOwner.OpenContext) :
    OracleComp (Spec Metadata Result) (Result × Owner Metadata) :=
  match effect with
  | .rejected entry _ => after (entry, .None)
  | .openRequested pending => do
      let reply ← (Spec Metadata Result).query (none, .inl (.inr pending))
      after (RawCtxChainReceive.normalFinish pending reply)
  | .kdfRequested pending => do
      let reply ← (Spec Metadata Result).query (some (.receive before outside pending), .inl (.inl pending))
      receive before outside after (RawCtxChainReceive.normalResume pending reply)
termination_by RawCtxChainReceive.effectRank effect
decreasing_by exact RawCtxChainReceive.normalResume_rank _ _

noncomputable def send {Metadata Result : Type}
    (before : Owner Metadata)
    (outside : Option RawCtxSourceSend.Encrypted → OracleComp SourceSpec Result)
    (after : (RawCtxPendingOwnerQueries.Kernel RatchetChain × Option RawCtxSourceSend.Encrypted) →
      OracleComp (Spec Metadata Result) (Result × Owner Metadata))
    (start : RawCtxChainSend.Start RatchetChain RatchetChain RatchetMaterial RawCtxSourceSend.SealContext) :
    OracleComp (Spec Metadata Result) (Result × Owner Metadata) :=
  match start with
  | .exhausted entry _ => after (entry, none)
  | .requested pending => do
      let reply ← (Spec Metadata Result).query (some (.send before outside pending), .inr (.inl (.inl pending)))
      let ready := RawCtxChainSend.ready pending reply
      let sealed ← (Spec Metadata Result).query (none, .inr (.inl (.inr ready)))
      after (ready.advanced, sealed)

noncomputable def program {Metadata Result : Type}
    (sender : Std.U64) (decode : RawCtxReceive.FrameDecoder) (client : OracleComp SourceSpec Result) :
    Owner Metadata → OracleComp (Spec Metadata Result) (Result × Owner Metadata) :=
  OracleComp.recOn client
    (fun result state => pure (result, state))
    (fun query outside recurse state => match query with
      | .inl (.inl plaintext) =>
          if plaintext.isEmpty then recurse none state
          else send state outside (fun result => recurse result.2 {state with kernel := result.1})
            (RawCtxChainSend.normalBegin state.kernel ⟨plaintext, state.expectedSender, sender, state.associatedData⟩)
      | .inl (.inr raw) =>
          let after := fun result =>
            let published := RawCtxChainOwner.publish state result
            recurse published.1 published.2
          if raw.isEmpty then after (state.kernel, .None)
          else match decode raw with
          | none => after (state.kernel, .None)
          | some decoded =>
              if RawCtxReceive.ValidFrame state.expectedSender state.associatedData decoded then
                receive state outside after
                  (RawCtxChainReceive.normalBegin state.kernel decoded.sequence ⟨raw, decoded, state.associatedData⟩)
              else after (state.kernel, .None)
      | .inr publicQuery => do
          let reply ← (Spec Metadata Result).query (none, .inr (.inr publicQuery))
          recurse reply state)

/-- Erasure keeps the complete original receive effect and the entire already compiled source continuation. -/
theorem receive_erase {Metadata Result : Type}
    (before : Owner Metadata)
    (outside : core.option.Option RawCtxWholeOwner.Decrypted → OracleComp SourceSpec Result)
    (after : (RawCtxPendingOwnerQueries.Kernel RatchetChain × core.option.Option RawCtxWholeOwner.Decrypted) →
      OracleComp (Spec Metadata Result) (Result × Owner Metadata))
    (effect : RawCtxChainReceive.Effect RatchetChain RatchetChain RatchetMaterial RawCtxWholeOwner.OpenContext) :
    simulateQ erase (receive before outside after effect) =
      (simulateQ RawCtxPendingOwnerQueries.receiveForward (RawCtxPendingReceiveQueries.program effect) >>=
        fun result => simulateQ erase (after result)) := by
  generalize depth : RawCtxChainReceive.effectRank effect = count
  induction count using Nat.strong_induction_on generalizing effect with
  | h count ih =>
    cases effect with
    | rejected entry context => simp [receive, RawCtxPendingReceiveQueries.program]
    | openRequested pending =>
      simp only [receive, RawCtxPendingReceiveQueries.program, erase, simulateQ_bind,
        simulateQ_spec_query, RawCtxPendingOwnerQueries.receiveForward, simulateQ_pure, bind_assoc, pure_bind]
      rfl
    | kdfRequested pending =>
      simp only [receive, RawCtxPendingReceiveQueries.program, erase, simulateQ_bind,
        simulateQ_spec_query, RawCtxPendingOwnerQueries.receiveForward, bind_assoc]
      exact bind_congr fun reply => ih _ (depth ▸ RawCtxChainReceive.normalResume_rank pending reply) _ rfl

/-- Erasure keeps the actual send request, advanced sealing state and full compiled publication continuation. -/
theorem send_erase {Metadata Result : Type}
    (before : Owner Metadata)
    (outside : Option RawCtxSourceSend.Encrypted → OracleComp SourceSpec Result)
    (after : (RawCtxPendingOwnerQueries.Kernel RatchetChain × Option RawCtxSourceSend.Encrypted) →
      OracleComp (Spec Metadata Result) (Result × Owner Metadata))
    (start : RawCtxChainSend.Start RatchetChain RatchetChain RatchetMaterial RawCtxSourceSend.SealContext) :
    simulateQ erase (send before outside after start) =
      (simulateQ RawCtxPendingOwnerQueries.sendForward (RawCtxPendingOwnerQueries.sendProgram start) >>=
        fun result => simulateQ erase (after result)) := by
  cases start with
  | exhausted entry context => simp [send, RawCtxPendingOwnerQueries.sendProgram]
  | requested pending =>
    simp only [send, RawCtxPendingOwnerQueries.sendProgram, simulateQ_bind, simulateQ_spec_query,
      erase, RawCtxPendingOwnerQueries.sendForward, simulateQ_pure, bind_assoc, pure_bind]
    rfl

/-- Every forward receive descriptor names its exact source query and whole remaining continuation, before the primitive reply exists. -/
theorem receive_sound {Metadata Result : Type}
    (sender : Std.U64) (decode : RawCtxReceive.FrameDecoder) (before : Owner Metadata)
    (outside : core.option.Option RawCtxWholeOwner.Decrypted → OracleComp SourceSpec Result)
    (after : (RawCtxPendingOwnerQueries.Kernel RatchetChain × core.option.Option RawCtxWholeOwner.Decrypted) →
      OracleComp (Spec Metadata Result) (Result × Owner Metadata))
    (after_erase : ∀ result, simulateQ erase (after result) = RawCtxPendingOwnerTails.receiveRest sender decode before outside result)
    (after_sound : ∀ result, Sound (ownerFrame sender decode) (after result))
    (effect : RawCtxChainReceive.Effect RatchetChain RatchetChain RatchetMaterial RawCtxWholeOwner.OpenContext) :
    Sound (ownerFrame sender decode) (receive before outside after effect) := by
  generalize depth : RawCtxChainReceive.effectRank effect = count
  induction count using Nat.strong_induction_on generalizing effect with
  | h count ih =>
    cases effect with
    | rejected entry context => simpa only [receive] using after_sound (entry, .None)
    | openRequested pending =>
      rw [receive, sound_query]
      constructor
      · intro tag impossible
        cases impossible
      · intro reply
        exact after_sound _
    | kdfRequested pending =>
      rw [receive, sound_query]
      constructor
      · intro tag same
        cases same
        simp only [ownerFrame]
        apply congrArg (fun next : RatchetChain × RatchetMaterial → OracleComp Base (Result × Owner Metadata) =>
          (⟨.inl (.inl pending), next⟩ : RawCtxForwardAnnotation.Frame Base (Result × Owner Metadata)))
        funext reply
        rw [receive_erase]
        exact bind_congr after_erase
      · intro reply
        exact ih _ (depth ▸ RawCtxChainReceive.normalResume_rank pending reply) _ rfl

/-- One actual source request constructs its descriptor before the complete original source continuation resumes. -/
theorem program_query {Metadata Result : Type}
    (sender : Std.U64) (decode : RawCtxReceive.FrameDecoder) (request : SourceSpec.Domain)
    (outside : SourceSpec.Range request → OracleComp SourceSpec Result) (state : Owner Metadata) :
    program sender decode ((SourceSpec.query request : OracleComp SourceSpec _) >>= outside) state =
      (match request, outside with
      | .inl (.inl plaintext), outside =>
          if plaintext.isEmpty then program sender decode (outside none) state
          else send state outside (fun result => program sender decode (outside result.2) {state with kernel := result.1})
            (RawCtxChainSend.normalBegin state.kernel ⟨plaintext, state.expectedSender, sender, state.associatedData⟩)
      | .inl (.inr raw), outside =>
          let after := fun result =>
            let published := RawCtxChainOwner.publish state result
            program sender decode (outside published.1) published.2
          if raw.isEmpty then after (state.kernel, .None)
          else match decode raw with
          | none => after (state.kernel, .None)
          | some decoded =>
              if RawCtxReceive.ValidFrame state.expectedSender state.associatedData decoded then
                receive state outside after
                  (RawCtxChainReceive.normalBegin state.kernel decoded.sequence ⟨raw, decoded, state.associatedData⟩)
              else after (state.kernel, .None)
      | .inr publicQuery, outside => do
          let reply ← (Spec Metadata Result).query (none, .inr (.inr publicQuery))
          program sender decode (outside reply) state) := by
  rcases request with (plaintext | raw) | publicQuery
  all_goals rfl

set_option backward.isDefEq.respectTransparency false in
/-- The actual whole owner source interpreter erases to the original pending program, preserving every gate, publication and adaptive source continuation. -/
theorem program_erase {Metadata Result : Type}
    (sender : Std.U64) (decode : RawCtxReceive.FrameDecoder) (client : OracleComp SourceSpec Result) (state : Owner Metadata) :
    simulateQ erase (program sender decode client state) = RawCtxPendingOwnerTails.program sender decode client state := by
  induction client using OracleComp.inductionOn generalizing state with
  | pure value => rfl
  | query_bind query outside ih =>
    rw [program_query, RawCtxPendingOwnerTails.program_query]
    rcases query with (plaintext | raw) | publicQuery
    · simp only [RawCtxPendingOwnerQueries.compiler, RawCtxChainOwner.ownerImpl,
        RawCtxChainOwner.sendOwner, StateT.run]
      split
      · simp only [pure_bind]
        exact ih none state
      · simp only [RawCtxPendingOwnerQueries.calls, bind_assoc, pure_bind]
        rw [send_erase]
        exact bind_congr fun result => ih result.2 {state with kernel := result.1}
    · simp only [RawCtxPendingOwnerQueries.compiler, RawCtxChainOwner.ownerImpl,
        RawCtxChainOwner.rawReceive, StateT.run]
      by_cases empty : raw.isEmpty = true
      · simp only [empty, ite_true, pure_bind]
        exact ih .None _
      · simp only [empty, Bool.false_eq_true, ite_false]
        cases decoded : decode raw with
        | none =>
          simp only [pure_bind]
          exact ih .None _
        | some frame =>
          by_cases valid : RawCtxReceive.ValidFrame state.expectedSender state.associatedData frame
          · simp only [valid, ite_true, RawCtxPendingOwnerQueries.calls, bind_assoc, pure_bind]
            rw [receive_erase]
            exact bind_congr fun result => ih (RawCtxChainOwner.publish state result).1 (RawCtxChainOwner.publish state result).2
          · simp only [valid, ite_false, pure_bind]
            exact ih .None _
    · simp only [RawCtxPendingOwnerQueries.compiler, StateT.run, simulateQ_bind,
        simulateQ_spec_query, erase, RawCtxPendingOwnerQueries.publicForward, bind_assoc, pure_bind]
      exact bind_congr fun reply => ih reply state

/-- A forward send descriptor contains the exact actual sealing continuation and the original source publication. -/
theorem send_sound {Metadata Result : Type}
    (sender : Std.U64) (decode : RawCtxReceive.FrameDecoder) (before : Owner Metadata)
    (outside : Option RawCtxSourceSend.Encrypted → OracleComp SourceSpec Result)
    (after : (RawCtxPendingOwnerQueries.Kernel RatchetChain × Option RawCtxSourceSend.Encrypted) →
      OracleComp (Spec Metadata Result) (Result × Owner Metadata))
    (after_erase : ∀ result, simulateQ erase (after result) = RawCtxPendingOwnerTails.sendRest sender decode before outside result)
    (after_sound : ∀ result, Sound (ownerFrame sender decode) (after result))
    (start : RawCtxChainSend.Start RatchetChain RatchetChain RatchetMaterial RawCtxSourceSend.SealContext) :
    Sound (ownerFrame sender decode) (send before outside after start) := by
  cases start with
  | exhausted entry context => exact after_sound _
  | requested pending =>
    rw [send, sound_query]
    constructor
    · intro tag same
      cases same
      simp only [ownerFrame]
      apply congrArg (fun next : RatchetChain × RatchetMaterial → OracleComp Base (Result × Owner Metadata) =>
        (⟨.inr (.inl (.inl pending)), next⟩ : RawCtxForwardAnnotation.Frame Base (Result × Owner Metadata)))
      funext reply
      simp only [simulateQ_bind, simulateQ_spec_query, erase, RawCtxPendingOwnerTails.sendTail]
      exact bind_congr fun sealed => after_erase _
    · intro reply
      rw [sound_query]
      constructor
      · intro tag impossible
        cases impossible
      · intro sealed
        exact after_sound _

/-- Every receive private query carries a descriptor, and every nonprivate opening carries none, throughout the complete continuation. -/
theorem receive_covered {Metadata Result : Type}
    (before : Owner Metadata)
    (outside : core.option.Option RawCtxWholeOwner.Decrypted → OracleComp SourceSpec Result)
    (after : (RawCtxPendingOwnerQueries.Kernel RatchetChain × core.option.Option RawCtxWholeOwner.Decrypted) →
      OracleComp (Spec Metadata Result) (Result × Owner Metadata))
    (after_covered : ∀ result, RawCtxForwardCoverage.Covered RawCtxPendingMixedPrefix.ownerSelected (after result))
    (effect : RawCtxChainReceive.Effect RatchetChain RatchetChain RatchetMaterial RawCtxWholeOwner.OpenContext) :
    RawCtxForwardCoverage.Covered RawCtxPendingMixedPrefix.ownerSelected (receive before outside after effect) := by
  generalize depth : RawCtxChainReceive.effectRank effect = count
  induction count using Nat.strong_induction_on generalizing effect with
  | h count ih =>
    cases effect with
    | rejected entry context => simpa only [receive] using after_covered (entry, .None)
    | openRequested pending =>
      rw [receive, RawCtxForwardCoverage.covered_query]
      exact ⟨rfl, fun reply => after_covered _⟩
    | kdfRequested pending =>
      rw [receive, RawCtxForwardCoverage.covered_query]
      exact ⟨rfl, fun reply => ih _ (depth ▸ RawCtxChainReceive.normalResume_rank pending reply) _ rfl⟩

/-- Every send derivation carries its descriptor before the reply; its subsequent sealing query and publication retain exact coverage. -/
theorem send_covered {Metadata Result : Type}
    (before : Owner Metadata)
    (outside : Option RawCtxSourceSend.Encrypted → OracleComp SourceSpec Result)
    (after : (RawCtxPendingOwnerQueries.Kernel RatchetChain × Option RawCtxSourceSend.Encrypted) →
      OracleComp (Spec Metadata Result) (Result × Owner Metadata))
    (after_covered : ∀ result, RawCtxForwardCoverage.Covered RawCtxPendingMixedPrefix.ownerSelected (after result))
    (start : RawCtxChainSend.Start RatchetChain RatchetChain RatchetMaterial RawCtxSourceSend.SealContext) :
    RawCtxForwardCoverage.Covered RawCtxPendingMixedPrefix.ownerSelected (send before outside after start) := by
  cases start with
  | exhausted entry context => exact after_covered _
  | requested pending =>
    rw [send, RawCtxForwardCoverage.covered_query]
    refine ⟨rfl, ?_⟩
    intro reply
    rw [RawCtxForwardCoverage.covered_query]
    exact ⟨rfl, fun sealed => after_covered _⟩

/-- The complete source owner constructs only exact descriptors. Each one retains its original source outside client and the full source continuation after the actual pending reply. -/
theorem program_sound {Metadata Result : Type}
    (sender : Std.U64) (decode : RawCtxReceive.FrameDecoder) (client : OracleComp SourceSpec Result) (state : Owner Metadata) :
    Sound (ownerFrame sender decode) (program sender decode client state) := by
  induction client using OracleComp.inductionOn generalizing state with
  | pure value => exact sound_pure _ _
  | query_bind query outside ih =>
    rw [program_query]
    rcases query with (plaintext | raw) | publicQuery
    all_goals dsimp only
    · split
      · exact ih none state
      · apply send_sound sender decode
        · intro result
          exact program_erase sender decode (outside result.2) {state with kernel := result.1}
        · intro result
          exact ih result.2 {state with kernel := result.1}
    · by_cases empty : raw.isEmpty = true
      · simp only [empty, ite_true]
        exact ih .None _
      · simp only [empty, Bool.false_eq_true, ite_false]
        cases decoded : decode raw with
        | none => exact ih .None _
        | some frame =>
          by_cases valid : RawCtxReceive.ValidFrame state.expectedSender state.associatedData frame
          · simp only [valid, ite_true]
            apply receive_sound sender decode
            · intro result
              exact program_erase sender decode (outside (RawCtxChainOwner.publish state result).1)
                (RawCtxChainOwner.publish state result).2
            · intro result
              exact ih (RawCtxChainOwner.publish state result).1 (RawCtxChainOwner.publish state result).2
          · simp only [valid, ite_false]
            exact ih .None _
    · rw [sound_query]
      constructor
      · intro tag impossible
        cases impossible
      · intro reply
        exact ih reply state

/-- Every selected private call in the actual full owner source carries its descriptor; all other callbacks carry none, for every adaptive reply. -/
theorem program_covered {Metadata Result : Type}
    (sender : Std.U64) (decode : RawCtxReceive.FrameDecoder) (client : OracleComp SourceSpec Result) (state : Owner Metadata) :
    RawCtxForwardCoverage.Covered RawCtxPendingMixedPrefix.ownerSelected (program sender decode client state) := by
  induction client using OracleComp.inductionOn generalizing state with
  | pure value => exact RawCtxForwardCoverage.covered_pure _ _
  | query_bind query outside ih =>
    rw [program_query]
    rcases query with (plaintext | raw) | publicQuery
    all_goals dsimp only
    · split
      · exact ih none state
      · apply send_covered
        intro result
        exact ih result.2 {state with kernel := result.1}
    · by_cases empty : raw.isEmpty = true
      · simp only [empty, ite_true]
        exact ih .None _
      · simp only [empty, Bool.false_eq_true, ite_false]
        cases decoded : decode raw with
        | none => exact ih .None _
        | some frame =>
          by_cases valid : RawCtxReceive.ValidFrame state.expectedSender state.associatedData frame
          · simp only [valid, ite_true]
            apply receive_covered
            intro result
            exact ih (RawCtxChainOwner.publish state result).1 (RawCtxChainOwner.publish state result).2
          · simp only [valid, ite_false]
            exact ih .None _
    · rw [RawCtxForwardCoverage.covered_query]
      exact ⟨rfl, fun reply => ih reply state⟩

end BeaconcryptCore.Computational.RawCtxForwardOwner

/-- info: 'BeaconcryptCore.Computational.RawCtxForwardOwner.receive_erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxForwardOwner.receive_erase
/-- info: 'BeaconcryptCore.Computational.RawCtxForwardOwner.send_erase' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxForwardOwner.send_erase
/-- info: 'BeaconcryptCore.Computational.RawCtxForwardOwner.receive_sound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxForwardOwner.receive_sound
/-- info: 'BeaconcryptCore.Computational.RawCtxForwardOwner.program_query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxForwardOwner.program_query
/-- info: 'BeaconcryptCore.Computational.RawCtxForwardOwner.program_erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxForwardOwner.program_erase
/-- info: 'BeaconcryptCore.Computational.RawCtxForwardOwner.send_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxForwardOwner.send_sound
/-- info: 'BeaconcryptCore.Computational.RawCtxForwardOwner.receive_covered' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxForwardOwner.receive_covered
/-- info: 'BeaconcryptCore.Computational.RawCtxForwardOwner.send_covered' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxForwardOwner.send_covered
/-- info: 'BeaconcryptCore.Computational.RawCtxForwardOwner.program_sound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxForwardOwner.program_sound
/-- info: 'BeaconcryptCore.Computational.RawCtxForwardOwner.program_covered' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxForwardOwner.program_covered
