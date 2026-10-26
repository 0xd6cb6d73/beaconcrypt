import BeaconcryptCore.Computational.RawCtxSourceOpen

/-!
Every reached opening must use the original decoded sequence and immutable raw/frame/AD context before its reply is known. The source begin/resume scope and universal rank decrease establish a zero bound for out-of-scope opening requests, across all typed KDF replies and both optional opening outcomes. Present material is obtained only through the actual source getter; missing material remains a no-opening rejection. No success event, key distribution, fixed response, freshness or authentication assumption enters this occurrence argument.

The congruence statements replace local handlers whose actual computations are equal on source-scoped inputs. These are explicit operational proof obligations to discharge with the component interface equality; they are not new primitive security contracts or assumed protocol conclusions. Arbitrary lawful target monads include the complete stateful cryptographic interpreter. The raw and adaptive-schedule equalities preserve actual optional plaintext, parser/validation rejection, failed opening effects, source finish, complete owner publication and complete primitive state. They do not reveal the API plaintext to the network adversary.

This module does not instantiate the canonical handler, prove a primitive algorithm, alter the source protocol, introduce independent keys, or claim multi-session secrecy/authentication. Native decoder/library/runtime contracts, per-key component selection, correlated evolving keys, interleaved send/reveal actions, freshness, query costs and global reduction losses remain their existing separate obligations. The structural replacements add no approximation loss and preserve existing query-accounted source schedules; any cryptographic change inside the local handlers must still supply its own proved game relation and ledger.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
open OracleComp

set_option autoImplicit false

universe u

namespace BeaconcryptCore.Computational.RawCtxOpeningOccurrence

open RawCtxOwnerOracle RawCtxOwnerProvenance

/-- An opening request outside its actual decoded target/context; KDF requests are not opening occurrences. -/
def Outside {Context Plaintext : Type} (target : Std.U64) (context : Context) :
    (ReceiveSpec Context Plaintext).Domain → Prop
  | .inl _ => False
  | .inr pending => ¬(pending.sequence = ok target ∧ pending.context = context)

attribute [local instance] Classical.propDecidable

/-- All possible typed callback replies preserve the original opening scope, including optional failure. -/
theorem program_scoped {Context Plaintext : Type} (target : Std.U64) (context : Context)
    (effect : ReceiveEffect Context) (hscope : Scope target context effect) :
    (program (Plaintext := Plaintext) effect).IsQueryBoundP (Outside (Plaintext := Plaintext) target context) 0 := by
  classical
  generalize hdepth : effectDepth effect = depth
  induction depth using Nat.strong_induction_on generalizing effect with
  | h depth ih =>
      cases effect with
      | ReceiveRejected => simp [program]
      | ReceiveOpenRequested pending =>
          rw [program, isQueryBoundP_query_bind_iff]
          refine ⟨Or.inl (fun hbad => hbad hscope), ?_⟩
          simp only [isQueryBoundP_pure, implies_true]
      | ReceiveKdfRequested pending =>
          rw [program, isQueryBoundP_query_bind_iff]
          refine ⟨Or.inl ?_, ?_⟩
          · simp only [Outside, not_false_eq_true]
          · intro response
            rw [ite_eq_right (by simp only [Outside, not_false_eq_true])]
            apply ih _ (hdepth ▸ resume_rank pending response) _ _ rfl
            simpa only [hscope.1, hscope.2] using oracle_resume_scope pending response

/-- Actual source admission invokes no out-of-scope opening, regardless of every optional reply. -/
theorem receive_scoped {Context Plaintext : Type} (entry : ConcreteRatchetKernel)
    (target : Std.U64) (context : Context) :
    (receive (Plaintext := Plaintext) entry target context).IsQueryBoundP
      (Outside (Plaintext := Plaintext) target context) 0 :=
  program_scoped target context _ (oracle_begin_scope entry target context)

/-- Equal scoped callback implementations give equal entire source computations, including failed replies. -/
theorem program_congr {Context Plaintext : Type} {m : Type → Type u} [Monad m] [LawfulMonad m]
    (left right : QueryImpl (ReceiveSpec Context Plaintext) m)
    (target : Std.U64) (context : Context)
    (hkdf : ∀ request, left (.inl request) = right (.inl request))
    (hopen : ∀ pending, pending.sequence = ok target → pending.context = context →
      left (.inr pending) = right (.inr pending))
    (effect : ReceiveEffect Context) (hscope : Scope target context effect) :
    simulateQ left (program effect) = simulateQ right (program effect) := by
  generalize hdepth : effectDepth effect = depth
  induction depth using Nat.strong_induction_on generalizing effect with
  | h depth ih =>
      cases effect with
      | ReceiveRejected => simp [program]
      | ReceiveOpenRequested pending =>
          simp only [program, simulateQ_bind, simulateQ_spec_query, simulateQ_pure]
          rw [hopen pending hscope.1 hscope.2]
      | ReceiveKdfRequested pending =>
          simp only [program, simulateQ_bind, simulateQ_spec_query]
          rw [hkdf pending.request]
          apply bind_congr
          intro response
          apply ih _ (hdepth ▸ resume_rank pending response) _ _ rfl
          simpa only [hscope.1, hscope.2] using oracle_resume_scope pending response

/-- A present source material is passed with the original sequence/context before its opening result exists. -/
theorem arguments_scoped (pending : ReceiveOpen RawCtxWholeOwner.OpenContext)
    (input : RawCtxWholeOwner.OpenInput) (target : Std.U64) (context : RawCtxWholeOwner.OpenContext)
    (hargs : RawCtxWholeOwner.arguments pending = some input)
    (hsequence : pending.sequence = ok target) (hcontext : pending.context = context) :
    pending.material = ok (.Some input.material) ∧ input.sequence = target ∧ input.context = context := by
  obtain ⟨hmaterial, hinputSequence, hinputContext⟩ := RawCtxWholeOwner.arguments_some pending input hargs
  exact ⟨hmaterial, RustM.ok.inj (hinputSequence.symm.trans hsequence), hinputContext.trans hcontext⟩

/-- Selected opening equality lifts through the actual missing-material branch and optional-result construction. -/
theorem adapter_congr {m : Type → Type u} [Monad m] [LawfulMonad m]
    (left right : QueryImpl RawCtxWholeOwner.PrimitiveSpec m)
    (target : Std.U64) (context : RawCtxWholeOwner.OpenContext)
    (hopen : ∀ input, input.sequence = target → input.context = context →
      left (.inr input) = right (.inr input))
    (pending : ReceiveOpen RawCtxWholeOwner.OpenContext)
    (hsequence : pending.sequence = ok target) (hcontext : pending.context = context) :
    (left ∘ₛ RawCtxWholeOwner.adapter) (.inr pending) =
      (right ∘ₛ RawCtxWholeOwner.adapter) (.inr pending) := by
  simp only [QueryImpl.compose, RawCtxWholeOwner.adapter]
  cases hargs : RawCtxWholeOwner.arguments pending
  · simp only [simulateQ_pure]
  · rename_i input
    obtain ⟨_, hinputSequence, hinputContext⟩ := arguments_scoped pending input target context hargs hsequence hcontext
    simp only [simulateQ_bind, simulateQ_spec_query, simulateQ_pure, hopen input hinputSequence hinputContext]

/-- All selected opening handlers can be replaced before observing any reply, preserving the whole receive. -/
theorem receive_selected_congr {m : Type → Type u} [Monad m] [LawfulMonad m]
    (left right : QueryImpl RawCtxWholeOwner.PrimitiveSpec m)
    (entry : ConcreteRatchetKernel) (target : Std.U64) (context : RawCtxWholeOwner.OpenContext)
    (hkdf : ∀ request, left (.inl request) = right (.inl request))
    (hopen : ∀ input, input.sequence = target → input.context = context →
      left (.inr input) = right (.inr input)) :
    simulateQ left (simulateQ RawCtxWholeOwner.adapter (receive entry target context)) =
      simulateQ right (simulateQ RawCtxWholeOwner.adapter (receive entry target context)) := by
  rw [← QueryImpl.simulateQ_compose, ← QueryImpl.simulateQ_compose]
  apply program_congr _ _ target context _ _ _ (oracle_begin_scope entry target context)
  · intro request
    simpa [QueryImpl.compose, RawCtxWholeOwner.adapter, OracleSpec.query] using hkdf request
  · exact adapter_congr left right target context hopen

/-- Raw replacement requires only actual validated source opening arguments, and preserves every rejection. -/
theorem raw_congr {Metadata : Type} {m : Type → Type u} [Monad m] [LawfulMonad m]
    (left right : QueryImpl RawCtxWholeOwner.PrimitiveSpec m)
    (decode : RawCtxReceive.FrameDecoder) (raw : Pqxdh.Bytes)
    (state : RawCtxWholeOwner.OwnerState Metadata)
    (hkdf : ∀ request, left (.inl request) = right (.inl request))
    (hopen : ∀ frame input,
      raw.isEmpty = false → decode raw = some frame →
      RawCtxReceive.ValidFrame state.owner.expectedSender state.owner.associatedData frame →
      input.sequence = frame.sequence →
      input.context = ⟨raw, frame, state.owner.associatedData⟩ →
      left (.inr input) = right (.inr input)) :
    simulateQ left ((RawCtxWholeOwner.rawReceive decode raw).run state) =
      simulateQ right ((RawCtxWholeOwner.rawReceive decode raw).run state) := by
  unfold RawCtxWholeOwner.rawReceive StateT.run
  split
  · simp only [simulateQ_pure]
  · rename_i hraw
    cases hdecode : decode raw
    · simp only [simulateQ_pure]
    · rename_i frame
      dsimp only
      split
      · rename_i hvalid
        simp only [bind_pure_comp, simulateQ_map]
        congr 1
        apply receive_selected_congr left right _ _ _ hkdf
        exact fun input => hopen frame input (by simpa using hraw) hdecode hvalid
      · simp only [simulateQ_pure]

/-- Scoped source replacement preserves actual optional output, complete owner and complete primitive state. -/
theorem rawGame_congr {Metadata PrimitiveState : Type} {ι : Type} {base : OracleSpec ι}
    (left right : QueryImpl RawCtxWholeOwner.PrimitiveSpec
      (StateT PrimitiveState (OracleComp base)))
    (decode : RawCtxReceive.FrameDecoder) (raw : Pqxdh.Bytes)
    (state : RawCtxWholeOwner.OwnerState Metadata) (primitive : PrimitiveState)
    (hkdf : ∀ request, left (.inl request) = right (.inl request))
    (hopen : ∀ frame input,
      raw.isEmpty = false → decode raw = some frame →
      RawCtxReceive.ValidFrame state.owner.expectedSender state.owner.associatedData frame →
      input.sequence = frame.sequence →
      input.context = ⟨raw, frame, state.owner.associatedData⟩ →
      left (.inr input) = right (.inr input)) :
    RawCtxWholeOwner.rawGame left decode raw state primitive =
      RawCtxWholeOwner.rawGame right decode raw state primitive := by
  exact congrArg (fun computation : StateT PrimitiveState (OracleComp base)
      (Option RawCtxWholeOwner.Decrypted × RawCtxWholeOwner.OwnerState Metadata) => computation.run primitive)
    (raw_congr left right decode raw state hkdf hopen)

/-- Scoped callback equality preserves the serialized whole-owner transition for every raw request. -/
theorem owner_congr {Metadata PrimitiveState : Type} {ι : Type} {base : OracleSpec ι}
    (left right : QueryImpl RawCtxWholeOwner.PrimitiveSpec
      (StateT PrimitiveState (OracleComp base)))
    (decode : RawCtxReceive.FrameDecoder)
    (hkdf : ∀ request, left (.inl request) = right (.inl request))
    (hopen : ∀ (state : RawCtxWholeOwner.OwnerState Metadata) raw frame input,
      raw.isEmpty = false → decode raw = some frame →
      RawCtxReceive.ValidFrame state.owner.expectedSender state.owner.associatedData frame →
      input.sequence = frame.sequence →
      input.context = ⟨raw, frame, state.owner.associatedData⟩ →
      left (.inr input) = right (.inr input)) :
    RawCtxWholeOwner.ownerImpl (Metadata := Metadata) left decode =
      RawCtxWholeOwner.ownerImpl right decode := by
  funext raw state
  simp only [RawCtxWholeOwner.ownerImpl, rawGame_congr left right decode raw state.1 state.2 hkdf (hopen state.1 raw)]

/-- Every adaptive raw schedule retains actual replies and both full states under proved local replacement. -/
theorem rawSchedule_congr {Metadata PrimitiveState Result : Type} {ι : Type} {base : OracleSpec ι}
    (left right : QueryImpl RawCtxWholeOwner.PrimitiveSpec
      (StateT PrimitiveState (OracleComp base)))
    (decode : RawCtxReceive.FrameDecoder)
    (hkdf : ∀ request, left (.inl request) = right (.inl request))
    (hopen : ∀ (state : RawCtxWholeOwner.OwnerState Metadata) raw frame input,
      raw.isEmpty = false → decode raw = some frame →
      RawCtxReceive.ValidFrame state.owner.expectedSender state.owner.associatedData frame →
      input.sequence = frame.sequence →
      input.context = ⟨raw, frame, state.owner.associatedData⟩ →
      left (.inr input) = right (.inr input))
    (client : OracleComp RawCtxWholeOwner.RawSpec Result)
    (state : RawCtxWholeOwner.OwnerState Metadata × PrimitiveState) :
    RawCtxWholeOwner.scheduleGame left decode client state =
      RawCtxWholeOwner.scheduleGame right decode client state := by
  simp only [RawCtxWholeOwner.scheduleGame, owner_congr left right decode hkdf hopen]

end BeaconcryptCore.Computational.RawCtxOpeningOccurrence

/--
info: 'BeaconcryptCore.Computational.RawCtxOpeningOccurrence.program_scoped' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxOpeningOccurrence.program_scoped

/--
info: 'BeaconcryptCore.Computational.RawCtxOpeningOccurrence.receive_scoped' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxOpeningOccurrence.receive_scoped

/--
info: 'BeaconcryptCore.Computational.RawCtxOpeningOccurrence.program_congr' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxOpeningOccurrence.program_congr

/--
info: 'BeaconcryptCore.Computational.RawCtxOpeningOccurrence.arguments_scoped' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxOpeningOccurrence.arguments_scoped

/--
info: 'BeaconcryptCore.Computational.RawCtxOpeningOccurrence.adapter_congr' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxOpeningOccurrence.adapter_congr

/--
info: 'BeaconcryptCore.Computational.RawCtxOpeningOccurrence.receive_selected_congr' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxOpeningOccurrence.receive_selected_congr

/--
info: 'BeaconcryptCore.Computational.RawCtxOpeningOccurrence.raw_congr' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxOpeningOccurrence.raw_congr

/--
info: 'BeaconcryptCore.Computational.RawCtxOpeningOccurrence.rawGame_congr' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxOpeningOccurrence.rawGame_congr

/--
info: 'BeaconcryptCore.Computational.RawCtxOpeningOccurrence.owner_congr' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxOpeningOccurrence.owner_congr

/--
info: 'BeaconcryptCore.Computational.RawCtxOpeningOccurrence.rawSchedule_congr' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxOpeningOccurrence.rawSchedule_congr
