-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.RegistrationSigningTrace

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
open BeaconcryptCore.Computational
open BeaconcryptCore.Refinement.RegistrationSigningTrace

set_option autoImplicit false

namespace BeaconcryptCore.Refinement.RegistrationSigningHistory

/-- An interleaving consists of actual extracted dispatches, in their chronological order. -/
inductive Executes {Encoded : Type} (hash : HashOracle) (sign : SignOracle) :
    List (Command × core.option.Option Encoded) → List Observation → List (Publication Encoded) → Prop where
  | nil : Executes hash sign [] [] []
  | cons {command : Command} {encoded : core.option.Option Encoded}
      {result : DispatchResult Encoded} {event : Observation}
      {commands : List (Command × core.option.Option Encoded)}
      {events : List Observation} {outcomes : List (Publication Encoded)}
      (dispatchRun : dispatch hash sign command encoded = ok result)
      (logged : result.event = some event)
      (rest : Executes hash sign commands events outcomes) :
      Executes hash sign ((command, encoded) :: commands) (event :: events) (result.outcome :: outcomes)

/-- The existing ML transcript trial reads exactly the selected key's entire prior source-signing log. -/
def trial (publicKey : Pqxdh.Bytes) (protectedKey : Bool) (events : List Observation)
    (candidate : MldsaTranscriptAuth.Payload) (signature : Pqxdh.Bytes) : MldsaTranscriptAuth.Trial :=
  ⟨publicKey, protectedKey, historyFor publicKey events, candidate, signature⟩

/-- Key selection preserves chronological concatenation across interleaved protocol roles. -/
theorem history_append (publicKey : Pqxdh.Bytes) (before after : List Observation) :
    historyFor publicKey (before ++ after) = historyFor publicKey before ++ historyFor publicKey after := by
  simp [historyFor]

/-- A call under the selected key is logged regardless of role, reply or publication outcome. -/
theorem history_selected_cons (publicKey : Pqxdh.Bytes) (event : Observation) (after : List Observation)
    (selected : absBytes event.publicKey = publicKey) :
    historyFor publicKey (event :: after) = event.call :: historyFor publicKey after := by
  simp [historyFor, selected]

/-- Membership in the old abstract signing log is exactly membership of an actual same-key event. -/
theorem history_mem_iff (publicKey : Pqxdh.Bytes) (events : List Observation)
    (call : MldsaTranscriptAuth.SigningCall) :
    call ∈ historyFor publicKey events ↔
      ∃ event ∈ events, absBytes event.publicKey = publicKey ∧ event.call = call := by
  simp [historyFor, List.mem_filterMap]

/-- Unsigned origin quantifies every prior invocation under the key, across both roles and outcomes. -/
theorem issued_iff_source_event (publicKey : Pqxdh.Bytes) (protectedKey : Bool)
    (events : List Observation) (candidate : MldsaTranscriptAuth.Payload) (signature : Pqxdh.Bytes) :
    MldsaTranscriptAuth.Issued (trial publicKey protectedKey events candidate signature) ↔
      ∃ event ∈ events, absBytes event.publicKey = publicKey ∧ event.payload = candidate := by
  simp [MldsaTranscriptAuth.Issued, trial, history_mem_iff, Observation.call]

/-- Every chronological source dispatch contributes one attempted query, regardless of its outcome. -/
theorem execution_counts {Encoded : Type} {hash : HashOracle} {sign : SignOracle}
    {commands : List (Command × core.option.Option Encoded)} {events : List Observation}
    {outcomes : List (Publication Encoded)} (execution : Executes hash sign commands events outcomes) :
    events.length = commands.length ∧ outcomes.length = commands.length := by
  induction execution <;> simp_all

/-- The selected query retains its exact position relative to all earlier and later same-key calls. -/
theorem history_selected_at_position (publicKey : Pqxdh.Bytes) (before after : List Observation)
    (event : Observation) (selected : absBytes event.publicKey = publicKey) :
    historyFor publicKey (before ++ event :: after) =
      historyFor publicKey before ++ event.call :: historyFor publicKey after := by
  rw [history_append, history_selected_cons publicKey event after selected]

/-- A source-origin failure exposes the same weak forgery or displayed hash collision as the existing ML theorem. -/
theorem source_origin_failure_split (hash : MldsaTranscriptAuth.Hash512) (verify : MldsaTranscriptAuth.Verify)
    (publicKey : Pqxdh.Bytes) (protectedKey : Bool) (events : List Observation)
    (candidate : MldsaTranscriptAuth.Payload) (signature : Pqxdh.Bytes)
    (accepted : MldsaTranscriptAuth.Accepted hash verify
      (trial publicKey protectedKey events candidate signature))
    (absent : ¬ ∃ event ∈ events, absBytes event.publicKey = publicKey ∧ event.payload = candidate) :
    MldsaTranscriptAuth.WeakForgery hash verify (trial publicKey protectedKey events candidate signature) ∨
      MldsaTranscriptAuth.TranscriptCollision hash (trial publicKey protectedKey events candidate signature) :=
  MldsaTranscriptAuth.origin_failure_split hash verify _
    ⟨accepted, fun issued => absent ((issued_iff_source_event publicKey protectedKey events candidate signature).mp issued)⟩

/-- A public verification attempt with its chronological source-signing observations. -/
structure SourceTrial where
  publicKey : Pqxdh.Bytes
  protectedKey : Bool
  events : List Observation
  candidate : MldsaTranscriptAuth.Payload
  signature : Pqxdh.Bytes

def SourceTrial.toTrial (source : SourceTrial) : MldsaTranscriptAuth.Trial :=
  trial source.publicKey source.protectedKey source.events source.candidate source.signature

def SourceOriginFailure (hash : MldsaTranscriptAuth.Hash512) (verify : MldsaTranscriptAuth.Verify)
    (source : SourceTrial) : Prop :=
  MldsaTranscriptAuth.Accepted hash verify source.toTrial ∧
    ¬ ∃ event ∈ source.events, absBytes event.publicKey = source.publicKey ∧ event.payload = source.candidate

/-- The old event split lifts to any distribution of source observations, without adding a primitive hypothesis. -/
theorem source_origin_failure_bound [MeasurableSpace SourceTrial]
    (hash : MldsaTranscriptAuth.Hash512) (verify : MldsaTranscriptAuth.Verify)
    (traces : MeasureTheory.Measure SourceTrial) :
    traces {source | SourceOriginFailure hash verify source} ≤
      traces {source | MldsaTranscriptAuth.WeakForgery hash verify source.toTrial} +
        traces {source | MldsaTranscriptAuth.TranscriptCollision hash source.toTrial} :=
  (MeasureTheory.measure_mono (show {source | SourceOriginFailure hash verify source} ⊆
    {source | MldsaTranscriptAuth.WeakForgery hash verify source.toTrial} ∪
      {source | MldsaTranscriptAuth.TranscriptCollision hash source.toTrial} from
    fun source failure => source_origin_failure_split hash verify source.publicKey source.protectedKey
      source.events source.candidate source.signature failure.1 failure.2)).trans
    (MeasureTheory.measure_union_le _ _)

/-- The source-log byte-origin bound retains the existing explicit primitive-error conditions. -/
theorem source_origin_failure_le_errors [MeasurableSpace SourceTrial]
    (hash : MldsaTranscriptAuth.Hash512) (verify : MldsaTranscriptAuth.Verify)
    (traces : MeasureTheory.Measure SourceTrial) (signatureError hashError : ENNReal)
    (signatureBound : traces {source | MldsaTranscriptAuth.WeakForgery hash verify source.toTrial} ≤ signatureError)
    (collisionBound : traces {source | MldsaTranscriptAuth.TranscriptCollision hash source.toTrial} ≤ hashError) :
    traces {source | SourceOriginFailure hash verify source} ≤ signatureError + hashError :=
  (source_origin_failure_bound hash verify traces).trans (add_le_add signatureBound collisionBound)

end BeaconcryptCore.Refinement.RegistrationSigningHistory

/-- info: 'BeaconcryptCore.Refinement.RegistrationSigningHistory.history_append' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationSigningHistory.history_append
/-- info: 'BeaconcryptCore.Refinement.RegistrationSigningHistory.history_selected_cons' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationSigningHistory.history_selected_cons
/-- info: 'BeaconcryptCore.Refinement.RegistrationSigningHistory.history_mem_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationSigningHistory.history_mem_iff
/-- info: 'BeaconcryptCore.Refinement.RegistrationSigningHistory.issued_iff_source_event' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationSigningHistory.issued_iff_source_event
/-- info: 'BeaconcryptCore.Refinement.RegistrationSigningHistory.execution_counts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationSigningHistory.execution_counts
/-- info: 'BeaconcryptCore.Refinement.RegistrationSigningHistory.history_selected_at_position' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationSigningHistory.history_selected_at_position
/-- info: 'BeaconcryptCore.Refinement.RegistrationSigningHistory.source_origin_failure_split' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationSigningHistory.source_origin_failure_split
/-- info: 'BeaconcryptCore.Refinement.RegistrationSigningHistory.source_origin_failure_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationSigningHistory.source_origin_failure_bound
/-- info: 'BeaconcryptCore.Refinement.RegistrationSigningHistory.source_origin_failure_le_errors' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationSigningHistory.source_origin_failure_le_errors
