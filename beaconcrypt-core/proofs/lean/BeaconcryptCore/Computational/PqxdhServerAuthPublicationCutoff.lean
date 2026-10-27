import BeaconcryptCore.Computational.PqxdhServerAuthPublicationTrace
import BeaconcryptCore.Computational.AdaptiveCtxDynamicKnownBounds

/-! The publication observer stops before the first selected raw request. It forwards every preceding real component query, keeps known-key calls unchanged and retains the actual selected-seal reply before any writer-dependent continuation. -/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhServerAuthPublicationCutoff
open PqxdhServerAuthPublicationTrace (Annotation AnnotatedSpec)
open CtxRomAuth

/-- Private chronological evidence retains the exact component seal reply as well as the source's separate begin/completion annotations. A failed writer never deletes the component record from this journal. -/
inductive Observation where
  | annotation (event : Annotation)
  | selectedSeal (input : CtxSealInput) (reply : Option CtxRomRecord)

abbrev Journal := List Observation
abbrev Candidate := Pqxdh.Bytes × Journal

/-- Stop before forwarding any selected raw request, including malformed raw bytes. Actual known-key raw calls still execute through their original local interface. The candidate and private journal are outputs only for the final decision. -/
noncomputable def beforeRaw {Result : Type} (client : OracleComp AnnotatedSpec Result) :
    Journal → OracleComp AdaptiveCtxDynamicKnownKeys.Spec (Option Candidate) :=
  OracleComp.recOn client
    (fun _ _ => pure none)
    (fun query _ recurse history =>
      match query with
      | .inl (.inl (.inr raw)) => pure (some (raw, history))
      | .inl (.inl (.inl (.inr (.inr input)))) => do
          let reply ← AdaptiveCtxDynamicKnownKeys.Spec.query (.inl (.inl (.inr (.inr input))))
          recurse reply (history ++ [.selectedSeal input reply])
      | .inl request => do
          let reply ← AdaptiveCtxDynamicKnownKeys.Spec.query request
          recurse reply history
      | .inr event => recurse () (history ++ [.annotation event]))

/-- Stopping without a selected raw request supplies no fallback candidate. -/
theorem beforeRaw_pure {Result : Type} (value : Result) (history : Journal) :
    beforeRaw (pure value) history = pure none := rfl

/-- The first selected raw request is never issued to the challenger, decoded or looked up by this observer. Its exact bytes are returned as the sole candidate. -/
theorem beforeRaw_raw {Result : Type} (raw : Pqxdh.Bytes)
    (next : Option Pqxdh.Bytes → OracleComp AnnotatedSpec Result) (history : Journal) :
    beforeRaw (liftM (AnnotatedSpec.query (.inl (.inl (.inr raw)))) >>= next) history =
      pure (some (raw, history)) := rfl

/-- The source completion annotation remains private and returns only Unit to the unchanged continuation. -/
theorem beforeRaw_annotation {Result : Type} (event : Annotation)
    (next : Unit → OracleComp AnnotatedSpec Result) (history : Journal) :
    beforeRaw (liftM (AnnotatedSpec.query (.inr event)) >>= next) history =
      beforeRaw (next ()) (history ++ [.annotation event]) := rfl

/-- The original selected-seal query is forwarded once, and its actual optional component record is retained before the writer-dependent continuation executes. -/
theorem beforeRaw_seal {Result : Type} (input : CtxSealInput)
    (next : Option CtxRomRecord → OracleComp AnnotatedSpec Result) (history : Journal) :
    beforeRaw (liftM (AnnotatedSpec.query (.inl (.inl (.inl (.inr (.inr input)))))) >>= next) history = (do
      let reply ← AdaptiveCtxDynamicKnownKeys.Spec.query (.inl (.inl (.inr (.inr input))))
      beforeRaw (next reply) (history ++ [.selectedSeal input reply])) := rfl

/-- Uniform source queries remain exact and do not expose the private journal. -/
theorem beforeRaw_coin {Result : Type} (coin : unifSpec.Domain)
    (next : unifSpec.Range coin → OracleComp AnnotatedSpec Result) (history : Journal) :
    beforeRaw (liftM (AnnotatedSpec.query (.inl (.inl (.inl (.inl coin))))) >>= next) history = (do
      let reply ← AdaptiveCtxDynamicKnownKeys.Spec.query (.inl (.inl (.inl coin)))
      beforeRaw (next reply) history) := rfl

/-- Every preceding selected public-hash request executes against the original shared interface. -/
theorem beforeRaw_hash {Result : Type} (input : CtxRO.Domain)
    (next : CtxDigest → OracleComp AnnotatedSpec Result) (history : Journal) :
    beforeRaw (liftM (AnnotatedSpec.query (.inl (.inl (.inl (.inr (.inl input)))))) >>= next) history = (do
      let reply ← AdaptiveCtxDynamicKnownKeys.Spec.query (.inl (.inl (.inr (.inl input))))
      beforeRaw (next reply) history) := rfl

/-- Known-key calls retain all their actual local work and optional replies, even when a supplied key has equal bytes to the selected key. -/
theorem beforeRaw_known {Result : Type} (known : AdaptiveCtxDynamicKnownKeys.KnownCall)
    (next : AdaptiveCtxReceive.ReceiveSpec.Range known.request → OracleComp AnnotatedSpec Result)
    (history : Journal) :
    beforeRaw (liftM (AnnotatedSpec.query (.inl (.inr known))) >>= next) history = (do
      let reply ← AdaptiveCtxDynamicKnownKeys.Spec.query (.inr known)
      beforeRaw (next reply) history) := rfl

set_option backward.isDefEq.respectTransparency false in
/-- Every adaptive annotated client stops without issuing any selected raw query. This includes malformed first requests and does not assume a source raw budget or a successful parse. -/
theorem beforeRaw_zero_raw {Result : Type} (client : OracleComp AnnotatedSpec Result) (history : Journal) :
    (beforeRaw client history).IsQueryBoundP
      (AdaptiveCtxDynamicKnownBounds.TargetClass AdaptiveCtxReceive.IsRawQuery) 0 := by
  induction client using OracleComp.inductionOn generalizing history with
  | pure value => simp [beforeRaw_pure]
  | query_bind query next ih =>
      rcases query with ((((coin | (hash | input)) | raw) | known) | event)
      · rw [beforeRaw_coin coin next history]
        simp [AdaptiveCtxDynamicKnownBounds.TargetClass, AdaptiveCtxReceive.IsRawQuery, ih]
      · rw [beforeRaw_hash hash next history]
        simp [AdaptiveCtxDynamicKnownBounds.TargetClass, AdaptiveCtxReceive.IsRawQuery, ih]
      · rw [beforeRaw_seal input next history]
        simp [AdaptiveCtxDynamicKnownBounds.TargetClass, AdaptiveCtxReceive.IsRawQuery, ih]
      · rw [beforeRaw_raw raw next history]
        simp
      · rw [beforeRaw_known known next history]
        simp [AdaptiveCtxDynamicKnownBounds.TargetClass, ih]
      · exact ih () (history ++ [.annotation event])

/-- The cutoff preserves every generalized query budget of the annotation-erased client. This includes separate oracle classes and weighted plaintext bytes; private journal updates add no component request. -/
theorem beforeRaw_budget {Result Budget : Type} (client : OracleComp AnnotatedSpec Result)
    (canQuery : AdaptiveCtxDynamicKnownKeys.Spec.Domain → Budget → Prop)
    (cost : AdaptiveCtxDynamicKnownKeys.Spec.Domain → Budget → Budget)
    (budget : Budget) (history : Journal)
    (bounded : (simulateQ PqxdhServerAuthPublicationTrace.erase client).IsQueryBound budget canQuery cost) :
    (beforeRaw client history).IsQueryBound budget canQuery cost := by
  induction client using OracleComp.inductionOn generalizing budget history with
  | pure value => simp [beforeRaw_pure]
  | query_bind query next ih =>
      rcases query with ((((coin | (hash | input)) | raw) | known) | event)
      · simp only [simulateQ_bind, simulateQ_spec_query, PqxdhServerAuthPublicationTrace.erase,
          isQueryBound_query_bind_iff] at bounded
        rw [beforeRaw_coin coin next history, isQueryBound_query_bind_iff]
        exact ⟨bounded.1, fun reply => ih reply _ history (bounded.2 reply)⟩
      · simp only [simulateQ_bind, simulateQ_spec_query, PqxdhServerAuthPublicationTrace.erase,
          isQueryBound_query_bind_iff] at bounded
        rw [beforeRaw_hash hash next history, isQueryBound_query_bind_iff]
        exact ⟨bounded.1, fun reply => ih reply _ history (bounded.2 reply)⟩
      · simp only [simulateQ_bind, simulateQ_spec_query, PqxdhServerAuthPublicationTrace.erase,
          isQueryBound_query_bind_iff] at bounded
        rw [beforeRaw_seal input next history, isQueryBound_query_bind_iff]
        exact ⟨bounded.1, fun reply => ih reply _ (history ++ [.selectedSeal input reply]) (bounded.2 reply)⟩
      · rw [beforeRaw_raw raw next history]
        trivial
      · simp only [simulateQ_bind, simulateQ_spec_query, PqxdhServerAuthPublicationTrace.erase,
          isQueryBound_query_bind_iff] at bounded
        rw [beforeRaw_known known next history, isQueryBound_query_bind_iff]
        exact ⟨bounded.1, fun reply => ih reply _ history (bounded.2 reply)⟩
      · simp only [simulateQ_bind, simulateQ_spec_query, PqxdhServerAuthPublicationTrace.erase,
          pure_bind] at bounded
        exact ih () budget (history ++ [.annotation event]) bounded

/-- In particular, every actual uniform/hash/seal class bound is retained from the original erased client. -/
theorem beforeRaw_class {Result : Type} (client : OracleComp AnnotatedSpec Result)
    (predicate : AdaptiveCtxDynamicKnownKeys.Spec.Domain → Prop) [DecidablePred predicate]
    (bound : Nat) (history : Journal)
    (bounded : (simulateQ PqxdhServerAuthPublicationTrace.erase client).IsQueryBoundP predicate bound) :
    (beforeRaw client history).IsQueryBoundP predicate bound :=
  beforeRaw_budget client _ _ bound history bounded

/-- The weighted selected-plaintext bill is preserved without counting known-key local encryptions as selected messages. -/
theorem beforeRaw_plaintext {Result : Type} (client : OracleComp AnnotatedSpec Result)
    (bound : Nat) (history : Journal)
    (bounded : AdaptiveCtxDynamicKnownBounds.PlaintextBound
      (simulateQ PqxdhServerAuthPublicationTrace.erase client) bound) :
    AdaptiveCtxDynamicKnownBounds.PlaintextBound (beforeRaw client history) bound :=
  beforeRaw_budget client _ _ bound history bounded

/-- This nonstopping observer retains the same chronological evidence while forwarding every actual query. It is used only to identify complete source prefixes before the cutoff. -/
noncomputable def journalImpl : QueryImpl AnnotatedSpec
    (StateT Journal (OracleComp AdaptiveCtxDynamicKnownKeys.Spec)) :=
  fun query history => match query with
  | .inl (.inl (.inl (.inr (.inr input)))) => do
      let reply ← AdaptiveCtxDynamicKnownKeys.Spec.query (.inl (.inl (.inr (.inr input))))
      pure (reply, history ++ [.selectedSeal input reply])
  | .inl request => do
      let reply ← AdaptiveCtxDynamicKnownKeys.Spec.query request
      pure (reply, history)
  | .inr event => pure ((), history ++ [.annotation event])

/-- Erasing the nonstopping journal retains the complete original component program and all adaptive replies. The journal is never passed to the original continuation. -/
theorem journal_erase {Result : Type} (client : OracleComp AnnotatedSpec Result) (history : Journal) :
    Prod.fst <$> (simulateQ journalImpl client).run history =
      simulateQ PqxdhServerAuthPublicationTrace.erase client := by
  induction client using OracleComp.inductionOn generalizing history with
  | pure value => simp only [simulateQ_pure, StateT.run_pure, map_pure]
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, map_bind]
      rcases query with ((((coin | (hash | input)) | raw) | known) | event)
      · simp only [journalImpl, StateT.run, bind_assoc, pure_bind, PqxdhServerAuthPublicationTrace.erase]
        exact bind_congr fun reply => ih reply history
      · simp only [journalImpl, StateT.run, bind_assoc, pure_bind, PqxdhServerAuthPublicationTrace.erase]
        exact bind_congr fun reply => ih reply history
      · simp only [journalImpl, StateT.run, bind_assoc, pure_bind, PqxdhServerAuthPublicationTrace.erase]
        exact bind_congr fun reply => ih reply (history ++ [Observation.selectedSeal input reply])
      · simp only [journalImpl, StateT.run, bind_assoc, pure_bind, PqxdhServerAuthPublicationTrace.erase]
        exact bind_congr fun reply => ih reply history
      · simp only [journalImpl, StateT.run, bind_assoc, pure_bind, PqxdhServerAuthPublicationTrace.erase]
        exact bind_congr fun reply => ih reply history
      · simp only [journalImpl, StateT.run, pure_bind, PqxdhServerAuthPublicationTrace.erase]
        exact ih () (history ++ [.annotation event])

set_option backward.isDefEq.respectTransparency false in
/-- A prefix that makes no selected raw query completes with its full chronological journal before the cutoff continues. No source reply, component seal or annotation is replayed. -/
theorem beforeRaw_prefix {Middle Result : Type} (work : OracleComp AnnotatedSpec Middle)
    (next : Middle → OracleComp AnnotatedSpec Result) (history : Journal)
    (quiet : (simulateQ PqxdhServerAuthPublicationTrace.erase work).IsQueryBoundP
      (AdaptiveCtxDynamicKnownBounds.TargetClass AdaptiveCtxReceive.IsRawQuery) 0) :
    beforeRaw (work >>= next) history = (do
      let result ← (simulateQ journalImpl work).run history
      beforeRaw (next result.1) result.2) := by
  induction work using OracleComp.inductionOn generalizing history with
  | pure value => simp only [pure_bind, simulateQ_pure, StateT.run_pure]
  | query_bind query after ih =>
      rw [bind_assoc]
      rcases query with ((((coin | (hash | input)) | raw) | known) | event)
      · simp only [simulateQ_bind, simulateQ_spec_query, PqxdhServerAuthPublicationTrace.erase,
          isQueryBoundP_query_bind_iff] at quiet
        change (do
          let reply ← AdaptiveCtxDynamicKnownKeys.Spec.query (.inl (.inl (.inl coin)))
          beforeRaw (after reply >>= next) history :
            OracleComp AdaptiveCtxDynamicKnownKeys.Spec (Option Candidate)) = _
        simp only [simulateQ_bind, simulateQ_spec_query, StateT.run]
        exact bind_congr fun reply => ih reply history (by simpa [AdaptiveCtxDynamicKnownBounds.TargetClass, AdaptiveCtxReceive.IsRawQuery] using quiet.2 reply)
      · simp only [simulateQ_bind, simulateQ_spec_query, PqxdhServerAuthPublicationTrace.erase,
          isQueryBoundP_query_bind_iff] at quiet
        change (do
          let reply ← AdaptiveCtxDynamicKnownKeys.Spec.query (.inl (.inl (.inr (.inl hash))))
          beforeRaw (after reply >>= next) history :
            OracleComp AdaptiveCtxDynamicKnownKeys.Spec (Option Candidate)) = _
        simp only [simulateQ_bind, simulateQ_spec_query, StateT.run]
        exact bind_congr fun reply => ih reply history (by simpa [AdaptiveCtxDynamicKnownBounds.TargetClass, AdaptiveCtxReceive.IsRawQuery] using quiet.2 reply)
      · simp only [simulateQ_bind, simulateQ_spec_query, PqxdhServerAuthPublicationTrace.erase,
          isQueryBoundP_query_bind_iff] at quiet
        change (do
          let reply ← AdaptiveCtxDynamicKnownKeys.Spec.query (.inl (.inl (.inr (.inr input))))
          beforeRaw (after reply >>= next) (history ++ [Observation.selectedSeal input reply]) :
            OracleComp AdaptiveCtxDynamicKnownKeys.Spec (Option Candidate)) = _
        simp only [simulateQ_bind, simulateQ_spec_query, StateT.run]
        exact bind_congr fun reply => ih reply (history ++ [Observation.selectedSeal input reply])
          (by simpa [AdaptiveCtxDynamicKnownBounds.TargetClass, AdaptiveCtxReceive.IsRawQuery] using quiet.2 reply)
      · simp [simulateQ_bind, PqxdhServerAuthPublicationTrace.erase,
          AdaptiveCtxDynamicKnownBounds.TargetClass, AdaptiveCtxReceive.IsRawQuery] at quiet
      · simp only [simulateQ_bind, simulateQ_spec_query, PqxdhServerAuthPublicationTrace.erase,
          isQueryBoundP_query_bind_iff] at quiet
        change (do
          let reply ← AdaptiveCtxDynamicKnownKeys.Spec.query (.inr known)
          beforeRaw (after reply >>= next) history :
            OracleComp AdaptiveCtxDynamicKnownKeys.Spec (Option Candidate)) = _
        simp only [simulateQ_bind, simulateQ_spec_query, StateT.run]
        exact bind_congr fun reply => ih reply history (by simpa [AdaptiveCtxDynamicKnownBounds.TargetClass] using quiet.2 reply)
      · simp only [simulateQ_bind, simulateQ_spec_query, PqxdhServerAuthPublicationTrace.erase,
          pure_bind] at quiet
        change beforeRaw (after () >>= next) (history ++ [.annotation event]) = _
        simp only [simulateQ_bind, simulateQ_spec_query, StateT.run]
        exact ih () (history ++ [.annotation event]) quiet

/-- The literal observed builder completes before this cutoff can select a raw request. Its actual zero-raw compiler theorem discharges the generic prefix premise, including every rejection and both writer-failure branches. -/
theorem builder_prefix {Reader WireResponse Metadata PeerMetadata Consumed Result : Type}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (codec : PqxdhServerAuthExperiment.Codec Reader WireResponse) (checks : PqxdhServerAuthExperiment.Checks)
    (rest : PqxdhServerAuthCtxCalls.Residual) (coordinate : Nat)
    (pending : pqxdh.PendingServerRegistration) (data : Option Pqxdh.Bytes) (metadata : PeerMetadata)
    (state : PqxdhServerRegistrationPublication.State Metadata PeerMetadata Consumed)
    (log : PqxdhServerAuthBuildProgram.Log)
    (next : (Option (RustM (Option PqxdhServerRegistrationPublication.Response ×
      PqxdhServerRegistrationPublication.State Metadata PeerMetadata Consumed)) × PqxdhServerAuthBuildProgram.Log) →
      OracleComp AnnotatedSpec Result) (history : Journal) :
    beforeRaw (PqxdhServerAuthPublicationTrace.annotated source codec checks rest coordinate
      pending data metadata state log >>= next) history = (do
        let result ← (simulateQ journalImpl (PqxdhServerAuthPublicationTrace.annotated source codec checks rest
          coordinate pending data metadata state log)).run history
        beforeRaw (next result.1) result.2) := by
  apply beforeRaw_prefix
  rw [PqxdhServerAuthPublicationTrace.annotated_erase]
  exact (PqxdhServerAuthBuildProgramBounds.compiled_other source codec checks rest pending data metadata state log).1

/-- The nonstopping source journal places the actual builder's component observations strictly between its begin and completion annotations. The completion contains the actual local trailer, including all optional failure outcomes. -/
theorem journal_builder {Reader WireResponse Metadata PeerMetadata Consumed : Type}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (codec : PqxdhServerAuthExperiment.Codec Reader WireResponse) (checks : PqxdhServerAuthExperiment.Checks)
    (rest : PqxdhServerAuthCtxCalls.Residual) (coordinate : Nat)
    (pending : pqxdh.PendingServerRegistration) (data : Option Pqxdh.Bytes) (metadata : PeerMetadata)
    (state : PqxdhServerRegistrationPublication.State Metadata PeerMetadata Consumed)
    (log : PqxdhServerAuthBuildProgram.Log) (history : Journal) :
    (simulateQ journalImpl (PqxdhServerAuthPublicationTrace.annotated source codec checks rest coordinate
      pending data metadata state log)).run history = (do
        let result ← (simulateQ journalImpl (simulateQ PqxdhServerAuthPublicationTrace.liftDynamic
          ((PqxdhServerAuthPublicationTrace.compiled source codec checks rest pending data metadata state).run.run
            (log, [])))).run (history ++ [.annotation (.beginBuild coordinate)])
        pure (PqxdhServerAuthPublicationTrace.project result.1,
          result.2 ++ [.annotation (.completedBuild coordinate result.1.2.2)])) := by
  simp only [PqxdhServerAuthPublicationTrace.annotated, simulateQ_bind,
    simulateQ_spec_query, simulateQ_pure, StateT.run_bind, StateT.run_pure]
  simp only [journalImpl, StateT.run, pure_bind, map_pure, bind_pure_comp]

end BeaconcryptCore.Computational.PqxdhServerAuthPublicationCutoff

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationCutoff.beforeRaw_pure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationCutoff.beforeRaw_pure

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationCutoff.beforeRaw_raw' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationCutoff.beforeRaw_raw

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationCutoff.beforeRaw_annotation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationCutoff.beforeRaw_annotation

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationCutoff.beforeRaw_seal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationCutoff.beforeRaw_seal

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationCutoff.beforeRaw_coin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationCutoff.beforeRaw_coin

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationCutoff.beforeRaw_hash' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationCutoff.beforeRaw_hash

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationCutoff.beforeRaw_known' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationCutoff.beforeRaw_known

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationCutoff.beforeRaw_zero_raw' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationCutoff.beforeRaw_zero_raw

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationCutoff.beforeRaw_budget' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationCutoff.beforeRaw_budget

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationCutoff.beforeRaw_class' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationCutoff.beforeRaw_class

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationCutoff.beforeRaw_plaintext' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationCutoff.beforeRaw_plaintext

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationCutoff.journal_erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationCutoff.journal_erase

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationCutoff.beforeRaw_prefix' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationCutoff.beforeRaw_prefix

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationCutoff.builder_prefix' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationCutoff.builder_prefix

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationCutoff.journal_builder' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationCutoff.journal_builder
