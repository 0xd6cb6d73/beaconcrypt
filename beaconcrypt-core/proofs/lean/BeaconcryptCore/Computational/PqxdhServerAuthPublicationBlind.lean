import BeaconcryptCore.Computational.PqxdhServerAuthPublicationForcedFrame
import BeaconcryptCore.Computational.PqxdhServerAuthPublicationGhost
import BeaconcryptCore.Computational.PqxdhServerAuthPublicationReference

/-! The forced inner writer cannot pass selected ciphertext contents into the executable source continuation. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhServerAuthPublicationBlind
open CtxRomAuth AdaptiveCtxReceive AdaptiveCtxDynamicKnownKeys
open PqxdhServerAuthPublicationForcedFrame
variable {Result : Type}

/-- Execute the actual component request, preserving refusal, but give a fixed replacement for a successful selected seal. Every known-key request stays unchanged. -/
noncomputable def scrub (replacement : CtxRomRecord) : QueryImpl Spec (OracleComp Spec)
  | .inl (.inl (.inr (.inr input))) => do
      let reply ← Spec.query (.inl (.inl (.inr (.inr input))))
      pure (reply.map fun _ => replacement)
  | query => Spec.query query

/-- An executable component program with no selected sealing request is unchanged by replacement, including all public and known-key work. -/
theorem quiet (replacement : CtxRomRecord) (work : OracleComp Spec Result)
    (bounded : work.IsQueryBoundP (AdaptiveCtxDynamicKnownBounds.TargetClass AdaptiveCtxQueryBounds.SourceSeal) 0) :
    simulateQ (scrub replacement) work = work := by
  induction work using OracleComp.inductionOn with
  | pure value => simp only [simulateQ_pure]
  | query_bind query next ih =>
    simp only [OracleComp.isQueryBoundP_query_bind_iff, Nat.lt_irrefl, or_false,
      Nat.zero_sub, ite_self] at bounded
    rcases query with (((coin | (input | request)) | raw) | known)
    all_goals simp only [simulateQ_bind, simulateQ_spec_query, scrub]
    all_goals first
      | exact False.elim (bounded.1 trivial)
      | exact bind_congr fun reply => ih reply (bounded.2 reply)

open PqxdhFullSecretInputKdf RawCtxSelectedMessageSealing

/-- The literal forced selected writer depends only on the actual optional reply's success/refusal, never on its returned record contents. -/
theorem selected_scrub (replacement : CtxRomRecord) (nonce : NonceOutput) (sequence : Std.U64)
    (context : RawCtxSourceSend.SealContext) :
    simulateQ (scrub replacement) (simulateQ RawCtxSelectedSealConsumer.liftSelected
      (selected writer nonce sequence context)) =
      simulateQ RawCtxSelectedSealConsumer.liftSelected (selected writer nonce sequence context) := by
  unfold selected
  split
  · simp only [simulateQ_bind, simulateQ_spec_query, RawCtxSelectedSealConsumer.liftSelected,
      scrub, bind_assoc, pure_bind]
    apply bind_congr
    intro reply
    cases reply <;> rfl
  · simp only [simulateQ_pure]

/-- The actual material dispatcher is blind to successful selected record contents; real known-material work remains unchanged, including byte aliases. -/
theorem call_scrub (replacement : CtxRomRecord) (crypto : Pqxdh.Crypto)
    (input : RawCtxInterpretedArguments.Input RawCtxSelectedMessageKey.Slot RawCtxSourceSend.SealContext) :
    simulateQ (scrub replacement) (RawCtxSelectedSealConsumer.call crypto writer input) =
      RawCtxSelectedSealConsumer.call crypto writer input := by
  rcases input with ⟨material, sequence, context⟩
  cases material with
  | hidden nonce => exact selected_scrub replacement nonce sequence context
  | known material =>
    exact quiet replacement _ (RawCtxSelectedSealConsumer.call_seal crypto writer
      ⟨.known material, sequence, context⟩)

/-- Complete native optional conversion retains only component refusal and the constant failed-writer reply. -/
theorem sealing_scrub (replacement : CtxRomRecord) (crypto : Pqxdh.Crypto)
    (pending : RawCtxInterpretedSend.Seal RawCtxSelectedMessageKey.Slot RawCtxSourceSend.SealContext) :
    simulateQ (scrub replacement) (RawCtxSelectedSealConsumer.sealing crypto writer pending) =
      RawCtxSelectedSealConsumer.sealing crypto writer pending := by
  simp only [RawCtxSelectedSealConsumer.sealing, simulateQ_map, call_scrub]

/-- The complete optional sealer preserves its source log and ignores the contents of a successful selected reply. -/
theorem sealer_scrub (replacement : CtxRomRecord)
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (pending : PqxdhServerAuthCtxSend.Pending) (before : PqxdhServerAuthBuildProgram.Log) :
    simulateQ (scrub replacement) ((PqxdhServerAuthBuildProgram.sealer source writer pending).run.run before) =
      (PqxdhServerAuthBuildProgram.sealer source writer pending).run.run before := by
  simp only [PqxdhServerAuthPublicationForcedFrame.sealer_run source writer,
    simulateQ_map, sealing_scrub]

/-- Pointwise replacement invariance extends through every optional adaptive continuation, retaining the complete local state and refusal branch. -/
theorem optional_scrub {Input State : Type} {spec : OracleSpec Input}
    (replacement : CtxRomRecord)
    (handler : QueryImpl spec (OptionT (StateT State (OracleComp Spec))))
    (same : ∀ query state, simulateQ (scrub replacement) ((handler query).run.run state) =
      (handler query).run.run state)
    (work : OracleComp spec Result) (state : State) :
    simulateQ (scrub replacement) ((simulateQ handler work).run.run state) =
      (simulateQ handler work).run.run state := by
  induction work using OracleComp.inductionOn generalizing state with
  | pure value => simp only [simulateQ_pure, OptionT.run_pure, StateT.run_pure]
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, OptionT.run_bind,
        Option.elimM, StateT.run_bind, same]
      refine bind_congr fun ⟨reply, after⟩ => ?_
      cases reply with
      | none => simp only [Option.elim_none, StateT.run_pure, simulateQ_pure]
      | some value => exact ih value after

open PqxdhServerAuthExperiment (Codec Checks)
variable {Reader WireResponse : Type}

/-- Every actual builder service is invariant under selected-record replacement when only its inner writer is forced to fail. Auxiliary outcomes, including the original outer writer, are unchanged. -/
theorem compiler_scrub (replacement : CtxRomRecord)
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (codec : Codec Reader WireResponse) (checks : Checks)
    (query : PqxdhServerAuthBuildProgram.Spec.Domain) (before : PqxdhServerAuthBuildProgram.Log) :
    simulateQ (scrub replacement) ((PqxdhServerAuthBuildProgram.compiler source
      (referenceCodec codec) checks query).run.run before) =
      (PqxdhServerAuthBuildProgram.compiler source (referenceCodec codec) checks query).run.run before := by
  cases query with
  | inl pending => exact sealer_scrub replacement source pending before
  | inr query => cases query <;> rfl

/-- The entire literal reference builder, including all source admission, allocation, KDF, diagnostic and publication branches, is invariant under replacement of successful selected records. -/
theorem compiled_scrub {Metadata PeerMetadata Consumed : Type} (replacement : CtxRomRecord)
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (codec : Codec Reader WireResponse) (checks : Checks)
    (rest : PqxdhServerAuthCtxCalls.Residual) (pending : pqxdh.PendingServerRegistration)
    (data : Option Pqxdh.Bytes) (metadata : PeerMetadata)
    (state : PqxdhServerRegistrationPublication.State Metadata PeerMetadata Consumed)
    (before : PqxdhServerAuthBuildProgram.Log) :
    simulateQ (scrub replacement) ((PqxdhServerAuthBuildProgram.compiled source
      (referenceCodec codec) checks rest pending data metadata state).run.run before) =
      (PqxdhServerAuthBuildProgram.compiled source (referenceCodec codec) checks rest pending data metadata state).run.run before :=
  optional_scrub replacement _ (compiler_scrub replacement source codec checks) _ before

open PqxdhServerAuthExperiment PqxdhServerAuthEntryFactor PqxdhServerAuthCtxState
variable {KemSK : Type}

/-- Session settlement observes the unchanged reference builder result and full log, so the selected callback remains invariant under record replacement. -/
theorem selected_build_scrub (replacement : CtxRomRecord)
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (codec : Codec Reader WireResponse) (checks : Checks)
    (rest : PqxdhServerAuthCtxCalls.Residual) (session : Nat)
    (token : PqxdhServerRelatedRootConsumer.Returned) (payload : Option Pqxdh.Bytes)
    (server : ServerState) (state : Local KemSK) :
    simulateQ (scrub replacement) ((PqxdhServerAuthCtxBuild.selected source
      (referenceCodec codec) checks rest session token payload server).run.run state) =
      (PqxdhServerAuthCtxBuild.selected source (referenceCodec codec) checks rest session token payload server).run.run state := by
  change simulateQ (scrub replacement) (PqxdhServerAuthCtxBuild.post session state <$>
    (PqxdhServerAuthBuildProgram.compiled source (referenceCodec codec) checks rest token.pending payload () server).run.run []) = _
  rw [simulateQ_map, compiled_scrub]
  rfl

/-- The actual mixed pending-token dispatcher preserves arbitrary known-key work and uses the blind writer only on its marked selected branch. -/
theorem build_scrub (replacement : CtxRomRecord)
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (codec : Codec Reader WireResponse) (checks : Checks)
    (rest : PqxdhServerAuthCtxCalls.Residual) (session : Nat)
    (payload : Option Pqxdh.Bytes) (state : Local KemSK) :
    simulateQ (scrub replacement) ((PqxdhServerAuthPublicationReference.build source
      codec checks rest session payload).run.run state) =
      (PqxdhServerAuthPublicationReference.build source codec checks rest session payload).run.run state := by
  simp only [PqxdhServerAuthPublicationReference.build, OptionT.run_mk, StateT.run]
  cases found : state.1.1.pending session with
  | none => simp only [simulateQ_pure]
  | some token =>
      split_ifs
      · exact selected_build_scrub replacement source codec checks rest session token payload _ state
      · exact quiet replacement _ (PqxdhServerAuthCtxBuildBounds.known_bills source codec checks session token payload _ state).2.2.1

variable {ι : Type} {baseSpec : OracleSpec ι}

/-- Every original API route outside build has zero selected seals; the mixed builder uses its exact replacement equation. All actual reply-dependent continuations and state are retained. -/
theorem route_scrub (replacement : CtxRomRecord)
    (setup : Setup baseSpec KemSK) (codec : Codec Reader WireResponse) (checks : Checks)
    (context : Context KemSK) (rest : PqxdhServerAuthCtxCalls.Residual)
    (select : Bool) (query : ServerAuthSpec.Domain) (state : Local KemSK) :
    simulateQ (scrub replacement) ((PqxdhServerAuthPublicationReference.route setup
      codec checks context rest select query).run.run state) =
      (PqxdhServerAuthPublicationReference.route setup codec checks context rest select query).run.run state := by
  have bounded := (PqxdhServerAuthCtxHandlerBounds.route_record_bills setup codec checks context rest select query state).1
  rcases query with (coin | query)
  · exact quiet replacement _ bounded
  · cases query with
    | build session payload => exact build_scrub replacement setup.source codec checks rest session payload state
    | accept raw => exact quiet replacement _ bounded
    | finish raw => exact quiet replacement _ bounded
    | hmac key message => exact quiet replacement _ bounded
    | hash bytes => exact quiet replacement _ bounded
    | reveal keyId => exact quiet replacement _ bounded

/-- The original designation latch and sticky refusal settlement inspect the same complete callback result under replacement. -/
theorem handler_scrub (replacement : CtxRomRecord)
    (setup : Setup baseSpec KemSK) (codec : Codec Reader WireResponse) (checks : Checks)
    (context : Context KemSK) (rest : PqxdhServerAuthCtxCalls.Residual)
    (Q : Nat) (j : Fin (Q + 1)) (query : ServerAuthSpec.Domain) (state : Local KemSK) :
    simulateQ (scrub replacement) ((PqxdhServerAuthPublicationReference.handler setup
      codec checks context rest Q j query).run.run state) =
      (PqxdhServerAuthPublicationReference.handler setup codec checks context rest Q j query).run.run state := by
  change simulateQ (scrub replacement) (PqxdhServerAuthCtxHandler.settle Q j query state <$>
    (PqxdhServerAuthPublicationReference.route setup codec checks context rest
      (!state.2 && hiddenDesignated Q j query state.1) query).run.run state) = _
  rw [simulateQ_map, route_scrub]
  rfl

/-- The real post-accept stop monitor preserves replacement invariance even when it refuses after a completed callback. -/
theorem stopped_scrub (replacement : CtxRomRecord)
    (setup : Setup baseSpec KemSK) (codec : Codec Reader WireResponse) (checks : Checks)
    (context : Context KemSK) (rest : PqxdhServerAuthCtxCalls.Residual)
    (Q : Nat) (j : Fin (Q + 1)) (query : ServerAuthSpec.Domain) (state : Local KemSK × Option Nat) :
    simulateQ (scrub replacement) ((PqxdhServerAuthPublicationReference.stopped setup
      codec checks context rest Q j query).run.run state) =
      (PqxdhServerAuthPublicationReference.stopped setup codec checks context rest Q j query).run.run state := by
  simp only [PqxdhServerAuthPublicationReference.stopped, PqxdhServerAuthCtxReserve.stopped,
    PqxdhServerAuthCtxStop.stopped, OptionT.run_mk, StateT.run, bind_pure_comp, simulateQ_map]
  exact congrArg (Functor.map (PqxdhServerAuthCtxStop.observe
    (fun localState : Local KemSK => localState.1.1.sessions)
    (fun localState : Local KemSK => localState.1.2.1) query state))
    (handler_scrub replacement setup codec checks context rest Q j query state.1)

/-- Every optional adaptive reference continuation is unchanged as a complete component program, including its original monitored state and all failure branches. -/
theorem program_scrub (replacement : CtxRomRecord)
    (setup : Setup baseSpec KemSK) (codec : Codec Reader WireResponse) (checks : Checks)
    (context : Context KemSK) (rest : PqxdhServerAuthCtxCalls.Residual)
    (Q : Nat) (j : Fin (Q + 1)) (work : OracleComp ServerAuthSpec Result) (state : Local KemSK × Option Nat) :
    simulateQ (scrub replacement) ((simulateQ (PqxdhServerAuthPublicationReference.stopped setup
      codec checks context rest Q j) work).run.run state) =
      (simulateQ (PqxdhServerAuthPublicationReference.stopped setup codec checks context rest Q j) work).run.run state :=
  optional_scrub replacement _ (stopped_scrub replacement setup codec checks context rest Q j) work state

/-- The actual adversary starts in the literal initial monitored state; no caller control or history invariant is required for replacement invariance. -/
theorem execution_scrub (replacement : CtxRomRecord)
    (setup : Setup baseSpec KemSK) (codec : Codec Reader WireResponse) (checks : Checks)
    (adversary : Adversary) (Q : Nat) (j : Fin (Q + 1))
    (context : Context KemSK) (rest : PqxdhServerAuthCtxCalls.Residual) :
    simulateQ (scrub replacement) (PqxdhServerAuthPublicationReference.execution setup
      codec checks adversary Q j context rest) =
      PqxdhServerAuthPublicationReference.execution setup codec checks adversary Q j context rest :=
  program_scrub replacement setup codec checks context rest Q j _ _

/-- The original source sampler contains no selected sealing request, even when later draws depend on earlier samples. -/
theorem sample_scrub (replacement : CtxRomRecord) (sample : ProbComp Result) :
    simulateQ (scrub replacement) (simulateQ PqxdhServerAuthCtxAmbient.coin sample) =
      simulateQ PqxdhServerAuthCtxAmbient.coin sample :=
  quiet replacement _ (PqxdhServerAuthCtxAmbient.coin_other sample).2.1

/-- The exact fully sampled reference client is invariant under successful selected-record replacement, retaining the original context, residual material and complete optional execution result. -/
theorem client_scrub (replacement : CtxRomRecord)
    (setup : Setup baseSpec KemSK) (codec : Codec Reader WireResponse) (checks : Checks)
    (adversary : Adversary) (Q : Nat) (j : Fin (Q + 1)) :
    simulateQ (scrub replacement) (PqxdhServerAuthPublicationReference.client setup
      codec checks adversary Q j) =
      PqxdhServerAuthPublicationReference.client setup codec checks adversary Q j := by
  simp only [PqxdhServerAuthPublicationReference.client, simulateQ_bind,
    simulateQ_pure, sample_scrub, execution_scrub]

end BeaconcryptCore.Computational.PqxdhServerAuthPublicationBlind

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationBlind.quiet' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationBlind.quiet

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationBlind.selected_scrub' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationBlind.selected_scrub

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationBlind.call_scrub' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationBlind.call_scrub

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationBlind.sealing_scrub' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationBlind.sealing_scrub

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationBlind.sealer_scrub' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationBlind.sealer_scrub

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationBlind.optional_scrub' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationBlind.optional_scrub

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationBlind.compiler_scrub' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationBlind.compiler_scrub

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationBlind.compiled_scrub' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationBlind.compiled_scrub

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationBlind.selected_build_scrub' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationBlind.selected_build_scrub

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationBlind.build_scrub' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationBlind.build_scrub

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationBlind.route_scrub' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationBlind.route_scrub

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationBlind.handler_scrub' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationBlind.handler_scrub

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationBlind.stopped_scrub' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationBlind.stopped_scrub

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationBlind.program_scrub' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationBlind.program_scrub

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationBlind.execution_scrub' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationBlind.execution_scrub

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationBlind.sample_scrub' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationBlind.sample_scrub

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationBlind.client_scrub' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationBlind.client_scrub
