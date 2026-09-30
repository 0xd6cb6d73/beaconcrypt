import BeaconcryptCore.Computational.PqxdhServerAuthBuildProgram

/-! The executable first-record builder counts attempted component calls through its complete source program, including every rejected branch and both optional writers. Native callback computation retains its separate source bill. -/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete PqxdhRefinement
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhServerAuthBuildProgramBounds
open PqxdhJointKdfGame
open PqxdhServerAuthCtxCalls (Kernel Residual)
open PqxdhServerAuthBuildProgram
open PqxdhServerRegistrationPublication (AuxSpec Response registrationWitness)
open PqxdhInitialGenericPublication (State)

def IsSealing (query : Spec.Domain) : Prop := query.isLeft = true

instance : DecidablePred IsSealing := fun query => inferInstanceAs (Decidable (query.isLeft = true))

/-- The actual chain driver reaches at most one sealing request after its real local KDF step, regardless of exhaustion or the optional writer reply. -/
theorem send_bound (source : FixedHkdfSha512NoSaltSource) (rest : Residual)
    (entry : Kernel) (context : RawCtxSourceSend.SealContext) :
    ((PqxdhServerAuthCtxBuildSettlement.calls (fun entry _ _ => pure (entry, .None))
      source rest sealQuery).send entry context).IsQueryBoundP IsSealing 1 := by
  unfold PqxdhServerAuthCtxBuildSettlement.calls
  apply RawCtxSourceOpen.simulate_bound _ (fun query => query.isRight = true) IsSealing
    _ 1 (RawCtxChainSend.program_seal_bound (RawCtxChainSend.normalBegin entry context))
  intro query
  cases query <;> simp [PqxdhServerAuthCtxBuildSettlement.labels, sealQuery, IsSealing]

variable {Metadata PeerMetadata Consumed : Type}

/-- Erasure and the optional outer response writer add no seal attempt after the actual first-record send. -/
theorem after_bound (source : FixedHkdfSha512NoSaltSource) (rest : Residual)
    (candidate : pqxdh.ServerRegistrationCandidate) (authenticated : Pqxdh.Bytes)
    (entry : Kernel) (metadata : PeerMetadata) (state : State Kernel Metadata PeerMetadata Consumed) :
    (PqxdhInitialGenericPublication.afterInitialization
      (PqxdhServerAuthCtxBuildSettlement.calls (fun entry _ _ => pure (entry, .None)) source rest sealQuery)
      auxQuery candidate authenticated entry metadata state).IsQueryBoundP IsSealing 1 := by
  unfold PqxdhInitialGenericPublication.afterInitialization
  refine (isQueryBoundP_bind (send_bound source rest entry _) (m := 0) (fun sent _ => ?_)).mono (by omega)
  simp only [auxQuery, isQueryBoundP_query_bind_iff]
  refine ⟨by simp [IsSealing], fun _ => ?_⟩
  cases sent.2 with
  | none => trivial
  | some encrypted =>
      rw [isQueryBoundP_query_bind_iff]
      refine ⟨by simp [IsSealing], fun written => ?_⟩
      cases written <;> trivial

/-- Every candidate rejection precedes the same single first-record attempt; no success conditioning is used. -/
theorem candidate_bound (source : FixedHkdfSha512NoSaltSource) (rest : Residual)
    (initial : RustM Kernel) (candidate : pqxdh.ServerRegistrationCandidate) (data : Option Pqxdh.Bytes)
    (metadata : PeerMetadata) (state : State Kernel Metadata PeerMetadata Consumed) :
    (PqxdhInitialGenericBuilder.candidate
      (PqxdhServerAuthCtxBuildSettlement.calls (fun entry _ _ => pure (entry, .None)) source rest sealQuery)
      auxQuery initial candidate data metadata state).IsQueryBoundP IsSealing 1 := by
  unfold PqxdhInitialGenericBuilder.candidate
  simp only [auxQuery, isQueryBoundP_query_bind_iff]
  refine ⟨by simp [IsSealing], fun valid => ?_⟩
  cases valid <;> simp only [Bool.not_false, Bool.not_true, Bool.false_eq_true, ite_true, ite_false]
  · trivial
  rw [isQueryBoundP_query_bind_iff]
  refine ⟨by simp [IsSealing], fun reserved => ?_⟩
  cases reserved <;> simp only [Bool.not_false, Bool.not_true, Bool.false_eq_true, ite_true, ite_false]
  · trivial
  cases initial <;> simp only [PqxdhInitialGenericBuilder.continueRust]
  case ok entry =>
    split
    · trivial
    · split
      · rw [isQueryBoundP_query_bind_iff]
        refine ⟨by simp [IsSealing], fun allocated => ?_⟩
        cases allocated <;> simp only [Bool.not_false, Bool.not_true, Bool.false_eq_true, ite_true, ite_false]
        · trivial
        cases candidate.key_id_binding
        case ok binding =>
          rw [isQueryBoundP_map_iff]
          exact after_bound source rest candidate _ entry metadata state
        all_goals trivial
      · trivial
  all_goals trivial

/-- The complete original allocation, pending-token Server-binding and peer-availability gates cannot add a second sealing request. -/
theorem build_bound (source : FixedHkdfSha512NoSaltSource) (rest : Residual)
    (initial : RustM Kernel) (pending : pqxdh.PendingServerRegistration) (data : Option Pqxdh.Bytes)
    (metadata : PeerMetadata) (state : State Kernel Metadata PeerMetadata Consumed) :
    (PqxdhServerAuthSendFactor.genericBuild
      (PqxdhServerAuthCtxBuildSettlement.calls (fun entry _ _ => pure (entry, .None)) source rest sealQuery)
      auxQuery initial pending data metadata state).IsQueryBoundP IsSealing 1 := by
  unfold PqxdhServerAuthSendFactor.genericBuild
  cases pqxdh.server_next_key_id state.control <;> simp only [PqxdhInitialGenericBuilder.continueRust]
  case ok next =>
    cases next with
    | Err => trivial
    | Ok key =>
      cases hprepared : pqxdh.server_prepare_commit state.control pending
          ⟨state.server.identity, state.identityKeyId⟩
          (if (state.server.peers key).isSome then .Occupied else .Available) <;>
        simp only [hprepared]
      case ok value =>
        cases value with
        | Err => trivial
        | Ok candidate => exact candidate_bound source rest initial candidate data metadata state
      all_goals trivial
  all_goals trivial

/-- The concrete service program reaches at most one seal attempt, independently of the final native result and publication. -/
theorem program_bound (source : FixedHkdfSha512NoSaltSource) (rest : Residual)
    (pending : pqxdh.PendingServerRegistration) (data : Option Pqxdh.Bytes)
    (metadata : PeerMetadata) (state : PqxdhServerRegistrationPublication.State Metadata PeerMetadata Consumed) :
    (program source rest pending data metadata state).IsQueryBoundP IsSealing 1 := by
  rw [program, isQueryBoundP_map_iff]
  exact build_bound source rest _ pending data metadata _

/-- Explicit stopping can only remove later calls. This transports a weighted budget while retaining the complete local state and each actual optional reply. -/
theorem stopping_bound {ι κ A Result : Type} {input : OracleSpec ι} {output : OracleSpec κ}
    (handler : QueryImpl input (OptionT (StateT A (OracleComp output))))
    (p : ι → Prop) (q : κ → Prop) [DecidablePred p] [DecidablePred q]
    (step : ∀ query state, ((handler query).run.run state).IsQueryBoundP q (if p query then 1 else 0))
    (work : OracleComp input Result) (bound : Nat) (bounded : work.IsQueryBoundP p bound) (state : A) :
    ((simulateQ handler work).run.run state).IsQueryBoundP q bound := by
  induction work using OracleComp.inductionOn generalizing bound state with
  | pure value => trivial
  | query_bind query continuation ih =>
    rw [isQueryBoundP_query_bind_iff] at bounded
    simp only [simulateQ_bind, simulateQ_spec_query, OptionT.run_bind, Option.elimM, StateT.run_bind]
    refine (isQueryBoundP_bind (step query state) (m := if p query then bound - 1 else bound)
      (fun result _ => ?_)).mono ?_
    · rcases result with ⟨none | value, after⟩
      · trivial
      · exact ih value _ (bounded.2 value) after
    · split_ifs with hit
      · have positive : 0 < bound := bounded.1.resolve_left (not_not.mpr hit)
        omega
      · omega

/-- The concrete optional sealer and its writer-sensitive log add at most one component call, including refused nonces and failed writers. -/
theorem sealer_bound (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (pending : PqxdhServerAuthCtxSend.Pending) (state : Log) :
    ((sealer source writer pending).run.run state).IsTotalQueryBound 1 := by
  rw [sealer_run]
  simpa only [IsTotalQueryBound, isQueryBound_map_iff] using
    RawCtxSelectedSendCompiler.sealing_queries source.crypto writer (PqxdhServerAuthCtxSend.sealing pending)

variable {Reader WireResponse : Type}
open PqxdhServerAuthExperiment (Codec Checks)

/-- Only the actual sealing service can issue a component query; original admission, allocation, erasure and response serialization callbacks are local computations. -/
theorem compiler_step (source : FixedHkdfSha512NoSaltSource) (codec : Codec Reader WireResponse)
    (checks : Checks) (query : Spec.Domain) (state : Log) :
    ((compiler source codec checks query).run.run state).IsTotalQueryBound (if IsSealing query then 1 else 0) := by
  cases query with
  | inl pending => exact sealer_bound source codec.frameWrite pending state
  | inr query =>
    cases query <;> simp [compiler, impl, PqxdhServerAuthCtxNative.aux, IsSealing,
      StateT.run_pure, IsTotalQueryBound]

/-- The entire executable builder issues at most one component request; outer stop, inner writer failure and later response failure are all included. -/
theorem compiled_bound (source : FixedHkdfSha512NoSaltSource) (codec : Codec Reader WireResponse)
    (checks : Checks) (rest : Residual) (pending : pqxdh.PendingServerRegistration)
    (data : Option Pqxdh.Bytes) (metadata : PeerMetadata)
    (state : PqxdhServerRegistrationPublication.State Metadata PeerMetadata Consumed) (log : Log) :
    ((compiled source codec checks rest pending data metadata state).run.run log).IsTotalQueryBound 1 := by
  exact (isQueryBoundP_true_iff _ _).1
    (stopping_bound (compiler source codec checks) IsSealing (fun _ => True)
      (fun query before => (isQueryBoundP_true_iff _ _).2 (compiler_step source codec checks query before))
      (program source rest pending data metadata state) 1 (program_bound source rest pending data metadata state) log)

/-- The actual selected sealing/compiler service contributes no raw-opening or uniform requests, even when a known byte alias is supplied. -/
theorem compiler_other (source : FixedHkdfSha512NoSaltSource) (codec : Codec Reader WireResponse)
    (checks : Checks) (query : Spec.Domain) (state : Log) :
    ((compiler source codec checks query).run.run state).IsQueryBoundP
        (AdaptiveCtxDynamicKnownBounds.TargetClass AdaptiveCtxReceive.IsRawQuery) 0 ∧
      ((compiler source codec checks query).run.run state).IsQueryBoundP
        AdaptiveCtxDynamicKnownBounds.UniformRoute 0 := by
  cases query with
  | inl pending =>
    change ((sealer source codec.frameWrite pending).run.run state).IsQueryBoundP _ 0 ∧
      ((sealer source codec.frameWrite pending).run.run state).IsQueryBoundP _ 0
    rw [sealer_run]
    simp only [isQueryBoundP_map_iff]
    exact (RawCtxSelectedSealConsumer.sealing_bills source.crypto codec.frameWrite
      (PqxdhServerAuthCtxSend.sealing pending)).2.2
  | inr query =>
    cases query <;> simp [compiler, impl, PqxdhServerAuthCtxNative.aux, StateT.run_pure]

/-- Full adaptive service interpretation preserves the zero raw-opening and uniform ledgers of this concrete builder. -/
theorem compiled_other (source : FixedHkdfSha512NoSaltSource) (codec : Codec Reader WireResponse)
    (checks : Checks) (rest : Residual) (pending : pqxdh.PendingServerRegistration)
    (data : Option Pqxdh.Bytes) (metadata : PeerMetadata)
    (state : PqxdhServerRegistrationPublication.State Metadata PeerMetadata Consumed) (log : Log) :
    ((compiled source codec checks rest pending data metadata state).run.run log).IsQueryBoundP
        (AdaptiveCtxDynamicKnownBounds.TargetClass AdaptiveCtxReceive.IsRawQuery) 0 ∧
      ((compiled source codec checks rest pending data metadata state).run.run log).IsQueryBoundP
        AdaptiveCtxDynamicKnownBounds.UniformRoute 0 := by
  constructor
  · exact stopping_bound (compiler source codec checks) (fun _ => False) _
      (fun query before => (compiler_other source codec checks query before).1)
      (program source rest pending data metadata state) 0 (by simp) log
  · exact stopping_bound (compiler source codec checks) (fun _ => False) _
      (fun query before => (compiler_other source codec checks query before).2)
      (program source rest pending data metadata state) 0 (by simp) log

/-- Explicit per-class bounds for the actual compiled builder: at most one selected seal and one forwarded hash, and zero raw-opening and uniform requests. The total component-call cap is one, so the two upper bounds do not assert two calls occur. -/
theorem compiled_bills (source : FixedHkdfSha512NoSaltSource) (codec : Codec Reader WireResponse)
    (checks : Checks) (rest : Residual) (pending : pqxdh.PendingServerRegistration)
    (data : Option Pqxdh.Bytes) (metadata : PeerMetadata)
    (state : PqxdhServerRegistrationPublication.State Metadata PeerMetadata Consumed) (log : Log) :
    ((compiled source codec checks rest pending data metadata state).run.run log).IsQueryBoundP
        (AdaptiveCtxDynamicKnownBounds.TargetClass AdaptiveCtxQueryBounds.SourceSeal) 1 ∧
      ((compiled source codec checks rest pending data metadata state).run.run log).IsQueryBoundP
        AdaptiveCtxDynamicKnownBounds.HashRoute 1 ∧
      ((compiled source codec checks rest pending data metadata state).run.run log).IsQueryBoundP
        (AdaptiveCtxDynamicKnownBounds.TargetClass AdaptiveCtxReceive.IsRawQuery) 0 ∧
      ((compiled source codec checks rest pending data metadata state).run.run log).IsQueryBoundP
        AdaptiveCtxDynamicKnownBounds.UniformRoute 0 := by
  have total := (isQueryBoundP_true_iff _ _).2
    (compiled_bound source codec checks rest pending data metadata state log)
  exact ⟨IsQueryBoundP.of_imp (fun _ _ => True.intro) total,
    IsQueryBoundP.of_imp (fun _ _ => True.intro) total,
    compiled_other source codec checks rest pending data metadata state log⟩

end BeaconcryptCore.Computational.PqxdhServerAuthBuildProgramBounds

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthBuildProgramBounds.send_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthBuildProgramBounds.send_bound
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthBuildProgramBounds.after_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthBuildProgramBounds.after_bound
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthBuildProgramBounds.candidate_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthBuildProgramBounds.candidate_bound
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthBuildProgramBounds.build_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthBuildProgramBounds.build_bound
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthBuildProgramBounds.program_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthBuildProgramBounds.program_bound
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthBuildProgramBounds.stopping_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthBuildProgramBounds.stopping_bound
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthBuildProgramBounds.sealer_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthBuildProgramBounds.sealer_bound
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthBuildProgramBounds.compiler_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthBuildProgramBounds.compiler_step
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthBuildProgramBounds.compiled_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthBuildProgramBounds.compiled_bound
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthBuildProgramBounds.compiler_other' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthBuildProgramBounds.compiler_other
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthBuildProgramBounds.compiled_other' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthBuildProgramBounds.compiled_other
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthBuildProgramBounds.compiled_bills' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthBuildProgramBounds.compiled_bills
