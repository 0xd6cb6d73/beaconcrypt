import BeaconcryptCore.Computational.PqxdhServerAuthBuildReceipt
import BeaconcryptCore.Computational.PqxdhServerAuthCtxExperiment

/-! Actual registration sealing bytes are bounded by the source overflow gate, including all failed attempts. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.refined ratchet.concrete PqxdhRefinement
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhServerAuthCtxByteBounds
open PqxdhJointKdfGame
open PqxdhServerAuthCtxCalls (Kernel Residual)
open PqxdhServerAuthBuildProgram
open PqxdhServerAuthBuildReceipt (Forbidden after_context)
open PqxdhServerRegistrationPublication (AuxSpec Response registrationWitness)
open PqxdhInitialGenericPublication (State)
variable {Metadata PeerMetadata Consumed : Type}

def Sized (context : RawCtxSourceSend.SealContext) : Prop := context.plaintext.length ≤ Usize.max

/-- Every reached complete registration plaintext passes the literal source checked-addition gate before sealing, independently of the optional replies. -/
theorem candidate_bounded (source : FixedHkdfSha512NoSaltSource) (rest : Residual)
    (initial : RustM Kernel) (candidate : pqxdh.ServerRegistrationCandidate) (data : Option Pqxdh.Bytes)
    (metadata : PeerMetadata) (state : State Kernel Metadata PeerMetadata Consumed) :
    (PqxdhInitialGenericBuilder.candidate
      (PqxdhServerAuthCtxBuildSettlement.calls (fun entry _ _ => pure (entry, .None)) source rest sealQuery)
      auxQuery initial candidate data metadata state).IsQueryBoundP (Forbidden Sized) 0 := by
  unfold PqxdhInitialGenericBuilder.candidate
  simp only [auxQuery, isQueryBoundP_query_bind_iff]
  refine ⟨by simp [Forbidden], fun valid => ?_⟩
  cases valid <;> simp only [Bool.not_false, Bool.not_true, Bool.false_eq_true, ite_true, ite_false]
  · trivial
  rw [isQueryBoundP_query_bind_iff]
  refine ⟨by simp [Forbidden], fun reserved => ?_⟩
  cases reserved <;> simp only [Bool.not_false, Bool.not_true, Bool.false_eq_true, ite_true, ite_false]
  · trivial
  cases initial <;> simp only [PqxdhInitialGenericBuilder.continueRust]
  case ok entry =>
    split
    · trivial
    · split
      · rw [isQueryBoundP_query_bind_iff]
        refine ⟨by simp [Forbidden], fun allocated => ?_⟩
        cases allocated <;> simp only [Bool.not_false, Bool.not_true, Bool.false_eq_true, ite_true, ite_false]
        · trivial
        cases binding : candidate.key_id_binding
        case ok bytes =>
          rw [isQueryBoundP_map_iff]
          simpa [Forbidden] using
            after_context source rest candidate _ entry metadata state Sized (by
              obtain ⟨actual, actualEq, actualBytes⟩ := PqxdhServerRegistrationPublication.candidate_binding candidate
              have same : actual = bytes := RustM.ok.inj (actualEq.symm.trans binding)
              subst actual
              change (absBytes bytes.bytes ++ data.getD registrationWitness).length ≤ Usize.max
              rwa [List.length_append, actualBytes, Pqxdh.LE64_length])
        all_goals trivial
      · trivial
  all_goals trivial

/-- The complete next-ID, pending-token binding and peer-availability gates preserve the actual plaintext-size bound. -/
theorem build_bounded (source : FixedHkdfSha512NoSaltSource) (rest : Residual)
    (initial : RustM Kernel) (pending : pqxdh.PendingServerRegistration) (data : Option Pqxdh.Bytes)
    (metadata : PeerMetadata) (state : State Kernel Metadata PeerMetadata Consumed) :
    (PqxdhServerAuthSendFactor.genericBuild
      (PqxdhServerAuthCtxBuildSettlement.calls (fun entry _ _ => pure (entry, .None)) source rest sealQuery)
      auxQuery initial pending data metadata state).IsQueryBoundP (Forbidden Sized) 0 := by
  unfold PqxdhServerAuthSendFactor.genericBuild
  cases pqxdh.server_next_key_id state.control <;> simp only [PqxdhInitialGenericBuilder.continueRust]
  case ok next =>
    cases next with
    | Err => trivial
    | Ok key =>
      cases prepared : pqxdh.server_prepare_commit state.control pending
          ⟨state.server.identity, state.identityKeyId⟩
          (if (state.server.peers key).isSome then .Occupied else .Available) <;>
        simp only [prepared]
      case ok value =>
        cases value with
        | Err => trivial
        | Ok candidate => exact candidate_bounded source rest initial candidate data metadata state
      all_goals trivial
  all_goals trivial

/-- The concrete builder issues no sealing request above the source's plaintext-size limit. This is a syntactic all-reply property, with no success or selected-key premise. -/
theorem program_bounded (source : FixedHkdfSha512NoSaltSource) (rest : Residual)
    (pending : pqxdh.PendingServerRegistration) (data : Option Pqxdh.Bytes)
    (metadata : PeerMetadata) (state : PqxdhServerRegistrationPublication.State Metadata PeerMetadata Consumed) :
    (program source rest pending data metadata state).IsQueryBoundP (Forbidden Sized) 0 := by
  rw [program, isQueryBoundP_map_iff]
  exact build_bounded source rest _ pending data metadata _

open AdaptiveCtxDynamicKnownBounds (PlaintextCost PlaintextBound TargetClass)

def Oversized (query : AdaptiveCtxDynamicKnownKeys.Spec.Domain) : Prop := Usize.max < PlaintextCost query

instance : DecidablePred Oversized := fun query => inferInstanceAs (Decidable (Usize.max < PlaintextCost query))

/-- A forbidden oversized request must be an actual selected sealing attempt. -/
theorem oversized_seal (query : AdaptiveCtxDynamicKnownKeys.Spec.Domain) (large : Oversized query) :
    TargetClass AdaptiveCtxQueryBounds.SourceSeal query := by
  rcases query with (((coin | hash | input) | raw) | known)
  all_goals simp_all [Oversized, PlaintextCost, AdaptiveCtxPlaintextQueryBounds.SourcePlaintextCost,
    TargetClass, AdaptiveCtxQueryBounds.SourceSeal]

/-- A component program with no selected sealing requests has no oversized request. -/
theorem no_seal {Result : Type} (work : OracleComp AdaptiveCtxDynamicKnownKeys.Spec Result)
    (bounded : work.IsQueryBoundP (TargetClass AdaptiveCtxQueryBounds.SourceSeal) 0) :
    work.IsQueryBoundP Oversized 0 := IsQueryBoundP.of_imp oversized_seal bounded


/-- A reached source-sized sealing callback forwards precisely that bounded plaintext; known material contributes no target seal. -/
theorem sealer_bounded (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (pending : PqxdhServerAuthCtxSend.Pending) (sized : Sized pending.context) (before : Log) :
    ((sealer source writer pending).run.run before).IsQueryBoundP Oversized 0 := by
  rw [sealer_run]
  simp only [isQueryBoundP_map_iff, RawCtxSelectedSealConsumer.sealing]
  let input := RawCtxInterpretedArguments.sealArguments (PqxdhServerAuthCtxSend.sealing pending)
  change (RawCtxSelectedSealConsumer.call source.crypto writer input).IsQueryBoundP Oversized 0
  cases material : input.material with
  | known value =>
      exact no_seal _ (by simpa only [material] using RawCtxSelectedSealConsumer.call_seal source.crypto writer input)
  | hidden nonce =>
      simp only [RawCtxSelectedSealConsumer.call, material]
      apply RawCtxSelectedSealConsumer.lifted_bound
      unfold RawCtxSelectedMessageSealing.selected
      split
      · simp only [bind_pure_comp, isQueryBoundP_map_iff, isQueryBoundP_query_iff]
        simp only [Oversized, PlaintextCost, AdaptiveCtxPlaintextQueryBounds.SourcePlaintextCost,
          RawCtxSelectedMessageSealing.selectedInput]
        intro large
        exact (Nat.not_lt_of_ge sized large).elim
      · trivial


variable {Reader WireResponse : Type}
open PqxdhServerAuthExperiment (Codec Checks)

/-- The compiler can forward an oversized request only if the original source sealer's context itself violates the checked size gate. -/
theorem compiler_bounded (source : FixedHkdfSha512NoSaltSource) (codec : Codec Reader WireResponse)
    (checks : Checks) (query : Spec.Domain) (state : Log) :
    ((compiler source codec checks query).run.run state).IsQueryBoundP Oversized
      (if Forbidden Sized query then 1 else 0) := by
  classical
  cases query with
  | inl pending =>
      by_cases sized : Sized pending.context
      · simpa only [compiler, impl, Forbidden, sized, not_true_eq_false, ite_false] using
          sealer_bounded source codec.frameWrite pending sized state
      · simp only [Forbidden, sized, not_false_eq_true, ite_true]
        exact (PqxdhServerAuthBuildProgramBounds.sealer_bound source codec.frameWrite pending state).isQueryBoundP
          |> IsQueryBoundP.of_imp (fun _ _ => True.intro)
  | inr query =>
      cases query <;> simp [compiler, impl, PqxdhServerAuthCtxNative.aux, Forbidden, StateT.run_pure]

/-- The full executable registration builder, including every optional refusal or writer failure, forwards no oversized selected plaintext. -/
theorem compiled_bounded (source : FixedHkdfSha512NoSaltSource) (codec : Codec Reader WireResponse)
    (checks : Checks) (rest : Residual) (pending : pqxdh.PendingServerRegistration)
    (data : Option Pqxdh.Bytes) (metadata : PeerMetadata)
    (state : PqxdhServerRegistrationPublication.State Metadata PeerMetadata Consumed) (log : Log) :
    ((compiled source codec checks rest pending data metadata state).run.run log).IsQueryBoundP Oversized 0 := by
  exact PqxdhServerAuthBuildProgramBounds.stopping_bound (compiler source codec checks) (Forbidden Sized) Oversized
    (compiler_bounded source codec checks) (program source rest pending data metadata state) 0
    (program_bounded source rest pending data metadata state) log


variable {KemSK : Type}
open PqxdhServerAuthCtxState (Local)

/-- Actual pending-token and marked/ordinary dispatch retain the source plaintext limit; ordinary local encryption adds no selected plaintext. -/
theorem build_route_bounded (source : FixedHkdfSha512NoSaltSource) (codec : Codec Reader WireResponse)
    (checks : Checks) (rest : Residual) (session : Nat) (payload : Option Pqxdh.Bytes)
    (state : Local KemSK) :
    ((PqxdhServerAuthCtxBuild.build source codec checks rest session payload).run.run state).IsQueryBoundP Oversized 0 := by
  simpa only [ite_self, Nat.zero_mul] using
    PqxdhServerAuthCtxBuildBounds.build_query_bound source codec checks rest session payload Oversized 0 0
      (fun token server state => by
        simpa only [PqxdhServerAuthCtxBuild.selected, PqxdhServerAuthCtxBuild.after,
          OptionT.run_mk, StateT.run, isQueryBoundP_map_iff] using
          compiled_bounded source codec checks rest token.pending payload () server [])
      (fun token server state => no_seal _
        (PqxdhServerAuthCtxBuildBounds.known_bills source codec checks session token payload server state).2.2.1)
      state


open PqxdhServerAuthExperiment PqxdhServerAuthEntryFactor
variable {ι : Type} {baseSpec : OracleSpec ι}

/-- Every original API route either uses the checked registration builder or issues no selected sealing request. -/
theorem route_bounded (setup : Setup baseSpec KemSK) (codec : Codec Reader WireResponse)
    (checks : Checks) (context : Context KemSK) (rest : Residual) (select : Bool)
    (query : ServerAuthSpec.Domain) (state : Local KemSK) :
    ((PqxdhServerAuthCtxHandler.route setup codec checks context rest select query).run.run state).IsQueryBoundP Oversized 0 := by
  have bill := (PqxdhServerAuthCtxHandlerBounds.route_record_bills setup codec checks context rest select query state).1
  cases query with
  | inl coin =>
      apply no_seal
      simpa only [PqxdhServerAuthCtxStop.buildBill] using bill
  | inr query =>
      cases query
      case build session payload => exact build_route_bounded setup.source codec checks rest session payload state
      all_goals
        apply no_seal
        simpa only [PqxdhServerAuthCtxStop.buildBill] using bill

/-- The actual full handler's source settlement adds no oversized request. -/
theorem handler_bounded (setup : Setup baseSpec KemSK) (codec : Codec Reader WireResponse)
    (checks : Checks) (context : Context KemSK) (rest : Residual) (Q : Nat) (j : Fin (Q + 1))
    (query : ServerAuthSpec.Domain) (state : Local KemSK) :
    ((PqxdhServerAuthCtxHandler.handler setup codec checks context rest Q j query).run.run state).IsQueryBoundP Oversized 0 := by
  simpa only [PqxdhServerAuthCtxHandler.handler, OptionT.run_mk, StateT.run, isQueryBoundP_map_iff] using
    route_bounded setup codec checks context rest (!state.2 && hiddenDesignated Q j query state.1) query state


/-- Optional stopping preserves the byte gate along every adaptive reply path and complete local state. -/
theorem stopped_bounded {Result : Type} (setup : Setup baseSpec KemSK) (codec : Codec Reader WireResponse)
    (checks : Checks) (context : Context KemSK) (rest : Residual) (Q : Nat) (j : Fin (Q + 1))
    (work : OracleComp ServerAuthSpec Result) (state : Local KemSK × Option Nat) :
    ((simulateQ (PqxdhServerAuthCtxReserve.stopped
      (PqxdhServerAuthCtxHandler.handler setup codec checks context rest Q j)) work).run.run state).IsQueryBoundP Oversized 0 := by
  apply PqxdhServerAuthBuildProgramBounds.stopping_bound _ (fun _ => False) Oversized _ work 0
    (isQueryBoundP_false work 0) state
  intro query before
  change ((PqxdhServerAuthCtxReserve.stopped
    (PqxdhServerAuthCtxHandler.handler setup codec checks context rest Q j) query).run before).IsQueryBoundP Oversized 0
  rw [PqxdhServerAuthCtxReserve.stopped, PqxdhServerAuthCtxStop.stopped_step, isQueryBoundP_map_iff]
  exact handler_bounded setup codec checks context rest Q j query before.1

/-- The literal full context/residual client has no oversized selected query, without a caller-supplied plaintext-size bound. -/
theorem client_bounded (setup : Setup baseSpec KemSK) (codec : Codec Reader WireResponse)
    (checks : Checks) (adversary : Adversary) (Q : Nat) (j : Fin (Q + 1)) :
    (PqxdhServerAuthCtxExperiment.client setup codec checks adversary Q j).IsQueryBoundP Oversized 0 := by
  unfold PqxdhServerAuthCtxExperiment.client
  apply (isQueryBoundP_bind (no_seal _ (PqxdhServerAuthCtxAmbient.coin_other _).2.1) (m := 0)
    (fun context _ => ?_)).mono (by omega)
  apply (isQueryBoundP_bind (no_seal _ (PqxdhServerAuthCtxAmbient.coin_other _).2.1) (m := 0)
    (fun rest _ => ?_)).mono (by omega)
  simpa only [PqxdhServerAuthCtxExperiment.continuation, PqxdhServerAuthCtxExperiment.execution,
    isQueryBoundP_map_iff] using stopped_bounded setup codec checks context rest Q j
      (adversary (contextInput setup false context)) (PqxdhServerAuthCtxReserve.initial setup context).1


/-- No other component query submits plaintext to the selected encryption challenger. -/
theorem cost_nonseal (query : AdaptiveCtxDynamicKnownKeys.Spec.Domain)
    (notSeal : ¬ TargetClass AdaptiveCtxQueryBounds.SourceSeal query) : PlaintextCost query = 0 := by
  rcases query with (((coin | hash | input) | raw) | known)
  all_goals simp_all [PlaintextCost, AdaptiveCtxPlaintextQueryBounds.SourcePlaintextCost,
    TargetClass, AdaptiveCtxQueryBounds.SourceSeal]

/-- A syntactic sealing cap and the exact per-request source size gate bound total submitted bytes on every adaptive continuation. -/
theorem weighted {Result : Type} (work : OracleComp AdaptiveCtxDynamicKnownKeys.Spec Result)
    (count bytes : Nat)
    (counted : work.IsQueryBoundP (TargetClass AdaptiveCtxQueryBounds.SourceSeal) count)
    (sized : work.IsQueryBoundP Oversized 0) (enough : count * Usize.max ≤ bytes) :
    PlaintextBound work bytes := by
  induction work using OracleComp.inductionOn generalizing count bytes with
  | pure value => trivial
  | query_bind query next ih =>
      rw [isQueryBoundP_query_bind_iff] at counted sized
      rw [PlaintextBound, isQueryBound_query_bind_iff]
      have small : PlaintextCost query ≤ Usize.max := by simpa [Oversized] using sized.1
      by_cases isSeal : TargetClass AdaptiveCtxQueryBounds.SourceSeal query
      · have positive : 0 < count := counted.1.resolve_left (not_not.mpr isSeal)
        have splitCount : count * Usize.max = (count - 1) * Usize.max + Usize.max := by
          calc
            count * Usize.max = ((count - 1) + 1) * Usize.max := congrArg (fun n => n * Usize.max) (by omega)
            _ = (count - 1) * Usize.max + Usize.max := by rw [Nat.add_mul, Nat.one_mul]
        refine ⟨by omega, fun reply => ?_⟩
        apply ih reply (count - 1) (bytes - PlaintextCost query)
          (by simpa only [isSeal, ite_true] using counted.2 reply)
          (by simpa only [Nat.zero_sub, ite_self] using sized.2 reply)
        omega
      · have zero := cost_nonseal query isSeal
        refine ⟨by simp [zero], fun reply => ?_⟩
        apply ih reply count (bytes - PlaintextCost query)
          (by simpa only [isSeal, ite_false] using counted.2 reply)
          (by simpa only [Nat.zero_sub, ite_self] using sized.2 reply)
        simpa only [zero, Nat.sub_zero] using enough

/-- The complete original client submits at most Usize.max selected plaintext bytes, from its actual checked builder and proved one-seal control; no caller byte budget is required. -/
theorem client_plaintext (setup : Setup baseSpec KemSK) (codec : Codec Reader WireResponse)
    (checks : Checks) (adversary : Adversary) (Q : Nat) (j : Fin (Q + 1)) :
    PlaintextBound (PqxdhServerAuthCtxExperiment.client setup codec checks adversary Q j) Usize.max := by
  exact weighted _ 1 Usize.max
    (PqxdhServerAuthCtxExperiment.client_record_bills setup codec checks adversary Q j).1
    (client_bounded setup codec checks adversary Q j) (by simp)

end BeaconcryptCore.Computational.PqxdhServerAuthCtxByteBounds

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxByteBounds.candidate_bounded' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxByteBounds.candidate_bounded
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxByteBounds.build_bounded' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxByteBounds.build_bounded
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxByteBounds.program_bounded' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxByteBounds.program_bounded
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxByteBounds.oversized_seal' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxByteBounds.oversized_seal
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxByteBounds.no_seal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxByteBounds.no_seal
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxByteBounds.sealer_bounded' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxByteBounds.sealer_bounded
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxByteBounds.compiler_bounded' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxByteBounds.compiler_bounded
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxByteBounds.compiled_bounded' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxByteBounds.compiled_bounded
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxByteBounds.build_route_bounded' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxByteBounds.build_route_bounded
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxByteBounds.route_bounded' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxByteBounds.route_bounded
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxByteBounds.handler_bounded' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxByteBounds.handler_bounded
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxByteBounds.stopped_bounded' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxByteBounds.stopped_bounded
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxByteBounds.client_bounded' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxByteBounds.client_bounded
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxByteBounds.cost_nonseal' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxByteBounds.cost_nonseal
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxByteBounds.weighted' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxByteBounds.weighted
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxByteBounds.client_plaintext' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxByteBounds.client_plaintext
