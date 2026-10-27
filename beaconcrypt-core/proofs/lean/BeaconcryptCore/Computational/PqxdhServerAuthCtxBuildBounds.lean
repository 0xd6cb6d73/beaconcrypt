import VCVio.OracleComp.QueryTracking.QueryBound.Partition
import BeaconcryptCore.Computational.PqxdhServerAuthCtxBuild
import BeaconcryptCore.Computational.PqxdhServerAuthEntryResourceHandlers

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhServerAuthCtxBuildBounds
open PqxdhServerAuthExperiment PqxdhServerAuthEntryFactor PqxdhServerAuthCtxState
open PqxdhServerAuthCtxBuild PqxdhServerAuthSourceCosts PqxdhServerAuthGapDh
open PqxdhSecretInputKdf PqxdhJointKdfGame PqxdhServerAuthPendingBudget
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader WireResponse : Type}

/-- The reached selected builder retains its complete one-call ledger through native settlement, optional response failure and outer component refusal. -/
theorem selected_bills (source : FixedHkdfSha512NoSaltSource) (codec : Codec Reader WireResponse)
    (checks : Checks) (rest : PqxdhServerAuthCtxCalls.Residual) (session : Nat)
    (token : PqxdhServerRelatedRootConsumer.Returned) (payload : Option Pqxdh.Bytes)
    (server : ServerState) (state : Local KemSK) :
    ((selected source codec checks rest session token payload server).run.run state).IsTotalQueryBound 1 ∧
    ((selected source codec checks rest session token payload server).run.run state).IsQueryBoundP
      (AdaptiveCtxDynamicKnownBounds.TargetClass AdaptiveCtxQueryBounds.SourceSeal) 1 ∧
    ((selected source codec checks rest session token payload server).run.run state).IsQueryBoundP AdaptiveCtxDynamicKnownBounds.HashRoute 1 ∧
    ((selected source codec checks rest session token payload server).run.run state).IsQueryBoundP
      (AdaptiveCtxDynamicKnownBounds.TargetClass AdaptiveCtxReceive.IsRawQuery) 0 ∧
    ((selected source codec checks rest session token payload server).run.run state).IsQueryBoundP AdaptiveCtxDynamicKnownBounds.UniformRoute 0 := by
  simpa only [selected, after, OptionT.run_mk, StateT.run, IsTotalQueryBound,
    isQueryBound_map_iff, isQueryBoundP_map_iff] using
    And.intro (PqxdhServerAuthBuildProgramBounds.compiled_bound source codec checks rest token.pending payload () server [])
      (PqxdhServerAuthBuildProgramBounds.compiled_bills source codec checks rest token.pending payload () server [])

/-- The actual ordinary builder forwards only its single attempted shared hash. Local KDF, AEAD, validation and writers remain in the original program. -/
theorem known_bills (source : FixedHkdfSha512NoSaltSource) (codec : Codec Reader WireResponse)
    (checks : Checks) (session : Nat) (token : PqxdhServerRelatedRootConsumer.Returned)
    (payload : Option Pqxdh.Bytes) (server : ServerState) (state : Local KemSK) :
    ((known source codec checks session token payload server).run.run state).IsTotalQueryBound 1 ∧
    ((known source codec checks session token payload server).run.run state).IsQueryBoundP AdaptiveCtxDynamicKnownBounds.HashRoute 1 ∧
    ((known source codec checks session token payload server).run.run state).IsQueryBoundP
      (AdaptiveCtxDynamicKnownBounds.TargetClass AdaptiveCtxQueryBounds.SourceSeal) 0 ∧
    ((known source codec checks session token payload server).run.run state).IsQueryBoundP
      (AdaptiveCtxDynamicKnownBounds.TargetClass AdaptiveCtxReceive.IsRawQuery) 0 ∧
    ((known source codec checks session token payload server).run.run state).IsQueryBoundP AdaptiveCtxDynamicKnownBounds.UniformRoute 0 := by
  have hash : ((known source codec checks session token payload server).run.run state).IsQueryBoundP
      AdaptiveCtxDynamicKnownBounds.HashRoute 1 := by
    simpa only [known, after, OptionT.run_mk, StateT.run, isQueryBoundP_map_iff] using
      PqxdhServerAuthCtxNativeBounds.build_hash source codec checks token.pending token.root payload server []
  have onlyHash : ((known source codec checks session token payload server).run.run state).IsQueryBoundP
      (fun query => ¬ AdaptiveCtxDynamicKnownBounds.HashRoute query) 0 := by
    simpa only [known, after, OptionT.run_mk, StateT.run, isQueryBoundP_map_iff] using
      PqxdhServerAuthCtxNativeBounds.build_only_hash source codec checks token.pending token.root payload server []
  refine ⟨?_, hash, PqxdhServerAuthCtxNativeBounds.only_hash_other _ onlyHash⟩
  simpa only [Nat.add_zero] using isTotalQueryBound_of_partition _
    AdaptiveCtxDynamicKnownBounds.HashRoute (fun query => ¬ AdaptiveCtxDynamicKnownBounds.HashRoute query)
    (fun _ => Iff.rfl) 1 0 hash onlyHash

/-- Actual pending-token lookup and the session mark select the entire concrete callback bill, retaining work before optional refusal. -/
theorem build_query_bound (source : FixedHkdfSha512NoSaltSource) (codec : Codec Reader WireResponse)
    (checks : Checks) (rest : PqxdhServerAuthCtxCalls.Residual) (session : Nat)
    (payload : Option Pqxdh.Bytes) (predicate : AdaptiveCtxDynamicKnownKeys.Spec.Domain → Prop)
    [DecidablePred predicate] (selectedBill knownBill : Nat)
    (selectedBound : ∀ token server (state : Local KemSK),
      ((selected source codec checks rest session token payload server).run.run state).IsQueryBoundP predicate selectedBill)
    (knownBound : ∀ token server (state : Local KemSK),
      ((known source codec checks session token payload server).run.run state).IsQueryBoundP predicate knownBill)
    (state : Local KemSK) :
    ((build source codec checks rest session payload).run.run state).IsQueryBoundP predicate
      ((if state.1.2.1 session then selectedBill else knownBill) * slotWeight (state.1.1.pending session)) := by
  simp only [build, OptionT.run_mk, StateT.run]
  cases found : state.1.1.pending session with
  | none => trivial
  | some token =>
      simp only [slotWeight, Nat.mul_one]
      split_ifs
      · exact selectedBound token _ state
      · exact knownBound token _ state

/-- The original marked pending token pays the only possible selected seal; all builds retain their exact hash and zero raw/uniform component classes. -/
theorem build_bills (source : FixedHkdfSha512NoSaltSource) (codec : Codec Reader WireResponse)
    (checks : Checks) (rest : PqxdhServerAuthCtxCalls.Residual) (session : Nat)
    (payload : Option Pqxdh.Bytes) (state : Local KemSK) :
    ((build source codec checks rest session payload).run.run state).IsTotalQueryBound (slotWeight (state.1.1.pending session)) ∧
    ((build source codec checks rest session payload).run.run state).IsQueryBoundP
      (AdaptiveCtxDynamicKnownBounds.TargetClass AdaptiveCtxQueryBounds.SourceSeal)
      (if state.1.2.1 session then slotWeight (state.1.1.pending session) else 0) ∧
    ((build source codec checks rest session payload).run.run state).IsQueryBoundP AdaptiveCtxDynamicKnownBounds.HashRoute
      (slotWeight (state.1.1.pending session)) ∧
    ((build source codec checks rest session payload).run.run state).IsQueryBoundP
      (AdaptiveCtxDynamicKnownBounds.TargetClass AdaptiveCtxReceive.IsRawQuery) 0 ∧
    ((build source codec checks rest session payload).run.run state).IsQueryBoundP AdaptiveCtxDynamicKnownBounds.UniformRoute 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · apply (isQueryBoundP_true_iff _ _).1
    simpa only [ite_self, Nat.one_mul] using build_query_bound source codec checks rest session payload
      (fun _ => True) 1 1
      (fun token server state => (isQueryBoundP_true_iff _ _).2 (selected_bills source codec checks rest session token payload server state).1)
      (fun token server state => (isQueryBoundP_true_iff _ _).2 (known_bills source codec checks session token payload server state).1) state
  · simpa only [ite_mul, Nat.one_mul, Nat.zero_mul] using build_query_bound source codec checks rest session payload
      (AdaptiveCtxDynamicKnownBounds.TargetClass AdaptiveCtxQueryBounds.SourceSeal) 1 0
      (fun token server state => (selected_bills source codec checks rest session token payload server state).2.1)
      (fun token server state => (known_bills source codec checks session token payload server state).2.2.1) state
  · simpa only [ite_self, Nat.one_mul] using build_query_bound source codec checks rest session payload
      AdaptiveCtxDynamicKnownBounds.HashRoute 1 1
      (fun token server state => (selected_bills source codec checks rest session token payload server state).2.2.1)
      (fun token server state => (known_bills source codec checks session token payload server state).2.1) state
  · simpa only [ite_self, Nat.zero_mul] using build_query_bound source codec checks rest session payload
      (AdaptiveCtxDynamicKnownBounds.TargetClass AdaptiveCtxReceive.IsRawQuery) 0 0
      (fun token server state => (selected_bills source codec checks rest session token payload server state).2.2.2.1)
      (fun token server state => (known_bills source codec checks session token payload server state).2.2.2.1) state
  · simpa only [ite_self, Nat.zero_mul] using build_query_bound source codec checks rest session payload
      AdaptiveCtxDynamicKnownBounds.UniformRoute 0 0
      (fun token server state => (selected_bills source codec checks rest session token payload server state).2.2.2.2)
      (fun token server state => (known_bills source codec checks session token payload server state).2.2.2.2) state

/-- Literal native settlement consumes the reached pending token and preserves all allocation, Beacon, mark and designation fields. -/
theorem complete_footprint (session : Nat) (payload : Option Pqxdh.Bytes) (state : Local KemSK)
    (outcome : Outcome) (log : Log) :
    ResourceStep (.inr (.build session payload)) state.1.1 (complete session state outcome log).2.1.1 ∧
      (complete session state outcome log).2.1.2.1 = state.1.2.1 ∧
      (complete session state outcome log).2.2 = state.2 := by
  exact ⟨⟨rfl, rfl, rfl⟩, rfl, rfl⟩

/-- Optional component refusal does not masquerade as token consumption. Every normal result has the actual source resource footprint, and both routes preserve marks and designation. -/
theorem post_footprint (session : Nat) (payload : Option Pqxdh.Bytes) (state : Local KemSK)
    (result : Option Outcome × Log) :
    ((post session state result).1.isSome →
      ResourceStep (.inr (.build session payload)) state.1.1 (post session state result).2.1.1) ∧
      (post session state result).2.1.2.1 = state.1.2.1 ∧
      (post session state result).2.2 = state.2 := by
  rcases result with ⟨_ | outcome, log⟩
  · exact ⟨by simp only [post, Option.isSome_none, Bool.false_eq_true, false_implies], rfl, rfl⟩
  · exact ⟨fun _ => (complete_footprint session payload state outcome log).1,
      (complete_footprint session payload state outcome log).2⟩

/-- Complete callback execution preserves the source footprint on normal output for every syntactically possible component reply; refusal keeps marks and designation unchanged. -/
theorem after_footprint (session : Nat) (payload : Option Pqxdh.Bytes)
    (work : OracleComp AdaptiveCtxDynamicKnownKeys.Spec (Option Outcome × Log))
    (state : Local KemSK) (result : Option (Option PqxdhServerRegistrationPublication.Response) × Local KemSK)
    (supported : result ∈ support ((after session work).run.run state)) :
    (result.1.isSome → ResourceStep (.inr (.build session payload)) state.1.1 result.2.1.1) ∧
      result.2.1.2.1 = state.1.2.1 ∧ result.2.2 = state.2 := by
  simp only [after, OptionT.run_mk, StateT.run, support_map, Set.mem_image] at supported
  obtain ⟨output, _, rfl⟩ := supported
  exact post_footprint session payload state output

/-- Actual pending-token dispatch supplies the resource and mark footprints for every dynamic reply, including optional component refusal and native writer failure. -/
theorem build_footprint (source : FixedHkdfSha512NoSaltSource) (codec : Codec Reader WireResponse)
    (checks : Checks) (rest : PqxdhServerAuthCtxCalls.Residual) (session : Nat)
    (payload : Option Pqxdh.Bytes) (state : Local KemSK)
    (result : Option (Option PqxdhServerRegistrationPublication.Response) × Local KemSK)
    (supported : result ∈ support ((build source codec checks rest session payload).run.run state)) :
    (result.1.isSome → ResourceStep (.inr (.build session payload)) state.1.1 result.2.1.1) ∧
      result.2.1.2.1 = state.1.2.1 ∧ result.2.2 = state.2 := by
  simp only [build, OptionT.run_mk, StateT.run] at supported
  cases found : state.1.1.pending session with
  | none =>
      simp only [found, support_pure, Set.mem_singleton_iff] at supported
      subst supported
      exact ⟨fun _ => ⟨rfl, rfl, by rw [← found, Function.update_eq_self]⟩, rfl, rfl⟩
  | some token =>
      simp only [found] at supported
      split_ifs at supported
      · exact after_footprint session payload _ state result supported
      · exact after_footprint session payload _ state result supported

/-- The full interpreted source bill retains the shared commitment sampling. The unused-endpoint condition is precisely the existing operational source-comparison condition, needed only for a reached marked token. -/
theorem build_evaluated_uniform (setup : Setup baseSpec KemSK) (codec : Codec Reader WireResponse)
    (checks : Checks) (context : Context KemSK) (rest : PqxdhServerAuthCtxCalls.Residual)
    (session : Nat) (payload : Option Pqxdh.Bytes) (key : RootOutput) (state : State KemSK)
    (empty : state.1.1.2.1 session = true → (state.1.1.1.pending session).isSome →
      state.2.selected.1.usedNonces = []) :
    ((evaluate setup.source key codec.frameRead
      (build setup.source codec checks rest session payload).run).run state).IsTotalQueryBound
      (64 * slotWeight (state.1.1.1.pending session)) := by
  have bill := build_step_uniform setup codec checks
    (factorServices setup codec checks context (PqxdhServerAuthCtxMaterial.output key rest))
    (factor_services_uniform setup codec checks context _) session payload
    (PqxdhServerAuthCtxState.project state).1
  have same := build_source setup codec checks context rest session payload key state empty
  have mapped : (Prod.map id PqxdhServerAuthCtxState.project <$>
      (evaluate setup.source key codec.frameRead
        (build setup.source codec checks rest session payload).run).run state).IsTotalQueryBound
          (64 * slotWeight (state.1.1.1.pending session)) := by
    rw [same]
    simpa only [IsTotalQueryBound, isQueryBound_map_iff, PqxdhServerAuthCtxState.project,
      restore, restoreFlat] using bill
  simpa only [IsTotalQueryBound, isQueryBound_map_iff] using mapped

end BeaconcryptCore.Computational.PqxdhServerAuthCtxBuildBounds

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxBuildBounds.selected_bills' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxBuildBounds.selected_bills
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxBuildBounds.known_bills' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxBuildBounds.known_bills
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxBuildBounds.build_query_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxBuildBounds.build_query_bound
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxBuildBounds.build_bills' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxBuildBounds.build_bills
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxBuildBounds.complete_footprint' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxBuildBounds.complete_footprint
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxBuildBounds.post_footprint' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxBuildBounds.post_footprint
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxBuildBounds.after_footprint' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxBuildBounds.after_footprint
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxBuildBounds.build_footprint' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxBuildBounds.build_footprint
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxBuildBounds.build_evaluated_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxBuildBounds.build_evaluated_uniform
