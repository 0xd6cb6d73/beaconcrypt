import VCVio.OracleComp.QueryTracking.QueryBound.Partition
import BeaconcryptCore.Computational.PqxdhServerAuthCtxFinish
import BeaconcryptCore.Computational.PqxdhServerAuthEntryResourceHandlers

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhServerAuthCtxFinishBounds
open PqxdhServerAuthExperiment PqxdhServerAuthEntryFactor PqxdhServerAuthCtxState
open PqxdhServerAuthCtxFinish PqxdhServerAuthSourceCosts PqxdhServerAuthGapDh
open PqxdhSecretInputKdf PqxdhJointKdfGame
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}

/-- The complete actual finish pays its real prefix, table and reached tail bills before any optional rejection. Inactive phases make no calls. -/
theorem finish_query_bound (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (context : Context KemSK) (rest : PqxdhServerAuthCtxCalls.Residual) (select : Bool) (raw : Pqxdh.Bytes)
    (predicate : AdaptiveCtxDynamicKnownKeys.Spec.Domain → Prop) [DecidablePred predicate]
    (prefixBill tableBill tailBill : Nat)
    (prefixBound : ∀ control identity oneTime kem,
      (simulateQ PqxdhServerAuthCtxAmbient.coin
        ((beaconPrefix setup codec context.beaconSeed control identity oneTime kem raw).run' ())).IsQueryBoundP predicate prefixBill)
    (table : ∀ message cache,
      (simulateQ PqxdhServerAuthCtxAmbient.coin
        (((tableServices (WireResponse := Response) setup context select).derive message).run cache)).IsQueryBoundP predicate tableBill)
    (ordinary : ∀ control pending root state,
      ((known setup.source codec control pending root).run state : OracleComp AdaptiveCtxDynamicKnownKeys.Spec
        (Option Pqxdh.Bytes × Local KemSK)).IsQueryBoundP predicate tailBill)
    (hidden : ∀ control pending state,
      ((selected setup.source codec rest control pending).run state : OracleComp AdaptiveCtxDynamicKnownKeys.Spec
        (Option Pqxdh.Bytes × Local KemSK)).IsQueryBoundP predicate tailBill)
    (state : Local KemSK) :
    ((finish setup codec context rest select raw).run state).IsQueryBoundP predicate
      ((prefixBill + tableBill + tailBill) * initSentFlag state.1.1) := by
  unfold finish
  simp only [StateT.run]
  cases phase : state.1.1.beacon.beacon.phase with
  | initSent control prekey oneTime kem =>
    simp only [initSentFlag, phase, Nat.mul_one, Nat.add_assoc]
    apply isQueryBoundP_bind (m := tableBill + tailBill) (prefixBound control _ oneTime kem)
    intro prepared _
    cases prepared with
    | none => trivial
    | some pending =>
      apply isQueryBoundP_bind (m := tailBill) (table _ _)
      intro derived _
      cases derived.1 with
      | rejected => trivial
      | root root => exact ordinary control pending root _
      | hidden => exact hidden control pending _
  | _ => trivial

/-- The ordinary complete post-root callback forwards only its one attempted hash; native optional failures and local KDF work remain present. -/
theorem known_bills (source : FixedHkdfSha512NoSaltSource) (codec : Codec Reader Response)
    (control : pqxdh.BeaconInitSent) (pending : PqxdhPhase2DhMetadata.Prepared Response)
    (root : RootOutput) (state : Local KemSK) :
    ((known source codec control pending root).run state).IsTotalQueryBound 1 ∧
      ((known source codec control pending root).run state).IsQueryBoundP AdaptiveCtxDynamicKnownBounds.HashRoute 1 ∧
      ((known source codec control pending root).run state).IsQueryBoundP
        (AdaptiveCtxDynamicKnownBounds.TargetClass AdaptiveCtxQueryBounds.SourceSeal) 0 ∧
      ((known source codec control pending root).run state).IsQueryBoundP
        (AdaptiveCtxDynamicKnownBounds.TargetClass AdaptiveCtxReceive.IsRawQuery) 0 ∧
      ((known source codec control pending root).run state).IsQueryBoundP AdaptiveCtxDynamicKnownBounds.UniformRoute 0 := by
  have hash : ((known source codec control pending root).run state).IsQueryBoundP
      AdaptiveCtxDynamicKnownBounds.HashRoute 1 := by
    simpa only [known, after, StateT.run, isQueryBoundP_map_iff] using
      PqxdhServerAuthCtxNativeBounds.beacon_after_hash source codec pending
        (PqxdhRootTableInitialization.rootArray root) ()
  have onlyHash : ((known source codec control pending root).run state).IsQueryBoundP
      (fun query => ¬ AdaptiveCtxDynamicKnownBounds.HashRoute query) 0 := by
    simpa only [known, after, StateT.run, isQueryBoundP_map_iff] using
      PqxdhServerAuthCtxNativeBounds.beacon_program_only_hash source codec
        (PqxdhPhase2DhRootConsumer.afterRoot codec.frameRead pending (PqxdhRootTableInitialization.rootArray root)) ()
  refine ⟨?_, hash, PqxdhServerAuthCtxNativeBounds.only_hash_other _ onlyHash⟩
  simpa only [Nat.add_zero] using isTotalQueryBound_of_partition _
    AdaptiveCtxDynamicKnownBounds.HashRoute (fun query => ¬ AdaptiveCtxDynamicKnownBounds.HashRoute query)
    (fun _ => Iff.rfl) 1 0 hash onlyHash

/-- The selected complete post-root callback retains every attempted raw operation and the source observation without additional queries, with local computation separately present. -/
theorem selected_bills (source : FixedHkdfSha512NoSaltSource) (codec : Codec Reader Response)
    (rest : PqxdhServerAuthCtxCalls.Residual) (control : pqxdh.BeaconInitSent)
    (pending : PqxdhPhase2DhMetadata.Prepared Response) (state : Local KemSK) :
    ((selected source codec rest control pending).run state).IsTotalQueryBound 1 ∧
      ((selected source codec rest control pending).run state).IsQueryBoundP AdaptiveCtxDynamicKnownBounds.HashRoute 1 ∧
      ((selected source codec rest control pending).run state).IsQueryBoundP
        (AdaptiveCtxDynamicKnownBounds.TargetClass AdaptiveCtxQueryBounds.SourceSeal) 0 ∧
      ((selected source codec rest control pending).run state).IsQueryBoundP
        (AdaptiveCtxDynamicKnownBounds.TargetClass AdaptiveCtxReceive.IsRawQuery) 1 ∧
      ((selected source codec rest control pending).run state).IsQueryBoundP AdaptiveCtxDynamicKnownBounds.UniformRoute 0 := by
  have bills := PqxdhServerAuthFinishMaterial.program_bills source codec rest pending
  refine ⟨?_, ?_⟩
  · simpa only [selected, after, StateT.run, IsTotalQueryBound, isQueryBound_map_iff] using
      PqxdhServerAuthFinishMaterial.program_bound source codec rest pending
  · simpa only [selected, after, StateT.run, isQueryBoundP_map_iff] using
      And.intro bills.2.1 (And.intro bills.1 bills.2.2)

/-- Every complete actual finish has at most one attempted hash/raw route exactly when the original finish phase is active, and no selected seal. Full source coin and table work is separately charged. -/
theorem finish_record_bills (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (context : Context KemSK) (rest : PqxdhServerAuthCtxCalls.Residual) (select : Bool)
    (raw : Pqxdh.Bytes) (state : Local KemSK) :
    ((finish setup codec context rest select raw).run state).IsQueryBoundP
        AdaptiveCtxDynamicKnownBounds.HashRoute (initSentFlag state.1.1) ∧
      ((finish setup codec context rest select raw).run state).IsQueryBoundP
        (AdaptiveCtxDynamicKnownBounds.TargetClass AdaptiveCtxQueryBounds.SourceSeal) 0 ∧
      ((finish setup codec context rest select raw).run state).IsQueryBoundP
        (AdaptiveCtxDynamicKnownBounds.TargetClass AdaptiveCtxReceive.IsRawQuery) (initSentFlag state.1.1) := by
  refine ⟨?_, ?_, ?_⟩
  · simpa only [Nat.zero_add, Nat.one_mul] using finish_query_bound setup codec context rest select raw
      AdaptiveCtxDynamicKnownBounds.HashRoute 0 0 1
      (fun _ _ _ _ => (PqxdhServerAuthCtxAmbient.coin_other _).1)
      (fun _ _ => (PqxdhServerAuthCtxAmbient.coin_other _).1)
      (fun control pending root state => (known_bills setup.source codec control pending root state).2.1)
      (fun control pending state => (selected_bills setup.source codec rest control pending state).2.1) state
  · simpa only [Nat.zero_add, Nat.zero_mul] using finish_query_bound setup codec context rest select raw
      (AdaptiveCtxDynamicKnownBounds.TargetClass AdaptiveCtxQueryBounds.SourceSeal) 0 0 0
      (fun _ _ _ _ => (PqxdhServerAuthCtxAmbient.coin_other _).2.1)
      (fun _ _ => (PqxdhServerAuthCtxAmbient.coin_other _).2.1)
      (fun control pending root state => (known_bills setup.source codec control pending root state).2.2.1)
      (fun control pending state => (selected_bills setup.source codec rest control pending state).2.2.1) state
  · simpa only [Nat.zero_add, Nat.one_mul] using finish_query_bound setup codec context rest select raw
      (AdaptiveCtxDynamicKnownBounds.TargetClass AdaptiveCtxReceive.IsRawQuery) 0 0 1
      (fun _ _ _ _ => (PqxdhServerAuthCtxAmbient.coin_other _).2.2)
      (fun _ _ => (PqxdhServerAuthCtxAmbient.coin_other _).2.2)
      (fun control pending root state => ((known_bills setup.source codec control pending root state).2.2.2.1).mono (by decide))
      (fun control pending state => (selected_bills setup.source codec rest control pending state).2.2.2.1) state

/-- The literal prefix forwards every direct and base-interpreted decapsulation coin; all parsing, validation and DH callback work remains in the source program. -/
theorem prefix_bound (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (context : Context KemSK) (caps : KemCaps) (bounded : KemBound setup caps)
    (control : pqxdh.BeaconInitSent) (identity : Unit) (oneTime : Unit ⊕ PqxdhJointGapDh.ScalarBytes)
    (kem : KemSK) (raw : Pqxdh.Bytes) :
    (simulateQ PqxdhServerAuthCtxAmbient.coin
      ((beaconPrefix setup codec context.beaconSeed control identity oneTime kem raw).run' ())).IsTotalQueryBound caps.decapsCost := by
  apply PqxdhServerAuthCtxAmbient.coin_bound
  simpa only [StateT.run', StateT.run, IsTotalQueryBound, isQueryBound_map_iff] using
    beacon_prefix_uniform setup codec context.beaconSeed caps bounded control identity oneTime kem raw ()

/-- Every actual unselected table miss retains its sixty-four source samples, including bad-state continuations; designation itself samples nothing. -/
theorem table_bound (setup : Setup baseSpec KemSK) (context : Context KemSK) (select : Bool)
    (message : PqxdhJointDhExtractFamily.Message) (cache : HiddenTable) :
    (simulateQ PqxdhServerAuthCtxAmbient.coin
      (((tableServices (WireResponse := Response) setup context select).derive message).run cache)).IsTotalQueryBound 64 := by
  apply PqxdhServerAuthCtxAmbient.coin_bound
  cases select with
  | false => exact hidden_derive_uniform setup.hmac setup.joint setup.dh context.seed context.scalar message cache
  | true => exact (select_hidden_uniform setup.joint setup.dh context.seed context.scalar message cache).mono (by decide)

/-- Explicit component coins pay the complete decapsulation cost plus one possible Extract-table miss. Commitment/opening interpreter coins remain separately charged by their route bounds. -/
theorem finish_uniform (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (context : Context KemSK) (rest : PqxdhServerAuthCtxCalls.Residual) (select : Bool)
    (caps : KemCaps) (bounded : KemBound setup caps) (raw : Pqxdh.Bytes) (state : Local KemSK) :
    ((finish setup codec context rest select raw).run state).IsQueryBoundP AdaptiveCtxDynamicKnownBounds.UniformRoute
      ((caps.decapsCost + 64) * initSentFlag state.1.1) := by
  simpa only [Nat.add_zero] using finish_query_bound setup codec context rest select raw
    AdaptiveCtxDynamicKnownBounds.UniformRoute caps.decapsCost 64 0
    (fun control identity oneTime kem => IsQueryBoundP.of_imp (fun _ _ => True.intro)
      ((isQueryBoundP_true_iff _ _).2 (prefix_bound setup codec context caps bounded control identity oneTime kem raw)))
    (fun message cache => IsQueryBoundP.of_imp (fun _ _ => True.intro)
      ((isQueryBoundP_true_iff _ _).2 (table_bound (Response := Response) setup context select message cache)))
    (fun control pending root state => (known_bills setup.source codec control pending root state).2.2.2.2)
    (fun control pending state => (selected_bills setup.source codec rest control pending state).2.2.2.2) state

/-- The complete dynamic finish pays every forwarded source coin and its one possible component receive/hash call. No prefix or table work is omitted on later refusal. -/
theorem finish_total (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (context : Context KemSK) (rest : PqxdhServerAuthCtxCalls.Residual) (select : Bool)
    (caps : KemCaps) (bounded : KemBound setup caps) (raw : Pqxdh.Bytes) (state : Local KemSK) :
    ((finish setup codec context rest select raw).run state).IsTotalQueryBound
      ((caps.decapsCost + 65) * initSentFlag state.1.1) := by
  apply (isQueryBoundP_true_iff _ _).1
  simpa only [Nat.add_assoc] using finish_query_bound setup codec context rest select raw
    (fun _ => True) caps.decapsCost 64 1
    (fun control identity oneTime kem => (isQueryBoundP_true_iff _ _).2
      (prefix_bound setup codec context caps bounded control identity oneTime kem raw))
    (fun message cache => (isQueryBoundP_true_iff _ _).2
      (table_bound (Response := Response) setup context select message cache))
    (fun control pending root state => (isQueryBoundP_true_iff _ _).2
      (known_bills setup.source codec control pending root state).1)
    (fun control pending state => (isQueryBoundP_true_iff _ _).2
      (selected_bills setup.source codec rest control pending state).1) state

/-- Interpreting the complete actual finish additionally pays its real shared commitment/opening sampling. Exact source-program equality retains all private component work under projection. -/
theorem finish_evaluated_uniform (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (context : Context KemSK) (rest : PqxdhServerAuthCtxCalls.Residual) (select : Bool)
    (caps : KemCaps) (bounded : KemBound setup caps) (raw : Pqxdh.Bytes) (key : RootOutput)
    (state : State KemSK) :
    ((evaluate setup.source key codec.frameRead (finish setup codec context rest select raw)).run state).IsTotalQueryBound
      ((caps.decapsCost + 128) * initSentFlag state.1.1.1) := by
  have services : ServiceUniform (if select then selectingServices setup context
      (factorServices setup codec checks context (PqxdhServerAuthCtxMaterial.output key rest))
      else factorServices setup codec checks context (PqxdhServerAuthCtxMaterial.output key rest)) := by
    cases select
    · exact factor_services_uniform setup codec checks context _
    · exact selecting_services_uniform setup context _ (factor_services_uniform setup codec checks context _)
  have bill := finish_step_uniform setup codec (context.publicValue setup) context.beaconSeed _ services
    caps bounded raw (PqxdhServerAuthCtxState.project state).1
  have same := finish_source setup codec checks context rest select raw key state
  have mapped : (Prod.map id PqxdhServerAuthCtxState.project <$>
      (evaluate setup.source key codec.frameRead (finish setup codec context rest select raw)).run state).IsTotalQueryBound
        ((caps.decapsCost + 128) * initSentFlag state.1.1.1) := by
    rw [same]
    simpa only [IsTotalQueryBound, isQueryBound_map_iff, PqxdhServerAuthCtxState.project, restore, restoreFlat, initSentFlag] using bill
  simpa only [IsTotalQueryBound, isQueryBound_map_iff] using mapped

/-- Final native publication consumes the one-shot finish opportunity while preserving allocation, pending tokens, session marks and the designation flag. -/
theorem complete_footprint (control : pqxdh.BeaconInitSent) (state : Local KemSK)
    (staged : Option PqxdhBeaconPhase2Publication.Staged) :
    (complete control state staged).2.1.1.sessions = state.1.1.sessions ∧
    (complete control state staged).2.1.1.pending = state.1.1.pending ∧
    initSentFlag (complete control state staged).2.1.1 = 0 ∧
    (complete control state staged).2.1.2.1 = state.1.2.1 ∧
    (complete control state staged).2.2 = state.2 := by
  exact ⟨(finishOutcome_resources control state.1.1 staged).1,
    (finishOutcome_resources control state.1.1 staged).2.1,
    (finishOutcome_resources control state.1.1 staged).2.2, rfl, rfl⟩

/-- Every syntactically supported dynamic finish reply has the original resource footprint, unchanged session marks and unchanged designation flag, for arbitrary component replies. -/
theorem finish_footprint (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (context : Context KemSK) (rest : PqxdhServerAuthCtxCalls.Residual) (select : Bool)
    (raw : Pqxdh.Bytes) (state : Local KemSK) (result : Option Pqxdh.Bytes × Local KemSK)
    (supported : result ∈ support ((finish setup codec context rest select raw).run state)) :
    ResourceStep (.inr (.finish raw)) state.1.1 result.2.1.1 ∧
      result.2.1.2.1 = state.1.2.1 ∧ result.2.2 = state.2 := by
  simp only [finish, StateT.run] at supported
  cases phase : state.1.1.beacon.beacon.phase with
  | initSent control prekey oneTime kem =>
      simp only [phase, mem_support_bind_iff] at supported
      obtain ⟨prepared, _, supported⟩ := supported
      cases found : prepared with
      | none =>
          simp only [found, support_pure, Set.mem_singleton_iff] at supported
          subst supported
          simpa only [ResourceStep, and_assoc] using complete_footprint control state none
      | some pending =>
          simp only [found, mem_support_bind_iff] at supported
          obtain ⟨derived, _, supported⟩ := supported
          cases reply : derived.1 with
          | rejected =>
              simp only [reply, support_pure, Set.mem_singleton_iff] at supported
              subst supported
              simpa only [ResourceStep, and_assoc, touched] using complete_footprint control
                (touched state _ derived.2) none
          | root root =>
              simp only [reply, known, after, support_map, Set.mem_image] at supported
              obtain ⟨staged, _, rfl⟩ := supported
              simpa only [ResourceStep, and_assoc, touched] using complete_footprint control
                (touched state _ derived.2) staged
          | hidden =>
              simp only [reply, selected, after, support_map, Set.mem_image] at supported
              obtain ⟨staged, _, rfl⟩ := supported
              simpa only [ResourceStep, and_assoc, touched] using complete_footprint control
                (touched state _ derived.2) staged
  | _ =>
      simp only [phase, support_pure, Set.mem_singleton_iff] at supported
      subst supported
      exact ⟨⟨rfl, rfl, by simp only [initSentFlag, phase]⟩, rfl, rfl⟩

end BeaconcryptCore.Computational.PqxdhServerAuthCtxFinishBounds

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxFinishBounds.finish_query_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxFinishBounds.finish_query_bound
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxFinishBounds.known_bills' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxFinishBounds.known_bills
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxFinishBounds.selected_bills' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxFinishBounds.selected_bills
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxFinishBounds.finish_record_bills' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxFinishBounds.finish_record_bills
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxFinishBounds.prefix_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxFinishBounds.prefix_bound
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxFinishBounds.table_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxFinishBounds.table_bound
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxFinishBounds.finish_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxFinishBounds.finish_uniform
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxFinishBounds.finish_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxFinishBounds.finish_total
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxFinishBounds.finish_evaluated_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxFinishBounds.finish_evaluated_uniform
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxFinishBounds.complete_footprint' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxFinishBounds.complete_footprint
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxFinishBounds.finish_footprint' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxFinishBounds.finish_footprint
