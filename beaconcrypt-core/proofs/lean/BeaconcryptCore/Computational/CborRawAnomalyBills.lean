-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.CborRawAnomalyGuesser
import BeaconcryptCore.Computational.PqxdhDeploymentHeadlineAnomaly

/-! The raw anomaly reduction makes at most one logical decapsulation per original finish request. All initialization, nonselected private work, record callbacks and secrecy draws run on its own coins; admission remains below the unchanged ledger. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.CborRawAnomalyBills
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhDeploymentIdealParams (Target Params)
open PqxdhDeploymentInterface (Spec FullSpec FreshBounds Mode ModeSpec Budget)
open PqxdhKemIndCca (IsMlKemLogicalDecapsulationQuery MlKem768PublicKey)
open PqxdhDeploymentNative (State)
open PqxdhPrivateKemSource (ccaCoins)
open PqxdhDeploymentIdealAnomalyGuesser (ccaCoins_decapsulate flat)
variable {ι KemSK Reader Response A X : Type} {baseSpec : OracleSpec ι}

private theorem native_selected_run (setup : Setup baseSpec KemSK) (wire : Codec Reader Response)
    (parse : Pqxdh.Bytes → Option CborProductionBoundary.NativeFrame) (checks : Checks) {count : Nat}
    (target : Target count) (parameters : Params KemSK count) (created : PqxdhLiveServerConstruction.Created Unit)
    (raw : Pqxdh.Bytes) (state : State KemSK) :
    (CborRawAnomalyNativeGuesser.native setup wire parse checks target parameters created (.inr (.finish target.kem.val raw))).run state =
      (CborRawAnomalyOracle.rawFinish setup wire parse target.kem.val raw).run state := by
  change (if target.kem.val = target.kem.val then _ else _) = _
  rw [ite_eq_left rfl]

private theorem native_lift_run (setup : Setup baseSpec KemSK) (wire : Codec Reader Response)
    (parse : Pqxdh.Bytes → Option CborProductionBoundary.NativeFrame) (checks : Checks) {count : Nat}
    (target : Target count) (parameters : Params KemSK count) (created : PqxdhLiveServerConstruction.Created Unit)
    (query : Spec.Domain) (state : State KemSK)
    (notSelected : ∀ raw, query ≠ .inr (.finish target.kem.val raw)) :
    (CborRawAnomalyNativeGuesser.native setup wire parse checks target parameters created query).run state = ccaCoins
      ((CborRawPoolCompiler.native setup wire parse checks created.seed (parameters.pool target) query).run state) := by
  rcases query with coin | command
  · rfl
  · cases command
    case finish owner raw =>
      change (if owner = target.kem.val then _ else _) = _
      rw [ite_eq_right (fun same => notSelected raw (by rw [same]))]
    all_goals rfl

/-- Every actual native CCA handler call uses at most one logical decapsulation. -/
theorem native_bound (setup : Setup baseSpec KemSK) (wire : Codec Reader Response)
    (parse : Pqxdh.Bytes → Option CborProductionBoundary.NativeFrame) (checks : Checks) {count : Nat}
    (target : Target count) (parameters : Params KemSK count) (created : PqxdhLiveServerConstruction.Created Unit)
    (query : Spec.Domain) (state : State KemSK) :
    ((CborRawAnomalyNativeGuesser.native setup wire parse checks target parameters created query).run state).IsQueryBoundP
      IsMlKemLogicalDecapsulationQuery 1 := by
  by_cases selected : ∃ raw, query = .inr (.finish target.kem.val raw)
  · obtain ⟨raw, rfl⟩ := selected
    rw [native_selected_run]
    exact CborRawAnomalyOracle.rawFinish_decapsulations setup wire parse target.kem.val raw state
  · rw [native_lift_run setup wire parse checks target parameters created query state
      (fun raw same => selected ⟨raw, same⟩)]
    exact (ccaCoins_decapsulate ((CborRawPoolCompiler.native setup wire parse checks created.seed
      (parameters.pool target) query).run state)).mono (by omega)

/-- Every native operation other than an original finish has no logical decapsulation query. -/
theorem native_other (setup : Setup baseSpec KemSK) (wire : Codec Reader Response)
    (parse : Pqxdh.Bytes → Option CborProductionBoundary.NativeFrame) (checks : Checks) {count : Nat}
    (target : Target count) (parameters : Params KemSK count) (created : PqxdhLiveServerConstruction.Created Unit)
    (query : Spec.Domain) (other : ∀ owner raw, query ≠ .inr (.finish owner raw)) (state : State KemSK) :
    ((CborRawAnomalyNativeGuesser.native setup wire parse checks target parameters created query).run state).IsQueryBoundP
      IsMlKemLogicalDecapsulationQuery 0 := by
  rw [native_lift_run setup wire parse checks target parameters created query state (fun raw same => other target.kem.val raw same)]
  exact ccaCoins_decapsulate ((CborRawPoolCompiler.native setup wire parse checks created.seed (parameters.pool target) query).run state)

/-- Complete original ledger steps make no decapsulation query outside the original finish class. -/
theorem flat_bound (setup : Setup baseSpec KemSK) (wire : Codec Reader Response)
    (parse : Pqxdh.Bytes → Option CborProductionBoundary.NativeFrame) (checks : Checks) {count : Nat}
    (t : Target count) (p : Params KemSK count) (bounds : PqxdhDeploymentInterface.FreshBounds)
    (created : PqxdhLiveServerConstruction.Created Unit) (query : PqxdhDeploymentInterface.Query)
    (state : PqxdhDeploymentSecrecy.Ledger × State KemSK) :
    ((flat setup (CborTaggedSimulation.boundaryWire wire parse) bounds (CborRawAnomalyNativeGuesser.native setup wire parse checks t p created) query).run
      state).IsQueryBoundP IsMlKemLogicalDecapsulationQuery
        (if PqxdhDeploymentInterface.queryClass query = 5 then 1 else 0) := by
  rcases query with request | secrecy
  · change ((fun r => (r.1.1, (r.1.2, r.2))) <$> (simulateQ (CborRawAnomalyNativeGuesser.native setup wire parse checks t p created)
      ((PqxdhDeploymentSecrecy.ledgerImpl setup.source.crypto (CborTaggedSimulation.boundaryWire wire parse) setup.serverKeyId bounds (.inl request)).run state.1)).run state.2).IsQueryBoundP
        _ _
    rw [isQueryBoundP_map_iff, PqxdhDeploymentSecrecy.ledgerImpl_forward, simulateQ_map, simulateQ_spec_query,
      StateT.run_map, isQueryBoundP_map_iff]
    split
    · exact native_bound setup wire parse checks t p created request state.2
    · rename_i notFinish
      refine native_other setup wire parse checks t p created request (fun owner raw same => ?_) state.2
      subst same
      exact notFinish rfl
  · change ((fun r => (r.1.1, (r.1.2, r.2))) <$> (simulateQ (CborRawAnomalyNativeGuesser.native setup wire parse checks t p created)
      ((PqxdhDeploymentSecrecy.ledgerImpl setup.source.crypto (CborTaggedSimulation.boundaryWire wire parse) setup.serverKeyId bounds (.inr secrecy)).run state.1)).run state.2).IsQueryBoundP
        _ _
    have notFinish : PqxdhDeploymentInterface.queryClass (.inr secrecy) ≠ 5 := by
      rcases secrecy <;> simp [PqxdhDeploymentInterface.queryClass]
    simp only [notFinish, ↓reduceIte]
    rw [isQueryBoundP_map_iff]
    refine (PqxdhDeploymentSecrecy.secrecy_frame setup.source.crypto (CborTaggedSimulation.boundaryWire wire parse) setup.serverKeyId bounds secrecy
      state.1).simulateQ_run_of_step (fun query _ inner => native_bound setup wire parse checks t p created
        query inner) (fun query coinSend inner => native_other setup wire parse checks t p created query
          (fun owner raw same => by subst same; exact coinSend rfl) inner) _


private theorem wrap_run {σ Result : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (bounds : FreshBounds)
    (impl : QueryImpl Spec (StateT σ m)) (work : OracleComp FullSpec Result) (state : σ) :
    (simulateQ impl (PqxdhDeploymentSecrecy.wrap setup.source.crypto codec setup.serverKeyId bounds work)).run state =
      (fun result => ((result.1, result.2.1), result.2.2)) <$>
        (simulateQ (flat setup codec bounds impl) work).run (PqxdhDeploymentSecrecy.Ledger.empty, state) := by
  unfold PqxdhDeploymentSecrecy.wrap
  rw [OracleComp.simulateQ_mapStateTBase_run_eq_map_flattenStateT]
  rfl

/-- The entire original secrecy wrapper respects the adversary's finish budget under the actual native CCA oracle interpreter. -/
theorem wrapped_bound (setup : Setup baseSpec KemSK) (wire : Codec Reader Response)
    (parse : Pqxdh.Bytes → Option CborProductionBoundary.NativeFrame) (checks : Checks) {count : Nat}
    (target : Target count) (parameters : Params KemSK count) (created : PqxdhLiveServerConstruction.Created Unit)
    (bounds : FreshBounds) (mode : Mode) (adversary : OracleComp (ModeSpec mode) X) (budget : Budget)
    (respects : budget.Respects adversary) (state : State KemSK) :
    ((simulateQ (CborRawAnomalyNativeGuesser.native setup wire parse checks target parameters created)
      (PqxdhDeploymentSecrecy.wrap setup.source.crypto (CborTaggedSimulation.boundaryWire wire parse)
        setup.serverKeyId bounds (PqxdhDeploymentInterface.asModeO mode adversary))).run state).IsQueryBoundP
      IsMlKemLogicalDecapsulationQuery budget.finish := by
  rw [wrap_run, isQueryBoundP_map_iff]
  have total := FinitePartitionQueryBounds.weighted_bound PqxdhDeploymentInterface.queryClass
    (fun kind => if kind = 5 then 1 else 0) budget.cap
    (flat setup (CborTaggedSimulation.boundaryWire wire parse) bounds
      (CborRawAnomalyNativeGuesser.native setup wire parse checks target parameters created))
    IsMlKemLogicalDecapsulationQuery (PqxdhDeploymentInterface.asModeO mode adversary)
    (PqxdhDeploymentCompileSecrecy.asModeO_bound mode adversary budget respects)
    (fun query state => flat_bound setup wire parse checks target parameters bounds created query state)
    (PqxdhDeploymentSecrecy.Ledger.empty, state)
  have sum : (∑ kind : Fin 14, (if kind = 5 then 1 else 0) * budget.cap kind) = budget.finish := by
    simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
    rfl
  rwa [sum] at total

/-- The explicit complete raw CCA predictor makes at most one logical decapsulation per original finish command. -/
theorem guesser_bound (setup : Setup baseSpec KemSK) (wire : Codec Reader Response)
    (parse : Pqxdh.Bytes → Option CborProductionBoundary.NativeFrame) (checks : Checks) {count : Nat}
    (target : Target count) (ensureInit : StateT A ProbComp Bool) (runtime : A) (bounds : FreshBounds)
    (mode : Mode) (adversary : OracleComp (ModeSpec mode) X) (budget : Budget)
    (respects : budget.Respects adversary) (publicKey : MlKem768PublicKey) :
    (CborRawAnomalyGuesser.guesser setup wire parse checks target ensureInit runtime bounds mode adversary publicKey).IsQueryBoundP
      IsMlKemLogicalDecapsulationQuery budget.finish := by
  unfold CborRawAnomalyGuesser.guesser
  rw [show budget.finish = 0 + (0 + (0 + (budget.finish + 0))) by omega]
  refine isQueryBoundP_bind (ccaCoins_decapsulate _) fun dummy _ => ?_
  refine isQueryBoundP_bind (ccaCoins_decapsulate _) fun others _ => ?_
  refine isQueryBoundP_bind (ccaCoins_decapsulate _) fun born _ => ?_
  rcases born with ⟨_ | created, after⟩
  · exact isQueryBoundP_pure _ _ _
  · refine isQueryBoundP_bind ?_ fun _ _ => isQueryBoundP_pure _ _ _
    exact wrapped_bound setup wire parse checks target _ created bounds mode adversary budget respects _

/-- The concrete predict-then-compare phase adds exactly one logical decapsulation to the raw predictor's finish budget. -/
theorem ptc_pre_bound (setup : Setup baseSpec KemSK) (wire : Codec Reader Response)
    (parse : Pqxdh.Bytes → Option CborProductionBoundary.NativeFrame) (checks : Checks) {count : Nat}
    (target : Target count) (ensureInit : StateT A ProbComp Bool) (runtime : A) (bounds : FreshBounds)
    (mode : Mode) (adversary : OracleComp (ModeSpec mode) X) (budget : Budget)
    (respects : budget.Respects adversary) (publicKey : MlKem768PublicKey) :
    ((PqxdhDeploymentHeadlineAnomaly.ptc setup.kem
      (CborRawAnomalyGuesser.guesser setup wire parse checks target ensureInit runtime bounds mode adversary)).preChallenge publicKey).IsQueryBoundP
        IsMlKemLogicalDecapsulationQuery (budget.finish + 1) :=
  PqxdhDeploymentHeadlineAnomaly.ptc_decapsulations setup.kem _ budget.finish
    (fun key => guesser_bound setup wire parse checks target ensureInit runtime bounds mode adversary budget respects key) publicKey

/-- The actual raw anomaly CCA reduction issues no post-challenge query of any kind. -/
theorem ptc_post_bound (setup : Setup baseSpec KemSK) (wire : Codec Reader Response)
    (parse : Pqxdh.Bytes → Option CborProductionBoundary.NativeFrame) (checks : Checks) {count : Nat}
    (target : Target count) (ensureInit : StateT A ProbComp Bool) (runtime : A) (bounds : FreshBounds)
    (mode : Mode) (adversary : OracleComp (ModeSpec mode) X)
    (transcript : PqxdhKemIndCca.MlKemChallengeTranscript (PqxdhDeploymentHeadlineAnomaly.ptc setup.kem
      (CborRawAnomalyGuesser.guesser setup wire parse checks target ensureInit runtime bounds mode adversary)).Context)
    (key : PqxdhKemIndCca.MlKemSharedSecret)
    (predicate : (PqxdhKemIndCca.MlKemCCAOracleSpec baseSpec).Domain → Prop) [DecidablePred predicate] :
    ((PqxdhDeploymentHeadlineAnomaly.ptc setup.kem
      (CborRawAnomalyGuesser.guesser setup wire parse checks target ensureInit runtime bounds mode adversary)).postChallenge transcript key).IsQueryBoundP predicate 0 :=
  PqxdhDeploymentHeadlineAnomaly.ptc_post setup.kem _ transcript key predicate

end BeaconcryptCore.Computational.CborRawAnomalyBills

/-- info: 'BeaconcryptCore.Computational.CborRawAnomalyBills.native_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawAnomalyBills.native_bound
/-- info: 'BeaconcryptCore.Computational.CborRawAnomalyBills.native_other' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawAnomalyBills.native_other

/-- info: 'BeaconcryptCore.Computational.CborRawAnomalyBills.flat_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawAnomalyBills.flat_bound

/-- info: 'BeaconcryptCore.Computational.CborRawAnomalyBills.wrapped_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawAnomalyBills.wrapped_bound
/-- info: 'BeaconcryptCore.Computational.CborRawAnomalyBills.guesser_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawAnomalyBills.guesser_bound

/-- info: 'BeaconcryptCore.Computational.CborRawAnomalyBills.ptc_pre_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawAnomalyBills.ptc_pre_bound
/-- info: 'BeaconcryptCore.Computational.CborRawAnomalyBills.ptc_post_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawAnomalyBills.ptc_post_bound
