import BeaconcryptCore.Computational.PqxdhServerAuthNativeUniformCosts
import BeaconcryptCore.Computational.PqxdhJointIdentityFamily

/-! Explicit uniform bill for the same concrete all-attempt joint identity reduction. All KEM base calls are interpreted and charged. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhServerAuthJointIdentityUniformCosts
open PqxdhJointIdentity PqxdhServerAuthExperiment PqxdhJointIdentityFamily
open PqxdhServerAuthJointIdentityCompiler PqxdhServerAuthSourceCosts
open PqxdhJointGapDh (ScalarBytes PublicChallenge)
variable {ι KemSK Reader Response : Type} {baseSpec : OracleSpec ι}

/-- Every draw of a fully interpreted local primitive computation remains on the joint uniform interface. -/
theorem coins_uniform {Result : Type} (work : ProbComp Result) (count : Nat)
    (bounded : work.IsTotalQueryBound count) :
    (coins work).IsQueryBoundP (IsClass .uniform) count := by
  exact bounded.isQueryBoundP.simulateQ_of_step
    (fun query _ => (isQueryBoundP_query_iff _ _ _).mpr (fun _ => Nat.one_pos))
    (fun _ absent => (absent trivial).elim)

/-- Select the one actual logical KEM callback in the original Beacon preparation interface. -/
def Decaps {I D K X R : Type} : (PqxdhBeaconPhase2Preparation.Spec I D K X R).Domain → Bool
  | .decapsulate _ _ => true
  | _ => false

set_option maxHeartbeats 1000000 in
/-- Every original success or rejection path attempts at most one decapsulation. -/
theorem collect_decaps {I D K X R : Type} (identity : I) (prekey oneTime : D) (kem : K) (raw : Pqxdh.Bytes) :
    (PqxdhBeaconPhase2Preparation.collect (X := X) (Response := R) identity prekey oneTime kem raw).IsQueryBoundP
      (fun query => Decaps query = true) 1 := by
  unfold PqxdhBeaconPhase2Preparation.collect
  simp only [OptionT.run_bind, OptionT.run_mk, OptionT.run_pure, OptionT.run_monadLift, Option.elimM, bind_map_left]
  repeat' first
    | trivial
    | (rw [isQueryBoundP_query_bind_iff]; refine ⟨by simp [Decaps], ?_⟩)
    | (fail_if_no_progress simp only [Option.elim_some])
    | intro answer; cases answer

/-- Core admission and shared-secret erasure add no KEM request after collection. -/
theorem prepare_decaps {I D K X R : Type} (control : pqxdh.BeaconInitSent)
    (identity : I) (prekey oneTime : D) (kem : K) (raw : Pqxdh.Bytes) :
    (PqxdhBeaconPhase2Preparation.prepare (X := X) (Response := R) control identity prekey oneTime kem raw).IsQueryBoundP
      (fun query => Decaps query = true) 1 := by
  unfold PqxdhBeaconPhase2Preparation.prepare
  refine isQueryBoundP_bind (n := 1) (m := 0) (collect_decaps identity prekey oneTime kem raw) ?_
  rintro (_ | input) _
  · trivial
  · simp [PqxdhBeaconPhase2Preparation.afterInputs, Decaps]

/-- Both disjoint source query classes include every optional reply path. -/
theorem prepare_classes {I D K X R : Type} (control : pqxdh.BeaconInitSent)
    (identity : I) (prekey oneTime : D) (kem : K) (raw : Pqxdh.Bytes) (kind : Bool) :
    (PqxdhBeaconPhase2Preparation.prepare (X := X) (Response := R) control identity prekey oneTime kem raw).IsQueryBoundP
      (fun query => Decaps query = kind) (if kind then 1 else 13) := by
  cases kind
  · exact (PqxdhBeaconPhase2Preparation.prepare_bound control identity prekey oneTime kem raw).isQueryBoundP
  · exact prepare_decaps control identity prekey oneTime kem raw

set_option backward.isDefEq.respectTransparency false in
/-- Only actual KEM work contributes uniform queries in the auxiliary interpreter; its full interpreted base bill is retained. -/
theorem auxiliary_uniform (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (caps : KemCaps) (bounded : KemBound setup caps)
    (query : (PqxdhBeaconPhase2Preparation.Spec Unit (Unit ⊕ ScalarBytes) KemSK Unit Response).Domain) :
    (auxiliary setup codec query).IsQueryBoundP (IsClass .uniform) (if Decaps query then caps.decapsCost else 0) := by
  cases query <;> simp only [auxiliary, Decaps, Bool.false_eq_true, ite_true, ite_false, isQueryBoundP_pure,
    isQueryBoundP_map_iff, isQueryBoundP_query_iff, IsClass, reduceCtorEq, false_implies]
  case decapsulate ciphertext secret =>
    exact coins_uniform _ caps.decapsCost (decaps_uniform setup caps bounded secret (PqxdhPhase2InputBytes.ciphertext ciphertext))
  case dhPair pair point => cases pair <;> trivial

set_option backward.isDefEq.respectTransparency false in
/-- Selected-prekey routing preserves the full optional-decapsulation bill; scalar-DH and joint-DH replies add no uniform query. -/
theorem prefix_uniform (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (scalar : ScalarBytes)
    (caps : KemCaps) (bounded : KemBound setup caps)
    (query : (PqxdhBeaconPhase2Preparation.Spec Unit (Unit ⊕ (Unit ⊕ ScalarBytes)) KemSK Unit Response).Domain)
    (state : Unit) :
    ((prefixImpl setup codec scalar query).run state).IsQueryBoundP (IsClass .uniform)
      (if Decaps query then caps.decapsCost else 0) := by
  cases query <;> simp only [prefixImpl, PqxdhPhase2GapDhSource.nativeImpl, StateT.run_lift, bind_pure_comp,
    isQueryBoundP_map_iff]
  all_goals try exact auxiliary_uniform setup codec caps bounded _
  rename_i pair point
  cases pair <;> simp only [StateT.run, StateT.lift, bind_pure_comp, isQueryBoundP_map_iff]
  all_goals first | exact auxiliary_uniform setup codec caps bounded _ | trivial

set_option backward.isDefEq.respectTransparency false in
/-- The complete original preparation pays the full cost of at most one optional KEM decapsulation. -/
theorem prepare_uniform (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (scalar : ScalarBytes) (caps : KemCaps) (bounded : KemBound setup caps)
    (control : pqxdh.BeaconInitSent) (identity : Unit) (oneTime : Unit ⊕ ScalarBytes)
    (kem : KemSK) (raw : Pqxdh.Bytes) :
    (prepare setup codec scalar control identity oneTime kem raw).IsQueryBoundP (IsClass .uniform) caps.decapsCost := by
  have result := FinitePartitionQueryBounds.weighted_bound
    (Decaps (I := Unit) (D := Unit ⊕ (Unit ⊕ ScalarBytes)) (K := KemSK) (X := Unit) (R := Response))
    (fun kind => if kind then caps.decapsCost else 0) (fun kind => if kind then 1 else 13)
    (prefixImpl setup codec scalar) (IsClass .uniform)
    (PqxdhBeaconPhase2Preparation.prepare control identity (.inl ()) (.inr oneTime) kem raw)
    (prepare_classes (X := Unit) (R := Response) control identity
      (Sum.inl () : Unit ⊕ (Unit ⊕ ScalarBytes)) (.inr oneTime) kem raw)
    (prefix_uniform setup codec scalar caps bounded) ()
  simpa only [prepare, StateT.run'_eq, isQueryBoundP_map_iff, Fintype.sum_bool,
    Bool.false_eq_true, ite_true, ite_false, Nat.mul_one, Nat.zero_mul, Nat.add_zero] using result

/-- The routed preparation and complete original Beacon tail pay one decapsulation plus two 64-byte cache-miss allowances. -/
theorem stage_uniform (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (serverSeed : IdentitySeed) (scalar : ScalarBytes) (caps : KemCaps) (bounded : KemBound setup caps)
    (control : pqxdh.BeaconInitSent) (identity : Unit) (oneTime : Unit ⊕ ScalarBytes)
    (kem : KemSK) (raw : Pqxdh.Bytes) (state : PqxdhServerAuthNative.NativeState KemSK) :
    ((stage setup codec serverSeed scalar control identity oneTime kem raw).run state).IsQueryBoundP
      (IsClass .uniform) (caps.decapsCost + 128) := by
  simp only [stage, StateT.run]
  refine isQueryBoundP_bind (n := caps.decapsCost) (m := 128)
    (prepare_uniform setup codec scalar caps bounded control identity oneTime kem raw) ?_
  rintro (_ | original) _
  · trivial
  · exact coins_uniform _ 128 (PqxdhServerAuthNativeUniformCosts.beacon_tail_uniform setup codec _ original state)

/-- Every attempted finish pays the full active-stage allowance; inactive, rejected and aborted calls retain their original results. -/
theorem finish_uniform (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (serverSeed : IdentitySeed) (scalar : ScalarBytes) (caps : KemCaps) (bounded : KemBound setup caps)
    (raw : Pqxdh.Bytes) (state : PqxdhServerAuthNative.NativeState KemSK) :
    ((finish setup codec serverSeed scalar raw).run state).IsQueryBoundP
      (IsClass .uniform) (caps.decapsCost + 128) := by
  simp only [finish, StateT.run]
  cases state.2.beacon.beacon.phase <;> simp only [isQueryBoundP_pure]
  rename_i control prekey oneTime kem
  refine (isQueryBoundP_bind (n := caps.decapsCost + 128) (m := 0)
    (stage_uniform setup codec serverSeed scalar caps bounded control state.2.beacon.beacon.identity oneTime kem raw state)
    ?_).mono (by omega)
  exact fun _ _ => trivial

/-- A conservative common bill for any public API call. Its KEM terms include every interpreted base query. -/
def callCost (caps : KemCaps) : Nat := 128 + caps.encapsCost + caps.decapsCost

set_option backward.isDefEq.respectTransparency false in
/-- The complete public handler bills arbitrary accepts, builds, finishes, public primitive queries and reveals without assuming any accepted candidate is honest. -/
theorem handler_uniform (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (serverSeed : IdentitySeed) (scalar : ScalarBytes) (caps : KemCaps) (bounded : KemBound setup caps)
    (query : ServerAuthSpec.Domain) (state : PqxdhServerAuthNative.NativeState KemSK) :
    ((handler setup codec checks serverSeed scalar query).run state).IsQueryBoundP
      (IsClass .uniform) (callCost caps) := by
  rcases query with coin | request
  · exact (coins_uniform _ 1 (PqxdhServerAuthNativeUniformCosts.coin_uniform setup codec checks serverSeed serverSeed scalar coin state)).mono
      (by unfold callCost; omega)
  · cases request
    case finish raw =>
      exact (finish_uniform setup codec serverSeed scalar caps bounded raw state).mono (by unfold callCost; omega)
    case accept raw =>
      exact (coins_uniform _ (96 + caps.encapsCost)
        (PqxdhServerAuthNativeUniformCosts.accept_uniform setup codec checks caps bounded serverSeed scalar raw state)).mono
          (by unfold callCost; omega)
    case build session payload =>
      exact (coins_uniform _ 64
        (PqxdhServerAuthNativeUniformCosts.native_build_uniform setup codec checks session payload state)).mono
          (by unfold callCost; omega)
    case hmac key message =>
      exact (coins_uniform _ 64
        (PqxdhServerAuthNativeUniformCosts.hmac_uniform setup serverSeed scalar key message state)).mono
          (by unfold callCost; omega)
    case hash bytes =>
      exact (coins_uniform _ 64 (PqxdhServerAuthNativeUniformCosts.hash_uniform bytes state)).mono (by unfold callCost; omega)
    case reveal key => trivial

/-- All adaptive source API calls are billed, including rejected and post-termination requests, before the original complete state is returned. -/
theorem program_uniform {Result : Type} (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (serverSeed : IdentitySeed) (scalar : ScalarBytes) (caps : KemCaps) (kemBound : KemBound setup caps)
    (work : OracleComp ServerAuthSpec Result) (qTotal : Nat) (bounded : work.IsTotalQueryBound qTotal)
    (state : PqxdhServerAuthNative.NativeState KemSK) :
    ((simulateQ (handler setup codec checks serverSeed scalar) work).run state).IsQueryBoundP
      (IsClass .uniform) (qTotal * callCost caps) := by
  have result := FinitePartitionQueryBounds.weighted_bound
    (fun (_ : ServerAuthSpec.Domain) => ()) (fun (_ : Unit) => callCost caps) (fun (_ : Unit) => qTotal)
    (handler setup codec checks serverSeed scalar) (IsClass .uniform) work
    (fun _ => bounded.isQueryBoundP) (handler_uniform setup codec checks serverSeed scalar caps kemBound) state
  simpa only [Fintype.sum_unique, Nat.mul_comm] using result

set_option backward.isDefEq.respectTransparency false in
/-- The literal generated Phase1 bundle makes three signing calls and no uniform request, including optional writer refusal. -/
theorem phase1_uniform (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (target : PublicIdentity) (publicValue : PublicChallenge) (oneTime : ScalarBytes)
    (kemPk : PqxdhKemIndCca.MlKem768PublicKey) (kemSk : KemSK) :
    (phase1 setup codec target publicValue oneTime kemPk kemSk).IsQueryBoundP (IsClass .uniform) 0 := by
  simp only [phase1, PqxdhLivePhase1Bundle.bundle, freshBeacon,
    simulateQ_bind, simulateQ_spec_query, signingImpl, pure_bind]
  simp only [PqxdhLivePhase1Bundle.afterGenerated, PqxdhBeaconPhase1Publication.prepare,
    Option.map_some, publicProjection, PqxdhLivePhase1Bundle.signing,
    PqxdhJointPhase1SourceWriter.signingProgram, simulateQ_bind, simulateQ_spec_query,
    signingImpl, bind_map_left]
  simp only [simulateQ_pure, bind_assoc, pure_bind, PqxdhLivePhase1Bundle.writing,
    PqxdhBeaconPhase1Publication.afterSigning, PqxdhBeaconPhase1Publication.prepare,
    Option.map_some, simulateQ_bind, simulateQ_spec_query, signingImpl]
  repeat' (rw [isQueryBoundP_query_bind_iff]; refine ⟨by simp [IsClass], ?_⟩; intro signature)
  split <;> simp only [simulateQ_pure] <;> trivial

/-- Publication followed by the complete adaptive source continuation retains the all-call uniform bill and every original output and state field. -/
theorem execution_uniform {Result : Type} (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (serverSeed : IdentitySeed) (scalar oneTime : ScalarBytes)
    (keys : PqxdhKemIndCca.MlKem768PublicKey × KemSK) (caps : KemCaps) (kemBound : KemBound setup caps)
    (work : AuthInput → OracleComp ServerAuthSpec Result) (qTotal : Nat)
    (bounded : ∀ input, (work input).IsTotalQueryBound qTotal) (target : PublicIdentity) :
    (execution setup codec checks serverSeed scalar oneTime keys work target).IsQueryBoundP
      (IsClass .uniform) (qTotal * callCost caps) := by
  unfold execution
  refine (isQueryBoundP_bind (n := 0) (m := qTotal * callCost caps)
    (phase1_uniform setup codec target _ oneTime keys.1 keys.2) ?_).mono (by omega)
  intro published _
  refine (isQueryBoundP_bind (n := qTotal * callCost caps) (m := 0)
    (program_uniform setup codec checks serverSeed scalar caps kemBound _ qTotal (bounded _) _) ?_).mono (by omega)
  exact fun _ _ => trivial

/-- Complete local source generation and every adaptive API call, excluding the challenger's own target-seed sampling cost. -/
def reductionCost (caps : KemCaps) (qTotal : Nat) : Nat := 96 + caps.keygenCost + qTotal * callCost caps

/-- The actual captured execution pays three local 32-byte samplers, one full KEM key generation, and all adaptive API calls. Journaling adds no oracle request. -/
theorem capture_uniform (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (caps : KemCaps) (kemBound : KemBound setup caps) (adversary : Adversary) (qTotal : Nat)
    (bounded : ∀ input, (adversary input).IsTotalQueryBound qTotal) (target : PublicIdentity) :
    (PqxdhServerAuthJointIdentityEuf.capture setup codec checks adversary target).IsQueryBoundP
      (IsClass .uniform) (reductionCost caps qTotal) := by
  unfold PqxdhServerAuthJointIdentityEuf.capture reductionCost
  refine (isQueryBoundP_bind (n := 32) (m := 64 + caps.keygenCost + qTotal * callCost caps)
    (coins_uniform _ 32 sampleSeed_uniform_bound) (fun serverSeed _ => ?_)).mono (by omega)
  refine (isQueryBoundP_bind (n := 32) (m := 32 + caps.keygenCost + qTotal * callCost caps)
    (coins_uniform _ 32 PqxdhJointGapDh.sampleScalar_uniform) (fun scalar _ => ?_)).mono (by omega)
  refine (isQueryBoundP_bind (n := caps.keygenCost) (m := 32 + qTotal * callCost caps)
    (coins_uniform _ caps.keygenCost (keygen_uniform setup caps kemBound)) (fun keys _ => ?_)).mono (by omega)
  refine isQueryBoundP_bind (n := 32) (m := qTotal * callCost caps)
    (coins_uniform _ 32 PqxdhJointGapDh.sampleScalar_uniform) (fun oneTime _ => ?_)
  rw [bind_pure_comp, isQueryBoundP_map_iff]
  exact execution_uniform setup codec checks serverSeed scalar oneTime keys caps kemBound _ qTotal
    (fun input => (isQueryBoundP_true_iff _ _).mp
      ((PqxdhServerAuthApiJournal.query_bound (adversary input) (fun _ => True) qTotal).mpr
        (bounded input).isQueryBoundP)) target

/-- Public forgery extraction preserves the full concrete execution bill. No ambient computation is declared free. -/
theorem reduction_uniform (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (caps : KemCaps) (kemBound : KemBound setup caps) (adversary : Adversary) (qTotal : Nat)
    (bounded : ∀ input, (adversary input).IsTotalQueryBound qTotal) (fallback : Forgery) (target : PublicIdentity) :
    (PqxdhServerAuthJointIdentityEuf.reduction setup codec checks adversary fallback target).IsQueryBoundP
      (IsClass .uniform) (reductionCost caps qTotal) :=
  (PqxdhServerAuthJointIdentityResources.reduction_queries setup codec checks adversary fallback target
    (IsClass .uniform) (reductionCost caps qTotal)).mpr
      (capture_uniform setup codec checks caps kemBound adversary qTotal bounded target)

/-- The ordinary joint-use game also pays its own 32-byte target identity sampler. Its entire signing/DH history is interpreted. -/
theorem game_uniform (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (caps : KemCaps) (kemBound : KemBound setup caps) (adversary : Adversary) (qTotal : Nat)
    (bounded : ∀ input, (adversary input).IsTotalQueryBound qTotal) (fallback : Forgery) :
    (PqxdhJointIdentity.game setup.joint
      (PqxdhServerAuthJointIdentityEuf.reduction setup codec checks adversary fallback)).IsTotalQueryBound
        (32 + reductionCost caps qTotal) :=
  jointGame_uniform_bound setup.joint _ _
    (fun target => reduction_uniform setup codec checks caps kemBound adversary qTotal bounded fallback target)

/-- Expanded whole-game bill: four 32-byte samplers and the declared direct/base costs of key generation and all optional KEM calls. -/
theorem expanded_game_cost (caps : KemCaps) (qTotal : Nat) :
    32 + reductionCost caps qTotal = 128 + caps.keygenUniform + caps.baseUniform * caps.keygenBase +
      qTotal * (128 + caps.encapsUniform + caps.baseUniform * caps.encapsBase +
        caps.decapsUniform + caps.baseUniform * caps.decapsBase) := by
  simp only [reductionCost, callCost, KemCaps.keygenCost, KemCaps.encapsCost, KemCaps.decapsCost, Nat.add_assoc]
  omega

/-- The actual source substitution event, its coefficient-one ordinary joint-use reduction, and the complete query ledger for that same executable reduction. The source API cap includes every attempted call and every possible reply. -/
theorem source_bound_with_resources (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (caps : KemCaps) (kemBound : KemBound setup caps) (adversary : Adversary) (qTotal qFinish : Nat)
    (totalBound : ∀ input, (adversary input).IsTotalQueryBound qTotal)
    (finishBound : ∀ input, (adversary input).IsQueryBoundP PqxdhServerAuthJointIdentityDhBudget.IsFinish qFinish)
    (fallback : Forgery) :
    𝒟[PqxdhServerAuthJointIdentityEuf.sourceBad setup codec checks adversary] {true} ≤
      PqxdhJointIdentity.advantage setup.joint (PqxdhServerAuthJointIdentityEuf.reduction setup codec checks adversary fallback) ∧
    (∀ target, (PqxdhServerAuthJointIdentityEuf.reduction setup codec checks adversary fallback target).IsQueryBoundP
      PqxdhServerAuthJointIdentityLog.IsSign 3) ∧
    (∀ target, (PqxdhServerAuthJointIdentityEuf.reduction setup codec checks adversary fallback target).IsQueryBoundP
      PqxdhServerAuthJointIdentityDhBudget.IsDh qFinish) ∧
    (∀ target, (PqxdhServerAuthJointIdentityEuf.reduction setup codec checks adversary fallback target).IsQueryBoundP
      (IsClass .uniform) (reductionCost caps qTotal)) ∧
    (PqxdhJointIdentity.game setup.joint
      (PqxdhServerAuthJointIdentityEuf.reduction setup codec checks adversary fallback)).IsTotalQueryBound
        (32 + reductionCost caps qTotal) :=
  ⟨PqxdhServerAuthJointIdentityEuf.source_bound setup codec checks adversary fallback,
    PqxdhServerAuthJointIdentityResources.reduction_signing setup codec checks adversary fallback,
    PqxdhServerAuthJointIdentityDhBudget.reduction_dh setup codec checks adversary qFinish finishBound fallback,
    reduction_uniform setup codec checks caps kemBound adversary qTotal totalBound fallback,
    game_uniform setup codec checks caps kemBound adversary qTotal totalBound fallback⟩

end BeaconcryptCore.Computational.PqxdhServerAuthJointIdentityUniformCosts

/-! Checked theorem dependencies. -/

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthJointIdentityUniformCosts.coins_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthJointIdentityUniformCosts.coins_uniform
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthJointIdentityUniformCosts.collect_decaps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthJointIdentityUniformCosts.collect_decaps
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthJointIdentityUniformCosts.prepare_decaps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthJointIdentityUniformCosts.prepare_decaps
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthJointIdentityUniformCosts.prepare_classes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthJointIdentityUniformCosts.prepare_classes
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthJointIdentityUniformCosts.auxiliary_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthJointIdentityUniformCosts.auxiliary_uniform
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthJointIdentityUniformCosts.prefix_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthJointIdentityUniformCosts.prefix_uniform
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthJointIdentityUniformCosts.prepare_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthJointIdentityUniformCosts.prepare_uniform
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthJointIdentityUniformCosts.stage_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthJointIdentityUniformCosts.stage_uniform
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthJointIdentityUniformCosts.finish_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthJointIdentityUniformCosts.finish_uniform
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthJointIdentityUniformCosts.handler_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthJointIdentityUniformCosts.handler_uniform
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthJointIdentityUniformCosts.program_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthJointIdentityUniformCosts.program_uniform
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthJointIdentityUniformCosts.phase1_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthJointIdentityUniformCosts.phase1_uniform
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthJointIdentityUniformCosts.execution_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthJointIdentityUniformCosts.execution_uniform
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthJointIdentityUniformCosts.capture_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthJointIdentityUniformCosts.capture_uniform
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthJointIdentityUniformCosts.reduction_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthJointIdentityUniformCosts.reduction_uniform
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthJointIdentityUniformCosts.game_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthJointIdentityUniformCosts.game_uniform
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthJointIdentityUniformCosts.expanded_game_cost' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthJointIdentityUniformCosts.expanded_game_cost
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthJointIdentityUniformCosts.source_bound_with_resources' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthJointIdentityUniformCosts.source_bound_with_resources
