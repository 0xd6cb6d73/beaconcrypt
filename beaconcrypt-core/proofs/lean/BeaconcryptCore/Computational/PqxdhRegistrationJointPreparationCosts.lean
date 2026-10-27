-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRegistrationJointPreparation

/-! Exact service classes and complete interpreted primitive bills for the actual registration preparation. Deterministic source/codec work remains real local work, separate from oracle counts. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhRegistrationJointPreparationCosts
open PqxdhRefinement PqxdhJointIdentity PqxdhJointGapDh PqxdhServerAuthExperiment
open PqxdhRegistrationJointPreparation PqxdhServerAuthSourceCosts
variable {ι I D K X Reader Response Result KemSK : Type} {baseSpec : OracleSpec ι}

inductive Kind where
  | decapsulate
  | staticDh
  | localCall
  deriving DecidableEq

instance : Fintype Kind := ⟨{.decapsulate, .staticDh, .localCall}, by
  intro kind
  cases kind <;> simp⟩

def classify : (PqxdhBeaconPhase2Preparation.Spec I D K X Response).Domain → Kind
  | .decapsulate _ _ => .decapsulate
  | .dhIdentity _ _ => .staticDh
  | _ => .localCall

def cap : Kind → Nat
  | .decapsulate | .staticDh => 1
  | .localCall => 13

def uniformCost (caps : KemCaps) : Kind → Nat
  | .decapsulate => caps.decapsCost
  | _ => 0

set_option maxHeartbeats 1000000 in
/-- Each optional source collector attempts at most one KEM decapsulation and one converted-identity DH. The local class retains the full twelve-callback conservative allowance. -/
theorem collect_classes (identity : I) (prekey oneTime : D) (key : K) (raw : Pqxdh.Bytes) (kind : Kind) :
    (PqxdhBeaconPhase2Preparation.collect (X := X) (Response := Response) identity prekey oneTime key raw).IsQueryBoundP
      (fun query => classify query = kind) (if kind = .localCall then 12 else 1) := by
  cases kind
  case localCall => exact (PqxdhBeaconPhase2Preparation.collect_bound identity prekey oneTime key raw).isQueryBoundP
  all_goals unfold PqxdhBeaconPhase2Preparation.collect
  all_goals simp only [OptionT.run_bind, OptionT.run_mk, OptionT.run_pure, OptionT.run_monadLift,
    Option.elimM, bind_map_left]
  all_goals repeat' first
    | trivial
    | (rw [isQueryBoundP_query_bind_iff]; refine ⟨by simp [classify], ?_⟩)
    | (fail_if_no_progress simp only [Option.elim_some])
    | intro answer; cases answer

/-- Core admission and erasure add no service call. Every source branch retains at most one logical request to each private service and the full local callback allowance. -/
theorem prepare_classes (control : beaconcrypt_core.pqxdh.BeaconInitSent)
    (identity : I) (prekey oneTime : D) (key : K) (raw : Pqxdh.Bytes) (kind : Kind) :
    (PqxdhBeaconPhase2Preparation.prepare (X := X) (Response := Response) control identity prekey oneTime key raw).IsQueryBoundP
      (fun query => classify query = kind) (cap kind) := by
  cases kind
  case localCall => exact (PqxdhBeaconPhase2Preparation.prepare_bound control identity prekey oneTime key raw).isQueryBoundP
  all_goals unfold PqxdhBeaconPhase2Preparation.prepare
  all_goals refine isQueryBoundP_bind (n := 1) (m := 0) (collect_classes identity prekey oneTime key raw _) ?_
  all_goals rintro (_ | input) _
  all_goals first | trivial | simp [PqxdhBeaconPhase2Preparation.afterInputs, classify]

/-- A callback is charged for all real KEM direct and base randomness; deterministic callbacks have no uniform-oracle request but retain their local work. -/
theorem source_step_uniform (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (caps : KemCaps) (bounded : KemBound setup caps) (query : (NativeSpec KemSK Response).Domain) :
    (PqxdhRegistrationSchedule.preparation setup codec query).IsTotalQueryBound
      (uniformCost caps (classify query)) := by
  cases query <;> try trivial
  exact decaps_uniform setup caps bounded _ _

/-- Private analysis histories preserve the exact uniform query bill of the same actual callback. -/
theorem annotated_step_uniform (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (caps : KemCaps) (bounded : KemBound setup caps) (identityIndex kemIndex : Nat)
    (query : (NativeSpec KemSK Response).Domain) (pool : Pool KemSK) :
    ((annotated setup codec identityIndex kemIndex query).run pool).IsTotalQueryBound
      (uniformCost caps (classify query)) := by
  have bounded := source_step_uniform setup codec caps bounded query
  rw [← annotated_query_erase setup codec identityIndex kemIndex query pool,
    IsTotalQueryBound, isQueryBound_map_iff] at bounded
  exact bounded


/-- The finite service partition charges exactly the one complete optional-decapsulation allowance. -/
theorem uniform_bill (caps : KemCaps) : (∑ kind, uniformCost caps kind * cap kind) = caps.decapsCost := by
  change (∑ kind ∈ ({.decapsulate, .staticDh, .localCall} : Finset Kind),
    uniformCost caps kind * cap kind) = _
  simp [uniformCost, cap]

/-- Full preparation retains all callbacks and histories while paying every declared KEM direct and interpreted base draw on the single possible decapsulation. -/
theorem annotated_prepare_uniform (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (caps : KemCaps) (bounded : KemBound setup caps) (identityIndex kemIndex : Nat)
    (control : beaconcrypt_core.pqxdh.BeaconInitSent) (seed : IdentitySeed) (prekey oneTime : ScalarBytes)
    (key : PqxdhKemIndCca.MlKem768PublicKey × KemSK) (raw : Pqxdh.Bytes) (pool : Pool KemSK) :
    ((simulateQ (annotated setup codec identityIndex kemIndex)
      (PqxdhBeaconPhase2Preparation.prepare control seed prekey oneTime key raw)).run pool).IsTotalQueryBound caps.decapsCost := by
  have bound := FinitePartitionQueryBounds.weighted_bound classify (uniformCost caps) cap
    (annotated setup codec identityIndex kemIndex) (fun _ => True)
    (PqxdhBeaconPhase2Preparation.prepare control seed prekey oneTime key raw)
    (prepare_classes control seed prekey oneTime key raw)
    (fun query state => (annotated_step_uniform setup codec caps bounded identityIndex kemIndex query state).isQueryBoundP) pool
  simpa only [uniform_bill, isQueryBoundP_true_iff] using bound

/-- The actual indexed client inherits the same complete source bill, under its exact private slot ownership relation. No ambient work is omitted. -/
theorem prepare_uniform (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (caps : KemCaps) (bounded : KemBound setup caps) (identityIndex kemIndex : Nat)
    (control : beaconcrypt_core.pqxdh.BeaconInitSent) (seed : IdentitySeed) (prekey oneTime : ScalarBytes)
    (key : PqxdhKemIndCca.MlKem768PublicKey × KemSK) (raw : Pqxdh.Bytes) (pool : Pool KemSK)
    (identityOwned : pool.1.seeds[identityIndex]? = some seed)
    (kemOwned : pool.2.keys[kemIndex]? = some key) :
    ((simulateQ (interpreted setup codec)
      (PqxdhBeaconPhase2Preparation.prepare control (PqxdhRegistrationJointBundle.identityMap setup identityIndex seed)
        prekey oneTime (PqxdhRegistrationJointBundle.keyMap kemIndex key) raw)).run pool).IsTotalQueryBound
      (caps.decapsUniform + caps.baseUniform * caps.decapsBase) := by
  rw [prepare_source setup codec identityIndex kemIndex seed prekey oneTime key control raw pool identityOwned kemOwned]
  exact annotated_prepare_uniform setup codec caps bounded identityIndex kemIndex control seed prekey oneTime key raw pool


/-- Only the two reached private service operations are protocol preparation requests; every other service capability is in the remaining class. -/
def serviceClass : (PqxdhLiveKemBirth.Spec KemSK).Domain → Kind
  | .inr (.inr (.decapsulate _ _)) => .decapsulate
  | .inl (.inr (.service _ (.staticDh _))) => .staticDh
  | _ => .localCall

set_option backward.isDefEq.respectTransparency false in
/-- Every compiled source callback emits only its own optional single service operation, with all unrelated capabilities absent. -/
theorem compiler_step (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (query : (Spec Response).Domain) (kind : Kind) :
    (compiler setup codec query).IsQueryBoundP (fun request => serviceClass (KemSK := KemSK) request = kind)
      (if classify query = kind ∧ kind ≠ .localCall then 1 else 0) := by
  cases query <;> cases kind <;> simp [compiler, classify, serviceClass, isQueryBoundP_query_iff]


/-- No preparation client can create or reveal service owners, sign, or request local coins through this compiler. Every emitted query belongs to its KEM or static-DH service. -/
theorem compiler_other_free (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (program : OracleComp (Spec Response) Result) :
    (simulateQ (compiler setup codec) program).IsQueryBoundP
      (fun request => serviceClass (KemSK := KemSK) request = .localCall) 0 := by
  induction program using OracleComp.inductionOn with
  | pure value => trivial
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query]
      apply isQueryBoundP_bind (n := 0) (m := 0)
      · simpa only [ne_eq, not_true_eq_false, and_false, ite_false] using compiler_step setup codec query .localCall
      · exact fun reply _ => ih reply

def serviceCap : Kind → Nat
  | .decapsulate | .staticDh => 1
  | .localCall => 0

/-- The executable compiled preparation has at most one KEM request, one joint identity-DH request and zero requests to all other service capabilities. Counts include failed attempts and every possible typed reply. -/
theorem compiler_prepare_classes (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (control : beaconcrypt_core.pqxdh.BeaconInitSent) (identity : PqxdhRegistrationJointBundle.Identity)
    (prekey oneTime : ScalarBytes) (key : PqxdhRegistrationJointBundle.Key) (raw : Pqxdh.Bytes) (kind : Kind) :
    (simulateQ (compiler setup codec)
      (PqxdhBeaconPhase2Preparation.prepare control identity prekey oneTime key raw)).IsQueryBoundP
      (fun request => serviceClass (KemSK := KemSK) request = kind) (serviceCap kind) := by
  by_cases localKind : kind = .localCall
  · subst kind
    exact compiler_other_free setup codec _
  · have same : cap kind = serviceCap kind := by cases kind <;> simp_all [cap, serviceCap]
    have source := prepare_classes (X := Nat) (Response := Response) control identity prekey oneTime key raw kind
    rw [same] at source
    apply source.simulateQ_of_step
    · intro query selected
      simpa [selected, localKind] using compiler_step setup codec query kind
    · intro query absent
      simpa only [absent, false_and, ite_false] using compiler_step setup codec query kind


end BeaconcryptCore.Computational.PqxdhRegistrationJointPreparationCosts

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointPreparationCosts.collect_classes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointPreparationCosts.collect_classes

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointPreparationCosts.prepare_classes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointPreparationCosts.prepare_classes

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointPreparationCosts.source_step_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointPreparationCosts.source_step_uniform

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointPreparationCosts.annotated_step_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointPreparationCosts.annotated_step_uniform

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointPreparationCosts.uniform_bill' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointPreparationCosts.uniform_bill

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointPreparationCosts.annotated_prepare_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointPreparationCosts.annotated_prepare_uniform

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointPreparationCosts.prepare_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointPreparationCosts.prepare_uniform

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointPreparationCosts.compiler_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointPreparationCosts.compiler_step

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointPreparationCosts.compiler_other_free' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointPreparationCosts.compiler_other_free

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointPreparationCosts.compiler_prepare_classes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointPreparationCosts.compiler_prepare_classes
