import BeaconcryptCore.Computational.PqxdhKemControllerSource

/-!
The authentication-only controller does not erase source primitive costs. The Server prefix has one possible encapsulation and twenty-one other callback positions; Beacon owner preparation has one possible decapsulation and twelve other positions. Every rejected path remains in the bounds. Local interpretation pays the complete allowance of each reached callback, and the concrete controller's audit preserves the original primitive bill exactly.
-/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhKemControllerBounds
open PqxdhKemCoordinateController

def serverKem {Reader E : Type} : PqxdhServerRootPreparation.Query Reader E → Bool
  | .encapsulate _ => true
  | _ => false

def beaconKem {I D K X Response : Type} : PqxdhBeaconPhase2Preparation.Query I D K X Response → Bool
  | .decapsulate _ _ => true
  | _ => false

/-- Width, tag and signature checks use nine ordinary callbacks and no KEM controller request. -/
theorem server_verification {Reader E Shared : Type} (kind : Bool) (raw : Pqxdh.Bytes) :
    (PqxdhServerRootPreparation.verifyInput (Reader := Reader) (E := E) (Shared := Shared) raw).IsQueryBoundP
      (fun query => serverKem query = kind) (if kind then 0 else 9) := by
  cases kind <;> unfold PqxdhServerRootPreparation.verifyInput
  all_goals repeat' first
    | trivial
    | (rw [isQueryBoundP_query_bind_iff]; simp [serverKem])
    | intro answer; cases answer
    | split

/-- One actual encapsulation follows generation and KEM-key admission; all twelve other source callbacks remain charged, including later conversion and DH failures. -/
theorem server_prepared {Reader E Shared : Type} (kind : Bool) (verified : PqxdhServerRootPreparation.Verified Reader) :
    (PqxdhServerRootPreparation.collectVerified (E := E) (Shared := Shared) verified).IsQueryBoundP
      (fun query => serverKem query = kind) (if kind then 1 else 12) := by
  cases kind <;> unfold PqxdhServerRootPreparation.collectVerified
  all_goals simp only [OptionT.run_bind, OptionT.run_monadLift, Option.elimM, bind_map_left]
  all_goals repeat' first
    | trivial
    | (rw [isQueryBoundP_query_bind_iff]; simp [serverKem])
    | (simp only [OptionT.run_bind, OptionT.run_monadLift, Option.elimM, Option.elim_some, bind_map_left])
    | intro answer; cases answer
  all_goals simp [isQueryBoundP_map_iff, isQueryBoundP_query_iff]

/-- The complete raw Server prefix counts the actual encapsulation once, and at most twenty-one ordinary callbacks, without successful-path filtering. -/
theorem server_collect {Reader E Shared : Type} (kind : Bool) (raw : Pqxdh.Bytes) :
    (PqxdhServerRootPreparation.collect (Reader := Reader) (E := E) (Shared := Shared) raw).IsQueryBoundP
      (fun query => serverKem query = kind) (if kind then 1 else 21) := by
  cases kind <;> unfold PqxdhServerRootPreparation.collect
  · apply isQueryBoundP_bind (server_verification (Reader := Reader) (E := E) (Shared := Shared) false raw) (m := 12)
    rintro (_ | verified) _
    · trivial
    · exact server_prepared false verified
  · apply isQueryBoundP_bind (server_verification (Reader := Reader) (E := E) (Shared := Shared) true raw) (m := 1)
    rintro (_ | verified) _
    · trivial
    · exact server_prepared true verified

/-- Twelve pre-core Beacon callbacks contain exactly one possible KEM request; conversion and every early optional exit retain their actual ordering. -/
theorem beacon_collect {I D K X Response : Type} (kind : Bool)
    (identity : I) (prekey oneTime : D) (kem : K) (raw : Pqxdh.Bytes) :
    (PqxdhBeaconPhase2Preparation.collect (X := X) (Response := Response) identity prekey oneTime kem raw).IsQueryBoundP
      (fun query => beaconKem query = kind) (if kind then 1 else 11) := by
  cases kind <;> unfold PqxdhBeaconPhase2Preparation.collect
  all_goals simp only [OptionT.run_bind, OptionT.run_mk, OptionT.run_pure,
    OptionT.run_monadLift, Option.elimM, bind_map_left]
  all_goals repeat' first
    | trivial
    | (rw [isQueryBoundP_query_bind_iff]; simp [beaconKem])
    | (simp only [Option.elim_some])
    | intro answer; cases answer
  all_goals simp [isQueryBoundP_map_iff, isQueryBoundP_query_iff]

/-- Core preparation always runs its single shared-secret erasure callback and makes no further KEM request, including pin mismatch and zero-DH errors. -/
theorem beacon_after {I D K X Response : Type} (kind : Bool)
    (control : pqxdh.BeaconInitSent) (inputs : PqxdhBeaconPhase2Preparation.Inputs Response) :
    (PqxdhBeaconPhase2Preparation.afterInputs (I := I) (D := D) (K := K) (X := X) control inputs).IsQueryBoundP
      (fun query => beaconKem query = kind) (if kind then 0 else 1) := by
  cases kind <;> unfold PqxdhBeaconPhase2Preparation.afterInputs
  all_goals rw [isQueryBoundP_query_bind_iff]
  all_goals simp [beaconKem]

/-- Full active preparation retains all twelve non-KEM positions around its single possible decapsulation. -/
theorem beacon_prepare {I D K X Response : Type} (kind : Bool)
    (control : pqxdh.BeaconInitSent) (identity : I) (prekey oneTime : D) (kem : K) (raw : Pqxdh.Bytes) :
    (PqxdhBeaconPhase2Preparation.prepare (X := X) (Response := Response) control identity prekey oneTime kem raw).IsQueryBoundP
      (fun query => beaconKem query = kind) (if kind then 1 else 12) := by
  cases kind <;> unfold PqxdhBeaconPhase2Preparation.prepare
  · apply isQueryBoundP_bind (beacon_collect (X := X) (Response := Response) false identity prekey oneTime kem raw) (m := 1)
    rintro (_ | inputs) _
    · trivial
    · exact beacon_after false control inputs
  · apply isQueryBoundP_bind (beacon_collect (X := X) (Response := Response) true identity prekey oneTime kem raw) (m := 0)
    rintro (_ | inputs) _
    · trivial
    · exact beacon_after true control inputs

/-- The literal owner dispatch adds no KEM or other callback when inactive and preserves the active cap through both success and abort. -/
theorem beacon_owner {I D K X Response : Type} (kind : Bool) (raw : Pqxdh.Bytes)
    (owner : PqxdhBeaconPhase2Preparation.State I D K) :
    (PqxdhBeaconPhase2Preparation.owner (X := X) (Response := Response) raw owner).IsQueryBoundP
      (fun query => beaconKem query = kind) (if kind then 1 else 12) := by
  cases active : owner.beacon.phase with
  | initSent control prekey oneTime kem =>
      simp only [PqxdhBeaconPhase2Preparation.owner, active, bind_pure_comp, isQueryBoundP_map_iff]
      exact beacon_prepare kind control owner.beacon.identity prekey oneTime kem raw
  | _ => simp only [PqxdhBeaconPhase2Preparation.owner, active]; trivial

/-- The complete source Server computation pays actual stateful callback bills, including generation, reservation and every rejected branch. -/
theorem server_interpreted {Reader E Shared A ι : Type} {base : OracleSpec ι}
    (native : QueryImpl (PqxdhServerRootPreparation.Spec Reader E Shared) (StateT A (OracleComp base)))
    (predicate : base.Domain → Prop) [DecidablePred predicate] (qKem qOther : Nat)
    (bounded : ∀ query state, ((native query).run state).IsQueryBoundP predicate
      (if serverKem query then qKem else qOther)) (raw : Pqxdh.Bytes) (state : A) :
    ((simulateQ native (PqxdhServerRootPreparation.collect raw)).run state).IsQueryBoundP predicate
      (qKem + 21 * qOther) := by
  simpa [Fintype.sum_bool, Nat.mul_comm, Nat.add_comm] using
    FinitePartitionQueryBounds.weighted_bound serverKem
      (fun kind => if kind then qKem else qOther) (fun kind => if kind then 1 else 21)
      native predicate (PqxdhServerRootPreparation.collect raw)
      (fun kind => server_collect kind raw) bounded state

/-- Beacon interpretation charges decapsulation once and every other local callback, including DH and erasure before late rejection; the complete owner and native state remain in the computation. -/
theorem beacon_interpreted {I D K X Response A ι : Type} {base : OracleSpec ι}
    (native : QueryImpl (PqxdhBeaconPhase2Preparation.Spec I D K X Response) (StateT A (OracleComp base)))
    (predicate : base.Domain → Prop) [DecidablePred predicate] (qKem qOther : Nat)
    (bounded : ∀ query state, ((native query).run state).IsQueryBoundP predicate
      (if beaconKem query then qKem else qOther)) (raw : Pqxdh.Bytes)
    (owner : PqxdhBeaconPhase2Preparation.State I D K) (state : A) :
    ((simulateQ native (PqxdhBeaconPhase2Preparation.owner raw owner)).run state).IsQueryBoundP predicate
      (qKem + 12 * qOther) := by
  simpa [Fintype.sum_bool, Nat.mul_comm, Nat.add_comm] using
    FinitePartitionQueryBounds.weighted_bound beaconKem
      (fun kind => if kind then qKem else qOther) (fun kind => if kind then 1 else 12)
      native predicate (PqxdhBeaconPhase2Preparation.owner raw owner)
      (fun kind => beacon_owner kind raw owner) bounded state

end BeaconcryptCore.Computational.PqxdhKemControllerBounds

/-- info: 'BeaconcryptCore.Computational.PqxdhKemControllerBounds.server_verification' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhKemControllerBounds.server_verification

/-- info: 'BeaconcryptCore.Computational.PqxdhKemControllerBounds.server_prepared' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhKemControllerBounds.server_prepared

/-- info: 'BeaconcryptCore.Computational.PqxdhKemControllerBounds.server_collect' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhKemControllerBounds.server_collect

/-- info: 'BeaconcryptCore.Computational.PqxdhKemControllerBounds.beacon_collect' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhKemControllerBounds.beacon_collect

/-- info: 'BeaconcryptCore.Computational.PqxdhKemControllerBounds.beacon_after' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhKemControllerBounds.beacon_after

/-- info: 'BeaconcryptCore.Computational.PqxdhKemControllerBounds.beacon_prepare' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhKemControllerBounds.beacon_prepare

/-- info: 'BeaconcryptCore.Computational.PqxdhKemControllerBounds.beacon_owner' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhKemControllerBounds.beacon_owner

/-- info: 'BeaconcryptCore.Computational.PqxdhKemControllerBounds.server_interpreted' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhKemControllerBounds.server_interpreted

/-- info: 'BeaconcryptCore.Computational.PqxdhKemControllerBounds.beacon_interpreted' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhKemControllerBounds.beacon_interpreted
