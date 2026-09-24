import BeaconcryptCore.Computational.PqxdhServerStaticDhSource

/-!
The ordered Server prefix bills its single unavailable-static-DH call separately from its twenty-one ordinary source callback positions. Every rejected parser, freshness, allocation, generation, conversion and DH branch remains in these worst-case path bounds. Stateful implementations pay the full supplied allowance for each reached callback; no ambient primitive work is assumed free.
-/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhServerRootQueryBounds
open PqxdhServerRootPreparation PqxdhServerStaticDhSource
open PqxdhJointIdentity
open PqxdhBeaconPhase2Preparation (Word32)

def selected {Reader E : Type} : Query Reader E → Bool
  | .staticDh _ => true
  | _ => false

/-- All nine verification and parsing callback positions are ordinary source work, with no selected static-DH call. -/
theorem verification_class {Reader E Shared : Type} (kind : Bool) (raw : Pqxdh.Bytes) :
    (verifyInput (Reader := Reader) (E := E) (Shared := Shared) raw).IsQueryBoundP
      (fun query => selected query = kind) (if kind then 0 else 9) := by
  cases kind <;> unfold verifyInput
  all_goals repeat' first
    | trivial
    | (rw [isQueryBoundP_query_bind_iff]; simp [selected])
    | intro answer; cases answer
    | split

/-- Source ephemeral/KEM preparation has one static call and twelve other callback positions in their actual order. -/
theorem prepared_class {Reader E Shared : Type} (kind : Bool) (verified : Verified Reader) :
    (collectVerified (E := E) (Shared := Shared) verified).IsQueryBoundP
      (fun query => selected query = kind) (if kind then 1 else 12) := by
  cases kind <;> unfold collectVerified
  all_goals simp only [OptionT.run_bind, OptionT.run_monadLift, Option.elimM, bind_map_left]
  all_goals repeat' first
    | trivial
    | (rw [isQueryBoundP_query_bind_iff]; simp [selected])
    | (simp only [OptionT.run_bind, OptionT.run_monadLift, Option.elimM, Option.elim_some, bind_map_left])
    | intro answer; cases answer
  all_goals simp [isQueryBoundP_map_iff, isQueryBoundP_query_iff]

/-- The complete raw prefix retains all twenty-one ordinary callbacks and its one selected static call, including early failures. -/
theorem collect_class {Reader E Shared : Type} (kind : Bool) (raw : Pqxdh.Bytes) :
    (collect (Reader := Reader) (E := E) (Shared := Shared) raw).IsQueryBoundP
      (fun query => selected query = kind) (if kind then 1 else 21) := by
  cases kind <;> unfold collect
  · apply isQueryBoundP_bind (verification_class (Reader := Reader) (E := E) (Shared := Shared) false raw) (m := 12)
    rintro (_ | verified) _
    · trivial
    · exact prepared_class false verified
  · apply isQueryBoundP_bind (verification_class (Reader := Reader) (E := E) (Shared := Shared) true raw) (m := 1)
    rintro (_ | verified) _
    · trivial
    · exact prepared_class true verified

set_option backward.isDefEq.respectTransparency false in
/-- The complete source prefix pays every actual ordinary callback and the retained selected-call instrumentation, preserving all reached states. -/
theorem interpreted_bound {joint : Primitives} (domain : PublicDomain joint)
    {Reader E A ι : Type} {target : OracleSpec ι}
    (aux : QueryImpl (Spec Reader E Unit) (StateT A (OracleComp target)))
    (visit : Word32 → StateT A (OracleComp target) Unit)
    (predicate : target.Domain → Prop) [DecidablePred predicate] (qAux qVisit : Nat)
    (auxBound : ∀ query state, ((aux query).run state).IsQueryBoundP predicate qAux)
    (visitBound : ∀ input state, ((visit input).run state).IsQueryBoundP predicate qVisit)
    (raw : Pqxdh.Bytes) (state : A) :
    ((simulateQ (prefixImpl domain aux visit) (collect raw)).run state).IsQueryBoundP
      predicate (21 * qAux + qVisit) := by
  have step (query : (Spec Reader E PeerEncoding).Domain) (before : A) :
      ((prefixImpl domain aux visit query).run before).IsQueryBoundP predicate
        (if selected query then qVisit else qAux) := by
    cases query <;> simp only [prefixImpl, selected, Bool.false_eq_true, if_false, if_true]
    all_goals first | exact auxBound _ before | simpa only [bind_pure_comp, StateT.run_map, isQueryBoundP_map_iff] using visitBound _ before
  simpa [Fintype.sum_bool, Nat.mul_comm, Nat.add_comm] using
    FinitePartitionQueryBounds.weighted_bound selected
      (fun kind => if kind then qVisit else qAux) (fun kind => if kind then 1 else 21)
      (prefixImpl domain aux visit) predicate (collect raw)
      (fun kind => collect_class kind raw) step state

end BeaconcryptCore.Computational.PqxdhServerRootQueryBounds

/-- info: 'BeaconcryptCore.Computational.PqxdhServerRootQueryBounds.verification_class' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerRootQueryBounds.verification_class
/-- info: 'BeaconcryptCore.Computational.PqxdhServerRootQueryBounds.prepared_class' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerRootQueryBounds.prepared_class
/-- info: 'BeaconcryptCore.Computational.PqxdhServerRootQueryBounds.collect_class' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerRootQueryBounds.collect_class
/-- info: 'BeaconcryptCore.Computational.PqxdhServerRootQueryBounds.interpreted_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerRootQueryBounds.interpreted_bound
