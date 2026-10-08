import BeaconcryptCore.Computational.PqxdhRegistrationJointBeaconFinishOnceOwners
import BeaconcryptCore.Computational.PqxdhRegistrationJointKemRootExpandCount

/-!
# Grouped Beacon finishes on the challenge marker (item 2, stage T, marked finishes)

In the services skeleton of stage S1b a grouped Beacon finish reads a hidden value only if the decapsulation handle of its prepared root is the challenge marker (`PqxdhRegistrationJointKemPostSkeleton.groupStep`); a known decapsulation result reads the public table. This module counts those requests by their handle instead of by their kind:

- `markedGroup` is the grouped finish request whose prepared root carries the challenge marker, and `skelImpl_marked` refines stage S2's `skelImpl_hidden`: every native step of the skeleton makes at most one hidden read, and only on such a request.
- `collect_shared` and `prepare_shared` follow the decapsulation handle through the Beacon preparation (`PqxdhBeaconPhase2Shared.collect` and `prepare`): the handle of a prepared root is a reply of the decapsulation request for the owner's KEM handle, for every interpreter.
- `groupedOwner_marked`: the marked preparation (`PqxdhRegistrationJointBeaconOpaqueFinish.markedPreparation`) answers with the challenge marker only for the KEM handle with the selected creation index, so a grouped finish of an owner makes a marked request only if the owner is in phase `initSent` with that index, and then at most one (`awaits`); `groupedClient_marked` lifts this to the source requests of the grouped client (`finishMark`).

These are structural facts about the source programs; they charge nothing.
-/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc

set_option autoImplicit false
set_option maxRecDepth 100000

namespace BeaconcryptCore.Computational.PqxdhRegistrationJointBeaconFinishOnce

open PqxdhServerAuthExperiment PqxdhJointIdentity
open PqxdhRegistrationJointGeneratedFinish (EncodedEntry)
open PqxdhRegistrationJointKemPostSkeleton
open PqxdhRegistrationJointKemRootExpand (HiddenN HiddenC hiddenN_bind hiddenN_table hiddenN_game hiddenN_pure
  hiddenN_mono hiddenN_group hiddenC_liftT skelImpl_hidden groupRequest?)
open PqxdhRegistrationJointKemRomSplit (query_free query_one simulate_free)

/-! ### The decapsulation handle through the Beacon preparation -/

section Flow

variable {I D K X Response Shared ι : Type} {spec : OracleSpec.{0, 0} ι}

/-- The handle of a collected root is a reply of the decapsulation request for the owner's KEM handle, for every interpreter. -/
theorem collect_shared (handler : QueryImpl (PqxdhBeaconPhase2Shared.Spec I D K X Response Shared) (OracleComp spec))
    (good : Shared → Prop) (identity : I) (prekey oneTime : D) (kem : K) (raw : Pqxdh.Bytes)
    (replies : ∀ ciphertext, ∀ reply ∈ support (handler (.decapsulate ciphertext kem)), ∀ shared, reply = some shared →
      good shared) :
    ∀ result ∈ support (simulateQ handler (PqxdhBeaconPhase2Shared.collect identity prekey oneTime kem raw)),
      ∀ inputs, result = some inputs → good inputs.secrets.shared := by
  intro result member inputs found
  subst found
  simp only [PqxdhBeaconPhase2Shared.collect, OptionT.run_bind, OptionT.run_mk, OptionT.run_pure,
    OptionT.run_monadLift, Option.elimM, simulateQ_bind, simulateQ_spec_query, mem_support_bind_iff] at member
  repeat' (
    obtain ⟨_ | _, _, member⟩ := member <;>
    simp only [Option.elim, simulateQ_pure, simulateQ_bind, simulateQ_spec_query, simulateQ_map, support_pure,
      Set.mem_singleton_iff, mem_support_bind_iff, support_map, Set.mem_image, reduceCtorEq,
      Option.some.injEq] at member)
  subst member
  exact replies _ _ (by assumption) _ rfl

/-- The handle of a prepared root is a reply of the decapsulation request for the owner's KEM handle, for every interpreter. -/
theorem prepare_shared (handler : QueryImpl (PqxdhBeaconPhase2Shared.Spec I D K X Response Shared) (OracleComp spec))
    (good : Shared → Prop) (control : beaconcrypt_core.pqxdh.BeaconInitSent) (identity : I) (prekey oneTime : D) (kem : K)
    (raw : Pqxdh.Bytes)
    (replies : ∀ ciphertext, ∀ reply ∈ support (handler (.decapsulate ciphertext kem)), ∀ shared, reply = some shared →
      good shared) :
    ∀ result ∈ support (simulateQ handler (PqxdhBeaconPhase2Shared.prepare control identity prekey oneTime kem raw)),
      ∀ prepared, result = some prepared → good prepared.root.shared := by
  intro result member prepared found
  unfold PqxdhBeaconPhase2Shared.prepare at member
  rw [simulateQ_bind, mem_support_bind_iff] at member
  obtain ⟨inputs, collected, member⟩ := member
  cases inputs with
  | none =>
      simp only [simulateQ_pure, support_pure, Set.mem_singleton_iff] at member
      rw [member] at found
      cases found
  | some inputs =>
      simp only [PqxdhBeaconPhase2Shared.afterInputs, simulateQ_bind, simulateQ_spec_query, simulateQ_pure,
        mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at member
      obtain ⟨_, -, member⟩ := member
      rw [member] at found
      cases admitted : PqxdhBeaconPhase2Shared.admitted control inputs with
      | none => simp [admitted] at found
      | some metadata =>
          simp only [admitted, Option.map_some, Option.some.injEq] at found
          subst found
          exact collect_shared handler good identity prekey oneTime kem raw replies _ collected inputs rfl

end Flow

/-! ### Marked grouped finishes -/

section Marked

variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response V : Type}

/-- The grouped Beacon finish request whose prepared root carries the challenge marker. -/
def markedGroup : (GSpec KemSK Response).Domain → Bool
  | .inr pending => match pending.root.shared with
    | .challenge => true
    | .known _ => false
  | .inl _ => false

/-- Every native step of the skeleton makes at most one hidden read, and only on a grouped finish request with the challenge marker. -/
theorem skelImpl_marked (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (identityIndex : Nat) (publicIdentity : PublicIdentity) (services : Services V Response)
    (query : (GSpec KemSK Response).Domain) :
    HiddenC (skelImpl setup codec checks identityIndex publicIdentity services query)
      (if markedGroup query = true then 1 else 0) := by
  rcases query with query | pending
  · simpa [markedGroup, groupRequest?] using
      skelImpl_hidden setup codec checks identityIndex publicIdentity services (.inl query)
  · cases marker : pending.root.shared with
    | challenge =>
        simpa [markedGroup, groupRequest?, marker] using
          skelImpl_hidden setup codec checks identityIndex publicIdentity services (.inr pending)
    | known secret =>
        simp only [markedGroup, marker, Bool.false_eq_true, ite_false]
        refine hiddenC_liftT ?_
        unfold groupStep
        split
        · rw [marker]
          exact hiddenN_bind (a := 0) (b := 0) (hiddenN_table _) fun _ => hiddenN_game _
        · exact hiddenN_pure _

/-- A grouped finish of an owner makes a request with the challenge marker only if the owner is in phase `initSent` with the selected KEM creation index, and then at most one. -/
theorem groupedOwner_marked (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (selected : Nat)
    (challenge : PqxdhKemIndCca.MlKem768Ciphertext) (raw : Pqxdh.Bytes) (state : PqxdhRegistrationJointBundle.Owner) :
    (simulateQ (groupedCompiler setup codec selected challenge) (groupedOwner (Response := Response) raw state)).IsQueryBoundP
      (fun query => markedGroup (KemSK := KemSK) query = true) (if awaits selected state then 1 else 0) := by
  have pool : ∀ query, (groupedCompiler (KemSK := KemSK) setup codec selected challenge (.inl query)).IsQueryBoundP
      (fun query => markedGroup (KemSK := KemSK) query = true) 0 := fun query =>
    simulate_free (groupedPoolLift (KemSK := KemSK) (Response := Response)) _
      (fun query => query_free _ _ (by simp [markedGroup])) _
  by_cases holds : awaits selected state = true
  · simp only [holds, ite_true]
    refine IsQueryBoundP.simulateQ_of_step
      (PqxdhRegistrationJointKemRomSplit.groupedOwner_bound raw state) (fun query owner => ?_) (fun query owner => ?_)
    · rcases query with query | query
      · simp [PqxdhRegistrationJointKemRomSplit.ownerGroup] at owner
      · exact query_one _ _
    · rcases query with query | query
      · exact pool query
      · simp [PqxdhRegistrationJointKemRomSplit.ownerGroup] at owner
  · simp only [Bool.not_eq_true] at holds
    simp only [holds, Bool.false_eq_true, ite_false]
    unfold groupedOwner
    split
    · rename_i control prekey oneTime kem active
      have other : kem.2 ≠ selected := by
        intro same
        simp [awaits, active, same] at holds
      rw [simulateQ_bind]
      refine isQueryBoundP_bind (n := 0) (m := 0) ?_ fun prepared reached => ?_
      · rw [← QueryImpl.simulateQ_compose]
        exact simulate_free _ _ (fun query => by
          rw [QueryImpl.apply_compose, simulateQ_spec_query]
          exact pool query) _
      · cases prepared with
        | none => trivial
        | some prepared =>
            rw [← QueryImpl.simulateQ_compose] at reached
            have known := prepare_shared _ (fun shared => shared ≠ .challenge) control state.beacon.identity prekey oneTime
              kem raw (fun ciphertext reply member shared found => by
                rw [QueryImpl.apply_compose, simulateQ_spec_query] at member
                have inner := simulate_support _ _ member
                simp only [PqxdhRegistrationJointBeaconOpaqueFinish.markedPreparation, support_map] at inner
                obtain ⟨answer, -, rfl⟩ := inner
                simp only [PqxdhRegistrationJointBeaconOpaqueFinish.toHandle, other, false_and, decide_false,
                  Bool.false_eq_true, ite_false] at found
                cases answer with
                | none => cases found
                | some answer =>
                    simp only [Option.map_some, Option.some.injEq] at found
                    rw [← found]
                    exact fun absurd => by cases absurd)
              _ reached prepared rfl
            simp only [simulateQ_bind, simulateQ_spec_query, simulateQ_pure]
            refine isQueryBoundP_bind (n := 0) (m := 0) ?_ fun _ _ => trivial
            refine query_free _ _ ?_
            cases marker : prepared.root.shared with
            | challenge => exact absurd marker known
            | known secret => simp [markedGroup, marker]
    · trivial

/-- Every source request of the grouped client makes a request with the challenge marker only if it is a Beacon finish of an owner in phase `initSent` with the selected KEM creation index, and then at most one. -/
theorem groupedClient_marked (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (selected : Nat)
    (challenge : PqxdhKemIndCca.MlKem768Ciphertext) (query : (PqxdhRegistrationJointRevealSchedule.Spec KemSK).Domain)
    (owners : List EncodedEntry) :
    ((groupedClient setup codec selected challenge query).run owners).IsQueryBoundP
      (fun query => markedGroup (KemSK := KemSK) (Response := Response) query = true)
      (match FinishAt query with
        | some request => finishMark selected owners request.1
        | none => 0) := by
  have lifted : ∀ {α : Type} (work : PqxdhRegistrationJointServiceSchedule.Client KemSK Response α),
      ((liftGrouped work).run owners).IsQueryBoundP
        (fun query => markedGroup (KemSK := KemSK) (Response := Response) query = true) 0 := by
    intro _ work
    exact simulate_free groupedLift _ (fun query => query_free _ _ (by simp [markedGroup])) _
  rcases query with (coin | request) | read
  · exact lifted _
  · cases request with
    | finish address raw =>
        simp only [groupedClient, groupedFinish, StateT.run, FinishAt, finishMark]
        cases found : owners[address]? with
        | none => trivial
        | some entry =>
            simp only []
            rw [isQueryBoundP_map_iff]
            exact groupedOwner_marked setup codec selected challenge raw entry.2.2
    | _ => exact lifted _
  · exact lifted _

end Marked

end BeaconcryptCore.Computational.PqxdhRegistrationJointBeaconFinishOnce

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointBeaconFinishOnce.collect_shared' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointBeaconFinishOnce.collect_shared

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointBeaconFinishOnce.prepare_shared' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointBeaconFinishOnce.prepare_shared

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointBeaconFinishOnce.skelImpl_marked' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointBeaconFinishOnce.skelImpl_marked

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointBeaconFinishOnce.groupedOwner_marked' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointBeaconFinishOnce.groupedOwner_marked

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointBeaconFinishOnce.groupedClient_marked' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointBeaconFinishOnce.groupedClient_marked
