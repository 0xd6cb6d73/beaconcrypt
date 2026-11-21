-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhDeploymentPublicationSuppression

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true

namespace BeaconcryptCore.Computational.PqxdhDeploymentPublicationSuppressionFreshness
open PqxdhJointIdentity PqxdhJointGapDh PqxdhServerAuthExperiment PqxdhEd25519EufCma
open PqxdhDeploymentPublicationSuppression PqxdhBeaconPhase1Publication
open PqxdhRegistrationJointSigningTranscript (messagesAt)
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}

def Fresh (target : Target) (pool : PqxdhDynamicIdentityPool.SourceState) : Prop :=
  target.message ∉ messagesAt target.identityIndex pool.transcript

/-- Once a call selected its target, later calls cannot change the selected capability or message. -/
theorem next_fixed (selection : Selection) (prepared : Option Target) (armed : selection.pending = none) :
    selection.next prepared = selection := by
  simp [Selection.next, Selection.advance, armed]

/-- The selected prepared call performs no signing or writing and retains its complete earlier identity pool. -/
theorem after_selected (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (index : Nat)
    (owner : PqxdhRegistrationSchedule.Owner KemSK) (generated : Option ScalarBytes)
    (pool : PqxdhDynamicIdentityPool.SourceState) (selection : Selection) (target : Target)
    (selected : selection.pending = some 0)
    (prepared : nativeCurrent setup index owner generated = some target) :
    after setup codec index owner generated pool selection =
      (((none, owner), pool), ⟨none, some target⟩) := by
  simp only [after, prepared, Selection.next, Selection.advance, selected, ite_true, Selection.blocks,
    beq_self_eq_true]

/-- Every later prepared attempt preserves freshness of the captured one-time message. Matching tuples skip the whole block; distinct tuples cannot issue its canonically tagged message. -/
theorem after_fresh (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (index : Nat)
    (owner : PqxdhRegistrationSchedule.Owner KemSK) (generated : Option ScalarBytes)
    (pool : PqxdhDynamicIdentityPool.SourceState) (selection : Selection) (target : Target)
    (armed : selection.pending = none) (captured : selection.target = some target) (fresh : Fresh target pool) :
    Fresh target (after setup codec index owner generated pool selection).1.2 := by
  rw [show after setup codec index owner generated pool selection =
    if selection.blocks (nativeCurrent setup index owner generated) then
      (((none, owner), pool), selection)
    else (PqxdhRegistrationJointBundle.after setup codec index owner generated pool, selection) by
      simp only [after, next_fixed selection _ armed]]
  split
  · exact fresh
  · rename_i notBlocked
    cases ready : prepare owner generated with
    | none => simpa only [PqxdhRegistrationJointBundle.after, ready] using fresh
    | some prepared =>
      have notSame : (⟨index, setup.dh.publicKey prepared.oneTime⟩ : Target) ≠ target := by
        intro same
        apply notBlocked
        simp only [nativeCurrent, current, ready, Option.map_some,
          PqxdhRegistrationSchedule.projection, Selection.blocks, captured, same, beq_self_eq_true]
      unfold Fresh at fresh ⊢
      rw [PqxdhRegistrationJointBundle.after_history setup codec index owner generated pool prepared ready,
        PqxdhRegistrationJointSigningTranscript.signed]
      by_cases sameIndex : index = target.identityIndex
      · rw [ite_eq_left sameIndex]
        have different : setup.dh.publicKey prepared.oneTime ≠ target.oneTime := by
          intro sameKey
          apply notSame
          cases target
          simp_all
        have absent : target.message ∉ PqxdhRegistrationJointIssuedAttempts.messages
            ⟨setup.dh.publicKey prepared.prekey, setup.dh.publicKey prepared.oneTime, prepared.kem.1⟩ := by
          have unissued : ¬ ∃ tuple ∈ ([⟨setup.dh.publicKey prepared.prekey,
              setup.dh.publicKey prepared.oneTime, prepared.kem.1⟩] : List Phase1KeyTuple), target.oneTime = tuple.oneTime := by
            simpa only [List.mem_singleton, exists_eq_left] using Ne.symm different
          have notMember := (PqxdhRegistrationJointIssuedAttempts.oneTime_member target.oneTime
            [⟨setup.dh.publicKey prepared.prekey, setup.dh.publicKey prepared.oneTime, prepared.kem.1⟩]).not.mpr unissued
          simpa only [PqxdhRegistrationJointIssuedAttempts.history, List.flatMap_cons,
            List.flatMap_nil, List.append_nil, Target.message] using notMember
        simpa only [List.mem_append, not_or] using And.intro fresh absent
      · simpa only [ite_eq_right sameIndex, List.append_nil] using fresh

end BeaconcryptCore.Computational.PqxdhDeploymentPublicationSuppressionFreshness

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentPublicationSuppressionFreshness.next_fixed' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentPublicationSuppressionFreshness.next_fixed

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentPublicationSuppressionFreshness.after_selected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentPublicationSuppressionFreshness.after_selected

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentPublicationSuppressionFreshness.after_fresh' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentPublicationSuppressionFreshness.after_fresh
