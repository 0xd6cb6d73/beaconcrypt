-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRegistrationJointKemPreBills

/-! The exact constructed ordinary KEM adversary has explicit pre/post uniform, base and logical-decapsulation caps. The proof annotation only restricts impossible saved continuation values and preserves every actual source execution. -/
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhRegistrationJointKemReductionBills
open PqxdhKemIndCca PqxdhRegistrationJointKemChallenge PqxdhRegistrationJointKemPostBills
open PqxdhRegistrationJointKemCommands (SourceSpec Budget)
open PqxdhServerAuthSourceCosts (KemCaps KemBound)
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response A : Type}

/-- Forward support annotation leaves every source prephase resource bound unchanged at every public challenger key. -/
theorem annotated_bound (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (checks : PqxdhServerAuthExperiment.Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes)
    (client : OracleComp (SourceSpec KemSK) Bool) (runtime : A)
    (count : Nat) (selected : Fin (count + 1)) (occurrence : Nat) (target : MlKem768PublicKey)
    (predicate : (MlKemCCAOracleSpec baseSpec).Domain → Prop) [DecidablePred predicate] (cap : Nat)
    (bounded : (pre setup codec checks ensureInit supplied client runtime count selected occurrence target).IsQueryBoundP predicate cap) :
    (PqxdhRegistrationJointKemCertified.annotatedPre setup codec checks ensureInit supplied client runtime count selected occurrence target).IsQueryBoundP predicate cap := by
  rw [← PqxdhRegistrationJointKemCertified.prefix_erase setup codec checks ensureInit supplied client runtime count selected occurrence target] at bounded
  exact (isQueryBoundP_map_iff _ _ _).mp bounded

set_option backward.isDefEq.respectTransparency false in
/-- The exact adversary of the source-cut IND-CCA equality is bounded on every prechallenge key, every valid saved context and every postchallenge reply. The separate phase caps conservatively sum to at most twice qFinish logical requests; the original source itself retains qFinish. -/
theorem adversary_bound (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (checks : PqxdhServerAuthExperiment.Checks)
    (caps : KemCaps) (bounded : KemBound setup caps) (ensureInit : StateT A ProbComp Bool)
    (qInit : Nat) (initBound : ∀ runtime, (ensureInit.run runtime).IsTotalQueryBound qInit)
    (supplied : Option Pqxdh.Bytes) (client : OracleComp (SourceSpec KemSK) Bool) (budget : Budget)
    (certified : ∀ source, client.IsQueryBoundP
      (fun query => PqxdhRegistrationJointRevealCosts.sourceKind (KemSK := KemSK) query = source) (budget source))
    (runtime : A) (count : Nat) (selected : Fin (count + 1)) (occurrence : Nat) :
    (PqxdhRegistrationJointKemCertified.adversary setup codec checks ensureInit supplied client runtime count selected occurrence).MakesAtMostQueries
      ((qInit + if supplied.isNone then 32 else 0) +
        (caps.keygenCost * count + uniformCap caps (budget (.inl 1)) (budget (.inl 5))
          (PqxdhRegistrationJointOpenUniform.total caps budget) (budget (.inl 3))))
      (caps.decapsBase * budget (.inl 5)) (budget (.inl 5))
      (uniformCap caps (budget (.inl 1)) (budget (.inl 5))
        (PqxdhRegistrationJointOpenUniform.total caps budget) (budget (.inl 3)))
      (caps.decapsBase * budget (.inl 5)) (budget (.inl 5)) := by
  constructor
  · intro target
    refine ⟨?_, ?_, ?_⟩
    · exact annotated_bound setup codec checks ensureInit supplied client runtime count selected occurrence target _ _
        (PqxdhRegistrationJointKemPreBills.uniform setup codec checks caps bounded ensureInit qInit initBound
          supplied client budget certified runtime count selected occurrence target)
    · exact annotated_bound setup codec checks ensureInit supplied client runtime count selected occurrence target _ _
        (PqxdhRegistrationJointKemPreBills.base setup codec checks caps bounded ensureInit supplied client
          budget certified runtime count selected occurrence target)
    · exact annotated_bound setup codec checks ensureInit supplied client runtime count selected occurrence target _ _
        (PqxdhRegistrationJointKemPreBills.decapsulations setup codec checks caps bounded ensureInit supplied client
          budget certified runtime count selected occurrence target)
  · intro transcript candidate
    have bills := adversary_post setup codec checks caps bounded ensureInit supplied client runtime count selected occurrence
      budget certified transcript candidate
    exact ⟨bills.uniform, bills.base, bills.decaps⟩

end BeaconcryptCore.Computational.PqxdhRegistrationJointKemReductionBills

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemReductionBills.annotated_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemReductionBills.annotated_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemReductionBills.adversary_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemReductionBills.adversary_bound
