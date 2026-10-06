-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRegistrationJointKemSavedBills

/-! The actual saved encapsulation continuation supplies finite ordinary postchallenge query caps on every valid adversary context and every candidate reply. Initialization and local reservations remain separate prephase work. -/
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhRegistrationJointKemPostBills
open PqxdhKemIndCca PqxdhRegistrationJointKemChallenge PqxdhRegistrationJointKemResume
open PqxdhRegistrationJointKemSavedBills PqxdhRegistrationJointKemCutInterpreted
open PqxdhServerAuthSourceCosts (KemCaps KemBound)
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK A Result Reader Response : Type}

structure CcaBills (work : OracleComp (MlKemCCAOracleSpec baseSpec) Result) (qUniform qBase qD : Nat) : Prop where
  uniform : work.IsQueryBoundP IsMlKemUniformQuery qUniform
  base : work.IsQueryBoundP IsMlKemBaseQuery qBase
  decaps : work.IsQueryBoundP IsMlKemLogicalDecapsulationQuery qD

def uniformCap (caps : KemCaps) (qCreate qD qUniform qEncap : Nat) : Nat :=
  32 * qCreate + (qUniform + caps.encapsCost * qEncap) + caps.decapsUniform * qD

/-- Full postphase bill for the original saved source callback. Actual later encapsulations, every identity seed and all local decapsulation effects remain charged; exact challenge ciphertexts are handled by the existing blocked router. -/
theorem post_bound (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (caps : KemCaps) (bounded : KemBound setup caps) (count : Nat) (selected : Fin (count + 1))
    (context : Context KemSK A Result count) (target : MlKem768PublicKey)
    (ciphertext : MlKem768Ciphertext) (candidate : MlKemSharedSecret)
    (qCreate qD qUniform qEncap : Nat) (certificate : Certificate context qCreate qD qUniform qEncap) :
    CcaBills (post setup count selected ⟨target, ciphertext, context⟩ candidate)
      (uniformCap caps qCreate qD qUniform qEncap) (caps.decapsBase * qD) qD := by
  cases context with
  | failed state => constructor <;> trivial
  | ready created others cut state runtime =>
    cases cut with
    | none => constructor <;> trivial
    | some cut =>
      cases cut with
      | complete result => constructor <;> trivial
      | pending request next =>
        simp only [post]
        split
        · have bills := actual_bills setup caps bounded (next (reply ciphertext candidate))
            qCreate qD qUniform qEncap
            (pending created others request next state runtime qCreate qD qUniform qEncap certificate _)
          constructor
          · simpa only [uniformCap, bind_pure_comp, isQueryBoundP_map_iff] using
              PqxdhDynamicKemJointBounds.post_uniform setup.joint setup.kem selected.val
                (PqxdhDynamicKemRouter.selectedReservation selected target others) ciphertext candidate _
                qCreate (qUniform + caps.encapsCost * qEncap) qD bills.creates bills.uniform bills.decaps
                state caps.decapsUniform (PqxdhRegistrationJointKemCosts.local_uniform setup caps bounded)
          · simpa only [bind_pure_comp, isQueryBoundP_map_iff] using
              PqxdhDynamicKemJointBounds.post_base setup.joint setup.kem selected.val
                (PqxdhDynamicKemRouter.selectedReservation selected target others) ciphertext candidate _ qD bills.decaps
                state IsMlKemBaseQuery (fun _ => by simp [IsMlKemBaseQuery]) (fun _ => by simp [IsMlKemBaseQuery])
                caps.decapsBase (PqxdhRegistrationJointKemCosts.local_base setup caps bounded)
          · simpa only [bind_pure_comp, isQueryBoundP_map_iff] using
              PqxdhDynamicKemJointBounds.post_decaps setup.joint setup.kem selected.val
                (PqxdhDynamicKemRouter.selectedReservation selected target others) ciphertext candidate _ qD bills.decaps state
        · constructor <;> trivial

set_option backward.isDefEq.respectTransparency false in
/-- Every postchallenge context of the actual ordinary adversary has explicit source-derived caps. Arbitrary challenge keys, ciphertexts and candidate secrets are permitted; only erased executable-prephase provenance constrains saved continuations. -/
theorem adversary_post (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (checks : PqxdhServerAuthExperiment.Checks)
    (caps : KemCaps) (bounded : KemBound setup caps)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes)
    (client : OracleComp (PqxdhRegistrationJointKemCommands.SourceSpec KemSK) Bool) (runtime : A)
    (count : Nat) (selected : Fin (count + 1)) (occurrence : Nat)
    (budget : PqxdhRegistrationJointKemCommands.Budget)
    (certified : ∀ source, client.IsQueryBoundP
      (fun query => PqxdhRegistrationJointRevealCosts.sourceKind (KemSK := KemSK) query = source) (budget source))
    (transcript : MlKemChallengeTranscript
      (PqxdhRegistrationJointKemCertified.Saved setup codec checks ensureInit supplied client runtime count selected occurrence))
    (candidate : MlKemSharedSecret) :
    CcaBills ((PqxdhRegistrationJointKemCertified.adversary setup codec checks ensureInit supplied client runtime count selected occurrence).postChallenge transcript candidate)
      (uniformCap caps (budget (.inl 1)) (budget (.inl 5))
        (PqxdhRegistrationJointOpenUniform.total caps budget) (budget (.inl 3)))
      (caps.decapsBase * budget (.inl 5)) (budget (.inl 5)) := by
  have bill := post_bound setup caps bounded count selected transcript.context.2.val
    transcript.publicKey transcript.ciphertext candidate _ _ _ _
    (saved setup codec checks caps bounded ensureInit supplied client runtime count selected occurrence budget certified transcript.context)
  constructor
  · simpa only [PqxdhRegistrationJointKemCertified.adversary, isQueryBoundP_map_iff] using bill.uniform
  · simpa only [PqxdhRegistrationJointKemCertified.adversary, isQueryBoundP_map_iff] using bill.base
  · simpa only [PqxdhRegistrationJointKemCertified.adversary, isQueryBoundP_map_iff] using bill.decaps

end BeaconcryptCore.Computational.PqxdhRegistrationJointKemPostBills

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemPostBills.post_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemPostBills.post_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemPostBills.adversary_post' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemPostBills.adversary_post
