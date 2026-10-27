-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRegistrationJointKemPostBills

/-! Complete prechallenge accounting includes actual runtime initialization, the optional generated Server identity, every local unselected KEM reservation, the source scan and every permitted private service. -/
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhRegistrationJointKemPreBills
open PqxdhKemIndCca PqxdhRegistrationJointKemChallenge PqxdhRegistrationJointKemPostBills
open PqxdhRegistrationJointKemCommands (SourceSpec Budget)
open PqxdhServerAuthSourceCosts (KemCaps KemBound)
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response A Result : Type}

noncomputable def sourceScan (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (checks : PqxdhServerAuthExperiment.Checks)
    (client : OracleComp (SourceSpec KemSK) Result)
    (created : PqxdhRegistrationJointServerBirth.ClientCreated Unit) (occurrence : Nat) :=
  PqxdhRegistrationJointKemCut.scan setup
    (PqxdhRegistrationJointKemEncapsulation.commands setup codec checks created.server.server.metadata.identityIndex
      created.publicIdentity client [] (PqxdhRegistrationJointInitializedAccept.initial created)) occurrence

/-- The literal initialized source scan supplies all private and native uniform bounds on arbitrary intermediate replies. -/
theorem scan_bills (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (checks : PqxdhServerAuthExperiment.Checks)
    (caps : KemCaps) (bounded : KemBound setup caps)
    (client : OracleComp (SourceSpec KemSK) Result) (budget : Budget)
    (certified : ∀ source, client.IsQueryBoundP
      (fun query => PqxdhRegistrationJointRevealCosts.sourceKind (KemSK := KemSK) query = source) (budget source))
    (created : PqxdhRegistrationJointServerBirth.ClientCreated Unit) (occurrence : Nat) :
    PqxdhRegistrationJointKemCutInterpreted.Bills (sourceScan setup codec checks client created occurrence)
      (budget (.inl 1)) (budget (.inl 5))
      (PqxdhRegistrationJointOpenUniform.total caps budget + caps.encapsCost * budget (.inl 3)) :=
  PqxdhRegistrationJointKemCutInterpreted.scan_bills setup caps bounded _ _ _ _ _ occurrence
    (PqxdhRegistrationJointKemProgramBills.commands setup codec checks caps bounded
      created.server.server.metadata.identityIndex created.publicIdentity client budget certified []
      (PqxdhRegistrationJointInitializedAccept.initial created))

/-- Full actual prephase uniform allowance, including failed initialization and all locally reserved pairs even when never used. The selected KEM key generator belongs separately to the ordinary challenger. -/
theorem uniform (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (checks : PqxdhServerAuthExperiment.Checks)
    (caps : KemCaps) (bounded : KemBound setup caps) (ensureInit : StateT A ProbComp Bool)
    (qInit : Nat) (initBound : ∀ runtime, (ensureInit.run runtime).IsTotalQueryBound qInit)
    (supplied : Option Pqxdh.Bytes) (client : OracleComp (SourceSpec KemSK) Result) (budget : Budget)
    (certified : ∀ source, client.IsQueryBoundP
      (fun query => PqxdhRegistrationJointRevealCosts.sourceKind (KemSK := KemSK) query = source) (budget source))
    (runtime : A) (count : Nat) (selected : Fin (count + 1)) (occurrence : Nat) (target : MlKem768PublicKey) :
    (pre setup codec checks ensureInit supplied client runtime count selected occurrence target).IsQueryBoundP
      IsMlKemUniformQuery ((qInit + if supplied.isNone then 32 else 0) +
        (caps.keygenCost * count + uniformCap caps (budget (.inl 1)) (budget (.inl 5))
          (PqxdhRegistrationJointOpenUniform.total caps budget) (budget (.inl 3)))) := by
  unfold pre
  apply isQueryBoundP_bind (PqxdhPrivateRootQueryBounds.ccaCoins_uniform _ _
    (PqxdhRegistrationJointServerBirth.client_uniform setup ensureInit qInit initBound setup.serverKeyId supplied _))
  rintro ⟨(_ | created), after⟩ _
  · simp
  · apply isQueryBoundP_bind (PqxdhPrivateRootQueryBounds.ccaCoins_uniform _ _
      (PqxdhLiveKemSelection.family_uniform _ caps.keygenCost count
        (PqxdhServerAuthSourceCosts.keygen_uniform setup caps bounded)))
    intro others _
    have bills := scan_bills setup codec checks caps bounded client budget certified created occurrence
    simpa only [uniformCap, sourceScan, bind_pure_comp, isQueryBoundP_map_iff] using
      PqxdhDynamicKemJointBounds.pre_uniform setup.joint setup.kem selected.val
        (PqxdhDynamicKemRouter.selectedReservation selected target others) _ _ _ _
        bills.creates bills.uniform bills.decaps (after.1.1, PqxdhDynamicKemRouter.empty)
        caps.decapsUniform (PqxdhRegistrationJointKemCosts.local_uniform setup caps bounded)

/-- Local constructor and reservation work have no external nonuniform CCA query. They keep their complete evaluated random/base work in the separately charged prefix allowance. -/
theorem excluded (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (checks : PqxdhServerAuthExperiment.Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes)
    (client : OracleComp (SourceSpec KemSK) Result) (runtime : A)
    (count : Nat) (selected : Fin (count + 1)) (occurrence : Nat) (target : MlKem768PublicKey)
    (predicate : (MlKemCCAOracleSpec baseSpec).Domain → Prop) [DecidablePred predicate]
    (noCoins : ∀ coin, ¬ predicate (.inl (.inl coin))) (q : Nat)
    (suffix : ∀ created joint others,
      ((((simulateQ (PqxdhDynamicKemJointRouter.pre setup.joint setup.kem selected.val
        (PqxdhDynamicKemRouter.selectedReservation selected target others))
        (sourceScan setup codec checks client created occurrence)).run).run
          (joint, PqxdhDynamicKemRouter.empty))).IsQueryBoundP predicate q) :
    (pre setup codec checks ensureInit supplied client runtime count selected occurrence target).IsQueryBoundP predicate q := by
  unfold pre
  rw [← Nat.zero_add q]
  apply isQueryBoundP_bind (PqxdhPrivateRootQueryBounds.ccaCoins_excluded _ predicate noCoins)
  rintro ⟨(_ | created), after⟩ _
  · simp
  · rw [← Nat.zero_add q]
    apply isQueryBoundP_bind (PqxdhPrivateRootQueryBounds.ccaCoins_excluded _ predicate noCoins)
    intro others _
    simpa only [sourceScan, bind_pure_comp, isQueryBoundP_map_iff] using suffix created after.1.1 others

/-- Complete initialization plus the literal source scan has at most qFinish logical CCA decapsulation queries. -/
theorem decapsulations (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (checks : PqxdhServerAuthExperiment.Checks)
    (caps : KemCaps) (bounded : KemBound setup caps)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes)
    (client : OracleComp (SourceSpec KemSK) Result) (budget : Budget)
    (certified : ∀ source, client.IsQueryBoundP
      (fun query => PqxdhRegistrationJointRevealCosts.sourceKind (KemSK := KemSK) query = source) (budget source))
    (runtime : A) (count : Nat) (selected : Fin (count + 1)) (occurrence : Nat) (target : MlKem768PublicKey) :
    (pre setup codec checks ensureInit supplied client runtime count selected occurrence target).IsQueryBoundP
      IsMlKemLogicalDecapsulationQuery (budget (.inl 5)) :=
  excluded setup codec checks ensureInit supplied client runtime count selected occurrence target
    IsMlKemLogicalDecapsulationQuery (fun _ => by simp [IsMlKemLogicalDecapsulationQuery]) _
    (fun created joint others => PqxdhDynamicKemJointBounds.pre_decaps setup.joint setup.kem selected.val
      (PqxdhDynamicKemRouter.selectedReservation selected target others) _ _
      (scan_bills setup codec checks caps bounded client budget certified created occurrence).decaps
      (joint, PqxdhDynamicKemRouter.empty))

/-- The complete prephase retains every local decapsulation base query; other locally interpreted native/base work is explicitly included in uniform. -/
theorem base (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (checks : PqxdhServerAuthExperiment.Checks)
    (caps : KemCaps) (bounded : KemBound setup caps)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes)
    (client : OracleComp (SourceSpec KemSK) Result) (budget : Budget)
    (certified : ∀ source, client.IsQueryBoundP
      (fun query => PqxdhRegistrationJointRevealCosts.sourceKind (KemSK := KemSK) query = source) (budget source))
    (runtime : A) (count : Nat) (selected : Fin (count + 1)) (occurrence : Nat) (target : MlKem768PublicKey) :
    (pre setup codec checks ensureInit supplied client runtime count selected occurrence target).IsQueryBoundP
      IsMlKemBaseQuery (caps.decapsBase * budget (.inl 5)) :=
  excluded setup codec checks ensureInit supplied client runtime count selected occurrence target
    IsMlKemBaseQuery (fun _ => by simp [IsMlKemBaseQuery]) _
    (fun created joint others => PqxdhDynamicKemJointBounds.pre_base setup.joint setup.kem selected.val
      (PqxdhDynamicKemRouter.selectedReservation selected target others) _ _
      (scan_bills setup codec checks caps bounded client budget certified created occurrence).decaps
      (joint, PqxdhDynamicKemRouter.empty) IsMlKemBaseQuery
      (fun _ => by simp [IsMlKemBaseQuery]) (fun _ => by simp [IsMlKemBaseQuery])
      caps.decapsBase (PqxdhRegistrationJointKemCosts.local_base setup caps bounded))

end BeaconcryptCore.Computational.PqxdhRegistrationJointKemPreBills

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemPreBills.scan_bills' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemPreBills.scan_bills

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemPreBills.uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemPreBills.uniform

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemPreBills.excluded' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemPreBills.excluded

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemPreBills.decapsulations' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemPreBills.decapsulations

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemPreBills.base' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemPreBills.base
