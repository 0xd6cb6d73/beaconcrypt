-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRegistrationJointKemInitializedRouter

/-! The complete actual initialized KEM simulator pays for constructor initialization, generated identity seeds, every unselected key generator, the full source command program and local decapsulation. These bounds hold for every typed challenger reply. The selected generator belongs to the ordinary challenger and remains separately counted. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhRegistrationJointKemInitializedCosts
open PqxdhKemIndCca PqxdhJointIdentity PqxdhServerAuthExperiment PqxdhServerAuthNative
open PqxdhRegistrationJointKemCommands (SourceSpec Budget)
open PqxdhRegistrationJointKemInitializedRouter (pre)
open PqxdhServerAuthSourceCosts (KemCaps KemBound)
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response A Result : Type}

/-- Complete initialized uniform-query bound. Even failed initialization pays its declared allowance; local reservation generation and every possible source continuation are included. -/
theorem uniform (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (caps : KemCaps) (bounded : KemBound setup caps) (ensureInit : StateT A ProbComp Bool)
    (qInit : Nat) (initBound : ∀ runtime, (ensureInit.run runtime).IsTotalQueryBound qInit)
    (supplied : Option Pqxdh.Bytes) (client : OracleComp (SourceSpec KemSK) Result)
    (budget : Budget)
    (certified : ∀ source, client.IsQueryBoundP
      (fun query => PqxdhRegistrationJointRevealCosts.sourceKind (KemSK := KemSK) query = source) (budget source))
    (runtime : A) (count : Nat) (selected : Fin (count + 1)) (target : MlKem768PublicKey) :
    (pre setup codec checks ensureInit supplied client runtime count selected target).IsQueryBoundP
      IsMlKemUniformQuery
      ((qInit + if supplied.isNone then 32 else 0) +
        (caps.keygenCost * count + (32 * budget (.inl 1) +
          PqxdhRegistrationJointOpenUniform.total caps budget + caps.decapsUniform * budget (.inl 5)))) := by
  unfold pre
  apply isQueryBoundP_bind (PqxdhPrivateRootQueryBounds.ccaCoins_uniform _ _
    (PqxdhRegistrationJointServerBirth.client_uniform setup ensureInit qInit initBound setup.serverKeyId supplied _))
  rintro ⟨(_ | created), after⟩ _
  · simp
  · apply isQueryBoundP_bind (PqxdhPrivateRootQueryBounds.ccaCoins_uniform _ _
      (PqxdhLiveKemSelection.family_uniform _ caps.keygenCost count
        (PqxdhServerAuthSourceCosts.keygen_uniform setup caps bounded)))
    intro others _
    simpa only [isQueryBoundP_map_iff] using
      PqxdhRegistrationJointKemCosts.pre_uniform setup codec checks caps bounded
        created.server.server.metadata.identityIndex created.publicIdentity client budget certified []
        (PqxdhRegistrationJointInitializedAccept.initial created) selected.val
        (PqxdhDynamicKemRouter.selectedReservation selected target others) (after.1.1, PqxdhDynamicKemRouter.empty)

/-- The actual local constructor and unselected generators add no external CCA resource other than their counted uniform queries. This transports a complete continuation bound, including every failed initializer branch. -/
theorem excluded (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes)
    (client : OracleComp (SourceSpec KemSK) Result) (runtime : A)
    (count : Nat) (selected : Fin (count + 1)) (target : MlKem768PublicKey)
    (predicate : (MlKemCCAOracleSpec baseSpec).Domain → Prop) [DecidablePred predicate]
    (noCoins : ∀ coin, ¬ predicate (.inl (.inl coin))) (q : Nat)
    (suffix : ∀ created joint others,
      (PqxdhRegistrationJointKemRouting.pre setup codec checks
        created.server.server.metadata.identityIndex created.publicIdentity client []
        (PqxdhRegistrationJointInitializedAccept.initial created) selected.val
        (PqxdhDynamicKemRouter.selectedReservation selected target others)
        (joint, PqxdhDynamicKemRouter.empty)).IsQueryBoundP predicate q) :
    (pre setup codec checks ensureInit supplied client runtime count selected target).IsQueryBoundP predicate q := by
  unfold pre
  rw [← Nat.zero_add q]
  apply isQueryBoundP_bind (PqxdhPrivateRootQueryBounds.ccaCoins_excluded _ predicate noCoins)
  rintro ⟨(_ | created), after⟩ _
  · simp
  · rw [← Nat.zero_add q]
    apply isQueryBoundP_bind (PqxdhPrivateRootQueryBounds.ccaCoins_excluded _ predicate noCoins)
    intro others _
    simpa only [isQueryBoundP_map_iff] using suffix created after.1.1 others

/-- Initialization and local reservation do not create extra logical decapsulation requests. Every attempted source finish still contributes at most one. -/
theorem decapsulations (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes)
    (client : OracleComp (SourceSpec KemSK) Result) (budget : Budget)
    (certified : ∀ source, client.IsQueryBoundP
      (fun query => PqxdhRegistrationJointRevealCosts.sourceKind (KemSK := KemSK) query = source) (budget source))
    (runtime : A) (count : Nat) (selected : Fin (count + 1)) (target : MlKem768PublicKey) :
    (pre setup codec checks ensureInit supplied client runtime count selected target).IsQueryBoundP
      IsMlKemLogicalDecapsulationQuery (budget (.inl 5)) :=
  excluded setup codec checks ensureInit supplied client runtime count selected target
    IsMlKemLogicalDecapsulationQuery (fun _ => by simp [IsMlKemLogicalDecapsulationQuery]) _
    (fun created joint others => PqxdhRegistrationJointKemRouting.pre_decapsulations setup codec checks
      created.server.server.metadata.identityIndex created.publicIdentity client budget certified []
      (PqxdhRegistrationJointInitializedAccept.initial created) selected.val
      (PqxdhDynamicKemRouter.selectedReservation selected target others) (joint, PqxdhDynamicKemRouter.empty))

/-- Only other-key local decapsulation forwards base callbacks. The actual initialized/local-generator prefix is already interpreted and charged in the uniform bill, not omitted. -/
theorem base (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (caps : KemCaps) (bounded : KemBound setup caps) (ensureInit : StateT A ProbComp Bool)
    (supplied : Option Pqxdh.Bytes) (client : OracleComp (SourceSpec KemSK) Result) (budget : Budget)
    (certified : ∀ source, client.IsQueryBoundP
      (fun query => PqxdhRegistrationJointRevealCosts.sourceKind (KemSK := KemSK) query = source) (budget source))
    (runtime : A) (count : Nat) (selected : Fin (count + 1)) (target : MlKem768PublicKey) :
    (pre setup codec checks ensureInit supplied client runtime count selected target).IsQueryBoundP
      IsMlKemBaseQuery (caps.decapsBase * budget (.inl 5)) :=
  excluded setup codec checks ensureInit supplied client runtime count selected target
    IsMlKemBaseQuery (fun _ => by simp [IsMlKemBaseQuery]) _
    (fun created joint others => PqxdhRegistrationJointKemCosts.pre_base setup codec checks caps bounded
      created.server.server.metadata.identityIndex created.publicIdentity client budget certified []
      (PqxdhRegistrationJointInitializedAccept.initial created) selected.val
      (PqxdhDynamicKemRouter.selectedReservation selected target others) (joint, PqxdhDynamicKemRouter.empty))

end BeaconcryptCore.Computational.PqxdhRegistrationJointKemInitializedCosts

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemInitializedCosts.uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemInitializedCosts.uniform

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemInitializedCosts.excluded' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemInitializedCosts.excluded

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemInitializedCosts.decapsulations' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemInitializedCosts.decapsulations

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemInitializedCosts.base' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemInitializedCosts.base
