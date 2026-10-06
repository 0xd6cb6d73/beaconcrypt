-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRegistrationJointOpenUniform
import BeaconcryptCore.Computational.PqxdhRegistrationJointOpenInitializedCosts

/-! The actual open initialized registration program's all-reply uniform bill. Private key generation and decapsulation remain explicit service classes for their downstream compiler. -/
open OracleComp OracleSpec CoreModels Aeneas
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhRegistrationJointOpenInitializedUniform
open PqxdhRegistrationJointServiceCosts (Kind poolClass)
open PqxdhDynamicKemJointBounds (IsUniform)
open PqxdhServerAuthExperiment PqxdhServerAuthNative
open PqxdhServerAuthSourceCosts (KemCaps KemBound)
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response Result : Type}

/-- The old local uniform class is included in the complete uniform interface, which also permits ordinary joint-interface coins. -/
theorem local_uniform_implies (query : (PqxdhLiveKemBirth.Spec KemSK).Domain) :
    poolClass (KemSK := KemSK) query = .uniform → IsUniform (KemSK := KemSK) query := by
  rcases query with (coin | request) | (coin | request)
  case inl.inr =>
    cases request
    case service index service => cases service <;> simp [IsUniform, PqxdhDynamicIdentityPool.IsUniform, poolClass]
    all_goals simp [IsUniform, PqxdhDynamicIdentityPool.IsUniform, poolClass]
  case inr.inr => cases request <;> simp [IsUniform, poolClass]
  all_goals simp [IsUniform, PqxdhDynamicIdentityPool.IsUniform, poolClass]

/-- Explicit coins in either source interface; constructor initialization/import is billed separately. -/
def IsCoin : (PqxdhRegistrationJointServerBirth.Spec KemSK).Domain → Prop
  | .inl query => IsUniform (KemSK := KemSK) query
  | .inr _ => False
instance : DecidablePred (IsCoin (KemSK := KemSK)) := fun query => by
  cases query <;> simp only [IsCoin] <;> infer_instance

/-- The constructor-interface forwarding layer preserves the complete explicit-coin allowance. -/
theorem lifted_coins (program : OracleComp (PqxdhLiveKemBirth.Spec KemSK) Result) (bound : Nat) :
    (simulateQ PqxdhRegistrationJointOpenInitialization.poolLift program).IsQueryBoundP (IsCoin (KemSK := KemSK)) bound ↔
      program.IsQueryBoundP (IsUniform (KemSK := KemSK)) bound := by
  induction program using OracleComp.inductionOn generalizing bound with
  | pure value => simp
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, PqxdhRegistrationJointOpenInitialization.poolLift,
        isQueryBoundP_query_bind_iff, IsCoin, ih]
      rfl

/-- The open constructor has no direct coin query: generated identity randomness stays with the private challenger, and runtime initialization is a separate local call. -/
theorem constructor_coins (sender : Std.U64) (supplied : Option Pqxdh.Bytes) :
    (PqxdhRegistrationJointServerBirth.client (KemSK := KemSK) (P := Unit) sender supplied).IsQueryBoundP
      (IsCoin (KemSK := KemSK)) 0 := by
  cases supplied <;>
    simp [PqxdhRegistrationJointServerBirth.client, IsCoin, IsUniform,
      PqxdhDynamicIdentityPool.IsUniform, isQueryBoundP_query_bind_iff]
  all_goals split <;> simp [IsCoin,
    isQueryBoundP_map_iff, isQueryBoundP_query_iff]

/-- Every explicit source coin in the complete initialized program is charged, for every typed service reply and native state. Runtime initialization and private KEM services stay in separate downstream classes. -/
theorem initialized_coins (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (caps : KemCaps) (bounded : KemBound setup caps) (supplied : Option Pqxdh.Bytes)
    (program : OracleComp (PqxdhRegistrationJointRevealSchedule.Spec KemSK) Result)
    (budget : PqxdhRegistrationJointRevealCosts.SourceKind → Nat)
    (certified : ∀ source, program.IsQueryBoundP
      (fun query => PqxdhRegistrationJointRevealCosts.sourceKind (KemSK := KemSK) query = source) (budget source)) :
    (PqxdhRegistrationJointOpenInitialization.client setup codec checks supplied program).IsQueryBoundP
      (IsCoin (KemSK := KemSK)) (PqxdhRegistrationJointOpenUniform.total caps budget) := by
  unfold PqxdhRegistrationJointOpenInitialization.client
  rw [← Nat.zero_add (PqxdhRegistrationJointOpenUniform.total caps budget)]
  apply isQueryBoundP_bind (n := 0) (constructor_coins setup.serverKeyId supplied)
  rintro (_ | created) _
  · trivial
  · simpa only [isQueryBoundP_map_iff, lifted_coins, PqxdhRegistrationJointKemCommands.program] using
      PqxdhRegistrationJointOpenUniform.command_program setup codec checks caps bounded
        created.server.server.metadata.identityIndex created.publicIdentity program budget certified []
        (PqxdhRegistrationJointInitializedAccept.initial created)

end BeaconcryptCore.Computational.PqxdhRegistrationJointOpenInitializedUniform

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointOpenInitializedUniform.local_uniform_implies' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointOpenInitializedUniform.local_uniform_implies

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointOpenInitializedUniform.lifted_coins' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointOpenInitializedUniform.lifted_coins

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointOpenInitializedUniform.constructor_coins' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointOpenInitializedUniform.constructor_coins

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointOpenInitializedUniform.initialized_coins' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointOpenInitializedUniform.initialized_coins
