-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeOpenMaterialCaps

/-! The complete generated open client has its actual original build-plus-finish material cap. Optional native startup failures, selected challenge sampling and all routed KEM requests add no protected material queries. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeOpenStartupMaterialCaps
open PqxdhServerAuthExperiment (Setup Checks)
variable {n : Nat} {ι KemSK Value : Type} {base : OracleSpec ι}

private theorem retained_coins_free (work : ProbComp Value) :
    (simulateQ (RegistrationNativeOpenRetainedStartup.coins (KemSK := KemSK)) work).IsQueryBoundP
      (RegistrationNativeOpenMaterialCaps.IsDemand (KemSK := KemSK)) 0 := by
  apply RawCtxSourceOpen.simulate_bound _ (fun _ => False) _ _ 0 (isQueryBoundP_false _ 0)
  intro coin
  simp [RegistrationNativeOpenRetainedStartup.coins, QueryImpl.apply_compose,
    RegistrationNativeOpenRetained.baseLift, RegistrationNativePublicRetained.coins,
    RegistrationNativeOpenMaterialCaps.IsDemand, RegistrationNativeRetainedService.IsDemand, isQueryBoundP_query_iff]

/-- The whole open retained experiment has its original material cap for every public startup value and original secrecy mode. -/
theorem retained_bound (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (source : RegistrationNativeMldsa.Source)
    (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64)
    (selectedOwner selectedAccept : Nat) (bounds : PqxdhDeploymentInterface.FreshBounds)
    (mode : PqxdhDeploymentInterface.Mode)
    (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (decision : Value × RegistrationNativeLedger.State → Bool)
    (budget : PqxdhDeploymentInterface.Budget)
    (bounded : ∀ publicValue, RegistrationNativeInterface.Respects budget (adversary publicValue))
    (publicValue : PqxdhJointGapDh.PublicChallenge) :
    (RegistrationNativeOpenRetainedStartup.client (n := n) setup checks wire route source ensureInit identityIndex serverKeyId
      selectedOwner selectedAccept bounds mode adversary decision publicValue).IsQueryBoundP
      (RegistrationNativeOpenMaterialCaps.IsDemand (KemSK := KemSK)) (budget.cap 4 + budget.cap 5) := by
  unfold RegistrationNativeOpenRetainedStartup.client RegistrationNativeOpenRetainedStartup.start
  refine (isQueryBoundP_bind (n := 0) (m := budget.cap 4 + budget.cap 5) (retained_coins_free _) ?_).mono (by omega)
  intro initialized _reached
  cases initialized.1 with
  | none => trivial
  | some started =>
      apply RegistrationNativeOpenMaterialCaps.retained_bound
      rw [isQueryBoundP_map_iff]
      exact RegistrationNativePublicCaps.run_bound setup checks wire source
        (RegistrationNativeMldsa.owned source started.credential) selectedOwner selectedAccept publicValue.prekey serverKeyId bounds mode
        (adversary ⟨publicValue.identity, started.credential.publicKey, serverKeyId⟩) budget (bounded _) started.frontend

private theorem key_coins_free (work : ProbComp Value) :
    (simulateQ (RegistrationNativeOpenKeyStartup.coins (KemSK := KemSK)) work).IsQueryBoundP
      (RegistrationNativeOpenMaterialCaps.IsMaterial (KemSK := KemSK)) 0 := by
  apply RawCtxSourceOpen.simulate_bound _ (fun _ => False) _ _ 0 (isQueryBoundP_false _ 0)
  intro coin
  simp [RegistrationNativeOpenKeyStartup.coins, QueryImpl.apply_compose,
    RegistrationNativeOpenKey.keyLift, RegistrationNativeKeyCompiler.coins,
    RegistrationNativeOpenMaterialCaps.IsMaterial, PqxdhRegistrationJointKemSecondEntry.IsValue, isQueryBoundP_query_iff]

/-- Independent private source challenges and literal counted native startup preserve the whole original material allowance. -/
theorem key_bound (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (source : RegistrationNativeMldsa.Source)
    (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64)
    (selectedOwner selectedAccept : Nat) (bounds : PqxdhDeploymentInterface.FreshBounds)
    (mode : PqxdhDeploymentInterface.Mode)
    (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (decision : Value × RegistrationNativeLedger.State → Bool)
    (budget : PqxdhDeploymentInterface.Budget)
    (bounded : ∀ publicValue, RegistrationNativeInterface.Respects budget (adversary publicValue)) :
    (RegistrationNativeOpenKeyStartup.client (n := n) setup checks wire route source ensureInit identityIndex serverKeyId
      selectedOwner selectedAccept bounds mode adversary decision).IsQueryBoundP
      (RegistrationNativeOpenMaterialCaps.IsMaterial (KemSK := KemSK)) (budget.cap 4 + budget.cap 5) := by
  unfold RegistrationNativeOpenKeyStartup.client
  refine (isQueryBoundP_bind (n := 0) (m := budget.cap 4 + budget.cap 5) (key_coins_free _) ?_).mono (by omega)
  intro seed _seed
  refine (isQueryBoundP_bind (n := 0) (m := budget.cap 4 + budget.cap 5) (key_coins_free _) ?_).mono (by omega)
  intro scalar _scalar
  apply RegistrationNativeOpenMaterialCaps.key_bound
  exact retained_bound setup checks wire route source ensureInit identityIndex serverKeyId selectedOwner selectedAccept
    bounds mode adversary decision budget bounded _

def IsMaterial : (RegistrationNativeOpenKey.NativeSpec KemSK).Domain → Prop
  | .inl (.inl query) => PqxdhRegistrationJointKemSecondEntry.IsValue
      (D := Pqxdh.Bytes) (R := PqxdhServerAuthKeySchedule.Output) query
  | _ => False
instance : DecidablePred (IsMaterial (KemSK := KemSK)) := fun query => by
  rcases query with (query | query) | query
  · exact inferInstanceAs (Decidable (PqxdhRegistrationJointKemSecondEntry.IsValue
      (D := Pqxdh.Bytes) (R := PqxdhServerAuthKeySchedule.Output) query))
  · exact isFalse id
  · exact isFalse id

/-- Reassociation into the actual native CCA interface retains the same whole-client protected table cap. -/
theorem native_bound (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (source : RegistrationNativeMldsa.Source)
    (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64)
    (selectedOwner selectedAccept : Nat) (bounds : PqxdhDeploymentInterface.FreshBounds)
    (mode : PqxdhDeploymentInterface.Mode)
    (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (decision : Value × RegistrationNativeLedger.State → Bool)
    (budget : PqxdhDeploymentInterface.Budget)
    (bounded : ∀ publicValue, RegistrationNativeInterface.Respects budget (adversary publicValue)) :
    (RegistrationNativeOpenKeyStartup.nativeClient (n := n) setup checks wire route source ensureInit identityIndex serverKeyId
      selectedOwner selectedAccept bounds mode adversary decision).IsQueryBoundP
      (IsMaterial (KemSK := KemSK)) (budget.cap 4 + budget.cap 5) := by
  unfold RegistrationNativeOpenKeyStartup.nativeClient
  apply RawCtxSourceOpen.simulate_bound _ _ _ _ _
    (key_bound setup checks wire route source ensureInit identityIndex serverKeyId selectedOwner selectedAccept
      bounds mode adversary decision budget bounded)
  intro query
  rcases query with query | (query | query) | query
  all_goals simp only [RegistrationNativeOpenKey.native, isQueryBoundP_query_iff,
    IsMaterial, RegistrationNativeOpenMaterialCaps.IsMaterial]
  · intro counted
    simpa only [ite_eq_left counted] using Nat.zero_lt_one
  all_goals simp

end BeaconcryptCore.Computational.RegistrationNativeOpenStartupMaterialCaps

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeOpenStartupMaterialCaps.retained_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeOpenStartupMaterialCaps.retained_bound
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeOpenStartupMaterialCaps.key_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeOpenStartupMaterialCaps.key_bound
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeOpenStartupMaterialCaps.native_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeOpenStartupMaterialCaps.native_bound
