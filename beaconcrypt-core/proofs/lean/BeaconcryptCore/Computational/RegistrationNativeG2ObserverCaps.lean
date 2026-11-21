-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeOpenKeyKemTransport
import BeaconcryptCore.Computational.RegistrationNativeG2Observer
import BeaconcryptCore.Computational.RegistrationNativeOpenKeyStartup
import BeaconcryptCore.Computational.RegistrationNativeKemPoolSource

/-! The complete open native G2 client derives its indexed KEM resource bills from the original public budget. Its local Server/prekey draws, actual constructor/ML startup and private key108 compilation add no KEM birth or reveal. The literal original ledger and arbitrary decision remain in the client. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeG2ObserverCaps
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeKemBeaconFootprint (Kind)
open RegistrationNativeOpenKeyKemTransport (RetainedPrivate KeyPrivate)
variable {n : Nat} {ι KemSK Value : Type} {base : OracleSpec ι} {kind : Kind}

private theorem start_zero (setup : Setup base KemSK) (source : RegistrationNativeMldsa.Source)
    (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64)
    (identity : PqxdhJointIdentity.PublicIdentity) :
    (RegistrationNativeOpenRetainedStartup.start (n := n) setup source ensureInit identityIndex serverKeyId identity).IsQueryBoundP
      (RetainedPrivate (KemSK := KemSK) kind) 0 := by
  unfold RegistrationNativeOpenRetainedStartup.start
  apply RawCtxSourceOpen.simulate_bound _ (fun _ => False) _ _ 0 (isQueryBoundP_false _ 0)
  intro query
  simp [RegistrationNativeOpenRetainedStartup.coins, QueryImpl.apply_compose,
    RegistrationNativePublicRetained.coins, RegistrationNativeOpenRetained.baseLift,
    RetainedPrivate, isQueryBoundP_query_iff]

/-- Actual startup and the original full native public ledger retain the exact indexed birth/reveal cap. -/
theorem retained_bound (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (source : RegistrationNativeMldsa.Source)
    (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64)
    (selectedOwner selectedAccept : Nat) (bounds : PqxdhDeploymentInterface.FreshBounds)
    (mode : PqxdhDeploymentInterface.Mode)
    (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (observe : RegistrationNativeG2Observer.Outcome Value → Bool) (budget : PqxdhDeploymentInterface.Budget)
    (bounded : ∀ publicValue, RegistrationNativeInterface.Respects budget (adversary publicValue))
    (publicValue : PqxdhJointGapDh.PublicChallenge) :
    (RegistrationNativeG2Observer.retained (n := n) setup checks wire route source ensureInit identityIndex serverKeyId
      selectedOwner selectedAccept bounds mode adversary observe publicValue).IsQueryBoundP
        (RetainedPrivate (KemSK := KemSK) kind) (if kind = .create then budget.create else 0) := by
  unfold RegistrationNativeG2Observer.retained
  rw [← Nat.zero_add (if kind = .create then budget.create else 0)]
  apply isQueryBoundP_bind (n := 0) (m := if kind = .create then budget.create else 0)
    (start_zero (n := n) (kind := kind) setup source ensureInit identityIndex serverKeyId publicValue.identity)
  intro initialized _
  cases initialized.1 with
  | none => exact isQueryBoundP_pure _ _ _
  | some started =>
      apply RegistrationNativeOpenKeyKemTransport.retained_bound
      rw [isQueryBoundP_map_iff]
      unfold RegistrationNativeG2Trace.program
      apply RegistrationNativeG2Trace.program_bound
      exact RegistrationNativeOpenKeyKemPublic.run_bound setup checks wire source
        (RegistrationNativeMldsa.owned source started.credential) selectedOwner selectedAccept publicValue.prekey serverKeyId bounds mode
        (adversary ⟨publicValue.identity, started.credential.publicKey, serverKeyId⟩) budget (bounded _) started.frontend

private theorem coins_zero (draw : ProbComp Value) :
    (simulateQ (RegistrationNativeOpenKeyStartup.coins (KemSK := KemSK)) draw).IsQueryBoundP
      (KeyPrivate (KemSK := KemSK) kind) 0 := by
  apply RawCtxSourceOpen.simulate_bound _ (fun _ => False) _ draw 0 (isQueryBoundP_false draw 0)
  intro query
  simp [RegistrationNativeOpenKeyStartup.coins, QueryImpl.apply_compose,
    RegistrationNativeKeyCompiler.coins, RegistrationNativeOpenKey.keyLift, KeyPrivate, isQueryBoundP_query_iff]

/-- Independent local challenge draws and the complete key108 compiler add no indexed KEM operations. -/
theorem key_bound (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (source : RegistrationNativeMldsa.Source)
    (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64)
    (selectedOwner selectedAccept : Nat) (bounds : PqxdhDeploymentInterface.FreshBounds)
    (mode : PqxdhDeploymentInterface.Mode)
    (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (observe : PqxdhJointIdentity.IdentitySeed → PqxdhJointGapDh.ScalarBytes → RegistrationNativeG2Observer.Outcome Value → Bool) (budget : PqxdhDeploymentInterface.Budget)
    (bounded : ∀ publicValue, RegistrationNativeInterface.Respects budget (adversary publicValue)) :
    (RegistrationNativeG2Observer.client (n := n) setup checks wire route source ensureInit identityIndex serverKeyId
      selectedOwner selectedAccept bounds mode adversary observe).IsQueryBoundP
        (KeyPrivate (KemSK := KemSK) kind) (if kind = .create then budget.create else 0) := by
  unfold RegistrationNativeG2Observer.client
  rw [← Nat.zero_add (if kind = .create then budget.create else 0)]
  apply isQueryBoundP_bind (n := 0) (m := if kind = .create then budget.create else 0)
    (coins_zero (KemSK := KemSK) (kind := kind) _)
  intro seed _
  rw [← Nat.zero_add (if kind = .create then budget.create else 0)]
  apply isQueryBoundP_bind (n := 0) (m := if kind = .create then budget.create else 0)
    (coins_zero (KemSK := KemSK) (kind := kind) _)
  intro scalar _
  exact RegistrationNativeOpenKeyKemTransport.key_bound _ _ _ _ _
    (retained_bound setup checks wire route source ensureInit identityIndex serverKeyId selectedOwner selectedAccept bounds mode
      adversary (observe seed scalar) budget bounded (PqxdhJointGapDh.challenge setup.joint setup.dh seed scalar))

/-- The actual normalized native cut program retains its original public KEM allowance. -/
theorem native_bound (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (source : RegistrationNativeMldsa.Source)
    (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64)
    (selectedOwner selectedAccept : Nat) (bounds : PqxdhDeploymentInterface.FreshBounds)
    (mode : PqxdhDeploymentInterface.Mode)
    (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (observe : PqxdhJointIdentity.IdentitySeed → PqxdhJointGapDh.ScalarBytes → RegistrationNativeG2Observer.Outcome Value → Bool) (budget : PqxdhDeploymentInterface.Budget)
    (bounded : ∀ publicValue, RegistrationNativeInterface.Respects budget (adversary publicValue)) :
    (RegistrationNativeG2Observer.nativeClient (n := n) setup checks wire route source ensureInit identityIndex serverKeyId
      selectedOwner selectedAccept bounds mode adversary observe).IsQueryBoundP
        (RegistrationNativeKemCompilerFootprint.predicate RegistrationNativeOpenKey.Ambient KemSK kind)
        (if kind = .create then budget.create else 0) :=
  RegistrationNativeOpenKeyKemTransport.native_bound _ _
    (key_bound setup checks wire route source ensureInit identityIndex serverKeyId selectedOwner selectedAccept bounds mode
      adversary observe budget bounded)

/-- The whole actual cut program creates at most the original adversary's create budget. -/
theorem creates (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (source : RegistrationNativeMldsa.Source)
    (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64)
    (selectedOwner selectedAccept : Nat) (bounds : PqxdhDeploymentInterface.FreshBounds)
    (mode : PqxdhDeploymentInterface.Mode)
    (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (observe : PqxdhJointIdentity.IdentitySeed → PqxdhJointGapDh.ScalarBytes → RegistrationNativeG2Observer.Outcome Value → Bool) (budget : PqxdhDeploymentInterface.Budget)
    (bounded : ∀ publicValue, RegistrationNativeInterface.Respects budget (adversary publicValue)) :
    (RegistrationNativeG2Observer.nativeClient (n := n) setup checks wire route source ensureInit identityIndex serverKeyId
      selectedOwner selectedAccept bounds mode adversary observe).IsQueryBoundP
        (RegistrationNativeKemReservation.IsCreate (ambient := RegistrationNativeOpenKey.Ambient) (KemSK := KemSK)) budget.create := by
  have bill := native_bound (n := n) (kind := .create) setup checks wire route source ensureInit identityIndex serverKeyId
    selectedOwner selectedAccept bounds mode adversary observe budget bounded
  simp only [ite_true] at bill
  apply OracleComp.IsQueryBoundP.of_imp _ bill
  intro query counted
  rcases query with query | (query | key)
  · exact counted.elim
  · cases query <;> simp_all [RegistrationNativeKemReservation.IsCreate, RegistrationNativeKemCompilerFootprint.predicate]
  · exact counted.elim

/-- Every actual startup/public/key branch has zero private KEM secret-reveal calls. -/
theorem no_reveal (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (source : RegistrationNativeMldsa.Source)
    (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64)
    (selectedOwner selectedAccept : Nat) (bounds : PqxdhDeploymentInterface.FreshBounds)
    (mode : PqxdhDeploymentInterface.Mode)
    (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (observe : PqxdhJointIdentity.IdentitySeed → PqxdhJointGapDh.ScalarBytes → RegistrationNativeG2Observer.Outcome Value → Bool) (budget : PqxdhDeploymentInterface.Budget)
    (bounded : ∀ publicValue, RegistrationNativeInterface.Respects budget (adversary publicValue)) :
    (RegistrationNativeG2Observer.nativeClient (n := n) setup checks wire route source ensureInit identityIndex serverKeyId
      selectedOwner selectedAccept bounds mode adversary observe).IsQueryBoundP
        (RegistrationNativeKemPoolSource.IsReveal (ambient := RegistrationNativeOpenKey.Ambient) (KemSK := KemSK)) 0 := by
  have bill := native_bound (n := n) (kind := .reveal) setup checks wire route source ensureInit identityIndex serverKeyId
    selectedOwner selectedAccept bounds mode adversary observe budget bounded
  simp only [reduceCtorEq, ite_false] at bill
  apply OracleComp.IsQueryBoundP.of_imp _ bill
  intro query counted
  rcases query with query | (query | key)
  · exact counted.elim
  · cases query <;> simp_all [RegistrationNativeKemPoolSource.IsReveal, RegistrationNativeKemCompilerFootprint.predicate]
  · exact counted.elim

end BeaconcryptCore.Computational.RegistrationNativeG2ObserverCaps

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG2ObserverCaps.retained_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG2ObserverCaps.retained_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG2ObserverCaps.key_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG2ObserverCaps.key_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG2ObserverCaps.native_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG2ObserverCaps.native_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG2ObserverCaps.creates' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG2ObserverCaps.creates

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG2ObserverCaps.no_reveal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG2ObserverCaps.no_reveal
