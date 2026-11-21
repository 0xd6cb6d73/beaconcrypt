-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSecretWordCheckedBeaconFinish
import BeaconcryptCore.Computational.RegistrationNativeSecretWordCheckedOrdinaryFinish
import BeaconcryptCore.Computational.RegistrationNativeSecretWordCheckedFrontendLift

/-! The concrete mixed roster chooses the selected scalar-free controller or its ordinary supplied-name translation from the actual stored owner. Both complete source equations preserve the opaque handle, every owner field, full environment and terminal failures. No owner index is equated with a private KEM handle. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSecretWordCheckedOwners
open PqxdhServerAuthExperiment (Setup)
open RegistrationNativeSecretWordMessage (State input)
open PqxdhJointIdentity (IdentitySeed)
open PqxdhJointGapDh (ScalarBytes)
open RegistrationWorldAgreementCompiler (EnvState)
variable {n : Nat} {ι KemSK Auxiliary : Type} {base : OracleSpec ι}

attribute [local irreducible] RegistrationBeaconReferenceFinish.finish
  RegistrationNativeSecretWordBeaconCompiler.finish RegistrationNativeSecretWordChecked.native
  RegistrationNativeSecretWordChecked.implementation

/-- Every actual mixed-roster finish restores the original complete local source, retaining the real ordinary translated name through demand. -/
theorem finish_local (setup : Setup base KemSK) (source : RegistrationNativeMldsa.Source)
    (inside : RegistrationNativeSuffixKeyPrf.Prefix → Bool) (candidate : PqxdhKemIndCca.MlKemSharedSecret)
    (seed : IdentitySeed) (scalar : ScalarBytes) (index : Nat) (packet : Option registration.ResponsePacket)
    (owners : RegistrationNativePublicOwners.State source) (env : EnvState Auxiliary) :
    simulateQ (RegistrationNativeSecretWordChecked.native (n := n) setup.source inside candidate (input setup.joint setup.dh seed scalar))
      (((RegistrationNativePublicOwners.finish setup source index packet).run owners).run env) =
      simulateQ (RegistrationNativeSecretWordChecked.implementation setup.source inside candidate (input setup.joint setup.dh seed scalar))
        (((RegistrationNativeSecretWordOwners.finish setup source index packet).run owners).run env) := by
  simp only [RegistrationNativePublicOwners.finish, RegistrationNativeSecretWordOwners.finish, StateT.run]
  cases found : owners[index]? with
  | none => rfl
  | some owner =>
      simp only [simulateQ_map]
      cases scalarShape : owner.scalar with
      | none =>
          have source := RegistrationNativeSecretWordCheckedBeaconFinish.finish (n := n) setup source inside candidate seed scalar packet owner.view env
          simp only [StateT.run] at source
          rw [source]
      | some ownScalar =>
          have source := RegistrationNativeSecretWordCheckedOrdinaryFinish.finish (n := n) setup ownScalar source inside candidate seed scalar packet owner.view env
          simp only [RegistrationNativeSecretWordCheckedOrdinary.original,
            RegistrationNativeSecretWordCheckedOrdinary.symbolic, QueryImpl.simulateQ_compose, StateT.run] at source
          rw [source]

attribute [local irreducible] RegistrationNativePublicOwners.finish RegistrationNativeSecretWordOwners.finish
  RegistrationNativeSecretWordCheckedFrontend.native RegistrationNativeSecretWordCheckedFrontend.implementation

/-- The actual whole frontend retains every terminal finish, consumed owner, native record and original application reply. -/
theorem finish (setup : Setup base KemSK) (source : RegistrationNativeMldsa.Source)
    (inside : RegistrationNativeSuffixKeyPrf.Prefix → Bool) (candidate : PqxdhKemIndCca.MlKemSharedSecret)
    (seed : IdentitySeed) (scalar : ScalarBytes) (index : Nat) (packet : Option registration.ResponsePacket) (before : State source) :
    simulateQ (RegistrationNativeSecretWordCheckedFrontend.native (n := n) (KemSK := KemSK) setup.source inside candidate (input setup.joint setup.dh seed scalar))
      ((RegistrationNativePublicFrontend.beacon (RegistrationNativePublicOwners.finish setup source index packet)).run (before.eval candidate)) =
      Prod.map id (State.eval candidate) <$>
        simulateQ (RegistrationNativeSecretWordCheckedFrontend.implementation setup.source inside candidate (input setup.joint setup.dh seed scalar))
          ((RegistrationNativeSecretWordFrontend.beacon (RegistrationNativeSecretWordOwners.finish setup source index packet)).run before) := by
  simp only [RegistrationNativePublicFrontend.beacon, RegistrationNativeSecretWordFrontend.beacon,
    StateT.run, simulateQ_map]
  rw [RegistrationNativeSecretWordCheckedFrontendLift.native_program,
    RegistrationNativeSecretWordCheckedFrontendLift.symbolic_program]
  simp only [State.eval]
  have localSource := finish_local (n := n) setup source inside candidate seed scalar index packet before.beacons before.environment
  simp only [StateT.run] at localSource
  rw [localSource]
  simp only [Functor.map_map]
  rfl

end BeaconcryptCore.Computational.RegistrationNativeSecretWordCheckedOwners
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordCheckedOwners.finish_local' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordCheckedOwners.finish_local
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordCheckedOwners.finish' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordCheckedOwners.finish
