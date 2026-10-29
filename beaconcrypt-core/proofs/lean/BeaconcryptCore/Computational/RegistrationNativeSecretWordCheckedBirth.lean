-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSecretWordCheckedFrontendLift
import BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetBirth

/-! Actual birth and outgoing publication never consume a KEM shared-secret reply. Their derived concrete footprint therefore permits the candidate-free zero realization in the symbolic executable roster, while preserving every original result, roster field, failed signing attempt and current environment. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSecretWordCheckedBirth
open PqxdhServerAuthExperiment (Setup)
open RegistrationNativeSecretWordMessage (Message input State)
open PqxdhJointIdentity (IdentitySeed PeerEncoding)
open PqxdhJointGapDh (ScalarBytes)
open RegistrationWorldAgreementCompiler (EnvState)
variable {n : Nat} {ι KemSK Auxiliary : Type} {base : OracleSpec ι}

/-- Actual source creation equals the symbolic roster operation, including every optional constructor failure. -/
theorem create_local (setup : Setup base KemSK) (source : RegistrationNativeMldsa.Source)
    (inside : RegistrationNativeSuffixKeyPrf.Prefix → Bool) (candidate : PqxdhKemIndCca.MlKemSharedSecret)
    (seed : IdentitySeed) (scalar : ScalarBytes) (selected : Nat) (publicPrekey : PeerEncoding)
    (edPin : Std.Array U8 32#usize) (mlPin : Std.Array U8 1952#usize) (keyId : U64)
    (owners : RegistrationNativePublicOwners.State source) (env : EnvState Auxiliary) :
    simulateQ (RegistrationNativeSecretWordChecked.native (n := n) setup.source inside candidate (input setup.joint setup.dh seed scalar))
      (((RegistrationNativePublicOwners.create setup source selected publicPrekey edPin mlPin keyId).run owners).run env) =
      simulateQ (RegistrationNativeSecretWordChecked.implementation setup.source inside candidate (input setup.joint setup.dh seed scalar))
        (((RegistrationNativeSecretWordOwners.create setup source selected publicPrekey edPin mlPin keyId).run owners).run env) := by
  unfold RegistrationNativeSecretWordChecked.native
  rw [QueryImpl.simulateQ_compose, RegistrationNativeSecretWordTargetBirth.create_realize setup selected publicPrekey candidate edPin mlPin keyId owners env]
  rfl

/-- Actual complete outgoing publication has the same roster and environment under the candidate-free executable realization. -/
theorem bundle_local (setup : Setup base KemSK) (source : RegistrationNativeMldsa.Source) (wire : RegistrationNativeWire.Wire)
    (inside : RegistrationNativeSuffixKeyPrf.Prefix → Bool) (candidate : PqxdhKemIndCca.MlKemSharedSecret)
    (seed : IdentitySeed) (scalar : ScalarBytes) (selected : Nat) (publicPrekey : PeerEncoding) (index : Nat)
    (owners : RegistrationNativePublicOwners.State source) (env : EnvState Auxiliary) :
    simulateQ (RegistrationNativeSecretWordChecked.native (n := n) setup.source inside candidate (input setup.joint setup.dh seed scalar))
      (((RegistrationNativePublicOwners.bundle setup source wire selected publicPrekey index).run owners).run env) =
      simulateQ (RegistrationNativeSecretWordChecked.implementation setup.source inside candidate (input setup.joint setup.dh seed scalar))
        (((RegistrationNativeSecretWordOwners.bundle setup source wire selected publicPrekey index).run owners).run env) := by
  unfold RegistrationNativeSecretWordChecked.native
  rw [QueryImpl.simulateQ_compose, RegistrationNativeSecretWordTargetBirth.bundle_realize setup wire selected index publicPrekey candidate owners env]
  rfl

attribute [local irreducible] RegistrationNativePublicOwners.create RegistrationNativeSecretWordOwners.create
  RegistrationNativePublicOwners.bundle RegistrationNativeSecretWordOwners.bundle
  RegistrationNativeSecretWordCheckedFrontend.native RegistrationNativeSecretWordCheckedFrontend.implementation

/-- Complete whole-frontend creation retains the actual shared World effects and the full symbolic session table. -/
theorem create (setup : Setup base KemSK) (source : RegistrationNativeMldsa.Source)
    (inside : RegistrationNativeSuffixKeyPrf.Prefix → Bool) (candidate : PqxdhKemIndCca.MlKemSharedSecret)
    (seed : IdentitySeed) (scalar : ScalarBytes) (selected : Nat) (publicPrekey : PeerEncoding)
    (edPin : Std.Array U8 32#usize) (mlPin : Std.Array U8 1952#usize) (keyId : U64) (before : State source) :
    simulateQ (RegistrationNativeSecretWordCheckedFrontend.native (n := n) (KemSK := KemSK) setup.source inside candidate (input setup.joint setup.dh seed scalar))
      ((RegistrationNativePublicFrontend.beacon
        (RegistrationNativePublicOwners.create setup source selected publicPrekey edPin mlPin keyId)).run (before.eval candidate)) =
      Prod.map id (State.eval candidate) <$>
        simulateQ (RegistrationNativeSecretWordCheckedFrontend.implementation setup.source inside candidate (input setup.joint setup.dh seed scalar))
          ((RegistrationNativeSecretWordFrontend.beacon
            (RegistrationNativeSecretWordOwners.create setup source selected publicPrekey edPin mlPin keyId)).run before) := by
  simp only [RegistrationNativePublicFrontend.beacon, RegistrationNativeSecretWordFrontend.beacon,
    StateT.run, simulateQ_map]
  rw [RegistrationNativeSecretWordCheckedFrontendLift.native_program,
    RegistrationNativeSecretWordCheckedFrontendLift.symbolic_program]
  simp only [State.eval]
  have localSource := create_local (n := n) setup source inside candidate seed scalar selected publicPrekey edPin mlPin keyId before.beacons before.environment
  simp only [StateT.run] at localSource
  rw [localSource]
  simp only [Functor.map_map]
  rfl

/-- The original full publication reply and every failed poststate are preserved in the complete symbolic frontend. -/
theorem bundle (setup : Setup base KemSK) (source : RegistrationNativeMldsa.Source) (wire : RegistrationNativeWire.Wire)
    (inside : RegistrationNativeSuffixKeyPrf.Prefix → Bool) (candidate : PqxdhKemIndCca.MlKemSharedSecret)
    (seed : IdentitySeed) (scalar : ScalarBytes) (selected : Nat) (publicPrekey : PeerEncoding) (index : Nat) (before : State source) :
    simulateQ (RegistrationNativeSecretWordCheckedFrontend.native (n := n) (KemSK := KemSK) setup.source inside candidate (input setup.joint setup.dh seed scalar))
      ((RegistrationNativePublicFrontend.beacon
        (RegistrationNativePublicOwners.bundle setup source wire selected publicPrekey index)).run (before.eval candidate)) =
      Prod.map id (State.eval candidate) <$>
        simulateQ (RegistrationNativeSecretWordCheckedFrontend.implementation setup.source inside candidate (input setup.joint setup.dh seed scalar))
          ((RegistrationNativeSecretWordFrontend.beacon
            (RegistrationNativeSecretWordOwners.bundle setup source wire selected publicPrekey index)).run before) := by
  simp only [RegistrationNativePublicFrontend.beacon, RegistrationNativeSecretWordFrontend.beacon,
    StateT.run, simulateQ_map]
  rw [RegistrationNativeSecretWordCheckedFrontendLift.native_program,
    RegistrationNativeSecretWordCheckedFrontendLift.symbolic_program]
  simp only [State.eval]
  have localSource := bundle_local (n := n) setup source wire inside candidate seed scalar selected publicPrekey index before.beacons before.environment
  simp only [StateT.run] at localSource
  rw [localSource]
  simp only [Functor.map_map]
  rfl

end BeaconcryptCore.Computational.RegistrationNativeSecretWordCheckedBirth
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordCheckedBirth.create_local' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordCheckedBirth.create_local
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordCheckedBirth.bundle_local' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordCheckedBirth.bundle_local
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordCheckedBirth.create' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordCheckedBirth.create
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordCheckedBirth.bundle' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordCheckedBirth.bundle
