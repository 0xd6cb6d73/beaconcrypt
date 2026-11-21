-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeOpenRetained
import BeaconcryptCore.Computational.RegistrationNativeKeyBounds

/-! The retained prepare/material compiler and PRK-free key compiler leave indexed KEM requests external at both stages. The normalized native KEM interface has the108-byte table and ordinary public KEM operations in its pool-free ambient service. Thus an eventual CCA experiment need not receive the selected KEM secret or assert that a closed real encapsulation simulates its candidate branch. Source closure, complete-client caps and the KEM game instantiation are separate theorems. -/
open OracleComp OracleSpec CoreModels
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RegistrationNativeOpenKey
open RegistrationNativeRelatedFamily (Message)
open PqxdhJointKdfGame (FixedHkdfSha512NoSaltSource)
variable {KemSK Value : Type}

abbrev PhaseSpec (KemSK : Type) := RegistrationNativeKeyPhases.Spec + RegistrationNativePublicFrontend.RoutedKem KemSK
abbrev Spec (KemSK : Type) := RegistrationNativeKeyHybrid.Spec + RegistrationNativePublicFrontend.RoutedKem KemSK
abbrev Ambient := RegistrationNativeKeyHybrid.Spec +
  (RegistrationNativeKemInterface.OtherSpec + RegistrationNativeKemInterface.EncapsulationSpec)
abbrev NativeSpec (KemSK : Type) := RegistrationNativeKemInterface.Spec Ambient KemSK

def phaseLift : QueryImpl RegistrationNativeKeyPhases.Spec (OracleComp (PhaseSpec KemSK)) :=
  fun query => (PhaseSpec KemSK).query (.inl query)

def keyLift : QueryImpl RegistrationNativeKeyHybrid.Spec (OracleComp (Spec KemSK)) :=
  fun query => (Spec KemSK).query (.inl query)

def phaseCompiler : QueryImpl (RegistrationNativeOpenRetained.Spec KemSK)
    (StateT RegistrationNativeRetainedService.Flags (OracleComp (PhaseSpec KemSK)))
  | .inl query => fun before => simulateQ phaseLift ((RegistrationNativeRetainedService.compiler query).run before)
  | .inr query => StateT.lift ((PhaseSpec KemSK).query (.inr query))

def phaseClient (work : OracleComp (RegistrationNativeOpenRetained.Spec KemSK) Value) :
    OracleComp (PhaseSpec KemSK) Value :=
  (simulateQ phaseCompiler work).run' (fun _ => false)

def keyCompiler (source : FixedHkdfSha512NoSaltSource)
    (input : Message → Option Pqxdh.Bytes) (inside : Pqxdh.Bytes → Bool) :
    QueryImpl (PhaseSpec KemSK) (StateT RegistrationNativeKeyPhases.Meta (OracleComp (Spec KemSK)))
  | .inl query => fun before => simulateQ keyLift ((RegistrationNativeKeyCompiler.compiler source input inside query).run before)
  | .inr query => StateT.lift ((Spec KemSK).query (.inr query))

def client (source : FixedHkdfSha512NoSaltSource)
    (input : Message → Option Pqxdh.Bytes) (inside : Pqxdh.Bytes → Bool)
    (work : OracleComp (RegistrationNativeOpenRetained.Spec KemSK) Value) : OracleComp (Spec KemSK) Value :=
  (simulateQ (keyCompiler source input inside) (phaseClient work)).run' RegistrationNativeKeyPhases.emptyMeta

/-- Reassociate the existing actual routed KEM operations, retaining public ordinary encapsulation separately from the selected getter. -/
def native : QueryImpl (Spec KemSK) (OracleComp (NativeSpec KemSK))
  | .inl query => (NativeSpec KemSK).query (.inl (.inl query))
  | .inr (.inl query) => (NativeSpec KemSK).query (.inl (.inr query))
  | .inr (.inr query) => (NativeSpec KemSK).query (.inr query)

def nativeClient (source : FixedHkdfSha512NoSaltSource)
    (input : Message → Option Pqxdh.Bytes) (inside : Pqxdh.Bytes → Bool)
    (work : OracleComp (RegistrationNativeOpenRetained.Spec KemSK) Value) : OracleComp (NativeSpec KemSK) Value :=
  simulateQ native (client source input inside work)

/-- Root erasure forwards the same opaque KEM request and preserves its public success flags. -/
theorem phase_kem (query : (RegistrationNativePublicFrontend.RoutedKem KemSK).Domain)
    (before : RegistrationNativeRetainedService.Flags) :
    (phaseCompiler (.inr query)).run before =
      (fun reply => (reply, before)) <$> ((PhaseSpec KemSK).query (.inr query) : OracleComp (PhaseSpec KemSK) _) := by
  simp only [phaseCompiler, StateT.run_lift, bind_pure_comp]
  rfl

/-- The actual key-schedule compiler also forwards KEM requests, without reading or modifying PRKs or their preparation metadata. -/
theorem key_kem (source : FixedHkdfSha512NoSaltSource)
    (input : Message → Option Pqxdh.Bytes) (inside : Pqxdh.Bytes → Bool)
    (query : (RegistrationNativePublicFrontend.RoutedKem KemSK).Domain) (before : RegistrationNativeKeyPhases.Meta) :
    (keyCompiler source input inside (.inr query)).run before =
      (fun reply => (reply, before)) <$> ((Spec KemSK).query (.inr query) : OracleComp (Spec KemSK) _) := by
  simp only [keyCompiler, StateT.run_lift, bind_pure_comp]
  rfl

/-- The selected encapsulation remains the literal lower getter used by the existing native CCA cut. -/
theorem native_encapsulation (key : PqxdhKemIndCca.MlKem768PublicKey) :
    native (KemSK := KemSK) (.inr (.inr (.inr key))) =
      ((NativeSpec KemSK).query (.inr (.inr key)) : OracleComp (NativeSpec KemSK) _) := rfl

/-- Pool creation retains its actual opaque handle/public-key reply and never returns the generated secret key. -/
theorem native_create : native (KemSK := KemSK) (.inr (.inr (.inl .create))) =
    ((NativeSpec KemSK).query (.inr (.inl .create)) : OracleComp (NativeSpec KemSK) _) := rfl

end BeaconcryptCore.Computational.RegistrationNativeOpenKey

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeOpenKey.phase_kem' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeOpenKey.phase_kem
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeOpenKey.key_kem' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeOpenKey.key_kem
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeOpenKey.native_encapsulation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeOpenKey.native_encapsulation
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeOpenKey.native_create' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeOpenKey.native_create
