-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetAliasOrdinal
import BeaconcryptCore.Computational.RegistrationNativeG3NativeCheckedUniformSource
import BeaconcryptCore.Computational.RegistrationNativeInstallKernelStorage

/-! At each genuine early challenge and reached cold native frontend, the original good target probability implies its selected final installation ordinal. The proof uses the complete actual native-to-Word byte source and its normalized finite-table completion; no protected Ready, hidden-origin or execution equality is a caller premise. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeG3NativeTargetFixed
open PqxdhServerAuthExperiment (Setup Checks)
open PqxdhDeploymentInterface (FreshBounds Mode Budget)
open PqxdhKemIndCca
open RegistrationNativeG3NativeCheckedUniformSource (Result openProgram)
variable {n : Nat} {ι KemSK Value : Type} {base : OracleSpec ι}
variable (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
  (source : RegistrationNativeMldsa.Source) (route : RawCtxServerRouting.SenderDecoder)
  (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
  (serverKeyId : U64) (bounds : FreshBounds) (mode : Mode)
  (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
  (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value) (budget : Budget)
  (selectedTarget : Fin budget.accept × Fin budget.capacity)
  (pairs : List (MlKem768PublicKey × KemSK)) (chosen : MlKem768PublicKey × KemSK) (challenge : MlKem768Ciphertext)
  (candidate : MlKemSharedSecret) (before : RegistrationNativeSecretWordMessage.State source)
  (ordinary : RegistrationNativePublicInterpreter.State n KemSK)
local notation "target" => setup.joint.staticDh seed (setup.dh.publicKey scalar)

noncomputable def game : ProbComp (Result source Value) :=
  (simulateQ (RegistrationNativeOpenKeyKemEarlySource.reference setup.baseImpl setup.kem selectedTarget.2.val pairs chosen.1 challenge candidate)
    (openProgram setup checks wire source route sign selectedTarget.2.val selectedTarget.1.val (setup.dh.publicKey scalar) serverKeyId bounds mode
      seed scalar target work before ordinary)).run' ((PqxdhLiveKemBirth.empty, none), ∅)

def Good (claim : Value → Option (Nat × Pqxdh.Bytes)) (result : Result source Value) : Prop :=
  RegistrationNativePrekeyEvents.GoodAt setup.source.crypto wire serverKeyId budget selectedTarget claim
    (result.1.1.1, (result.1.1.2, ()))

def Hit (claim : Value → Option (Nat × Pqxdh.Bytes)) (result : Result source Value) : Prop :=
  RegistrationNativeInstallTarget.Claimed claim result.1.1.1 result.1.1.2 result.2.events
    (RegistrationNativeInstallKernelStorage.Selected setup seed scalar candidate)

/-- The actual complete fixed native early source supplies the claimed selected final ordinal of every original good target. -/
theorem probability (bounded : RegistrationNativeInterface.Respects budget work) (reserved : budget.create ≤ pairs.length)
    (chosenAt : pairs[selectedTarget.2.val]? = some chosen) (readback : RegistrationNativeWire.InitReadBack wire)
    (responseReadback : RegistrationNativeWire.ResponseReadBack wire)
    (claim : Value → Option (Nat × Pqxdh.Bytes)) (empty : before.server.sessions = [])
    (initialCounter : before.parsedAccepts = 0) (ownersEmpty : before.beacons = [])
    (initialPin : PqxdhRefinement.absBytes before.server.pin.binding.identity_public_key = (setup.joint.publicKeys seed).ed25519.toList) :
    Pr{let result ← game setup checks wire source route sign serverKeyId bounds mode seed scalar work budget selectedTarget pairs chosen challenge candidate before ordinary}[
      Good setup wire source serverKeyId budget selectedTarget claim result] ≤
    Pr{let result ← game setup checks wire source route sign serverKeyId bounds mode seed scalar work budget selectedTarget pairs chosen challenge candidate before ordinary}[
      Hit setup source seed scalar candidate claim result] := by
  rw [game, RegistrationNativeG3NativeCheckedUniformSource.fixed_source setup checks wire source route sign
    selectedTarget.2.val selectedTarget.1.val (setup.dh.publicKey scalar) serverKeyId bounds mode seed scalar target work before ordinary empty
      selectedTarget.2.val pairs chosen.1 challenge candidate]
  simp only [prEvent_map]
  have actual := RegistrationNativeSecretWordTargetAliasOrdinal.bytes_probability setup checks wire route sign seed scalar pairs chosen challenge
    serverKeyId bounds mode work budget selectedTarget bounded reserved chosenAt readback responseReadback claim before initialCounter ownersEmpty initialPin ordinary candidate
  simp only [Good, Hit, RegistrationNativeG3NativeCheckedAliasSource.view, Prod.map_def, id_eq,
    RegistrationNativeSecretWordCheckedTrace.state, RegistrationNativeG3NativeCheckedAliasSource.aliasClient]
  convert actual using 1; rfl

end BeaconcryptCore.Computational.RegistrationNativeG3NativeTargetFixed
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3NativeTargetFixed.probability' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3NativeTargetFixed.probability
