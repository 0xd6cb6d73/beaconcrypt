-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSelectiveHiddenService
import BeaconcryptCore.Computational.RegistrationNativeHiddenStartup
import BeaconcryptCore.Computational.RegistrationNativePublicCaps

/-! The selective native G3 client extends only the private material-service state with reduction-owned nonselected uniform108-byte outputs. All actual World, KEM, signing receipts, record commands and frontend controllers remain the existing ones. The selected candidate is used only by the private root-input classifier. It is not a hidden record seed. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSelectiveHiddenInterpreter
open PqxdhServerAuthExperiment (Setup Checks)
open PqxdhRecordLiftInterface (WorldSpec effectLift)
open RegistrationNativeHiddenInterpreter (Provider)
variable {n : Nat} {ι KemSK ProviderState Value : Type} {base : OracleSpec ι}

abbrev State (n : Nat) (KemSK ProviderState : Type) := RegistrationNativeHiddenInterpreter.State n KemSK ProviderState ×
  RegistrationNativeSelectiveHiddenService.KnownOracle.QueryCache
abbrev M (n : Nat) (KemSK ProviderState Value : Type) := StateT (State n KemSK ProviderState) (OracleComp (WorldSpec n)) Value

def initial (provider : ProviderState) : State n KemSK ProviderState := (RegistrationNativeHiddenInterpreter.initial provider, ∅)

def onBase (work : RegistrationNativeHiddenInterpreter.M n KemSK ProviderState Value) : M n KemSK ProviderState Value := fun before =>
  (fun result => (result.1, (result.2, before.2))) <$> work.run before.1

def onKeys (work : StateT (RegistrationNativeSelectiveHiddenService.State n)
    (OracleComp (PqxdhRecordLiftInterface.EnvEffects n)) Value) : M n KemSK ProviderState Value := fun before =>
  (fun result => (result.1, ({ before.1 with keys := result.2.1 }, result.2.2))) <$>
    simulateQ effectLift (work.run (before.1.keys, before.2))

noncomputable def handler (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret) (provider : Provider KemSK ProviderState) :
    QueryImpl (RegistrationNativePublicFrontend.Spec n KemSK) (M n KemSK ProviderState)
  | .inl (.inr (.inl (.inl message))) => onKeys (RegistrationNativeSelectiveHiddenService.demand setup.source
      (RegistrationNativeRelatedFamily.input setup.joint setup.dh seed scalar)
      (RegistrationNativeKeyFamilyPreparation.inside (setup.joint.staticDh seed (setup.dh.publicKey scalar))) candidate message)
  | query => onBase (RegistrationNativeHiddenInterpreter.handler setup wire sign seed scalar provider query)

/-- Every callback outside material demand is exactly the original actual thin implementation, with the extra nonselected table retained. -/
theorem query_other (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret) (provider : Provider KemSK ProviderState)
    (query : (RegistrationNativePublicFrontend.Spec n KemSK).Domain)
    (other : ¬RegistrationNativePublicCaps.IsDemand query) :
    handler setup wire sign seed scalar candidate provider query =
      onBase (RegistrationNativeHiddenInterpreter.handler setup wire sign seed scalar provider query) := by
  rcases query with (message | (message | common) | kem) | record
  · rfl
  · exact (other trivial).elim
  · rfl
  · rfl
  · rfl

/-- The actual material request runs through the one shared World effect surface; only service-owned tables are updated. -/
theorem query_demand (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret) (provider : Provider KemSK ProviderState)
    (message : RegistrationNativeRelatedFamily.Message) :
    handler (n := n) setup wire sign seed scalar candidate provider (.inl (.inr (.inl (.inl message)))) =
      onKeys (RegistrationNativeSelectiveHiddenService.demand setup.source
        (RegistrationNativeRelatedFamily.input setup.joint setup.dh seed scalar)
        (RegistrationNativeKeyFamilyPreparation.inside (setup.joint.staticDh seed (setup.dh.publicKey scalar))) candidate message) := rfl

noncomputable def run (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (source : RegistrationNativeMldsa.Source) (credential : RegistrationNativeMldsa.Credential source)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret) (provider : Provider KemSK ProviderState)
    (selectedOwner selectedAccept : Nat) (serverKeyId : U64)
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (frontend : RegistrationNativePublicFrontend.State source) (before : State n KemSK ProviderState) :=
  (simulateQ (handler setup wire (RegistrationNativeMldsa.owned source credential) seed scalar candidate provider)
    (RegistrationNativePublicFrontend.run setup checks wire source (RegistrationNativeMldsa.owned source credential)
      selectedOwner selectedAccept (setup.dh.publicKey scalar) serverKeyId bounds mode work frontend)).run before

end BeaconcryptCore.Computational.RegistrationNativeSelectiveHiddenInterpreter
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSelectiveHiddenInterpreter.query_other' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSelectiveHiddenInterpreter.query_other
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSelectiveHiddenInterpreter.query_demand' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSelectiveHiddenInterpreter.query_demand
