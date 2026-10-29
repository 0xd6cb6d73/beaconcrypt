-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSelectiveEntropyNative

/-! Every non-Beacon-record raw callback of the actual thin frontend is exactly its initialized entropy environment callback. The actual pure-start field is irrelevant to these reached-state laws; public startup hashing stays outside the original ledger and in the same World. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSelectiveEntropyOrdinary
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeHiddenInterpreter (Provider)
open RegistrationNativeSelectiveEntropyEnvironment (State environment)
open RegistrationNativeSelectiveEntropyNative (handler)
variable {n : Nat} {ι KemSK ProviderState : Type} {base : OracleSpec ι}

def Ordinary : RegistrationNativeInterface.Spec.Domain → Prop
  | .inr (.beaconSend _ _) | .inr (.beaconRaw _ _) => False
  | _ => True

/-- The actual reached native ordinary callback has precisely the original entropy-interface World AST. -/
theorem query_source (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (source : RegistrationNativeMldsa.Source) (credential : RegistrationNativeMldsa.Credential source)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret) (provider : Provider KemSK ProviderState) (selectedOwner selectedAccept : Nat)
    (startup : ProbComp (Option (PqxdhLiveServerConstruction.Created Unit × State n KemSK ProviderState source)))
    (query : RegistrationNativeInterface.Spec.Domain) (ordinary : Ordinary query)
    (before : State n KemSK ProviderState source) :
    (handler setup checks wire source credential seed scalar candidate provider selectedOwner selectedAccept query).run before =
      (RegistrationNativeEntropyWorld.native (environment setup checks wire source credential seed scalar candidate provider
        selectedOwner selectedAccept startup) query).run before := by
  cases query with
  | inl coin =>
      rw [RegistrationNativeSelectiveEntropyNative.coin_source]
      simp only [RegistrationNativeEntropyWorld.native, StateT.run_lift, bind_pure_comp]
      rfl
  | inr command => cases command with
    | create edPin mlPin keyId =>
        exact RegistrationNativeSelectiveEntropyNative.environment_source setup checks wire source credential seed scalar candidate provider
          selectedOwner selectedAccept ⟨.create edPin mlPin keyId, trivial⟩ before
    | bundle owner =>
        exact RegistrationNativeSelectiveEntropyNative.environment_source setup checks wire source credential seed scalar candidate provider
          selectedOwner selectedAccept ⟨.bundle owner, trivial⟩ before
    | accept raw =>
        exact RegistrationNativeSelectiveEntropyNative.environment_source setup checks wire source credential seed scalar candidate provider
          selectedOwner selectedAccept ⟨.accept raw, trivial⟩ before
    | build handle payload =>
        exact RegistrationNativeSelectiveEntropyNative.environment_source setup checks wire source credential seed scalar candidate provider
          selectedOwner selectedAccept ⟨.build handle payload, trivial⟩ before
    | finish owner raw =>
        exact RegistrationNativeSelectiveEntropyNative.environment_source setup checks wire source credential seed scalar candidate provider
          selectedOwner selectedAccept ⟨.finish owner raw, trivial⟩ before
    | hmac key bytes =>
        exact RegistrationNativeSelectiveEntropyNative.environment_source setup checks wire source credential seed scalar candidate provider
          selectedOwner selectedAccept ⟨.hmac key bytes, trivial⟩ before
    | hash bytes =>
        rw [RegistrationNativeSelectiveEntropyNative.hash_source]
        simp only [RegistrationNativeEntropyWorld.native, StateT.run_lift, bind_pure_comp]
        rfl
    | serverSend keyId plaintext =>
        rw [RegistrationNativeSelectiveEntropyNative.server_send_source]
        simp only [RegistrationNativeEntropyWorld.native, StateT.run_lift, bind_pure_comp]
        rfl
    | serverRaw raw =>
        rw [RegistrationNativeSelectiveEntropyNative.server_raw_source]
        simp only [RegistrationNativeEntropyWorld.native, StateT.run_lift, bind_pure_comp]
        rfl
    | beaconSend owner bytes | beaconRaw owner raw => exact ordinary.elim

end BeaconcryptCore.Computational.RegistrationNativeSelectiveEntropyOrdinary

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSelectiveEntropyOrdinary.query_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSelectiveEntropyOrdinary.query_source
