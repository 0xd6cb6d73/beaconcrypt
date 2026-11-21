-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealBeaconAgreement
import BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealBeaconSuffix
/-! Arbitrary-choice source Beacon agreement is composed from the literal opaque-word collector and the actual stateful prepare echo. The physical World remains free and the same private provider/root-service state is retained. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealBeaconPhase
open PqxdhServerAuthExperiment (Setup)
open PqxdhKemIndCca
open RegistrationNativePlatformLorCtxLeaves (World Symbolic frame)
variable {n : Nat} {I KemSK Auxiliary : Type} {base : OracleSpec I}
variable (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes) (candidate : MlKemSharedSecret)
    (unused : QueryImpl RegistrationNativeSecretWordService.Combined (World n))
    (selected : Nat) (pairs : List (MlKem768PublicKey × KemSK)) (publicKey : MlKem768PublicKey) (challenge : MlKem768Ciphertext)
local notation "symbolicProvider" => RegistrationNativeSecretWordKemEarly.early setup.baseImpl setup.kem selected pairs publicKey challenge
local notation "actualProvider" => RegistrationNativeSecretWordKemEarly.actual setup.baseImpl setup.kem selected pairs publicKey challenge candidate
local notation "symbolic" => RegistrationNativePlatformLorCtxLeaves.lower setup wire sign seed scalar candidate unused symbolicProvider
local notation "actual" => RegistrationNativeSelectiveHiddenInterpreter.handler setup wire sign seed scalar candidate actualProvider

local notation "wordLocal" => symbolic ∘ₛ RegistrationNativeSecretWordInterface.liftLocal false
local notation "actualLocal" => actual ∘ₛ RegistrationNativePublicFrontend.liftLocal false
variable {source : RegistrationNativeMldsa.Source}
theorem phase_source (owner current : RegistrationBeaconReferenceCompiler.SelectedOwner source)
    (oneTime : PqxdhJointGapDh.ScalarBytes) (authenticated : registration.AuthenticatedResponse)
    (env : RegistrationWorldAgreementCompiler.EnvState RegistrationServerRoleBackend.State) (before : Symbolic n KemSK) :
    Prod.map id (frame candidate) <$>
      (simulateQ wordLocal
        (((RegistrationNativePlatformSecretWordFinish.phase setup wire owner oneTime authenticated).run current).run env)).run before =
      (simulateQ actualLocal
        (((RegistrationNativePlatformBeaconPhase.phase setup wire owner oneTime authenticated).run current).run env)).run (frame candidate before) := by
  simp only [RegistrationNativePlatformSecretWordFinish.phase,RegistrationNativePlatformBeaconPhase.phase,
    StateT.run_bind,StateT.run_lift,bind_pure_comp,simulateQ_bind,bind_map_left,map_bind]
  have sourceEq := RegistrationNativePlatformLorIdealBeaconAgreement.agreement_source setup wire sign seed scalar candidate unused selected pairs publicKey challenge
    owner oneTime authenticated env before
  rw [←sourceEq,bind_map_left]
  apply bind_congr
  rintro ⟨⟨prepared,envAfter⟩,after⟩
  simp only [Prod.map_apply,id_eq]
  exact RegistrationNativePlatformLorIdealBeaconSuffix.afterPrepared_source setup wire sign seed scalar candidate unused selected pairs publicKey challenge
    owner current prepared envAfter after
end BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealBeaconPhase

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealBeaconPhase.phase_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealBeaconPhase.phase_source
