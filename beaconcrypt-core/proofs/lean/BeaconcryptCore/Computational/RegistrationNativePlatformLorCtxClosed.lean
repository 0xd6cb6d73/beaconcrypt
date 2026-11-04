-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformLorCtxLeaves
import BeaconcryptCore.Computational.RegistrationNativePlatformLorClosedDictionary
import BeaconcryptCore.Computational.RegistrationNativeSecretWordCheckedFrontendLift
import BeaconcryptCore.Computational.RegistrationNativeSecretWordBeaconSource
/-! The literal native request surface realizes through the open symbolic dictionary while the physical World remains free. The proof uses the concrete per-query source equations, not a whole-controller law. All arbitrary adaptive native work and its complete private/physical poststate can then be transported by the generic state projection theorem. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformLorCtxClosed
open PqxdhServerAuthExperiment (Setup)
open PqxdhKemIndCca
open RegistrationNativePlatformLorCtxLeaves (World Symbolic frame)
variable {n : Nat} {I KemSK Value : Type} {base : OracleSpec I}
variable (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes) (candidate : MlKemSharedSecret)
    (unused : QueryImpl RegistrationNativeSecretWordService.Combined (World n))
    (selected : Nat) (pairs : List (MlKem768PublicKey × KemSK)) (publicKey : MlKem768PublicKey) (challenge : MlKem768Ciphertext)
local notation "symbolicProvider" => RegistrationNativeSecretWordKemEarly.early setup.baseImpl setup.kem selected pairs publicKey challenge
local notation "actualProvider" => RegistrationNativeSecretWordKemEarly.actual setup.baseImpl setup.kem selected pairs publicKey challenge candidate
local notation "symbolic" => RegistrationNativePlatformLorCtxLeaves.lower setup wire sign seed scalar candidate unused symbolicProvider
local notation "actual" => RegistrationNativeSelectiveHiddenInterpreter.handler setup wire sign seed scalar candidate actualProvider

variable {Physical : Type}
    (physical : QueryImpl (PqxdhRecordLiftInterface.WorldSpec n) (StateT Physical ProbComp))
noncomputable def implementation : QueryImpl (RegistrationNativeSecretWordInterface.Spec n KemSK)
    (StateT (Symbolic n KemSK × Physical) ProbComp) :=
  (QueryImpl.mapStateTBase physical symbolic).flattenStateT

theorem source_support (query : (RegistrationNativeSecretWordInterface.Spec n KemSK).Domain)
    (before : Symbolic n KemSK × Physical)
    (result : (RegistrationNativeSecretWordInterface.Spec n KemSK).Range query × (Symbolic n KemSK × Physical))
    (supported : result ∈ support ((implementation setup wire sign seed scalar candidate unused selected pairs publicKey challenge physical query).run before)) :
    (result.1,result.2.1.1) ∈ support ((RegistrationNativePlatformLorOpenDictionary.handler setup wire sign
      (RegistrationNativeSecretWordMessage.input setup.joint setup.dh seed scalar)
      (RegistrationNativeSecretWordProtection.inside (setup.joint.staticDh seed (setup.dh.publicKey scalar))) symbolicProvider query).run before.1.1) := by
  rw [implementation,QueryImpl.flattenStateT_mapStateTBase_apply_run,support_map] at supported
  obtain ⟨⟨⟨reply,after⟩,physicalAfter⟩,called,equal⟩ := supported
  cases equal
  have first : (reply,after) ∈ support ((symbolic query).run before.1) := by
    apply OracleComp.support_simulateQ_run'_subset physical _ before.2
    rw [StateT.run'_eq,support_map]
    exact Set.mem_image_of_mem Prod.fst called
  rw [RegistrationNativePlatformLorCtxLeaves.lower,QueryImpl.flattenStateT_mapStateTBase_apply_run,support_map] at first
  obtain ⟨opened,queried,equal⟩ := first
  cases equal
  apply OracleComp.support_simulateQ_run'_subset (RegistrationNativePlatformLorCtxLeaves.closing setup seed scalar candidate unused) _ before.1.2
  rw [StateT.run'_eq,support_map]
  exact Set.mem_image_of_mem Prod.fst queried

theorem contract : RegistrationNativePlatformLorSourceKem.Contract
    (implementation setup wire sign seed scalar candidate unused selected pairs publicKey challenge physical)
    (fun current => current.1.1.kem) (RegistrationNativeSecretWordMessage.input setup.joint setup.dh seed scalar) symbolicProvider := by
  constructor
  · intro message before result supported
    exact RegistrationNativePlatformLorOpenDictionary.prepare_support setup wire sign
      (RegistrationNativeSecretWordMessage.input setup.joint setup.dh seed scalar)
      (RegistrationNativeSecretWordProtection.inside (setup.joint.staticDh seed (setup.dh.publicKey scalar))) symbolicProvider
      message before.1.1 (result.1,result.2.1.1)
      (source_support setup wire sign seed scalar candidate unused selected pairs publicKey challenge physical _ before result supported)
  · intro query before result supported
    exact RegistrationNativePlatformLorOpenDictionary.kem_support setup wire sign
      (RegistrationNativeSecretWordMessage.input setup.joint setup.dh seed scalar)
      (RegistrationNativeSecretWordProtection.inside (setup.joint.staticDh seed (setup.dh.publicKey scalar))) symbolicProvider
      query before.1.1 (result.1,result.2.1.1)
      (source_support setup wire sign seed scalar candidate unused selected pairs publicKey challenge physical _ before result supported)
  · intro query ordinary before result supported
    exact RegistrationNativePlatformLorOpenDictionary.nonrouted_kem setup wire sign
      (RegistrationNativeSecretWordMessage.input setup.joint setup.dh seed scalar)
      (RegistrationNativeSecretWordProtection.inside (setup.joint.staticDh seed (setup.dh.publicKey scalar))) symbolicProvider
      query ordinary before.1.1 (result.1,result.2.1.1)
      (source_support setup wire sign seed scalar candidate unused selected pairs publicKey challenge physical _ before result supported)
end BeaconcryptCore.Computational.RegistrationNativePlatformLorCtxClosed

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorCtxClosed.source_support' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorCtxClosed.source_support

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorCtxClosed.contract' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorCtxClosed.contract
