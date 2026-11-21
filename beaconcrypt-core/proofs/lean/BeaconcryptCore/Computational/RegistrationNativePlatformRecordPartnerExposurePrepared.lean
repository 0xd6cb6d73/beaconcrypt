-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposurePreparedCore
import BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposurePreparedFields
import BeaconcryptCore.Computational.RegistrationNativePlatformLorSourcePreparedTrace
/-! Actual native preparation flags retain the same valid source descriptors at every reached original prefix. Physical caches, provider state and all failure outcomes remain literal. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposurePrepared
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeSecretWordMessage (Message)
open RegistrationNativeSecretWord (Key)
open RegistrationNativeSecretWordInterface (Spec)
open RegistrationNativePlatformLorSourcePreparedTraceCore (Prepared)
open RegistrationNativePlatformOriginCallbackCut (Prefix)
variable {n : Nat} {I KemSK Physical A : Type} {base : OracleSpec I}
variable (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest →ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret)
    (unused : QueryImpl RegistrationNativeSecretWordService.Combined (OracleComp (PqxdhRecordLiftInterface.WorldSpec n)))
    (selected : Nat) (pairs : List (PqxdhKemIndCca.MlKem768PublicKey ×KemSK))
    (publicKey : PqxdhKemIndCca.MlKem768PublicKey) (challenge : PqxdhKemIndCca.MlKem768Ciphertext)
    (physical : QueryImpl (PqxdhRecordLiftInterface.WorldSpec n) (StateT Physical ProbComp))
local notation "Input"=>RegistrationNativeSecretWordMessage.input setup.joint setup.dh seed scalar
local notation "Current"=>RegistrationNativePlatformLorCtxLeaves.Symbolic n KemSK ×Physical
local notation "impl"=>RegistrationNativePlatformLorCtxClosed.implementation setup wire sign seed scalar candidate unused selected pairs publicKey challenge physical
local notation "actual"=>RegistrationNativePlatformLorStatefulSupport.trace impl
def flags (current : RegistrationNativePlatformLorCtxLeaves.Symbolic n KemSK ×Physical) : RegistrationNativeRelatedFamily.Message →Bool :=
  current.1.2.1.prepared
local notation "Trace"=>RegistrationNativeSecretWordFrontendTrace.State

/-- Optional source input validity is constant on complete native address evaluation, including atom/literal aliases. -/
theorem validity (first second : Message)
    (equal : RegistrationNativeSecretWordMessage.eval candidate first=RegistrationNativeSecretWordMessage.eval candidate second) :
    (Input first).isSome=(Input second).isSome := by
  have left := congrArg Option.isSome (RegistrationNativeSecretWordMessage.input_eval setup.joint setup.dh seed scalar candidate first)
  have right := congrArg Option.isSome (RegistrationNativeSecretWordMessage.input_eval setup.joint setup.dh seed scalar candidate second)
  simp only [Option.isSome_map] at left right
  rw [equal] at left
  exact left.trans right.symm

/-- The actual closed dictionary derives each individual native flag update of the chronological trace invariant. -/
theorem query (request : (Spec n KemSK).Domain) (before : Current)
    (result : (Spec n KemSK).Range request ×Current)
    (supported : result∈support ((impl request).run before)) :
    flags result.2=RegistrationNativePlatformRecordPartnerExposurePreparedCore.next
      (fun message=>(Input message).isSome) (RegistrationNativeSecretWordMessage.eval candidate) request (flags before) := by
  dsimp only [flags]
  rw [RegistrationNativePlatformRecordPartnerExposurePreparedFields.closed setup wire sign seed scalar candidate unused selected pairs publicKey challenge physical request before result supported]
  rcases request with (message|(message|common)|kem)|record
  · simp only [RegistrationNativePlatformRecordPartnerExposurePreparedFields.next,
      RegistrationNativePlatformLorCtxLeaves.nativeQuery,RegistrationNativePlatformRecordPartnerExposurePreparedCore.next]
    rw [←RegistrationNativeSecretWordMessage.input_eval]
    simp only [Option.isSome_map]
    funext address
    by_cases equal : address=RegistrationNativeSecretWordMessage.eval candidate message <;>
      simp only [Function.update_apply,equal,ite_true,ite_false]
  all_goals rfl

/-- Each reached original prefix retains the native preparation of every valid same-name tag in its own prior trace. -/
theorem at_prefix (work : OracleComp (Spec n KemSK) A)
    (before : Current) (after : Trace ×Current) (rest : OracleComp (Spec n KemSK) A)
    (path : Prefix actual work (RegistrationNativeSecretWordFrontendTrace.initial,before) rest after)
    (message : Message) (available : (Input message).isSome=true) (prepared : Prepared message after.1) :
    after.2.1.2.1.prepared (RegistrationNativeSecretWordMessage.eval candidate message)=true := by
  have good := RegistrationNativePlatformRecordPartnerExposurePreparedCore.at_prefix
    (fun message=>(Input message).isSome) (RegistrationNativeSecretWordMessage.eval candidate)
    (validity setup seed scalar candidate) impl flags
    (query setup wire sign seed scalar candidate unused selected pairs publicKey challenge physical)
    path (RegistrationNativePlatformRecordPartnerExposurePreparedCore.empty _ _ _ none)
  exact good message available prepared

end BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposurePrepared
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposurePrepared.validity' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposurePrepared.validity

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposurePrepared.query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposurePrepared.query

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposurePrepared.at_prefix' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposurePrepared.at_prefix
