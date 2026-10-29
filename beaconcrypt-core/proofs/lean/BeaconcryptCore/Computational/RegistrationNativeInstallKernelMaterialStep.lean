-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeInstallKernelServer
import BeaconcryptCore.Computational.RegistrationNativeInstallKernelBeacon
import BeaconcryptCore.Computational.RegistrationNativeInstallTypedHandles
import BeaconcryptCore.Computational.RegistrationNativeInstallKernelStorage
import BeaconcryptCore.Computational.RegistrationNativeInstallBeaconTyped

/-! Actual guarded material callbacks supply the complete role-local ordinal step receipt. Every new selected descriptor is paired only with the literal successful public handle of that same callback. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeInstallKernelMaterialStep
open PqxdhServerAuthExperiment (Setup Checks Codec)
open RegistrationNativeSelectiveInstallKernel (State typed)
open RegistrationNativeInstallKernelStorage (events slots Selected Valid)
open RegistrationNativeInstallTypedEntry (entry)
open RegistrationNativeInstallStep (RoleStep)
variable {n : Nat} {ι KemSK ProviderState Reader Response Secret : Type} {base : OracleSpec ι}
variable {source : RegistrationNativeMldsa.Source}
variable (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
  (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
  (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
  (candidate : PqxdhKemIndCca.MlKemSharedSecret) (provider : RegistrationNativeHiddenInterpreter.Provider KemSK ProviderState)
  (service : QueryImpl (PqxdhRecordLiftProtocol.ServiceSpec n) (StateT Secret ProbComp))
  (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder) (selectedOwner selectedAccept : Nat)

/-- The literal actual typed Server build supplies its complete new-handle ordinal receipt for every result. -/
theorem build (role : PqxdhRecordLiftInterface.Role) (handle : Nat) (application : Option (Slice U8))
    (before : State n KemSK ProviderState Secret source)
    (result : RustM (Option (U64 × Pqxdh.Bytes)) × State n KemSK ProviderState Secret source)
    (supported : result ∈ support ((typed setup checks wire sign seed scalar candidate provider service codec route selectedOwner selectedAccept
      (.inr (.build handle application))).run before)) :
    RoleStep role (events before) (events result.2) (entry (.inr (.build handle application)) result.1)
      (slots result.2) (Selected setup seed scalar candidate) := by
  obtain ⟨added, observed, count, installed⟩ := RegistrationNativeInstallKernelServer.build_step
    setup checks wire sign seed scalar candidate provider service codec route selectedOwner selectedAccept role handle application before result supported
  refine ⟨added, observed, count.trans (RegistrationNativeInstallTypedHandles.build_length role handle application result.1).symm, ?_⟩
  intro position message publicHandle messageAt handleAt selected
  obtain ⟨keyId, bytes, reply, same⟩ := RegistrationNativeInstallTypedHandles.build_handle role handle application result.1 position publicHandle handleAt
  obtain ⟨slot, hidden⟩ := installed keyId bytes reply message (List.mem_of_getElem? messageAt) selected
  subst publicHandle
  exact Option.isSome_iff_exists.mpr ⟨slot, hidden⟩


private theorem finish_failed (role : PqxdhRecordLiftInterface.Role) (index : Nat) (packet : Option registration.ResponsePacket)
    (before : State n KemSK ProviderState Secret source)
    (result : RustM (Option Pqxdh.Bytes) × State n KemSK ProviderState Secret source)
    (supported : result ∈ support ((typed setup checks wire sign seed scalar candidate provider service codec route selectedOwner selectedAccept
      (.inr (.finish index packet))).run before))
    (failed : RegistrationNativeInstallBeaconComplete.present result.1 = false) :
    RoleStep role (events before) (events result.2) (entry (.inr (.finish index packet)) result.1)
      (slots result.2) (Selected setup seed scalar candidate) := by
  have original := RegistrationNativeInstallKernelSupport.open_support setup checks wire sign seed scalar candidate provider service codec route
    selectedOwner selectedAccept (.inr (.finish index packet)) before result supported
  obtain ⟨added, observed, count⟩ := RegistrationNativeInstallBeaconTyped.finish setup checks wire sign selectedOwner selectedAccept
    (setup.dh.publicKey scalar) role index packet before.2.1.1.1.1 before.1 ((result.1, result.2.2.1.1.1.1), result.2.1) original
  have empty : added = [] := List.eq_nil_of_length_eq_zero (by simpa only [failed, Bool.false_eq_true, and_false, ite_false] using count)
  apply RegistrationNativeInstallStep.of_quiet
  · simpa only [empty, List.append_nil, events] using observed
  · apply List.eq_nil_of_length_eq_zero
    rw [RegistrationNativeInstallTypedHandles.finish_length, failed]
    simp only [Bool.false_eq_true, and_false, ite_false]

private theorem finish_succeeded (role : PqxdhRecordLiftInterface.Role) (index : Nat) (packet : Option registration.ResponsePacket)
    (before : State n KemSK ProviderState Secret source) (valid : Valid before)
    (owner : RegistrationNativePublicOwners.Owner source) (found : before.2.1.1.1.1.beacons[index]? = some owner)
    (result : RustM (Option Pqxdh.Bytes) × State n KemSK ProviderState Secret source)
    (supported : result ∈ support ((typed setup checks wire sign seed scalar candidate provider service codec route selectedOwner selectedAccept
      (.inr (.finish index packet))).run before))
    (application : Pqxdh.Bytes) (successful : result.1 = .ok (some application)) :
    RoleStep role (events before) (events result.2) (entry (.inr (.finish index packet)) result.1)
      (slots result.2) (Selected setup seed scalar candidate) := by
  obtain ⟨reference, observed, installed⟩ := RegistrationNativeInstallKernelBeacon.finish_success
    setup checks wire sign seed scalar candidate provider service codec route selectedOwner selectedAccept index packet before owner found valid.1 result supported application successful
  refine ⟨if role = .beacon then [reference] else [], observed role, ?_, ?_⟩
  · rw [RegistrationNativeInstallTypedHandles.finish_length, successful]
    cases role <;> simp [RegistrationNativeInstallBeaconComplete.present]
  · intro position message publicHandle messageAt handleAt selected
    have member := List.mem_of_getElem? messageAt
    split at member
    · simp only [List.mem_singleton] at member
      subst message
      have same := RegistrationNativeInstallTypedHandles.finish_handle role index packet result.1 position publicHandle handleAt
      subst publicHandle
      obtain ⟨slot, hidden⟩ := installed selected
      exact Option.isSome_iff_exists.mpr ⟨slot, hidden⟩
    · cases member

/-- The literal actual typed owner finish supplies its complete new-handle ordinal receipt for every owner and result. -/
theorem finish (role : PqxdhRecordLiftInterface.Role) (index : Nat) (packet : Option registration.ResponsePacket)
    (before : State n KemSK ProviderState Secret source) (valid : Valid before)
    (result : RustM (Option Pqxdh.Bytes) × State n KemSK ProviderState Secret source)
    (supported : result ∈ support ((typed setup checks wire sign seed scalar candidate provider service codec route selectedOwner selectedAccept
      (.inr (.finish index packet))).run before)) :
    RoleStep role (events before) (events result.2) (entry (.inr (.finish index packet)) result.1)
      (slots result.2) (Selected setup seed scalar candidate) := by
  have unsuccessful (failed : RegistrationNativeInstallBeaconComplete.present result.1 = false) :=
    finish_failed setup checks wire sign seed scalar candidate provider service codec route selectedOwner selectedAccept
      role index packet before result supported failed
  cases reply : result.1 with
  | fail error | div => simpa only [reply] using unsuccessful (by rw [reply]; rfl)
  | ok replyValue => cases replyValue with
    | none => simpa only [reply] using unsuccessful (by rw [reply]; rfl)
    | some application =>
        cases found : before.2.1.1.1.1.beacons[index]? with
        | none =>
            have original := RegistrationNativeInstallKernelSupport.open_support setup checks wire sign seed scalar candidate provider service codec route
              selectedOwner selectedAccept (.inr (.finish index packet)) before result supported
            rw [RegistrationNativeInstallBeaconTyped.missing_source setup checks wire sign selectedOwner selectedAccept (setup.dh.publicKey scalar)
              index packet before.2.1.1.1.1 found] at original
            simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at original
            have absent : result.1 = .ok none := congrArg (fun value => value.1.1) original
            rw [reply] at absent
            cases absent
        | some owner =>
            simpa only [reply] using finish_succeeded setup checks wire sign seed scalar candidate provider service codec route selectedOwner selectedAccept
              role index packet before valid owner found result supported application reply

end BeaconcryptCore.Computational.RegistrationNativeInstallKernelMaterialStep

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeInstallKernelMaterialStep.build' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeInstallKernelMaterialStep.build

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeInstallKernelMaterialStep.finish' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeInstallKernelMaterialStep.finish
