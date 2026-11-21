-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformInstallServerTyped
import BeaconcryptCore.Computational.RegistrationNativePlatformSelectiveBuildSource
import BeaconcryptCore.Computational.RegistrationNativePlatformInstallKernelStorage
import BeaconcryptCore.Computational.RegistrationNativeInstallStep
import BeaconcryptCore.Computational.RegistrationNativeInstallTypedHandles
/-! The literal shared-platform Server build pairs its retained descriptor with the same returned physical peer, after every source and allocator outcome. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformInstallKernelServer
open PqxdhServerAuthExperiment (Setup Checks Codec)
open RegistrationNativePlatformSelectiveInstallKernel (State)
open RegistrationNativeInstallOrdinals (messages)
open RegistrationNativePlatformInstallKernelStorage (Valid events slots Selected)
open RegistrationNativeInstallStep (RoleStep)
open RegistrationNativeInstallTypedEntry (entry)
open BeaconcryptCore.Refinement
variable {n : Nat} {I KemSK ProviderState Platform E Reader Response Secret : Type} {base : OracleSpec I}
variable {source : RegistrationNativeMldsa.Source}
variable [primitive : AdapterSealPrimitive.Operations]
variable (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (credential : RegistrationNativeMldsa.Credential source)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret) (provider : RegistrationNativeHiddenInterpreter.Provider KemSK ProviderState)
    (selectedOwner selectedAccept : Nat)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
    (reserveFrame : Nat → StateT Platform ProbComp (core.result.Result Unit E)) (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (service : QueryImpl (PqxdhRecordLiftProtocol.ServiceSpec n) (StateT Secret ProbComp))
    (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
local notation "canonical" => RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire
local notation "sign" => RegistrationNativeMldsa.owned source credential
local notation "actual" => RegistrationNativePlatformSelectiveInstallKernel.typed setup wire seed scalar candidate provider checks credential selectedOwner selectedAccept
  view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer service codec route


private theorem build_hidden (handle : Nat) (application : Option (Slice U8))
    (before : State n KemSK ProviderState Platform Secret source) (ready : RegistrationServerReferenceRoot.Ready)
    (stored : before.2.1.1.1.1.1.server.sessions[handle]? = some (some ready))
    (result : RustM (Option (U64 × Pqxdh.Bytes)) × State n KemSK ProviderState Platform Secret source)
    (supported : result ∈ support ((actual (.inr (.build handle application))).run before))
    (keyId : U64) (bytes : Pqxdh.Bytes) (successful : result.1 = .ok (some (keyId,bytes)))
    (selected : Selected setup seed scalar candidate ready.reference) :
    ∃ slot, PqxdhRecordLiftIdeal.handleSlot result.2.2.1.2 (.peer keyId) = some slot := by
  have projected := Set.mem_image_of_mem (Prod.map id Prod.snd) supported
  rw [← support_map,RegistrationNativePlatformSelectiveInstallKernel.typed_erase] at projected
  change (result.1,result.2.2) ∈ support
    ((RegistrationNativeHiddenEnvironmentWorld.lower service codec route
      (RegistrationNativePlatformHiddenAllocationCore.close
        (RegistrationNativePlatformSelectiveEntropyBackend.handler setup canonical sign seed scalar candidate provider)
        (RegistrationNativePlatformPublicFrontend.executeLocal
          (RegistrationNativePlatformPublicFrontend.build setup sign view failure allocation erased helper writer reservePeer handle application source)))).run before.2) at projected
  have exactResult : (.ok (some (keyId,bytes)),result.2.2) = (result.1,result.2.2) := by rw [successful]
  rw [← exactResult] at projected
  exact RegistrationNativePlatformSelectiveBuildSource.build_hidden setup canonical sign seed scalar candidate provider
    view failure allocation erased helper writer reservePeer service codec route handle application ready before.2 result.2.2 stored selected keyId bytes projected

private theorem build_missing (role : PqxdhRecordLiftInterface.Role) (handle : Nat) (application : Option (Slice U8))
    (before : State n KemSK ProviderState Platform Secret source)
    (missing : ∀ ready, before.2.1.1.1.1.1.server.sessions[handle]? ≠ some (some ready))
    (result : RustM (Option (U64 × Pqxdh.Bytes)) × State n KemSK ProviderState Platform Secret source)
    (supported : result ∈ support ((actual (.inr (.build handle application))).run before)) :
    messages role result.2.1.events = messages role before.1.events ∧ result.1 = .ok none := by
  have original := RegistrationNativePlatformSelectiveInstallKernel.open_support setup wire seed scalar candidate provider checks credential selectedOwner selectedAccept
    view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer service codec route (.inr (.build handle application)) before result supported
  simp only [RegistrationNativePlatformPublicFrontend.handler] at original
  rw [RegistrationNativePlatformInstallServerTyped.build_source] at original
  cases stored : before.2.1.1.1.1.1.server.sessions[handle]? with
  | none =>
    simp only [RegistrationNativePlatformInstallServerControl.body,RegistrationNativePlatformServerMaterialFrontend.build,
      RegistrationServerMaterialFrontend.take,stored,StateT.run] at original
    exact ⟨congrArg (fun value => messages role value.2.events) original,congrArg (fun value => value.1.1) original⟩
  | some entry => cases entry with
    | none =>
      simp only [RegistrationNativePlatformInstallServerControl.body,RegistrationNativePlatformServerMaterialFrontend.build,
        RegistrationServerMaterialFrontend.take,stored,StateT.run] at original
      exact ⟨congrArg (fun value => messages role value.2.events) original,congrArg (fun value => value.1.1) original⟩
    | some ready => exact False.elim (missing ready stored)

/-- Every actual Server build supplies its exact successful-handle suffix and same-result selected physical slot. -/
theorem build_step (role : PqxdhRecordLiftInterface.Role) (handle : Nat) (application : Option (Slice U8))
    (before : State n KemSK ProviderState Platform Secret source)
    (result : RustM (Option (U64 × Pqxdh.Bytes)) × State n KemSK ProviderState Platform Secret source)
    (supported : result ∈ support ((actual (.inr (.build handle application))).run before)) :
    RoleStep role (events before) (events result.2) (entry (.inr (.build handle application)) result.1)
      (slots result.2) (Selected setup seed scalar candidate) := by
  have absent (missing : ∀ ready, before.2.1.1.1.1.1.server.sessions[handle]? ≠ some (some ready)) :
      RoleStep role (events before) (events result.2) (entry (.inr (.build handle application)) result.1)
        (slots result.2) (Selected setup seed scalar candidate) := by
    have quiet := build_missing setup checks wire credential seed scalar candidate provider selectedOwner selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer service codec route role handle application before missing result supported
    apply RegistrationNativeInstallStep.of_quiet
    · exact quiet.1
    · apply List.eq_nil_of_length_eq_zero
      rw [RegistrationNativeInstallTypedHandles.build_length,quiet.2]
      simp only [RegistrationNativeInstallBeaconComplete.present,Bool.false_eq_true,and_false,ite_false]
  cases stored : before.2.1.1.1.1.1.server.sessions[handle]? with
  | none => exact absent (by intro ready impossible; rw [stored] at impossible; cases impossible)
  | some entry => cases entry with
    | none => exact absent (by intro ready impossible; rw [stored] at impossible; cases impossible)
    | some ready =>
      have original := RegistrationNativePlatformSelectiveInstallKernel.open_support setup wire seed scalar candidate provider checks credential selectedOwner selectedAccept
        view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer service codec route (.inr (.build handle application)) before result supported
      have counted := RegistrationNativePlatformInstallServerTyped.build_live setup sign view failure allocation erased helper writer reservePeer
        role handle application ready before.2.1.1.1.1 stored before.1 ((result.1,result.2.2.1.1.1.1),result.2.1)
        (by simpa only [RegistrationNativePlatformPublicFrontend.handler] using original)
      have attach (keyId : U64) (bytes : Pqxdh.Bytes) (successful : result.1 = .ok (some (keyId,bytes)))
          (selected : Selected setup seed scalar candidate ready.reference) : (slots result.2 (.peer keyId)).isSome := by
        obtain ⟨slot,hidden⟩ := build_hidden setup checks wire credential seed scalar candidate provider selectedOwner selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer service codec route handle application before ready stored result supported keyId bytes successful selected
        exact Option.isSome_iff_exists.mpr ⟨slot,hidden⟩
      refine ⟨if role = .server ∧ RegistrationNativeInstallBeaconComplete.present result.1 = true then [ready.reference] else [],counted,?_,?_⟩
      · rw [RegistrationNativeInstallTypedHandles.build_length]
        split <;> rfl
      · intro position message publicHandle messageAt handleAt selected
        have member := List.mem_of_getElem? messageAt
        split at member
        · simp only [List.mem_singleton] at member
          subst message
          obtain ⟨keyId,bytes,successful,sameHandle⟩ := RegistrationNativeInstallTypedHandles.build_handle role handle application result.1 position publicHandle handleAt
          rw [sameHandle]
          exact attach keyId bytes successful selected
        · cases member

end BeaconcryptCore.Computational.RegistrationNativePlatformInstallKernelServer
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformInstallKernelServer.build_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformInstallKernelServer.build_step
