-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeInstallKernelSupport
import BeaconcryptCore.Computational.RegistrationNativeInstallServerTyped
import BeaconcryptCore.Computational.RegistrationNativeSelectiveTypedServerUniversalOrigin

/-! The same actual guarded typed Server callback supplies both its exact successful descriptor suffix and its selected hidden handle. The current Ready is read from the literal initial frontend state shared by both source projections. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeInstallKernelServer
open PqxdhServerAuthExperiment (Setup Checks Codec)
open RegistrationNativeSelectiveInstallKernel (State typed)
open RegistrationNativeInstallOrdinals (messages)
open RegistrationNativeInstallBeaconComplete (present)
variable {n : Nat} {ι KemSK ProviderState Reader Response Secret : Type} {base : OracleSpec ι}
variable {source : RegistrationNativeMldsa.Source}
variable (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
  (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
  (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
  (candidate : PqxdhKemIndCca.MlKemSharedSecret) (provider : RegistrationNativeHiddenInterpreter.Provider KemSK ProviderState)
  (service : QueryImpl (PqxdhRecordLiftProtocol.ServiceSpec n) (StateT Secret ProbComp))
  (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder) (selectedOwner selectedAccept : Nat)

/-- Actual guarded typed Server success has its exact same pre-call Ready descriptor suffix. -/
theorem build_live (role : PqxdhRecordLiftInterface.Role) (handle : Nat) (application : Option (Slice U8))
    (before : State n KemSK ProviderState Secret source) (ready : RegistrationServerReferenceRoot.Ready)
    (stored : before.2.1.1.1.1.server.sessions[handle]? = some (some ready))
    (result : RustM (Option (U64 × Pqxdh.Bytes)) × State n KemSK ProviderState Secret source)
    (supported : result ∈ support ((typed setup checks wire sign seed scalar candidate provider service codec route selectedOwner selectedAccept
      (.inr (.build handle application))).run before)) :
    messages role result.2.1.events = messages role before.1.events ++
      if role = .server ∧ present result.1 = true then [ready.reference] else [] := by
  exact RegistrationNativeInstallServerTyped.build_live setup checks wire sign selectedOwner selectedAccept (setup.dh.publicKey scalar)
    role handle application before.2.1.1.1.1 ready stored before.1 ((result.1, result.2.2.1.1.1.1), result.2.1)
      (RegistrationNativeInstallKernelSupport.open_support setup checks wire sign seed scalar candidate provider service codec route
        selectedOwner selectedAccept (.inr (.build handle application)) before result supported)

/-- The same successful guarded callback's selected descriptor installs its actual returned public peer handle. -/
theorem build_hidden (handle : Nat) (application : Option (Slice U8))
    (before : State n KemSK ProviderState Secret source) (ready : RegistrationServerReferenceRoot.Ready)
    (stored : before.2.1.1.1.1.server.sessions[handle]? = some (some ready))
    (result : RustM (Option (U64 × Pqxdh.Bytes)) × State n KemSK ProviderState Secret source)
    (supported : result ∈ support ((typed setup checks wire sign seed scalar candidate provider service codec route selectedOwner selectedAccept
      (.inr (.build handle application))).run before))
    (keyId : U64) (bytes : Pqxdh.Bytes) (successful : result.1 = .ok (some (keyId, bytes)))
    (selected : ∀ realizedBytes, RegistrationNativeRelatedFamily.input setup.joint setup.dh seed scalar ready.reference = some realizedBytes →
      RegistrationNativeSelectiveHiddenService.selected
        (RegistrationNativeKeyFamilyPreparation.inside (setup.joint.staticDh seed (setup.dh.publicKey scalar))) candidate realizedBytes = true) :
    ∃ slot, PqxdhRecordLiftIdeal.handleSlot result.2.2.1.2 (.peer keyId) = some slot := by
  have erased := Set.mem_image_of_mem (Prod.map id Prod.snd) supported
  rw [← support_map, RegistrationNativeSelectiveInstallKernel.typed_erase] at erased
  rw [RegistrationNativeSelectiveAllocation.typed, RegistrationNativeHiddenEnvironmentWorld.lower_run, support_map] at erased
  obtain ⟨native, actual, returned⟩ := erased
  rw [RegistrationNativeSelectiveEntropyEffects.close_run, RegistrationNativeHiddenEnvironmentWorld.interpret_map, support_map] at actual
  obtain ⟨original, called, sourceEq⟩ := actual
  have reply : original.1.1.1.1.1 = .ok (some (keyId, bytes)) :=
    ((congrArg (fun value => value.1.1.1.1) sourceEq).trans (congrArg Prod.fst returned)).trans successful
  have control : original.1.2 = result.2.2.1.2 :=
    (congrArg (fun value => value.1.2) sourceEq).trans (congrArg (fun value => value.2.1.2) returned)
  have installed := RegistrationNativeSelectiveTypedServerUniversalOrigin.build setup checks wire route sign seed scalar candidate provider service codec
    selectedOwner selectedAccept (setup.dh.publicKey scalar) handle application before.2.1.1.1.1 ready stored before.2.1.1.1.2
      before.2.1.1.2 before.2.1.2 before.2.2 original called keyId bytes reply selected
  rw [control] at installed
  exact installed


/-- Actual missing or consumed sessions return public failure and retain the successful descriptor prefix. -/
theorem build_missing (role : PqxdhRecordLiftInterface.Role) (handle : Nat) (application : Option (Slice U8))
    (before : State n KemSK ProviderState Secret source)
    (missing : ∀ ready, before.2.1.1.1.1.server.sessions[handle]? ≠ some (some ready))
    (result : RustM (Option (U64 × Pqxdh.Bytes)) × State n KemSK ProviderState Secret source)
    (supported : result ∈ support ((typed setup checks wire sign seed scalar candidate provider service codec route selectedOwner selectedAccept
      (.inr (.build handle application))).run before)) :
    messages role result.2.1.events = messages role before.1.events ∧ result.1 = .ok none := by
  have original := RegistrationNativeInstallKernelSupport.open_support setup checks wire sign seed scalar candidate provider service codec route
    selectedOwner selectedAccept (.inr (.build handle application)) before result supported
  rw [RegistrationNativeInstallServerTyped.build_missing_source setup checks wire sign selectedOwner selectedAccept
    (setup.dh.publicKey scalar) handle application before.2.1.1.1.1 missing] at original
  simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at original
  have sameTrace : result.2.1 = before.1 := congrArg Prod.snd original
  exact ⟨congrArg (fun trace => messages role trace.events) sameTrace, congrArg (fun value => value.1.1) original⟩

set_option maxHeartbeats 800000 in
/-- Every actual guarded typed Server callback has an exact role-local suffix and its selected successful returned-handle receipt. -/
theorem build_step (role : PqxdhRecordLiftInterface.Role) (handle : Nat) (application : Option (Slice U8))
    (before : State n KemSK ProviderState Secret source)
    (result : RustM (Option (U64 × Pqxdh.Bytes)) × State n KemSK ProviderState Secret source)
    (supported : result ∈ support ((typed setup checks wire sign seed scalar candidate provider service codec route selectedOwner selectedAccept
      (.inr (.build handle application))).run before)) :
    ∃ added, messages role result.2.1.events = messages role before.1.events ++ added ∧
      added.length = (if role = .server ∧ present result.1 = true then 1 else 0) ∧
      ∀ keyId bytes, result.1 = .ok (some (keyId, bytes)) → ∀ message, message ∈ added →
        (∀ realizedBytes, RegistrationNativeRelatedFamily.input setup.joint setup.dh seed scalar message = some realizedBytes →
          RegistrationNativeSelectiveHiddenService.selected
            (RegistrationNativeKeyFamilyPreparation.inside (setup.joint.staticDh seed (setup.dh.publicKey scalar))) candidate realizedBytes = true) →
        ∃ slot, PqxdhRecordLiftIdeal.handleSlot result.2.2.1.2 (.peer keyId) = some slot := by
  have absent (missing : ∀ ready, before.2.1.1.1.1.server.sessions[handle]? ≠ some (some ready)) :
      ∃ added, messages role result.2.1.events = messages role before.1.events ++ added ∧
        added.length = (if role = .server ∧ present result.1 = true then 1 else 0) ∧
        ∀ keyId bytes, result.1 = .ok (some (keyId, bytes)) → ∀ message, message ∈ added →
          (∀ realizedBytes, RegistrationNativeRelatedFamily.input setup.joint setup.dh seed scalar message = some realizedBytes →
            RegistrationNativeSelectiveHiddenService.selected
              (RegistrationNativeKeyFamilyPreparation.inside (setup.joint.staticDh seed (setup.dh.publicKey scalar))) candidate realizedBytes = true) →
          ∃ slot, PqxdhRecordLiftIdeal.handleSlot result.2.2.1.2 (.peer keyId) = some slot := by
    have quiet := build_missing setup checks wire sign seed scalar candidate provider service codec route selectedOwner selectedAccept
      role handle application before missing result supported
    refine ⟨[], ?_, ?_, ?_⟩
    · simpa only [List.append_nil] using quiet.1
    · rw [quiet.2]; simp [present]
    · intro keyId bytes success
      rw [quiet.2] at success
      cases success
  cases stored : before.2.1.1.1.1.server.sessions[handle]? with
  | none => exact absent (by intro ready impossible; rw [stored] at impossible; cases impossible)
  | some entry => cases entry with
    | none => exact absent (by intro ready impossible; rw [stored] at impossible; cases impossible)
    | some ready =>
        refine ⟨if role = .server ∧ present result.1 = true then [ready.reference] else [], ?_, ?_, ?_⟩
        · exact build_live setup checks wire sign seed scalar candidate provider service codec route selectedOwner selectedAccept
            role handle application before ready stored result supported
        · split <;> rfl
        · intro keyId bytes success message member selected
          split at member
          · simp only [List.mem_singleton] at member
            subst message
            exact build_hidden setup checks wire sign seed scalar candidate provider service codec route selectedOwner selectedAccept
              handle application before ready stored result supported keyId bytes success selected
          · cases member

end BeaconcryptCore.Computational.RegistrationNativeInstallKernelServer

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeInstallKernelServer.build_live' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeInstallKernelServer.build_live
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeInstallKernelServer.build_hidden' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeInstallKernelServer.build_hidden

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeInstallKernelServer.build_missing' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeInstallKernelServer.build_missing
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeInstallKernelServer.build_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeInstallKernelServer.build_step
