-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeInstallRuntimeTrace
import BeaconcryptCore.Computational.RegistrationNativeInstallBeaconComplete
import BeaconcryptCore.Computational.RegistrationNativeSelectiveBeaconCompletionOrigin
import BeaconcryptCore.Computational.RegistrationNativeBeaconFinishController

/-! A selected Ready at an actual complete-runtime Beacon cut installs its own physical hidden origin. The callback source is derived from the literal selective and Cbor interpreters; it is never a caller-owned game equation. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeInstallBeaconRuntime
open PqxdhServerAuthExperiment (Setup Codec)
open RegistrationBeaconReferenceCompiler (SelectedOwner)
open RegistrationWorldAgreementCompiler (EnvState)
open RegistrationNativeInstallRuntime (Runtime publicCallback)
variable {n : Nat} {ι KemSK ProviderState Auxiliary Reader Response Secret : Type} {base : OracleSpec ι}
variable {source : RegistrationNativeMldsa.Source}
variable (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
  (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
  (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
  (candidate : PqxdhKemIndCca.MlKemSharedSecret) (provider : RegistrationNativeHiddenInterpreter.Provider KemSK ProviderState)
  (service : QueryImpl (PqxdhRecordLiftProtocol.ServiceSpec n) (StateT Secret ProbComp))
  (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)

/-- The same selected Ready in the actual terminal completion installs its own physical owner handle. -/
theorem complete (owner current : SelectedOwner source) (ready : RegistrationBeaconReferenceRoot.Ready)
    (env : EnvState Auxiliary) (before : Runtime n KemSK ProviderState Secret)
    (result : (RustM (Option Pqxdh.Bytes) × SelectedOwner source) × (EnvState Auxiliary × Runtime n KemSK ProviderState Secret))
    (supported : result ∈ support
      ((RegistrationNativeBeaconFinishController.lower
        (publicCallback setup wire sign seed scalar candidate provider service codec route ∘ₛ RegistrationNativePublicFrontend.liftLocal false)
        ((RegistrationBeaconReferenceFinish.complete setup.source owner ready).run current)).run (env, before)))
    (bytes : Pqxdh.Bytes) (successful : result.1.1 = .ok (some bytes))
    (selected : ∀ realizedBytes, RegistrationNativeRelatedFamily.input setup.joint setup.dh seed scalar ready.reference = some realizedBytes →
      RegistrationNativeSelectiveHiddenService.selected
        (RegistrationNativeKeyFamilyPreparation.inside (setup.joint.staticDh seed (setup.dh.publicKey scalar))) candidate realizedBytes = true) :
    ∃ slot, PqxdhRecordLiftIdeal.handleSlot result.2.2.1.2 (.owner owner.worldOwner) = some slot := by
  simp only [RegistrationNativeBeaconFinishController.lower, StateT.run, support_map] at supported
  obtain ⟨native, called, returned⟩ := supported
  rw [QueryImpl.simulateQ_compose] at called
  change native ∈ support ((simulateQ
    (fun query => RegistrationNativeHiddenEnvironmentWorld.lower service codec route
      (RegistrationNativeSelectiveHiddenInterpreter.handler setup wire sign seed scalar candidate provider query))
    (simulateQ (RegistrationNativePublicFrontend.liftLocal false)
      (((RegistrationBeaconReferenceFinish.complete setup.source owner ready).run current).run env))).run before) at called
  rw [← RegistrationNativeHiddenEnvironmentWorld.program_lower,
    RegistrationNativeHiddenEnvironmentWorld.lower_run, support_map] at called
  obtain ⟨actual, possible, nativeEq⟩ := called
  have reply : actual.1.1.1.1.1.1 = .ok (some bytes) :=
    ((congrArg (fun value => value.1.1.1) nativeEq).trans (congrArg (fun value => value.1.1) returned)).trans successful
  have control : actual.1.2 = result.2.2.1.2 :=
    (congrArg (fun value => value.2.1.2) nativeEq).trans (congrArg (fun value => value.2.2.1.2) returned)
  have installed := RegistrationNativeSelectiveBeaconCompletionOrigin.complete setup wire route sign seed scalar candidate provider service codec
    owner current ready env before.1.1.1 before.1.1.2 before.1.2 before.2 actual (by
      simpa only [RegistrationNativeSelectiveBeaconCompletionSource.execute,
        RegistrationNativeSelectiveMaterialSource.closedLocal, QueryImpl.simulateQ_compose, StateT.run] using possible)
      bytes reply selected
  rw [control] at installed
  exact installed


/-- The same actual chronological completion retains its selected physical hidden origin after erasing only the observer. -/
theorem complete_traced (owner current : SelectedOwner source) (ready : RegistrationBeaconReferenceRoot.Ready)
    (env : EnvState Auxiliary) (before : RegistrationNativeInstallRuntimeTrace.Runtime n KemSK ProviderState Secret)
    (result : (RustM (Option Pqxdh.Bytes) × SelectedOwner source) ×
      (EnvState Auxiliary × RegistrationNativeInstallRuntimeTrace.Runtime n KemSK ProviderState Secret))
    (supported : result ∈ support
      ((RegistrationNativeBeaconFinishController.lower
        (RegistrationNativeInstallRuntimeTrace.callback setup wire sign seed scalar candidate provider service codec route ∘ₛ
          RegistrationNativePublicFrontend.liftLocal false)
        ((RegistrationBeaconReferenceFinish.complete setup.source owner ready).run current)).run (env, before)))
    (bytes : Pqxdh.Bytes) (successful : result.1.1 = .ok (some bytes))
    (selected : ∀ realizedBytes, RegistrationNativeRelatedFamily.input setup.joint setup.dh seed scalar ready.reference = some realizedBytes →
      RegistrationNativeSelectiveHiddenService.selected
        (RegistrationNativeKeyFamilyPreparation.inside (setup.joint.staticDh seed (setup.dh.publicKey scalar))) candidate realizedBytes = true) :
    ∃ slot, PqxdhRecordLiftIdeal.handleSlot result.2.2.2.1.2 (.owner owner.worldOwner) = some slot := by
  simp only [RegistrationNativeBeaconFinishController.lower, StateT.run, support_map] at supported
  obtain ⟨native, called, returned⟩ := supported
  rw [QueryImpl.simulateQ_compose] at called
  have forgotten := Set.mem_image_of_mem (Prod.map id Prod.snd) called
  have erased := RegistrationNativeInstallRuntimeTrace.forget_source setup wire sign seed scalar candidate provider service codec route
    (simulateQ (RegistrationNativePublicFrontend.liftLocal false)
      (((RegistrationBeaconReferenceFinish.complete setup.source owner ready).run current).run env)) before
  simp only [StateT.run] at erased
  rw [← support_map, erased] at forgotten
  have untraced : (native.1.1, (native.1.2, native.2.2)) ∈ support
      ((RegistrationNativeBeaconFinishController.lower
        (publicCallback setup wire sign seed scalar candidate provider service codec route ∘ₛ RegistrationNativePublicFrontend.liftLocal false)
        ((RegistrationBeaconReferenceFinish.complete setup.source owner ready).run current)).run (env, before.2)) := by
    simp only [RegistrationNativeBeaconFinishController.lower, StateT.run, support_map]
    refine ⟨(native.1, native.2.2), ?_, rfl⟩
    simpa only [QueryImpl.simulateQ_compose, StateT.run, Prod.map_def, id_eq] using forgotten
  have reply : native.1.1.1 = .ok (some bytes) := (congrArg (fun value => value.1.1) returned).trans successful
  have control : native.2.2.1.2 = result.2.2.2.1.2 := congrArg (fun value => value.2.2.2.1.2) returned
  have installed := complete setup wire sign seed scalar candidate provider service codec route owner current ready env before.2
    (native.1.1, (native.1.2, native.2.2)) untraced bytes reply selected
  rw [control] at installed
  exact installed


/-- The same complete chronological runtime records its actual Ready descriptor exactly once on public success. -/
theorem complete_count (role : PqxdhRecordLiftInterface.Role)
    (owner current : SelectedOwner source) (ready : RegistrationBeaconReferenceRoot.Ready)
    (env : EnvState Auxiliary) (before : RegistrationNativeInstallRuntimeTrace.Runtime n KemSK ProviderState Secret)
    (result : (RustM (Option Pqxdh.Bytes) × SelectedOwner source) ×
      (EnvState Auxiliary × RegistrationNativeInstallRuntimeTrace.Runtime n KemSK ProviderState Secret))
    (supported : result ∈ support
      ((RegistrationNativeBeaconFinishController.lower
        (RegistrationNativeInstallRuntimeTrace.callback setup wire sign seed scalar candidate provider service codec route ∘ₛ
          RegistrationNativePublicFrontend.liftLocal false)
        ((RegistrationBeaconReferenceFinish.complete setup.source owner ready).run current)).run (env, before))) :
    RegistrationNativeInstallOrdinals.messages role result.2.2.1.events =
      RegistrationNativeInstallOrdinals.messages role before.1.events ++
        if role = .beacon ∧ RegistrationNativeInstallBeaconComplete.present result.1.1 = true then [ready.reference] else [] := by
  simp only [RegistrationNativeBeaconFinishController.lower, StateT.run, support_map] at supported
  obtain ⟨native, called, returned⟩ := supported
  rw [QueryImpl.simulateQ_compose] at called
  have original := RegistrationNativeInstallRuntimeTrace.open_support setup wire sign seed scalar candidate provider service codec route
    _ before native called
  have bill := RegistrationNativeInstallBeaconComplete.complete role setup.source owner current ready env before.1
    (native.1, native.2.1) (by simpa only [RegistrationNativeInstallBeaconComplete.compile, StateT.run] using original)
  cases returned
  exact bill

end BeaconcryptCore.Computational.RegistrationNativeInstallBeaconRuntime

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeInstallBeaconRuntime.complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeInstallBeaconRuntime.complete

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeInstallBeaconRuntime.complete_traced' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeInstallBeaconRuntime.complete_traced

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeInstallBeaconRuntime.complete_count' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeInstallBeaconRuntime.complete_count
