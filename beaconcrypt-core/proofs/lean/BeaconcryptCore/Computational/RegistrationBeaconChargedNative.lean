-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationBeaconChargedSource
import BeaconcryptCore.Computational.RegistrationBeaconReferenceNativeRecord
import BeaconcryptCore.Computational.RegistrationNativePlatformPairedBeaconOwner
import BeaconcryptCore.Computational.RegistrationNativePlatformBeaconSettle
/-! The charged source interface is derived from each actual native record callback. Every local environment field, World effect and owner is retained. Only KDF operands are replaced inside their primitive functional interface; actual kind markers are preserved. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete PqxdhRefinement
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationBeaconChargedNative
open RegistrationNativeBeaconFrontend (M Owner Trusted)
open RegistrationWorldAgreement (RecordCall)
variable {n : Nat} {ι KemSK Auxiliary Value : Type} {base : OracleSpec ι} {source : RegistrationNativeMldsa.Source}

def charge (kind : RecordCall) : M n KemSK source Auxiliary Unit :=
  RegistrationNativeBeaconFrontend.updateEnv fun env => {env with recordRequests := env.recordRequests ++ [kind]}

def lift (work : OracleComp (PqxdhRecordLiftInterface.EnvEffects n) Value) : M n KemSK source Auxiliary Value :=
  StateT.lift (StateT.lift (simulateQ RegistrationBeaconReferenceNativeRecord.environment work))

def kind : RegistrationRawReceiveBridge.Spec.Domain → RecordCall
  | .inl request => RegistrationWorldAgreement.recordCall request
  | .inr (.inl _) => .ratchetKdf
  | .inr (.inr (.inl _)) => .hash
  | .inr (.inr (.inr _)) => .openAead

noncomputable def read (setup : PqxdhServerAuthExperiment.Setup base KemSK) (wire : RegistrationNativeWire.Wire) :
    QueryImpl RegistrationRawReceiveBridge.Spec (M n KemSK source Auxiliary) := fun query => do
  let _ ← charge (kind query)
  lift (RegistrationBeaconRecordSourceProgram.read setup.source wire.frameWrite query)

theorem record (setup : PqxdhServerAuthExperiment.Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (query : RegistrationRecordPrimitives.Request) :
    RegistrationNativeBeaconFrontend.record (n := n) (mldsaSource := source) (Auxiliary := Auxiliary) setup wire query =
      simulateQ (read setup wire) (RegistrationRawReceiveBridge.nativeAdapter query) := by
  apply StateT.ext
  intro owners
  apply StateT.ext
  intro env
  cases query <;> first | rfl | (rename_i writing; cases writing <;> rfl)

theorem initial (setup : PqxdhServerAuthExperiment.Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (request : ratchet.SymmetricRatchetKdfRequest) :
    read (n := n) (source := source) (Auxiliary := Auxiliary) setup wire (.inl (.initialKdf request)) =
      charge .initialKdf *> pure (.Some (RawCtxSourceHkdf.initialResponse setup.source.crypto request)) := by
  simp only [read, kind, RegistrationWorldAgreement.recordCall, RegistrationBeaconRecordSourceProgram.initial_source]
  rfl

theorem ratchet (setup : PqxdhServerAuthExperiment.Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (request : ratchet.SymmetricRatchetKdfRequest) :
    RegistrationBeaconChargedSource.primitive (read (n := n) (source := source) (Auxiliary := Auxiliary) setup wire) (.inl request) =
      charge .ratchetKdf *> pure (RawCtxSourceHkdf.response setup.source.crypto request) := by
  rfl

theorem controller (setup : PqxdhServerAuthExperiment.Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (erased : Std.Array U8 357#usize) (descriptor : RegistrationBeaconBoundSource.PublicAgreement)
    (root : PqxdhSecretInputKdf.RootOutput) :
    simulateQ (RegistrationNativeBeaconFrontend.record (n := n) (mldsaSource := source) (Auxiliary := Auxiliary) setup wire)
      (RegistrationBeaconRecordExecutor.begin (RegistrationBeaconBoundSource.atRoot descriptor root)) = (do
        let _ ← charge .initialKdf
        let _ ← if RawCtxReceive.ValidFrame descriptor.candidate.server_binding.identity_key_id
          (absBytes descriptor.binding.associated_data) (RegistrationBeaconBoundSource.frame descriptor) then charge .ratchetKdf else pure ()
        simulateQ (RegistrationBeaconChargedSource.primitive (read setup wire))
          (RegistrationBeaconSeed.program setup.source descriptor (PqxdhServerAuthKeySchedule.fromRoot setup.source root))) := by
  have actual : RegistrationNativeBeaconFrontend.record (n := n) (mldsaSource := source) (Auxiliary := Auxiliary) setup wire =
      read setup wire ∘ₛ RegistrationRawReceiveBridge.nativeAdapter := by
    funext query
    exact record setup wire query
  rw [actual, QueryImpl.simulateQ_compose, RegistrationBeaconPostRootServices.beacon_exact erased]
  exact RegistrationBeaconChargedSource.source_factor (read setup wire) setup.source
    (charge .initialKdf) (charge .ratchetKdf) (initial setup wire) (ratchet setup wire) erased descriptor root

noncomputable def postRoot (setup : PqxdhServerAuthExperiment.Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (index : Nat) (owner : Owner source) (agreed : agreement.BeaconAgreement) : M n KemSK source Auxiliary (RustM (Option Pqxdh.Bytes)) := do
  let opened ← simulateQ (RegistrationNativeBeaconFrontend.record setup wire) (RegistrationBeaconRecordExecutor.begin agreed)
  RegistrationNativePlatformBeaconSettle.native index owner opened

theorem post_root (setup : PqxdhServerAuthExperiment.Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (erased : Std.Array U8 357#usize) (index : Nat) (owner : Owner source)
    (descriptor : RegistrationBeaconBoundSource.PublicAgreement) (root : PqxdhSecretInputKdf.RootOutput) :
    postRoot (n := n) (Auxiliary := Auxiliary) setup wire index owner (RegistrationBeaconBoundSource.atRoot descriptor root) = (do
      let _ ← charge .initialKdf
      let _ ← if RawCtxReceive.ValidFrame descriptor.candidate.server_binding.identity_key_id
        (absBytes descriptor.binding.associated_data) (RegistrationBeaconBoundSource.frame descriptor) then charge .ratchetKdf else pure ()
      let result ← RegistrationNativePlatformPairedBeaconOwner.knownStage setup.source
        (RegistrationBeaconChargedSource.primitive (read setup wire)) RegistrationNativeBeaconFrontend.effect owner.worldOwner descriptor
          (PqxdhServerAuthKeySchedule.fromRoot setup.source root)
      RegistrationNativePlatformBeaconSettle.settle index owner result) := by
  unfold postRoot RegistrationNativePlatformPairedBeaconOwner.knownStage
  rw [controller setup wire erased descriptor root]
  simp only [bind_assoc]
  apply bind_congr
  intro initialCharge
  by_cases valid : RawCtxReceive.ValidFrame descriptor.candidate.server_binding.identity_key_id
    (absBytes descriptor.binding.associated_data) (RegistrationBeaconBoundSource.frame descriptor)
  · simp only [valid, ite_true, bind_assoc]
    apply bind_congr
    intro ratchetCharge
    exact bind_congr (fun opened => RegistrationNativePlatformBeaconSettle.installed index owner opened)
  · simp only [valid, ite_false]
    exact bind_congr (fun opened => RegistrationNativePlatformBeaconSettle.installed index owner opened)

/-- info: 'BeaconcryptCore.Computational.RegistrationBeaconChargedNative.record' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationBeaconChargedNative.record

/-- info: 'BeaconcryptCore.Computational.RegistrationBeaconChargedNative.initial' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationBeaconChargedNative.initial

/-- info: 'BeaconcryptCore.Computational.RegistrationBeaconChargedNative.ratchet' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationBeaconChargedNative.ratchet

/-- info: 'BeaconcryptCore.Computational.RegistrationBeaconChargedNative.controller' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationBeaconChargedNative.controller

/-- info: 'BeaconcryptCore.Computational.RegistrationBeaconChargedNative.post_root' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationBeaconChargedNative.post_root

end BeaconcryptCore.Computational.RegistrationBeaconChargedNative
