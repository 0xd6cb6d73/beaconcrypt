-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.AdapterPublicFinishLifetime
import BeaconcryptCore.Computational.RegistrationNativeLocalStatePatch
/-! Every source state other than InitSent returns the unchanged complete SDK Beacon before decoding or primitive calls. Its existing private-material relation derives this source condition from the selected native owner phase. The actual corrected native finish likewise returns None with the entire Native state unchanged. This closes inactive calls alongside the separate complete active finish lifecycle. -/
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Refinement.AdapterPublicFinishInactive
open BeaconcryptCore.Computational
open RegistrationNativeBeaconFrontend (Owner)
variable {n : Nat} {I KemSK : Type} {base : OracleSpec I} {source : RegistrationNativeMldsa.Source}

def Inactive (owner : Owner source) : Prop :=
  ∀ pending scalar, owner.phase ≠ .initSent pending scalar

theorem native (setup : PqxdhServerAuthExperiment.Setup base KemSK) (checks : PqxdhServerAuthExperiment.Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (wire : RegistrationNativeWire.Wire) (index : Nat) (owner : Owner source)
    (packet : Option registration.ResponsePacket) (before : RegistrationNativeExperiment.State n KemSK source)
    (selected : before.beacons[index]? = some owner) (inactive : Inactive owner) :
    (RegistrationNativeExperiment.beacon setup checks representation created
      (RegistrationNativePlatformBeaconFinish.finish setup source wire index packet)).run before = pure (.ok none, before) := by
  rw [RegistrationNativeLocalStatePatch.beacon_run]
  simp only [RegistrationNativePlatformBeaconFinish.finish, RegistrationNativePlatformBeaconFinish.finishWith,
    StateT.run_bind, StateT.run_get, pure_bind, selected]
  cases phase : owner.phase with
  | initSent pending scalar => exact False.elim (inactive pending scalar phase)
  | _ => simp only [StateT.run_pure, simulateQ_pure, map_pure, RegistrationNativeLocalStatePatch.assemble_self]

variable [material : PublicWrapperPlatform.Material] [platform : PublicWrapperPlatform.Platform]
variable [ed : AdapterInitEdPrimitive.Operations]
variable [PublicWrapperPlatform.CryptoOperations]

def SourceInactive (self : beaconcrypt_public_wrapper.beacon.Beacon) : Prop :=
  ∀ pending prekey oneTime kem, self.state ≠ .InitSent pending prekey oneTime kem

omit platform [PublicWrapperPlatform.CryptoOperations] in
theorem source_phase (view : AdapterPublicWrapperState.MaterialView source KemSK)
    (joint : PqxdhJointIdentity.Primitives) (pool : PqxdhLiveKemBirth.Pool KemSK)
    (self : beaconcrypt_public_wrapper.beacon.Beacon) (owner : Owner source)
    (world : Option PqxdhRecordLiftBeacon.Phase) (related : AdapterPublicWrapperState.Beacon view joint pool self owner world)
    (inactive : Inactive owner) : SourceInactive self := by
  intro pending prekey oneTime kem stored
  have data := related.phase
  cases phase : owner.phase with
  | initSent retained scalar => exact inactive retained scalar phase
  | _ => simp only [AdapterPublicWrapperState.Phase, stored, phase] at data

variable {m : Type → Type} [Monad m] [LawfulMonad m]
variable [localOps : AdapterPublicWrapperRequestMonad.LocalOperations (AdapterPublicWrapperRustT.RustT m)]
variable [crypto : AdapterPublicWrapperRequestMonad.CryptoOperations (AdapterPublicWrapperRustT.RustT m)]
variable [codec : AdapterPublicWrapperRequestMonad.Codecs (AdapterPublicWrapperRustT.RustT m)]
variable [children : AdapterPublicWrapperRequestMonad.ChildOperations (AdapterPublicWrapperRustT.RustT m)]

theorem source_inactive (self : beaconcrypt_public_wrapper.beacon.Beacon) (input : Slice U8) (inactive : SourceInactive self) :
    (beaconcrypt_public_request.beacon.Beacon.Insts.BeaconcryptBeaconProviderBeacon.finish_registration
      (m := AdapterPublicWrapperRustT.RustT m) self input).run = pure (.ok (.None, self)) := by
  rw [AdapterPublicFinishBody.source]
  cases state : self.state with
  | InitSent pending prekey oneTime kem => exact False.elim (inactive pending prekey oneTime kem state)
  | _ => simp only [AdapterPublicFinishBody.program, state, AdapterPublicWrapperRustT.RustT.run_pure]


theorem same (setup : PqxdhServerAuthExperiment.Setup base KemSK) (checks : PqxdhServerAuthExperiment.Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (wire : RegistrationNativeWire.Wire) (index : Nat) (owner : Owner source)
    (view : AdapterPublicWrapperState.MaterialView source KemSK) (self : beaconcrypt_public_wrapper.beacon.Beacon)
    (input : Slice U8) (before : RegistrationNativeExperiment.State n KemSK source)
    (related : AdapterPublicWrapperState.Beacon view setup.joint before.pool self owner before.server.world.world.1.owners[owner.worldOwner]?)
    (selected : before.beacons[index]? = some owner) (inactive : Inactive owner) :
    ((beaconcrypt_public_request.beacon.Beacon.Insts.BeaconcryptBeaconProviderBeacon.finish_registration
      (m := AdapterPublicWrapperRustT.RustT m) self input).run = pure (.ok (.None, self))) ∧
    ((RegistrationNativeExperiment.beacon setup checks representation created
      (RegistrationNativePlatformBeaconFinish.finish setup source wire index (AdapterPublicFinishLifetime.packet input))).run before = pure (.ok none, before)) := by
  exact ⟨source_inactive self input (source_phase view setup.joint before.pool self owner _ related inactive),
    native setup checks representation created wire index owner _ before selected inactive⟩

end BeaconcryptCore.Refinement.AdapterPublicFinishInactive

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicFinishInactive.native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicFinishInactive.native

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicFinishInactive.source_phase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicFinishInactive.source_phase

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicFinishInactive.source_inactive' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicFinishInactive.source_inactive

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicFinishInactive.same' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicFinishInactive.same
