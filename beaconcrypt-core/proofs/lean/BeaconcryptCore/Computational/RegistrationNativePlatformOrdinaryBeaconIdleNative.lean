-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryExperiment
/-! Missing Beacon handles and inactive ordinary-record dispatch retain the exact full native/platform state. Inactive raw calls retain their one actual owner-attempt charge. -/
open OracleComp OracleSpec CoreModels Aeneas beaconcrypt_core
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryBeaconIdleNative
open RegistrationNativePlatformOrdinaryExperiment (record replaceWorld)
variable {n : Nat} {I KemSK Platform E : Type} {base : OracleSpec I} {source : RegistrationNativeMldsa.Source}
variable (setup : PqxdhServerAuthExperiment.Setup base KemSK) (wire : RegistrationNativeWire.Wire)
variable (reserve : Nat →StateT Platform ProbComp (core.result.Result Unit E))
variable (route : RawCtxServerRouting.SenderDecoder)
variable (before : RegistrationNativeExperiment.State n KemSK source) (logical : Nat)

private theorem pure_apply {S A : Type} {m : Type →Type} [Monad m] (value : A) (state : S) :
    (pure value : StateT S m A) state=pure (value,state) := rfl

private theorem set_same {A : Type} (values : List A) (index : Nat) (value : A)
    (present : values[index]?=some value) : values.set index value=values := by
  obtain ⟨below,equal⟩:=List.getElem?_eq_some_iff.mp present
  rw [←equal]
  exact List.set_getElem_self below

theorem missing_send (bytes : Pqxdh.Bytes) (missing : before.beacons[logical]?=none) :
    (record setup wire reserve route (.inr (logical,.inl bytes)) source).run before=pure (none,before) := by
  simp only [record,StateT.run,missing]

theorem missing_receive (bytes : Pqxdh.Bytes) (missing : before.beacons[logical]?=none) :
    (record setup wire reserve route (.inr (logical,.inr bytes)) source).run before=pure (.None,before) := by
  simp only [record,StateT.run,missing]

theorem inactive_send (bytes : Pqxdh.Bytes) (owner : RegistrationNativeBeaconFrontend.Owner source)
    (selected : before.beacons[logical]?=some owner) (tag : PqxdhRecordLiftInterface.InactivePhase)
    (inactive : before.server.world.world.1.owners[owner.worldOwner]?=some (.inactive tag)) :
    (record setup wire reserve route (.inr (logical,.inl bytes)) source).run before=pure (none,before) := by
  simp only [record,selected,RegistrationNativePlatformOrdinaryExperiment.world,
    RegistrationNativePlatformOrdinaryWorld.guarded,CborRecordWorldClient.refusal,CborRecordWorldCursor.worldShell,
    inactive,Option.bind_some,RegistrationNativePlatformOrdinaryWorld.handler,
    RegistrationNativePlatformOrdinaryWorld.beaconStep,PqxdhRecordLiftBeacon.handler,
    StateT.run,PqxdhRecordLiftBeacon.rejected,PqxdhDeploymentNative.logged,pure_apply,simulateQ_pure,
    pure_bind,map_pure,PqxdhRecordLiftWorld.produce,List.map_nil,List.append_nil]
  congr 1
  rw [set_same _ _ _ inactive,Function.update_eq_self]
  rfl

theorem inactive_receive (bytes : Pqxdh.Bytes) (owner : RegistrationNativeBeaconFrontend.Owner source)
    (selected : before.beacons[logical]?=some owner) (tag : PqxdhRecordLiftInterface.InactivePhase)
    (inactive : before.server.world.world.1.owners[owner.worldOwner]?=some (.inactive tag)) :
    (record setup wire reserve route (.inr (logical,.inr bytes)) source).run before=
      pure (.None,replaceWorld before {before.server.world.world.1 with
        ownerRaw:=Function.update before.server.world.world.1.ownerRaw owner.worldOwner
          (before.server.world.world.1.ownerRaw owner.worldOwner+1)}) := by
  simp only [record,selected,RegistrationNativePlatformOrdinaryExperiment.world,
    RegistrationNativePlatformOrdinaryWorld.guarded,CborRecordWorldClient.refusal,
    RegistrationNativePlatformOrdinaryWorld.handler,RegistrationNativePlatformOrdinaryWorld.beaconStep,inactive,
    PqxdhRecordLiftBeacon.handler,StateT.run,PqxdhRecordLiftBeacon.rejected,PqxdhDeploymentNative.logged,pure_apply,simulateQ_pure,
    pure_bind,map_pure,PqxdhRecordLiftWorld.produce,List.map_nil,List.append_nil]
  congr 1
  rw [set_same _ _ _ inactive]

end BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryBeaconIdleNative
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryBeaconIdleNative.missing_send' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryBeaconIdleNative.missing_send
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryBeaconIdleNative.missing_receive' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryBeaconIdleNative.missing_receive
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryBeaconIdleNative.inactive_send' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryBeaconIdleNative.inactive_send
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryBeaconIdleNative.inactive_receive' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryBeaconIdleNative.inactive_receive
