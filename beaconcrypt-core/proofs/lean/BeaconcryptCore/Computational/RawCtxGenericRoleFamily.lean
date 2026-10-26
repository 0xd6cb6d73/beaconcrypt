import BeaconcryptCore.Computational.RawCtxGenericRoleStorage

/-!
The entire finite Server/Beacon family changes only its installed kernel representation. Every Server peer entry, Beacon phase, identity, metadata and attempted-receive field remains at its original index. Native reconstruction and composition act on all kernels, including correlated paired owners. Original live-read owner lookup commutes with both native reconstruction and generic kernel maps, preserving missing-peer and inactive-phase rejection.

These are complete representation laws. The consuming generic frontends must prove actual source dispatch and publication and the cryptographic interpreters must supply their source call equations. No key independence, secret-input distribution, target freshness, allocation or registration behavior, security advantage or runtime bound is assumed or concluded.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RawCtxGenericRoleFamily
open RawCtxGenericRoleStorage RawCtxProtocolReveals

abbrev Roles (Kernel Metadata PeerMetadata Identity DhPair KemPair : Type) (serverCount beaconCount : Nat) :=
  (Fin serverCount → ServerState Kernel Metadata PeerMetadata) ×
    (Fin beaconCount → BeaconState Kernel Identity DhPair KemPair)

def mapRoles {Kernel Other Metadata PeerMetadata Identity DhPair KemPair : Type} {serverCount beaconCount : Nat}
    (interpret : Kernel → Other) (roles : Roles Kernel Metadata PeerMetadata Identity DhPair KemPair serverCount beaconCount) :
    Roles Other Metadata PeerMetadata Identity DhPair KemPair serverCount beaconCount :=
  (fun index => mapServer interpret (roles.1 index), fun index => mapBeacon interpret (roles.2 index))

def nativeRoles {Kernel Metadata PeerMetadata Identity DhPair KemPair : Type} {serverCount beaconCount : Nat}
    (interpret : Kernel → ConcreteRatchetKernel)
    (roles : Roles Kernel Metadata PeerMetadata Identity DhPair KemPair serverCount beaconCount) :
    RawCtxProtocolReveals.Roles Metadata PeerMetadata Identity DhPair KemPair serverCount beaconCount :=
  (fun index => nativeServer interpret (roles.1 index), fun index => nativeBeacon interpret (roles.2 index))

def fromRoles {Kernel Metadata PeerMetadata Identity DhPair KemPair : Type} {serverCount beaconCount : Nat}
    (represent : ConcreteRatchetKernel → Kernel)
    (roles : RawCtxProtocolReveals.Roles Metadata PeerMetadata Identity DhPair KemPair serverCount beaconCount) :
    Roles Kernel Metadata PeerMetadata Identity DhPair KemPair serverCount beaconCount :=
  (fun index => fromServer represent (roles.1 index), fun index => fromBeacon represent (roles.2 index))

def selectedKernel {Kernel Metadata PeerMetadata Identity DhPair KemPair : Type} {serverCount beaconCount : Nat}
    (owner : Owner serverCount beaconCount)
    (roles : Roles Kernel Metadata PeerMetadata Identity DhPair KemPair serverCount beaconCount) : Option Kernel :=
  match owner with
  | .server index peer => (roles.1 index).server.peers peer |>.map Peer.kernel
  | .beacon index => match (roles.2 index).beacon.phase with
      | .established _ _ kernel => some kernel
      | _ => none

/-- The full finite family reconstructs every original native role and peer at the same index. -/
theorem roundtrip {Kernel Metadata PeerMetadata Identity DhPair KemPair : Type} {serverCount beaconCount : Nat}
    (represent : ConcreteRatchetKernel → Kernel) (interpret : Kernel → ConcreteRatchetKernel)
    (inverse : ∀ kernel, interpret (represent kernel) = kernel)
    (roles : RawCtxProtocolReveals.Roles Metadata PeerMetadata Identity DhPair KemPair serverCount beaconCount) :
    nativeRoles interpret (fromRoles represent roles) = roles := by
  simp [nativeRoles, fromRoles, server_roundtrip represent interpret inverse,
    beacon_roundtrip represent interpret inverse]

/-- Representation composition acts on every installed kernel without changing any role field. -/
theorem compose {Kernel Other Metadata PeerMetadata Identity DhPair KemPair : Type} {serverCount beaconCount : Nat}
    (represent : Kernel → Other) (interpret : Other → ConcreteRatchetKernel)
    (roles : Roles Kernel Metadata PeerMetadata Identity DhPair KemPair serverCount beaconCount) :
    nativeRoles interpret (mapRoles represent roles) = nativeRoles (interpret ∘ represent) roles := by
  simp [nativeRoles, mapRoles, server_compose, beacon_compose]

/-- An actual native reveal selects the same original owner and kernel after the whole-family representation map. -/
theorem native_selected {Kernel Metadata PeerMetadata Identity DhPair KemPair : Type} {serverCount beaconCount : Nat}
    (interpret : Kernel → ConcreteRatchetKernel) (owner : Owner serverCount beaconCount)
    (roles : Roles Kernel Metadata PeerMetadata Identity DhPair KemPair serverCount beaconCount) :
    RawCtxProtocolReveals.selectedKernel owner (nativeRoles interpret roles) =
      (selectedKernel owner roles).map interpret := by
  cases owner with
  | server index peer => simp [RawCtxProtocolReveals.selectedKernel, nativeRoles, nativeServer,
      selectedKernel, Option.map_map, Function.comp_def]
  | beacon index =>
      cases phase : (roles.2 index).beacon.phase <;>
        simp [RawCtxProtocolReveals.selectedKernel, nativeRoles, nativeBeacon, mapPhase, selectedKernel, phase]

/-- Whole-family kernel conversion preserves every accepted or rejected owner lookup. -/
theorem map_selected {Kernel Other Metadata PeerMetadata Identity DhPair KemPair : Type} {serverCount beaconCount : Nat}
    (interpret : Kernel → Other) (owner : Owner serverCount beaconCount)
    (roles : Roles Kernel Metadata PeerMetadata Identity DhPair KemPair serverCount beaconCount) :
    selectedKernel owner (mapRoles interpret roles) = (selectedKernel owner roles).map interpret := by
  cases owner with
  | server index peer => simp [mapRoles, mapServer, mapPeer, selectedKernel, Option.map_map, Function.comp_def]
  | beacon index =>
      cases phase : (roles.2 index).beacon.phase <;>
        simp [mapRoles, mapBeacon, mapPhase, selectedKernel, phase]

end BeaconcryptCore.Computational.RawCtxGenericRoleFamily

/-- info: 'BeaconcryptCore.Computational.RawCtxGenericRoleFamily.roundtrip' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxGenericRoleFamily.roundtrip

/-- info: 'BeaconcryptCore.Computational.RawCtxGenericRoleFamily.compose' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxGenericRoleFamily.compose

/-- info: 'BeaconcryptCore.Computational.RawCtxGenericRoleFamily.native_selected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxGenericRoleFamily.native_selected

/-- info: 'BeaconcryptCore.Computational.RawCtxGenericRoleFamily.map_selected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxGenericRoleFamily.map_selected
