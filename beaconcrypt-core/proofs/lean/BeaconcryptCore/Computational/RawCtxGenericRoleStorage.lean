import BeaconcryptCore.Computational.RawCtxProtocolReveals
import BeaconcryptCore.Computational.RawCtxGenericOwnerMap

/-!
The finite role family retains every original Server peer and Beacon phase field while changing only the representation of installed ratchet kernels. Inactive Beacon variants retain all original identity and prekey material. The generic storage has the same original routing identifiers, associated-data inputs, metadata and attempted-receive counters. Native projection is a representation map, not a freshness or cryptographic assumption; the consuming source frontends must prove their complete operational correspondence.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RawCtxGenericRoleStorage

structure Peer (Kernel PeerMetadata : Type) where
  identity : RawCtxServerRouting.Identity
  kernel : Kernel
  metadata : PeerMetadata

structure Server (Kernel Metadata PeerMetadata : Type) where
  identity : RawCtxServerRouting.Identity
  peers : Std.U64 → Option (Peer Kernel PeerMetadata)
  metadata : Metadata

structure ServerState (Kernel Metadata PeerMetadata : Type) where
  server : Server Kernel Metadata PeerMetadata
  rawAttempts : Nat

structure Beacon (Kernel Identity DhPair KemPair : Type) where
  identity : Identity
  identityKeyId : Std.U64
  serverIdentity : Array Std.U8 32#usize
  phase : RawCtxBeaconLifecycle.Phase DhPair KemPair Kernel

structure BeaconState (Kernel Identity DhPair KemPair : Type) where
  beacon : Beacon Kernel Identity DhPair KemPair
  rawAttempts : Nat

def mapPeer {Kernel Other PeerMetadata : Type} (interpret : Kernel → Other)
    (peer : Peer Kernel PeerMetadata) : Peer Other PeerMetadata :=
  ⟨peer.identity, interpret peer.kernel, peer.metadata⟩

def mapServer {Kernel Other Metadata PeerMetadata : Type} (interpret : Kernel → Other)
    (state : ServerState Kernel Metadata PeerMetadata) : ServerState Other Metadata PeerMetadata :=
  ⟨⟨state.server.identity, fun kid => (state.server.peers kid).map (mapPeer interpret), state.server.metadata⟩,
    state.rawAttempts⟩

def mapPhase {Kernel Other DhPair KemPair : Type} (interpret : Kernel → Other) :
    RawCtxBeaconLifecycle.Phase DhPair KemPair Kernel → RawCtxBeaconLifecycle.Phase DhPair KemPair Other
  | .fresh control prekey kem => .fresh control prekey kem
  | .freshWithCoins control prekey oneTime kem => .freshWithCoins control prekey oneTime kem
  | .initSent control prekey oneTime kem => .initSent control prekey oneTime kem
  | .established control associatedData kernel => .established control associatedData (interpret kernel)
  | .aborted control => .aborted control

def mapBeacon {Kernel Other Identity DhPair KemPair : Type} (interpret : Kernel → Other)
    (state : BeaconState Kernel Identity DhPair KemPair) : BeaconState Other Identity DhPair KemPair :=
  ⟨⟨state.beacon.identity, state.beacon.identityKeyId, state.beacon.serverIdentity,
    mapPhase interpret state.beacon.phase⟩, state.rawAttempts⟩

def nativeServer {Kernel Metadata PeerMetadata : Type} (interpret : Kernel → ConcreteRatchetKernel)
    (state : ServerState Kernel Metadata PeerMetadata) : RawCtxServerRouting.State Metadata PeerMetadata :=
  ⟨⟨state.server.identity, fun kid => (state.server.peers kid).map
    (fun peer => ⟨peer.identity, interpret peer.kernel, peer.metadata⟩), state.server.metadata⟩, state.rawAttempts⟩

def nativeBeacon {Kernel Identity DhPair KemPair : Type} (interpret : Kernel → ConcreteRatchetKernel)
    (state : BeaconState Kernel Identity DhPair KemPair) : RawCtxBeaconLifecycle.State Identity DhPair KemPair :=
  ⟨⟨state.beacon.identity, state.beacon.identityKeyId, state.beacon.serverIdentity,
    mapPhase interpret state.beacon.phase⟩, state.rawAttempts⟩

def fromServer {Kernel Metadata PeerMetadata : Type} (represent : ConcreteRatchetKernel → Kernel)
    (state : RawCtxServerRouting.State Metadata PeerMetadata) : ServerState Kernel Metadata PeerMetadata :=
  ⟨⟨state.server.identity, fun kid => (state.server.peers kid).map
    (fun peer => ⟨peer.identity, represent peer.kernel, peer.metadata⟩), state.server.metadata⟩, state.rawAttempts⟩

def fromBeacon {Kernel Identity DhPair KemPair : Type} (represent : ConcreteRatchetKernel → Kernel)
    (state : RawCtxBeaconLifecycle.State Identity DhPair KemPair) : BeaconState Kernel Identity DhPair KemPair :=
  ⟨⟨state.beacon.identity, state.beacon.identityKeyId, state.beacon.serverIdentity,
    mapPhase represent state.beacon.phase⟩, state.rawAttempts⟩

/-- Two private representation changes preserve every inactive phase field and compose on the established kernel alone. -/
theorem phase_compose {Kernel Middle Other DhPair KemPair : Type}
    (first : Kernel → Middle) (second : Middle → Other)
    (phase : RawCtxBeaconLifecycle.Phase DhPair KemPair Kernel) :
    mapPhase second (mapPhase first phase) = mapPhase (second ∘ first) phase := by
  cases phase <;> rfl

/-- The entire native Server peer map retains the same fields through successive kernel interpretations. -/
theorem server_compose {Kernel Other Metadata PeerMetadata : Type}
    (represent : Kernel → Other) (interpret : Other → ConcreteRatchetKernel)
    (state : ServerState Kernel Metadata PeerMetadata) :
    nativeServer interpret (mapServer represent state) = nativeServer (interpret ∘ represent) state := by
  simp [nativeServer, mapServer, mapPeer, Option.map_map, Function.comp_def]

/-- Beacon projection composes on its installed kernel and preserves every other phase and outer identity field. -/
theorem beacon_compose {Kernel Other Identity DhPair KemPair : Type}
    (represent : Kernel → Other) (interpret : Other → ConcreteRatchetKernel)
    (state : BeaconState Kernel Identity DhPair KemPair) :
    nativeBeacon interpret (mapBeacon represent state) = nativeBeacon (interpret ∘ represent) state := by
  simp [nativeBeacon, mapBeacon, phase_compose]

/-- A kernel representation that reconstructs each input preserves the entire original Server state, including every peer. -/
theorem server_roundtrip {Kernel Metadata PeerMetadata : Type}
    (represent : ConcreteRatchetKernel → Kernel) (interpret : Kernel → ConcreteRatchetKernel)
    (inverse : ∀ kernel, interpret (represent kernel) = kernel)
    (state : RawCtxServerRouting.State Metadata PeerMetadata) :
    nativeServer interpret (fromServer represent state) = state := by
  simp [nativeServer, fromServer, Option.map_map, Function.comp_def, inverse]

/-- Reconstructing kernels preserves every original Beacon phase, identity field and attempted-receive count. -/
theorem beacon_roundtrip {Kernel Identity DhPair KemPair : Type}
    (represent : ConcreteRatchetKernel → Kernel) (interpret : Kernel → ConcreteRatchetKernel)
    (inverse : ∀ kernel, interpret (represent kernel) = kernel)
    (state : RawCtxBeaconLifecycle.State Identity DhPair KemPair) :
    nativeBeacon interpret (fromBeacon represent state) = state := by
  cases phase : state.beacon.phase <;>
    simp [nativeBeacon, fromBeacon, mapPhase, phase, inverse]
  all_goals rw [← phase]

end BeaconcryptCore.Computational.RawCtxGenericRoleStorage

/-- info: 'BeaconcryptCore.Computational.RawCtxGenericRoleStorage.phase_compose' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxGenericRoleStorage.phase_compose
/-- info: 'BeaconcryptCore.Computational.RawCtxGenericRoleStorage.server_compose' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxGenericRoleStorage.server_compose
/-- info: 'BeaconcryptCore.Computational.RawCtxGenericRoleStorage.beacon_compose' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxGenericRoleStorage.beacon_compose
/-- info: 'BeaconcryptCore.Computational.RawCtxGenericRoleStorage.server_roundtrip' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxGenericRoleStorage.server_roundtrip
/-- info: 'BeaconcryptCore.Computational.RawCtxGenericRoleStorage.beacon_roundtrip' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxGenericRoleStorage.beacon_roundtrip
