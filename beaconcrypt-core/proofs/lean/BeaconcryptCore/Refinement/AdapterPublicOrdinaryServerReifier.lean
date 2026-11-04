-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.AdapterPublicOrdinaryServerLookup
import BeaconcryptCore.Refinement.AdapterPublicWrapperState
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
/-! Record state is reconstructed from the returned source Server and its actual map view. Mutable manager updates preserve every unrelated peer. The raw-attempt count is an explicit source observer coordinate; no model-final peer map, log or counter is copied. -/
namespace BeaconcryptCore.Refinement.AdapterPublicOrdinaryServerReifier
open BeaconcryptCore.Computational AdapterPublicWrapperStorage
variable {source : RegistrationNativeMldsa.Source} {KemSK : Type}
variable [material : PublicWrapperPlatform.Material] [platform : PublicWrapperPlatform.Platform]
variable [ed : AdapterInitEdPrimitive.Operations]

def peers (views : Views) (self : beaconcrypt_public_wrapper.server.Server) :
    U64 →Option (RawCtxServerRouting.Peer (Std.Array U8 281#usize)) :=
  fun key=>(views.peer self.known_ids key).bind peerView

def server (view : AdapterPublicWrapperState.MaterialView source KemSK) (views : Views)
    (self : beaconcrypt_public_wrapper.server.Server) (rawAttempts : Nat) : PqxdhRecordLiftWorld.Server :=
  let identity:=platform.arcView self.identity
  ⟨identity.identity_key_kid,⟨⟨view.edPublic identity.identity_key.public_key,peers views self,()⟩,rawAttempts⟩⟩

theorem related {n : Nat} (view : AdapterPublicWrapperState.MaterialView source KemSK) (views : Views)
    (created : PqxdhLiveServerConstruction.Created Unit) (credential : RegistrationNativeMldsa.Credential source)
    (self : beaconcrypt_public_wrapper.server.Server) (native : RegistrationServerFrontendCompiler.State n)
    (held : AdapterPublicWrapperState.Server view views created credential self native) :
    ∃records,native.world.world.1.server=some records ∧ server view views self records.records.rawAttempts=records := by
  obtain ⟨records,present,sender,identity,matched⟩:=held.peers
  have peerEq : peers views self=records.records.server.peers := funext fun key=>(matched key).1
  refine ⟨records,present,?_⟩
  cases records with
  | mk actualSender actualRecords=>
    cases actualRecords with
    | mk actualServer attempts=>
      cases actualServer with
      | mk actualIdentity actualPeers metadata=>
        cases metadata
        dsimp only at sender identity peerEq
        dsimp only [server]
        rw [held.identity.identifier,held.identity.publicKey,peerEq,←sender,←identity]

omit material platform in
theorem peer_kernel (remote : Remote ed.PublicKey) (manager : Manager)
    (kernel : ratchet.concrete.ConcreteRatchetKernel) (stored : manager.refined.kernel=some kernel) :
    peerView {remote with peer:={remote.peer with ratchet:=manager}}=
      some ⟨remote.peer.binding.beacon_identity_public_key,kernel,remote.peer.binding.associated_data⟩ := by
  simp only [peerView,stored,Option.map_some]

theorem restore_peers (views : Views) (self : beaconcrypt_public_wrapper.server.Server) (key : U64)
    (remote : Remote ed.PublicKey) (back : Option (Remote ed.PublicKey) →PeerMap)
    (lens : ∀changed query,views.peer (back changed) query=if query=key then changed else views.peer self.known_ids query)
    (manager : Manager) (kernel : ratchet.concrete.ConcreteRatchetKernel) (stored : manager.refined.kernel=some kernel) :
    peers views (AdapterPublicOrdinaryServerLookup.restore self (some remote) back (some manager))=
      Function.update (peers views self) key
        (some ⟨remote.peer.binding.beacon_identity_public_key,kernel,remote.peer.binding.associated_data⟩) := by
  funext query
  unfold peers
  rw [AdapterPublicOrdinaryServerLookup.restore_view views self key (some remote) back lens]
  by_cases selected:query=key
  · subst query
    simp only [ite_true,AdapterPublicOrdinaryServerLookup.managerUpdate,Option.getD_some,Option.bind_some,Function.update_self]
    exact peer_kernel remote manager kernel stored
  · simp only [selected,ite_false,Function.update_of_ne selected]

theorem restore_live (views : Views) (self : beaconcrypt_public_wrapper.server.Server) (key : U64)
    (remote : Remote ed.PublicKey) (back : Option (Remote ed.PublicKey) →PeerMap)
    (lens : ∀changed query,views.peer (back changed) query=if query=key then changed else views.peer self.known_ids query)
    (manager : Manager) (kernel : ratchet.concrete.ConcreteRatchetKernel) (stored : manager.refined.kernel=some kernel)
    (before : ∀query,(views.peer self.known_ids query).isSome=(peers views self query).isSome) :
    ∀query,(views.peer (AdapterPublicOrdinaryServerLookup.restore self (some remote) back (some manager)).known_ids query).isSome=
      (peers views (AdapterPublicOrdinaryServerLookup.restore self (some remote) back (some manager)) query).isSome := by
  intro query
  rw [AdapterPublicOrdinaryServerLookup.restore_view views self key (some remote) back lens,
    restore_peers views self key remote back lens manager kernel stored]
  by_cases selected:query=key
  · subst query
    simp only [ite_true,AdapterPublicOrdinaryServerLookup.managerUpdate,Option.getD_some,Option.isSome_some,Function.update_self]
  · simp only [selected,ite_false,Function.update_of_ne selected]
    exact before query

def install {n : Nat} (view : AdapterPublicWrapperState.MaterialView source KemSK) (views : Views)
    (self : beaconcrypt_public_wrapper.server.Server) (rawAttempts : Nat) (native : RegistrationServerFrontendCompiler.State n) :
    RegistrationServerFrontendCompiler.State n :=
  {native with world:={native.world with world:=({native.world.world.1 with server:=some (server view views self rawAttempts)},native.world.world.2)}}

theorem restored_material {n : Nat} (view : AdapterPublicWrapperState.MaterialView source KemSK) (views : Views)
    (created : PqxdhLiveServerConstruction.Created Unit) (credential : RegistrationNativeMldsa.Credential source)
    (self : beaconcrypt_public_wrapper.server.Server) (native : RegistrationServerFrontendCompiler.State n)
    (held : AdapterPublicWrapperState.Server view views created credential self native)
    (key : U64) (remote : Remote ed.PublicKey) (back : Option (Remote ed.PublicKey) →PeerMap)
    (lens : ∀changed query,views.peer (back changed) query=if query=key then changed else views.peer self.known_ids query)
    (manager : Manager) (kernel : ratchet.concrete.ConcreteRatchetKernel) (stored : manager.refined.kernel=some kernel)
    (rawAttempts : Nat) :
    let returned:=AdapterPublicOrdinaryServerLookup.restore self (some remote) back (some manager)
    AdapterPublicWrapperState.Server view views created credential returned (install view views returned rawAttempts native) := by
  obtain ⟨records,_present,_sender,_identity,matched⟩:=held.peers
  have live : ∀query,(views.peer self.known_ids query).isSome=(peers views self query).isSome := by
    intro query
    exact (matched query).2.trans (congrArg Option.isSome (matched query).1.symm)
  refine { identity := held.identity
           control := held.control
           pinIdentity := held.pinIdentity
           pinIdentifier := held.pinIdentifier
           pinMldsa := held.pinMldsa
           replay := held.replay
           peers := ?_ }
  refine ⟨server view views _ rawAttempts,rfl,held.identity.identifier,held.identity.publicKey,?_⟩
  intro query
  exact ⟨rfl,restore_live views self key remote back lens manager kernel stored live query⟩

end BeaconcryptCore.Refinement.AdapterPublicOrdinaryServerReifier

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicOrdinaryServerReifier.related' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicOrdinaryServerReifier.related

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicOrdinaryServerReifier.peer_kernel' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicOrdinaryServerReifier.peer_kernel

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicOrdinaryServerReifier.restore_peers' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicOrdinaryServerReifier.restore_peers

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicOrdinaryServerReifier.restore_live' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicOrdinaryServerReifier.restore_live

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicOrdinaryServerReifier.restored_material' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicOrdinaryServerReifier.restored_material
