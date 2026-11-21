-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.AdapterPublicServerInstall
import BeaconcryptCore.Refinement.AdapterPublicWrapperState
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
/-! Narrow standard map-entry and insertion footprints preserve the complete Server material relation. Installing a peer changes exactly that peer and the actual published control; opaque identity and ML material, replay history and every other peer remain related. -/
namespace BeaconcryptCore.Refinement.AdapterPublicServerInstallMaterial
open AdapterPublicWrapperStorage
open AdapterPublicWrapperState
open BeaconcryptCore.Computational
variable [material : PublicWrapperPlatform.Material] [platform : PublicWrapperPlatform.Platform]
variable [ed : AdapterInitEdPrimitive.Operations]
variable {source : RegistrationNativeMldsa.Source} {KemSK : Type}

theorem control (view : MaterialView source KemSK) (containers : Views)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (credential : RegistrationNativeMldsa.Credential source)
    (stored : beaconcrypt_public_wrapper.server.Server) {n : Nat} (native : RegistrationServerFrontendCompiler.State n)
    (related : Server view containers created credential stored native) (next : pqxdh.ServerState) :
    Server view containers created credential { stored with control := next } { native with control := next } := by
  exact { related with control := rfl }

theorem entry (view : MaterialView source KemSK) (containers : Views)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (credential : RegistrationNativeMldsa.Credential source)
    (stored : beaconcrypt_public_wrapper.server.Server) {n : Nat} (native : RegistrationServerFrontendCompiler.State n)
    (related : Server view containers created credential stored native) (identifier : U64)
    (result : Entry × (Entry → PeerMap)) (preserves : PeerEntry containers stored.known_ids identifier result) :
    Server view containers created credential { stored with known_ids := result.2 result.1 } native := by
  rcases related.peers with ⟨records, reached, sender, identity, peers⟩
  refine { related with peers := ⟨records, reached, sender, identity, ?_⟩ }
  intro query
  rw [preserves.2 query]
  exact peers query

theorem vacant (view : MaterialView source KemSK) (containers : Views)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (credential : RegistrationNativeMldsa.Credential source)
    (stored : beaconcrypt_public_wrapper.server.Server) {n : Nat} (native : RegistrationServerFrontendCompiler.State n)
    (related : Server view containers created credential stored native)
    (pending : peer.PeerInsert (alloc.vec.Vec U8)) (publicKey : ed.PublicKey)
    (back : Entry → PeerMap)
    (result : Remote ed.PublicKey × (Remote ed.PublicKey → Vacant))
    (updates : VacantInsert containers stored.known_ids pending.peer.binding.assigned_key_id back
      (AdapterPublicServerInstall.remote pending publicKey) result) :
    Server view containers created credential
      { stored with known_ids := back (.Vacant (result.2 result.1)), control := pending.next }
      { withPeer native pending.peer.binding.assigned_key_id
        ⟨pending.peer.binding.beacon_identity_public_key, pending.peer.ratchet, pending.peer.binding.associated_data⟩
        with control := pending.next } := by
  exact control view containers created credential _ _
    (peer_inserted view containers created credential stored native related _ back
      (AdapterPublicServerInstall.remote pending publicKey) result _ updates
      (AdapterPublicServerInstall.remote_view pending publicKey)) pending.next
end BeaconcryptCore.Refinement.AdapterPublicServerInstallMaterial

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicServerInstallMaterial.control' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicServerInstallMaterial.control

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicServerInstallMaterial.entry' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicServerInstallMaterial.entry

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicServerInstallMaterial.vacant' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicServerInstallMaterial.vacant
