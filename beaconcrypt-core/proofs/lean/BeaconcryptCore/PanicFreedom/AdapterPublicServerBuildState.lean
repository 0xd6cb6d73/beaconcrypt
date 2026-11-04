-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.PanicFreedom.AdapterPublicServerBuild

/-! The returned peer-map invariant follows through allocator refusal and both actual mutable map lenses. Normality is supplied by the separately proved native builder certificate under individual leaf contracts. -/
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 3000000
namespace BeaconcryptCore.PanicFreedom.AdapterPublicServerBuildState
open Refinement AdapterNormal AdapterPublicOrdinary AdapterPublicServerBuild beaconcrypt_public_wrapper
variable [material : PublicWrapperPlatform.Material] [platform : PublicWrapperPlatform.Platform]
variable [primitive : AdapterInitEdPrimitive.Operations] [PublicWrapperPlatform.Allocator]
variable [localOps : PublicWrapperPlatform.LocalOperations] [crypto : PublicWrapperPlatform.CryptoOperations]
variable [containers : PublicWrapperPlatform.ContainerOperations]
variable [authentication : beaconcrypt.auth.Operations] [recordOps : beaconcrypt.ratchet.Operations]
variable [wire : AdapterWirePrimitive.Operations] [writer : RegistrationWriterPrimitive.Operations]
variable [lookup : AdapterPublicOrdinaryPlatform.LookupOperations]

structure ContainerContracts : Prop where
  reserve : ∀ map result, mapReserve map = ok result → ValidMap map → ValidMap result.2
  entry : ∀ map key result, mapEntry map key = ok result → ValidMap map →
    ValidMap (result.2 result.1)
  insert : ∀ map key entryResult vacant remote insertResult,
    mapEntry map key = ok entryResult → entryResult.1 = .Vacant vacant →
    vacantInsert vacant remote = ok insertResult → ValidMap map → ValidRemote remote →
    ValidMap (entryResult.2 (.Vacant (insertResult.2 insertResult.1)))

omit crypto authentication recordOps wire writer in
private theorem restore_entry (laws : ContainerContracts) (map : AdapterPublicServerBuild.PeerMap)
    (key : U64) (result : AdapterPublicServerBuild.Entry × (AdapterPublicServerBuild.Entry → AdapterPublicServerBuild.PeerMap))
    (selected : AdapterPublicServerBuild.Entry) (actual : mapEntry map key = ok result)
    (same : result.1 = selected) (valid : ValidMap map) : ValidMap (result.2 selected) := by
  rw [← same]
  exact laws.entry map key result actual valid

omit material platform [PublicWrapperPlatform.Allocator] localOps crypto containers authentication recordOps wire writer lookup in
theorem established_remote_valid (signature : shared.SignaturePk beaconcrypt_crypto.crypto_sign.PublicKey)
    (publicKey : beaconcrypt_crypto.crypto_sign.PublicKey)
    (peer : peer.Peer ratchet.concrete.ConcreteRatchetKernel)
    (remote : shared.EstablishedRemote beaconcrypt_crypto.crypto_sign.PublicKey)
    (returned : shared.EstablishedRemote.from_peer signature publicKey peer = ok remote) :
    ValidRemote remote := by
  cases returned
  exact ⟨_, rfl⟩

omit material platform primitive [PublicWrapperPlatform.Allocator] localOps crypto containers authentication recordOps wire writer lookup in
private theorem bind_ok_parts {A B : Type} {work : RustM A} {next : A → RustM B} {result : B}
    (returned : (work >>= next) = ok result) :
    ∃ value, work = ok value ∧ next value = ok result := by
  cases work with
  | fail error | div => cases returned
  | ok value => exact ⟨value, rfl, returned⟩

theorem returned_valid (laws : ContainerContracts) (self : server.Server)
    (reg_out : server.RegistrationOutput) (data : core.option.Option (Slice U8))
    (result : core.option.Option server.RegResponse × server.Server)
    (valid : ValidServer self)
    (returned : server.Server.Insts.BeaconcryptServerProviderServer.build_registration_response self reg_out data = ok result) :
    ValidServer result.2 := by
  unfold server.Server.Insts.BeaconcryptServerProviderServer.build_registration_response at returned
  simp only [AdapterOptionDeref.byte_vector, lift,
    beaconcrypt.auth.execute_hash, beaconcrypt.ratchet.ratchet_hkdf,
    beaconcrypt.ratchet.execute_commitment_hash,
    beaconcrypt_crypto.crypto_sign.PublicKey.from_bytes,
    alloc.sync.Arc.Insts.CoreOpsDerefDeref.deref,
    PublicWrapperPlatform.peerBinding, PublicWrapperPlatform.beaconIdentity,
    core.slice.Slice.len, rust_primitives.slice.slice_length] at returned
  repeat'
    try simp only [uncurry, bind_tc_ok] at returned
    first
      | (have same := RustM.ok.inj returned
         subst result
         change ValidMap _
         dsimp! only)
      | (obtain ⟨value, called, later⟩ := bind_ok_parts returned
         clear returned
         have returned := later
         clear later)
      | (split at returned)
  all_goals try solve_by_elim (maxDepth := 6) [valid, laws.reserve, laws.entry, restore_entry, laws.insert, established_remote_valid]
  all_goals
    apply laws.insert
    · assumption
    · assumption
    · assumption
    · apply laws.reserve
      · assumption
      · exact valid
    · apply established_remote_valid <;> assumption

theorem build_registration_response_preserves (contracts : AdapterPublicServerBuild.Contracts)
    (laws : ContainerContracts) (self : server.Server) (reg_out : server.RegistrationOutput)
    (data : core.option.Option (Slice U8)) (valid : ValidServer self) :
    Ensures (server.Server.Insts.BeaconcryptServerProviderServer.build_registration_response self reg_out data)
      (fun result => ValidServer result.2) := by
  obtain ⟨result, returned⟩ := AdapterPublicServerBuild.build_registration_response_total contracts self reg_out data
  exact ⟨result, returned, returned_valid laws self reg_out data result valid returned⟩

end BeaconcryptCore.PanicFreedom.AdapterPublicServerBuildState
