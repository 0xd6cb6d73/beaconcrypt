-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.AdapterPublicWrapperExtraction.Funs
import BeaconcryptCore.AdapterPublicOrdinaryExtraction.Funs
import BeaconcryptCore.PanicFreedom.AdapterNormal
import BeaconcryptCore.PanicFreedom.AdapterConstructors

/-! Native public getters, structural peer lenses, and populated-slot construction. The only contracts concern the actual ML-DSA public-key, Ed25519 public-byte and hash leaves. -/
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true

namespace BeaconcryptCore.PanicFreedom.AdapterPublicTrivial
open Refinement AdapterNormal
open beaconcrypt_public_wrapper
variable [material : PublicWrapperPlatform.Material]
variable [platform : PublicWrapperPlatform.Platform]
variable [primitive : AdapterInitEdPrimitive.Operations]
variable [localOps : PublicWrapperPlatform.LocalOperations]
variable [crypto : PublicWrapperPlatform.CryptoOperations]
variable [authentication : beaconcrypt.auth.Operations]

omit platform in
structure Contracts : Prop where
  mldsaPublic : ∀ identity, Normal (localOps.auth_MldsaIdentity_public_key identity)
  edPublicBytes : ∀ key, Normal (crypto.edPublicBytes key)
  hash : ∀ request, Normal (authentication.hash request)


omit platform localOps crypto authentication in
theorem beacon_identity_pk_total (self : beacon.Beacon) :
    ∃ result, beacon.Beacon.identity_pk self = ok result := ⟨_, rfl⟩

omit platform localOps crypto authentication in
theorem beacon_identity_sk_total (self : beacon.Beacon) :
    ∃ result, beacon.Beacon.identity_sk self = ok result := ⟨_, rfl⟩

omit material platform primitive localOps crypto authentication in
theorem slot_new_total (kernel : ratchet.concrete.ConcreteRatchetKernel) :
    ∃ result, beaconcrypt_public_wrapper.ratchet.RatchetKernelSlot.new kernel = ok result := ⟨_, rfl⟩

omit material platform primitive localOps crypto authentication in
theorem manager_from_kernel_total (kernel : ratchet.concrete.ConcreteRatchetKernel) :
    ∃ result, beaconcrypt_public_wrapper.ratchet.RatchetManager.from_kernel kernel = ok result := ⟨_, rfl⟩

omit material platform primitive localOps crypto authentication in
theorem manager_from_kernel_populated (kernel : ratchet.concrete.ConcreteRatchetKernel) :
    beaconcrypt_public_wrapper.ratchet.RatchetManager.from_kernel kernel =
      ok { refined := { kernel := .Some kernel } } := rfl

omit localOps crypto authentication in
theorem server_identity_pk_total (self : server.Server) :
    ∃ result, server.Server.identity_pk self = ok result := ⟨_, rfl⟩

omit localOps crypto authentication in
theorem server_identity_key_kid_total (self : server.Server) :
    ∃ result, server.Server.identity_key_kid self = ok result := ⟨_, rfl⟩

omit localOps crypto authentication in
theorem server_identity_sk_total (self : server.Server) :
    ∃ result, server.Server.identity_sk self = ok result := ⟨_, rfl⟩

omit material platform primitive localOps crypto authentication in
theorem map_peer_ratchet_total (peer : peer.Peer ratchet.concrete.ConcreteRatchetKernel) :
    ∃ result, shared.map_peer_ratchet peer = ok result := ⟨_, rfl⟩

omit material platform primitive localOps crypto authentication in
theorem established_remote_from_peer_total {Pk : Type} (signature : shared.SignaturePk Pk)
    (pk : Pk) (peer : peer.Peer ratchet.concrete.ConcreteRatchetKernel) :
    ∃ result, shared.EstablishedRemote.from_peer signature pk peer = ok result := ⟨_, rfl⟩

omit material platform primitive localOps crypto authentication in
theorem receive_transition_into_option_total {T : Type}
    (self : beaconcrypt_public_ordinary.server.ReceiveTransition T) :
    ∃ result, beaconcrypt_public_ordinary.server.ReceiveTransition.into_option self = ok result :=
  ⟨match self with | .Rejected => .None | .Accepted result => .Some result, by cases self <;> rfl⟩

omit localOps crypto authentication in
theorem ordinary_server_identity_key_kid_total (self : server.Server) :
    ∃ result, beaconcrypt_public_ordinary.server.Server.identity_key_kid self = ok result := ⟨_, rfl⟩

omit material platform primitive localOps crypto authentication in
theorem established_remote_ratchet_mut_total {Pk : Type} (signature : shared.SignaturePk Pk)
    (self : shared.EstablishedRemote Pk) :
    ∃ result, beaconcrypt_public_ordinary.shared.EstablishedRemote.ratchet_mut signature self = ok result := ⟨_, rfl⟩

omit material platform primitive localOps crypto authentication in
theorem established_remote_binding_total {Pk : Type} (signature : shared.SignaturePk Pk)
    (self : shared.EstablishedRemote Pk) :
    ∃ result, beaconcrypt_public_ordinary.shared.EstablishedRemote.binding signature self = ok result := ⟨_, rfl⟩

theorem beacon_mldsa_public_key_total (contracts : Contracts) (self : beacon.Beacon) :
    ∃ result, beacon.Beacon.mldsa_public_key self = ok result := contracts.mldsaPublic self.authentication.identity

theorem server_mldsa_public_key_total (contracts : Contracts) (self : server.Server) :
    ∃ result, server.Server.mldsa_public_key self = ok result := contracts.mldsaPublic (platform.arcView self.identity).mldsa_identity

theorem server_authentication_pin_total (contracts : Contracts) (self : server.Server) :
    ∃ result, server.Server.authentication_pin self = ok result := by
  unfold server.Server.authentication_pin
  simp only [server.Server.identity_pk, server.Server.identity_key_kid, server.Server.mldsa_public_key,
    alloc.sync.Arc.Insts.CoreOpsDerefDeref.deref, bind_tc_ok]
  obtain ⟨keyBytes, keyBytesEq⟩ := contracts.edPublicBytes (platform.arcView self.identity).identity_key.public_key
  obtain ⟨mldsaKey, mldsaKeyEq⟩ := contracts.mldsaPublic (platform.arcView self.identity).mldsa_identity
  simpa only [beaconcrypt_crypto.crypto_sign.PublicKey.as_bytes, keyBytesEq,
    auth.MldsaIdentity.public_key, mldsaKeyEq, bind_tc_ok] using
    AdapterConstructors.fingerprint_pin_total contracts.hash
      { identity_public_key := keyBytes, identity_key_id := (platform.arcView self.identity).identity_key_kid } mldsaKey

end BeaconcryptCore.PanicFreedom.AdapterPublicTrivial
