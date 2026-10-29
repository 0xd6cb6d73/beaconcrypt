-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RawCtxServerRouting

/-! Public associated data accompanies an installed peer identity. The legacy embedding retains identity-derived AD, while completed native registrations supply their actual populated AD281. Neither form supplies ratchet keys or hidden seed material. -/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open beaconcrypt_core

set_option autoImplicit false

namespace BeaconcryptCore.Computational.PqxdhRecordLiftInterface

/-- Public per-peer installation data. Legacy callers retain their original identity-derived AD. -/
structure PeerBinding where
  identity : RawCtxServerRouting.Identity
  associatedData : Option (Std.Array Std.U8 281#usize)

def PeerBinding.legacy (identity : RawCtxServerRouting.Identity) : PeerBinding :=
  ⟨identity, none⟩

instance : Coe RawCtxServerRouting.Identity PeerBinding := ⟨PeerBinding.legacy⟩

/-- Public AD is fixed at installation and does not reveal or choose hidden ratchet material. -/
noncomputable def PeerBinding.associatedArray (server : RawCtxServerRouting.Identity)
    (binding : PeerBinding) : Std.Array Std.U8 281#usize :=
  binding.associatedData.getD (RawCtxServerRouting.associatedArray server binding.identity)

noncomputable def PeerBinding.associatedBytes (server : RawCtxServerRouting.Identity)
    (binding : PeerBinding) : Pqxdh.Bytes :=
  PqxdhRefinement.absBytes (binding.associatedArray server)

def PeerBinding.ofSession (binding : session.SessionBinding) : PeerBinding :=
  ⟨binding.beacon_identity_public_key, some binding.associated_data⟩

theorem PeerBinding.legacy_associatedBytes (server peer : RawCtxServerRouting.Identity) :
    (PeerBinding.legacy peer).associatedBytes server =
      RawCtxServerRouting.associatedBytes server peer := by
  rfl

theorem PeerBinding.ofSession_associatedBytes (server : RawCtxServerRouting.Identity)
    (binding : session.SessionBinding) :
    (PeerBinding.ofSession binding).associatedBytes server =
      PqxdhRefinement.absBytes binding.associated_data := by
  rfl

end BeaconcryptCore.Computational.PqxdhRecordLiftInterface

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftInterface.PeerBinding.legacy_associatedBytes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftInterface.PeerBinding.legacy_associatedBytes

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftInterface.PeerBinding.ofSession_associatedBytes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftInterface.PeerBinding.ofSession_associatedBytes
