-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RawCtxServerRouting

/-! Current record installations carry an explicit complete AD151 from the completed session. The independent historical identity-derived AD model is not a constructor of this capability. No identity-only coercion or missing-hash fallback can produce a current binding. -/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open beaconcrypt_core

set_option autoImplicit false

namespace BeaconcryptCore.Computational.PqxdhRecordLiftInterface

/-- Public per-peer installation data. A completed transcript hash is required by production registration before construction. -/
structure PeerBinding where
  identity : RawCtxServerRouting.Identity
  associatedData : Std.Array Std.U8 151#usize

/-- Routing reads the exact complete AD fixed at installation. -/
def PeerBinding.associatedArray (_server : RawCtxServerRouting.Identity)
    (binding : PeerBinding) : Std.Array Std.U8 151#usize := binding.associatedData

def PeerBinding.associatedBytes (server : RawCtxServerRouting.Identity)
    (binding : PeerBinding) : Pqxdh.Bytes :=
  PqxdhRefinement.absBytes (binding.associatedArray server)

def PeerBinding.ofSession (binding : session.SessionBinding) : PeerBinding :=
  ⟨binding.beacon_identity_public_key, binding.associated_data⟩

theorem PeerBinding.ofSession_associatedBytes (server : RawCtxServerRouting.Identity)
    (binding : session.SessionBinding) :
    (PeerBinding.ofSession binding).associatedBytes server =
      PqxdhRefinement.absBytes binding.associated_data := by
  rfl

end BeaconcryptCore.Computational.PqxdhRecordLiftInterface

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftInterface.PeerBinding.ofSession_associatedBytes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftInterface.PeerBinding.ofSession_associatedBytes
