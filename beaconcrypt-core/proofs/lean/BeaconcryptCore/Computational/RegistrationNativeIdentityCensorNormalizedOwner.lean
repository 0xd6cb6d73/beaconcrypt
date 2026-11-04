-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorNormalizedJournal
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorActualHashSource
/-! Normalized call snapshots retain exactly the original owner's generated handle and fixed public tuple; only old signature-history slots change. -/
open OracleComp OracleSpec
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityCensorNormalizedOwner
open RegistrationNativePlatformIdentityCtxKeyJournal (Whole owners)
variable {n : Nat} {KemSK Platform : Type} {source : RegistrationNativeMldsa.Source}

/-- A captured normalized owner at the same original callback has that original owner's actual handle/prekey/PQ tuple. -/
theorem captured (placeholder : PqxdhEd25519EufCma.Ed25519Signature)
    (original : Whole n KemSK Platform source)
    (current : RegistrationNativeIdentityCensorEdOutgoingSource.Full (n := n) (KemSK := KemSK) (Platform := Platform) (mlSource := source))
    (same : RegistrationNativeIdentityCensorActualHashSource.project current=RegistrationNativeIdentityCensorNormalizedJournal.project placeholder original)
    (index : Nat) (owner : RegistrationNativeIdentityFrontend.Owner source)
    (found : current.1.1.1.beacons[index]?=some owner) :
    ∃ earlier,(owners original)[index]?=some earlier ∧ RegistrationNativeIdentityMetadata.key earlier=RegistrationNativeIdentityMetadata.key owner := by
  have roster := congrArg (fun before=>before.1.1.beacons) same
  change current.1.1.1.beacons=RegistrationNativeIdentityHistoryView.owners placeholder (owners original) at roster
  rw [roster,RegistrationNativeIdentityHistoryView.owners,List.getElem?_map] at found
  obtain ⟨earlier,present,equal⟩ := Option.map_eq_some_iff.mp found
  subst owner
  exact ⟨earlier,present,rfl⟩

end BeaconcryptCore.Computational.RegistrationNativeIdentityCensorNormalizedOwner

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorNormalizedOwner.captured' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorNormalizedOwner.captured
