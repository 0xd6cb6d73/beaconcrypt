-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePublicInvariantRequests

/-! Public pending coherence depends only on the retained lifecycle phase. Restoring a private scalar or packing an outgoing public prekey does not change it. Actual native constructors and outgoing controllers therefore provide its public preservation law before any cryptographic hybrid is selected. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePublicInvariantOwners
open PqxdhServerAuthExperiment (Setup)
open RegistrationWorldAgreementCompiler (EnvState)
open RegistrationNativeBeaconCoherence (PhaseCoherent)
variable {n : Nat} {ι KemSK Auxiliary : Type} {base : OracleSpec ι}
variable {source : RegistrationNativeMldsa.Source}

def Coherent (roster : RegistrationNativePublicOwners.State source) : Prop :=
  ∀ (index : Nat) (owner : RegistrationNativePublicOwners.Owner source),
    roster[index]? = some owner → PhaseCoherent owner.view.phase

private theorem lookup_iff {Item : Type} (predicate : Item → Prop) (items : List Item) :
    (∀ (index : Nat) (item : Item), items[index]? = some item → predicate item) ↔ ∀ item ∈ items, predicate item := by
  constructor
  · induction items with
    | nil => simp
    | cons first rest ih =>
        intro valid item member
        rcases List.mem_cons.mp member with rfl | member
        · exact valid 0 _ rfl
        · exact ih (fun index selected found => valid (index + 1) selected (by simpa only [List.getElem?_cons_succ] using found)) item member
  · intro valid index item found
    exact valid item (List.mem_of_getElem? found)

/-- Pending coherence is a property of all retained public owners, independently of their indices or private scalar restoration. -/
theorem coherent_iff (roster : RegistrationNativePublicOwners.State source) :
    Coherent roster ↔ ∀ owner ∈ roster, PhaseCoherent owner.view.phase := lookup_iff _ _

/-- Every private scalar restoration has exactly the public roster's phase-coherence property. -/
theorem restored_holds (scalar : PqxdhJointGapDh.ScalarBytes) (roster : RegistrationNativePublicOwners.State source) :
    Coherent roster ↔ RegistrationNativeBeaconCoherence.Holds (RegistrationNativePublicSourceState.owners scalar roster) := by
  constructor
  · intro valid
    apply (lookup_iff (fun owner : RegistrationNativeBeaconFrontend.Owner source => PhaseCoherent owner.phase)
      (RegistrationNativePublicSourceState.owners scalar roster)).mp
    intro index owner found
    simp only [RegistrationNativePublicSourceState.owners, List.getElem?_map, Option.map_eq_some_iff] at found
    obtain ⟨original, present, rfl⟩ := found
    exact valid index original present
  · intro valid index owner found
    have present : (RegistrationNativePublicSourceState.owners scalar roster)[index]? =
        some (RegistrationNativePublicSourceState.owner scalar owner) := by
      simp only [RegistrationNativePublicSourceState.owners, List.getElem?_map, found, Option.map_some]
    exact valid _ (List.mem_of_getElem? present)

/-- Scalar erasure and selected-public-prekey packing retain every coherent pending native capability. -/
theorem packed_holds (selected : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
    (roster : RegistrationNativeBeaconFrontend.State source) (valid : RegistrationNativeBeaconCoherence.Holds roster) :
    Coherent (RegistrationNativePublicOwners.pack selected publicPrekey roster) := by
  intro index owner found
  simp only [RegistrationNativePublicOwners.pack, List.getElem?_mapIdx, Option.map_eq_some_iff] at found
  obtain ⟨original, present, rfl⟩ := found
  have prior := valid original (List.mem_of_getElem? present)
  by_cases chosen : index = selected
  · simpa only [chosen, ite_true, RegistrationBeaconReferenceCompiler.eraseOwner] using prior
  · simpa only [chosen, ite_false, RegistrationBeaconReferenceCompiler.eraseOwner] using prior

private theorem dummy_holds (roster : RegistrationNativePublicOwners.State source) (valid : Coherent roster) :
    RegistrationNativeBeaconCoherence.Holds (roster.map RegistrationNativePublicOwners.restore) := by
  change RegistrationNativeBeaconCoherence.Holds
    (RegistrationNativePublicSourceState.owners RegistrationNativePublicOwners.dummy roster)
  exact (restored_holds RegistrationNativePublicOwners.dummy roster).mp valid

/-- The actual public constructor preserves all pending capabilities; any new owner is fresh. -/
theorem create_coherent (setup : Setup base KemSK) (selected : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
    (edPin : Std.Array U8 32#usize) (mlPin : Std.Array U8 1952#usize) (keyId : U64)
    (roster : RegistrationNativePublicOwners.State source) (env : EnvState Auxiliary)
    (result : (RustM (Option Nat) × RegistrationNativePublicOwners.State source) × EnvState Auxiliary)
    (valid : Coherent roster) (supported : result ∈ support
      (((RegistrationNativePublicOwners.create (n := n) setup source selected publicPrekey edPin mlPin keyId).run roster).run env)) :
    Coherent result.1.2 := by
  simp only [RegistrationNativePublicOwners.create, RegistrationNativePublicOwners.executeLocal, StateT.run, support_map] at supported
  obtain ⟨reached, member, equal⟩ := supported
  have native := PqxdhDeploymentEnvironment.support_simulateQ_subset _ _ member
  have kept := RegistrationNativeBeaconCoherence.create_keeps setup edPin mlPin keyId
    (roster.map RegistrationNativePublicOwners.restore) env reached (dummy_holds roster valid) native
  cases equal
  exact packed_holds selected publicPrekey reached.1.2 kept

/-- Actual outgoing signing, encoding failure and successful pending installation preserve the public coherence property. -/
theorem bundle_coherent (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (selected : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding) (index : Nat)
    (roster : RegistrationNativePublicOwners.State source) (env : EnvState Auxiliary)
    (result : (RustM (Option Pqxdh.Bytes) × RegistrationNativePublicOwners.State source) × EnvState Auxiliary)
    (valid : Coherent roster) (supported : result ∈ support
      (((RegistrationNativePublicOwners.bundle (n := n) setup source wire selected publicPrekey index).run roster).run env)) :
    Coherent result.1.2 := by
  simp only [RegistrationNativePublicOwners.bundle, RegistrationNativePublicOwners.executeLocal, StateT.run, support_map] at supported
  obtain ⟨reached, member, equal⟩ := supported
  have native := PqxdhDeploymentEnvironment.support_simulateQ_subset _ _ member
  have kept := RegistrationNativeBeaconCoherence.bundle_keeps setup wire index
    (roster.map RegistrationNativePublicOwners.restore) env reached (dummy_holds roster valid) native
  cases equal
  exact packed_holds selected publicPrekey reached.1.2 kept

end BeaconcryptCore.Computational.RegistrationNativePublicInvariantOwners

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePublicInvariantOwners.coherent_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePublicInvariantOwners.coherent_iff
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePublicInvariantOwners.restored_holds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePublicInvariantOwners.restored_holds
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePublicInvariantOwners.packed_holds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePublicInvariantOwners.packed_holds
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePublicInvariantOwners.create_coherent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePublicInvariantOwners.create_coherent
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePublicInvariantOwners.bundle_coherent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePublicInvariantOwners.bundle_coherent
