-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSecretWordLifecycleOwnerFinish

/-! Actual public scalar erasure and restoration preserve terminal phases at the same local owner positions. Native creation, outgoing publication and both selected and ordinary incoming finish therefore cannot revive a consumed owner. The optional raw response is inspected only after the actual native terminal move. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSecretWordLifecycleOwnerRoster
open PqxdhServerAuthExperiment (Setup)
open RegistrationWorldAgreementCompiler (EnvState)
open RegistrationNativeSecretWordLifecycleOwnerPhase (Terminal NativeDone Done)
variable {n : Nat} {ι KemSK Auxiliary Value : Type} {base : OracleSpec ι}
variable {source : RegistrationNativeMldsa.Source}

/-- Restoring a private scalar leaves the terminal role at exactly the same local list position. -/
theorem restore_done (index : Nat) (owners : RegistrationNativePublicOwners.State source) (valid : Done index owners) :
    NativeDone index (owners.map RegistrationNativePublicOwners.restore) := by
  obtain ⟨owner, found, terminal⟩ := valid
  exact ⟨RegistrationNativePublicOwners.restore owner, by simp only [List.getElem?_map, found, Option.map_some], terminal⟩

/-- Packing the actual selected or ordinary source owner leaves its lifecycle position and terminal phase literal. -/
theorem pack_done (index selected : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
    (owners : RegistrationNativeBeaconFrontend.State source) (valid : NativeDone index owners) :
    Done index (RegistrationNativePublicOwners.pack selected publicPrekey owners) := by
  obtain ⟨owner, found, terminal⟩ := valid
  unfold Done
  simp only [RegistrationNativePublicOwners.pack, List.getElem?_mapIdx, found, Option.map_some]
  by_cases chosen : index = selected
  · simp only [chosen, ite_true]
    exact ⟨_, rfl, terminal⟩
  · simp only [chosen, ite_false]
    exact ⟨_, rfl, terminal⟩

/-- Every actual public constructor retains all earlier consumed owners, regardless of selected scalar erasure or failure. -/
theorem create_done (setup : Setup base KemSK) (index selected : Nat)
    (publicPrekey : PqxdhJointIdentity.PeerEncoding) (edPin : Std.Array U8 32#usize) (mlPin : Std.Array U8 1952#usize) (keyId : U64)
    (owners : RegistrationNativePublicOwners.State source) (env : EnvState Auxiliary)
    (result : (RustM (Option Nat) × RegistrationNativePublicOwners.State source) × EnvState Auxiliary)
    (valid : Done index owners) (supported : result ∈ support
      (((RegistrationNativePublicOwners.create (n := n) setup source selected publicPrekey edPin mlPin keyId).run owners).run env)) :
    Done index result.1.2 := by
  simp only [RegistrationNativePublicOwners.create, RegistrationNativePublicOwners.executeLocal, StateT.run, support_map] at supported
  obtain ⟨native, reached, equal⟩ := supported
  have original := PqxdhDeploymentEnvironment.support_simulateQ_subset _ _ reached
  have kept := RegistrationNativeSecretWordLifecycleOwnerPhase.create_done setup index edPin mlPin keyId
    (owners.map RegistrationNativePublicOwners.restore) env native (restore_done index owners valid) original
  cases equal
  exact pack_done index selected publicPrekey native.1.2 kept

/-- Actual outgoing bundles never restore a consumed owner, including failed publication and signature attempts. -/
theorem bundle_done (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire) (index selected target : Nat)
    (publicPrekey : PqxdhJointIdentity.PeerEncoding) (owners : RegistrationNativePublicOwners.State source) (env : EnvState Auxiliary)
    (result : (RustM (Option Pqxdh.Bytes) × RegistrationNativePublicOwners.State source) × EnvState Auxiliary)
    (valid : Done index owners) (supported : result ∈ support
      (((RegistrationNativePublicOwners.bundle (n := n) setup source wire selected publicPrekey target).run owners).run env)) :
    Done index result.1.2 := by
  simp only [RegistrationNativePublicOwners.bundle, RegistrationNativePublicOwners.executeLocal, StateT.run, support_map] at supported
  obtain ⟨native, reached, equal⟩ := supported
  have original := PqxdhDeploymentEnvironment.support_simulateQ_subset _ _ reached
  have kept := RegistrationNativeSecretWordLifecycleOwnerPhase.bundle_done setup wire index target
    (owners.map RegistrationNativePublicOwners.restore) env native (restore_done index owners valid) original
  cases equal
  exact pack_done index selected publicPrekey native.1.2 kept

private theorem finish_view (setup : Setup base KemSK) (index : Nat) (packet : Option registration.ResponsePacket)
    (owners : RegistrationNativePublicOwners.State source) (env : EnvState RegistrationServerRoleBackend.State)
    (owner : RegistrationNativePublicOwners.Owner source) (found : owners[index]? = some owner)
    (result : (RustM (Option Pqxdh.Bytes) × RegistrationNativePublicOwners.State source) × EnvState RegistrationServerRoleBackend.State)
    (supported : result ∈ support
      (((RegistrationNativePublicOwners.finish (n := n) setup source index packet).run owners).run env)) :
    ∃ middle, middle ∈ support (((RegistrationBeaconReferenceFinish.finish (n := n) setup source packet).run owner.view).run env) ∧
      result = ((middle.1.1, owners.set index { owner with view := middle.1.2 }), middle.2) := by
  simp only [RegistrationNativePublicOwners.finish, StateT.run, found, support_map] at supported
  obtain ⟨middle, reached, equal⟩ := supported
  refine ⟨middle, ?_, equal.symm⟩
  cases selected : owner.scalar with
  | none => simpa only [selected, StateT.run] using reached
  | some scalar =>
      simp only [selected] at reached
      simpa only [StateT.run] using PqxdhDeploymentEnvironment.support_simulateQ_subset _ _ reached

/-- Selected and ordinary finish retain every already consumed owner at its actual local position. -/
theorem finish_done (setup : Setup base KemSK) (index target : Nat) (packet : Option registration.ResponsePacket)
    (owners : RegistrationNativePublicOwners.State source) (env : EnvState RegistrationServerRoleBackend.State)
    (result : (RustM (Option Pqxdh.Bytes) × RegistrationNativePublicOwners.State source) × EnvState RegistrationServerRoleBackend.State)
    (valid : Done index owners) (supported : result ∈ support
      (((RegistrationNativePublicOwners.finish (n := n) setup source target packet).run owners).run env)) :
    Done index result.1.2 := by
  cases found : owners[target]? with
  | none =>
      simp only [RegistrationNativePublicOwners.finish, StateT.run, found, mem_support_pure_iff] at supported
      cases supported
      exact valid
  | some owner =>
      obtain ⟨middle, reached, rfl⟩ := finish_view setup target packet owners env owner found result supported
      by_cases same : index = target
      · subst target
        obtain ⟨old, oldAt, terminal⟩ := valid
        have equal : old = owner := Option.some.inj (oldAt.symm.trans found)
        subst old
        have kept := RegistrationNativeSecretWordLifecycleOwnerFinish.reference_terminal setup packet owner.view env middle terminal reached
        exact ⟨{ owner with view := middle.1.2 }, List.getElem?_set_self (List.getElem?_eq_some_iff.mp found).1, kept⟩
      · obtain ⟨old, oldAt, terminal⟩ := valid
        exact ⟨old, by simpa only [List.getElem?_set_ne (Ne.symm same)] using oldAt, terminal⟩

/-- Passing the native pending move consumes exactly the selected public owner's position before any optional raw response admission. -/
theorem finish_consumes (setup : Setup base KemSK) (index : Nat) (packet : Option registration.ResponsePacket)
    (owners : RegistrationNativePublicOwners.State source) (env : EnvState RegistrationServerRoleBackend.State)
    (owner : RegistrationNativePublicOwners.Owner source) (found : owners[index]? = some owner)
    (pending : registration.BeaconPending) (oneTime : PqxdhJointGapDh.ScalarBytes) (aborted : pqxdh.BeaconAborted)
    (sent : owner.view.phase = .initSent pending oneTime) (moved : pending.aborted_state = .ok aborted)
    (result : (RustM (Option Pqxdh.Bytes) × RegistrationNativePublicOwners.State source) × EnvState RegistrationServerRoleBackend.State)
    (supported : result ∈ support
      (((RegistrationNativePublicOwners.finish (n := n) setup source index packet).run owners).run env)) :
    Done index result.1.2 := by
  obtain ⟨middle, reached, rfl⟩ := finish_view setup index packet owners env owner found result supported
  have terminal := RegistrationNativeSecretWordLifecycleOwnerFinish.reference_consumes setup packet owner.view env
    pending oneTime aborted sent moved middle reached
  exact ⟨{ owner with view := middle.1.2 }, List.getElem?_set_self (List.getElem?_eq_some_iff.mp found).1, terminal⟩

end BeaconcryptCore.Computational.RegistrationNativeSecretWordLifecycleOwnerRoster
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordLifecycleOwnerRoster.restore_done' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordLifecycleOwnerRoster.restore_done
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordLifecycleOwnerRoster.pack_done' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordLifecycleOwnerRoster.pack_done
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordLifecycleOwnerRoster.create_done' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordLifecycleOwnerRoster.create_done
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordLifecycleOwnerRoster.bundle_done' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordLifecycleOwnerRoster.bundle_done
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordLifecycleOwnerRoster.finish_done' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordLifecycleOwnerRoster.finish_done
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordLifecycleOwnerRoster.finish_consumes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordLifecycleOwnerRoster.finish_consumes
