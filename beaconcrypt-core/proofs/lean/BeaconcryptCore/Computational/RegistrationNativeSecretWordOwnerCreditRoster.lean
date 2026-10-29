-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSecretWordOwnerCreditFinish
import BeaconcryptCore.Computational.RegistrationNativeSecretWordLifecycleOwnerRoster

/-! Actual symbolic owner birth/publication retain all earlier terminal positions, and selected or ordinary symbolic finish consumes its own position before optional response admission. No concrete KEM handle is identified with a local owner position by these lifecycle statements. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSecretWordOwnerCreditRoster
open PqxdhServerAuthExperiment (Setup)
open RegistrationWorldAgreementCompiler (EnvState)
open RegistrationNativeSecretWordLifecycleOwnerPhase (Terminal Done)
variable {n : Nat} {ι KemSK Auxiliary : Type} {base : OracleSpec ι} {source : RegistrationNativeMldsa.Source}

/-- Every actual public constructor retains all earlier consumed owners, regardless of selected scalar erasure or failure. -/
theorem create_done (setup : Setup base KemSK) (index selected : Nat)
    (publicPrekey : PqxdhJointIdentity.PeerEncoding) (edPin : Std.Array U8 32#usize) (mlPin : Std.Array U8 1952#usize) (keyId : U64)
    (owners : RegistrationNativePublicOwners.State source) (env : EnvState Auxiliary)
    (result : (RustM (Option Nat) × RegistrationNativePublicOwners.State source) × EnvState Auxiliary)
    (valid : Done index owners) (supported : result ∈ support
      (((RegistrationNativeSecretWordOwners.create (n := n) setup source selected publicPrekey edPin mlPin keyId).run owners).run env)) :
    Done index result.1.2 := by
  simp only [RegistrationNativeSecretWordOwners.create, RegistrationNativeSecretWordOwners.executeLocal, StateT.run] at supported
  have original := PqxdhDeploymentEnvironment.support_simulateQ_subset _ _ supported
  exact RegistrationNativeSecretWordLifecycleOwnerRoster.create_done setup index selected publicPrekey edPin mlPin keyId
    owners env result valid original

/-- Actual outgoing bundles never restore a consumed owner, including failed publication and signature attempts. -/
theorem bundle_done (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire) (index selected target : Nat)
    (publicPrekey : PqxdhJointIdentity.PeerEncoding) (owners : RegistrationNativePublicOwners.State source) (env : EnvState Auxiliary)
    (result : (RustM (Option Pqxdh.Bytes) × RegistrationNativePublicOwners.State source) × EnvState Auxiliary)
    (valid : Done index owners) (supported : result ∈ support
      (((RegistrationNativeSecretWordOwners.bundle (n := n) setup source wire selected publicPrekey target).run owners).run env)) :
    Done index result.1.2 := by
  simp only [RegistrationNativeSecretWordOwners.bundle, RegistrationNativeSecretWordOwners.executeLocal, StateT.run] at supported
  have original := PqxdhDeploymentEnvironment.support_simulateQ_subset _ _ supported
  exact RegistrationNativeSecretWordLifecycleOwnerRoster.bundle_done setup wire index selected target publicPrekey
    owners env result valid original

private theorem finish_view (setup : Setup base KemSK) (index : Nat) (packet : Option registration.ResponsePacket)
    (owners : RegistrationNativePublicOwners.State source) (env : EnvState RegistrationServerRoleBackend.State)
    (owner : RegistrationNativePublicOwners.Owner source) (found : owners[index]? = some owner)
    (result : (RustM (Option Pqxdh.Bytes) × RegistrationNativePublicOwners.State source) × EnvState RegistrationServerRoleBackend.State)
    (supported : result ∈ support
      (((RegistrationNativeSecretWordOwners.finish (n := n) setup source index packet).run owners).run env)) :
    ∃ middle, middle ∈ support (((RegistrationNativeSecretWordBeaconCompiler.finish (n := n) setup source packet).run owner.view).run env) ∧
      result = ((middle.1.1, owners.set index { owner with view := middle.1.2 }), middle.2) := by
  simp only [RegistrationNativeSecretWordOwners.finish, StateT.run, found, support_map] at supported
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
      (((RegistrationNativeSecretWordOwners.finish (n := n) setup source target packet).run owners).run env)) :
    Done index result.1.2 := by
  cases found : owners[target]? with
  | none =>
      simp only [RegistrationNativeSecretWordOwners.finish, StateT.run, found, mem_support_pure_iff] at supported
      cases supported
      exact valid
  | some owner =>
      obtain ⟨middle, reached, rfl⟩ := finish_view setup target packet owners env owner found result supported
      by_cases same : index = target
      · subst target
        obtain ⟨old, oldAt, terminal⟩ := valid
        have equal : old = owner := Option.some.inj (oldAt.symm.trans found)
        subst old
        have kept := RegistrationNativeSecretWordOwnerCreditFinish.finish_terminal setup packet owner.view env middle terminal reached
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
      (((RegistrationNativeSecretWordOwners.finish (n := n) setup source index packet).run owners).run env)) :
    Done index result.1.2 := by
  obtain ⟨middle, reached, rfl⟩ := finish_view setup index packet owners env owner found result supported
  have terminal := RegistrationNativeSecretWordOwnerCreditFinish.finish_consumes setup packet owner.view env
    pending oneTime aborted sent moved middle reached
  exact ⟨{ owner with view := middle.1.2 }, List.getElem?_set_self (List.getElem?_eq_some_iff.mp found).1, terminal⟩

end BeaconcryptCore.Computational.RegistrationNativeSecretWordOwnerCreditRoster
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordOwnerCreditRoster.create_done' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordOwnerCreditRoster.create_done
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordOwnerCreditRoster.bundle_done' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordOwnerCreditRoster.bundle_done
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordOwnerCreditRoster.finish_done' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordOwnerCreditRoster.finish_done
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordOwnerCreditRoster.finish_consumes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordOwnerCreditRoster.finish_consumes
