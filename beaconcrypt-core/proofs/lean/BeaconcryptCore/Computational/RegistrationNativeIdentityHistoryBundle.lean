-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityHistoryOutgoing

/-! Actual whole bundle execution keeps the public native owner histories synchronized with the indexed joint source. Retries, reused supplied one-time coins, optional signing and encoder failures retain the reached signing attempts. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityHistoryBundle
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeIdentityFrontend (Owner)
open RegistrationNativeIdentityHistoryInvariant
open RegistrationNativeIdentitySourceSimulation (NewState runNew)
variable {ι KemSK Auxiliary : Type} {base : OracleSpec ι} {n : Nat}
variable {source : RegistrationNativeMldsa.Source}

theorem next_preserves (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (index : Nat) (owner : Owner source)
    (oneTime : PqxdhJointGapDh.ScalarBytes) (reply : RustM (RegistrationBeaconInitExecutor.Result Pqxdh.Bytes)) :
    Preserves (n := n) (Auxiliary := Auxiliary) setup checks representation created index owner.identity.handle
      (RegistrationNativeIdentityBundleSource.next index owner oneTime reply) := by
  cases reply with
  | fail error | div => exact pure_preserves setup checks representation created index owner.identity.handle _
  | ok result => cases result with
    | Err error => exact pure_preserves setup checks representation created index owner.identity.handle _
    | Ok published =>
        exact bind_preserves setup checks representation created index owner.identity.handle _ _
          (phase_preserves setup checks representation created index owner.identity.handle index _)
          (fun _ => bind_preserves setup checks representation created index owner.identity.handle _ _
            (RegistrationNativeIdentityHistoryOutgoing.effect_preserves setup checks representation created index owner.identity.handle _)
            (fun _ => pure_preserves setup checks representation created index owner.identity.handle _))

theorem bundled_preserves (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (wire : RegistrationNativeWire.Wire)
    (index : Nat) (owner : Owner source) (oneTime : PqxdhJointGapDh.ScalarBytes) :
    Preserves (n := n) (Auxiliary := Auxiliary) setup checks representation created index owner.identity.handle
      (RegistrationNativeIdentityBundleSource.bundled setup wire index owner oneTime) :=
  bind_preserves setup checks representation created index owner.identity.handle _ _
    (RegistrationNativeIdentityHistoryOutgoing.init_preserves setup checks representation created wire index owner oneTime)
    (next_preserves setup checks representation created index owner oneTime)

theorem start_preserves (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (wire : RegistrationNativeWire.Wire)
    (index : Nat) (owner : Owner source) :
    Preserves (n := n) (Auxiliary := Auxiliary) setup checks representation created index owner.identity.handle
      (RegistrationNativeIdentityBundleDispatch.start setup wire index owner) := by
  cases phase : owner.phase with
  | fresh =>
      simp only [RegistrationNativeIdentityBundleDispatch.start, phase]
      exact bind_preserves setup checks representation created index owner.identity.handle _ _
        (RegistrationNativeIdentityHistoryOutgoing.sample_preserves setup checks representation created index owner.identity.handle _)
        (bundled_preserves setup checks representation created wire index owner)
  | freshWithCoins scalar =>
      simpa only [RegistrationNativeIdentityBundleDispatch.start, phase, pure_bind] using
        bundled_preserves setup checks representation created wire index owner scalar
  | initSent pending scalar | established completed | aborted aborted =>
      simpa only [RegistrationNativeIdentityBundleDispatch.start, phase] using
        (pure_preserves (n := n) (Auxiliary := Auxiliary) (source := source) setup checks representation created index owner.identity.handle
          (.ok none : RustM (Option Pqxdh.Bytes)))

/-- Generated ownership, distinct handles and exact signed-message synchronization survive the complete actual bundle operation. -/
theorem bundle_holds (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (wire : RegistrationNativeWire.Wire) (index : Nat)
    (before : NewState n KemSK Auxiliary source) (result : RustM (Option Pqxdh.Bytes) × NewState n KemSK Auxiliary source)
    (prior : Holds setup.joint before.2.identities before.1.1)
    (supported : result ∈ support (runNew setup checks representation created
      (RegistrationNativeIdentityFrontend.bundle setup source wire index) before)) :
    Holds setup.joint result.2.2.identities result.2.1.1 := by
  cases found : before.1.1[index]? with
  | none =>
      simp only [runNew, RegistrationNativeIdentityFrontend.bundle, StateT.run_bind, StateT.run_get,
        pure_bind, found, StateT.run_pure, simulateQ_pure, map_pure, mem_support_pure_iff] at supported
      cases supported
      exact prior
  | some owner =>
      have same : runNew setup checks representation created (RegistrationNativeIdentityFrontend.bundle setup source wire index) before =
          runNew setup checks representation created (RegistrationNativeIdentityBundleDispatch.start setup wire index owner) before := by
        unfold runNew
        rw [RegistrationNativeIdentityBundleDispatch.new_run setup wire index owner before.1.1 found before.1.2]
      rw [same] at supported
      apply (start_preserves setup checks representation created wire index owner before result ⟨prior, ?_⟩ supported).1
      simp only [At, RegistrationNativeIdentityHistorySync.handles, List.getElem?_map, found, Option.map_some]

end BeaconcryptCore.Computational.RegistrationNativeIdentityHistoryBundle

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityHistoryBundle.next_preserves' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityHistoryBundle.next_preserves

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityHistoryBundle.bundled_preserves' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityHistoryBundle.bundled_preserves

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityHistoryBundle.start_preserves' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityHistoryBundle.start_preserves

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityHistoryBundle.bundle_holds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityHistoryBundle.bundle_holds
