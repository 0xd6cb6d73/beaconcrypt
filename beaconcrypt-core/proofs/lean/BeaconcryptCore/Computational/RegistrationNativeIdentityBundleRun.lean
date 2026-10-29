-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityBundleDispatch

/-! Actual owner lookup selects the generated identity receipt used by the complete bundle source correspondence. Public-key aliases do not merge generated indices. Every unselected owner, reached history, mutable environment and complete native context is retained. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityBundleRun
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeIdentitySourceSimulation
open RegistrationNativeIdentityBundleDispatch (start)
variable {ι KemSK Auxiliary : Type} {base : OracleSpec ι} {n : Nat}
variable {source : RegistrationNativeMldsa.Source}

/-- The whole actual bundle operation equals the original native source operation after private credential realization; all signing/publication failures keep their reached effects. -/
theorem bundle_source (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit)
    (wire : RegistrationNativeWire.Wire) (index : Nat) (seeds : List PqxdhJointIdentity.IdentitySeed)
    (before : NewState n KemSK Auxiliary source) (prior : before.2.identities.seeds = seeds)
    (owned : RegistrationNativeIdentityRealization.Owned setup.joint before.2.identities before.1.1) :
    Prod.map id (view seeds) <$>
      runNew setup checks representation created (RegistrationNativeIdentityFrontend.bundle setup source wire index) before =
      runOld setup checks representation created (RegistrationNativeBeaconFrontend.bundle setup source wire index) (view seeds before) := by
  cases selected : before.1.1[index]? with
  | none =>
      simp only [runNew, runOld, RegistrationNativeIdentityFrontend.bundle, RegistrationNativeBeaconFrontend.bundle,
        StateT.run_bind, StateT.run_get, pure_bind, view, RegistrationNativeIdentityRealization.owners,
        List.getElem?_map, selected, Option.map_none, StateT.run_pure, simulateQ_pure, map_pure,
        Prod.map_def, id_eq]
  | some current =>
      obtain ⟨seed, receipt⟩ := owned current (List.mem_of_getElem? selected)
      have found : seeds[current.identity.handle]? = some seed := by rw [← prior]; exact receipt.1
      have nativeOwner : RegistrationNativeIdentityRealization.owner ⟨seeds, []⟩ current =
          RegistrationNativeIdentityFrontend.restore seed current := by
        simp only [RegistrationNativeIdentityRealization.owner,
          RegistrationNativeIdentityRealization.seed_found ⟨seeds, []⟩ current.identity seed found]
      have nativeFound : (view seeds before).1.1[index]? =
          some (RegistrationNativeIdentityFrontend.restore seed current) := by
        simp only [view, RegistrationNativeIdentityRealization.owners, List.getElem?_map,
          selected, Option.map_some, nativeOwner]
      have actual := RegistrationNativeIdentityBundleDispatch.start_source setup checks representation created seeds
        wire index current seed found receipt.2 before prior
      unfold runNew runOld
      rw [RegistrationNativeIdentityBundleDispatch.new_run setup wire index current before.1.1 selected before.1.2,
        RegistrationNativeIdentityBundleDispatch.old_run setup wire index
          (RegistrationNativeIdentityFrontend.restore seed current) (view seeds before).1.1 nativeFound (view seeds before).1.2]
      exact actual

/-- Complete actual bundle execution preserves the existing private identity prefix on every return path. -/
theorem bundle_keeps (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit)
    (wire : RegistrationNativeWire.Wire) (index : Nat) :
    Keeps (n := n) (Auxiliary := Auxiliary) (source := source) setup checks representation created
      (RegistrationNativeIdentityFrontend.bundle setup source wire index) := by
  intro before result supported
  cases selected : before.1.1[index]? with
  | none =>
      simp only [runNew, RegistrationNativeIdentityFrontend.bundle, StateT.run_bind, StateT.run_get,
        pure_bind, selected, StateT.run_pure, simulateQ_pure, map_pure, mem_support_pure_iff] at supported
      cases supported
      rfl
  | some current =>
      have same : runNew setup checks representation created
          (RegistrationNativeIdentityFrontend.bundle setup source wire index) before =
          runNew setup checks representation created (start setup wire index current) before := by
        unfold runNew
        rw [RegistrationNativeIdentityBundleDispatch.new_run setup wire index current before.1.1 selected before.1.2]
      rw [same] at supported
      exact RegistrationNativeIdentityBundleDispatch.start_keeps setup checks representation created wire index current before result supported

end BeaconcryptCore.Computational.RegistrationNativeIdentityBundleRun

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityBundleRun.bundle_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityBundleRun.bundle_source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityBundleRun.bundle_keeps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityBundleRun.bundle_keeps
