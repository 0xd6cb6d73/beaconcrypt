-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityFinishDispatch

/-! Actual owner lookup selects the generated identity receipt used by the complete bundle source correspondence. Public-key aliases do not merge generated indices. Every unselected owner, reached history, mutable environment and complete native context is retained. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityFinishRun
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeIdentitySourceSimulation
open RegistrationNativeIdentityFinishDispatch (start)
variable {ι KemSK Auxiliary : Type} {base : OracleSpec ι} {n : Nat}
variable {source : RegistrationNativeMldsa.Source}

/-- The whole actual finishing operation equals the original native source operation after private credential realization; all authentication/agreement/opening failures keep their reached effects. -/
theorem finish_source (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit)
    (wire : RegistrationNativeWire.Wire) (index : Nat) (packet : Option registration.ResponsePacket) (seeds : List PqxdhJointIdentity.IdentitySeed)
    (before : NewState n KemSK Auxiliary source) (prior : before.2.identities.seeds = seeds)
    (owned : RegistrationNativeIdentityRealization.Owned setup.joint before.2.identities before.1.1) :
    Prod.map id (view seeds) <$>
      runNew setup checks representation created (RegistrationNativeIdentityFrontend.finish setup source wire index packet) before =
      runOld setup checks representation created (RegistrationNativeBeaconFrontend.finish setup source wire index packet) (view seeds before) := by
  cases selected : before.1.1[index]? with
  | none =>
      simp only [runNew, runOld, RegistrationNativeIdentityFrontend.finish, RegistrationNativeBeaconFrontend.finish,
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
      have actual := RegistrationNativeIdentityFinishDispatch.start_source setup checks representation created seeds
        wire index current seed packet found before prior
      unfold runNew runOld
      rw [RegistrationNativeIdentityFinishDispatch.new_run setup wire index current before.1.1 selected before.1.2 packet,
        RegistrationNativeIdentityFinishDispatch.old_run setup wire index
          (RegistrationNativeIdentityFrontend.restore seed current) (view seeds before).1.1 nativeFound (view seeds before).1.2 packet]
      exact actual

/-- Complete actual finishing execution preserves the existing private identity prefix on every return path. -/
theorem finish_keeps (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit)
    (wire : RegistrationNativeWire.Wire) (index : Nat) (packet : Option registration.ResponsePacket) :
    Keeps (n := n) (Auxiliary := Auxiliary) (source := source) setup checks representation created
      (RegistrationNativeIdentityFrontend.finish setup source wire index packet) := by
  intro before result supported
  cases selected : before.1.1[index]? with
  | none =>
      simp only [runNew, RegistrationNativeIdentityFrontend.finish, StateT.run_bind, StateT.run_get,
        pure_bind, selected, StateT.run_pure, simulateQ_pure, map_pure, mem_support_pure_iff] at supported
      cases supported
      rfl
  | some current =>
      have same : runNew setup checks representation created
          (RegistrationNativeIdentityFrontend.finish setup source wire index packet) before =
          runNew setup checks representation created (start setup wire index current packet) before := by
        unfold runNew
        rw [RegistrationNativeIdentityFinishDispatch.new_run setup wire index current before.1.1 selected before.1.2 packet]
      rw [same] at supported
      exact RegistrationNativeIdentityFinishDispatch.start_keeps setup checks representation created wire index current packet before result supported

end BeaconcryptCore.Computational.RegistrationNativeIdentityFinishRun

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityFinishRun.finish_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityFinishRun.finish_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityFinishRun.finish_keeps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityFinishRun.finish_keeps
