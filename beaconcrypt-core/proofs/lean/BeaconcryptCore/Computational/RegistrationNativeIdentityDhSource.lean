-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentitySourceSimulation
import BeaconcryptCore.Computational.RegistrationNativeIdentityWorldServices

/-! The actual native local-identity DH getter is realized by the indexed joint service. Optional source failure is retained, its converted secret is never returned to the executable frontend, and the complete owner/environment/World frame is preserved. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityDhSource
open PqxdhServerAuthExperiment (Setup Checks)
open PqxdhJointIdentity
open RegistrationNativeIdentitySourceSimulation
open RegistrationNativeIdentityFrontend (Owner Ambient)
variable {ι KemSK Auxiliary : Type} {base : OracleSpec ι} {n : Nat}
variable {source : RegistrationNativeMldsa.Source}

def service (credential : RegistrationNativeIdentityInterface.Credential) (peer : PqxdhBeaconPhase2Preparation.Word32) :
    RegistrationNativeIdentityFrontend.M n KemSK Auxiliary source (core.option.Option PqxdhBeaconPhase2Preparation.Word32) :=
  StateT.lift (StateT.lift (RegistrationNativeIdentityCallbacks.dh (Ambient n KemSK) credential peer))

/-- The generated handle supplies precisely its source seed's optional static-DH reply. -/
theorem service_source (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (seeds : List IdentitySeed)
    (credential : RegistrationNativeIdentityInterface.Credential) (seed : IdentitySeed)
    (peer : PqxdhBeaconPhase2Preparation.Word32) (found : seeds[credential.handle]? = some seed) :
    Related (n := n) (Auxiliary := Auxiliary) (source := source) setup checks representation created seeds
      (service credential peer) (pure (RegistrationAgreementRoot.nativeOption
        ((setup.joint.staticDh seed (PqxdhPhase2GapDhSource.peer peer)).map PqxdhRootTableInitialization.rootArray))) := by
  intro before prior
  have present : before.2.identities.seeds[credential.handle]? = some seed := by rw [prior]; exact found
  simp only [runNew, service, StateT.run_lift, StateT.run_map, bind_pure_comp, simulateQ_map]
  rw [RegistrationNativeIdentityWorldServices.dh_source setup checks representation created credential seed peer before.2 present]
  simp only [runOld, StateT.run_pure, simulateQ_pure, map_pure, Prod.map_def, id_eq, view]

theorem service_keeps (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (credential : RegistrationNativeIdentityInterface.Credential) (peer : PqxdhBeaconPhase2Preparation.Word32) :
    Keeps (n := n) (Auxiliary := Auxiliary) (source := source) setup checks representation created (service credential peer) := by
  intro before result supported
  simp only [runNew, service, StateT.run_lift, StateT.run_map, bind_pure_comp,
    simulateQ_map, RegistrationNativeIdentityCallbacks.dh, bind_pure_comp,
    RegistrationNativeIdentityInterface.staticDh, simulateQ_spec_query] at supported
  rw [RegistrationNativeIdentityWorld.service_source] at supported
  simp only [map_pure, mem_support_pure_iff] at supported
  cases supported
  rfl

/-- The original native local-identity callback computes this same optional source value, with no extra primitive query or state change. -/
theorem original_local_dh (setup : Setup base KemSK) (owner : Owner source) (seed : IdentitySeed)
    (oneTime : PqxdhJointGapDh.ScalarBytes) (peer : PqxdhBeaconPhase2Preparation.Word32) :
    RegistrationNativeBeaconFrontend.primitive (n := n) (Auxiliary := Auxiliary) setup
      (RegistrationNativeIdentityFrontend.restore seed owner) oneTime (.dh ⟨.LocalIdentity, peer⟩) =
      pure (RegistrationAgreementRoot.nativeOption
        ((setup.joint.staticDh seed (PqxdhPhase2GapDhSource.peer peer)).map PqxdhRootTableInitialization.rootArray)) := by
  simp only [RegistrationNativeBeaconFrontend.primitive, RegistrationNativeKemInterface.beacon,
    RegistrationNativeKemInterface.other, simulateQ_spec_query, RegistrationNativeKemBackend.beaconOther,
    RegistrationNativeKemInterface.OtherRequest.primitive, RegistrationBeaconRoleBackend.native,
    RegistrationBeaconRoleBackend.localBackend, RegistrationNativeIdentityFrontend.restore,
    StateT.run, map_pure, StateT.monad_pure_def, RegistrationNativeBeaconFrontend.sample, simulateQ_pure]

/-- The executable local-identity getter is the literal original native callback after private source interpretation. -/
theorem local_dh_source (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (seeds : List IdentitySeed)
    (owner : Owner source) (seed : IdentitySeed) (oneTime : PqxdhJointGapDh.ScalarBytes)
    (peer : PqxdhBeaconPhase2Preparation.Word32) (found : seeds[owner.identity.handle]? = some seed) :
    Related (n := n) (Auxiliary := Auxiliary) setup checks representation created seeds
      (RegistrationNativeIdentityFrontend.primitive setup owner oneTime (.dh ⟨.LocalIdentity, peer⟩))
      (RegistrationNativeBeaconFrontend.primitive setup (RegistrationNativeIdentityFrontend.restore seed owner) oneTime (.dh ⟨.LocalIdentity, peer⟩)) := by
  rw [original_local_dh]
  exact service_source setup checks representation created seeds owner.identity seed peer found

end BeaconcryptCore.Computational.RegistrationNativeIdentityDhSource

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityDhSource.service_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityDhSource.service_source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityDhSource.service_keeps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityDhSource.service_keeps
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityDhSource.original_local_dh' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityDhSource.original_local_dh
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityDhSource.local_dh_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityDhSource.local_dh_source
