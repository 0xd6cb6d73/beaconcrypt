-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerBeaconFinishHandles
import BeaconcryptCore.Computational.RegistrationNativeHiddenAllocationOwners
/-! The corrected source finish is embedded into the actual new public frontend with the same opaque owner, optional scalar preparation and persistent platform state. Paired safety retains all owner writes and failure replies. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerBeaconTyped
open PqxdhServerAuthExperiment (Setup)
open RegistrationNativePlatformPublicFrontend
variable {n : Nat} {I KemSK Platform A : Type} {base : OracleSpec I} {source : RegistrationNativeMldsa.Source}

private theorem local_query (query : (RegistrationBeaconReferenceCompiler.Spec n KemSK).Domain) :
    simulateQ RegistrationNativePlatformPublicCoinEmbedding.embed
      (simulateQ embedLocal (localQuery false query)) = RegistrationNativePublicFrontend.liftLocal false query := by
  rcases query with message | (message | common) | kem
  · simp [localQuery, embedLocal, RegistrationNativePlatformPublicCoinEmbedding.embed, RegistrationNativePublicFrontend.liftLocal]
  · simp [localQuery, embedLocal, RegistrationNativePlatformPublicCoinEmbedding.embed, RegistrationNativePublicFrontend.liftLocal]
  · simp [localQuery, embedLocal, RegistrationNativePlatformPublicCoinEmbedding.embed, RegistrationNativePublicFrontend.liftLocal]
  · rcases kem with other | pool | key
    · simp [localQuery, RegistrationNativeKemRouting.route, embedLocal,
        RegistrationNativePlatformPublicCoinEmbedding.embed, RegistrationNativePublicFrontend.liftLocal,
        RegistrationNativePublicFrontend.liftRoutedKem]
    · simp [localQuery, RegistrationNativeKemRouting.route, embedLocal,
        RegistrationNativePlatformPublicCoinEmbedding.embed, RegistrationNativePublicFrontend.liftLocal,
        RegistrationNativePublicFrontend.liftRoutedKem]
    · simp [localQuery, RegistrationNativeKemRouting.route, embedLocal,
        RegistrationNativePlatformPublicCoinEmbedding.embed, RegistrationNativePublicFrontend.liftLocal,
        RegistrationNativePublicFrontend.liftRoutedKem]

private theorem local_run (work : OracleComp (RegistrationBeaconReferenceCompiler.Spec n KemSK) A) (before : Platform) :
    simulateQ RegistrationNativePlatformPublicCoinEmbedding.embed
      (simulateQ embedLocal ((simulateQ (localHandler false) work).run before)) =
      (fun value => (value, before)) <$> simulateQ (RegistrationNativePublicFrontend.liftLocal false) work := by
  induction work using OracleComp.inductionOn with
  | pure value => simp only [simulateQ_pure, StateT.run_pure, map_pure]
  | query_bind query next ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, localHandler, StateT.run_bind,
      StateT.run_lift, bind_pure_comp, bind_map_left, map_bind]
    rw [local_query]
    apply bind_congr
    intro reply
    exact ih reply

private theorem local_apply (work : OracleComp (RegistrationBeaconReferenceCompiler.Spec n KemSK) A) (before : Platform) :
    simulateQ RegistrationNativePlatformPublicCoinEmbedding.embed
      (simulateQ embedLocal ((simulateQ (localHandler false) work) before)) =
      (fun value => (value, before)) <$> simulateQ (RegistrationNativePublicFrontend.liftLocal false) work :=
  local_run work before

private theorem map_apply {S V W : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (change : V → W) (work : StateT S m V) (before : S) :
    (change <$> work) before = Prod.map change id <$> work before := StateT.run_map change work before
private def attachOwner (index : Nat) (owners : RegistrationNativePublicOwners.State source)
    (owner : RegistrationNativePublicOwners.Owner source) (before : Platform)
    (result : (RustM (Option Pqxdh.Bytes) × RegistrationBeaconReferenceCompiler.SelectedOwner source) × RegistrationServerReferenceCompiler.Environment) :=
  (((result.1.1,owners.set index {owner with view:=result.1.2}),result.2),before)

private theorem owners_source (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (index : Nat) (packet : Option registration.ResponsePacket)
    (owners : RegistrationNativePublicOwners.State source) (owner : RegistrationNativePublicOwners.Owner source)
    (found : owners[index]?=some owner) (env : RegistrationServerReferenceCompiler.Environment) (before : Platform) :
    simulateQ (RegistrationNativePlatformPublicCoinEmbedding.embed (n := n) (KemSK := KemSK))
      (simulateQ embedLocal ((((RegistrationNativePlatformPublicFrontend.finish (n := n) (KemSK := KemSK) setup wire source index packet).run owners).run env).run before)) =
    attachOwner index owners owner before <$>
      RegistrationNativePlatformPublicSlotBeaconFinishSafe.compile setup owner.scalar
        (RegistrationNativePlatformBeaconReferenceFinish.finish setup wire source packet) owner.view env := by
  simp only [RegistrationNativePlatformPublicFrontend.finish,StateT.run,found]
  cases selectedScalar : owner.scalar with
  | none =>
    simp only [map_apply,simulateQ_map]
    rw [local_apply]
    simp only [Functor.map_map]
    congr 1
    funext result
    simp only [attachOwner,Prod.map_def,id_eq,selectedScalar]
  | some scalar =>
    simp only [map_apply,simulateQ_map]
    rw [local_apply]
    simp only [Functor.map_map]
    rw [←QueryImpl.simulateQ_compose]
    congr 1
    funext result
    simp only [attachOwner,Prod.map_def,id_eq,selectedScalar]

/-- The literal public finish records precisely the queried physical owner on its own successful public application. The address premise is the actual allocation invariant. -/
theorem finish (role : PqxdhRecordLiftInterface.Role) (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (index : Nat) (packet : Option registration.ResponsePacket) (before : State source Platform)
    (indexed : RegistrationNativeHiddenAllocationOwners.Indexed before.1.beacons)
    (trace : List PqxdhDeploymentInterface.Handle)
    (result : (RustM (Option Pqxdh.Bytes) × State source Platform) × List PqxdhDeploymentInterface.Handle)
    (supported : result∈support ((simulateQ (RegistrationNativePlatformRecordPartnerSnapshotHandles.handler role)
      (simulateQ (RegistrationNativePlatformPublicCoinEmbedding.embed (n := n) (KemSK := KemSK))
        ((executeLocal (beacon (RegistrationNativePlatformPublicFrontend.finish (n := n) (KemSK := KemSK) setup wire source index packet))).run before))).run trace)) :
    result.2=trace++if role=.beacon ∧ RegistrationNativeInstallBeaconComplete.present result.1.1=true then [.owner index] else [] := by
  simp only [executeLocal,beacon,StateT.run,simulateQ_map] at supported
  cases found : before.1.beacons[index]? with
  | none =>
    simp only [RegistrationNativePlatformPublicFrontend.finish,found,map_apply] at supported
    subst result
    simp [RegistrationNativeInstallBeaconComplete.present]
  | some owner =>
    have actual := owners_source (n := n) setup wire index packet before.1.beacons owner found before.1.environment before.2
    simp only [StateT.run] at actual
    rw [actual] at supported
    simp only [simulateQ_map,map_apply,Functor.map_map,support_map] at supported
    obtain ⟨reached,called,equal⟩ := supported
    cases equal
    have counted := RegistrationNativePlatformRecordPartnerBeaconFinishHandles.finish role setup wire owner.scalar
      owner.view before.1.environment packet trace reached called
    have ownerIndex := indexed index owner found
    simpa only [attachOwner,Prod.map_def,id_eq,ownerIndex] using counted

end BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerBeaconTyped
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerBeaconTyped.finish' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerBeaconTyped.finish
