-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPairedBeaconFinishSafe
/-! The corrected source finish is embedded into the actual new public frontend with the same opaque owner, optional scalar preparation and persistent platform state. Paired safety retains all owner writes and failure replies. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicFinishSafe
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
private theorem native_map_safe {V W : Type} (work : OracleComp (RegistrationNativePublicFrontend.Spec n KemSK) V)
    (observe : V → W) (safe : RegistrationNativePairedTrace.Safe work) : RegistrationNativePairedTrace.Safe (observe <$> work) := by
  rw [map_eq_bind_pure_comp]
  exact RegistrationNativePairedTrace.bind_safe _ _ safe (fun _ => RegistrationNativePairedTrace.pure_safe _)

private theorem owners_safe (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (index : Nat) (packet : Option registration.ResponsePacket)
    (owners : RegistrationNativePublicOwners.State source) (env : RegistrationServerReferenceCompiler.Environment)
    (before : Platform) :
    RegistrationNativePairedTrace.Safe (simulateQ RegistrationNativePlatformPublicCoinEmbedding.embed
      (simulateQ embedLocal ((((RegistrationNativePlatformPublicFrontend.finish (n := n) (KemSK := KemSK) setup wire source index packet).run owners).run env).run before))) := by
  simp only [RegistrationNativePlatformPublicFrontend.finish, StateT.run]
  cases found : owners[index]? with
  | none => exact RegistrationNativePairedTrace.pure_safe _
  | some owner =>
    dsimp only
    cases selectedScalar : owner.scalar with
    | none =>
      simp only [map_apply, simulateQ_map]
      rw [local_apply]
      simp only [Functor.map_map]
      apply native_map_safe
      exact RegistrationNativePlatformPairedBeaconFinishSafe.finish setup none wire packet owner.view env
    | some scalar =>
      simp only [map_apply, simulateQ_map]
      rw [local_apply]
      simp only [Functor.map_map]
      apply native_map_safe
      rw [← QueryImpl.simulateQ_compose]
      exact RegistrationNativePlatformPairedBeaconFinishSafe.finish setup (some scalar) wire packet owner.view env

/-- The literal corrected public finish callback is safe under the actual external-coin embedding, with complete returned frontend/platform state. -/
theorem finish (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (index : Nat) (packet : Option registration.ResponsePacket) (before : State source Platform) :
    RegistrationNativePairedTrace.Safe (simulateQ RegistrationNativePlatformPublicCoinEmbedding.embed
      ((executeLocal (beacon (RegistrationNativePlatformPublicFrontend.finish (n := n) (KemSK := KemSK) setup wire source index packet))).run before)) := by
  simp only [executeLocal, beacon, StateT.run, simulateQ_map]
  exact native_map_safe _ _ (owners_safe setup wire index packet before.1.beacons before.1.environment before.2)
end BeaconcryptCore.Computational.RegistrationNativePlatformPublicFinishSafe

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicFinishSafe.finish' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicFinishSafe.finish
