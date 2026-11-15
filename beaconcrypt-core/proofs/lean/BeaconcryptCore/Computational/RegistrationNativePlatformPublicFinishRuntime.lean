-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicFinishClosed
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicFinishEmbedding
import BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryScalarEager
/-! Actual corrected public finishing restores the literal final ordinary runtime callback on the same reached Native and P. The private selected scalar and root memo remain interpreter data; the assigned-ID source opening and installation retain every prior record marker. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicFinishRuntime
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativePlatformPublicSourceExecution (State execute)
open RegistrationNativePublicSourceState (roots restore project nativeView owners)
attribute [local irreducible] RegistrationNativePlatformBeaconFinish.finish
variable {n : Nat} {I KemSK Platform E : Type} {base : OracleSpec I} {source : RegistrationNativeMldsa.Source}

/-- The literal corrected finish callback has its full source/native/P equation without an empty-marker premise. -/
theorem finish [primitive : BeaconcryptCore.Refinement.AdapterSealPrimitive.Operations]
    (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (credential : RegistrationNativeMldsa.Credential source)
    (selectedOwner selectedAccept : Nat) (scalar : PqxdhJointGapDh.ScalarBytes)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
    (reserveFrame : Nat → StateT Platform ProbComp (core.result.Result Unit E)) (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (BeaconcryptCore.Refinement.AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (index : Nat) (packet : Option registration.ResponsePacket) (before : State n KemSK Platform source)
    (coherent : RegistrationNativeBeaconCoherence.Holds (owners scalar before.1.1.beacons)) :
    (fun result => ((result.1, project (roots setup created.seed scalar) scalar result.2.1.1 result.2.2), result.2.1.2)) <$>
      (execute setup (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) route (RegistrationNativeMldsa.owned source credential) created.seed scalar
        (RegistrationNativePlatformPublicFrontend.handler setup checks (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) source
          (RegistrationNativeMldsa.owned source credential) selectedOwner selectedAccept (setup.dh.publicKey scalar)
          view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer (.inr (.finish index packet)))).run before =
      (fun result => ((result.1.1, nativeView result.1.2), result.2)) <$>
        ((RegistrationNativePlatformOrdinaryScalarEager.handler setup checks wire route representation created source credential view failure allocation
          reserveRegistration reservePeer reserveFrame erased helper writer selectedOwner scalar (.inr (.finish index packet))).run
          (restore (roots setup created.seed scalar) scalar before.1.1 before.2)).run before.1.2 := by
  change (fun result => ((result.1, project (roots setup created.seed scalar) scalar result.2.1.1 result.2.2), result.2.1.2)) <$>
    (execute setup (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) route (RegistrationNativeMldsa.owned source credential) created.seed scalar
      (RegistrationNativePlatformPublicFrontend.executeLocal (RegistrationNativePlatformPublicFrontend.beacon
        (RegistrationNativePlatformPublicFrontend.finish setup (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) source index packet)))).run before = _
  rw [RegistrationNativePlatformPublicFinishEmbedding.body,
    RegistrationNativePlatformPublicSourceOrdinaryLens.old_source]
  have actual := RegistrationNativePlatformPublicFinishClosed.finish_source setup checks
    (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) route representation created scalar credential
    (roots setup created.seed scalar) index packet (before.1.1, before.2) coherent
  have mapped := congrArg (fun action => (fun result => ((result.1, result.2), before.1.2)) <$> action) actual
  simp only [Functor.map_map, Prod.map_def, id_eq] at mapped ⊢
  have branch : RegistrationNativePlatformOrdinaryScalarEager.handler (n := n) setup checks wire route representation created source credential view failure allocation
      reserveRegistration reservePeer reserveFrame erased helper writer selectedOwner scalar (.inr (.finish index packet)) =
      RegistrationNativePlatformExperiment.liftNative RegistrationNativePlatformMldsaProgram.coins
        (RegistrationNativeExperiment.beacon setup checks representation created
          (RegistrationNativePlatformBeaconFinish.finish setup source (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) index packet)) := rfl
  rw [branch]
  change _ = (fun result => ((result.1.1, nativeView result.1.2), result.2)) <$>
    (simulateQ RegistrationNativePlatformMldsaProgram.coins
      ((RegistrationNativeExperiment.beacon setup checks representation created
        (RegistrationNativePlatformBeaconFinish.finish setup source (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) index packet)).run
          (restore (roots setup created.seed scalar) scalar before.1.1 before.2))).run before.1.2
  rw [RegistrationNativePlatformMldsaProgram.lift_coins, StateT.run_lift]
  simpa only [bind_pure_comp, Functor.map_map] using mapped
end BeaconcryptCore.Computational.RegistrationNativePlatformPublicFinishRuntime

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicFinishRuntime.finish' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicFinishRuntime.finish
