-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformResponseOrigin
import BeaconcryptCore.Computational.RegistrationNativePlatformHashReceipt
import BeaconcryptCore.Computational.RegistrationNativePlatformExperiment

/-! Actual corrected successful Beacon finish supplies its mandatory accepted pinned response trial at the actual returned shared cache, retaining assigned-ID install and all outer platform coordinates. No prior unsigned issuance or security conclusion is assumed. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformResponseAccepted
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeBeaconFrontend (M Owner)
open RegistrationNativeMldsaShared (Local lower)
variable {n : Nat} {E Platform Value ι KemSK : Type} {base : OracleSpec ι}
variable {source : RegistrationNativeMldsa.Source}
variable [primitive : BeaconcryptCore.Refinement.AdapterSealPrimitive.Operations]
omit primitive in
private theorem source_lower (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (work : M n KemSK source RegistrationServerRoleBackend.State Value)
    (before : RegistrationNativeExperiment.State n KemSK source) :
    (RegistrationNativeExperiment.beacon setup checks representation created work).run before =
      Prod.map id RegistrationNativeMldsaShared.close <$> (lower setup checks representation created work).run
        (before.beacons, (RegistrationWorldAgreementCompiler.erase before.server.world, before)) := by
  simp only [RegistrationNativeExperiment.beacon, lower, StateT.run,
    bind_pure_comp, Functor.map_map, Prod.map, id_eq, RegistrationNativeMldsaShared.close]

theorem typed
    (coins : QueryImpl unifSpec (StateT Platform ProbComp))
    (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (credential : RegistrationNativeMldsa.Credential source)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (reserveRegistration reservePeer : StateT Platform ProbComp Bool) (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (BeaconcryptCore.Refinement.AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (index : Nat) (owner : Owner source) (pending : registration.BeaconPending)
    (oneTime : PqxdhJointGapDh.ScalarBytes) (packet : registration.ResponsePacket)
    (before after : RegistrationNativeExperiment.State n KemSK source) (previous next : Platform) (application : Pqxdh.Bytes)
    (selected : before.beacons[index]? = some owner) (phase : owner.phase = .initSent pending oneTime)
    (supported : ((.ok (some application), after), next) ∈ support
      (((RegistrationNativePlatformExperiment.handler coins setup checks wire route representation created source credential view failure allocation
        reserveRegistration reservePeer erased helper writer (.inr (.finish index (some packet)))).run before).run previous))
 :
    MldsaTranscriptAuth.Accepted (MldsaSharedAuthentication.cacheHash after.server.world.world.1.primitive.2) source.verify
      (RegistrationResponseExecutor.trial true pending packet
        (RegistrationSigningShared.historyFor (PqxdhRefinement.absBytes pending.binding.server_pin.public_key)
          (RegistrationNativeMldsaShared.nativeProject before))) := by
  have native : (.ok (some application), after) ∈ support
      ((RegistrationNativeExperiment.beacon setup checks representation created
        (RegistrationNativePlatformBeaconFinish.finish setup source wire index (some packet))).run before) :=
    RegistrationNativePlatformHashReceipt.native_support coins _ _ previous next supported
  rw [source_lower, support_map] at native
  obtain ⟨reached, possible, same⟩ := native
  have outcome : reached.1 = .ok (some application) := congrArg Prod.fst same
  obtain ⟨other, otherPending, otherTime, otherPacket, found, stage, packetEq, accepted⟩ := RegistrationNativePlatformResponseOrigin.accepted setup checks representation created wire
    index (some packet) (before.beacons, (RegistrationWorldAgreementCompiler.erase before.server.world, before)) reached.2 application
    (outcome ▸ possible) true rfl
  have ownerEq : other = owner := Option.some.inj (found.symm.trans selected)
  subst other
  have phases := stage.symm.trans phase
  cases phases
  cases Option.some.inj packetEq
  have cacheEq : (RegistrationNativeMldsaShared.project reached.2).2 = after.server.world.world.1.primitive.2 :=
    congrArg (fun value : RustM (Option Pqxdh.Bytes) × RegistrationNativeExperiment.State n KemSK source => value.2.server.world.world.1.primitive.2) same
  have summaryEq : RegistrationNativeMldsaShared.project (before.beacons, (RegistrationWorldAgreementCompiler.erase before.server.world, before)) =
      RegistrationNativeMldsaShared.nativeProject before := rfl
  rw [summaryEq, cacheEq] at accepted
  exact accepted

end BeaconcryptCore.Computational.RegistrationNativePlatformResponseAccepted

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformResponseAccepted.typed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformResponseAccepted.typed
