-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhDeploymentNative

/-! Empty send requests preserve the complete native deployment state, including inactive owners, missing peers and every primitive cache. These operational equations support admission substitution without a freshness or cryptographic premise. -/
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.CborAdmissionSend
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhJointIdentity (IdentitySeed)
open PqxdhDeploymentNative
variable {ι KemSK Reader Response : Type} {baseSpec : OracleSpec ι}

theorem beacon_empty (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (route : RawCtxServerRouting.SenderDecoder) (seed : IdentitySeed)
    (index : Nat) (state : State KemSK) :
    (handler setup codec checks route seed (.inr (.beaconSend index []))).run state =
      pure (none, state) := by
  simp only [handler, beaconStep, StateT.run]
  cases lookup : state.native.owners[index]?
  case some owner =>
    obtain ⟨bound, atIndex⟩ := List.getElem_of_getElem? lookup
    simp only [RawCtxBeaconLifecycle.beaconImpl]
    cases phase : owner.beacon.phase
    case established control associatedData kernel =>
      simp only [RawCtxMixedOwner.ownerImpl, StateT.run, RawCtxSourceSend.sendOwner,
        List.isEmpty_nil, ite_true, simulateQ_pure, pure_bind]
      simp only [logged_pure, record, PqxdhRegistrationSchedule.onShared,
        PqxdhServerAuthNative.nativeCtx, simulateQ_pure, StateT.run_pure, map_pure, pure_bind]
      simp only [RawCtxBeaconLifecycle.reinstall, RawCtxBeaconLifecycle.selected, ← phase,
        produce, List.map_nil, List.append_nil, Function.update_eq_self]
      simp only [← atIndex, List.set_getElem_self bound]
    all_goals simp only [RawCtxBeaconLifecycle.rejected, logged_pure, record,
      PqxdhRegistrationSchedule.onShared, PqxdhServerAuthNative.nativeCtx,
      simulateQ_pure, StateT.run_pure, map_pure, pure_bind, produce,
      List.map_nil, List.append_nil, Function.update_eq_self, ← atIndex, List.set_getElem_self bound]
  case none => rfl

theorem server_empty (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (route : RawCtxServerRouting.SenderDecoder) (seed : IdentitySeed)
    (keyId : Std.U64) (state : State KemSK) :
    (handler setup codec checks route seed (.inr (.serverSend keyId []))).run state =
      pure (none, state) := by
  cases selected : state.native.shared.2.server.server.peers keyId
  case some peer =>
    simp only [handler, serverStep, StateT.run, RawCtxServerMixed.serverImpl,
      RawCtxServerMixed.sendServer, RawCtxServerSend.sendServer, serverView,
      RawCtxServerRouting.peerAssociatedData, selected]
    simp only [Option.bind_eq_bind, Option.bind_some, Option.pure_def,
      RawCtxSourceSend.sendOwner, List.isEmpty_nil, ite_true, simulateQ_pure, pure_bind]
    simp only [RawCtxServerRouting.selectedOwner,
      RawCtxServerRouting.putPeer_entry _ _ _ selected, logged_pure, record,
      PqxdhRegistrationSchedule.onShared, PqxdhServerAuthNative.nativeCtx,
      simulateQ_pure, StateT.run_pure, map_pure, pure_bind, withServer, produce,
      List.map_nil, List.append_nil]
  case none =>
    simp only [handler, serverStep, StateT.run, RawCtxServerMixed.serverImpl,
      RawCtxServerMixed.sendServer, RawCtxServerSend.sendServer, serverView,
      RawCtxServerRouting.peerAssociatedData, selected, Option.bind_eq_bind, Option.bind_none,
      simulateQ_pure, logged_pure, record, PqxdhRegistrationSchedule.onShared,
      PqxdhServerAuthNative.nativeCtx, withServer, produce]
    simp only [StateT.monad_pure_def, StateT.pure, map_pure, pure_bind,
      List.map_nil, List.append_nil]

end BeaconcryptCore.Computational.CborAdmissionSend

/-- info: 'BeaconcryptCore.Computational.CborAdmissionSend.beacon_empty' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborAdmissionSend.beacon_empty
/-- info: 'BeaconcryptCore.Computational.CborAdmissionSend.server_empty' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborAdmissionSend.server_empty
