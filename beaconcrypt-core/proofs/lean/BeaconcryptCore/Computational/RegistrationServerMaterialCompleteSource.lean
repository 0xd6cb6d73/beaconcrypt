-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationServerMaterialOccupancySource

/-! The actual complete-message preflight and occupancy request precede the native current-pin/reservation gate and material service. Restoring the private root changes no allocator/preflight decision and retains the entire reached semantic World, including every failed completion. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationServerMaterialCompleteSource
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationServerMaterialSourceState (State close project restore nativeView service)
variable {n : Nat} {ι KemSK : Type} {base : OracleSpec ι}

noncomputable def complete (wire : RegistrationNativeWire.Wire) (reserve : Bool)
    (ready : RegistrationServerReferenceRoot.Ready) (application : Slice U8) :
    StateT RegistrationServerMaterialFrontend.State (OracleComp (RegistrationServerMaterialFrontend.Spec n))
      RegistrationServerMaterialFrontend.Result := fun before =>
  match peer.begin_completion_lookup before.control before.pin (RegistrationServerMaterialFrontend.token ready) application with
  | .fail error => pure (.fail error, before)
  | .div => pure (.div, before)
  | .ok (.Err _) => pure (.ok none, before)
  | .ok (.Ok lookup) =>
      if RegistrationServerSdkSource.preflight application lookup.key_id then do
        let occupied ← RegistrationServerMaterialFrontend.effect (.inr (.peerPresent lookup.key_id))
        (RegistrationServerMaterialOccupancySource.after wire reserve before.control lookup ready.reference occupied).run before
      else pure (.ok none, before)

/-- The finite normalized controller is the literal public frontend, including all intermediate native lookup results. -/
theorem literal (wire : RegistrationNativeWire.Wire) (reserve : Bool)
    (ready : RegistrationServerReferenceRoot.Ready) (application : Slice U8) :
    RegistrationServerMaterialFrontend.complete (n := n) wire reserve ready application = complete wire reserve ready application := by
  funext before
  cases looked : peer.begin_completion_lookup before.control before.pin (RegistrationServerMaterialFrontend.token ready) application with
  | fail error => simp only [RegistrationServerMaterialFrontend.complete, complete, looked]
  | div => simp only [RegistrationServerMaterialFrontend.complete, complete, looked]
  | ok answer =>
      cases answer with
      | Err previous => simp only [RegistrationServerMaterialFrontend.complete, complete, looked]
      | Ok lookup =>
          simp only [RegistrationServerMaterialFrontend.complete, complete, looked, peer.CompletionLookup.request]
          split
          · apply bind_congr
            intro occupied
            cases resumed : lookup.resume occupied with
            | fail error =>
                simp only [RegistrationServerMaterialOccupancySource.after, resumed]
                rfl
            | div =>
                simp only [RegistrationServerMaterialOccupancySource.after, resumed]
                rfl
            | ok result =>
                cases result with
                | Err previous =>
                    simp only [RegistrationServerMaterialOccupancySource.after, resumed]
                    rfl
                | Ok initial =>
                    cases reserve <;>
                      simp only [RegistrationServerMaterialOccupancySource.after, resumed,
                        RawCtxMaterialInterpretation.rust_map_ok, RegistrationPublicationKernelErasure.mapOk,
                        RegistrationServerMaterialOccupancySource.continuation, Bool.false_eq_true, ite_true, ite_false,
                        RegistrationServerMaterialAdmittedSource.admitted, StateT.run_bind, StateT.run_lift, StateT.run_pure,
                        bind_pure_comp, bind_map_left]
          · rfl

private theorem occupancy (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (roots : RegistrationServerReferenceRestore.Roots) (keyId : U64) (before : State n) :
    (close setup.source wire.frameWrite sign roots
      (StateT.lift (RegistrationServerMaterialFrontend.effect (.inr (.peerPresent keyId))))).run before =
      (fun result => (result.1, (before.1, { before.2 with world := (result.2, before.2.world.2) }))) <$>
        (PqxdhRecordLiftWorld.effects (.inr (.peerPresent keyId))).run before.2.world.1 := by
  rw [RegistrationServerMaterialSourceLift.lift_run]
  simp only [RegistrationServerMaterialFrontend.effect, simulateQ_spec_query, service,
    RegistrationServerKnownStageWorldSource.common, RegistrationServerPublicationWorldCompiler.effect,
    StateT.run, Functor.map_map]

/-- Real occupancy is interpreted before all current-pin/reservation/material callbacks, on the original full source state. -/
theorem native (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (roots : RegistrationServerReferenceRestore.Roots) (ready : RegistrationServerReferenceRoot.Ready)
    (application : Slice U8) (before : State n) :
    Prod.map id (project roots) <$>
      (close setup.source wire.frameWrite sign roots
        (RegistrationServerMaterialFrontend.complete wire checks.reservePeer ready application)).run before =
      Prod.map id nativeView <$>
        (RegistrationServerSdkSource.complete setup (RegistrationNativeWire.ledgerCodec wire) checks sign wire.encodeResponse
          (RegistrationServerReferenceRestore.token roots ready) application).run (restore roots before) := by
  rw [literal]
  simp only [complete, close, StateT.run, RegistrationServerSdkSource.complete,
    restore, RegistrationServerReferenceRestore.restore, RegistrationServerReferenceRestore.token]
  rw [RegistrationServerReferenceSourceLookup.begin_root]
  cases looked : peer.begin_completion_lookup before.1.control before.1.pin (RegistrationServerMaterialFrontend.token ready) application with
  | fail error =>
      rfl
  | div =>
      rfl
  | ok answer =>
      cases answer with
      | Err previous =>
          simp only [RawCtxMaterialInterpretation.rust_map_ok, RegistrationPublicationKernelErasure.mapOk]
          rfl
      | Ok lookup =>
          simp only [RawCtxMaterialInterpretation.rust_map_ok, RegistrationPublicationKernelErasure.mapOk,
            peer.CompletionLookup.request,
            RegistrationServerReferenceSourceLookup.withRoot]
          by_cases preflight : RegistrationServerSdkSource.preflight application lookup.key_id = true
          · simp only [preflight, ite_true]
            change Prod.map id (project roots) <$>
              (close setup.source wire.frameWrite sign roots (do
                let occupied ← StateT.lift (RegistrationServerMaterialFrontend.effect (.inr (.peerPresent lookup.key_id)))
                RegistrationServerMaterialOccupancySource.after wire checks.reservePeer before.1.control lookup ready.reference occupied)).run before = _
            rw [RegistrationServerMaterialSourceLift.bind_run, occupancy, map_bind, bind_map_left]
            simp only [RegistrationServerSdkSource.world, RegistrationWorldServerCompletion.capability,
              StateT.run, bind_map_left, map_bind]
            apply bind_congr
            rintro ⟨occupied, world⟩
            have source := RegistrationServerMaterialOccupancySource.native setup checks wire sign roots before.1.control
              lookup ready.reference occupied (before.1, { before.2 with world := (world, before.2.world.2) })
            simp only [StateT.run] at source
            simpa only [restore, RegistrationServerReferenceRestore.restore, RegistrationServerReferenceSourceLookup.withRoot] using source
          · have refused : RegistrationServerSdkSource.preflight application lookup.key_id = false := Bool.eq_false_iff.mpr preflight
            simp only [refused, Bool.false_eq_true, ite_false, simulateQ_pure,
              StateT.monad_pure_def, StateT.pure, map_pure]
            rfl

end BeaconcryptCore.Computational.RegistrationServerMaterialCompleteSource

/-- info: 'BeaconcryptCore.Computational.RegistrationServerMaterialCompleteSource.literal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationServerMaterialCompleteSource.literal
/-- info: 'BeaconcryptCore.Computational.RegistrationServerMaterialCompleteSource.native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationServerMaterialCompleteSource.native
