-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationServerMaterialAdmittedSource

/-! Actual current-pin/occupancy and peer-reservation decisions precede material demand. Private root restoration changes only the source initializer's consumed KDF input; the public gate and every refusal are the native ones. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationServerMaterialOccupancySource
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationPublicationKernelErasure (mapOk)
open RegistrationServerMaterialSourceState (State close project restore nativeView)
variable {n : Nat} {ι KemSK : Type} {base : OracleSpec ι}

noncomputable def continuation (wire : RegistrationNativeWire.Wire) (reserve : Bool) (control : pqxdh.ServerState)
    (message : RegistrationNativeRelatedFamily.Message) :
    RustM (core.result.Result RegistrationBoundKeySchedule.PublicInitial pqxdh.ServerState) →
      StateT RegistrationServerMaterialFrontend.State (OracleComp (RegistrationServerMaterialFrontend.Spec n))
        RegistrationServerMaterialFrontend.Result
  | .fail error => pure (.fail error)
  | .div => pure .div
  | .ok (.Err _) => pure (.ok none)
  | .ok (.Ok initial) =>
      if reserve then RegistrationServerMaterialAdmittedSource.admitted wire control initial message
      else pure (.ok none)

noncomputable def after (wire : RegistrationNativeWire.Wire) (reserve : Bool) (control : pqxdh.ServerState)
    (lookup : peer.CompletionLookup) (message : RegistrationNativeRelatedFamily.Message) (occupied : Bool) :=
  continuation (n := n) wire reserve control message
    (mapOk RegistrationBoundKeySchedule.publicInitial <$> lookup.resume occupied)

/-- The actual native lookup supplies the public gate and root-role receipt needed by the real material service; failed reservation reaches no service. -/
theorem native (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (roots : RegistrationServerReferenceRestore.Roots) (control : pqxdh.ServerState)
    (lookup : peer.CompletionLookup) (message : RegistrationNativeRelatedFamily.Message)
    (occupied : Bool) (before : State n) :
    Prod.map id (project roots) <$>
      (close setup.source wire.frameWrite sign roots (after wire checks.reservePeer control lookup message occupied)).run before =
      Prod.map id nativeView <$>
        (RegistrationServerSdkSource.afterOccupancy setup (RegistrationNativeWire.ledgerCodec wire) checks sign wire.encodeResponse
          control (RegistrationServerReferenceSourceLookup.withRoot lookup (roots message)) occupied).run (restore roots before) := by
  unfold after
  rw [← RegistrationServerReferenceSourceLookup.resume_public lookup (roots message) occupied]
  cases actual : (RegistrationServerReferenceSourceLookup.withRoot lookup (roots message)).resume occupied with
  | fail error =>
      simp only [RegistrationServerSdkSource.afterOccupancy, actual]
      change Prod.map id (project roots) <$>
        (close setup.source wire.frameWrite sign roots (pure (RustM.fail error : RegistrationServerMaterialFrontend.Result))).run before = _
      rw [RegistrationServerMaterialSourceLift.pure_run]
      rfl
  | div =>
      simp only [RegistrationServerSdkSource.afterOccupancy, actual]
      change Prod.map id (project roots) <$>
        (close setup.source wire.frameWrite sign roots (pure (RustM.div : RegistrationServerMaterialFrontend.Result))).run before = _
      rw [RegistrationServerMaterialSourceLift.pure_run]
      rfl
  | ok result =>
      cases result with
      | Err previous =>
          simp only [RegistrationServerSdkSource.afterOccupancy, actual]
          change Prod.map id (project roots) <$>
            (close setup.source wire.frameWrite sign roots (pure (RustM.ok none : RegistrationServerMaterialFrontend.Result))).run before = _
          rw [RegistrationServerMaterialSourceLift.pure_run]
          rfl
      | Ok initial =>
          simp only [RawCtxMaterialInterpretation.rust_map_ok, mapOk, continuation,
            RegistrationServerSdkSource.afterOccupancy, actual]
          by_cases reserved : checks.reservePeer = true
          · simp only [reserved, ite_true]
            exact RegistrationServerMaterialAdmittedSource.native setup wire sign roots control initial message
              (RegistrationServerReferenceSourceLookup.resume_role lookup (roots message) occupied initial actual) before
          · have refused : checks.reservePeer = false := Bool.eq_false_iff.mpr reserved
            simp only [refused, Bool.false_eq_true, ite_false]
            rw [RegistrationServerMaterialSourceLift.pure_run]
            rfl

end BeaconcryptCore.Computational.RegistrationServerMaterialOccupancySource

/-- info: 'BeaconcryptCore.Computational.RegistrationServerMaterialOccupancySource.native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationServerMaterialOccupancySource.native
