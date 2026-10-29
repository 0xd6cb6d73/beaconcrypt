-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeG3CommonServer

/-! The actual Beacon first-open/common stage couples its consumed known kernel to the same cached unused hidden reference. Native opening failure, final admission, application, populated binding, signing receipts and the shared World are retained. Prefix cache/use facts and the supported canonical kernel are derived from the actual source program. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeG3CommonBeacon
open RegistrationNativeG3Common (State handler publication view)
variable {n : Nat} {Value : Type}

private theorem raw_lift (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (work : OracleComp RegistrationRawSealBridge.Spec Value) :
    simulateQ (handler (n := n) source writer sign) (simulateQ RegistrationNativePairedBeaconService.rawLift work) =
      simulateQ (publication source writer sign) (simulateQ RegistrationBoundPublication.rawLift work) := by
  rw [← QueryImpl.simulateQ_compose, ← QueryImpl.simulateQ_compose]
  congr 1

/-- Both complete actual Beacon stages agree on their native result, chronological receipts and every semantic World coordinate. -/
theorem stage (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (owner : Nat) (sender : U64) (slot : PqxdhRecordLiftInterface.Slot n)
    (descriptor : RegistrationBeaconBoundSource.PublicAgreement)
    (material : PqxdhDeploymentHiddenLayout.Material) (seed : PqxdhRecordLiftSeed.Seed)
    (before : State n) (cached : before.2.seeds.1 slot = some seed)
    (unused : before.2.used slot .beacon = false) :
    Prod.map id view <$>
      (simulateQ (handler source writer sign) (RegistrationNativePairedBeaconService.knownStage source owner sender descriptor
        (PqxdhDeploymentHiddenLayout.joinOutput material seed))).run before =
      Prod.map id view <$>
        (simulateQ (handler source writer sign) (RegistrationNativePairedBeaconService.privateHiddenStage source owner sender slot descriptor
          (PqxdhDeploymentHiddenLayout.joinOutput material seed))).run before := by
  simp only [RegistrationNativePairedBeaconService.knownStage, RegistrationNativePairedBeaconService.privateHiddenStage,
    simulateQ_bind, raw_lift, StateT.run_bind, map_bind]
  apply OracleComp.bind_congr_of_forall_mem_support
  intro reached supported
  have keeps := RegistrationNativeG3Common.publication_program_keeps source writer sign _ before reached supported
  have original : reached.1 ∈ support (RegistrationNativePairedBeaconService.program source descriptor
      (PqxdhDeploymentHiddenLayout.joinOutput material seed)) := by
    apply support_simulateQ_run'_subset (publication source writer sign ∘ₛ RegistrationBoundPublication.rawLift) _ before
    rw [StateT.run'_eq, support_map, QueryImpl.simulateQ_compose]
    exact ⟨reached, supported, rfl⟩
  have cachedAfter : reached.2.2.seeds.1 slot = some seed := by rw [keeps.1]; exact cached
  have unusedAfter : reached.2.2.used slot .beacon = false := by rw [keeps.2]; exact unused
  have suffix := RegistrationNativeG3BeaconInsertion.after_program source owner sender slot descriptor material seed
    reached.1 original reached.2.2 cachedAfter unusedAfter
  have retained := congrArg (fun distribution => (fun result => (result.1, (reached.2.1, result.2))) <$> distribution) suffix
  simpa only [RegistrationNativeG3Common.effect_lift, RegistrationNativeG3Common.effect_program,
    Functor.map_map, Prod.map_def, id_eq, view] using retained

end BeaconcryptCore.Computational.RegistrationNativeG3CommonBeacon
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3CommonBeacon.stage' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3CommonBeacon.stage
