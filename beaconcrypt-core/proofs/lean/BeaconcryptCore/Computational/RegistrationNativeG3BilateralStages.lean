-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeG3CommonBeacon
import BeaconcryptCore.Computational.RegistrationNativeG3KnownWorldFrameCommonStages

/-! The concrete full stages couple Worlds that already differ in private seed/use bookkeeping and the named analysis counters. Known-stage bilateral non-read laws first align their semantic inputs. The actual cached unused hidden installation then supplies the same kernel, while the public continuation receives only material44 and a slot. Chronological signing receipts remain exact. Cache availability and unused-role receipts are local coupling conditions to be discharged by the global allocator and repeated-role event. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeG3BilateralStages
open RegistrationNativeG3Common (State handler)
open RegistrationNativeG3KnownWorldFrameCommon (view)
variable {n : Nat} {Encoded Value : Type}

/-- The semantic view absorbs the finer seed/use-only installation view without discarding any further signing receipt. -/
theorem absorb (before : State n) : view (RegistrationNativeG3Common.view before) = view before := rfl

private theorem map_installation (left right : ProbComp (Value × State n))
    (same : Prod.map id RegistrationNativeG3Common.view <$> left =
      Prod.map id RegistrationNativeG3Common.view <$> right) :
    Prod.map id view <$> left = Prod.map id view <$> right := by
  have mapped := congrArg (fun distribution => Prod.map id view <$> distribution) same
  simpa only [Functor.map_map, Function.comp_def, Prod.map_def, id_eq, absorb] using mapped

/-- An actual Server known108 stage and public hidden44 stage preserve the same complete semantic result from related input Worlds. -/
theorem server (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (encode : registration.SignedResponseView → core.option.Option Encoded)
    (control : pqxdh.ServerState) (slot : PqxdhRecordLiftInterface.Slot n)
    (initial : RegistrationBoundKeySchedule.PublicInitial) (material : PqxdhDeploymentHiddenLayout.Material)
    (seed : PqxdhRecordLiftSeed.Seed) (left right : State n) (related : view left = view right)
    (cached : right.2.seeds.1 slot = some seed) (unused : right.2.used slot .server = false) :
    Prod.map id view <$>
      (simulateQ (handler source writer sign) (RegistrationNativePairedServerService.knownStage encode control initial
        (PqxdhDeploymentHiddenLayout.joinOutput material seed))).run left =
      Prod.map id view <$>
        (simulateQ (handler source writer sign) (RegistrationNativePairedServerService.hiddenStage encode control initial
          ⟨slot, material⟩)).run right := by
  rw [RegistrationNativeG3KnownWorldFrameCommonStages.server_input source writer sign encode control initial _ left,
    related, ← RegistrationNativeG3KnownWorldFrameCommonStages.server_input source writer sign encode control initial _ right]
  have same := map_installation _ _ (RegistrationNativeG3CommonServer.stage source writer sign encode control slot initial material seed right cached unused)
  have split := RegistrationHiddenInstall.stage_split encode control slot initial material seed
  rw [split] at same
  exact same

/-- The actual sequence-one Beacon opening and successful whole consumed-kernel installation have the same bilateral known108/hidden44 law. -/
theorem beacon (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (owner : Nat) (sender : U64) (slot : PqxdhRecordLiftInterface.Slot n)
    (descriptor : RegistrationBeaconBoundSource.PublicAgreement)
    (material : PqxdhDeploymentHiddenLayout.Material) (seed : PqxdhRecordLiftSeed.Seed)
    (left right : State n) (related : view left = view right)
    (cached : right.2.seeds.1 slot = some seed) (unused : right.2.used slot .beacon = false) :
    Prod.map id view <$>
      (simulateQ (handler source writer sign) (RegistrationNativePairedBeaconService.knownStage source owner sender descriptor
        (PqxdhDeploymentHiddenLayout.joinOutput material seed))).run left =
      Prod.map id view <$>
        (simulateQ (handler source writer sign) (RegistrationNativePairedBeaconService.hiddenStage source owner sender descriptor
          ⟨slot, material⟩)).run right := by
  rw [RegistrationNativeG3KnownWorldFrameCommonStages.beacon_input source writer sign owner sender descriptor _ left,
    related, ← RegistrationNativeG3KnownWorldFrameCommonStages.beacon_input source writer sign owner sender descriptor _ right]
  have same := map_installation _ _ (RegistrationNativeG3CommonBeacon.stage source writer sign owner sender slot descriptor material seed right cached unused)
  rw [RegistrationNativePairedBeaconService.hidden_split source owner sender slot descriptor material seed] at same
  exact same

end BeaconcryptCore.Computational.RegistrationNativeG3BilateralStages
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3BilateralStages.absorb' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3BilateralStages.absorb
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3BilateralStages.server' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3BilateralStages.server
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3BilateralStages.beacon' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3BilateralStages.beacon
