-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeBeaconOpeningCosts
import BeaconcryptCore.Computational.RegistrationNativeCreateCosts

/-! The actual paired Beacon completion requests material only after preparation, runs its original first-record opening and then performs its one possible native installation. Failed openings and failed installations retain their literal result; the outer native abort is charged separately. -/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
namespace BeaconcryptCore.Computational.RegistrationNativeBeaconInstallCosts
open PqxdhRecordLiftInterface (EffectKind)
open RegistrationNativePrimitiveCosts (coinCost)
open RegistrationNativePublicationCosts (hashCost)
open RegistrationNativeCreateCosts (administrativeCost)
open PqxdhRecordLiftCtxProgramBounds (Weighted weighted_bind weighted_simulate)
open RegistrationNativeWeightedContext (query_bound map_bound)
open RegistrationNativePairedServerService (Common PublicSpec)
variable {n : Nat}

def commonCost (qSign : Nat) (kind : EffectKind) (query : (Common n).Domain) : Nat :=
  RegistrationNativeReferenceCosts.bill (KemSK := Unit) qSign 0 (.inr (.inl (.inr query))) kind

def publicCost (qSign : Nat) (kind : EffectKind) (query : (PublicSpec n).Domain) : Nat :=
  RegistrationNativeReferenceCosts.bill (KemSK := Unit) qSign 0 (.inr (.inl query)) kind

def stageBill (kind : EffectKind) := hashCost kind + administrativeCost kind

def admittedBill (kind : EffectKind) := coinCost 108 kind + stageBill kind

set_option backward.isDefEq.respectTransparency false in
private theorem after_bound (qSign : Nat) (owner : Nat) (sender : U64)
    (select : registration.CompletedBeacon → PqxdhRecordLiftInterface.KernelRef n)
    (result : RustM RegistrationBeaconRecordExecutor.Result) (kind : EffectKind) :
    Weighted (commonCost qSign kind)
      (simulateQ RegistrationHiddenInstall.effectLift (RegistrationNativePairedBeaconService.after owner sender select result))
      (administrativeCost kind) := by
  cases result with
  | fail error => trivial
  | div => trivial
  | ok result => cases result with
    | Err error => trivial
    | Ok completed =>
        simp only [RegistrationNativePairedBeaconService.after, bind_pure_comp, simulateQ_map, simulateQ_spec_query,
          RegistrationHiddenInstall.effectLift]
        exact map_bound _ _ _ _ (by cases kind <;> exact query_bound _ _)

private theorem raw_bound (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (descriptor : RegistrationBeaconBoundSource.PublicAgreement) (output : PqxdhServerAuthKeySchedule.Output)
    (qSign : Nat) (kind : EffectKind) :
    Weighted (commonCost (n := n) qSign kind)
      (simulateQ RegistrationNativePairedBeaconService.rawLift (RegistrationNativePairedBeaconService.program source descriptor output))
      (hashCost kind) := by
  apply weighted_simulate (RegistrationNativeBeaconOpeningCosts.rawCost kind) _ _ _ _
    (RegistrationNativeBeaconOpeningCosts.program_bound source descriptor output kind)
  intro query
  exact query_bound _ _

private theorem known_bound (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (owner : Nat) (sender : U64) (descriptor : RegistrationBeaconBoundSource.PublicAgreement)
    (output : PqxdhServerAuthKeySchedule.Output) (qSign : Nat) (kind : EffectKind) :
    Weighted (commonCost (n := n) qSign kind)
      (RegistrationNativePairedBeaconService.knownStage source owner sender descriptor output) (stageBill kind) := by
  unfold RegistrationNativePairedBeaconService.knownStage stageBill
  exact weighted_bind _ _ _ _ _ (raw_bound source descriptor output qSign kind)
    (fun result => after_bound qSign owner sender _ result kind)

private theorem hidden_bound (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (owner : Nat) (sender : U64) (descriptor : RegistrationBeaconBoundSource.PublicAgreement)
    (reference : RegistrationNativePairedDemand.Reference n) (qSign : Nat) (kind : EffectKind) :
    Weighted (commonCost qSign kind)
      (RegistrationNativePairedBeaconService.hiddenStage source owner sender descriptor reference) (stageBill kind) := by
  unfold RegistrationNativePairedBeaconService.hiddenStage RegistrationNativePairedBeaconService.privateHiddenStage stageBill
  exact weighted_bind _ _ _ _ _ (raw_bound source descriptor _ qSign kind)
    (fun result => after_bound qSign owner sender _ result kind)

/-- The actual paired material/open/install program retains its108/hash/administrative bill through every optional failure. -/
theorem admitted_bound (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (owner : Nat) (sender : U64) (descriptor : RegistrationBeaconBoundSource.PublicAgreement)
    (message : RegistrationNativeRelatedFamily.Message) (qSign : Nat) (kind : EffectKind) :
    Weighted (publicCost (n := n) qSign kind)
      (RegistrationNativePairedBeaconService.admitted source owner sender descriptor message) (admittedBill kind) := by
  unfold RegistrationNativePairedBeaconService.admitted admittedBill
  apply weighted_bind _ _ _ _ _ (query_bound _ _)
  intro chosen
  cases chosen with
  | none => trivial
  | some choice =>
      simp only []
      apply weighted_simulate (commonCost (n := n) qSign kind) (publicCost qSign kind)
        RegistrationNativePairedServerService.publicCommon _ _ ?_ (fun query => query_bound _ _)
      cases choice with
      | known output => exact known_bound source owner sender descriptor output qSign kind
      | hidden reference => exact hidden_bound source owner sender descriptor reference qSign kind

end BeaconcryptCore.Computational.RegistrationNativeBeaconInstallCosts

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeBeaconInstallCosts.admitted_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeBeaconInstallCosts.admitted_bound
