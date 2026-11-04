-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformBeaconMaterialBills
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicNativeLocal
/-! The literal corrected public finish preserves its optional scalar route, roster update and complete platform state under a source-derived native/global weighted bill. No earlier whole finish equality or caller Frame is used. -/
open OracleComp OracleSpec CoreModels Aeneas beaconcrypt_core
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicNativeFinish
open PqxdhServerAuthExperiment (Setup)
open PqxdhRecordLiftInterface (EffectKind)
open RegistrationBeaconReferenceCompiler (Spec)
open RegistrationNativePlatformBeaconMaterialBills (finishBill)
open RegistrationNativePlatformPublicNativeLocal (bill)
open PqxdhRecordLiftCtxProgramBounds (Weighted weighted_simulate)
open RegistrationNativeWeightedContext (query_bound)
variable {n : Nat} {I KemSK Platform A : Type} {base : OracleSpec I}
private theorem map_apply {S X Y : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (f : X → Y) (work : StateT S m X) (before : S) :
    (f <$> work) before = Prod.map f id <$> work before := StateT.run_map f work before
private theorem ordinary_bound (setup : Setup base KemSK) (scalar : PqxdhJointGapDh.ScalarBytes)
    (qSign qKem : Nat) (kind : EffectKind) (work : OracleComp (Spec n KemSK) A) (cap : Nat)
    (bounded : Weighted (fun query => RegistrationNativeReferenceCosts.bill qSign qKem query kind) work cap) :
    Weighted (fun query => RegistrationNativeReferenceCosts.bill qSign qKem query kind)
      (simulateQ (RegistrationNativePublicOwners.ordinary setup scalar) work) cap := by
  apply weighted_simulate _ _ _ _ _ bounded
  intro query
  cases query with
  | inl message =>
    simp only [RegistrationNativePublicOwners.ordinary]
    cases RegistrationNativeLocalMessage.materialize setup.joint setup.dh scalar message
    · trivial
    · exact query_bound _ _
  | inr query => exact query_bound _ _

theorem owners_bound (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire) (source : RegistrationNativeMldsa.Source)
    (packet : Option registration.ResponsePacket) (index : Nat) (owners : RegistrationNativePublicOwners.State source)
    (env : RegistrationServerReferenceCompiler.Environment) (previous : Platform) (qSign qKem : Nat) (kind : EffectKind) :
    Weighted (bill (n := n) (KemSK := KemSK) qSign qKem kind)
      ((((RegistrationNativePlatformPublicFrontend.finish setup wire source index packet).run owners).run env).run previous)
      (finishBill qKem kind) := by
  simp only [RegistrationNativePlatformPublicFrontend.finish, StateT.run]
  cases owners[index]? with
  | none => trivial
  | some owner =>
    simp only [map_apply, Weighted, isQueryBound_map_iff]
    cases stored : owner.scalar with
    | none =>
      exact RegistrationNativePlatformPublicNativeLocal.local_program qSign qKem kind false _ _
        (RegistrationNativePlatformBeaconMaterialBills.finish_bound setup wire packet owner.view env qSign qKem kind) previous
    | some scalar =>
      exact RegistrationNativePlatformPublicNativeLocal.local_program qSign qKem kind false _ _
        (ordinary_bound setup scalar qSign qKem kind _ _
          (RegistrationNativePlatformBeaconMaterialBills.finish_bound setup wire packet owner.view env qSign qKem kind)) previous

theorem finish_bound (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire) (source : RegistrationNativeMldsa.Source)
    (packet : Option registration.ResponsePacket) (index : Nat)
    (before : RegistrationNativePlatformPublicFrontend.State source Platform) (qSign qKem : Nat) (kind : EffectKind) :
    Weighted (RegistrationNativePlatformPublicWorldBills.nativeBill (n := n) (KemSK := KemSK) qSign qKem kind)
      ((RegistrationNativePlatformPublicFrontend.executeLocal (RegistrationNativePlatformPublicFrontend.beacon
        (RegistrationNativePlatformPublicFrontend.finish setup wire source index packet))).run before)
      (finishBill qKem kind) := by
  apply RegistrationNativePlatformPublicNativeLocal.beacon_bound
  exact owners_bound setup wire source packet index before.1.beacons before.1.environment before.2 qSign qKem kind
end BeaconcryptCore.Computational.RegistrationNativePlatformPublicNativeFinish

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicNativeFinish.owners_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicNativeFinish.owners_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicNativeFinish.finish_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicNativeFinish.finish_bound
