-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxBundleDispatch
import BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxSampleHistory
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxBundleKeyCapture
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativePlatformIdentityCtxMain (Full interpret)
open RegistrationNativePlatformIdentityCtxSigningHistoryFrame (messages)
variable {n : Nat} {I KemSK Platform E : Type} {base : OracleSpec I} {source : RegistrationNativeMldsa.Source}
variable (setup : Setup base KemSK) (checks : Checks)
variable (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created Unit)
variable (index : Nat) (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
local notation "Main" => RegistrationNativePlatformIdentityCtxMain.beacon (n := n) (Platform := Platform) (source := source) setup checks representation created

/-- A first actual whole-bundle history crossing has its actual earlier captured owner, exact generated handle and both fixed source keys, including failed publication. -/
theorem bundle_new (before : Full n KemSK Platform source)
    (result : RustM (Option (alloc.vec.Vec U8)) × Full n KemSK Platform source)
    (supported : result ∈ support ((interpret setup.joint
      (Main (RegistrationNativePlatformIdentityBundleRun.bundle setup index writer))).run before))
    (identity : Nat) (message : Pqxdh.Bytes) (fresh : message ∉ messages identity before.2)
    (signed : message ∈ messages identity result.2.2) :
    ∃ owner, before.1.1.beacons[index]? = some owner ∧ owner.identity.handle = identity ∧
      RegistrationNativeEdKeyPolicy.Allowed (PqxdhPhase2InputBytes.word owner.prekeyPublic) owner.kemPublic message := by
  rcases RegistrationNativePlatformIdentityCtxBundleDispatch.cut setup checks representation created index writer before result supported with rejected | captured
  · cases rejected
    exact False.elim (fresh signed)
  · obtain ⟨owner, scalar, middle, found, picked, called⟩ := captured
    have freshAt : message ∉ messages identity middle.2 := by
      rcases picked with ⟨_phase, sampled⟩ | ⟨_phase, rfl⟩
      · have same := RegistrationNativePlatformIdentityCtxSampleHistory.history setup checks representation created
          PqxdhJointGapDh.sampleScalar before (scalar, middle) sampled identity
        exact fun old => fresh (same ▸ old)
      · exact fresh
    obtain ⟨matched, allowed⟩ := RegistrationNativePlatformIdentityCtxBundleKeyScope.new_message
      setup checks representation created index owner scalar writer middle result called identity message freshAt signed
    exact ⟨owner, found, matched, allowed⟩
end BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxBundleKeyCapture

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxBundleKeyCapture.bundle_new' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxBundleKeyCapture.bundle_new
