-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformInstallBeaconFinish
import BeaconcryptCore.Computational.RegistrationNativePlatformBeaconRuntimeDictionary
/-! Every actual public owner callback has the exact concrete G2 successful-install count of its same returned application, retaining persistent P and every terminal failure. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformInstallBeaconTyped
open PqxdhServerAuthExperiment (Setup)
open RegistrationNativeInstallOrdinals (messages)
open RegistrationNativeInstallBeaconComplete (present)
open RegistrationNativeG2Trace (State handler)
variable {n : Nat} {I KemSK Platform A : Type} {base : OracleSpec I} {source : RegistrationNativeMldsa.Source}

private theorem local_program (work : OracleComp (RegistrationBeaconReferenceCompiler.Spec n KemSK) A) :
    simulateQ RegistrationNativePlatformPublicCoinEmbedding.embed
      (simulateQ RegistrationNativePlatformPublicFrontend.embedLocal
        (simulateQ (RegistrationNativePlatformPublicFrontend.localQuery false) work)) =
      simulateQ (RegistrationNativePublicFrontend.liftLocal false) work := by
  induction work using OracleComp.inductionOn with
  | pure value => simp only [simulateQ_pure]
  | query_bind query next ih =>
    simp only [simulateQ_bind,simulateQ_spec_query,RegistrationNativePlatformBeaconRuntimeDictionary.local_query]
    congr 1
    funext reply
    exact ih reply

/-- The concrete same-result trace counts the actual corrected finish on every owner and failure branch. -/
theorem finish (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (role : PqxdhRecordLiftInterface.Role) (index : Nat) (packet : Option registration.ResponsePacket)
    (frontend : RegistrationNativePlatformPublicFrontend.State source Platform) (before : State)
    (result : (RustM (Option Pqxdh.Bytes) × RegistrationNativePlatformPublicFrontend.State source Platform) × State)
    (supported : result ∈ support ((simulateQ handler (simulateQ (RegistrationNativePlatformPublicCoinEmbedding.embed (n := n) (KemSK := KemSK))
      ((RegistrationNativePlatformPublicFrontend.executeLocal
        (RegistrationNativePlatformPublicFrontend.beacon (RegistrationNativePlatformPublicFrontend.finish setup wire source index packet))).run frontend))).run before)) :
    ∃ added, messages role result.2.events = messages role before.events ++ added ∧
      added.length = if role = .beacon ∧ present result.1.1 = true then 1 else 0 := by
  cases found : frontend.1.beacons[index]? with
  | none =>
    simp only [RegistrationNativePlatformPublicFrontend.executeLocal,RegistrationNativePlatformPublicFrontend.beacon,
      RegistrationNativePlatformPublicFrontend.finish,found,StateT.run] at supported
    subst result
    exact ⟨[],by simp only [List.append_nil],by simp [present]⟩
  | some owner =>
    rw [RegistrationNativePlatformTypedBeaconCut.finish_source setup wire index packet frontend owner found] at supported
    simp only [simulateQ_map,local_program,StateT.run_map,support_map] at supported
    obtain ⟨localResult,actual,returned⟩ := supported
    have counted := RegistrationNativePlatformInstallBeaconFinish.finish role setup wire owner.scalar owner.view
      frontend.1.environment packet before localResult (by
        simpa only [RegistrationNativePlatformInstallBeaconFinish.compile,RegistrationNativeInstallBeaconComplete.compile] using actual)
    cases returned
    exact counted

end BeaconcryptCore.Computational.RegistrationNativePlatformInstallBeaconTyped
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformInstallBeaconTyped.finish' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformInstallBeaconTyped.finish
