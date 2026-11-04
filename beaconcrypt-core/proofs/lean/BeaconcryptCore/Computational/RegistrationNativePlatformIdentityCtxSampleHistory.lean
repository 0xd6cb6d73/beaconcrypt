-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxSampleCoins
import BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxSigningHistoryFrame
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxSampleHistory
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativePlatformIdentityCtxSigningHistoryFrame (messages NoSignFor)
variable {n : Nat} {I KemSK Platform A : Type} {base : OracleSpec I} {source : RegistrationNativeMldsa.Source}
variable (setup : Setup base KemSK) (checks : Checks)
variable (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created Unit)
local notation "sample(" work ")" => RegistrationNativePlatformIdentityCtxMain.beacon (n := n) (Platform := Platform) (source := source)
  setup checks representation created (RegistrationNativePlatformIdentityProgram.native
    (RegistrationNativeIdentityFrontend.sample (n := n) (KemSK := KemSK) (Auxiliary := RegistrationServerRoleBackend.State) (source := source) work))

/-- Literal native scalar sampling retains every generated handle's actual successful signing messages while executing its full reached source state. -/
theorem history (work : ProbComp A) (before : RegistrationNativePlatformIdentityCtxMain.Full n KemSK Platform source)
    (result : A × RegistrationNativePlatformIdentityCtxMain.Full n KemSK Platform source)
    (supported : result ∈ support ((RegistrationNativePlatformIdentityCtxMain.interpret setup.joint (sample(work))).run before))
    (identity : Nat) : messages identity result.2.2 = messages identity before.2 := by
  simp only [RegistrationNativePlatformIdentityCtxMain.interpret, StateT.run, support_map] at supported
  obtain ⟨inner, reached, rfl⟩ := supported
  apply RegistrationNativePlatformIdentityCtxSigningHistoryFrame.program setup.joint identity _ ?_ before.2 inner reached
  apply (RegistrationNativePlatformIdentityCtxSampleCoins.sample setup checks representation created work before.1).mono
  intro query coin
  unfold NoSignFor
  split
  · exact coin.elim
  · trivial
end BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxSampleHistory

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxSampleHistory.history' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxSampleHistory.history
