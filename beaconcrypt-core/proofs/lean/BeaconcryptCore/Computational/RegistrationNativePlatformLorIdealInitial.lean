-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformLorCtxClosed
import BeaconcryptCore.Computational.RegistrationNativeG3NativeStartupFields
/-! A cold native private provider has an exact symbolic preimage without changing its material table, known cache or signing receipts. No physical World state is reset or represented by this private shadow. -/
open OracleComp OracleSpec CoreModels
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
namespace BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealInitial
variable {n : Nat} {KemSK : Type}
noncomputable def symbolicPrivate (before : RegistrationNativeSelectiveHiddenInterpreter.State n KemSK RegistrationNativeKemSwitchSource.Phase) :
    RegistrationNativePlatformLorCtxLeaves.Symbolic n KemSK :=
  (⟨fun _ => false,{RegistrationNativePublicInterpreter.initial with receipts:=before.1.receipts},
    (RegistrationNativeSecretWordKemPool.empty,none)⟩,(before.1.keys,before.2))

theorem frame_private (candidate : PqxdhKemIndCca.MlKemSharedSecret)
    (before : RegistrationNativeSelectiveHiddenInterpreter.State n KemSK RegistrationNativeKemSwitchSource.Phase)
    (pool : before.1.pool=PqxdhLiveKemBirth.empty) (phase : before.1.provider=none) :
    RegistrationNativePlatformLorCtxLeaves.frame candidate (symbolicPrivate before)=before := by
  rcases before with ⟨⟨keys,privatePool,provider,receipts⟩,cache⟩
  dsimp only at pool phase
  subst privatePool provider
  rfl

end BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealInitial

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealInitial.frame_private' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealInitial.frame_private
