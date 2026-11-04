-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureCandidateDraw
import BeaconcryptCore.Computational.RegistrationNativePlatformG3UniformRecordProgram
/-! The genuine uniform sampler's candidate value can be refreshed after any independent continuation while its original physical coin charge and all reached state remain in place. -/
open OracleComp OracleSpec CoreModels Aeneas
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureSampler
open PqxdhServerAuthExperiment (Setup Codec)
open RegistrationNativeSuffixKeyPrf (Secret)
open RegistrationNativePlatformG3UniformRecordProgram (Sample sample)
variable {I KemSK Reader Response A : Type} {base : OracleSpec I}
variable (setup : Setup base KemSK) (budget : PqxdhDeploymentInterface.Budget) (selected : Fin (budget.create+1))
local notation "cap"=>budget.cap 4+budget.cap 5
variable (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
local notation "State"=>RegistrationNativePlatformLorIdealPhysical.State cap (PqxdhRecordLiftIdeal.CtxPrivate cap)
local notation "physical"=>RegistrationNativePlatformLorIdealPhysical.implementation
  (PqxdhRecordLiftIdeal.ctxInterpreter (fun _=>PqxdhRecordLiftIdeal.KeyMode.random) id setup codec) codec route

def erase (parameters : Sample KemSK cap) : Sample KemSK cap :=
  {parameters with candidate:=RegistrationNativeSecretWordMessage.zero}

private theorem resample {C R : Type} (future : ProbComp C) (next : Secret →C →ProbComp R) :
    ($ᵗ Secret >>=fun candidate=>future >>=next candidate)=ᵈ
      ($ᵗ Secret >>=fun _=>future >>=fun current=>$ᵗ Secret >>=fun candidate=>next candidate current) := by
  exact (OracleComp.EvalDistEq.bind_bind_swap ($ᵗ Secret) future next).trans
    (OracleComp.EvalDistEq.bind_const ($ᵗ Secret) (future >>=fun current=>$ᵗ Secret >>=fun candidate=>next candidate current)).symm

/-- Original physical sampling and a later independent mathematical candidate have the same full continuation law, with the same actual charged physical state. -/
theorem refresh (before : State) (next : Secret →Sample KemSK cap →State →ProbComp A) :
    (do
      let sampled←(simulateQ physical (simulateQ PqxdhRecordLiftInterface.coinLift (sample setup budget selected))).run before
      next sampled.1.candidate (erase budget sampled.1) sampled.2)=ᵈ
    (do
      let sampled←(simulateQ physical (simulateQ PqxdhRecordLiftInterface.coinLift (sample setup budget selected))).run before
      let candidate←$ᵗ Secret
      next candidate (erase budget sampled.1) sampled.2) := by
  unfold sample RegistrationNativePlatformG3UniformOpaqueGame.draws
  simp only [simulateQ_bind,simulateQ_pure,StateT.run_bind,StateT.run_pure,bind_assoc,pure_bind]
  apply _root_.EvalDistEq.bind_right
  rintro ⟨seed,first⟩
  apply _root_.EvalDistEq.bind_right
  rintro ⟨scalar,second⟩
  apply _root_.EvalDistEq.bind_right
  rintro ⟨unused,third⟩
  apply _root_.EvalDistEq.bind_right
  rintro ⟨profile,fourth⟩
  rw [RegistrationNativePlatformRecordPartnerExposureCandidateDraw.draw setup codec route]
  simp only [bind_map_left,erase]
  exact resample
    ((simulateQ physical (simulateQ PqxdhRecordLiftInterface.coinLift
      ($ᵗ RegistrationNativeG3Tables.MaterialTable cap))).run
        (RegistrationNativePlatformRecordPartnerExposureCandidateDraw.advance 32 fourth))
    (fun candidate materials=>next candidate
      ⟨seed,scalar,unused,profile,RegistrationNativeSecretWordMessage.zero,materials.1⟩ materials.2)

end BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureSampler
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureSampler.refresh' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureSampler.refresh
