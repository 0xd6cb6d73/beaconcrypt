-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformG3UniformRecordProgram
open OracleComp OracleSpec CoreModels
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
namespace BeaconcryptCore.Computational.RegistrationNativePlatformG3UniformSamplerBounds

private theorem vector_bound {A : Type} [SampleableType A] (q : Nat)
    (bounded : ($ᵗ A : ProbComp A).IsTotalQueryBound q) (count : Nat) :
    (SampleableType.vector A count).IsTotalQueryBound (q*count) := by
  induction count with
  | zero => trivial
  | succ count ih =>
    simp only [SampleableType.vector,seq_eq_bind_map,bind_map_left,Nat.mul_succ]
    apply isTotalQueryBound_bind ih
    intro vector
    simpa only [IsTotalQueryBound,isQueryBound_map_iff] using bounded

private theorem function_bound {A : Type} [SampleableType A] (q : Nat)
    (bounded : ($ᵗ A : ProbComp A).IsTotalQueryBound q) (count : Nat) :
    ($ᵗ (Fin count → A) : ProbComp (Fin count → A)).IsTotalQueryBound (q*count) := by
  change ((arrayVectorEquivFin A count) <$> SampleableType.vector A count).IsTotalQueryBound (q*count)
  simpa only [IsTotalQueryBound,isQueryBound_map_iff] using vector_bound q bounded count


/-- The actual finite material table draws44 bytes at each record slot. -/
theorem material_table_bound (count : Nat) :
    ($ᵗ RegistrationNativeG3Tables.MaterialTable count : ProbComp _).IsTotalQueryBound (44*count) :=
  function_bound 44 PqxdhDeploymentHiddenLayout.material_bound count

open PqxdhServerAuthExperiment (Setup)
open PqxdhInitializerSecrecy (kemAmbientImpl)
variable {I KemSK : Type} {base : OracleSpec I}

/-- The real prior draws every reserved generated KEM pair once and then one actual encapsulation. -/
theorem prior_bound (setup : Setup base KemSK) (count : Nat) (selected : Fin (count+1))
    (qKeygen qEncap : Nat)
    (keygenBound : (simulateQ (kemAmbientImpl setup.baseImpl) setup.kem.keygen).IsTotalQueryBound qKeygen)
    (encapBound : ∀ publicKey, (simulateQ (kemAmbientImpl setup.baseImpl) (setup.kem.encaps publicKey)).IsTotalQueryBound qEncap) :
    (RegistrationNativeG3NativeRepeatUniformBound.prior setup.baseImpl setup.kem count selected).IsTotalQueryBound
      ((count+1)*qKeygen+qEncap) := by
  unfold RegistrationNativeG3NativeRepeatUniformBound.prior
  have billed := isTotalQueryBound_bind keygenBound (fun chosen =>
    isTotalQueryBound_bind (PqxdhLiveKemSelection.family_uniform _ qKeygen count keygenBound) (fun others =>
      isTotalQueryBound_bind (encapBound chosen.1) (fun pair =>
        show (pure (⟨List.ofFn (selected.insertNth chosen others),chosen.1,pair.1⟩ : RegistrationNativeSecretWordAliasOuter.Profile KemSK) : ProbComp _).IsTotalQueryBound 0 from by trivial)))
  convert billed using 1
  change count.succ*qKeygen+qEncap = qKeygen+(qKeygen*count+(qEncap+0))
  rw [Nat.succ_mul,Nat.mul_comm count qKeygen]
  omega


def cost (budget : PqxdhDeploymentInterface.Budget) (qKeygen qEncap : Nat) : Nat :=
  96 + 88*(budget.cap 4+budget.cap 5) + (budget.create+1)*qKeygen + qEncap

/-- The whole reduction-owned sampler has its literal seed/scalar/material/candidate draw bill plus the actual KEM generator and encapsulation bills. Runtime callback costs remain separate. -/
theorem sample_bound (setup : Setup base KemSK) (budget : PqxdhDeploymentInterface.Budget) (selected : Fin (budget.create+1))
    (qKeygen qEncap : Nat)
    (keygenBound : (simulateQ (kemAmbientImpl setup.baseImpl) setup.kem.keygen).IsTotalQueryBound qKeygen)
    (encapBound : ∀ publicKey, (simulateQ (kemAmbientImpl setup.baseImpl) (setup.kem.encaps publicKey)).IsTotalQueryBound qEncap) :
    (RegistrationNativePlatformG3UniformRecordProgram.sample setup budget selected).IsTotalQueryBound (cost budget qKeygen qEncap) := by
  unfold RegistrationNativePlatformG3UniformRecordProgram.sample RegistrationNativePlatformG3UniformOpaqueGame.draws
  simp only [bind_assoc,pure_bind]
  have billed := isTotalQueryBound_bind PqxdhJointIdentity.sampleSeed_uniform_bound (fun seed =>
    isTotalQueryBound_bind PqxdhJointGapDh.sampleScalar_uniform (fun scalar =>
      isTotalQueryBound_bind (material_table_bound (budget.cap 4+budget.cap 5)) (fun unused =>
        isTotalQueryBound_bind (prior_bound setup budget.create selected qKeygen qEncap keygenBound encapBound) (fun profile =>
          isTotalQueryBound_bind (CtxComputationalSecurity.uniformFixedBytes_isTotalQueryBound 32) (fun candidate =>
            isTotalQueryBound_bind (material_table_bound (budget.cap 4+budget.cap 5)) (fun materials =>
              show (pure (⟨seed,scalar,unused,profile,candidate,materials⟩ : RegistrationNativePlatformG3UniformRecordProgram.Sample KemSK (budget.cap 4+budget.cap 5)) : ProbComp _).IsTotalQueryBound 0 from by trivial))))))
  convert billed using 1
  simp only [cost]
  omega

end BeaconcryptCore.Computational.RegistrationNativePlatformG3UniformSamplerBounds

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformG3UniformSamplerBounds.material_table_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformG3UniformSamplerBounds.material_table_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformG3UniformSamplerBounds.prior_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformG3UniformSamplerBounds.prior_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformG3UniformSamplerBounds.sample_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformG3UniformSamplerBounds.sample_bound
