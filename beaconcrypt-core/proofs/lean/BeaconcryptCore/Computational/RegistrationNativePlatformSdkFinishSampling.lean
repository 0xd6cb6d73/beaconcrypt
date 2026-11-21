-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterCryptoPlatform
import BeaconcryptCore.Computational.RegistrationNativePlatformInterpret
/-! The original Finish crypto sampler observes only actual uniform draws. It does not synthesize explicit World coin-effect requests or private indexed KEM observations. -/
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformSdkFinishSampling
open BeaconcryptCore.Refinement
open RegistrationNativePlatformSdkReification (Backend)
open RegistrationAgreementSampledState
variable {n : Nat} {KemSK P A B : Type}

noncomputable def sample (work : ProbComp A) : StateT (Backend n KemSK) ProbComp A :=
  RegistrationNativePlatformPublicAdapterCrypto.world (PqxdhRecordLiftWorld.sampled work)

noncomputable def uniform : QueryImpl unifSpec (StateT (Backend n KemSK) ProbComp) :=
  fun query => sample (unifSpec.query query)

private theorem sample_pure (value : A) : sample (n:=n) (KemSK:=KemSK) (pure value) = pure value := by
  funext before
  change (fun result : A × PqxdhRecordLiftWorld.State n => (result.1,{before with world:=result.2})) <$>
    (PqxdhRecordLiftWorld.sampled (pure value)).run before.world = pure (value,before)
  rw [sampled_pure,map_pure]

private theorem sample_bind (work : ProbComp A) (next : A → ProbComp B) :
    sample (n:=n) (KemSK:=KemSK) (work >>= next) = (sample work >>= fun value => sample (next value)) := by
  funext before
  change (fun result : B × PqxdhRecordLiftWorld.State n => (result.1,{before with world:=result.2})) <$>
    (PqxdhRecordLiftWorld.sampled (work >>= next)).run before.world =
    (do
      let first ← (fun result : A × PqxdhRecordLiftWorld.State n => (result.1,{before with world:=result.2})) <$>
        (PqxdhRecordLiftWorld.sampled work).run before.world
      (fun result : B × PqxdhRecordLiftWorld.State n => (result.1,{first.2 with world:=result.2})) <$>
        (PqxdhRecordLiftWorld.sampled (next first.1)).run first.2.world)
  rw [sampled_bind,map_bind,bind_map_left]

 theorem program (work : ProbComp A) :
    simulateQ (uniform (n:=n) (KemSK:=KemSK)) work = sample work := by
  induction work using OracleComp.inductionOn with
  | pure value => rw [simulateQ_pure,sample_pure]
  | query_bind query next ih =>
      simp only [simulateQ_bind,simulateQ_spec_query,ih,uniform]
      exact (sample_bind (unifSpec.query query) next).symm

noncomputable def sampleP (coins : QueryImpl unifSpec (StateT P ProbComp)) (work : ProbComp A) :
    StateT (Backend n KemSK) (StateT P ProbComp) A :=
  RegistrationNativePlatformInterpret.state coins (sample work)

noncomputable def uniformP (coins : QueryImpl unifSpec (StateT P ProbComp)) :
    QueryImpl unifSpec (StateT (Backend n KemSK) (StateT P ProbComp)) :=
  fun query => RegistrationNativePlatformInterpret.state coins (uniform query)

 theorem programP (coins : QueryImpl unifSpec (StateT P ProbComp)) (work : ProbComp A) :
    simulateQ (uniformP (n:=n) (KemSK:=KemSK) coins) work = sampleP coins work := by
  unfold uniformP sampleP
  rw [←RegistrationNativePlatformInterpret.state_simulate,program]

end BeaconcryptCore.Computational.RegistrationNativePlatformSdkFinishSampling

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSdkFinishSampling.program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSdkFinishSampling.program

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSdkFinishSampling.programP' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSdkFinishSampling.programP
