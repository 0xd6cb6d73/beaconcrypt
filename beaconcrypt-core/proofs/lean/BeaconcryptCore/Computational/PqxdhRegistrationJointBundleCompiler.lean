-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRegistrationJointGeneratedFinish

/-! The actual source bundle emits the same one-time draw and three ordered signatures into the shared private-service interface. Optional serialization remains the literal codec computation, with no additional native or cryptographic assumption. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhRegistrationJointBundleCompiler
open PqxdhJointIdentity PqxdhJointGapDh PqxdhServerAuthExperiment
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response Result : Type}

/-- Source generation, signing and the actual optional writer become a client of the same indexed identity/KEM service used by creation and finish. -/
def compiler (codec : Codec Reader Response) :
    QueryImpl (PqxdhLivePhase1Bundle.Spec ScalarBytes) (OracleComp (PqxdhLiveKemBirth.Spec KemSK))
  | .inl _ => PqxdhLiveKemBirth.coins (some <$> sampleScalar)
  | .inr (.inl query) => (PqxdhLiveKemBirth.Spec KemSK).query (.inl query)
  | .inr (.inr candidate) => pure (codec.write1 candidate)

set_option backward.isDefEq.respectTransparency false in
/-- Interpreting the emitted service calls is the existing complete bundle callback interpreter on both full private pools. -/
theorem compiler_interpreted (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) :
    PqxdhLiveKemBirth.impl setup.baseImpl setup.joint setup.kem ∘ₛ compiler codec =
      PqxdhLiveJointSigning.impl setup.joint (PqxdhRegistrationJointBundle.generate (A := PqxdhLiveKemBirth.Pool KemSK))
        (PqxdhRegistrationJointBundle.writer codec) := by
  funext query pool
  cases query with
  | inl request =>
      simp only [QueryImpl.apply_compose, compiler, PqxdhLiveJointSigning.impl,
        PqxdhRegistrationJointBundle.generate, StateT.run_lift, bind_pure_comp,
        Functor.map_map, Prod.mk.eta]
      change (simulateQ (PqxdhLiveKemBirth.impl setup.baseImpl setup.joint setup.kem)
        (PqxdhLiveKemBirth.coins (some <$> sampleScalar))).run pool = _
      simpa only [Functor.map_map] using PqxdhLiveKemBirth.coins_complete setup.baseImpl setup.joint setup.kem
        (some <$> sampleScalar) pool
  | inr request =>
      cases request <;> simp [QueryImpl.apply_compose, compiler, PqxdhLiveKemBirth.impl,
        PqxdhLiveJointSigning.impl, PqxdhRegistrationJointBundle.writer]
      rfl

/-- Complete bundle programs keep all service replies and both full private states in their original continuation. -/
theorem program_interpreted (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (program : OracleComp (PqxdhLivePhase1Bundle.Spec ScalarBytes) Result) :
    simulateQ (PqxdhLiveKemBirth.impl setup.baseImpl setup.joint setup.kem)
      (simulateQ (compiler codec) program) =
    simulateQ (PqxdhLiveJointSigning.impl setup.joint
      (PqxdhRegistrationJointBundle.generate (A := PqxdhLiveKemBirth.Pool KemSK))
      (PqxdhRegistrationJointBundle.writer codec)) program := by
  rw [← QueryImpl.simulateQ_compose, compiler_interpreted]

/-- Compiled source bundle execution retains its complete encoded owner and both private services, including signatures emitted before an optional write failure. -/
theorem bundle_source (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (identityIndex kemIndex : Nat) (owner : PqxdhRegistrationSchedule.Owner KemSK)
    (pool : PqxdhLiveKemBirth.State KemSK)
    (created : pool.1.seeds[identityIndex]? = some owner.beacon.identity) :
    (simulateQ (PqxdhLiveKemBirth.impl setup.baseImpl setup.joint setup.kem)
      (simulateQ (compiler codec) (PqxdhLivePhase1Bundle.bundle
        (PqxdhRegistrationJointBundle.projection setup)
        (PqxdhRegistrationJointBundle.encode setup identityIndex kemIndex owner)))).run pool =
      (fun result => ((result.1.1, PqxdhRegistrationJointBundle.encode setup identityIndex kemIndex result.1.2),
        (result.2, pool.2))) <$> PqxdhRegistrationJointBundle.trace setup codec identityIndex owner pool.1 := by
  rw [program_interpreted, PqxdhRegistrationJointBundle.client_source setup codec identityIndex kemIndex owner pool.1 pool.2 created]

end BeaconcryptCore.Computational.PqxdhRegistrationJointBundleCompiler

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointBundleCompiler.compiler_interpreted' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointBundleCompiler.compiler_interpreted

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointBundleCompiler.program_interpreted' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointBundleCompiler.program_interpreted

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointBundleCompiler.bundle_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointBundleCompiler.bundle_source
