-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformSourceSeal
import BeaconcryptCore.Computational.RegistrationNativeRecordHashReceipt

/-! The actual mutable source commitment hash uses the original native shared cache. Every supported source reply retains its literal native hash cut and digest at the returned cache, while arbitrary external platform state and the returned transcript replacement remain explicit. -/
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformHashReceipt
open PqxdhServerAuthExperiment (Setup Codec)
open RegistrationWorldAgreement (State)
variable {n : Nat} {Auxiliary Platform Value ι KemSK Reader Response : Type} {base : OracleSpec ι}

/-- Interpreting ordinary primitive draws in a shared external state retains a supported original native result. -/
theorem native_support (coins : QueryImpl unifSpec (StateT Platform ProbComp))
    (work : ProbComp Value) (value : Value) (before after : Platform)
    (supported : (value, after) ∈ support ((simulateQ coins work).run before)) : value ∈ support work := by
  apply OracleComp.support_simulateQ_run'_subset coins work before
  rw [StateT.run'_eq, support_map]
  exact ⟨(value, after), supported, rfl⟩

/-- Actual source mutable hashing returns the precise native digest and its receipt in the same reached cache. -/
theorem source (coins : QueryImpl unifSpec (StateT Platform ProbComp))
    (setup : Setup base KemSK) (codec : Codec Reader Response)
    (erased transcript : commitment.CommitmentTranscript)
    (reply : RegistrationRecordPrimitives.Spec.Range (.hash transcript))
    (replacement : commitment.CommitmentTranscript)
    (before after : State n Auxiliary) (previous next : Platform)
    (supported : ((.ok (reply, replacement), after), next) ∈ support
      (((RegistrationNativePlatformSourceSeal.hash coins setup codec erased transcript).run before).run previous)) :
    replacement = erased ∧
      (reply, after) ∈ support ((RegistrationWorldRecords.handler setup codec (.hash transcript)).run before) ∧
      ∃ digest, reply = .Some (RegistrationAuthenticationShared.digestArray digest) ∧
        before.world.1.primitive.2 ≤ after.world.1.primitive.2 ∧
        after.world.1.primitive.2 ((), absBytes transcript.bytes) = some digest := by
  have hashRun : ((RegistrationNativePlatformSourceSeal.hash coins setup codec erased transcript).run before).run previous =
      (fun result => ((.ok (result.1.1, erased), result.1.2), result.2)) <$>
        ((RegistrationNativePlatformServerCompletion.records coins setup codec (.hash transcript)).run before).run previous := by
    simp only [RegistrationNativePlatformSourceSeal.hash, bind_pure_comp]
    simp only [StateT.run_map]
  rw [hashRun, support_map] at supported
  obtain ⟨⟨⟨answer, current⟩, platform⟩, called, equal⟩ := supported
  simp only [Prod.mk.injEq, RustM.ok.injEq] at equal
  obtain ⟨⟨⟨same, replaced⟩, stateEq⟩, platformEq⟩ := equal
  cases same
  cases stateEq
  cases platformEq
  have actual : (reply, after) ∈ support ((RegistrationWorldRecords.handler setup codec (.hash transcript)).run before) :=
    native_support coins _ (reply, after) previous next called
  exact ⟨replaced.symm, actual, RegistrationNativeRecordHashReceipt.world setup codec transcript before after reply actual⟩

end BeaconcryptCore.Computational.RegistrationNativePlatformHashReceipt

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformHashReceipt.native_support' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformHashReceipt.native_support

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformHashReceipt.source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformHashReceipt.source
