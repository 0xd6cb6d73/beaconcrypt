-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeKemReferenceEffects

/-! The open Server getter has the literal real encapsulation callback and chronological after-reply marker. Its real private interpretation is native counted sampling with the whole generated-key pool and remaining service state unchanged. No prepare/material/publication callback is invoked. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeKemReferenceEncapsulation
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationServerReferenceCompiler (Environment)
open RegistrationNativeKemReferenceWorld (Private sampled_map)
open RegistrationNativeKemReferenceEffects (Callbacks implementation)
variable {n : Nat} {ι KemSK Extra Value : Type} {base : OracleSpec ι}

private theorem indexed_program (setup : Setup base KemSK) (callbacks : Callbacks n KemSK Extra)
    (work : OracleComp (RegistrationNativeKemInterface.Spec RegistrationNativeKemInterface.OtherSpec KemSK) Value) :
    simulateQ (implementation setup callbacks) (simulateQ RegistrationBeaconReferenceCompiler.indexed work) =
      simulateQ (RegistrationNativeKemReferenceWorld.kem setup callbacks.other) work := by
  rw [← QueryImpl.simulateQ_compose]
  apply congrArg (fun interpreter => simulateQ interpreter work)
  funext query
  exact RegistrationNativeKemReferenceWorld.indexed_query setup callbacks.other callbacks.prepare
    callbacks.demand callbacks.publication query

/-- Real closure of the exposed native encapsulation callback retains every native poststate, the exact primitive draw bill, public request timing and the complete private pool. -/
theorem source (setup : Setup base KemSK) (checks : Checks) (callbacks : Callbacks n KemSK Extra)
    (key : core.option.Option (Std.Array U8 1184#usize)) (before : Environment)
    (privateBefore : Private n KemSK Extra) :
    (simulateQ (implementation setup callbacks)
      ((RegistrationNativeKemReferenceCompiler.backend setup checks (.encapsulate key)).run before)).run privateBefore =
      (fun result => ((result.1.1, { before with
          auxiliary := result.1.2
          requests := before.requests ++ RegistrationWorldAgreement.recorded (.encapsulate key) }),
        { privateBefore with world := result.2 })) <$>
        (PqxdhRecordLiftWorld.sampled
          ((RegistrationServerRoleBackend.localBackend setup checks (.encapsulate key)).run before.auxiliary)).run privateBefore.world := by
  rw [RegistrationNativeKemReferenceCompiler.backend_encapsulation]
  simp only [simulateQ_map, StateT.run_map, indexed_program]
  cases key with
  | none =>
      simp only [RegistrationNativeKemInterface.server, simulateQ_pure,
        RegistrationServerRoleBackend.localBackend, PqxdhRecordLiftWorld.sampled, StateT.run]
      rfl
  | some key =>
      simp only [RegistrationNativeKemInterface.server, RegistrationServerRoleBackend.localBackend]
      by_cases valid : checks.kemKey (RegistrationRootInput.pqKey key) = true
      · simp only [valid, ite_true, RegistrationNativeKemInterface.encapsulate,
          simulateQ_map, simulateQ_spec_query, StateT.run_map]
        rw [RegistrationNativeKemReferenceWorld.kem_encapsulation]
        have localRun : (StateT.lift
            (RegistrationAgreementRoot.nativeOption <$> PqxdhServerAuthExperiment.encapsulate setup (RegistrationRootInput.pqKey key)) :
              StateT RegistrationServerRoleBackend.State ProbComp _).run before.auxiliary =
            (fun reply => (reply, before.auxiliary)) <$>
              (RegistrationAgreementRoot.nativeOption <$> PqxdhServerAuthExperiment.encapsulate setup (RegistrationRootInput.pqKey key)) := by
          rw [StateT.run_lift, bind_pure_comp]
        rw [localRun, sampled_map]
        simp only [PqxdhServerAuthExperiment.encapsulate, simulateQ_map, sampled_map,
          Functor.map_map, Prod.map_def, id_eq, RegistrationAgreementRoot.nativeOption]
      · have rejected : checks.kemKey (RegistrationRootInput.pqKey key) = false := Bool.eq_false_iff.mpr valid
        simp only [rejected, Bool.false_eq_true, ite_false, simulateQ_pure,
          PqxdhRecordLiftWorld.sampled, StateT.run]
        rfl

end BeaconcryptCore.Computational.RegistrationNativeKemReferenceEncapsulation

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemReferenceEncapsulation.source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemReferenceEncapsulation.source
