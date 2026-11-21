-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeKemReferenceEncapsulation

/-! The open indexed getter and every ordinary Server primitive have the same actual native agreement result and World. Only the already proved additional Env coin-effect counter is projected. Separate support receipts retain the whole private KEM pool and remaining service state. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeKemReferenceBackend
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationServerReferenceCompiler (Environment)
open RegistrationNativeKemReferenceWorld (Private)
open RegistrationNativeKemReferenceEffects (Callbacks implementation)
variable {n : Nat} {ι KemSK Extra Value : Type} {base : OracleSpec ι}

abbrev State (n : Nat) (KemSK Extra : Type) := Environment × Private n KemSK Extra

def project (before : State n KemSK Extra) : RegistrationServerRootCompiler.Local n :=
  RegistrationWorldAgreementProgramCompiler.project (before.1, before.2.world)

noncomputable def backend (setup : Setup base KemSK) (checks : Checks) (callbacks : Callbacks n KemSK Extra) :
    QueryImpl RegistrationAgreementExecutor.Spec (StateT (State n KemSK Extra) ProbComp) :=
  ((implementation setup callbacks).mapStateTBase (RegistrationNativeKemReferenceCompiler.backend setup checks)).flattenStateT

private theorem backend_run (setup : Setup base KemSK) (checks : Checks) (callbacks : Callbacks n KemSK Extra)
    (query : RegistrationAgreementExecutor.Request) (before : State n KemSK Extra) :
    (backend setup checks callbacks query).run before =
      (fun result => (result.1.1, (result.1.2, result.2))) <$>
        (simulateQ (implementation setup callbacks)
          ((RegistrationNativeKemReferenceCompiler.backend setup checks query).run before.1)).run before.2 := rfl

/-- Ordinary callbacks keep the literal native reply, auxiliary state, request ordering and complete source World after the exact extra-coin projection. -/
theorem ordinary_project (setup : Setup base KemSK) (checks : Checks) (callbacks : Callbacks n KemSK Extra)
    (query : RegistrationAgreementExecutor.Request)
    (notKem : RegistrationNativeKemReferenceCompiler.NonEncapsulation query) (before : State n KemSK Extra) :
    Prod.map id project <$> (backend setup checks callbacks query).run before =
      (RegistrationWorldAgreement.agreement setup.source
        (RegistrationServerRoleBackend.localBackend setup checks) query).run (project before) := by
  rw [backend_run, Functor.map_map]
  have lowered := congrArg (fun distribution => (fun result => (result.1.1, project (result.1.2, result.2))) <$> distribution)
    (RegistrationNativeKemReferenceEffects.backend_ordinary setup checks callbacks query notKem before.1 before.2)
  have native := RegistrationWorldAgreementProgramCompiler.query_project setup.source
    (RegistrationServerRoleBackend.localBackend setup checks) query (before.1, before.2.world)
  calc
    _ = Prod.map id RegistrationWorldAgreementProgramCompiler.project <$>
        (RegistrationWorldAgreementProgramCompiler.handler setup.source
          (RegistrationServerRoleBackend.localBackend setup checks) query).run (before.1, before.2.world) := by
      simpa only [backend_run, Functor.map_map, Prod.map_def, id_eq, project,
        RegistrationWorldAgreementProgramCompiler.handler, RegistrationWorldAgreementCompiler.run, StateT.run] using lowered
    _ = _ := native

/-- The real exposed encapsulation has the actual native sampler and all native World fields; no source getter equality is assumed. -/
theorem encapsulation_project (setup : Setup base KemSK) (checks : Checks) (callbacks : Callbacks n KemSK Extra)
    (key : core.option.Option (Std.Array U8 1184#usize)) (before : State n KemSK Extra) :
    Prod.map id project <$> (backend setup checks callbacks (.encapsulate key)).run before =
      (RegistrationWorldAgreement.agreement setup.source
        (RegistrationServerRoleBackend.localBackend setup checks) (.encapsulate key)).run (project before) := by
  rw [backend_run, Functor.map_map]
  have lowered := congrArg (fun distribution => (fun result => (result.1.1, project (result.1.2, result.2))) <$> distribution)
    (RegistrationNativeKemReferenceEncapsulation.source setup checks callbacks key before.1 before.2)
  have native := RegistrationWorldAgreementProgramCompiler.native_mask setup.source
    (RegistrationServerRoleBackend.localBackend setup checks) (.encapsulate key)
    (RegistrationWorldAgreementCompiler.join before.1 before.2.world)
  calc
    _ = Prod.map id RegistrationWorldAgreementCompiler.mask <$>
        (RegistrationWorldAgreement.agreement setup.source
          (RegistrationServerRoleBackend.localBackend setup checks) (.encapsulate key)).run
          (RegistrationWorldAgreementCompiler.join before.1 before.2.world) := by
      simp only [RegistrationWorldAgreement.agreement, RegistrationAgreementShared.auxiliary,
        RegistrationWorldAgreementCompiler.join, project, RegistrationWorldAgreementProgramCompiler.project,
        RegistrationWorldAgreementCompiler.mask, StateT.run, Functor.map_map, Prod.map_def, id_eq] at lowered ⊢
      exact lowered
    _ = _ := native

/-- Every actual open primitive callback has its concrete native source meaning. -/
theorem query_project (setup : Setup base KemSK) (checks : Checks) (callbacks : Callbacks n KemSK Extra)
    (query : RegistrationAgreementExecutor.Request) (before : State n KemSK Extra) :
    Prod.map id project <$> (backend setup checks callbacks query).run before =
      (RegistrationWorldAgreement.agreement setup.source
        (RegistrationServerRoleBackend.localBackend setup checks) query).run (project before) := by
  cases query with
  | encapsulate key => exact encapsulation_project setup checks callbacks key before
  | convertPublic key => exact ordinary_project setup checks callbacks (.convertPublic key) trivial before
  | convertSecret role => exact ordinary_project setup checks callbacks (.convertSecret role) trivial before
  | generate role => exact ordinary_project setup checks callbacks (.generate role) trivial before
  | decapsulate ciphertext => exact ordinary_project setup checks callbacks (.decapsulate ciphertext) trivial before
  | dh request => exact ordinary_project setup checks callbacks (.dh request) trivial before
  | root request => exact ordinary_project setup checks callbacks (.root request) trivial before

end BeaconcryptCore.Computational.RegistrationNativeKemReferenceBackend

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemReferenceBackend.ordinary_project' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemReferenceBackend.ordinary_project
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemReferenceBackend.encapsulation_project' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemReferenceBackend.encapsulation_project
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemReferenceBackend.query_project' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemReferenceBackend.query_project
