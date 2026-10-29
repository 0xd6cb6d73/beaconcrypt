-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeKemReferenceWorld

/-! Ordinary callbacks of the open Server reference compiler lower to the original same-World environment computation. Private prepare/material/publication services remain arbitrary because this component never invokes them. The actual private KEM pool and all remaining service state are retained in the whole-program equality. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeKemReferenceEffects
open PqxdhServerAuthExperiment (Setup Checks)
open PqxdhRecordLiftInterface (EnvEffects)
open RegistrationServerReferenceCompiler (Environment)
open RegistrationNativeKemReferenceCompiler (Spec)
open RegistrationNativeKemReferenceWorld (Private)
variable {n : Nat} {ι KemSK Extra Value : Type} {base : OracleSpec ι}

structure Callbacks (n : Nat) (KemSK Extra : Type) where
  other : QueryImpl RegistrationNativeKemInterface.OtherSpec ProbComp
  prepare : QueryImpl RegistrationServerReferenceRoot.PrepareSpec (StateT (Private n KemSK Extra) ProbComp)
  demand : QueryImpl (RegistrationNativeRelatedFamily.Message →ₒ Option (RegistrationNativePairedChoice.Choice n))
    (StateT (Private n KemSK Extra) ProbComp)
  publication : QueryImpl RegistrationBoundPublication.Spec (StateT (Private n KemSK Extra) ProbComp)

noncomputable def implementation (setup : Setup base KemSK) (callbacks : Callbacks n KemSK Extra) :
    QueryImpl (Spec n KemSK) (StateT (Private n KemSK Extra) ProbComp) :=
  RegistrationNativeKemReferenceWorld.handler setup callbacks.other callbacks.prepare callbacks.demand callbacks.publication

/-- Every adaptive ordinary effect program has its exact original World result and keeps the entire private pool/service frame. -/
theorem ordinary_program (setup : Setup base KemSK) (callbacks : Callbacks n KemSK Extra)
    (work : OracleComp (EnvEffects n) Value) (before : Private n KemSK Extra) :
    (simulateQ (implementation setup callbacks)
      (simulateQ RegistrationNativeKemReferenceCompiler.lift
        (simulateQ RegistrationServerReferenceCompiler.effect work))).run before =
      (fun result => (result.1, { before with world := result.2 })) <$>
        (simulateQ PqxdhRecordLiftWorld.effects work).run before.world := by
  rw [← QueryImpl.simulateQ_compose, ← QueryImpl.simulateQ_compose]
  have same : (implementation setup callbacks ∘ₛ RegistrationNativeKemReferenceCompiler.lift) ∘ₛ
      RegistrationServerReferenceCompiler.effect = RegistrationNativeKemReferenceWorld.effect := by
    funext query
    exact RegistrationNativeKemReferenceWorld.effect_query setup callbacks.other callbacks.prepare
      callbacks.demand callbacks.publication query
  rw [same]
  exact RegistrationNativeKemReferenceWorld.world_program PqxdhRecordLiftWorld.effects work before

/-- A non-KEM agreement callback is the original scalar-free local callback and request-log program, with exact World and private-pool state. -/
theorem backend_ordinary (setup : Setup base KemSK) (checks : Checks) (callbacks : Callbacks n KemSK Extra)
    (query : RegistrationAgreementExecutor.Request)
    (notKem : RegistrationNativeKemReferenceCompiler.NonEncapsulation query)
    (before : Environment) (privateBefore : Private n KemSK Extra) :
    (simulateQ (implementation setup callbacks)
      ((RegistrationNativeKemReferenceCompiler.backend setup checks query).run before)).run privateBefore =
      (fun result => (result.1, { privateBefore with world := result.2 })) <$>
        (simulateQ PqxdhRecordLiftWorld.effects
          ((RegistrationWorldAgreementCompiler.compiler setup.source
            (RegistrationServerRoleBackend.localBackend setup checks) query).run before)).run privateBefore.world := by
  rw [RegistrationNativeKemReferenceCompiler.backend_ordinary setup checks query notKem before]
  change (simulateQ (implementation setup callbacks)
    (simulateQ RegistrationNativeKemReferenceCompiler.lift
      (simulateQ RegistrationServerReferenceCompiler.effect
        ((RegistrationWorldAgreementCompiler.compiler setup.source
          (RegistrationServerRoleBackend.localBackend setup checks) query).run before)))).run privateBefore = _
  exact ordinary_program setup callbacks _ privateBefore

end BeaconcryptCore.Computational.RegistrationNativeKemReferenceEffects

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemReferenceEffects.ordinary_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemReferenceEffects.ordinary_program
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemReferenceEffects.backend_ordinary' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemReferenceEffects.backend_ordinary
