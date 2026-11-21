-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeG3KeyServiceInlining
import BeaconcryptCore.Computational.RegistrationNativeSelectiveHiddenService
import BeaconcryptCore.Computational.RegistrationNativeG3MaterializedFrontend

/-! The actual descriptor-flag service can use a fixed first-touch material table and private seed table while retaining the same allocator and nonselected108 cache as the selective hidden service. The key state contains no seed or World field. Completing its material44 cache changes no descriptor, allocation, demand counter or nonselected output. The private tables are interpreter parameters, and original prefix capacity discharges fresh selected allocation room. -/
open OracleComp OracleSpec CoreModels
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeG3SelectiveService
open PqxdhRecordLiftInterface (Slot EnvEffects)
open PqxdhDeploymentHiddenLayout (Material joinOutput)
open PqxdhServerAuthKeySchedule (Output)
open RegistrationNativeRelatedFamily (Message)
open RegistrationNativeSelectiveHiddenService (State selected known)
open RegistrationNativeHiddenService (coins reserve)
open RegistrationNativeG3AuditedWorld (Seeds)
open RegistrationNativeKeyCompiler (KeySpec)
variable {n : Nat} {Value : Type}

def complete (materials : Slot n → Material) (before : State n) : State n :=
  ({ before.1 with materials := ⟨fun slot => some (materials slot)⟩ }, before.2)

noncomputable def fixedKeys (materials : Slot n → Material) (seeds : Seeds n)
    (inside : Pqxdh.Bytes → Bool) (candidate : PqxdhKemIndCca.MlKemSharedSecret) :
    QueryImpl KeySpec (StateT (State n) (OracleComp (EnvEffects n)))
  | .inl coin => StateT.lift (coins coin)
  | .inr bytes => fun before =>
      if selected inside candidate bytes then
        match reserve bytes before.1 with
        | (some slot, after) => pure (joinOutput (materials slot) (seeds slot), (after, before.2))
        | (none, after) => pure ((List.Vector.replicate 76 0, List.Vector.replicate 32 0), (after, before.2))
      else (known bytes).run before

def count : RegistrationNativeRetainedService.Spec.Domain → State n → State n
  | .inr (.demand _), before => ({ before.1 with demands := before.1.demands + 1 }, before.2)
  | _, before => before

noncomputable def direct (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (input : Message → Option Pqxdh.Bytes) (inside : Pqxdh.Bytes → Bool)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret) (materials : Slot n → Material) (seeds : Seeds n) :
    QueryImpl RegistrationNativeRetainedService.Spec (StateT (State n) (OracleComp (EnvEffects n))) := fun query before =>
  let current := count query before
  (fun result => (result.1.1, ({ result.2.1 with prepared := result.1.2 }, result.2.2))) <$>
    (simulateQ (fixedKeys materials seeds inside candidate)
      ((RegistrationNativeG3KeyService.direct source input inside query).run current.1.prepared)).run current

/-- Fixed material completion retains every actual descriptor flag, slot, cursor, demand counter and nonselected known108 cache. -/
theorem complete_fields (materials : Slot n → Material) (before : State n) :
    (complete materials before).1.prepared = before.1.prepared ∧
      (complete materials before).1.slots = before.1.slots ∧ (complete materials before).1.next = before.1.next ∧
      (complete materials before).1.demands = before.1.demands ∧ (complete materials before).2 = before.2 := by
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- Re-completing the material cache is idempotent and has no probabilistic or World effect. -/
theorem complete_idempotent (materials : Slot n → Material) (before : State n) :
    complete materials (complete materials before) = complete materials before := rfl

/-- The actual allocator uses exactly the same full input and slot before and after material completion, including overflow. -/
theorem reserve_complete (materials : Slot n → Material) (bytes : Pqxdh.Bytes)
    (before : RegistrationNativeHiddenService.State n) :
    reserve bytes (complete materials (before, (∅ : RegistrationNativeSelectiveHiddenService.KnownOracle.QueryCache))).1 =
      let result := reserve bytes before
      (result.1, (complete materials (result.2, (∅ : RegistrationNativeSelectiveHiddenService.KnownOracle.QueryCache))).1) := by
  unfold reserve complete
  cases before.slots bytes <;> simp only
  split <;> rfl

/-- Every selected material lookup in the completed cache returns the actual fixed44 value without an extra draw. -/
theorem material_complete (materials : Slot n → Material) (slot : Slot n) (before : RegistrationNativeHiddenService.State n) :
    (RegistrationNativeHiddenService.material slot).run
      (complete materials (before, (∅ : RegistrationNativeSelectiveHiddenService.KnownOracle.QueryCache))).1 =
      pure (materials slot, (complete materials (before, (∅ : RegistrationNativeSelectiveHiddenService.KnownOracle.QueryCache))).1) :=
  RegistrationNativeHiddenService.material_hit slot _ _ rfl

end BeaconcryptCore.Computational.RegistrationNativeG3SelectiveService
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3SelectiveService.complete_fields' does not depend on any axioms -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3SelectiveService.complete_fields
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3SelectiveService.complete_idempotent' does not depend on any axioms -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3SelectiveService.complete_idempotent
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3SelectiveService.reserve_complete' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3SelectiveService.reserve_complete
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3SelectiveService.material_complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3SelectiveService.material_complete
