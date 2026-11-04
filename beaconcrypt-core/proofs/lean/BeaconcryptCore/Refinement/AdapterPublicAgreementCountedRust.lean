-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.AdapterPublicWrapperRustT
import BeaconcryptCore.Computational.RegistrationAgreementSampledState
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
/-! Counting the original source Rust computation is a monad interpretation. Every failure and divergence stops the continuation after retaining the reached World counter; no source failure is erased. -/
namespace BeaconcryptCore.Refinement.AdapterPublicAgreementCountedRust
open AdapterPublicWrapperRustT (RustT)
open BeaconcryptCore.Computational RegistrationAgreementSampledState
variable {n : Nat} {A B : Type}

def counted (work : RustT ProbComp A) : RustT (StateT (PqxdhRecordLiftWorld.State n) ProbComp) A :=
  ⟨PqxdhRecordLiftWorld.sampled work.run⟩

theorem counted_pure (value : A) : counted (n := n) (pure value) = pure value := by
  apply RustT.ext
  funext world
  change (PqxdhRecordLiftWorld.sampled (pure (RustM.ok value : RustM A))).run world = _
  rw [sampled_pure]
  rfl

theorem counted_liftRust (result : RustM A) :
    counted (n := n) (AdapterRecordRequestMonad.liftRust result) = AdapterRecordRequestMonad.liftRust result := by
  apply RustT.ext
  funext world
  change (PqxdhRecordLiftWorld.sampled (pure result)).run world = _
  rw [sampled_pure]
  rfl

theorem counted_bind (work : RustT ProbComp A) (next : A → RustT ProbComp B) :
    counted (n := n) (work >>= next) = (counted work >>= fun value => counted (next value)) := by
  apply RustT.ext
  funext world
  change (PqxdhRecordLiftWorld.sampled (do
    let reply ← work.run
    match reply with
    | .ok value => (next value).run
    | .fail error => pure (.fail error)
    | .div => pure .div)).run world = _
  rw [sampled_bind]
  change (do
    let (reply, after) ← (PqxdhRecordLiftWorld.sampled work.run).run world
    (PqxdhRecordLiftWorld.sampled (match reply with
      | .ok value => (next value).run
      | .fail error => pure (.fail error)
      | .div => pure .div)).run after) = _
  simp only [RustT.run_bind]
  apply bind_congr
  rintro ⟨reply, after⟩
  cases reply <;> simp only [sampled_pure] <;> rfl

theorem counted_map (observe : A → B) (work : RustT ProbComp A) :
    counted (n := n) (observe <$> work) = observe <$> counted work := by
  rw [← bind_pure_comp, counted_bind]
  simp only [counted_pure, bind_pure_comp]
end BeaconcryptCore.Refinement.AdapterPublicAgreementCountedRust

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicAgreementCountedRust.counted_pure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicAgreementCountedRust.counted_pure

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicAgreementCountedRust.counted_liftRust' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicAgreementCountedRust.counted_liftRust

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicAgreementCountedRust.counted_bind' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicAgreementCountedRust.counted_bind

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicAgreementCountedRust.counted_map' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicAgreementCountedRust.counted_map
