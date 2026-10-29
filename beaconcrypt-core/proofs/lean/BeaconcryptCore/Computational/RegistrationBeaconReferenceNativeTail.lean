-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationBeaconReferenceNativeRecord
import BeaconcryptCore.Computational.RegistrationBeaconReferenceCompletion

/-! The native finishing tail installs precisely the completed sequence-one kernel before changing the local public phase. Its source and public-service forms have the same install/abort effects on every failure path; the public tail needs only the scalar-free owner view. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationBeaconReferenceNativeTail
open RegistrationNativeBeaconFrontend (Owner State M effect updatePhase)
open RegistrationBeaconReferenceCompiler (SelectedOwner eraseOwner)
open RegistrationBeaconReferenceNativeRecord (environment)
variable {n : Nat} {KemSK Auxiliary : Type} {mlSource : RegistrationNativeMldsa.Source}

/-- This is the actual branch after the extracted first-record controller returns. -/
def after (index : Nat) (owner : Owner mlSource) :
    RustM RegistrationBeaconRecordExecutor.Result → M n KemSK mlSource Auxiliary (RustM (Option Pqxdh.Bytes))
  | .fail error => RegistrationNativeBeaconFrontend.abort owner *> pure (.fail error)
  | .div => RegistrationNativeBeaconFrontend.abort owner *> pure .div
  | .ok (.Err _) => RegistrationNativeBeaconFrontend.abort owner *> pure (.ok none)
  | .ok (.Ok established) => do
      let shell : PqxdhRecordLiftInterface.BeaconShell :=
        ⟨owner.pin.binding.identity_key_id, established.control, established.binding.associated_data⟩
      let installed : Bool ← effect (.inr (.installBeacon owner.worldOwner shell (.known established.kernel)))
      if installed then
        updatePhase index (.established ⟨established.control, established.binding, established.application⟩)
        pure (.ok (some (TranscriptAuthParts.absSlice established.application)))
      else RegistrationNativeBeaconFrontend.abort owner *> pure (.ok none)

def abort (owner : SelectedOwner mlSource) : M n KemSK mlSource Auxiliary Unit := do
  let _ ← effect (.inr (.advanceOwner owner.worldOwner .aborted))
  pure ()

def settle (index : Nat) (owner : SelectedOwner mlSource) :
    RustM RegistrationNativePairedBeaconService.Result → M n KemSK mlSource Auxiliary (RustM (Option Pqxdh.Bytes))
  | .fail error => abort owner *> pure (.fail error)
  | .div => abort owner *> pure .div
  | .ok (.Err _) => abort owner *> pure (.ok none)
  | .ok (.Ok completed) => do
      updatePhase index (.established completed)
      pure (.ok (some (TranscriptAuthParts.absSlice completed.application)))

def compiled (index : Nat) (owner : SelectedOwner mlSource) (result : RustM RegistrationBeaconRecordExecutor.Result) :
    M n KemSK mlSource Auxiliary (RustM (Option Pqxdh.Bytes)) := do
  let completed ← StateT.lift (StateT.lift (simulateQ environment
    (RegistrationNativePairedBeaconService.after owner.worldOwner owner.pin.binding.identity_key_id
      (fun value => .known value.kernel) result)))
  settle index owner completed

/-- Every concrete source failure and successful consumed-kernel insertion agrees with the scalar-free service tail. -/
theorem after_exact (index : Nat) (owner : Owner mlSource) (result : RustM RegistrationBeaconRecordExecutor.Result) :
    after (n := n) (KemSK := KemSK) (Auxiliary := Auxiliary) index owner result =
      compiled index (eraseOwner owner) result := by
  cases result with
  | fail error => rfl
  | div => rfl
  | ok answer => cases answer with
    | Err aborted => rfl
    | Ok established =>
        apply StateT.ext
        intro owners
        apply StateT.ext
        intro env
        simp only [after, compiled, settle, RegistrationNativePairedBeaconService.after,
          simulateQ_map, simulateQ_spec_query, environment,
          effect, eraseOwner, StateT.run_bind, StateT.run_lift,
          bind_pure_comp, bind_map_left]
        apply bind_congr
        intro installed
        cases installed <;> rfl

/-- Native insertion and terminal abort do not inspect or change the projected record-request ledger. -/
theorem after_project (index : Nat) (owner : Owner mlSource) (result : RustM RegistrationBeaconRecordExecutor.Result)
    (before : RegistrationBeaconReferenceNativeRecord.Flat mlSource Auxiliary) :
    (fun value => (value.1.1, (value.1.2, RegistrationBeaconReferenceNativeRecord.erase value.2))) <$>
      ((after (n := n) (KemSK := KemSK) index owner result).run before.1).run before.2 =
      (fun value => (value.1.1, (value.1.2, value.2))) <$>
        ((compiled index (eraseOwner owner) result).run before.1).run
          (RegistrationBeaconReferenceNativeRecord.erase before.2) := by
  rw [← after_exact]
  cases result with
  | fail error | div => rfl
  | ok answer => cases answer with
    | Err aborted => rfl
    | Ok established =>
        simp only [after, effect, StateT.run_bind, StateT.run_lift,
          bind_pure_comp, bind_map_left, map_bind, RegistrationBeaconReferenceNativeRecord.erase]
        apply bind_congr
        intro installed
        cases installed <;> rfl

abbrev PostSpec := RegistrationRecordPrimitives.Spec +
  (RustM RegistrationBeaconRecordExecutor.Result →ₒ RustM (Option Pqxdh.Bytes))

def recordLift : QueryImpl RegistrationRecordPrimitives.Spec (OracleComp PostSpec) :=
  fun query => PostSpec.query (.inl query)

def program (agreement : agreement.BeaconAgreement) : OracleComp PostSpec (RustM (Option Pqxdh.Bytes)) := do
  let result ← simulateQ recordLift (RegistrationBeaconRecordExecutor.begin agreement)
  PostSpec.query (.inr result)

noncomputable def source {ι : Type} {base : OracleSpec ι} (setup : PqxdhServerAuthExperiment.Setup base KemSK)
    (wire : RegistrationNativeWire.Wire) (index : Nat) (owner : Owner mlSource) :
    QueryImpl PostSpec (StateT (RegistrationBeaconReferenceNativeRecord.Flat mlSource Auxiliary)
      (OracleComp (RegistrationNativeBeaconFrontend.Trusted n KemSK)))
  | .inl query => (RegistrationNativeBeaconFrontend.record setup wire).flattenStateT query
  | .inr result => fun before => (fun value => (value.1.1, (value.1.2, value.2))) <$>
      ((after index owner result).run before.1).run before.2

noncomputable def target {ι : Type} {base : OracleSpec ι} (setup : PqxdhServerAuthExperiment.Setup base KemSK)
    (wire : RegistrationNativeWire.Wire) (index : Nat) (owner : SelectedOwner mlSource) :
    QueryImpl PostSpec (StateT (RegistrationBeaconReferenceNativeRecord.Flat mlSource Auxiliary)
      (OracleComp (RegistrationNativeBeaconFrontend.Trusted n KemSK)))
  | .inl query => RegistrationBeaconReferenceNativeRecord.target setup wire query
  | .inr result => fun before => (fun value => (value.1.1, (value.1.2, value.2))) <$>
      ((compiled index owner result).run before.1).run before.2

noncomputable def postRoot {ι : Type} {base : OracleSpec ι} (setup : PqxdhServerAuthExperiment.Setup base KemSK)
    (wire : RegistrationNativeWire.Wire) (index : Nat) (owner : Owner mlSource)
    (agreement : agreement.BeaconAgreement) : M n KemSK mlSource Auxiliary (RustM (Option Pqxdh.Bytes)) := do
  let opened ← simulateQ (RegistrationNativeBeaconFrontend.record setup wire)
    (RegistrationBeaconRecordExecutor.begin agreement)
  after index owner opened

/-- The source component is the literal native record execution followed by its actual insertion/abort branch. -/
theorem program_source {ι : Type} {base : OracleSpec ι} (setup : PqxdhServerAuthExperiment.Setup base KemSK)
    (wire : RegistrationNativeWire.Wire) (index : Nat) (owner : Owner mlSource)
    (agreement : agreement.BeaconAgreement) (before : RegistrationBeaconReferenceNativeRecord.Flat mlSource Auxiliary) :
    (simulateQ (source (n := n) setup wire index owner) (program agreement)).run before =
      (fun value => (value.1.1, (value.1.2, value.2))) <$>
        ((postRoot setup wire index owner agreement).run before.1).run before.2 := by
  have restriction : source (n := n) (Auxiliary := Auxiliary) setup wire index owner ∘ₛ recordLift =
      (RegistrationNativeBeaconFrontend.record (n := n) setup wire).flattenStateT := by
    funext query
    simp only [QueryImpl.compose, recordLift, simulateQ_spec_query, source]
  simp only [program, simulateQ_bind, StateT.run_bind, simulateQ_spec_query]
  rw [← QueryImpl.simulateQ_compose, restriction, OracleComp.simulateQ_flattenStateT_run]
  simp only [postRoot, StateT.run_bind, bind_map_left, bind_pure_comp, map_bind,
    source]
  rfl

private theorem post_query {ι : Type} {base : OracleSpec ι} (setup : PqxdhServerAuthExperiment.Setup base KemSK)
    (wire : RegistrationNativeWire.Wire) (index : Nat) (owner : Owner mlSource) (query : PostSpec.Domain)
    (before : RegistrationBeaconReferenceNativeRecord.Flat mlSource Auxiliary) :
    Prod.map id RegistrationBeaconReferenceNativeRecord.project <$> (source (n := n) setup wire index owner query).run before =
      (target setup wire index (eraseOwner owner) query).run (RegistrationBeaconReferenceNativeRecord.project before) := by
  cases query with
  | inl query =>
      simpa only [simulateQ_spec_query, source, target] using RegistrationBeaconReferenceNativeRecord.program setup wire
        (RegistrationRecordPrimitives.Spec.query query : OracleComp RegistrationRecordPrimitives.Spec _) before
  | inr result =>
      simpa only [source, target, QueryImpl.flattenStateT, StateT.run, StateT.mk,
        Functor.map_map, Prod.map_def, id_eq, RegistrationBeaconReferenceNativeRecord.project,
        Function.comp_def] using after_project (n := n) (KemSK := KemSK) index owner result before

/-- The whole actual post-root finishing component has the same opening, consumed-kernel insertion and terminal failures as its native public service form. -/
theorem post_root {ι : Type} {base : OracleSpec ι} (setup : PqxdhServerAuthExperiment.Setup base KemSK)
    (wire : RegistrationNativeWire.Wire) (index : Nat) (owner : Owner mlSource)
    (agreement : agreement.BeaconAgreement) (before : RegistrationBeaconReferenceNativeRecord.Flat mlSource Auxiliary) :
    Prod.map id RegistrationBeaconReferenceNativeRecord.project <$>
      (simulateQ (source (n := n) setup wire index owner) (program agreement)).run before =
      (simulateQ (target setup wire index (eraseOwner owner)) (program agreement)).run
        (RegistrationBeaconReferenceNativeRecord.project before) :=
  OracleComp.map_run_simulateQ_eq_of_query_map_eq _ _ RegistrationBeaconReferenceNativeRecord.project
    (post_query setup wire index owner) (program agreement) before

end BeaconcryptCore.Computational.RegistrationBeaconReferenceNativeTail

/-- info: 'BeaconcryptCore.Computational.RegistrationBeaconReferenceNativeTail.after_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationBeaconReferenceNativeTail.after_exact

/-- info: 'BeaconcryptCore.Computational.RegistrationBeaconReferenceNativeTail.after_project' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationBeaconReferenceNativeTail.after_project

/-- info: 'BeaconcryptCore.Computational.RegistrationBeaconReferenceNativeTail.program_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationBeaconReferenceNativeTail.program_source

/-- info: 'BeaconcryptCore.Computational.RegistrationBeaconReferenceNativeTail.post_root' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationBeaconReferenceNativeTail.post_root
