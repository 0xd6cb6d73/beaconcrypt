-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeBeaconFrontend
import BeaconcryptCore.Computational.RegistrationNativePlatformBeaconPublication
import BeaconcryptCore.Computational.RegistrationNativePlatformWriter

/-! The logical native Beacon bundle runs its writer inside the existing owners/environment StateT stack at the actual Core Ready stage. Crypto, shared receipts, Ed histories, optional supplied coins and owner publication transitions remain those of the original native controller. The pure wire is a proved specialization; arbitrary platform state is not equated to that static model or to the full Rust wrapper. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformBundle
open PqxdhServerAuthExperiment (Setup)
open RegistrationNativeBeaconFrontend (M Owner)
open RegistrationNativeWire (Wire)
variable {ι KemSK Auxiliary : Type} {base : OracleSpec ι} {n : Nat}
variable {Encoded : Type}

noncomputable def bundle (setup : Setup base KemSK) (source : RegistrationNativeMldsa.Source)
    (encode : registration.InitView → M n KemSK source Auxiliary (RustM (core.option.Option Encoded)))
    (index : Nat) : M n KemSK source Auxiliary (RustM (Option Encoded)) := do
  let owners ← get
  match owners[index]? with
  | none => pure (.ok none)
  | some owner =>
    let selected : Option (Option PqxdhJointGapDh.ScalarBytes) := match owner.phase with
      | .fresh => some none
      | .freshWithCoins scalar => some (some scalar)
      | _ => none
    match selected with
    | none => pure (.ok none)
    | some supplied => do
      let oneTime ← match supplied with
        | some scalar => pure scalar
        | none => RegistrationNativeBeaconFrontend.sample PqxdhJointGapDh.sampleScalar
      let published ← RegistrationNativePlatformBeaconPublication.begin
        (RegistrationNativeBeaconFrontend.outgoing setup source index owner) encode
        ⟨owner.pin.binding⟩ (RegistrationNativeBeaconFrontend.inputs setup owner)
        ⟨PqxdhRootTableInitialization.rootArray (setup.dh.publicKey oneTime)⟩ owner.pin
      match published with
      | .fail error => pure (.fail error)
      | .div => pure .div
      | .ok (.Err _) => pure (.ok none)
      | .ok (.Ok finished) => do
        RegistrationNativeBeaconFrontend.updatePhase index (.initSent finished.pending oneTime)
        let _ ← RegistrationNativeBeaconFrontend.effect (.inr (.advanceOwner owner.worldOwner .initSent))
        pure (.ok (some finished.encoded))

private theorem pure_publication (setup : Setup base KemSK) (source : RegistrationNativeMldsa.Source)
    (wire : Wire) (index : Nat) (owner : Owner source) (oneTime : PqxdhJointGapDh.ScalarBytes) :
    RegistrationNativePlatformBeaconPublication.begin
      (RegistrationNativeBeaconFrontend.outgoing (n := n) (Auxiliary := Auxiliary) setup source index owner)
      (fun view => pure (.ok (wire.encodeInit view)))
      ⟨owner.pin.binding⟩ (RegistrationNativeBeaconFrontend.inputs setup owner)
      ⟨PqxdhRootTableInitialization.rootArray (setup.dh.publicKey oneTime)⟩ owner.pin =
    simulateQ (RegistrationNativeBeaconFrontend.outgoing setup source index owner)
      (RegistrationBeaconInitExecutor.begin wire.encodeInit ⟨owner.pin.binding⟩
        (RegistrationNativeBeaconFrontend.inputs setup owner)
        ⟨PqxdhRootTableInitialization.rootArray (setup.dh.publicKey oneTime)⟩ owner.pin) := by
  rw [← RegistrationNativePlatformBeaconPublication.begin_pure,
    RegistrationNativePlatformBeaconPublication.begin_interpret]
  simp only [simulateQ_spec_query, simulateQ_pure]

attribute [local irreducible] RegistrationNativeBeaconFrontend.outgoing RegistrationBeaconInitExecutor.begin
  RegistrationNativeBeaconFrontend.sample

/-- The original logical native bundle is exactly the specialization with a pure successful writer action. -/
theorem bundle_pure (setup : Setup base KemSK) (source : RegistrationNativeMldsa.Source)
    (wire : Wire) (index : Nat) :
    bundle (n := n) (Auxiliary := Auxiliary) setup source
      (fun view => pure (.ok (wire.encodeInit view))) index =
      RegistrationNativeBeaconFrontend.bundle setup source wire index := by
  unfold bundle RegistrationNativeBeaconFrontend.bundle
  simp_rw [pure_publication]
  apply bind_congr
  intro owners
  cases owned : owners[index]? with
  | none => rfl
  | some owner =>
      cases phase : owner.phase <;> simp only [phase]
      all_goals
        apply bind_congr
        intro oneTime
        apply bind_congr
        intro published
        cases published with
        | fail error => rfl
        | div => rfl
        | ok result => cases result <;> rfl

def encoder {E : Type} {source : RegistrationNativeMldsa.Source}
    (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E)
      (M n KemSK source Auxiliary)) (view : registration.InitView) :=
  simulateQ writer (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestExtraction.encodeInit
    (E := E) (m := BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Program E)
    (RegistrationNativePlatformWriter.initPacket view)).run

noncomputable def joint {E : Type} (setup : Setup base KemSK) (source : RegistrationNativeMldsa.Source)
    (index : Nat) (owner : Owner source)
    (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E)
      (M n KemSK source Auxiliary)) :
    QueryImpl (RegistrationNativePlatformWriter.Spec E) (M n KemSK source Auxiliary)
  | .inl query => RegistrationNativeBeaconFrontend.outgoing setup source index owner query
  | .inr query => writer query

noncomputable def sourceBundle {E : Type} (setup : Setup base KemSK) (source : RegistrationNativeMldsa.Source)
    (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E)
      (M n KemSK source Auxiliary)) (index : Nat) :=
  bundle setup source (encoder writer) index

/-- Actual native signing and actual writer primitives share the current owner/environment state, including failed publication prefixes. -/
theorem source_publication {E : Type} (setup : Setup base KemSK) (source : RegistrationNativeMldsa.Source)
    (index : Nat) (owner : Owner source) (oneTime : PqxdhJointGapDh.ScalarBytes)
    (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E)
      (M n KemSK source Auxiliary)) :
    simulateQ (joint setup source index owner writer)
      (RegistrationNativePlatformWriter.begin E ⟨owner.pin.binding⟩
        (RegistrationNativeBeaconFrontend.inputs setup owner)
        ⟨PqxdhRootTableInitialization.rootArray (setup.dh.publicKey oneTime)⟩ owner.pin) =
      RegistrationNativePlatformBeaconPublication.begin
        (RegistrationNativeBeaconFrontend.outgoing setup source index owner) (encoder writer)
        ⟨owner.pin.binding⟩ (RegistrationNativeBeaconFrontend.inputs setup owner)
        ⟨PqxdhRootTableInitialization.rootArray (setup.dh.publicKey oneTime)⟩ owner.pin := by
  rw [RegistrationNativePlatformWriter.begin_interpret]
  rfl
end BeaconcryptCore.Computational.RegistrationNativePlatformBundle

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformBundle.bundle_pure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformBundle.bundle_pure

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformBundle.source_publication' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformBundle.source_publication
