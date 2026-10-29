-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeKemStoppedSdk

/-! The actual selected-attempt wrapper reads the retained private parsed counter before incrementing it. A successful literal SDK accept therefore reaches getter zero for that selected attempt, with its entire source context retained. The successful session is an output and is never substituted for the selector. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeParsedTargetCut
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeKemParsedRouting (Spec source handler)
open RegistrationNativeKemAcceptCompiler (nativeProject)
open RegistrationNativeWire (Wire)
open RegistrationNativeKemCut (Cut scan)
variable {n : Nat} {ι KemSK : Type} {base : OracleSpec ι} {mlSource : RegistrationNativeMldsa.Source}

private theorem source_get (setup : Setup base KemSK) (checks : Checks) (wire : Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (credential : RegistrationNativeMldsa.Credential mlSource)
    (before : RegistrationNativeExperiment.State n KemSK mlSource) :
    (source setup checks wire route representation created credential (.inl (.inl (.inl .get)))).run (nativeProject before) =
      pure ((nativeProject before).1, nativeProject before) := by
  simp only [source, RegistrationNativeKemParsedRouting.other,
    RegistrationNativeKemRouting.publicAmbient, RegistrationNativeKemInterface.source,
    RegistrationNativeKemFrontendInterface.other, RegistrationNativeKemServerInterface.other,
    StateT.run, map_pure, nativeProject, RegistrationNativeKemServerState.project,
    RegistrationNativeKemServerState.mask_idempotent]

/-- Getter zero of the actual selected parsed attempt is the literal native SDK getter-zero cut. -/
theorem selected_scan (setup : Setup base KemSK) (checks : Checks) (wire : Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (credential : RegistrationNativeMldsa.Credential mlSource)
    (packet : registration.InitPacket) (selected : Nat)
    (before : RegistrationNativeExperiment.State n KemSK mlSource) (counter : before.parsedAccepts = selected) :
    (scan (source setup checks wire route representation created credential)
      (handler setup checks wire selected (.inr (.accept packet))) 0).run (nativeProject before) =
    (scan (source setup checks wire route representation created credential)
      (simulateQ (RegistrationNativeKemRouting.route true) (simulateQ RegistrationNativeKemFrontendInterface.lift
        (RegistrationNativeKemServerInterface.typedAccept setup checks packet))) 0).run (nativeProject before) := by
  unfold handler RegistrationNativeKemParsedRouting.get
  rw [RegistrationNativeKemCut.scan_other, StateT.run_bind, source_get, pure_bind]
  simp only [nativeProject, RegistrationNativeKemServerState.project, RegistrationNativeKemServerState.mask,
    RegistrationNativeKemServerState.ofNative, counter, decide_true, RegistrationNativeKemDispatcherCompiler.handler]

attribute [local irreducible] RegistrationNativeKemParsedRouting.source RegistrationNativeKemParsedRouting.handler
  RegistrationNativeExperiment.handler

/-- A selected successful session cannot be a completed cut before its first actual encapsulation getter. -/
theorem selected_complete_impossible (setup : Setup base KemSK) (checks : Checks) (wire : Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (credential : RegistrationNativeMldsa.Credential mlSource)
    (packet : registration.InitPacket) (selected session : Nat)
    (before : RegistrationNativeExperiment.State n KemSK mlSource) (counter : before.parsedAccepts = selected)
    (after : RegistrationNativeKemServerState.State n mlSource × PqxdhLiveKemBirth.Pool KemSK)
    (supported : (.complete (.ok (some session)), after) ∈ support
      ((scan (source setup checks wire route representation created credential)
        (handler setup checks wire selected (.inr (.accept packet))) 0).run (nativeProject before))) : False := by
  rw [selected_scan setup checks wire route representation created credential packet selected before counter] at supported
  exact RegistrationNativeKemStoppedSdk.completed_accept_impossible setup checks packet _ session _ after supported

/-- Every actually successful chosen SDK call suspends at its literal encapsulation getter with a concrete reached context. -/
theorem selected_pending (setup : Setup base KemSK) (checks : Checks) (wire : Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (credential : RegistrationNativeMldsa.Credential mlSource)
    (packet : registration.InitPacket) (selected session : Nat)
    (before after : RegistrationNativeExperiment.State n KemSK mlSource) (counter : before.parsedAccepts = selected)
    (supported : (.ok (some session), after) ∈ support
      ((RegistrationNativeExperiment.handler setup checks wire route representation created mlSource credential
        (.inr (.accept packet))).run before)) :
    ∃ key next reached, (.pending key next, reached) ∈ support
      ((scan (source setup checks wire route representation created credential)
        (handler setup checks wire selected (.inr (.accept packet))) 0).run (nativeProject before)) := by
  have compiled : (.ok (some session), nativeProject after) ∈ support
      ((simulateQ (source setup checks wire route representation created credential)
        (handler setup checks wire selected (.inr (.accept packet)))).run (nativeProject before)) := by
    rw [← RegistrationNativeKemParsedRouting.handler_source, support_map]
    exact Set.mem_image_of_mem (Prod.map id nativeProject) supported
  rw [← RegistrationNativeKemCut.scan_finish _ _ 0, StateT.run_bind, mem_support_bind_iff] at compiled
  obtain ⟨cut, reached, continued⟩ := compiled
  rcases cut with ⟨cut, state⟩
  cases cut with
  | complete result =>
      simp only [RegistrationNativeKemCut.finish, StateT.run_pure, mem_support_pure_iff,
        Prod.mk.injEq] at continued
      obtain ⟨rfl, _same⟩ := continued
      exact False.elim (selected_complete_impossible setup checks wire route representation created credential
        packet selected session before counter state reached)
  | pending key next => exact ⟨key, next, state, reached⟩

end BeaconcryptCore.Computational.RegistrationNativeParsedTargetCut

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeParsedTargetCut.selected_scan' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeParsedTargetCut.selected_scan
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeParsedTargetCut.selected_complete_impossible' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeParsedTargetCut.selected_complete_impossible
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeParsedTargetCut.selected_pending' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeParsedTargetCut.selected_pending
