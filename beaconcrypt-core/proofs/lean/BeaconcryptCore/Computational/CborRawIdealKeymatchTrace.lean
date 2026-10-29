-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.CborRawIdealKeymatchNative

/-! The actual public native raw handler preserves the selected-key trace on the original transcript. Refused records are complete-state quiet steps; delegated registration is proved with its actual source codec and then transported across the single public entry. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.CborRawIdealKeymatchTrace
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhDeploymentInterface (Entry Spec)
open PqxdhDeploymentIdealParams (Target Params)
open PqxdhDeploymentIdealKeymatch (KeyTrace Quiet)
open CborRawPublicState (Public)
open CborRawMiddleSimulation (Native)
open CborRawIdealBeaconTrace (EntryRel)
variable {ι KemSK Reader Response : Type} {baseSpec : OracleSpec ι}

/-- The public adaptation of a full native request has exactly the proved raw/canonical entry relation. -/
theorem public_entry (state : Public) (query : Spec.Domain)
    (reply : Spec.Range (CborRawPublicClient.request state query)) :
    EntryRel ⟨.inl query, CborRawPublicClient.reply state query reply⟩
      ⟨.inl (CborRawPublicClient.request state query), reply⟩ := by
  rcases query with coin | command
  · exact .same _ rfl
  · cases command with
    | build session payload => exact .build _ _ _ _
    | finish owner bytes => exact .finish _ _ _ _
    | _ => exact .same _ rfl

section Trace
variable (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks) {count : Nat}
    (target : Target count) (parameters : Params KemSK count)

/-- Removing entries cannot add an accept or bundle witness or alter a state fact. -/
theorem restrict (before after : List Entry) (contained : ∀ entry ∈ before, entry ∈ after)
    (base : PqxdhDeploymentNative.State KemSK) (core : PqxdhDeploymentIdealSteps.IdealCore)
    (holds : KeyTrace setup codec checks target parameters after base core) :
    KeyTrace setup codec checks target parameters before base core :=
  ⟨holds.sessions, fun raw session member => holds.below raw session (contained _ member),
    fun raw member => holds.selected raw (contained _ member), holds.owners,
    fun owner bytes member => holds.bundles owner bytes (contained _ member)⟩

/-- Only the unchanged accept and bundle witnesses of the newly appended entry are used by the key trace. -/
theorem append_transport (transcript : List Entry) (raw canonical : Entry) (related : EntryRel raw canonical)
    (base : PqxdhDeploymentNative.State KemSK) (core : PqxdhDeploymentIdealSteps.IdealCore)
    (holds : KeyTrace setup codec checks target parameters (transcript ++ [canonical]) base core) :
    KeyTrace setup codec checks target parameters (transcript ++ [raw]) base core := by
  have accepted : ∀ bytes reply, (⟨.inl (.inr (.accept bytes)), reply⟩ : Entry) ∈ transcript ++ [raw] ↔
      (⟨.inl (.inr (.accept bytes)), reply⟩ : Entry) ∈ transcript ++ [canonical] := by
    intro bytes reply
    simp only [List.mem_append, List.mem_singleton, eq_comm,
      CborRawIdealBeaconTrace.entry_accept raw canonical related bytes reply]
  have bundled : ∀ owner reply, (⟨.inl (.inr (.bundle owner)), reply⟩ : Entry) ∈ transcript ++ [raw] ↔
      (⟨.inl (.inr (.bundle owner)), reply⟩ : Entry) ∈ transcript ++ [canonical] := by
    intro owner reply
    simp only [List.mem_append, List.mem_singleton, eq_comm,
      CborRawIdealBeaconTrace.entry_bundle raw canonical related owner reply]
  exact ⟨holds.sessions, fun raw session member => holds.below raw session ((accepted _ _).mp member),
    fun raw member => holds.selected raw ((accepted _ _).mp member), holds.owners,
    fun owner bytes member => holds.bundles owner bytes ((bundled _ _).mp member)⟩

end Trace
section Native
variable (setup : Setup baseSpec KemSK) (wire : Codec Reader Response)
    (parse : Pqxdh.Bytes → Option CborProductionBoundary.NativeFrame) (checks : Checks) {count : Nat}
    (target : Target count) (parameters : Params KemSK count) (created : PqxdhLiveServerConstruction.Created Unit)

theorem guarded_trace (query : Spec.Domain) (transcript : List Entry) (state : Native KemSK)
    (holds : KeyTrace setup (CborRawCompile.sourceCodec wire parse) checks target parameters transcript state.base
      state.backend.2.2) (result : Spec.Range query × Native KemSK)
    (member : result ∈ support ((CborRawGuardedJoin.nativeHandler setup (CborTaggedSimulation.boundaryWire wire parse)
      (CborRawCompile.route parse) (PqxdhDeploymentIdealSteps.idealReg setup (CborRawCompile.sourceCodec wire parse)
        (CborRawCompile.route parse) checks target parameters created) query).run state)) :
    KeyTrace setup (CborRawCompile.sourceCodec wire parse) checks target parameters
      (transcript ++ [⟨.inl query, result.1⟩]) result.2.base result.2.backend.2.2 := by
  cases refused : CborRawGuardedJoin.refusal (n := 2) query (CborRecordNativeAdmission.nativeShell state.base) with
  | none =>
      simp only [CborRawGuardedJoin.nativeHandler, StateT.run, refused] at member
      exact CborRawIdealKeymatchNative.mixed_handler_trace setup (CborRawCompile.sourceCodec wire parse)
        (CborRawCompile.route parse) checks target parameters (CborTaggedSimulation.boundaryWire wire parse) created
        query transcript state holds result member
  | some reply =>
      simp only [CborRawGuardedJoin.nativeHandler, StateT.run, refused, support_pure, Set.mem_singleton_iff] at member
      subst member
      have quiet : Quiet (.inl query) := by
        rcases query with coin | command
        · cases refused
        · cases command <;> first | trivial | cases refused
      exact PqxdhDeploymentIdealKeymatch.keyTrace_quiet setup (CborRawCompile.sourceCodec wire parse) checks target
        parameters transcript state.base state.base state.backend.2.2 state.backend.2.2 holds (.inl query) quiet reply
          rfl holds.owners rfl rfl

/-- Every actual native raw step appends its original public query and optional reply to the key trace. -/
theorem handler_trace (query : Spec.Domain) (transcript : List Entry) (state : Public × Native KemSK)
    (holds : KeyTrace setup (CborRawCompile.sourceCodec wire parse) checks target parameters transcript state.2.base
      state.2.backend.2.2) (result : Spec.Range query × (Public × Native KemSK))
    (member : result ∈ support ((CborRawNativePublic.native setup wire parse checks target parameters created query).run
      state)) :
    KeyTrace setup (CborRawCompile.sourceCodec wire parse) checks target parameters
      (transcript ++ [⟨.inl query, result.1⟩]) result.2.2.base result.2.2.backend.2.2 := by
  rw [CborRawNativePublic.native, CborRawEnvironmentRun.handler_run, support_map] at member
  obtain ⟨inner, reached, rfl⟩ := member
  exact append_transport setup (CborRawCompile.sourceCodec wire parse) checks target parameters transcript _ _
    (public_entry state.1 query inner.1) inner.2.base inner.2.backend.2.2
    (guarded_trace setup wire parse checks target parameters created (CborRawPublicClient.request state.1 query)
      transcript state.2 holds inner reached)

end Native
end BeaconcryptCore.Computational.CborRawIdealKeymatchTrace

/-- info: 'BeaconcryptCore.Computational.CborRawIdealKeymatchTrace.public_entry' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawIdealKeymatchTrace.public_entry
/-- info: 'BeaconcryptCore.Computational.CborRawIdealKeymatchTrace.restrict' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawIdealKeymatchTrace.restrict
/-- info: 'BeaconcryptCore.Computational.CborRawIdealKeymatchTrace.append_transport' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawIdealKeymatchTrace.append_transport
/-- info: 'BeaconcryptCore.Computational.CborRawIdealKeymatchTrace.guarded_trace' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawIdealKeymatchTrace.guarded_trace
/-- info: 'BeaconcryptCore.Computational.CborRawIdealKeymatchTrace.handler_trace' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawIdealKeymatchTrace.handler_trace
