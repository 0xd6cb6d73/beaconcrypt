-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeScalarProgram

/-! The scalar interchange applies to the actual original raw/private secrecy execution and generated native startup. The original hidden bit, fresh-message list, raw transcript and complete source poststate are retained; no constructor-success or whole-game simulation premise is added. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeScalarRun
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeExperiment (State Initial Public)
variable {n : Nat} {ι KemSK Value : Type} {base : OracleSpec ι}

/-- Scalar interchange preserves the entire original raw/secrecy ledger and source poststate for every mode. -/
theorem run (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (source : RegistrationNativeMldsa.Source)
    (credential : RegistrationNativeMldsa.Credential source) (selected : Nat)
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value) (before : State n KemSK source)
    (short : before.beacons.length ≤ selected) :
    RegistrationNativeExperiment.run setup checks wire route representation created source credential bounds mode work before =ᵈ
      (do let scalar ← PqxdhJointGapDh.sampleScalar
          RegistrationNativeScalarEager.run setup checks wire route representation created source credential selected scalar bounds mode work before) := by
  simp only [RegistrationNativeExperiment.run, RegistrationNativeScalarEager.run, RegistrationNativeFullCompiler.compile_run]
  have moved := (RegistrationNativeScalarProgram.eager setup checks wire route representation created credential selected
    (RegistrationNativeFullCompiler.compile setup.source.crypto wire created.server.server.metadata.sender bounds mode work) before short).map
      (fun result => (result.1.1, (result.1.2, result.2)))
  simpa only [map_bind] using moved

/-- Actual generated native startup has an empty source roster, including every retained constructor/ML/initialization branch. -/
theorem start_empty (setup : Setup base KemSK) (source : RegistrationNativeMldsa.Source)
    (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64)
    (initial : Initial n KemSK source)
    (supported : some initial ∈ support (RegistrationNativeExperiment.start setup source ensureInit identityIndex serverKeyId)) :
    initial.state.beacons = [] := by
  unfold RegistrationNativeExperiment.start at supported
  rw [mem_support_bind_iff] at supported
  obtain ⟨constructed, _built, continued⟩ := supported
  cases built : constructed.1.1 with
  | none => simp only [built, support_pure, Set.mem_singleton_iff] at continued; cases continued
  | some created =>
      rw [built, mem_support_bind_iff] at continued
      obtain ⟨generated, _sampled, continued⟩ := continued
      cases chosen : generated.1 with
      | none => simp only [chosen, support_pure, Set.mem_singleton_iff] at continued; cases continued
      | some credential =>
          rw [chosen, mem_support_bind_iff] at continued
          obtain ⟨initialized, _native, continued⟩ := continued
          split at continued
          · simp only [support_pure, Set.mem_singleton_iff, Option.some.injEq] at continued
            cases continued
            rfl
          · simp only [support_pure, Set.mem_singleton_iff] at continued
            cases continued

/-- Actual original generated-startup profile equals the concrete private early-scalar profile for every public adversary and complete original observation. -/
theorem profile (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (source : RegistrationNativeMldsa.Source) (ensureInit : StateT Unit ProbComp Bool)
    (identityIndex : Nat) (serverKeyId : U64) (selected : Nat)
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (adversary : Public → OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (event : RegistrationNativeEvents.Observed Value (State n KemSK source) → Bool) :
    RegistrationNativeExperiment.profile setup checks wire route representation source ensureInit identityIndex serverKeyId bounds mode adversary event =ᵈ
      RegistrationNativeScalarEager.profile setup checks wire route representation source ensureInit identityIndex serverKeyId selected bounds mode adversary event := by
  unfold RegistrationNativeExperiment.profile RegistrationNativeScalarEager.profile
  refine _root_.EvalDistEq.trans ?_ (OracleComp.EvalDistEq.bind_bind_swap PqxdhJointGapDh.sampleScalar
    (RegistrationNativeExperiment.start setup source ensureInit identityIndex serverKeyId)
    (fun scalar initialized => match initialized with
      | none => pure false
      | some initial => event <$> RegistrationNativeScalarEager.run setup checks wire route representation initial.created source initial.credential
          selected scalar bounds mode (adversary initial.public) initial.state)).symm
  apply OracleComp.EvalDistEq.bind_congr_of_support
  intro initialized supported
  cases initialized with
  | none => exact (OracleComp.EvalDistEq.bind_const _ _).symm
  | some initial =>
      have short : initial.state.beacons.length ≤ selected := by
        rw [start_empty setup source ensureInit identityIndex serverKeyId initial supported]
        simp only [List.length_nil, Nat.zero_le]
      simpa only [map_bind] using
        (run setup checks wire route representation initial.created source initial.credential selected bounds mode
          (adversary initial.public) initial.state short).map event

end BeaconcryptCore.Computational.RegistrationNativeScalarRun

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeScalarRun.run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeScalarRun.run
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeScalarRun.start_empty' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeScalarRun.start_empty
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeScalarRun.profile' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeScalarRun.profile
