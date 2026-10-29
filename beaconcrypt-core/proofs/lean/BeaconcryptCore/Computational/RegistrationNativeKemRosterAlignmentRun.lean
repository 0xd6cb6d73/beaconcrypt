-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeKemRosterAlignment
import BeaconcryptCore.Computational.RegistrationNativeStatePreservation

/-! Generated native startup establishes the current source's private-KEM/local-owner alignment, and every original raw-ledger continuation preserves it. The generic arbitrary-before run theorem retains its initial invariant premise; the initialized endpoint derives it from the actual constructor. This provides a single owner/creation coordinate for the KEM reduction without identifying unrelated World or Ed-identity handles. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeKemRosterAlignmentRun
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeExperiment (State Initial)
open RegistrationNativeKemRosterAlignment (Holds)
open RegistrationNativeRawAdapter (TypedSpec)
variable {ι KemSK Value : Type} {base : OracleSpec ι} {n : Nat} {source : RegistrationNativeMldsa.Source}
attribute [local irreducible] RegistrationServerSdkSource.accept

/-- Every actual typed source operation preserves the derived alignment, including all pre-birth constructor failures. -/
theorem handler_keeps (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (credential : RegistrationNativeMldsa.Credential source)
    (query : TypedSpec.Domain) (before : State n KemSK source) (result : TypedSpec.Range query × State n KemSK source)
    (prior : Holds before)
    (supported : result ∈ support ((RegistrationNativeExperiment.handler setup checks wire route representation created source credential query).run before)) :
    Holds result.2 := by
  have ordinary (valid : RegistrationNativeStatePreservation.Ordinary query) : Holds result.2 := by
    obtain ⟨pool, owners⟩ := RegistrationNativeStatePreservation.handler_keeps setup checks wire route representation created credential query valid before result supported
    simpa only [Holds, pool, owners] using prior
  cases query with
  | inl coin => exact ordinary trivial
  | inr command => cases command with
    | create edPin mlPin keyId => exact RegistrationNativeKemRosterAlignment.create_keeps setup checks representation created edPin mlPin keyId before result prior supported
    | bundle index => exact RegistrationNativeKemRosterAlignment.bundle_keeps setup checks representation created wire index before result prior supported
    | finish index packet => exact RegistrationNativeKemRosterAlignment.finish_keeps setup checks representation created wire index packet before result prior supported
    | _ => exact ordinary trivial

/-- Arbitrary actual original raw-ledger work preserves alignment from a supplied aligned source state. -/
theorem run_holds (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (credential : RegistrationNativeMldsa.Credential source)
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value) (before : State n KemSK source)
    (result : Value × (RegistrationNativeLedger.State × State n KemSK source)) (prior : Holds before)
    (supported : result ∈ support (RegistrationNativeExperiment.run setup checks wire route representation created source credential bounds mode work before)) :
    Holds result.2.2 := by
  unfold RegistrationNativeExperiment.run at supported
  rw [RegistrationNativeFullCompiler.compile_run, support_map] at supported
  obtain ⟨inner, reached, rfl⟩ := supported
  exact OracleComp.simulateQ_run_preserves_inv_of_query _ Holds
    (fun query current valid next member => handler_keeps setup checks wire route representation created credential query current next valid member)
    _ before prior inner reached

/-- Actual generated startup establishes the alignment with both source rosters empty. -/
theorem start_holds (setup : Setup base KemSK) (source : RegistrationNativeMldsa.Source)
    (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : Aeneas.Std.U64)
    (initial : Initial n KemSK source)
    (supported : some initial ∈ support (RegistrationNativeExperiment.start setup source ensureInit identityIndex serverKeyId)) :
    Holds initial.state := by
  simp only [RegistrationNativeExperiment.start, mem_support_bind_iff] at supported
  obtain ⟨constructed, _born, continued⟩ := supported
  cases constructor : constructed.1.1 with
  | none => simp [constructor] at continued
  | some created =>
      simp only [constructor, mem_support_bind_iff] at continued
      obtain ⟨generated, _sampled, continued⟩ := continued
      cases generation : generated.1 with
      | none => simp [generation] at continued
      | some credential =>
          simp only [generation, mem_support_bind_iff] at continued
          obtain ⟨initialized, _native, returned⟩ := continued
          cases native : initialized.1 with
          | fail error | div => simp [native] at returned
          | ok reply => cases reply with
            | none => simp [native] at returned
            | some state =>
                simp only [native, support_pure, Set.mem_singleton_iff, Option.some.injEq] at returned
                cases returned
                simp [Holds, PqxdhLiveKemBirth.empty]

/-- Every initialized actual complete native outcome derives the owner-to-KEM-handle relation without an initial alignment hypothesis. -/
theorem initialized_run (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (source : RegistrationNativeMldsa.Source) (ensureInit : StateT Unit ProbComp Bool)
    (identityIndex : Nat) (serverKeyId : Aeneas.Std.U64) (initial : Initial n KemSK source)
    (started : some initial ∈ support (RegistrationNativeExperiment.start setup source ensureInit identityIndex serverKeyId))
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (result : Value × (RegistrationNativeLedger.State × State n KemSK source))
    (supported : result ∈ support (RegistrationNativeExperiment.run setup checks wire route representation initial.created source initial.credential bounds mode work initial.state)) :
    Holds result.2.2 :=
  run_holds setup checks wire route representation initial.created initial.credential bounds mode work initial.state result
    (start_holds setup source ensureInit identityIndex serverKeyId initial started) supported

end BeaconcryptCore.Computational.RegistrationNativeKemRosterAlignmentRun

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemRosterAlignmentRun.handler_keeps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemRosterAlignmentRun.handler_keeps
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemRosterAlignmentRun.run_holds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemRosterAlignmentRun.run_holds
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemRosterAlignmentRun.start_holds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemRosterAlignmentRun.start_holds
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemRosterAlignmentRun.initialized_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemRosterAlignmentRun.initialized_run
