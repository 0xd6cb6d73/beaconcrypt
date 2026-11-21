-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeBeaconCoherence
import BeaconcryptCore.Computational.RegistrationNativeStatePreservation

/-! Actual generated native startup and the full original raw secrecy-ledger experiment retain pending Beacon control/server-pin coherence. The invariant is derived for every source continuation, including failed raw requests and all reached primitive/cache states; it is not a caller-supplied initialization premise. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeBeaconCoherenceRun
open RegistrationNativeExperiment (State Initial)
open RegistrationNativeBeaconCoherence (Holds)
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeRawAdapter (TypedSpec)
variable {n : Nat} {ι KemSK Value : Type} {base : OracleSpec ι} {mlSource : RegistrationNativeMldsa.Source}
attribute [local irreducible] RegistrationServerSdkSource.accept

private theorem beacon_keeps (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (work : RegistrationNativeBeaconFrontend.M n KemSK mlSource RegistrationServerRoleBackend.State Value)
    (localLaw : ∀ owners env result, Holds owners → result ∈ support ((work.run owners).run env) → Holds result.1.2)
    (before : State n KemSK mlSource) (result : Value × State n KemSK mlSource) (prior : Holds before.beacons)
    (supported : result ∈ support ((RegistrationNativeExperiment.beacon setup checks representation created work).run before)) :
    Holds result.2.beacons := by
  simp only [RegistrationNativeExperiment.beacon, StateT.run, mem_support_bind_iff,
    support_pure, Set.mem_singleton_iff] at supported
  obtain ⟨inner, reached, returned⟩ := supported
  have native : inner.1 ∈ support
      ((work.run before.beacons).run (RegistrationWorldAgreementCompiler.erase before.server.world)) := by
    apply OracleComp.support_simulateQ_run'_subset
      (RegistrationNativeExperiment.trusted setup checks representation created mlSource) _ before
    rw [StateT.run'_eq, support_map]
    exact Set.mem_image_of_mem Prod.fst reached
  have valid := localLaw before.beacons _ inner.1 prior native
  cases returned
  exact valid

/-- Every actual native typed callback retains all pending capabilities' source-derived coherence. -/
theorem handler_keeps (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (credential : RegistrationNativeMldsa.Credential mlSource)
    (query : TypedSpec.Domain) (before : State n KemSK mlSource)
    (result : TypedSpec.Range query × State n KemSK mlSource) (prior : Holds before.beacons)
    (supported : result ∈ support ((RegistrationNativeExperiment.handler setup checks wire route representation
      created mlSource credential query).run before)) : Holds result.2.beacons := by
  have ordinary (ordinary : RegistrationNativeStatePreservation.Ordinary query) : Holds result.2.beacons := by
    have retained := (RegistrationNativeStatePreservation.handler_keeps setup checks wire route representation
      created credential query ordinary before result supported).2
    simpa only [retained] using prior
  cases query with
  | inl coin => exact ordinary trivial
  | inr command => cases command with
    | create edPin mlPin keyId =>
        exact beacon_keeps setup checks representation created _
          (RegistrationNativeBeaconCoherence.create_keeps setup edPin mlPin keyId) before result prior supported
    | bundle index =>
        exact beacon_keeps setup checks representation created _
          (RegistrationNativeBeaconCoherence.bundle_keeps setup wire index) before result prior supported
    | finish index packet =>
        exact beacon_keeps setup checks representation created _
          (RegistrationNativeBeaconCoherence.finish_keeps setup wire index packet) before result prior supported
    | _ => exact ordinary trivial

/-- The entire original raw native ledger execution preserves the actual lifecycle invariant below all original secrecy draws. -/
theorem run_holds (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (credential : RegistrationNativeMldsa.Credential mlSource)
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value) (before : State n KemSK mlSource)
    (result : Value × (RegistrationNativeLedger.State × State n KemSK mlSource)) (prior : Holds before.beacons)
    (supported : result ∈ support (RegistrationNativeExperiment.run setup checks wire route representation created
      mlSource credential bounds mode work before)) : Holds result.2.2.beacons := by
  unfold RegistrationNativeExperiment.run at supported
  rw [RegistrationNativeFullCompiler.compile_run, support_map] at supported
  obtain ⟨inner, reached, rfl⟩ := supported
  exact OracleComp.simulateQ_run_preserves_inv_of_query
    (RegistrationNativeExperiment.handler setup checks wire route representation created mlSource credential)
    (fun current => Holds current.beacons)
    (fun query current valid next member => handler_keeps setup checks wire route representation created credential
      query current next valid member) _ before prior inner reached

/-- Actual successful generated startup has an empty owner roster, so no pending coherence is assumed. -/
theorem start_holds (setup : Setup base KemSK) (source : RegistrationNativeMldsa.Source)
    (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64)
    (initial : Initial n KemSK source)
    (supported : some initial ∈ support (RegistrationNativeExperiment.start setup source ensureInit identityIndex serverKeyId)) :
    Holds initial.state.beacons := by
  delta RegistrationNativeExperiment.start at supported
  simp only [mem_support_bind_iff] at supported
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
                simp [Holds]

/-- Every complete actual generated source outcome has coherent retained pending capabilities, without a lifecycle hypothesis. -/
theorem initialized_run (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (source : RegistrationNativeMldsa.Source) (ensureInit : StateT Unit ProbComp Bool)
    (identityIndex : Nat) (serverKeyId : U64) (initial : Initial n KemSK source)
    (started : some initial ∈ support (RegistrationNativeExperiment.start setup source ensureInit identityIndex serverKeyId))
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (result : Value × (RegistrationNativeLedger.State × State n KemSK source))
    (supported : result ∈ support (RegistrationNativeExperiment.run setup checks wire route representation initial.created
      source initial.credential bounds mode work initial.state)) : Holds result.2.2.beacons :=
  run_holds setup checks wire route representation initial.created initial.credential bounds mode work initial.state result
    (start_holds setup source ensureInit identityIndex serverKeyId initial started) supported

end BeaconcryptCore.Computational.RegistrationNativeBeaconCoherenceRun

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeBeaconCoherenceRun.handler_keeps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeBeaconCoherenceRun.handler_keeps
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeBeaconCoherenceRun.run_holds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeBeaconCoherenceRun.run_holds
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeBeaconCoherenceRun.start_holds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeBeaconCoherenceRun.start_holds
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeBeaconCoherenceRun.initialized_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeBeaconCoherenceRun.initialized_run
