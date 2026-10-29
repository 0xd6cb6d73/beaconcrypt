-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeKemBirthSourceInvariant
import BeaconcryptCore.Computational.RegistrationNativeStatePreservation

/-! Generated native startup and the complete original raw secrecy ledger preserve genuine indexed KEM ownership. This invariant includes failed constructor, authentication, replay, signing, encoding, send and finish paths; it makes no identification between public owner, session, parsed-accept or KEM creation indices. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeKemBirthRun
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeKemBirthInvariant (Holds)
open RegistrationNativeExperiment (State Initial)
open RegistrationNativeRawAdapter (TypedSpec)
variable {ι KemSK Value : Type} {base : OracleSpec ι} {n : Nat}
variable {mlSource : RegistrationNativeMldsa.Source}
attribute [local irreducible] RegistrationServerSdkSource.accept

/-- Every actual typed deployment callback preserves initialized indexed ownership on all complete output/poststate pairs. -/
theorem handler_keeps (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (credential : RegistrationNativeMldsa.Credential mlSource)
    (query : TypedSpec.Domain) (before after : State n KemSK mlSource) (reply : TypedSpec.Range query)
    (prior : Holds setup before.beacons before.pool)
    (supported : (reply, after) ∈ support ((RegistrationNativeExperiment.handler setup checks wire route representation
      created mlSource credential query).run before)) : Holds setup after.beacons after.pool := by
  have ordinary (ordinary : RegistrationNativeStatePreservation.Ordinary query) : Holds setup after.beacons after.pool := by
    obtain ⟨pool, owners⟩ := RegistrationNativeStatePreservation.handler_keeps setup checks wire route representation
      created credential query ordinary before (reply, after) supported
    change after.pool = before.pool at pool
    change after.beacons = before.beacons at owners
    simpa only [pool, owners] using prior
  rcases query with coin | command
  · exact ordinary trivial
  · cases command with
    | create edPin mlPin keyId =>
        exact RegistrationNativeKemBirthSourceInvariant.create_keeps setup checks representation created
          edPin mlPin keyId before after reply prior supported
    | bundle index =>
        exact RegistrationNativeKemBirthSourceInvariant.bundle_keeps setup checks representation created
          wire index before after reply prior supported
    | finish index packet =>
        exact RegistrationNativeKemBirthSourceInvariant.finish_keeps setup checks representation created
          wire index packet before after reply prior supported
    | accept _ | build _ _ | hmac _ _ | hash _ | serverSend _ _ | serverRaw _ | beaconSend _ _ | beaconRaw _ _ =>
        exact ordinary trivial

/-- The complete adaptive raw experiment retains the original private secrecy ledger and every genuine generated owner. -/
theorem run_holds (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (credential : RegistrationNativeMldsa.Credential mlSource)
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (before : State n KemSK mlSource)
    (result : Value × (RegistrationNativeLedger.State × State n KemSK mlSource))
    (prior : Holds setup before.beacons before.pool)
    (supported : result ∈ support (RegistrationNativeExperiment.run setup checks wire route representation created
      mlSource credential bounds mode work before)) : Holds setup result.2.2.beacons result.2.2.pool := by
  unfold RegistrationNativeExperiment.run at supported
  rw [RegistrationNativeFullCompiler.compile_run, support_map] at supported
  obtain ⟨inner, reached, rfl⟩ := supported
  exact OracleComp.simulateQ_run_preserves_inv_of_query
    (RegistrationNativeExperiment.handler setup checks wire route representation created mlSource credential)
    (fun current => Holds setup current.beacons current.pool)
    (fun query current valid next member => handler_keeps setup checks wire route representation created credential
      query current next.2 next.1 valid member) _ before prior inner reached

/-- Actual generated startup begins with empty owner and private KEM pools after all native initialization and pin-fingerprint effects. -/
theorem start_holds (setup : Setup base KemSK) (source : RegistrationNativeMldsa.Source)
    (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64)
    (initial : Initial n KemSK source)
    (supported : some initial ∈ support (RegistrationNativeExperiment.start setup source ensureInit identityIndex serverKeyId)) :
    Holds setup initial.state.beacons initial.state.pool := by
  simp only [RegistrationNativeExperiment.start, mem_support_bind_iff] at supported
  obtain ⟨constructed, _, continued⟩ := supported
  cases constructor : constructed.1.1 with
  | none => simp [constructor] at continued
  | some created =>
      simp only [constructor, mem_support_bind_iff] at continued
      obtain ⟨generated, _, continued⟩ := continued
      cases generation : generated.1 with
      | none => simp [generation] at continued
      | some credential =>
          simp only [generation, mem_support_bind_iff] at continued
          obtain ⟨initialized, _, returned⟩ := continued
          cases native : initialized.1 with
          | fail error | div => simp [native] at returned
          | ok reply => cases reply with
            | none => simp [native] at returned
            | some state =>
                simp only [native, support_pure, Set.mem_singleton_iff, Option.some.injEq] at returned
                cases returned
                simp [Holds, RegistrationNativeKemBirthPool.Generated, RegistrationNativeKemBirthInvariant.Owns,
                  PqxdhLiveKemBirth.empty]

/-- Every complete raw outcome from actual generated startup has genuine indexed KEM targets, without a supplied owner-honesty invariant. -/
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
      source initial.credential bounds mode work initial.state)) : Holds setup result.2.2.beacons result.2.2.pool :=
  run_holds setup checks wire route representation initial.created initial.credential bounds mode work initial.state result
    (start_holds setup source ensureInit identityIndex serverKeyId initial started) supported

end BeaconcryptCore.Computational.RegistrationNativeKemBirthRun

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemBirthRun.handler_keeps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemBirthRun.handler_keeps

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemBirthRun.run_holds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemBirthRun.run_holds

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemBirthRun.start_holds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemBirthRun.start_holds

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemBirthRun.initialized_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemBirthRun.initialized_run
