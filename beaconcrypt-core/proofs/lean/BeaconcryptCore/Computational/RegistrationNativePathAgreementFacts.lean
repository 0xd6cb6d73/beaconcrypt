-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeStartupIdentity
import BeaconcryptCore.Computational.RegistrationNativePinPrekeyRun
import BeaconcryptCore.Computational.RegistrationNativeBeaconCoherenceRun
import BeaconcryptCore.Computational.RegistrationNativeInitTupleAgreement

/-! Actual initialized native paths derive all local public/private agreement provenance: genuine private KEM rows, scalar/public prekeys, pending control coherence, and the immutable generated Server identity. No adversary-supplied invariant or private root equality is required. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePathAgreementFacts
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeStageTrace (Call Path)
variable {n : Nat} {ι KemSK : Type} {base : OracleSpec ι} {source : RegistrationNativeMldsa.Source}
local notation "Native" => RegistrationNativeExperiment.State n KemSK source

def Valid (setup : Setup base KemSK) (before : Native) : Prop :=
  RegistrationNativeKemBirthInvariant.Holds setup before.beacons before.pool ∧
    RegistrationNativePrekeyCoherence.Holds setup before.beacons ∧ RegistrationNativeBeaconCoherence.Holds before.beacons

/-- Every actual source path retains the three independently proved key/control invariants. -/
theorem path (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (credential : RegistrationNativeMldsa.Credential source)
    {before after : Native} {calls : List (Call RegistrationNativeRawAdapter.TypedSpec Native)}
    (actual : Path (RegistrationNativeExperiment.handler setup checks wire route representation created source credential) before calls after)
    (prior : Valid setup before) : Valid setup after := by
  induction actual with
  | nil => exact prior
  | cons call called rest last following ih =>
    exact ih ⟨RegistrationNativeKemBirthRun.handler_keeps setup checks wire route representation created credential
        call.query call.before call.after call.reply prior.1 called,
      RegistrationNativePrekeyCoherence.handler setup checks wire route representation created credential
        call.query call.before prior.2.1 (call.reply, call.after) called,
      RegistrationNativeBeaconCoherenceRun.handler_keeps setup checks wire route representation created credential
        call.query call.before (call.reply, call.after) prior.2.2 called⟩

/-- The initial key/control invariants arise from successful actual native startup and persist to any reached source prefix. -/
theorem initialized (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64)
    (initial : RegistrationNativeExperiment.Initial n KemSK source)
    (started : some initial ∈ support (RegistrationNativeExperiment.start setup source ensureInit identityIndex serverKeyId))
    (after : Native) (calls : List (Call RegistrationNativeRawAdapter.TypedSpec Native))
    (actual : Path (RegistrationNativeExperiment.handler setup checks wire route representation initial.created source initial.credential)
      initial.state calls after) : Valid setup after :=
  path setup checks wire route representation initial.created initial.credential actual
    ⟨RegistrationNativeKemBirthRun.start_holds setup source ensureInit identityIndex serverKeyId initial started,
      RegistrationNativePrekeyCoherence.start setup ensureInit identityIndex serverKeyId initial started,
      RegistrationNativeBeaconCoherenceRun.start_holds setup source ensureInit identityIndex serverKeyId initial started⟩

/-- The actual current Server pin identity remains the one generated from startup's actual seed. -/
theorem server_identity (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64)
    (initial : RegistrationNativeExperiment.Initial n KemSK source)
    (started : some initial ∈ support (RegistrationNativeExperiment.start setup source ensureInit identityIndex serverKeyId))
    (after : Native) (calls : List (Call RegistrationNativeRawAdapter.TypedSpec Native))
    (actual : Path (RegistrationNativeExperiment.handler setup checks wire route representation initial.created source initial.credential)
      initial.state calls after) :
    after.server.pin.binding.identity_public_key = PqxdhRootTableInitialization.rootArray (setup.joint.publicKeys initial.created.seed).ed25519 := by
  have unchanged := RegistrationNativeInitTupleAgreement.path_pin setup checks wire route representation initial.created initial.credential actual
  have fields := RegistrationNativeServerPinStartup.start_pin setup source ensureInit identityIndex serverKeyId initial started
  rw [unchanged, fields.1]
  exact (RegistrationNativeStartupIdentity.identity setup source ensureInit identityIndex serverKeyId initial started).2

end BeaconcryptCore.Computational.RegistrationNativePathAgreementFacts

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePathAgreementFacts.path' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePathAgreementFacts.path

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePathAgreementFacts.initialized' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePathAgreementFacts.initialized

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePathAgreementFacts.server_identity' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePathAgreementFacts.server_identity
