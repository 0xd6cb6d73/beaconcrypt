-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentitySourcePrepare
import BeaconcryptCore.Computational.RegistrationNativeIdentitySourceEffects
import BeaconcryptCore.Computational.RegistrationNativeIdentitySourcePersistence

/-! The identity/prekey suffix of the actual source constructor uses the same seed and prekey draws on one World. The executable side retains only the generated credential; private realization reads precisely its newly appended seed after the ordinary prekey sampler. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeIdentitySourceSuffix
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeIdentityFrontend (Ambient Trusted)
open RegistrationNativeIdentityWorld (State implementation ambient)
variable {n : Nat} {ι KemSK Value : Type} {base : OracleSpec ι}
variable {source : RegistrationNativeMldsa.Source}

def oldSample (work : ProbComp Value) : OracleComp (Ambient n KemSK) Value :=
  simulateQ RegistrationBeaconReferenceNativeRecord.environment
    (simulateQ RegistrationWorldCoinCompiler.envCoin work)

def newSample (work : ProbComp Value) : OracleComp (Trusted n KemSK) Value :=
  simulateQ RegistrationNativeIdentityFrontend.ambientLift (oldSample work)

def native (pin : session.ServerAuthenticationPin) :
    OracleComp (Ambient n KemSK) (RustM (Option (RegistrationNativeBeaconFrontend.Prepared source))) := do
  let seed ← oldSample PqxdhJointIdentity.sampleSeed
  let scalar ← oldSample PqxdhJointGapDh.sampleScalar
  pure (.ok (some ⟨pin, seed, scalar⟩))

def exposed (pin : session.ServerAuthenticationPin) :
    OracleComp (Trusted n KemSK) (RustM (Option (RegistrationNativeIdentityFrontend.Prepared source))) := do
  let identity ← RegistrationNativeIdentityInterface.create (Ambient n KemSK)
  match identity with
  | none => pure (.ok none)
  | some identity =>
      let scalar ← newSample PqxdhJointGapDh.sampleScalar
      pure (.ok (some ⟨pin, identity, scalar⟩))

/-- The entire source identity/prekey suffix, including actual counters and context, equals the original scalar/seed constructor after private credential realization. -/
theorem source_exact (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (pin : session.ServerAuthenticationPin)
    (before : State n KemSK) :
    (fun result => (RegistrationNativeIdentityRealization.preparedReply result.2.identities result.1, result.2.context)) <$>
      (simulateQ (implementation (mlSource := source) setup checks representation created) (exposed (source := source) pin)).run before =
      (simulateQ (ambient (mlSource := source) setup checks representation created) (native (source := source) pin)).run before.context := by
  simp only [exposed, native, oldSample, simulateQ_bind, StateT.run_bind, map_bind]
  rw [RegistrationNativeIdentitySourceBirth.create_source, RegistrationNativeIdentitySourceEffects.seed]
  simp only [bind_map_left]
  apply bind_congr
  intro seed
  simp only [newSample, RegistrationNativeIdentitySourceBirth.credential,
    simulateQ_bind, StateT.run_bind, map_bind]
  rw [RegistrationNativeIdentitySourceFrame.ambient_program]
  simp only [bind_map_left, simulateQ_pure, StateT.run_pure, map_pure, oldSample]
  apply bind_congr
  intro scalar
  simp only [RegistrationNativeIdentityRealization.preparedReply,
    RegistrationNativeIdentityRealization.prepared, Option.map_some]
  have stored := RegistrationNativeIdentitySourceBirth.seed_found setup.joint before seed
  simp only [RegistrationNativeIdentitySourceBirth.credential] at stored
  simp only [stored]

end BeaconcryptCore.Computational.RegistrationNativeIdentitySourceSuffix

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentitySourceSuffix.source_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentitySourceSuffix.source_exact
