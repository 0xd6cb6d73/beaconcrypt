-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePublicStartupFrame
import BeaconcryptCore.Computational.RegistrationNativePublicSourceEffects
import BeaconcryptCore.Computational.RegistrationNativeSeedStart

/-! Fixed-private-seed native startup restores only private constructor and root coordinates. Its public initialization, complete World and pin fingerprint are the actual native startup operations with the same counted constructor and ML-generation prefixes. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePublicSourceStartupWorld
open PqxdhServerAuthExperiment (Setup)
open PqxdhJointIdentity (IdentitySeed PublicIdentity)
variable {n : Nat} {ι KemSK : Type} {base : OracleSpec ι}

noncomputable def observe (setup : Setup base KemSK) (source : RegistrationNativeMldsa.Source)
    (seed : IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes) (identityIndex : Nat) (serverKeyId : U64)
    (result : Option (RegistrationNativePublicStartup.Started source) × RegistrationNativePublicInterpreter.State n KemSK) :
    Option (RegistrationNativeExperiment.Initial n KemSK source) :=
  result.1.map fun started =>
    ⟨PqxdhLiveServerConstruction.initialized setup.joint identityIndex serverKeyId .generated seed, started.credential,
      RegistrationNativePublicSourceState.restore (RegistrationNativePublicSourceState.roots setup seed scalar) scalar started.frontend result.2⟩

noncomputable def privateAt (world : PqxdhRecordLiftWorld.State n) : RegistrationNativePublicInterpreter.State n KemSK :=
  { (RegistrationNativePublicInterpreter.initial : RegistrationNativePublicInterpreter.State n KemSK) with world }

noncomputable def initialized (identity : PublicIdentity) (identityIndex : Nat) (serverKeyId : U64)
    (source : RegistrationNativeMldsa.Source) (credential : RegistrationNativeMldsa.Credential source) :
    StateT (PqxdhRecordLiftWorld.State n) ProbComp (RegistrationNativePublicStartup.Started source) := do
  let created := RegistrationServerStartup.publicCreated identity identityIndex serverKeyId
  let _ ← PqxdhRecordLiftWorld.initializeServer created
  let digest ← PqxdhRecordLiftWorld.effects (.inr (.hash (absBytes credential.publicKey)))
  let pin : session.ServerAuthenticationPin :=
    ⟨⟨PqxdhRootTableInitialization.rootArray identity.ed25519, serverKeyId⟩,
      credential.publicKey, RegistrationAuthenticationShared.digestArray digest⟩
  pure ⟨credential, ⟨RegistrationServerMaterialFrontend.initial created.control pin, [],
    ⟨RegistrationServerRoleBackend.empty, [], [], []⟩, 0⟩⟩

/-- Source initialization uses the exact same imported native Server coordinates for the public and privately seeded constructor. -/
theorem initialize_server (joint : PqxdhJointIdentity.Primitives) (seed : IdentitySeed)
    (identityIndex : Nat) (serverKeyId : U64) (before : PqxdhRecordLiftWorld.State n) :
    (PqxdhRecordLiftWorld.initializeServer
      (RegistrationServerStartup.publicCreated (joint.publicKeys seed) identityIndex serverKeyId)).run before =
      (PqxdhRecordLiftWorld.initializeServer
        (PqxdhLiveServerConstruction.initialized joint identityIndex serverKeyId .generated seed)).run before := by
  cases stored : before.server <;>
    simp only [PqxdhRecordLiftWorld.initializeServer, StateT.run, stored, RegistrationServerStartup.imported_source]

private theorem pin_native (binding : pqxdh.ServerBinding) (publicKey : Std.Array U8 1952#usize) :
    RegistrationWorldServerFrontend.initializePin (n := n) (Auxiliary := RegistrationServerRoleBackend.State) binding publicKey =
      (fun before => do
        let result ← (RegistrationWorldServerCompletion.capability (.hash (absBytes publicKey))).run before.2
        pure (.ok (.Some (⟨binding, publicKey, RegistrationAuthenticationShared.digestArray result.1⟩ : session.ServerAuthenticationPin)),
          (before.1, result.2))) := by
  funext before
  exact RegistrationWorldServerFrontend.initializePin_native binding publicKey before

/-- The final startup initializer has the actual native pin/hash/World and privately restored empty frontend state. -/
theorem initialize_source (setup : Setup base KemSK) (source : RegistrationNativeMldsa.Source)
    (seed : IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes) (identityIndex : Nat) (serverKeyId : U64)
    (credential : RegistrationNativeMldsa.Credential source) (before : PqxdhRecordLiftWorld.State n) :
    (fun result => observe setup source seed scalar identityIndex serverKeyId (some result.1, privateAt result.2)) <$>
      (initialized (setup.joint.publicKeys seed) identityIndex serverKeyId source credential).run before = (do
        let initialized ← (RegistrationWorldServerFrontend.start
          (PqxdhLiveServerConstruction.initialized setup.joint identityIndex serverKeyId .generated seed)
          credential.publicKey RegistrationServerRoleBackend.empty).run before
        match initialized.1 with
        | .ok (.Some native) => pure (some ⟨PqxdhLiveServerConstruction.initialized setup.joint identityIndex serverKeyId .generated seed,
            credential, ⟨RegistrationServerFrontendCompiler.erase native, [], PqxdhLiveKemBirth.empty, 0⟩⟩)
        | _ => pure none) := by
  simp only [initialized, StateT.run_bind, map_bind]
  rw [initialize_server]
  simp only [RegistrationWorldServerFrontend.start, StateT.run, bind_assoc]
  apply bind_congr
  intro installed
  rw [pin_native]
  simp only [StateT.run, RegistrationWorldServerCompletion.capability, bind_map_left, pure_bind, bind_pure_comp, Functor.map_map]
  apply bind_congr
  intro hashed
  simp only [observe, Option.map_some, privateAt, RegistrationNativePublicSourceState.restore,
    RegistrationNativePublicSourceState.owners, RegistrationNativePublicInterpreter.initial,
    RegistrationServerMaterialSourceState.restore, RegistrationServerReferenceRestore.restore,
    RegistrationServerReferenceRestore.sessions, RegistrationServerMaterialFrontend.initial,
    RegistrationWorldAgreementCompiler.join, RegistrationServerFrontendCompiler.erase,
    RegistrationServerStartup.publicCreated, PqxdhLiveServerConstruction.initialized]
  rfl

end BeaconcryptCore.Computational.RegistrationNativePublicSourceStartupWorld

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePublicSourceStartupWorld.initialize_server' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePublicSourceStartupWorld.initialize_server
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePublicSourceStartupWorld.initialize_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePublicSourceStartupWorld.initialize_source
