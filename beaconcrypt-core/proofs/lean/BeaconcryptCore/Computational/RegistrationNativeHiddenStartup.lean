-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeHiddenInterpreter
import BeaconcryptCore.Computational.RegistrationNativePublicStartup

/-! The thin native World client performs its literal runtime/classical dummy constructor and local ML generation, then imports the public Server and retains its exact configured full ML public pin without a hash query before the first adversary command. Runtime initialization and both genuine Server key samplers retain their original World effects. Source/table coupling and the arbitrary-start entropy theorem must target this actual AST. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeHiddenStartup
open PqxdhServerAuthExperiment (Setup Checks)
open PqxdhRecordLiftInterface (WorldSpec coinLift effectLift)
variable {n : Nat} {ι KemSK ProviderState Value : Type} {base : OracleSpec ι}

structure Started (source : RegistrationNativeMldsa.Source) where
  created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)
  native : RegistrationNativePublicStartup.Started source

private abbrev PeerMetadata := Std.Array U8 151#usize

noncomputable def start (setup : Setup base KemSK) (source : RegistrationNativeMldsa.Source)
    (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64)
    (identity : PqxdhJointIdentity.PublicIdentity) : OracleComp (WorldSpec n) (Option (Started source)) := do
  let constructed ← simulateQ coinLift
    ((PqxdhLiveServerConstruction.construct (P := PeerMetadata) setup.joint ensureInit identityIndex serverKeyId none).run ())
  match constructed.1 with
  | none => pure none
  | some _ =>
      let generated ← simulateQ coinLift (RegistrationNativeMldsa.generate source)
      match generated with
      | none => pure none
      | some credential =>
          let created := RegistrationServerStartup.publicCreated identity identityIndex serverKeyId
          let _ ← (WorldSpec n).query (.inl created)
          let pin : session.ServerAuthenticationPin :=
            ⟨⟨PqxdhRootTableInitialization.rootArray identity.ed25519, serverKeyId⟩,
              credential.publicKey⟩
          let frontend : RegistrationNativePublicFrontend.State source :=
            ⟨RegistrationServerMaterialFrontend.initial created.control pin, [],
              ⟨RegistrationServerRoleBackend.empty, [], [], []⟩, 0⟩
          pure (some ⟨created, ⟨credential, frontend⟩⟩)

/-- Effectful native startup has the same literal empty local roster, record-request log and parsed-attempt counter on every supported successful branch. -/
theorem start_fields (setup : Setup base KemSK) (source : RegistrationNativeMldsa.Source)
    (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64)
    (identity : PqxdhJointIdentity.PublicIdentity) (started : Started source)
    (supported : some started ∈ support (start (n := n) setup source ensureInit identityIndex serverKeyId identity)) :
    started.native.frontend.beacons = [] ∧ started.native.frontend.environment.recordRequests = [] ∧
      started.native.frontend.parsedAccepts = 0 ∧ started.created.server.server.metadata.sender = serverKeyId := by
  simp only [start, mem_support_bind_iff] at supported
  obtain ⟨constructed, _constructed, continued⟩ := supported
  cases built : constructed.1 with
  | none => simp only [built, mem_support_pure_iff] at continued; cases continued
  | some created =>
      simp only [built, mem_support_bind_iff] at continued
      obtain ⟨generated, _generated, continued⟩ := continued
      cases sampled : generated with
      | none => simp only [sampled, mem_support_pure_iff] at continued; cases continued
      | some credential =>
          simp only [sampled, mem_support_bind_iff] at continued
          obtain ⟨installed, _installed, returned⟩ := continued
          simp only [mem_support_pure_iff, Option.some.injEq] at returned
          cases returned
          exact ⟨rfl, rfl, rfl, rfl⟩

noncomputable def program (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (source : RegistrationNativeMldsa.Source) (ensureInit : StateT Unit ProbComp Bool)
    (identityIndex : Nat) (serverKeyId : U64)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (provider : RegistrationNativeHiddenInterpreter.Provider KemSK ProviderState) (providerState : ProviderState)
    (selectedOwner selectedAccept : Nat) (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec mode) Value) := do
  let initialized ← start (n := n) setup source ensureInit identityIndex serverKeyId (setup.joint.publicKeys seed)
  match initialized with
  | none => pure none
  | some started =>
      let observed ← RegistrationNativeHiddenInterpreter.run setup checks wire source started.native.credential seed scalar provider
        selectedOwner selectedAccept serverKeyId bounds mode
        (adversary ⟨setup.joint.publicKeys seed, started.native.credential.publicKey, serverKeyId⟩)
        started.native.frontend (RegistrationNativeHiddenInterpreter.initial providerState)
      pure (some (started.created, observed))

end BeaconcryptCore.Computational.RegistrationNativeHiddenStartup

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeHiddenStartup.start_fields' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeHiddenStartup.start_fields
