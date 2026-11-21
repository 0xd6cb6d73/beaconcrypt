-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePublicSourceStartupGood
import BeaconcryptCore.Computational.RegistrationNativePublicSourceFull
import BeaconcryptCore.Computational.RegistrationNativeSeedProfile

/-! The concrete original native deployment and a selected-secret-free native related-root client have the same complete original-ledger decisions. Generated startup, both discarded source draws, every native failure and both roles are derived through the source compiler. This is a source endpoint; the later protected-slot and repeated-role-alias security bridges remain separate. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePublicSourceProfile
open PqxdhServerAuthExperiment (Setup Checks)
variable {n : Nat} {ι KemSK Value : Type} {base : OracleSpec ι}

/-- This executable client receives only the selected public identity/prekey, retains the original secrecy ledger and decides its literal final value and ledger. -/
noncomputable def client (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (source : RegistrationNativeMldsa.Source)
    (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64)
    (selectedOwner selectedAccept : Nat) (bounds : PqxdhDeploymentInterface.FreshBounds)
    (mode : PqxdhDeploymentInterface.Mode)
    (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (decision : Value × RegistrationNativeLedger.State → Bool)
    (publicValue : PqxdhJointGapDh.PublicChallenge) : OracleComp RegistrationNativeRelatedRoot.RootSpec Bool := do
  let initialized ← (RegistrationNativePublicStartup.start (n := n) setup source ensureInit identityIndex serverKeyId publicValue.identity).run
    RegistrationNativePublicInterpreter.initial
  match initialized.1 with
  | none => pure false
  | some started => do
      let observed ← RegistrationNativePublicInterpreter.run setup checks wire route source started.credential
        selectedOwner selectedAccept publicValue.prekey serverKeyId bounds mode
        (adversary ⟨publicValue.identity, started.credential.publicKey, serverKeyId⟩) started.frontend initialized.2
      pure (decision observed.1.1)

/-- For fixed private source challenges, successful startup derives every required invariant and the full ledger decision is the actual native eager execution. -/
theorem fixed_source (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (correct : PqxdhSecretInputKdf.SourceRootCorrect setup.source setup.hmac)
    (source : RegistrationNativeMldsa.Source) (ensureInit : StateT Unit ProbComp Bool)
    (identityIndex : Nat) (serverKeyId : U64) (selectedOwner selectedAccept : Nat)
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (decision : Value × RegistrationNativeLedger.State → Bool)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes) :
    simulateQ (RegistrationNativeSourceRoot.handler setup.source setup.hmac setup.joint setup.dh seed scalar)
      (client (n := n) setup checks wire route source ensureInit identityIndex serverKeyId selectedOwner selectedAccept bounds mode adversary decision
        (PqxdhJointGapDh.challenge setup.joint setup.dh seed scalar)) = (do
      let initialized ← RegistrationNativeSeedStart.start setup source ensureInit identityIndex serverKeyId seed
      match initialized with
      | none => pure false
      | some initial =>
          (fun (result : RegistrationNativeEvents.Observed Value (RegistrationNativeExperiment.State n KemSK source)) => decision (result.1, result.2.1)) <$>
            RegistrationNativeScalarEager.run setup checks wire route representation initial.created source initial.credential
              selectedOwner scalar bounds mode (adversary initial.public) initial.state) := by
  rw [← RegistrationNativePublicSourceStartup.start_source setup source ensureInit identityIndex serverKeyId seed scalar]
  simp only [client, simulateQ_bind, bind_map_left]
  apply bind_congr_of_forall_mem_support
  rintro ⟨initialized, after⟩ supported
  cases initialized with
  | none => rfl
  | some started =>
      have valid := RegistrationNativePublicSourceStartupGood.start_good setup source seed scalar ensureInit identityIndex serverKeyId
        selectedOwner started after supported
      let created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize) :=
        PqxdhLiveServerConstruction.initialized setup.joint identityIndex serverKeyId .generated seed
      have exactRun := RegistrationNativePublicSourceFull.ledger_source setup checks wire route representation correct created scalar
        started.credential selectedOwner selectedAccept bounds mode
        (adversary ⟨setup.joint.publicKeys seed, started.credential.publicKey, serverKeyId⟩) started.frontend after valid decision
      simpa only [RegistrationNativePublicSourceStartupWorld.observe, Option.map_some,
        simulateQ_bind, simulateQ_pure, simulateQ_map, bind_pure_comp, RegistrationNativeExperiment.Initial.public,
        PqxdhJointGapDh.challenge,
        created, PqxdhLiveServerConstruction.initialized] using exactRun

/-- The related-root source game is exactly the independently sampled private-seed/scalar native source profile, with the literal original ledger decision. -/
theorem seeded_source (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (correct : PqxdhSecretInputKdf.SourceRootCorrect setup.source setup.hmac)
    (source : RegistrationNativeMldsa.Source) (ensureInit : StateT Unit ProbComp Bool)
    (identityIndex : Nat) (serverKeyId : U64) (selectedOwner selectedAccept : Nat)
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (decision : Value × RegistrationNativeLedger.State → Bool) :
    RegistrationNativeRelatedRoot.sourceGame setup.source setup.hmac setup.joint setup.dh
      (client (n := n) setup checks wire route source ensureInit identityIndex serverKeyId selectedOwner selectedAccept bounds mode adversary decision) =
      RegistrationNativeSeedProfile.profile (n := n) setup checks wire route representation source ensureInit identityIndex serverKeyId selectedOwner
        bounds mode adversary (fun result => decision (result.1, result.2.1)) := by
  simp only [RegistrationNativeRelatedRoot.sourceGame, StateT.run'_eq, RegistrationNativeSourceRoot.program_value,
    fixed_source setup checks wire route representation correct, RegistrationNativeSeedProfile.profile]
  rfl

/-- The actual generated native profile is the source game of a concrete selected-secret-free client, for every original raw/secrecy mode and every literal original-ledger decision. -/
theorem profile_source (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (correct : PqxdhSecretInputKdf.SourceRootCorrect setup.source setup.hmac)
    (source : RegistrationNativeMldsa.Source) (ensureInit : StateT Unit ProbComp Bool)
    (identityIndex : Nat) (serverKeyId : U64) (selectedOwner selectedAccept : Nat)
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (decision : Value × RegistrationNativeLedger.State → Bool) :
    RegistrationNativeExperiment.profile (n := n) setup checks wire route representation source ensureInit identityIndex serverKeyId bounds mode
      adversary (fun result => decision (result.1, result.2.1)) =ᵈ
      RegistrationNativeRelatedRoot.sourceGame setup.source setup.hmac setup.joint setup.dh
        (client (n := n) setup checks wire route source ensureInit identityIndex serverKeyId selectedOwner selectedAccept bounds mode adversary decision) := by
  rw [seeded_source setup checks wire route representation correct]
  exact RegistrationNativeSeedProfile.source setup checks wire route representation source ensureInit identityIndex serverKeyId
    selectedOwner bounds mode adversary (fun result => decision (result.1, result.2.1))

end BeaconcryptCore.Computational.RegistrationNativePublicSourceProfile

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePublicSourceProfile.fixed_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePublicSourceProfile.fixed_source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePublicSourceProfile.seeded_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePublicSourceProfile.seeded_source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePublicSourceProfile.profile_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePublicSourceProfile.profile_source
