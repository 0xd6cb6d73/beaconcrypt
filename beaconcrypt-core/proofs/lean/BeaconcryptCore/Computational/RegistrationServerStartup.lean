-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationServerNativeSource

/-! Concrete fresh startup imports the actual generated constructor's public identity and empty peers, then executes the native Server-pin fingerprint through the same World cache. The public initializer stores no selected identity seed. Runtime initialization and ML-key generation precede this endpoint; the selected classical seed sampler is the one in NativeSource.profile. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
set_option autoImplicit false
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationServerStartup
open PqxdhJointIdentity
open RegistrationServerRootCompiler (Local)
open RegistrationServerFrontendCompiler (State restore erase)
variable {n : Nat}

/-- Only constructor-public fields enter the executable startup. This placeholder seed is not used by any startup operation. -/
def publicCreated (identity : PublicIdentity) (identityIndex : Nat) (serverKid : Std.U64) :
    PqxdhLiveServerConstruction.Created Unit :=
  { seed := List.Vector.replicate 32 0
    publicIdentity := identity
    server := ⟨⟨PqxdhRootTableInitialization.rootArray identity.ed25519, fun _ => none,
      ⟨identityIndex, serverKid⟩⟩, 0⟩
    control := ⟨serverKid⟩
    consumed := []
    origin := .generated }

noncomputable def entry (identity : PublicIdentity) (identityIndex : Nat) (serverKid : Std.U64) : Local n :=
  ⟨RegistrationServerRoleBackend.empty, [], [],
    ({ PqxdhRecordLiftWorld.initial with
        server := some (PqxdhRecordLiftWorld.importedServer (publicCreated identity identityIndex serverKid)) }, [])⟩

/-- The actual pin fingerprint pays its own shared hash query before any accepted Init packet. -/
noncomputable def start (identity : PublicIdentity) (identityIndex : Nat) (serverKid : Std.U64)
    (publicKey : Std.Array U8 1952#usize) : ProbComp (State n) := do
  let hashed ← (RegistrationWorldServerCompletion.capability (.hash (absBytes publicKey))).run
    (entry identity identityIndex serverKid)
  pure ⟨⟨serverKid⟩,
    ⟨⟨PqxdhRootTableInitialization.rootArray identity.ed25519, serverKid⟩, publicKey,
      RegistrationAuthenticationShared.digestArray hashed.1⟩,
    [], [], hashed.2⟩

/-- Public startup imports exactly the generated source constructor's native record coordinates. -/
theorem imported_source (joint : Primitives) (seed : IdentitySeed) (identityIndex : Nat) (serverKid : Std.U64) :
    PqxdhRecordLiftWorld.importedServer (publicCreated (joint.publicKeys seed) identityIndex serverKid) =
      PqxdhRecordLiftWorld.importedServer
        (PqxdhLiveServerConstruction.initialized (P := Unit) joint identityIndex serverKid .generated seed) := rfl

private theorem pin_native (binding : pqxdh.ServerBinding) (publicKey : Std.Array U8 1952#usize) :
    RegistrationWorldServerFrontend.initializePin (n := n) (Auxiliary := RegistrationServerRoleBackend.State) binding publicKey =
      (fun before => do
        let result ← (RegistrationWorldServerCompletion.capability (.hash (absBytes publicKey))).run before.2
        pure (.ok (.Some (⟨binding, publicKey, RegistrationAuthenticationShared.digestArray result.1⟩ : session.ServerAuthenticationPin)),
          (before.1, result.2))) := by
  funext before
  exact RegistrationWorldServerFrontend.initializePin_native binding publicKey before

/-- The native startup result, pin, actual shared hash state and initialized World are identical; only the private constructor/family coordinates are restored. -/
theorem start_native (joint : Primitives) (seed : IdentitySeed) (identityIndex : Nat) (serverKid : Std.U64)
    (publicKey : Std.Array U8 1952#usize) :
    (RegistrationWorldServerFrontend.start
      (PqxdhLiveServerConstruction.initialized (P := Unit) joint identityIndex serverKid .generated seed)
        publicKey RegistrationServerRoleBackend.empty).run (PqxdhRecordLiftWorld.initial : PqxdhRecordLiftWorld.State n) =
      (fun state => (.ok (.Some (restore
        (PqxdhLiveServerConstruction.initialized (P := Unit) joint identityIndex serverKid .generated seed)
        (PqxdhJointDhExtractFamily.empty, state))), state.world.world.1)) <$>
        start (joint.publicKeys seed) identityIndex serverKid publicKey := by
  simp only [RegistrationWorldServerFrontend.start, PqxdhRecordLiftWorld.initializeServer,
    PqxdhRecordLiftWorld.initial, StateT.run, pure_bind]
  rw [pin_native]
  simp only [start, entry, publicCreated, PqxdhLiveServerConstruction.initialized,
    StateT.run, bind_pure_comp, Functor.map_map, restore]
  rfl

private theorem hash_shell (bytes : Pqxdh.Bytes) (before : Local n)
    (result : CtxRomAuth.CtxDigest × Local n)
    (supported : result ∈ support ((RegistrationWorldServerCompletion.capability (.hash bytes)).run before)) :
    result.2.auxiliary = before.auxiliary ∧ result.2.requests = before.requests ∧
      result.2.recordRequests = before.recordRequests ∧ result.2.world.2 = before.world.2 ∧
      { result.2.world.1 with primitive := before.world.1.primitive } = before.world.1 := by
  simp only [RegistrationWorldServerCompletion.capability, PqxdhRecordLiftWorld.effects,
    PqxdhRecordLiftWorld.capability, PqxdhRecordLiftWorld.chargeEffect, PqxdhRecordLiftWorld.sampled,
    StateT.run, bind_pure_comp, Functor.map_map, support_map] at supported
  obtain ⟨inner, reached, rfl⟩ := supported
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- Fresh startup derives empty replay/session tables and genuinely unused hidden slots; these are not new security assumptions. -/
theorem start_fresh (identity : PublicIdentity) (identityIndex : Nat) (serverKid : Std.U64)
    (publicKey : Std.Array U8 1952#usize) (state : State n)
    (supported : state ∈ support (start identity identityIndex serverKid publicKey)) :
    state.consumed = [] ∧ state.sessions = [] ∧
      state.world.auxiliary = RegistrationServerRoleBackend.empty ∧
      state.world.requests = [] ∧ state.world.recordRequests = [] ∧ state.world.world.2 = [] ∧
      state.world.world.1.seeds = PqxdhRecordLiftLazyTable.initial ∧
      state.world.world.1.used = (fun _ _ => false) ∧ state.world.world.1.owners = [] := by
  simp only [start, bind_pure_comp, support_map] at supported
  obtain ⟨hashed, reached, rfl⟩ := supported
  obtain ⟨auxiliary, requests, records, receipts, shell⟩ := hash_shell (absBytes publicKey)
    (entry identity identityIndex serverKid) hashed reached
  refine ⟨rfl, rfl, auxiliary, requests, records, receipts, ?_, ?_, ?_⟩
  · exact congrArg PqxdhRecordLiftWorld.State.seeds shell
  · exact congrArg PqxdhRecordLiftWorld.State.used shell
  · exact congrArg PqxdhRecordLiftWorld.State.owners shell

/-- The native source experiment starts at the actual fresh constructor and actual pin fingerprint, with no arbitrary initial-world sampler. -/
noncomputable def profile {ι KemSK Reader Response Encoded X : Type} {base : OracleSpec ι}
    (setup : PqxdhServerAuthExperiment.Setup base KemSK) (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (checks : PqxdhServerAuthExperiment.Checks) (route : RawCtxServerRouting.SenderDecoder)
    (verify : MldsaTranscriptAuth.Verify)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (encode : registration.SignedResponseView → core.option.Option Encoded)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (correct : PqxdhSecretInputKdf.SourceRootCorrect setup.source setup.hmac)
    (identityIndex : Nat) (serverKid : Std.U64) (publicKey : Std.Array U8 1952#usize)
    (adversary : PqxdhJointGapDh.PublicChallenge → OracleComp (RegistrationServerFrontendGame.Spec Encoded) X)
    (event : PqxdhJointGapDh.PublicChallenge → X → State n → Bool) : ProbComp Bool :=
  RegistrationServerNativeSource.profile setup codec checks route verify sign encode representation correct identityIndex serverKid
    (fun publicValue => start publicValue.identity identityIndex serverKid publicKey) adversary event

/-- Concrete fresh startup and the entire actual native source API pay the constructed family advantage with coefficient one. The independent ML key fixture and ordinary source/codec/SDK representation boundaries are explicit parameters. -/
theorem profile_family_advantage {ι KemSK Reader Response Encoded X : Type} {base : OracleSpec ι}
    (setup : PqxdhServerAuthExperiment.Setup base KemSK) (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (checks : PqxdhServerAuthExperiment.Checks) (route : RawCtxServerRouting.SenderDecoder)
    (verify : MldsaTranscriptAuth.Verify)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (encode : registration.SignedResponseView → core.option.Option Encoded)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (correct : PqxdhSecretInputKdf.SourceRootCorrect setup.source setup.hmac)
    (identityIndex : Nat) (serverKid : Std.U64) (publicKey : Std.Array U8 1952#usize)
    (adversary : PqxdhJointGapDh.PublicChallenge → OracleComp (RegistrationServerFrontendGame.Spec Encoded) X)
    (event : PqxdhJointGapDh.PublicChallenge → X → State n → Bool) :
    (profile setup codec checks route verify sign encode representation correct identityIndex serverKid publicKey adversary event).boolDistance
      (RegistrationServerFrontendGame.idealProfile setup codec checks route verify sign encode
        (fun publicValue => start publicValue.identity identityIndex serverKid publicKey) adversary event) =
      PqxdhJointDhExtractFamily.advantage setup.hmac setup.joint setup.dh
        (fun publicValue => simulateQ PqxdhJointDhExtractRoot.reduction
          (RegistrationServerFrontendGame.client setup codec checks route verify sign encode
            (fun publicValue => start publicValue.identity identityIndex serverKid publicKey) adversary event publicValue)) :=
  RegistrationServerNativeSource.family_advantage setup codec checks route verify sign encode representation correct
    identityIndex serverKid (fun publicValue => start publicValue.identity identityIndex serverKid publicKey) adversary event

end BeaconcryptCore.Computational.RegistrationServerStartup

/-- info: 'BeaconcryptCore.Computational.RegistrationServerStartup.imported_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationServerStartup.imported_source

/-- info: 'BeaconcryptCore.Computational.RegistrationServerStartup.start_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationServerStartup.start_native

/-- info: 'BeaconcryptCore.Computational.RegistrationServerStartup.start_fresh' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationServerStartup.start_fresh

/-- info: 'BeaconcryptCore.Computational.RegistrationServerStartup.profile_family_advantage' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationServerStartup.profile_family_advantage
