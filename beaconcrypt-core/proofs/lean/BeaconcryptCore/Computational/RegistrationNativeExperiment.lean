-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeBeaconFrontend
import BeaconcryptCore.Computational.RegistrationServerSdkSource
import BeaconcryptCore.Computational.RegistrationNativeEvents
import BeaconcryptCore.Computational.RegistrationNativeFullCompiler
import BeaconcryptCore.Computational.CborRecordWorldSimulation

/-! The concrete native source deployment runs actual Server and Beacon controllers on one record World and one private generated KEM pool. The ML source generates local credentials; native packet parsing and dynamic encoding are the explicit Wire boundary. The source state retains native secrets privately. Cryptographic clients must erase selected identity/prekey bytes and native root/seed capabilities through the separate role and material compilers before applying their bounds. Original CE secrecy draws remain above this dispatcher. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeExperiment
open PqxdhServerAuthExperiment (Setup Checks)
open PqxdhRecordLiftInterface (EnvEffects WorldSpec RecordQuery)
open RegistrationNativeRawAdapter (TypedSpec)
open RegistrationNativeWire (Wire ledgerCodec)
variable {ι KemSK Value : Type} {base : OracleSpec ι} {n : Nat}

/-- Source-only state: owner handles, generated KEM handles and parsed accept attempts have separate coordinates. -/
structure State (n : Nat) (KemSK : Type) (mlSource : RegistrationNativeMldsa.Source) where
  server : RegistrationServerFrontendCompiler.State n
  beacons : RegistrationNativeBeaconFrontend.State mlSource
  pool : PqxdhLiveKemBirth.Pool KemSK
  parsedAccepts : Nat

abbrev M (n : Nat) (KemSK : Type) (mlSource : RegistrationNativeMldsa.Source) :=
  StateT (State n KemSK mlSource) ProbComp

def server {mlSource : RegistrationNativeMldsa.Source} {Result : Type}
    (work : StateT (RegistrationServerFrontendCompiler.State n) ProbComp Result) : M n KemSK mlSource Result :=
  fun before => (fun result => (result.1, { before with server := result.2 })) <$> work.run before.server

def world {mlSource : RegistrationNativeMldsa.Source} {Result : Type}
    (work : StateT (PqxdhRecordLiftWorld.State n) ProbComp Result) : M n KemSK mlSource Result :=
  server fun before => (fun result => (result.1,
    { before with world := { before.world with world := (result.2, before.world.world.2) } })) <$>
      work.run before.world.world.1

/-- The concrete indexed primitive interpretation keeps generated KEM secrets in the private pool and counts every actual primitive coin in the same World. -/
noncomputable def trusted (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (mlSource : RegistrationNativeMldsa.Source) :
    QueryImpl (RegistrationNativeBeaconFrontend.Trusted n KemSK) (M n KemSK mlSource)
  | .inl query => world (PqxdhRecordLiftWorld.effects query)
  | .inr query => fun before => do
      let result ← (PqxdhRecordLiftWorld.sampled
        ((RegistrationNativeKemInterface.source setup.baseImpl setup.kem RegistrationNativeKemInterface.OtherSpec
          (RegistrationNativeKemBackend.serverOther setup checks representation created.seed) query).run
            (before.server.world.auxiliary, before.pool))).run before.server.world.world.1
      pure (result.1.1,
        { before with
          pool := result.1.2.2
          server := { before.server with world := { before.server.world with
            auxiliary := result.1.2.1
            world := (result.2, before.server.world.world.2) } } })

/-- Beacon control and ordinary environment logs are threaded independently; the interpreted effects use the existing global World rather than a second cache. -/
noncomputable def beacon {mlSource : RegistrationNativeMldsa.Source} {Result : Type}
    (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (work : RegistrationNativeBeaconFrontend.M n KemSK mlSource RegistrationServerRoleBackend.State Result) :
    M n KemSK mlSource Result := fun before => do
  let result ← (simulateQ (trusted setup checks representation created mlSource)
    ((work.run before.beacons).run (RegistrationWorldAgreementCompiler.erase before.server.world))).run before
  pure (result.1.1.1,
    { result.2 with
      beacons := result.1.1.2
      server := { result.2.server with world :=
        RegistrationWorldAgreementCompiler.join result.1.2 result.2.server.world.world.1 } })

/-- Every established record command uses full native outer admission before the record program, below the unchanged secrecy layer. -/
noncomputable def record (setup : Setup base KemSK) (wire : Wire)
    (route : RawCtxServerRouting.SenderDecoder) (query : RecordQuery)
    (mlSource : RegistrationNativeMldsa.Source) : M n KemSK mlSource ((PqxdhRecordLiftInterface.RecordSpec .O).Range query) :=
  match query with
  | .inl query => world (CborRecordWorldSimulation.guarded setup (ledgerCodec wire) route (.inr (.inr (.inl query))))
  | .inr (owner, .inl plaintext) => fun before => match before.beacons[owner]? with
      | none => pure (none, before)
      | some selected => (world (CborRecordWorldSimulation.guarded setup (ledgerCodec wire) route
          (.inr (.inr (.inr (selected.worldOwner, .inl plaintext)))))).run before
  | .inr (owner, .inr raw) => fun before => match before.beacons[owner]? with
      | none => pure (.None, before)
      | some selected => (world (CborRecordWorldSimulation.guarded setup (ledgerCodec wire) route
          (.inr (.inr (.inr (selected.worldOwner, .inr raw)))))).run before

noncomputable def handler (setup : Setup base KemSK) (checks : Checks) (wire : Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (mlSource : RegistrationNativeMldsa.Source) (credential : RegistrationNativeMldsa.Credential mlSource) :
    QueryImpl TypedSpec (M n KemSK mlSource)
  | .inl coin => world (PqxdhRecordLiftWorld.effects (.inl coin))
  | .inr (.create edPin mlPin keyId) => beacon setup checks representation created
      (RegistrationNativeBeaconFrontend.create setup mlSource edPin mlPin keyId)
  | .inr (.bundle owner) => beacon setup checks representation created
      (RegistrationNativeBeaconFrontend.bundle setup mlSource wire owner)
  | .inr (.accept packet) => do
      modify fun state => { state with parsedAccepts := state.parsedAccepts + 1 }
      server (RegistrationServerSdkSource.accept setup (ledgerCodec wire) checks route mlSource.verify representation created packet)
  | .inr (.build session application) => server
      (RegistrationServerSdkSource.build setup (ledgerCodec wire) checks
        (RegistrationNativeMldsa.owned mlSource credential) wire.encodeResponse session application)
  | .inr (.finish owner packet) => beacon setup checks representation created
      (RegistrationNativeBeaconFrontend.finish setup mlSource wire owner packet)
  | .inr (.hmac key message) => pure (setup.hmac.eval key message)
  | .inr (.hash bytes) => world (PqxdhRecordLiftWorld.effects (.inr (.hash bytes)))
  | .inr (.serverSend keyId plaintext) => record setup wire route (.inl (.inl (plaintext, keyId))) mlSource
  | .inr (.serverRaw raw) => record setup wire route (.inl (.inr raw)) mlSource
  | .inr (.beaconSend owner plaintext) => record setup wire route (.inr (owner, .inl plaintext)) mlSource
  | .inr (.beaconRaw owner raw) => record setup wire route (.inr (owner, .inr raw)) mlSource

/-- The main source experiment retains the literal original hidden-bit/fresh-message ledger and the complete ML-pin-aware native transcript. -/
noncomputable def run (setup : Setup base KemSK) (checks : Checks) (wire : Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (mlSource : RegistrationNativeMldsa.Source) (credential : RegistrationNativeMldsa.Credential mlSource)
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value) (before : State n KemSK mlSource) :=
  RegistrationNativeFullCompiler.run setup.source.crypto wire created.server.server.metadata.sender bounds
    (handler setup checks wire route representation created mlSource credential) mode work before

/-- The final native APP event keeps the original broad verified-key eligibility. Exact-bundle membership is only a separately named reduction subcase. -/
noncomputable def app (setup : Setup base KemSK) (checks : Checks) (wire : Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (mlSource : RegistrationNativeMldsa.Source) (credential : RegistrationNativeMldsa.Credential mlSource)
    (bounds : PqxdhDeploymentInterface.FreshBounds) (budget : PqxdhDeploymentInterface.Budget)
    (claim : Value → Option (Nat × Pqxdh.Bytes))
    (work : OracleComp (RegistrationNativeInterface.ModeSpec .P) Value) (before : State n KemSK mlSource) :=
  RegistrationNativeEvents.ceAppEvent setup.source.crypto wire created.server.server.metadata.sender budget claim <$>
    run setup checks wire route representation created mlSource credential bounds .P work before


/-- Private actual Server startup includes runtime initialization, classical seed sampling, mandatory Server ML key generation, native World initialization and pure pin selection. -/
structure Initial (n : Nat) (KemSK : Type) (mlSource : RegistrationNativeMldsa.Source) where
  created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)
  credential : RegistrationNativeMldsa.Credential mlSource
  state : State n KemSK mlSource

structure Public where
  identity : PqxdhJointIdentity.PublicIdentity
  mldsaPublic : Std.Array U8 1952#usize
  serverKeyId : U64

def Initial.public {mlSource : RegistrationNativeMldsa.Source} (initial : Initial n KemSK mlSource) : Public :=
  ⟨initial.created.publicIdentity, initial.credential.publicKey, initial.created.server.server.metadata.sender⟩

private abbrev PeerMetadata := Std.Array U8 151#usize

noncomputable def start (setup : Setup base KemSK) (mlSource : RegistrationNativeMldsa.Source)
    (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64) :
    ProbComp (Option (Initial n KemSK mlSource)) := do
  let constructed ← (PqxdhRecordLiftWorld.sampled
    ((PqxdhLiveServerConstruction.construct (P := PeerMetadata) setup.joint ensureInit identityIndex serverKeyId none).run ())).run
      (PqxdhRecordLiftWorld.initial : PqxdhRecordLiftWorld.State n)
  match constructed.1.1 with
  | none => pure none
  | some created =>
    let generated ← (PqxdhRecordLiftWorld.sampled (RegistrationNativeMldsa.generate mlSource)).run constructed.2
    match generated.1 with
    | none => pure none
    | some credential =>
      let initialized ← (RegistrationWorldServerFrontend.start created credential.publicKey
        RegistrationServerRoleBackend.empty).run generated.2
      match initialized.1 with
      | .ok (.Some native) => pure (some ⟨created, credential,
          ⟨RegistrationServerFrontendCompiler.erase native, [], PqxdhLiveKemBirth.empty, 0⟩⟩)
      | _ => pure none

/-- The source probability starts at generated local identities and actual source failure branches. Its only public startup input is the generated public identity and public ML pin. -/
noncomputable def profile (setup : Setup base KemSK) (checks : Checks) (wire : Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (mlSource : RegistrationNativeMldsa.Source) (ensureInit : StateT Unit ProbComp Bool)
    (identityIndex : Nat) (serverKeyId : U64) (bounds : PqxdhDeploymentInterface.FreshBounds)
    (mode : PqxdhDeploymentInterface.Mode)
    (adversary : Public → OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (event : RegistrationNativeEvents.Observed Value (State n KemSK mlSource) → Bool) : ProbComp Bool := do
  let initialized ← start setup mlSource ensureInit identityIndex serverKeyId
  match initialized with
  | none => pure false
  | some initial => event <$> (run setup checks wire route representation initial.created mlSource initial.credential
      bounds mode (adversary initial.public) initial.state)


/-- A successful actual source KEM birth names the genuine generated private pair and the exact appended pool handle; public-key equality is never substituted for ownership. -/
theorem trusted_create_generated (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (mlSource : RegistrationNativeMldsa.Source)
    (before : State n KemSK mlSource)
    (result : (Nat × PqxdhKemIndCca.MlKem768PublicKey) × State n KemSK mlSource)
    (reached : result ∈ support ((trusted setup checks representation created mlSource
      (.inr (.inr (.inl .create)))).run before)) :
    ∃ pair ∈ support (simulateQ (PqxdhInitializerSecrecy.kemAmbientImpl setup.baseImpl) setup.kem.keygen),
      result.1 = (before.pool.keys.length, pair.1) ∧ result.2.pool.keys = before.pool.keys ++ [pair] := by
  simp only [trusted, PqxdhRecordLiftWorld.sampled, StateT.run, bind_pure_comp, Functor.map_map, support_map] at reached
  obtain ⟨inner, sampled, rfl⟩ := reached
  have actual : inner.1 ∈ support ((RegistrationNativeKemInterface.source setup.baseImpl setup.kem
      RegistrationNativeKemInterface.OtherSpec
      (RegistrationNativeKemBackend.serverOther setup checks representation created.seed)
      (.inr (.inl .create))).run (before.server.world.auxiliary, before.pool)) := by
    apply OracleComp.support_simulateQ_run'_subset PqxdhRecordLiftWorld.countCoin _ before.server.world.world.1.primitive.1.uniform
    rw [StateT.run'_eq, support_map]
    exact Set.mem_image_of_mem Prod.fst sampled
  exact RegistrationNativeKemInterface.create_generated setup.baseImpl setup.kem
    RegistrationNativeKemInterface.OtherSpec
    (RegistrationNativeKemBackend.serverOther setup checks representation created.seed) _ inner.1 actual

end BeaconcryptCore.Computational.RegistrationNativeExperiment

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeExperiment.trusted_create_generated' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeExperiment.trusted_create_generated
