-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.AdapterPublicWrapperCopy
import BeaconcryptCore.Computational.RegistrationNativeExperiment

/-! Private source objects are related to the native generated credentials and indexed KEM pool by their actual object views. Public-key equality never selects a private key or handle. The relation retains source control, full native binding, current assigned Beacon identifier and complete record kernel; standard map/set footprints are separate per-operation contracts. -/
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
namespace BeaconcryptCore.Refinement.AdapterPublicWrapperState
open BeaconcryptCore.Computational
open PublicWrapperPlatform AdapterPublicWrapperStorage
variable [material : Material] [platform : Platform] [ed : AdapterInitEdPrimitive.Operations]

structure MaterialView (source : RegistrationNativeMldsa.Source) (KemSK : Type) where
  edPublic : ed.PublicKey → Std.Array U8 32#usize
  edSecret : material.EdSecretKey → PqxdhJointIdentity.IdentitySeed
  kxPublic : material.KxPublicKey → Std.Array U8 32#usize
  kxSecret : material.KxSecretKey → PqxdhJointGapDh.ScalarBytes
  kemPublic : material.KemPublicKey → PqxdhKemIndCca.MlKem768PublicKey
  kemSecret : material.KemSecretKey → KemSK
  mldsa : material.MldsaIdentity → RegistrationNativeMldsa.Credential source

variable {source : RegistrationNativeMldsa.Source} {KemSK : Type}

def KxPair (view : MaterialView source KemSK) (stored : beaconcrypt_crypto.crypto_kx.KeyPair)
    (secret : PqxdhJointGapDh.ScalarBytes) (publicKey : Std.Array U8 32#usize) : Prop :=
  view.kxSecret stored.secret_key = secret ∧ view.kxPublic stored.public_key = publicKey

def KemPair (view : MaterialView source KemSK) (pool : PqxdhLiveKemBirth.Pool KemSK)
    (stored : beaconcrypt_crypto.crypto_kem.mlkem768.KeyPair) (handle : Nat)
    (publicKey : PqxdhKemIndCca.MlKem768PublicKey) : Prop :=
  view.kemPublic stored.public_key = publicKey ∧ pool.keys[handle]? = some (publicKey, view.kemSecret stored.secret_key)

def Phase (view : MaterialView source KemSK) (pool : PqxdhLiveKemBirth.Pool KemSK)
    (owner : RegistrationNativeBeaconFrontend.Owner source) (stored : beaconcrypt_public_wrapper.beacon.BeaconState)
    (world : Option PqxdhRecordLiftBeacon.Phase) : Prop :=
  match stored, owner.phase with
  | .Fresh control prekey kem, .fresh =>
      control.expected_server_binding = owner.pin.binding ∧
      KxPair view prekey owner.prekeyScalar owner.prekeyPublic ∧ KemPair view pool kem owner.kemHandle owner.kemPublic ∧
      world = some (.inactive .fresh)
  | .FreshWithCoins control prekey oneTime kem, .freshWithCoins scalar =>
      control.expected_server_binding = owner.pin.binding ∧
      KxPair view prekey owner.prekeyScalar owner.prekeyPublic ∧ view.kxSecret oneTime.secret_key = scalar ∧
      KemPair view pool kem owner.kemHandle owner.kemPublic ∧ world = some (.inactive .freshWithCoins)
  | .InitSent pending prekey oneTime kem, .initSent retained scalar =>
      pending = retained ∧ KxPair view prekey owner.prekeyScalar owner.prekeyPublic ∧ view.kxSecret oneTime.secret_key = scalar ∧
      KemPair view pool kem owner.kemHandle owner.kemPublic ∧ world = some (.inactive .initSent)
  | .Established control binding manager, .established completed =>
      control = completed.control ∧ binding = completed.binding ∧
      ∃ kernel, manager.refined.kernel = some kernel ∧
        world = some (.established ⟨binding.assigned_key_id, control, binding.associated_data⟩ kernel)
  | .Aborted control, .aborted retained => control = retained ∧ world = some (.inactive .aborted)
  | _, _ => False

def currentId (owner : RegistrationNativeBeaconFrontend.Owner source) : U64 :=
  match owner.phase with
  | .established completed => completed.binding.assigned_key_id
  | _ => owner.pin.binding.identity_key_id

structure Beacon (view : MaterialView source KemSK) (joint : PqxdhJointIdentity.Primitives)
    (pool : PqxdhLiveKemBirth.Pool KemSK) (stored : beaconcrypt_public_wrapper.beacon.Beacon)
    (owner : RegistrationNativeBeaconFrontend.Owner source) (world : Option PqxdhRecordLiftBeacon.Phase) : Prop where
  identityPublic : view.edPublic stored.identity_key.public_key = PqxdhRootTableInitialization.rootArray (joint.publicKeys owner.identitySeed).ed25519
  identitySecret : view.edSecret stored.identity_key.secret_key = owner.identitySeed
  mldsa : view.mldsa stored.authentication.identity = owner.mldsa
  pin : stored.authentication.server_pin = owner.pin
  serverPublic : view.edPublic stored.server_id = owner.pin.binding.identity_public_key
  identifier : stored.identity_key_kid = currentId owner
  phase : Phase view pool owner stored.state world

structure ServerIdentity (view : MaterialView source KemSK) (stored : beaconcrypt_public_wrapper.server.ServerIdentity)
    (created : PqxdhLiveServerConstruction.Created Unit) (credential : RegistrationNativeMldsa.Credential source) : Prop where
  publicKey : view.edPublic stored.identity_key.public_key = created.server.server.identity
  secret : view.edSecret stored.identity_key.secret_key = created.seed
  mldsa : view.mldsa stored.mldsa_identity = credential
  identifier : stored.identity_key_kid = created.server.server.metadata.sender

structure Server (view : MaterialView source KemSK) (containers : Views)
    (created : PqxdhLiveServerConstruction.Created Unit) (credential : RegistrationNativeMldsa.Credential source)
    (stored : beaconcrypt_public_wrapper.server.Server) {n : Nat} (native : RegistrationServerFrontendCompiler.State n) : Prop where
  identity : ServerIdentity view (platform.arcView stored.identity) created credential
  control : stored.control = native.control
  pinIdentity : native.pin.binding.identity_public_key = created.server.server.identity
  pinIdentifier : native.pin.binding.identity_key_id = created.server.server.metadata.sender
  pinMldsa : native.pin.public_key = credential.publicKey
  replay : ReplayRelated containers stored.consumed_registrations native.consumed
  peers : ∃ records, native.world.world.1.server = some records ∧
    records.sender = created.server.server.metadata.sender ∧
    records.records.server.identity = created.server.server.identity ∧
    PeersRelated containers stored.known_ids records.records.server.peers

def Token (stored : beaconcrypt_public_wrapper.server.RegistrationOutput) (native : peer.ConsumedRegistration) : Prop :=
  stored.registration = native ∧ stored.registration_id = native.agreement.pending.registration_id.bytes

omit platform in
theorem installed (view : MaterialView source KemSK) (joint : PqxdhJointIdentity.Primitives)
    (pool : PqxdhLiveKemBirth.Pool KemSK) (stored : beaconcrypt_public_wrapper.beacon.Beacon)
    (owner : RegistrationNativeBeaconFrontend.Owner source) (world : Option PqxdhRecordLiftBeacon.Phase)
    (related : Beacon view joint pool stored owner world) (completed : registration.CompletedBeacon) :
    Beacon view joint pool
      ({ stored with identity_key_kid := completed.binding.assigned_key_id, state := .Established completed.control completed.binding ⟨⟨some completed.kernel⟩⟩ })
      { owner with phase := .established ⟨completed.control, completed.binding, completed.application⟩ }
      (some (.established ⟨completed.binding.assigned_key_id, completed.control, completed.binding.associated_data⟩ completed.kernel)) := by
  exact ⟨related.identityPublic, related.identitySecret, related.mldsa, related.pin, related.serverPublic,
    rfl, rfl, rfl, completed.kernel, rfl, rfl⟩

omit platform in
theorem aborted (view : MaterialView source KemSK) (joint : PqxdhJointIdentity.Primitives)
    (pool : PqxdhLiveKemBirth.Pool KemSK) (stored : beaconcrypt_public_wrapper.beacon.Beacon)
    (owner : RegistrationNativeBeaconFrontend.Owner source) (world : Option PqxdhRecordLiftBeacon.Phase)
    (related : Beacon view joint pool stored owner world)
    (pending : registration.BeaconPending) (oneTime : PqxdhJointGapDh.ScalarBytes)
    (before : owner.phase = .initSent pending oneTime) (control : pqxdh.BeaconAborted) :
    Beacon view joint pool { stored with state := .Aborted control }
      { owner with phase := .aborted control } (some (.inactive .aborted)) := by
  refine ⟨related.identityPublic, related.identitySecret, related.mldsa, related.pin, related.serverPublic,
    ?_, rfl, rfl⟩
  simpa only [currentId, before] using related.identifier

omit platform in
theorem pending (view : MaterialView source KemSK) (joint : PqxdhJointIdentity.Primitives)
    (pool : PqxdhLiveKemBirth.Pool KemSK) (stored : beaconcrypt_public_wrapper.beacon.Beacon)
    (owner : RegistrationNativeBeaconFrontend.Owner source) (world : Option PqxdhRecordLiftBeacon.Phase)
    (related : Beacon view joint pool stored owner world)
    (identifier : currentId owner = owner.pin.binding.identity_key_id)
    (pending : registration.BeaconPending) (prekey oneTime : beaconcrypt_crypto.crypto_kx.KeyPair)
    (kem : beaconcrypt_crypto.crypto_kem.mlkem768.KeyPair) (scalar : PqxdhJointGapDh.ScalarBytes)
    (prekeyView : KxPair view prekey owner.prekeyScalar owner.prekeyPublic)
    (oneTimeView : view.kxSecret oneTime.secret_key = scalar)
    (kemView : KemPair view pool kem owner.kemHandle owner.kemPublic) :
    Beacon view joint pool { stored with state := .InitSent pending prekey oneTime kem }
      { owner with phase := .initSent pending scalar } (some (.inactive .initSent)) := by
  exact ⟨related.identityPublic, related.identitySecret, related.mldsa, related.pin, related.serverPublic,
    related.identifier.trans identifier, rfl, prekeyView, oneTimeView, kemView, rfl⟩

theorem replay_reserved (view : MaterialView source KemSK) (containers : Views)
    (created : PqxdhLiveServerConstruction.Created Unit) (credential : RegistrationNativeMldsa.Credential source)
    (stored : beaconcrypt_public_wrapper.server.Server) {n : Nat} (native : RegistrationServerFrontendCompiler.State n)
    (related : Server view containers created credential stored native)
    (result : core.result.Result Unit platform.ReserveError × ReplaySet)
    (preserves : ReplayReserve containers stored.consumed_registrations result) :
    Server view containers created credential { stored with consumed_registrations := result.2 } native := by
  exact { related with replay := replay_reserve containers _ _ result related.replay preserves }

theorem replay_inserted (view : MaterialView source KemSK) (containers : Views)
    (created : PqxdhLiveServerConstruction.Created Unit) (credential : RegistrationNativeMldsa.Credential source)
    (stored : beaconcrypt_public_wrapper.server.Server) {n : Nat} (native : RegistrationServerFrontendCompiler.State n)
    (related : Server view containers created credential stored native)
    (identifier : Std.Array U8 64#usize) (result : Bool × ReplaySet)
    (updates : ReplayInsert containers stored.consumed_registrations identifier result) :
    Server view containers created credential { stored with consumed_registrations := result.2 }
      { native with consumed := inserted native.consumed identifier } := by
  exact { related with replay := replay_insert containers _ _ identifier result related.replay updates }

theorem peer_reserved (view : MaterialView source KemSK) (containers : Views)
    (created : PqxdhLiveServerConstruction.Created Unit) (credential : RegistrationNativeMldsa.Credential source)
    (stored : beaconcrypt_public_wrapper.server.Server) {n : Nat} (native : RegistrationServerFrontendCompiler.State n)
    (related : Server view containers created credential stored native)
    (result : core.result.Result Unit platform.ReserveError × PeerMap)
    (preserves : PeerReserve containers stored.known_ids result) :
    Server view containers created credential { stored with known_ids := result.2 } native := by
  rcases related.peers with ⟨records, reached, sender, identity, peers⟩
  exact { related with peers := ⟨records, reached, sender, identity, peer_reserve containers _ _ result peers preserves⟩ }

omit platform ed material in
def retain (accepted : agreement.ServerAgreement) (inserted : Bool) :
    RustM (Option beaconcrypt_public_wrapper.server.RegistrationOutput) := do
  let pending ← peer.begin_registration_insert accepted
  let requested ← pending.request
  let identifier ← pqxdh.RegistrationId.as_bytes requested
  let consumed ← pending.resume inserted
  .ok (Option.map (fun value => ⟨value, identifier⟩) consumed)

omit platform ed material in
theorem retain_exact (accepted : agreement.ServerAgreement) (inserted : Bool) :
    retain accepted inserted = .ok (if inserted then some ⟨⟨accepted⟩, accepted.pending.registration_id.bytes⟩ else none) := by
  simp only [retain, peer.begin_registration_insert, PeerOwnership.registration_insert_request,
    pqxdh.RegistrationId.as_bytes, PeerOwnership.registration_insert_resume, bind_tc_ok]
  cases inserted <;> rfl

omit platform ed material in
def withPeer {n : Nat} (native : RegistrationServerFrontendCompiler.State n) (identifier : U64)
    (installed : RawCtxServerRouting.Peer (Std.Array U8 281#usize)) : RegistrationServerFrontendCompiler.State n :=
  match native.world.world.1.server with
  | none => native
  | some records =>
      let peers := Function.update records.records.server.peers identifier (some installed)
      let server := { records.records.server with peers := peers }
      let records := { records with records := { records.records with server := server } }
      let world := { native.world.world.1 with server := some records }
      { native with world := { native.world with world := (world, native.world.world.2) } }

theorem peer_inserted (view : MaterialView source KemSK) (containers : Views)
    (created : PqxdhLiveServerConstruction.Created Unit) (credential : RegistrationNativeMldsa.Credential source)
    (stored : beaconcrypt_public_wrapper.server.Server) {n : Nat} (native : RegistrationServerFrontendCompiler.State n)
    (related : Server view containers created credential stored native)
    (identifier : U64) (back : Entry → PeerMap) (value : Remote ed.PublicKey)
    (result : Remote ed.PublicKey × (Remote ed.PublicKey → Vacant))
    (installed : RawCtxServerRouting.Peer (Std.Array U8 281#usize))
    (updates : VacantInsert containers stored.known_ids identifier back value result)
    (viewed : peerView value = some installed) :
    Server view containers created credential { stored with known_ids := back (.Vacant (result.2 result.1)) }
      (withPeer native identifier installed) := by
  rcases related.peers with ⟨records, reached, sender, identity, peers⟩
  unfold withPeer
  rw [reached]
  refine { related with peers := ?_ }
  exact ⟨_, rfl, sender, identity, peer_insert containers _ _ identifier back value result installed peers updates viewed⟩

end BeaconcryptCore.Refinement.AdapterPublicWrapperState

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicWrapperState.installed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicWrapperState.installed

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicWrapperState.aborted' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicWrapperState.aborted

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicWrapperState.pending' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicWrapperState.pending

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicWrapperState.replay_reserved' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicWrapperState.replay_reserved

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicWrapperState.replay_inserted' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicWrapperState.replay_inserted

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicWrapperState.peer_reserved' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicWrapperState.peer_reserved

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicWrapperState.retain_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicWrapperState.retain_exact

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicWrapperState.peer_inserted' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicWrapperState.peer_inserted
