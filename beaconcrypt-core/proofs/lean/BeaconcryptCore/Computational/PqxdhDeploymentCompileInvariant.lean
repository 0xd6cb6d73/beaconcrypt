-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhDeploymentCompileFootprint

/-! The simulation invariant of the CE-3 trial and its preservation. Beyond the compile-step invariant `Inv`, the invariant records that every pending token's Beacon identity is the identity key read from the raw accept bytes logged under its handle, that every logged handle is below the session counter, and that every owner's phase is reconstructible from the public log: the pin and key ID of its `create`, the identity key read from its bundle bytes once InitSent, and its outer key ID, control and associated data once Established. Preservation uses two of the approved codec contracts: `Phase1ReadBack` for the bundle bytes and `Phase2ReadBack` for the Server identity in a build response. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhDeploymentCompileInvariant
open PqxdhServerAuthExperiment PqxdhServerAuthNative PqxdhJointIdentity PqxdhJointGapDh
open PqxdhDeploymentCompile (Kernel Identity Local Log merge compileImpl identityOf peerView ownerView)
open PqxdhDeploymentCompileRegistration (Installed Copied)
open PqxdhDeploymentCompileStep (Inv compiledImpl)
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}

/-- The public reconstruction of one owner from the log: its `create` entry, its pinned Server identity, and, by phase, its expected binding, its bundle's identity key, or its established outer key ID, control and associated data. -/
def OwnerShape (codec : Codec Reader Response) (log : Log) (index : Nat)
    (owner : PqxdhRegistrationSchedule.Owner KemSK) : Prop :=
  ∃ pin keyId, log.owners[index]? = some (pin, keyId) ∧ owner.beacon.serverIdentity = pin ∧
    match owner.beacon.phase with
    | .fresh control _ _ => control.expected_server_binding = ⟨pin, keyId⟩
    | .freshWithCoins control _ _ _ => control.expected_server_binding = ⟨pin, keyId⟩
    | .initSent control _ _ _ => control.expected_server_binding = ⟨pin, keyId⟩ ∧
        ∃ bytes, log.bundles index = some bytes ∧ identityOf codec bytes = some control.beacon_identity_public_key
    | .established control associatedData _ =>
        ownerView codec log index = some (owner.beacon.identityKeyId, control, associatedData)
    | .aborted _ => True

/-- The full simulation invariant. -/
structure Good (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (copies : Local)
    (native : PqxdhRegistrationSchedule.State KemSK) : Prop where
  keyId : native.shared.2.server.identityKeyId = setup.serverKeyId
  installed : Installed copies native.shared.2
  serverVisible : ∀ kid peer, native.shared.2.server.server.peers kid = some peer →
    peerView codec copies.log kid = some (native.shared.2.server.server.identity, peer.identity)
  count : copies.log.owners.length = native.owners.length
  copied : Copied copies native
  owners : ∀ index owner, native.owners[index]? = some owner → OwnerShape codec copies.log index owner
  pending : ∀ session token, native.shared.2.pending session = some token →
    session < native.shared.2.sessions ∧ ∃ raw, copies.log.accepts session = some raw ∧
      identityOf codec raw = some token.pending.beacon_identity_public_key
  accepts : ∀ session raw, copies.log.accepts session = some raw → session < native.shared.2.sessions

/-- The full invariant implies the compile-step invariant. -/
theorem good_inv (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (copies : Local)
    (native : PqxdhRegistrationSchedule.State KemSK) (good : Good setup codec copies native) :
    Inv setup codec copies native := by
  refine ⟨good.keyId, good.installed, good.serverVisible, good.count, good.copied, ?_⟩
  intro index owner control associatedData kernel found phase
  obtain ⟨pin, keyId, _, _, shape⟩ := good.owners index owner found
  simpa only [phase] using shape

/-- A source14 command run on the shared native state keeps the owners and returns an outcome of the original game computation. -/
theorem shared_footprint {Result : Type} (setup : Setup baseSpec KemSK) (serverSeed : IdentitySeed)
    (work : Game KemSK Result) (native : PqxdhRegistrationSchedule.State KemSK)
    (result : Result × PqxdhRegistrationSchedule.State KemSK)
    (supported : result ∈ support ((PqxdhRegistrationSchedule.onShared
      (evaluate setup serverSeed PqxdhRegistrationSchedule.observationScalar work)).run native)) :
    result.2.owners = native.owners ∧ (result.1, result.2.shared.2) ∈ support (work.run native.shared.2) := by
  refine ⟨?_, PqxdhRegistrationSchedule.shared_original setup serverSeed work native result supported⟩
  rw [PqxdhRegistrationSchedule.onShared_run, support_map] at supported
  obtain ⟨reached, _, rfl⟩ := supported
  rfl

/-- The invariant survives any step that keeps the log, the owners, the Server peer map, identity and key ID, the pending tokens and the session counter. -/
theorem good_frame (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (copies : Local)
    (native after : PqxdhRegistrationSchedule.State KemSK) (good : Good setup codec copies native)
    (owners : after.owners = native.owners)
    (fixed : PqxdhDeploymentCompileFootprint.ServerFixed native.shared.2 after.shared.2) :
    Good setup codec copies after := by
  obtain ⟨server, keyId, pending, sessions⟩ := fixed
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [keyId]
    exact good.keyId
  · intro kid current copied
    rw [server]
    exact good.installed kid current copied
  · rw [server]
    exact good.serverVisible
  · rw [owners]
    exact good.count
  · intro index current copied
    rw [owners]
    exact good.copied index current copied
  · rw [owners]
    exact good.owners
  · rw [pending, sessions]
    exact good.pending
  · rw [sessions]
    exact good.accepts

/-- The public HMAC and BLAKE2b commands keep the invariant. -/
theorem good_public (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (serverSeed : IdentitySeed) (request : PqxdhRegistrationSchedule.Request)
    (kind : match request with
      | .hmac _ _ | .hash _ => True
      | _ => False)
    (copies : Local) (native : PqxdhRegistrationSchedule.State KemSK) (good : Good setup codec copies native)
    (result : PqxdhRegistrationSchedule.QuerySpec request × PqxdhRegistrationSchedule.State KemSK)
    (supported : result ∈ support ((PqxdhRegistrationSchedule.handler setup codec checks serverSeed (.inr request)).run native)) :
    Good setup codec copies result.2 := by
  rcases request with _ | _ | _ | _ | _ | ⟨key, message⟩ | bytes | _
  all_goals simp only at kind
  · simp only [PqxdhRegistrationSchedule.handler, ← hmac_native setup serverSeed PqxdhRegistrationSchedule.observationScalar]
      at supported
    obtain ⟨owners, reached⟩ := shared_footprint setup serverSeed _ native result supported
    exact good_frame setup codec copies native result.2 good owners
      (PqxdhDeploymentCompileFootprint.hmac_fixed key message _ _ reached)
  · simp only [PqxdhRegistrationSchedule.handler, ← hash_native setup serverSeed PqxdhRegistrationSchedule.observationScalar]
      at supported
    obtain ⟨owners, reached⟩ := shared_footprint setup serverSeed _ native result supported
    exact good_frame setup codec copies native result.2 good owners
      (PqxdhDeploymentCompileFootprint.hash_fixed bytes _ _ reached)

/-- Owner shapes read only the created, bundle and finish entries of the log. -/
theorem ownerShape_accepts (codec : Codec Reader Response) (log : Log) (accepts : Nat → Option Pqxdh.Bytes)
    (index : Nat) (owner : PqxdhRegistrationSchedule.Owner KemSK) :
    OwnerShape codec { log with accepts := accepts } index owner ↔ OwnerShape codec log index owner := Iff.rfl

/-- Logging an accept at a handle with no earlier entry keeps every reconstructible peer. -/
theorem peerView_accept (codec : Codec Reader Response) (log : Log) (session : Nat) (raw : Pqxdh.Bytes)
    (fresh : log.accepts session = none) (kid : Std.U64) (view : Identity × Identity)
    (found : peerView codec log kid = some view) :
    peerView codec { log with accepts := Function.update log.accepts session (some raw) } kid = some view := by
  simp only [peerView, Option.bind_eq_bind, Option.bind_eq_some_iff] at found ⊢
  obtain ⟨built, builtEq, raw', rawEq, rest⟩ := found
  have different : built.1 ≠ session := by
    intro same
    rw [same, fresh] at rawEq
    cases rawEq
  exact ⟨built, builtEq, raw', by rw [Function.update_of_ne different]; exact rawEq, rest⟩

/-- A raw accept keeps the invariant; a successful accept logs its bytes under the returned handle. -/
theorem good_accept (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (serverSeed : IdentitySeed) (raw : Pqxdh.Bytes) (copies : Local) (native : PqxdhRegistrationSchedule.State KemSK)
    (good : Good setup codec copies native) (result : Option Nat × PqxdhRegistrationSchedule.State KemSK)
    (supported : result ∈ support ((PqxdhRegistrationSchedule.handler setup codec checks serverSeed
      (.inr (.accept raw))).run native)) :
    Good setup codec { copies with log := PqxdhDeploymentCompile.logReply copies.log (.accept raw) result.1 } result.2 := by
  simp only [PqxdhRegistrationSchedule.handler,
    ← accept_native setup codec checks serverSeed PqxdhRegistrationSchedule.observationScalar] at supported
  obtain ⟨owners, reached⟩ := shared_footprint setup serverSeed _ native result supported
  obtain ⟨server, keyId, sessions, others, rejected, accepted⟩ :=
    PqxdhDeploymentCompileFootprint.accept_footprint setup codec checks _ raw _ _ reached
  have freshLog : copies.log.accepts native.shared.2.sessions = none := by
    cases logged : copies.log.accepts native.shared.2.sessions with
    | none => rfl
    | some old => exact absurd (good.accepts _ old logged) (Nat.lt_irrefl _)
  rcases outcome : result.1 with _ | handle
  · have pending := rejected outcome
    simp only [PqxdhDeploymentCompile.logReply]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [keyId]; exact good.keyId
    · intro kid current copied
      rw [server]
      exact good.installed kid current copied
    · rw [server]; exact good.serverVisible
    · rw [owners]; exact good.count
    · intro index current copied
      rw [owners]
      exact good.copied index current copied
    · rw [owners]; exact good.owners
    · intro session token found
      rw [pending] at found
      obtain ⟨below, logged⟩ := good.pending session token found
      exact ⟨by rw [sessions]; omega, logged⟩
    · intro session logged found
      have below := good.accepts session logged found
      rw [sessions]
      omega
  · obtain ⟨handleEq, token, stored, identified⟩ := accepted handle outcome
    subst handleEq
    simp only [PqxdhDeploymentCompile.logReply]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [keyId]; exact good.keyId
    · intro kid current copied
      rw [server]
      exact good.installed kid current copied
    · intro kid peer found
      rw [server] at found ⊢
      exact peerView_accept codec copies.log _ raw freshLog kid _ (good.serverVisible kid peer found)
    · rw [owners]; exact good.count
    · intro index current copied
      rw [owners]
      exact good.copied index current copied
    · rw [owners]; exact good.owners
    · intro session found_token found
      by_cases same : session = native.shared.2.sessions
      · subst same
        rw [stored, Option.some.injEq] at found
        subst found
        refine ⟨by rw [sessions]; omega, raw, Function.update_self .., identified⟩
      · rw [others session same] at found
        obtain ⟨below, old, logged, oldIdentified⟩ := good.pending session found_token found
        exact ⟨by rw [sessions]; omega, old, by simp only [Function.update_of_ne same]; exact logged, oldIdentified⟩
    · intro session logged found
      rw [sessions]
      by_cases same : session = native.shared.2.sessions
      · omega
      · simp only [Function.update_of_ne same] at found
        have below := good.accepts session logged found
        omega

/-- Owner shapes do not read the build entries of the log. -/
theorem ownerShape_builds (codec : Codec Reader Response) (log : Log)
    (builds : Std.U64 → Option (Nat × PqxdhServerRegistrationPublication.Response))
    (index : Nat) (owner : PqxdhRegistrationSchedule.Owner KemSK) :
    OwnerShape codec { log with builds := builds } index owner ↔ OwnerShape codec log index owner := Iff.rfl

/-- A build keeps the invariant under the approved Phase 2 read-back contract: the new peer is reconstructible from the logged accept bytes of its session and the Server identity in its response. -/
theorem good_build (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (serverSeed : IdentitySeed) (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec)
    (session : Nat) (payload : Option Pqxdh.Bytes) (copies : Local) (native : PqxdhRegistrationSchedule.State KemSK)
    (good : Good setup codec copies native)
    (result : Option PqxdhServerRegistrationPublication.Response × PqxdhRegistrationSchedule.State KemSK)
    (supported : result ∈ support ((PqxdhRegistrationSchedule.handler setup codec checks serverSeed
      (.inr (.build session payload))).run native)) :
    Good setup codec
      { copies with log := PqxdhDeploymentCompile.logReply copies.log (.build session payload) result.1 } result.2 := by
  simp only [PqxdhRegistrationSchedule.handler,
    ← build_native setup codec checks serverSeed PqxdhRegistrationSchedule.observationScalar] at supported
  obtain ⟨owners, reached⟩ := shared_footprint setup serverSeed _ native result supported
  obtain ⟨identity, keyId, sessions, others, removed, rejected, published⟩ :=
    PqxdhDeploymentCompileFootprint.build_footprint setup codec checks session payload _ _ reached
  have pendingKept : ∀ other token, result.2.shared.2.pending other = some token →
      native.shared.2.pending other = some token := by
    intro other token found
    by_cases same : other = session
    · subst same
      rw [removed] at found
      cases found
    · rw [← others other same]
      exact found
  rcases outcome : result.1 with _ | response
  · have peers := rejected outcome
    simp only [PqxdhDeploymentCompile.logReply]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [keyId]; exact good.keyId
    · intro kid current copied
      rw [peers]
      exact good.installed kid current copied
    · rw [peers, identity]; exact good.serverVisible
    · rw [owners]; exact good.count
    · intro index current copied
      rw [owners]
      exact good.copied index current copied
    · rw [owners]; exact good.owners
    · intro other token found
      rw [sessions]
      exact good.pending other token (pendingKept other token found)
    · rw [sessions]; exact good.accepts
  · obtain ⟨token, kernel, fields, tokenFound, free, peers, written, fieldsIdentity⟩ := published response outcome
    obtain ⟨_, raw, logged, identified⟩ := good.pending session token tokenFound
    obtain ⟨decoded, decodedRead, _, _, serverRead, _, _⟩ := phase2 fields response.serialized written
    simp only [PqxdhDeploymentCompile.logReply]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [keyId]; exact good.keyId
    · intro kid current copied
      rw [peers]
      by_cases same : kid = response.keyId
      · subst same
        simp only [Function.update_self, ne_eq, reduceCtorEq, not_false_eq_true]
      · rw [Function.update_of_ne same]
        exact good.installed kid current copied
    · intro kid peer found
      rw [peers] at found
      rw [identity]
      by_cases same : kid = response.keyId
      · subst same
        simp only [Function.update_self, Option.some.injEq] at found
        subst found
        simp only [peerView, Function.update_self, Option.bind_eq_bind, Option.bind_some, logged,
          PqxdhDeploymentCompile.serverIdentityOf, decodedRead, serverRead, fieldsIdentity, identified,
          Option.pure_def]
      · rw [Function.update_of_ne same] at found
        have old := good.serverVisible kid peer found
        simpa only [peerView, Function.update_of_ne same] using old
    · rw [owners]; exact good.count
    · intro index current copied
      rw [owners]
      exact good.copied index current copied
    · rw [owners]; exact good.owners
    · intro other token found
      rw [sessions]
      exact good.pending other token (pendingKept other token found)
    · rw [sessions]; exact good.accepts

/-- Appending a created owner to the log keeps every earlier owner's reconstruction. -/
theorem ownerView_extend (codec : Codec Reader Response) (log : Log) (entry : PqxdhBeaconPhase2Preparation.Word32 × Std.U64)
    (index : Nat) (bound : index < log.owners.length) :
    ownerView codec { log with owners := log.owners ++ [entry] } index = ownerView codec log index := by
  simp only [ownerView, List.getElem?_append_left bound]

/-- Appending a created owner to the log keeps every earlier owner's shape. -/
theorem ownerShape_extend (codec : Codec Reader Response) (log : Log) (entry : PqxdhBeaconPhase2Preparation.Word32 × Std.U64)
    (index : Nat) (bound : index < log.owners.length) (owner : PqxdhRegistrationSchedule.Owner KemSK)
    (shape : OwnerShape codec log index owner) :
    OwnerShape codec { log with owners := log.owners ++ [entry] } index owner := by
  obtain ⟨pin, keyId, created, pinned, phase⟩ := shape
  refine ⟨pin, keyId, by rw [List.getElem?_append_left bound]; exact created, pinned, ?_⟩
  revert phase
  cases owner.beacon.phase with
  | established control associatedData kernel =>
      intro phase
      rw [ownerView_extend codec log entry index bound]
      exact phase
  | _ => exact id

/-- Owner creation keeps the invariant: the new Fresh owner is pinned and bound exactly as its logged `create`. -/
theorem good_create (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (serverSeed : IdentitySeed) (pin : PqxdhBeaconPhase2Preparation.Word32) (keyId : Std.U64) (copies : Local)
    (native : PqxdhRegistrationSchedule.State KemSK) (good : Good setup codec copies native)
    (result : Nat × PqxdhRegistrationSchedule.State KemSK)
    (supported : result ∈ support ((PqxdhRegistrationSchedule.handler setup codec checks serverSeed
      (.inr (.create pin keyId))).run native)) :
    Good setup codec { copies with log := { copies.log with owners := copies.log.owners ++ [(pin, keyId)] } }
      result.2 := by
  simp only [PqxdhRegistrationSchedule.handler, StateT.run, PqxdhRegistrationSchedule.create_source,
    mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at supported
  obtain ⟨identity, _, prekey, _, keys, _, rfl⟩ := supported
  refine ⟨good.keyId, good.installed, good.serverVisible, ?_, ?_, ?_, good.pending, good.accepts⟩
  · simp only [List.length_append, List.length_singleton, good.count]
  · intro index current copied
    obtain ⟨owner, control, associatedData, kernel, found, phase⟩ := good.copied index current copied
    have bound : index < native.owners.length := (List.getElem?_eq_some_iff.mp found).1
    exact ⟨owner, control, associatedData, kernel, by rw [List.getElem?_append_left bound]; exact found, phase⟩
  · intro index owner found
    by_cases bound : index < native.owners.length
    · rw [List.getElem?_append_left bound] at found
      exact ownerShape_extend codec copies.log (pin, keyId) index (good.count ▸ bound) owner
        (good.owners index owner found)
    · have last : index = native.owners.length := by
        have := (List.getElem?_eq_some_iff.mp found).1
        simp only [List.length_append, List.length_singleton] at this
        omega
      subst last
      rw [List.getElem?_append_right (le_refl _), Nat.sub_self] at found
      simp only [List.getElem?_cons_zero, Option.some.injEq] at found
      subst found
      refine ⟨pin, keyId, ?_, rfl, rfl⟩
      rw [List.getElem?_append_right (good.count ▸ le_refl _), good.count, Nat.sub_self]
      rfl

/-- Logging a bundle for one owner keeps every other owner's reconstruction. -/
theorem ownerShape_bundle (codec : Codec Reader Response) (log : Log) (index other : Nat) (bytes : Pqxdh.Bytes)
    (different : other ≠ index) (owner : PqxdhRegistrationSchedule.Owner KemSK)
    (shape : OwnerShape codec log other owner) :
    OwnerShape codec { log with bundles := Function.update log.bundles index (some bytes) } other owner := by
  obtain ⟨pin, keyId, created, pinned, phase⟩ := shape
  refine ⟨pin, keyId, created, pinned, ?_⟩
  revert phase
  cases owner.beacon.phase with
  | initSent control prekey oneTime kem =>
      rintro ⟨binding, logged, bytesOld, identified⟩
      exact ⟨binding, logged, by simp only [Function.update_of_ne different]; exact bytesOld, identified⟩
  | established control associatedData kernel =>
      intro view
      simpa only [ownerView, Function.update_of_ne different] using view
  | _ => exact id

/-- The bundle bytes of an owner read back, under the approved Phase 1 contract, to the owner's own identity key. -/
theorem identityOf_bundle (codec : Codec Reader Response) (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (candidate : PqxdhEd25519EufCma.Phase1Candidate) (bytes : Pqxdh.Bytes) (identity : PqxdhEd25519EufCma.Ed25519PublicKey)
    (written : codec.write1 candidate = some bytes)
    (encoded : candidate.identityKey = PqxdhEd25519EufCma.encodedIdentity identity) :
    identityOf codec bytes = some (PqxdhLivePhase1Bundle.identityArray identity) := by
  obtain ⟨reader, read, identityRead, _, _, _⟩ := phase1 candidate bytes written
  simp only [identityOf, read, identityRead, encoded, PqxdhEd25519EufCma.parseIdentity_encodedIdentity,
    Option.bind_eq_bind, Option.bind_some, Option.pure_def, PqxdhLivePhase1Bundle.identityArray]

/-- A Beacon bundle keeps the invariant under the approved Phase 1 read-back contract: a published bundle is logged and reads back to the identity key of the new InitSent control. -/
theorem good_bundle (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (serverSeed : IdentitySeed) (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec) (index : Nat)
    (copies : Local) (native : PqxdhRegistrationSchedule.State KemSK) (good : Good setup codec copies native)
    (result : Option Pqxdh.Bytes × PqxdhRegistrationSchedule.State KemSK)
    (supported : result ∈ support ((PqxdhRegistrationSchedule.handler setup codec checks serverSeed
      (.inr (.bundle index))).run native)) :
    Good setup codec { copies with log := PqxdhDeploymentCompile.logReply copies.log (.bundle index) result.1 }
      result.2 := by
  cases found : native.owners[index]? with
  | none =>
      simp only [PqxdhRegistrationSchedule.handler, PqxdhRegistrationSchedule.bundle, StateT.run_bind,
        StateT.run_get, pure_bind, found, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
      subst supported
      exact good
  | some owner =>
      simp only [PqxdhRegistrationSchedule.handler, StateT.run,
        PqxdhRegistrationSchedule.bundle_source setup codec index native owner found, support_map,
        Set.mem_image] at supported
      obtain ⟨reached, member, rfl⟩ := supported
      obtain ⟨rejected, published⟩ := PqxdhDeploymentCompileFootprint.bundle_owner setup codec index owner reached member
      have bound : index < native.owners.length := (List.getElem?_eq_some_iff.mp found).1
      rcases outcome : reached.1 with _ | bytes
      · have same := rejected outcome
        simp only [PqxdhDeploymentCompile.logReply, same, PqxdhDeploymentCompileRegistration.set_found _ index _ found]
        exact good
      · obtain ⟨fresh, prekey, oneTime, kem, candidate, phase, after, written, encoded⟩ := published bytes outcome
        have active : ¬ ∃ control associatedData kernel,
            owner.beacon.phase = .established control associatedData kernel := by
          rintro ⟨control, associatedData, kernel, established⟩
          rcases phase with phase | phase <;> rw [phase] at established <;> cases established
        simp only [PqxdhDeploymentCompile.logReply]
        refine ⟨good.keyId, good.installed, good.serverVisible, ?_, ?_, ?_, good.pending, good.accepts⟩
        · simp only [List.length_set, good.count]
        · intro other current copied
          obtain ⟨old, control, associatedData, kernel, oldFound, established⟩ := good.copied other current copied
          have different : other ≠ index := by
            intro same
            subst same
            rw [found, Option.some.injEq] at oldFound
            subst oldFound
            exact active ⟨control, associatedData, kernel, established⟩
          exact ⟨old, control, associatedData, kernel, by rw [List.getElem?_set_ne (Ne.symm different)]; exact oldFound,
            established⟩
        · intro other current currentFound
          by_cases same : other = index
          · subst same
            rw [List.getElem?_set_self bound, Option.some.injEq] at currentFound
            subst currentFound
            obtain ⟨pin, keyId, created, pinned, oldPhase⟩ := good.owners other owner found
            refine ⟨pin, keyId, created, by rw [after]; exact pinned, ?_⟩
            rw [after]
            dsimp only
            have binding : fresh.expected_server_binding = ⟨pin, keyId⟩ := by
              rcases phase with phase | phase <;> simpa only [phase] using oldPhase
            refine ⟨binding, bytes, Function.update_self .., ?_⟩
            exact identityOf_bundle codec phase1 candidate bytes _ written encoded
          · rw [List.getElem?_set_ne (Ne.symm same)] at currentFound
            exact ownerShape_bundle codec copies.log index other bytes same current
              (good.owners other current currentFound)

/-- Logging a finish for one owner keeps every other owner's reconstruction. -/
theorem ownerShape_finish (codec : Codec Reader Response) (log : Log) (index other : Nat) (raw : Pqxdh.Bytes)
    (different : other ≠ index) (owner : PqxdhRegistrationSchedule.Owner KemSK)
    (shape : OwnerShape codec log other owner) :
    OwnerShape codec { log with finishes := Function.update log.finishes index (some raw) } other owner := by
  obtain ⟨pin, keyId, created, pinned, phase⟩ := shape
  refine ⟨pin, keyId, created, pinned, ?_⟩
  revert phase
  cases owner.beacon.phase with
  | established control associatedData kernel =>
      intro view
      simpa only [ownerView, Function.update_of_ne different] using view
  | _ => exact id

/-- A Beacon finish keeps the invariant: a successful finish is logged, and the new Established owner's outer key ID, control and associated data are its public reconstruction. -/
theorem good_finish (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (serverSeed : IdentitySeed) (index : Nat) (raw : Pqxdh.Bytes) (copies : Local)
    (native : PqxdhRegistrationSchedule.State KemSK) (good : Good setup codec copies native)
    (result : Option Pqxdh.Bytes × PqxdhRegistrationSchedule.State KemSK)
    (supported : result ∈ support ((PqxdhRegistrationSchedule.handler setup codec checks serverSeed
      (.inr (.finish index raw))).run native)) :
    Good setup codec { copies with log := PqxdhDeploymentCompile.logReply copies.log (.finish index raw) result.1 }
      result.2 := by
  cases found : native.owners[index]? with
  | none =>
      change result ∈ support ((PqxdhRegistrationSchedule.finish setup codec index raw).run native) at supported
      rw [PqxdhRegistrationSchedule.finish_missing setup codec index raw native found, support_pure,
        Set.mem_singleton_iff] at supported
      subst supported
      exact good
  | some owner =>
      simp only [PqxdhRegistrationSchedule.handler, StateT.run,
        PqxdhRegistrationSchedule.finish_source setup codec index raw native owner found, support_map,
        Set.mem_image] at supported
      obtain ⟨reached, member, rfl⟩ := supported
      have fields := PqxdhRegistrationSchedule.program_fields setup codec _ native.shared reached member
      obtain ⟨rejected, published⟩ := PqxdhDeploymentCompileFootprint.finish_owner setup codec raw owner native.shared
        reached member
      have bound : index < native.owners.length := (List.getElem?_eq_some_iff.mp found).1
      have fixed : PqxdhDeploymentCompileFootprint.ServerFixed native.shared.2 reached.2.2 := by
        rw [fields]
        exact ⟨rfl, rfl, rfl, rfl⟩
      obtain ⟨server, keyId, pending, sessions⟩ := fixed
      have copiedKept : ∀ other current, copies.owners other = some current →
          ∃ owner' control associatedData kernel,
            (native.owners.set index reached.1.2)[other]? = some owner' ∧
            owner'.beacon.phase = .established control associatedData kernel := by
        intro other current copied
        obtain ⟨old, control, associatedData, kernel, oldFound, established⟩ := good.copied other current copied
        by_cases same : other = index
        · subst same
          rw [found, Option.some.injEq] at oldFound
          subst oldFound
          refine ⟨reached.1.2, control, associatedData, kernel, List.getElem?_set_self bound, ?_⟩
          rcases outcome : reached.1.1 with _ | plaintext
          · rcases rejected outcome with unchanged | ⟨control', prekey, oneTime, kem, initSent, _⟩
            · rw [unchanged]; exact established
            · rw [initSent] at established; cases established
          · obtain ⟨control', prekey, oneTime, kem, _, _, initSent, _⟩ := published plaintext outcome
            rw [initSent] at established
            cases established
        · exact ⟨old, control, associatedData, kernel, by rw [List.getElem?_set_ne (Ne.symm same)]; exact oldFound,
            established⟩
      rcases outcome : reached.1.1 with _ | plaintext
      · simp only [PqxdhDeploymentCompile.logReply]
        refine ⟨by rw [keyId]; exact good.keyId, ?_, by rw [server]; exact good.serverVisible,
          by simp only [List.length_set, good.count], copiedKept, ?_, by rw [pending, sessions]; exact good.pending,
          by rw [sessions]; exact good.accepts⟩
        · intro kid current copied
          rw [server]
          exact good.installed kid current copied
        · intro other current currentFound
          by_cases same : other = index
          · subst same
            rw [List.getElem?_set_self bound, Option.some.injEq] at currentFound
            subst currentFound
            obtain ⟨pin, keyId', created, pinned, _⟩ := good.owners other owner found
            rcases rejected outcome with unchanged | ⟨control, prekey, oneTime, kem, _, aborted⟩
            · rw [unchanged]; exact good.owners other owner found
            · refine ⟨pin, keyId', created, by rw [aborted]; exact pinned, ?_⟩
              rw [aborted]
              trivial
          · rw [List.getElem?_set_ne (Ne.symm same)] at currentFound
            exact good.owners other current currentFound
      · obtain ⟨control, prekey, oneTime, kem, response, kernel, initSent, decoded, established⟩ :=
          published plaintext outcome
        simp only [PqxdhDeploymentCompile.logReply]
        refine ⟨by rw [keyId]; exact good.keyId, ?_, by rw [server]; exact good.serverVisible,
          by simp only [List.length_set, good.count], copiedKept, ?_, by rw [pending, sessions]; exact good.pending,
          by rw [sessions]; exact good.accepts⟩
        · intro kid current copied
          rw [server]
          exact good.installed kid current copied
        · intro other current currentFound
          by_cases same : other = index
          · subst same
            rw [List.getElem?_set_self bound, Option.some.injEq] at currentFound
            subst currentFound
            obtain ⟨pin, keyId', created, pinned, oldShape⟩ := good.owners other owner found
            rw [initSent] at oldShape
            obtain ⟨binding, bytes, logged, identified⟩ := oldShape
            refine ⟨pin, keyId', created, by rw [established]; exact pinned, ?_⟩
            rw [established]
            dsimp only
            simp only [ownerView, created, logged, identified, Function.update_self, decoded, Option.bind_eq_bind,
              Option.bind_some, Option.pure_def]
            rw [← binding]
          · rw [List.getElem?_set_ne (Ne.symm same)] at currentFound
            exact ownerShape_finish codec copies.log index other raw same current
              (good.owners other current currentFound)

/-- A compiled Server record command changes only the BLAKE2b cache of the source14 state, keeps the log, owners and owner counters, and holds a local kernel only for a peer that had a local copy or is installed. -/
theorem serverLocal_support (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (serverSeed : IdentitySeed)
    (query : RawCtxServerMixed.SourceSpec.Domain) (copies : Local) (native : PqxdhRegistrationSchedule.State KemSK)
    (result : (RawCtxServerMixed.SourceSpec.Range query × Local) × PqxdhRegistrationSchedule.State KemSK)
    (supported : result ∈ support ((simulateQ (PqxdhRegistrationJointRevealSchedule.native setup codec checks serverSeed)
      ((PqxdhDeploymentCompile.serverLocal setup codec route query).run copies)).run native)) :
    (∃ cache, result.2 = PqxdhDeploymentRecordCache.setCtx native cache) ∧ result.1.2.log = copies.log ∧
      result.1.2.owners = copies.owners ∧
      ∀ kid current, result.1.2.peers kid = some current →
        copies.peers kid ≠ none ∨ native.shared.2.server.server.peers kid ≠ none := by
  cases target : PqxdhDeploymentCompile.serverTarget route query with
  | none =>
      rw [PqxdhDeploymentCompileRecords.serverLocal_none setup codec route query copies target,
        PqxdhDeploymentCompileRecords.serverImpl_absent _ route codec.frameRead query _
          (fun kid found => by simp only [target, reduceCtorEq] at found)] at supported
      simp only [simulateQ_pure, StateT.run_pure, map_pure, support_pure, Set.mem_singleton_iff] at supported
      subst supported
      exact ⟨⟨native.shared.2.ctx, rfl⟩, rfl, rfl, fun kid current found => Or.inl (by rw [found]; simp)⟩
  | some kid =>
      rw [PqxdhDeploymentCompileRecords.serverLocal_some setup codec route query copies kid target] at supported
      simp only [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at supported
      obtain ⟨⟨kernel, middle⟩, kernelSupport, supported⟩ := supported
      have kernelFacts : middle = native ∧ (kernel.isSome → copies.peers kid ≠ none ∨
          native.shared.2.server.server.peers kid ≠ none) := by
        cases copied : copies.peers kid with
        | some current =>
            simp only [PqxdhDeploymentCompile.peerKernel, copied, simulateQ_pure, StateT.run_pure, support_pure,
              Set.mem_singleton_iff, Prod.mk.injEq] at kernelSupport
            obtain ⟨rfl, rfl⟩ := kernelSupport
            exact ⟨rfl, fun _ => Or.inl (by simp)⟩
        | none =>
            simp only [PqxdhDeploymentCompile.peerKernel, copied, PqxdhDeploymentCompileRecords.reveal_run,
              support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at kernelSupport
            obtain ⟨rfl, rfl⟩ := kernelSupport
            refine ⟨rfl, fun some => Or.inr ?_⟩
            intro missing
            simp [missing] at some
      obtain ⟨middleEq, kernelOrigin⟩ := kernelFacts
      rw [middleEq, simulateQ_map, StateT.run_map, PqxdhDeploymentRecordCache.local_record, support_map] at supported
      obtain ⟨recorded, recordedSupport, rfl⟩ := supported
      obtain ⟨cache, cacheEq⟩ := PqxdhDeploymentNative.record_support setup codec _ native recorded recordedSupport
      refine ⟨⟨cache, cacheEq⟩, rfl, rfl, fun other current found => ?_⟩
      by_cases same : other = kid
      · subst same
        simp only [Function.update_self, Option.map_eq_some_iff] at found
        obtain ⟨peer, peerFound, _⟩ := found
        apply kernelOrigin
        cases kernel with
        | some _ => rfl
        | none =>
            exfalso
            rw [PqxdhDeploymentCompileRecords.serverImpl_absent _ route codec.frameRead query _ (fun other routed => by
                simp only [target, Option.some.injEq] at routed
                subst routed
                simp [PqxdhDeploymentCompile.localServer]), PqxdhDeploymentCompileRecords.record_pure, support_pure,
              Set.mem_singleton_iff] at recordedSupport
            subst recordedSupport
            simp [PqxdhDeploymentCompile.localServer] at peerFound
      · simp only [Function.update_of_ne same] at found
        exact Or.inl (by rw [found]; simp)

/-- A compiled Beacon record command changes only the BLAKE2b cache of the source14 state, keeps the log and peers, and holds a local kernel only for an owner that had a local copy or is established. -/
theorem beaconLocal_support (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (serverSeed : IdentitySeed) (index : Nat) (query : RawCtxMixedOwner.SourceSpec.Domain) (copies : Local)
    (native : PqxdhRegistrationSchedule.State KemSK)
    (result : (RawCtxMixedOwner.SourceSpec.Range query × Local) × PqxdhRegistrationSchedule.State KemSK)
    (supported : result ∈ support ((simulateQ (PqxdhRegistrationJointRevealSchedule.native setup codec checks serverSeed)
      ((PqxdhDeploymentCompile.beaconLocal setup codec index query).run copies)).run native)) :
    (∃ cache, result.2 = PqxdhDeploymentRecordCache.setCtx native cache) ∧ result.1.2.log = copies.log ∧
      result.1.2.peers = copies.peers ∧
      ∀ position current, result.1.2.owners position = some current →
        copies.owners position ≠ none ∨ ∃ owner control associatedData kernel,
          native.owners[position]? = some owner ∧ owner.beacon.phase = .established control associatedData kernel := by
  by_cases inside : index < copies.log.owners.length
  · rw [PqxdhDeploymentCompileRecords.beaconLocal_present setup codec index query copies inside] at supported
    simp only [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at supported
    obtain ⟨⟨kernel, middle⟩, kernelSupport, supported⟩ := supported
    have kernelFacts : middle = native ∧ (kernel.isSome → copies.owners index ≠ none ∨
        ∃ owner control associatedData current, native.owners[index]? = some owner ∧
          owner.beacon.phase = .established control associatedData current) := by
      cases copied : copies.owners index with
      | some current =>
          simp only [PqxdhDeploymentCompile.ownerKernel, copied, simulateQ_pure, StateT.run_pure, support_pure,
            Set.mem_singleton_iff, Prod.mk.injEq] at kernelSupport
          obtain ⟨kernelEq, middleEq⟩ := kernelSupport
          exact ⟨middleEq, fun _ => Or.inl (by simp)⟩
      | none =>
          simp only [PqxdhDeploymentCompile.ownerKernel, copied, PqxdhDeploymentCompileRecords.kernel_run,
            support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at kernelSupport
          obtain ⟨kernelEq, middleEq⟩ := kernelSupport
          subst kernelEq
          refine ⟨middleEq, fun some => Or.inr ?_⟩
          cases found : native.owners[index]? with
          | none => simp [found] at some
          | some owner =>
              cases phase : owner.beacon.phase <;>
                simp [found, phase, PqxdhDeploymentCompile.phaseKernel] at some
              exact ⟨owner, _, _, _, rfl, phase⟩
    obtain ⟨middleEq, kernelOrigin⟩ := kernelFacts
    rw [middleEq, simulateQ_map, StateT.run_map, PqxdhDeploymentRecordCache.local_record, support_map] at supported
    obtain ⟨recorded, recordedSupport, rfl⟩ := supported
    obtain ⟨cache, cacheEq⟩ := PqxdhDeploymentNative.record_support setup codec _ native recorded recordedSupport
    refine ⟨⟨cache, cacheEq⟩, rfl, rfl, fun other current found => ?_⟩
    by_cases same : other = index
    · subst same
      simp only [Function.update_self] at found
      apply kernelOrigin
      cases kernel with
      | some _ => rfl
      | none =>
          exfalso
          have inactive : ¬ RawCtxBeaconLifecycle.Established
              (PqxdhDeploymentCompile.localOwner codec copies.log other none (copies.ownerRaw other)).beacon.phase := by
            simp [PqxdhDeploymentCompile.localOwner, RawCtxBeaconLifecycle.Established]
          rw [RawCtxBeaconLifecycle.inactive codec.frameRead query _ inactive, PqxdhDeploymentCompileRecords.record_pure,
            support_pure, Set.mem_singleton_iff] at recordedSupport
          subst recordedSupport
          rcases query with plaintext | bytes <;>
            simp [RawCtxBeaconLifecycle.rejected, PqxdhDeploymentCompile.localOwner,
              PqxdhDeploymentCompile.phaseKernel] at found
    · simp only [Function.update_of_ne same] at found
      exact Or.inl (by rw [found]; simp)
  · rw [PqxdhDeploymentCompileRecords.beaconLocal_absent setup codec index query copies inside] at supported
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
    subst supported
    exact ⟨⟨native.shared.2.ctx, rfl⟩, rfl, rfl, fun position current found => Or.inl (by rw [found]; simp)⟩

/-- A compiled Server record command keeps the invariant. -/
theorem good_server_record (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (serverSeed : IdentitySeed)
    (query : RawCtxServerMixed.SourceSpec.Domain) (copies : Local) (native : PqxdhRegistrationSchedule.State KemSK)
    (good : Good setup codec copies native)
    (result : (RawCtxServerMixed.SourceSpec.Range query × Local) × PqxdhRegistrationSchedule.State KemSK)
    (supported : result ∈ support ((simulateQ (PqxdhRegistrationJointRevealSchedule.native setup codec checks serverSeed)
      ((PqxdhDeploymentCompile.serverLocal setup codec route query).run copies)).run native)) :
    Good setup codec result.1.2 result.2 := by
  obtain ⟨⟨cache, nativeEq⟩, logEq, ownersEq, origin⟩ :=
    serverLocal_support setup codec checks route serverSeed query copies native result supported
  rw [nativeEq]
  refine ⟨good.keyId, ?_, by rw [logEq]; exact good.serverVisible, by rw [logEq]; exact good.count, ?_,
    by rw [logEq]; exact good.owners, by rw [logEq]; exact good.pending, by rw [logEq]; exact good.accepts⟩
  · intro kid current found
    rcases origin kid current found with copied | installed
    · cases copiedValue : copies.peers kid with
      | none => exact absurd copiedValue copied
      | some value => exact good.installed kid value copiedValue
    · exact installed
  · intro index current found
    rw [ownersEq] at found
    exact good.copied index current found

/-- A compiled Beacon record command keeps the invariant. -/
theorem good_beacon_record (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (serverSeed : IdentitySeed) (index : Nat) (query : RawCtxMixedOwner.SourceSpec.Domain) (copies : Local)
    (native : PqxdhRegistrationSchedule.State KemSK) (good : Good setup codec copies native)
    (result : (RawCtxMixedOwner.SourceSpec.Range query × Local) × PqxdhRegistrationSchedule.State KemSK)
    (supported : result ∈ support ((simulateQ (PqxdhRegistrationJointRevealSchedule.native setup codec checks serverSeed)
      ((PqxdhDeploymentCompile.beaconLocal setup codec index query).run copies)).run native)) :
    Good setup codec result.1.2 result.2 := by
  obtain ⟨⟨cache, nativeEq⟩, logEq, peersEq, origin⟩ :=
    beaconLocal_support setup codec checks serverSeed index query copies native result supported
  rw [nativeEq]
  refine ⟨good.keyId, ?_, by rw [logEq]; exact good.serverVisible, by rw [logEq]; exact good.count, ?_,
    by rw [logEq]; exact good.owners, by rw [logEq]; exact good.pending, by rw [logEq]; exact good.accepts⟩
  · intro kid current found
    rw [peersEq] at found
    exact good.installed kid current found
  · intro position current found
    rcases origin position current found with copied | established
    · cases copiedValue : copies.owners position with
      | none => exact absurd copiedValue copied
      | some value => exact good.copied position value copiedValue
    · exact established

/-- Every compiled step keeps the invariant, under the approved Phase 1 and Phase 2 read-back contracts. -/
theorem good_step (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (serverSeed : IdentitySeed)
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec)
    (query : PqxdhDeploymentInterface.Spec.Domain) (copies : Local) (native : PqxdhRegistrationSchedule.State KemSK)
    (good : Good setup codec copies native)
    (result : PqxdhDeploymentInterface.Spec.Range query × (Local × PqxdhRegistrationSchedule.State KemSK))
    (supported : result ∈ support ((compiledImpl setup codec checks route serverSeed query).run (copies, native))) :
    Good setup codec result.2.1 result.2.2 := by
  rw [PqxdhDeploymentCompileStep.compiledImpl_run, support_map] at supported
  obtain ⟨reached, member, rfl⟩ := supported
  rcases query with coin | command
  · simp only [compileImpl, StateT.run_lift, bind_pure_comp, simulateQ_map, simulateQ_spec_query, StateT.run_map,
      support_map, Set.mem_image] at member
    obtain ⟨value, valueMember, rfl⟩ := member
    change value ∈ support ((StateT.lift (unifSpec.query coin : ProbComp _) :
      StateT (PqxdhRegistrationSchedule.State KemSK) ProbComp _).run native) at valueMember
    simp only [StateT.run_lift, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at valueMember
    obtain ⟨_, _, rfl⟩ := valueMember
    exact good
  · cases command with
    | create pin keyId =>
        simp only [compileImpl] at member
        cases parsed : PqxdhDeploymentInterface.parsePin pin with
        | none =>
            simp only [parsed] at member
            change reached ∈ support ((simulateQ (PqxdhRegistrationJointRevealSchedule.native setup codec checks serverSeed)
              (pure (none, copies) : OracleComp (PqxdhDeploymentRecordCache.SourceSpec KemSK) _)).run native) at member
            simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at member
            subst member
            exact good
        | some word =>
            simp only [parsed] at member
            change reached ∈ support ((simulateQ (PqxdhRegistrationJointRevealSchedule.native setup codec checks serverSeed)
              (PqxdhDeploymentCompile.forward (.create word keyId) >>= fun index => pure (some index, _))).run native)
              at member
            simp only [PqxdhDeploymentCompile.forward, bind_pure_comp, simulateQ_map, simulateQ_spec_query,
              StateT.run_map, support_map, Set.mem_image] at member
            obtain ⟨created, createdMember, rfl⟩ := member
            exact good_create setup codec checks serverSeed word keyId copies native good created createdMember
    | bundle index =>
        simp only [compileImpl] at member
        rw [PqxdhDeploymentCompileStep.forwardLogged_run, support_map] at member
        obtain ⟨answer, answerMember, rfl⟩ := member
        exact good_bundle setup codec checks serverSeed phase1 index copies native good answer answerMember
    | accept raw =>
        simp only [compileImpl] at member
        rw [PqxdhDeploymentCompileStep.forwardLogged_run, support_map] at member
        obtain ⟨answer, answerMember, rfl⟩ := member
        exact good_accept setup codec checks serverSeed raw copies native good answer answerMember
    | build session payload =>
        simp only [compileImpl] at member
        rw [PqxdhDeploymentCompileStep.forwardLogged_run, support_map] at member
        obtain ⟨answer, answerMember, rfl⟩ := member
        exact good_build setup codec checks serverSeed phase2 session payload copies native good answer answerMember
    | finish index raw =>
        simp only [compileImpl] at member
        rw [PqxdhDeploymentCompileStep.forwardLogged_run, support_map] at member
        obtain ⟨answer, answerMember, rfl⟩ := member
        exact good_finish setup codec checks serverSeed index raw copies native good answer answerMember
    | hmac key message =>
        simp only [compileImpl] at member
        rw [PqxdhDeploymentCompileStep.forward_run, support_map] at member
        obtain ⟨answer, answerMember, rfl⟩ := member
        exact good_public setup codec checks serverSeed (.hmac key message) trivial copies native good answer answerMember
    | hash bytes =>
        simp only [compileImpl] at member
        rw [PqxdhDeploymentCompileStep.forward_run, support_map] at member
        obtain ⟨answer, answerMember, rfl⟩ := member
        exact good_public setup codec checks serverSeed (.hash bytes) trivial copies native good answer answerMember
    | serverSend kid plaintext =>
        exact good_server_record setup codec checks route serverSeed (.inl (plaintext, kid)) copies native good reached
          member
    | serverRaw raw =>
        exact good_server_record setup codec checks route serverSeed (.inr raw) copies native good reached member
    | beaconSend index plaintext =>
        exact good_beacon_record setup codec checks serverSeed index (.inl plaintext) copies native good reached member
    | beaconRaw index raw =>
        exact good_beacon_record setup codec checks serverSeed index (.inr raw) copies native good reached member

/-- The invariant holds for the empty local state at a source14 state with the public Server key ID, no installed peer, no owner and no pending token. -/
theorem good_initial (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (native : PqxdhRegistrationSchedule.State KemSK) (keyId : native.shared.2.server.identityKeyId = setup.serverKeyId)
    (peers : ∀ kid, native.shared.2.server.server.peers kid = none) (owners : native.owners = [])
    (pending : ∀ session, native.shared.2.pending session = none) :
    Good setup codec Local.empty native := by
  refine ⟨keyId, fun _ _ found => (by cases found), fun kid peer found => ?_, (by rw [owners]; rfl),
    fun _ _ found => (by cases found), fun index owner found => ?_, fun session token found => ?_,
    fun _ _ found => (by cases found)⟩
  · rw [peers] at found
    cases found
  · rw [owners] at found
    cases found
  · rw [pending] at found
    cases found

/-- Theorem CE-COMPILE at the native level: under the approved Phase 1 and Phase 2 read-back contracts, the compiled program run under the source14 native handler from a fresh source14 state, with the compiled program's final local copies merged into the final source14 state, has exactly the distribution of the native deployment experiment from the same state with zero raw-attempt counters, jointly with the adversary's output. -/
theorem compile_native {X : Type} (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (serverSeed : IdentitySeed)
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec)
    (adversary : OracleComp PqxdhDeploymentInterface.Spec X) (native : PqxdhRegistrationSchedule.State KemSK)
    (keyId : native.shared.2.server.identityKeyId = setup.serverKeyId)
    (peers : ∀ kid, native.shared.2.server.server.peers kid = none) (owners : native.owners = [])
    (pending : ∀ session, native.shared.2.pending session = none) :
    (fun result => (result.1.1, merge result.1.2 result.2)) <$>
        (simulateQ (PqxdhRegistrationJointRevealSchedule.native setup codec checks serverSeed)
          (PqxdhDeploymentCompile.compile setup codec route adversary)).run native =
      (simulateQ (PqxdhDeploymentNative.handler setup codec checks route serverSeed) adversary).run
        ⟨native, 0, fun _ => 0⟩ :=
  PqxdhDeploymentCompileStep.compile_run setup codec checks route serverSeed (Good setup codec)
    (good_inv setup codec) (good_step setup codec checks route serverSeed phase1 phase2) adversary native
    (good_initial setup codec native keyId peers owners pending)

end BeaconcryptCore.Computational.PqxdhDeploymentCompileInvariant

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentCompileInvariant.good_inv' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentCompileInvariant.good_inv

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentCompileInvariant.shared_footprint' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentCompileInvariant.shared_footprint

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentCompileInvariant.good_frame' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentCompileInvariant.good_frame

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentCompileInvariant.good_public' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentCompileInvariant.good_public

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentCompileInvariant.ownerShape_accepts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentCompileInvariant.ownerShape_accepts

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentCompileInvariant.peerView_accept' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentCompileInvariant.peerView_accept

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentCompileInvariant.good_accept' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentCompileInvariant.good_accept

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentCompileInvariant.ownerShape_builds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentCompileInvariant.ownerShape_builds

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentCompileInvariant.good_build' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentCompileInvariant.good_build

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentCompileInvariant.ownerView_extend' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentCompileInvariant.ownerView_extend

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentCompileInvariant.ownerShape_extend' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentCompileInvariant.ownerShape_extend

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentCompileInvariant.good_create' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentCompileInvariant.good_create

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentCompileInvariant.ownerShape_bundle' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentCompileInvariant.ownerShape_bundle

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentCompileInvariant.identityOf_bundle' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentCompileInvariant.identityOf_bundle

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentCompileInvariant.good_bundle' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentCompileInvariant.good_bundle

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentCompileInvariant.ownerShape_finish' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentCompileInvariant.ownerShape_finish

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentCompileInvariant.good_finish' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentCompileInvariant.good_finish

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentCompileInvariant.serverLocal_support' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentCompileInvariant.serverLocal_support

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentCompileInvariant.beaconLocal_support' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentCompileInvariant.beaconLocal_support

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentCompileInvariant.good_server_record' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentCompileInvariant.good_server_record

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentCompileInvariant.good_beacon_record' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentCompileInvariant.good_beacon_record

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentCompileInvariant.good_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentCompileInvariant.good_step

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentCompileInvariant.good_initial' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentCompileInvariant.good_initial

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentCompileInvariant.compile_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentCompileInvariant.compile_native
