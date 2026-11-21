-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhDeploymentHeadlineGap
import BeaconcryptCore.Computational.PqxdhDeploymentHeadlineCtTrace
import BeaconcryptCore.Computational.PqxdhServerAuthRootSessionFields

/-!
# Session-field invariants of the common deployment experiment (O21, part 1)

Two run invariants of `PqxdhDeploymentSecrecy.game` (any identity index) that let CE-A1's public transcript match be read as an agreement on ten of the eleven fields of `PqxdhServerAuthRootSession.Session`, read from the experiment's final state: each party's state and the transcript (`PqxdhDeploymentSessionFields`).

- `ServerInv`: the Server key ID stays the compiled-in one; the ghost seal log (`PqxdhServerAuthExperiment.Ghost.seals`, appended only by `buildOracle`, under the built handle) and the pending tokens name only handles already issued; a pending handle has no logged seal context and its token carries the Beacon identity that `PqxdhDeploymentCompile.identityOf` reads from the accept bytes that returned the handle and the retained Init fields that `PqxdhDeploymentCompile.publicInit` reads from them; and each successful build entry of a handle has, for some candidate whose Phase 2 writer output is the build response, the build's first-send context as the handle's first logged seal context (`sealOf`), whose associated data is `PqxdhTranscriptAd.adOf` of the digest that the BLAKE2b cache holds for the registration transcript of those Init fields and the candidate's Phase 2 fields (`build_seals`). This is the associated data the Server sealed with: Rust assembles it from the session transcript hash (`assemble_associated_data`, `session.rs`).
- `BeaconInv`: every InitSent control carries the owner's own identity key (the Phase 1 publication, `PqxdhDeploymentEligibility.bundle_candidate`); every successful bundle entry wrote the owner's retained Phase 1 bundle (`PqxdhRegistrationSchedule.State.inits`), only existing owners retain one, and no Fresh or Fresh-with-coins owner does; every successful finish entry left its owner established with `PqxdhTranscriptAd.adOf` of the digest that the BLAKE2b cache holds for the registration transcript of its retained bundle and the finish input's decoded response fields (the success branch of `PqxdhDeploymentCompileFootprint.ownerFinish_owner`; Rust's `Established.associated_data`, `beacon.rs`); every Fresh, Fresh-with-coins and InitSent control expects the owner's pinned Server identity (`expectedPin`); and every owner that accepted in the registration view of the transcript (`PqxdhDeploymentServerAuthEvent.accepted`) is established.
- Both hold initially (`inv_initial`) and after every query (`inv_step`). The BLAKE2b cache only grows and the retained bundles change only at a bundle (`ServerKept`, `Kept`, `serverStep_grows`, `beaconStep_grows`). Coins, the public HMAC and BLAKE2b oracles, the record commands and the secrecy commands keep every field the invariants read (`native_quiet`, `coinSend_kept`, through `serverInv_frame` and `beaconInv_frame`; the raw accept and the HMAC only append Extract-table touches, `accept_seals`, `hmac_seals`); create, bundle, finish, raw accept and build have their own steps (`create_step`, `bundle_step`, `finish_step`, `accept_step`, `build_step` with `build_seals`). Hence on every outcome (`inv_game`) the final Server identity is the protected binding's pin and the final state satisfies both invariants for that pin and `setup.serverKeyId`.

The invariants state the hashed transcripts on the retained Init fields, the written Phase 2 fields and the decoded finish input; `PqxdhDeploymentSessionFields.pinned_agree_transcript` reads the public transcripts back to them with the approved read-back contracts. These are support facts: no codec law, contract or security assumption is used and nothing is charged. No root is read. The touch log keeps the Server's session roots, but no field of the state is labelled as a Beacon's root: the Extract entry from which a Beacon's root is expanded sits unlabelled in the shared HMAC cache (`PqxdhServerAuthNative.sourceRoot`), and the Beacon's evolving ratchet kernel is derived from that root.
-/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false

namespace BeaconcryptCore.Computational.PqxdhDeploymentSessionFieldsInvariant
open PqxdhServerAuthExperiment PqxdhJointIdentity
open PqxdhDeploymentInterface (Spec FullSpec ModeSpec Mode Entry FreshBounds parsePin asModeO)
open PqxdhDeploymentServerAuthEvent (Reg regsOf regOfEntry accepted acceptCheck summarizeReg)
open PqxdhBeaconPhase2Preparation (Word32)
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response A X : Type}

/-! ### Readouts -/

/-- The first logged seal context of a session handle in the Server's ghost seal log. -/
def sealOf (seals : List (Nat × RawCtxSourceSend.SealContext)) (session : Nat) : Option RawCtxSourceSend.SealContext :=
  (seals.find? fun entry => decide (entry.1 = session)).map Prod.snd

/-- The stored associated data of an established phase. -/
def establishedAd {D K Kernel : Type} : RawCtxBeaconLifecycle.Phase D K Kernel → Option PqxdhTranscriptAd.AssociatedData
  | .established _ associatedData _ => some associatedData
  | _ => none

/-- The Beacon identity of an InitSent control. -/
def controlIdentity {D K Kernel : Type} : RawCtxBeaconLifecycle.Phase D K Kernel → Option Word32
  | .initSent control _ _ _ => some control.beacon_identity_public_key
  | _ => none

/-- The expected Server identity of a Fresh, Fresh-with-coins or InitSent control. -/
def expectedPin {D K Kernel : Type} : RawCtxBeaconLifecycle.Phase D K Kernel → Option Word32
  | .fresh control _ _ => some control.expected_server_binding.identity_public_key
  | .freshWithCoins control _ _ _ => some control.expected_server_binding.identity_public_key
  | .initSent control _ _ _ => some control.expected_server_binding.identity_public_key
  | _ => none

/-- The owner fields the Beacon invariant reads: identity seed, pin, InitSent Beacon identity, expected Server identity and established associated data. -/
def ownerKey (owner : PqxdhRegistrationSchedule.Owner KemSK) :
    IdentitySeed × Word32 × Option Word32 × Option Word32 × Option PqxdhTranscriptAd.AssociatedData :=
  (owner.beacon.identity, owner.beacon.serverIdentity, controlIdentity owner.beacon.phase,
    expectedPin owner.beacon.phase, establishedAd owner.beacon.phase)

/-! ### The invariants -/

/-- Server-side invariant: constant Server key ID; ghost seals and pending tokens only at handles already issued; a pending handle has no seal yet and carries the identity and the retained Init fields of the accept that issued it; and a successfully built handle's first logged seal context has the associated data `PqxdhTranscriptAd.adOf` of the digest that the BLAKE2b cache holds for the registration transcript of the retained Init fields of the accept that issued the handle and of the Phase 2 fields of a candidate whose Phase 2 writer output is the build response. -/
structure ServerInv (codec : Codec Reader Response) (server : RawCtxServerRouting.Identity) (serverKid : Std.U64)
    (state : PqxdhDeploymentSecrecy.State KemSK) : Prop where
  kid : state.2.native.shared.2.server.identityKeyId = serverKid
  sealsBelow : ∀ session context, (session, context) ∈ state.2.native.shared.2.ghost.seals →
    session < state.2.native.shared.2.sessions
  pendingFresh : ∀ session token, state.2.native.shared.2.pending session = some token →
    session < state.2.native.shared.2.sessions ∧ sealOf state.2.native.shared.2.ghost.seals session = none ∧
    ∃ raw, (⟨.inl (.inr (.accept raw)), some session⟩ : Entry) ∈ state.1.transcript ∧
      PqxdhDeploymentCompile.identityOf codec raw = some token.pending.beacon_identity_public_key ∧
      PqxdhDeploymentCompile.publicInit codec raw = some (PqxdhTranscriptAd.initOf token.init)
  sealedTranscript : ∀ session payload response,
    (⟨.inl (.inr (.build session payload)), some response⟩ : Entry) ∈ state.1.transcript →
    ∃ (raw : Pqxdh.Bytes) (init : PqxdhEd25519EufCma.Phase1Candidate)
      (candidate : beaconcrypt_core.pqxdh.ServerRegistrationCandidate) (frameBytes : Pqxdh.Bytes)
      (digest : CtxRomAuth.CtxDigest) (context : RawCtxSourceSend.SealContext),
      (⟨.inl (.inr (.accept raw)), some session⟩ : Entry) ∈ state.1.transcript ∧
      PqxdhDeploymentCompile.publicInit codec raw = some (PqxdhTranscriptAd.initOf init) ∧
      codec.write2 ⟨candidate.key_id, candidate.ephemeral_public_key, candidate.server_identity_public_key,
        candidate.kem_ciphertext, frameBytes⟩ = some response.serialized ∧
      state.2.native.shared.2.ctx ((), PqxdhTranscriptAd.transcript (PqxdhTranscriptAd.initOf init)
        (PqxdhTranscriptAd.serverResponse candidate)) = some digest ∧
      sealOf state.2.native.shared.2.ghost.seals session = some context ∧
      context.associatedData = PqxdhRefinement.absBytes (PqxdhTranscriptAd.adOf digest)

/-- Beacon-side invariant: every InitSent control carries the owner's own identity key; every successful bundle in the transcript wrote the owner's retained Phase 1 bundle; only existing owners retain a bundle and no Fresh or Fresh-with-coins owner retains one; every successful finish in the transcript left its owner established with the associated data `PqxdhTranscriptAd.adOf` of the digest that the BLAKE2b cache holds for the registration transcript of the owner's retained bundle and the finish input's decoded response fields; every Fresh, Fresh-with-coins or InitSent control expects the owner's pinned Server identity; and every owner that accepted in the registration view of the transcript is established. -/
structure BeaconInv (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (state : PqxdhDeploymentSecrecy.State KemSK) : Prop where
  controls : ∀ (k : Nat) (owner : PqxdhRegistrationSchedule.Owner KemSK) control prekey oneTime kem,
    state.2.native.owners[k]? = some owner → owner.beacon.phase = .initSent control prekey oneTime kem →
      control.beacon_identity_public_key =
        PqxdhRootTableInitialization.rootArray (setup.joint.publicKeys owner.beacon.identity).ed25519
  bundled : ∀ k bytes, (⟨.inl (.inr (.bundle k)), some bytes⟩ : Entry) ∈ state.1.transcript →
    ∃ init, state.2.native.inits k = some init ∧ codec.write1 init = some bytes
  initsBelow : ∀ k init, state.2.native.inits k = some init → k < state.2.native.owners.length
  freshUnretained : ∀ (k : Nat) (owner : PqxdhRegistrationSchedule.Owner KemSK),
    state.2.native.owners[k]? = some owner → expectedPin owner.beacon.phase ≠ none →
      controlIdentity owner.beacon.phase = none → state.2.native.inits k = none
  installedTranscript : ∀ k raw reply, (⟨.inl (.inr (.finish k raw)), some reply⟩ : Entry) ∈ state.1.transcript →
    ∃ (owner : PqxdhRegistrationSchedule.Owner KemSK) (init : PqxdhEd25519EufCma.Phase1Candidate)
      (response : Pqxdh.SessionTranscript.ResponseFields) (digest : CtxRomAuth.CtxDigest),
      state.2.native.owners[k]? = some owner ∧ state.2.native.inits k = some init ∧
      responseOf codec raw = some response ∧
      state.2.native.shared.2.ctx ((), PqxdhTranscriptAd.transcript (PqxdhTranscriptAd.initOf init) response) =
        some digest ∧
      establishedAd owner.beacon.phase = some (PqxdhTranscriptAd.adOf digest)
  pinned : ∀ (k : Nat) (owner : PqxdhRegistrationSchedule.Owner KemSK) pin,
    state.2.native.owners[k]? = some owner → expectedPin owner.beacon.phase = some pin →
      pin = owner.beacon.serverIdentity
  accepts : ∀ c before raw, accepted c (regsOf state.1.transcript) = some (before, raw) →
    ∃ owner : PqxdhRegistrationSchedule.Owner KemSK, ∃ control associatedData kernel,
      state.2.native.owners[c]? = some owner ∧ owner.beacon.phase = .established control associatedData kernel

/-! ### Seal log lookups -/

/-- An earlier first seal context stays first when the log grows. -/
theorem sealOf_append_of_some (seals more : List (Nat × RawCtxSourceSend.SealContext)) (session : Nat)
    (context : RawCtxSourceSend.SealContext) (found : sealOf seals session = some context) :
    sealOf (seals ++ more) session = some context := by
  unfold sealOf at found ⊢
  rw [List.find?_append]
  cases first : seals.find? (fun entry => decide (entry.1 = session)) with
  | none => rw [first] at found; cases found
  | some entry => rw [first] at found; simpa using found

/-- Appended entries of other handles do not change a handle's first seal context. -/
theorem sealOf_append_ne (seals more : List (Nat × RawCtxSourceSend.SealContext)) (session : Nat)
    (others : ∀ entry ∈ more, entry.1 ≠ session) : sealOf (seals ++ more) session = sealOf seals session := by
  unfold sealOf
  rw [List.find?_append]
  cases first : seals.find? (fun entry => decide (entry.1 = session)) with
  | some entry => rfl
  | none =>
      have missing : more.find? (fun entry => decide (entry.1 = session)) = none := by
        rw [List.find?_eq_none]
        intro entry member
        simpa using others entry member
      simp [missing]

/-- A handle with no seal context gets the first context appended under it. -/
theorem sealOf_append_none (seals : List (Nat × RawCtxSourceSend.SealContext)) (session : Nat)
    (context : RawCtxSourceSend.SealContext) (rest : List RawCtxSourceSend.SealContext)
    (missing : sealOf seals session = none) :
    sealOf (seals ++ (context :: rest).map fun value => (session, value)) session = some context := by
  unfold sealOf at missing ⊢
  rw [List.find?_append]
  cases first : seals.find? (fun entry => decide (entry.1 = session)) with
  | some entry => rw [first] at missing; cases missing
  | none => simp

/-- A handle at or above every logged handle has no seal context. -/
theorem sealOf_none_of_below (seals : List (Nat × RawCtxSourceSend.SealContext)) (session : Nat)
    (below : ∀ entry ∈ seals, entry.1 < session) : sealOf seals session = none := by
  unfold sealOf
  rw [Option.map_eq_none_iff, List.find?_eq_none]
  intro entry member
  have := below entry member
  simp only [decide_eq_true_eq]
  omega

/-! ### Phase readouts -/

/-- A phase with stored associated data is established with it. -/
theorem establishedAd_some {D K : Type}
    (phase : RawCtxBeaconLifecycle.Phase D K beaconcrypt_core.ratchet.concrete.ConcreteRatchetKernel)
    (associatedData : PqxdhTranscriptAd.AssociatedData) (found : establishedAd phase = some associatedData) :
    ∃ control kernel, phase = .established control associatedData kernel := by
  cases phase with
  | established control stored kernel =>
      simp only [establishedAd, Option.some.injEq] at found
      exact ⟨control, kernel, by rw [found]⟩
  | _ => cases found

/-! ### Kept native fields -/

/-- The Server key ID, ghost seal log, session counter and pending tokens are kept, and the BLAKE2b cache only grows. -/
structure ServerKept (before after : PqxdhRegistrationSchedule.State KemSK) : Prop where
  kid : after.shared.2.server.identityKeyId = before.shared.2.server.identityKeyId
  seals : after.shared.2.ghost.seals = before.shared.2.ghost.seals
  sessions : after.shared.2.sessions = before.shared.2.sessions
  pending : after.shared.2.pending = before.shared.2.pending
  ctx : before.shared.2.ctx ≤ after.shared.2.ctx

/-- Every owner slot keeps the fields the Beacon invariant reads. -/
def OwnersKept (before after : PqxdhRegistrationSchedule.State KemSK) : Prop :=
  ∀ k : Nat, (after.owners[k]?).map (ownerKey (KemSK := KemSK)) = (before.owners[k]?).map ownerKey

/-- Kept Server fields, owner fields and retained Phase 1 bundles. -/
def Kept (before after : PqxdhRegistrationSchedule.State KemSK) : Prop :=
  ServerKept before after ∧ OwnersKept before after ∧ after.inits = before.inits

/-- A state keeps its own fields. -/
theorem kept_refl (state : PqxdhRegistrationSchedule.State KemSK) : Kept state state :=
  ⟨⟨rfl, rfl, rfl, rfl, le_rfl⟩, fun _ => rfl, rfl⟩

/-- Kept fields compose. -/
theorem kept_trans (first second third : PqxdhRegistrationSchedule.State KemSK) (left : Kept first second)
    (right : Kept second third) : Kept first third :=
  ⟨⟨right.1.kid.trans left.1.kid, right.1.seals.trans left.1.seals, right.1.sessions.trans left.1.sessions,
    right.1.pending.trans left.1.pending, le_trans left.1.ctx right.1.ctx⟩,
    fun k => (right.2.1 k).trans (left.2.1 k), right.2.2.trans left.2.2⟩

/-! ### Frames -/

/-- An entry that is not a successful finish keeps every owner's acceptance. -/
theorem accepted_quiet (transcript : List Entry) (entry : Entry)
    (quiet : ∀ owner raw payload, regOfEntry entry ≠ some (.finish owner raw (some payload))) (c : Nat) :
    accepted c (regsOf (transcript ++ [entry])) = accepted c (regsOf transcript) := by
  rw [PqxdhDeploymentHeadlineGap.regsOf_snoc]
  cases found : regOfEntry entry with
  | none => simp
  | some reg =>
      rw [Option.toList_some, PqxdhDeploymentServerAuthEvent.accepted_snoc]
      cases reg with
      | finish owner raw reply =>
          cases reply with
          | none => simp [acceptCheck]
          | some payload => exact absurd found (quiet owner raw payload)
      | _ => simp [acceptCheck]

/-- A finish entry adds at most the acceptance of its own owner, and only on a success. -/
theorem accepted_finish (transcript : List Entry) (index : Nat) (input : Pqxdh.Bytes) (reply : Option Pqxdh.Bytes)
    (c : Nat) (result : List Reg × Pqxdh.Bytes)
    (found : accepted c (regsOf (transcript ++ [⟨.inl (.inr (.finish index input)), reply⟩])) = some result) :
    accepted c (regsOf transcript) = some result ∨ (c = index ∧ reply.isSome) := by
  rw [PqxdhDeploymentHeadlineGap.regsOf_snoc] at found
  simp only [regOfEntry, Option.toList_some] at found
  rw [PqxdhDeploymentServerAuthEvent.accepted_snoc] at found
  cases earlier : accepted c (regsOf transcript) with
  | some value =>
      rw [earlier] at found
      exact Or.inl (by simpa using found)
  | none =>
      rw [earlier, Option.none_or] at found
      right
      cases reply with
      | none => simp [acceptCheck] at found
      | some payload =>
          simp only [acceptCheck] at found
          split at found
          · rename_i ready
            exact ⟨ready.1.symm, rfl⟩
          · cases found

/-- The Server invariant survives a step that keeps the Server fields and appends an entry other than a build. -/
theorem serverInv_frame (codec : Codec Reader Response) (server : RawCtxServerRouting.Identity) (serverKid : Std.U64)
    (before after : PqxdhDeploymentSecrecy.State KemSK) (inv : ServerInv codec server serverKid before)
    (kept : ServerKept before.2.native after.2.native) (entry : Entry)
    (transcript : after.1.transcript = before.1.transcript ++ [entry])
    (quiet : PqxdhDeploymentHeadlineCtTrace.NotBuild entry.query) : ServerInv codec server serverKid after := by
  have grow : ∀ e, e ∈ before.1.transcript → e ∈ after.1.transcript := fun e member => by
    rw [transcript]
    exact List.mem_append_left _ member
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [kept.kid]
    exact inv.kid
  · intro session context member
    rw [kept.seals] at member
    rw [kept.sessions]
    exact inv.sealsBelow session context member
  · intro session token found
    rw [kept.pending] at found
    obtain ⟨below, fresh, raw, accept, identity, init⟩ := inv.pendingFresh session token found
    exact ⟨by rw [kept.sessions]; exact below, by rw [kept.seals]; exact fresh, raw, grow _ accept, identity, init⟩
  · intro session payload response member
    rw [transcript] at member
    rcases List.mem_append.mp member with old | new
    · obtain ⟨raw, init, candidate, frameBytes, digest, context, accept, initRead, written, cached, sealEq, ad⟩ :=
        inv.sealedTranscript session payload response old
      exact ⟨raw, init, candidate, frameBytes, digest, context, grow _ accept, initRead, written, kept.ctx cached,
        by rw [kept.seals]; exact sealEq, ad⟩
    · rw [List.mem_singleton] at new
      subst new
      simp [PqxdhDeploymentHeadlineCtTrace.NotBuild] at quiet

/-- An owner slot with kept fields, read backwards. -/
theorem kept_back (before after : PqxdhRegistrationSchedule.State KemSK) (kept : OwnersKept before after) (k : Nat)
    (owner : PqxdhRegistrationSchedule.Owner KemSK) (found : after.owners[k]? = some owner) :
    ∃ old, before.owners[k]? = some old ∧ ownerKey old = ownerKey owner := by
  have same := kept k
  rw [found] at same
  cases old : before.owners[k]? with
  | none =>
      rw [old] at same
      cases same
  | some previous =>
      rw [old] at same
      simp only [Option.map_some, Option.some.injEq] at same
      exact ⟨previous, rfl, same.symm⟩

/-- An owner slot with kept fields, read forwards. -/
theorem kept_forth (before after : PqxdhRegistrationSchedule.State KemSK) (kept : OwnersKept before after) (k : Nat)
    (owner : PqxdhRegistrationSchedule.Owner KemSK) (found : before.owners[k]? = some owner) :
    ∃ next, after.owners[k]? = some next ∧ ownerKey next = ownerKey owner := by
  have same := kept k
  rw [found] at same
  cases next : after.owners[k]? with
  | none =>
      rw [next] at same
      cases same
  | some current =>
      rw [next] at same
      simp only [Option.map_some, Option.some.injEq] at same
      exact ⟨current, rfl, same⟩

/-- The Beacon invariant survives a step that keeps every owner's fields and the retained bundles, only extends the BLAKE2b cache, and adds no successful bundle, successful finish or acceptance. -/
theorem beaconInv_frame (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (before after : PqxdhDeploymentSecrecy.State KemSK)
    (inv : BeaconInv setup codec before) (kept : OwnersKept before.2.native after.2.native)
    (inits : after.2.native.inits = before.2.native.inits)
    (grow : before.2.native.shared.2.ctx ≤ after.2.native.shared.2.ctx)
    (bundles : ∀ k bytes, (⟨.inl (.inr (.bundle k)), some bytes⟩ : Entry) ∈ after.1.transcript →
      (⟨.inl (.inr (.bundle k)), some bytes⟩ : Entry) ∈ before.1.transcript)
    (finishes : ∀ k raw reply, (⟨.inl (.inr (.finish k raw)), some reply⟩ : Entry) ∈ after.1.transcript →
      (⟨.inl (.inr (.finish k raw)), some reply⟩ : Entry) ∈ before.1.transcript)
    (accepts : ∀ c result, accepted c (regsOf after.1.transcript) = some result →
      accepted c (regsOf before.1.transcript) = some result) : BeaconInv setup codec after := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro k owner control prekey oneTime kem found phase
    obtain ⟨old, oldFound, key⟩ := kept_back _ _ kept k owner found
    simp only [ownerKey, Prod.mk.injEq] at key
    obtain ⟨seed, _, identity, _, _⟩ := key
    have current : controlIdentity owner.beacon.phase = some control.beacon_identity_public_key := by
      rw [phase]
      rfl
    rw [← identity] at current
    cases oldPhase : old.beacon.phase with
    | initSent oldControl oldPrekey oldOneTime oldKem =>
        rw [oldPhase] at current
        simp only [controlIdentity, Option.some.injEq] at current
        rw [← current, ← seed]
        exact inv.controls k old oldControl oldPrekey oldOneTime oldKem oldFound oldPhase
    | _ =>
        rw [oldPhase] at current
        cases current
  · intro k bytes member
    rw [inits]
    exact inv.bundled k bytes (bundles k bytes member)
  · intro k init found
    rw [inits] at found
    obtain ⟨next, nextFound, _⟩ :=
      kept_forth _ _ kept k _ (List.getElem?_eq_getElem (inv.initsBelow k init found))
    exact (List.getElem?_eq_some_iff.mp nextFound).1
  · intro k owner found expected unsent
    obtain ⟨old, oldFound, key⟩ := kept_back _ _ kept k owner found
    simp only [ownerKey, Prod.mk.injEq] at key
    obtain ⟨_, _, identity, oldExpected, _⟩ := key
    rw [inits]
    exact inv.freshUnretained k old oldFound (by rw [oldExpected]; exact expected)
      (by rw [identity]; exact unsent)
  · intro k raw reply member
    obtain ⟨old, init, response, digest, oldFound, initFound, decoded, cached, stored⟩ :=
      inv.installedTranscript k raw reply (finishes k raw reply member)
    obtain ⟨next, nextFound, key⟩ := kept_forth _ _ kept k old oldFound
    simp only [ownerKey, Prod.mk.injEq] at key
    refine ⟨next, init, response, digest, nextFound, by rw [inits]; exact initFound, decoded, grow cached, ?_⟩
    rw [key.2.2.2.2]
    exact stored
  · intro k owner value found expected
    obtain ⟨old, oldFound, key⟩ := kept_back _ _ kept k owner found
    simp only [ownerKey, Prod.mk.injEq] at key
    obtain ⟨_, pin, _, oldExpected, _⟩ := key
    rw [← oldExpected] at expected
    rw [← pin]
    exact inv.pinned k old value oldFound expected
  · intro c earlier raw found
    obtain ⟨old, control, associatedData, kernel, oldFound, oldPhase⟩ := inv.accepts c earlier raw (accepts c _ found)
    obtain ⟨next, nextFound, key⟩ := kept_forth _ _ kept c old oldFound
    simp only [ownerKey, Prod.mk.injEq] at key
    obtain ⟨_, _, _, _, stored⟩ := key
    have current : establishedAd next.beacon.phase = some associatedData := by
      rw [stored, oldPhase]
      rfl
    obtain ⟨nextControl, nextKernel, nextPhase⟩ := establishedAd_some _ _ current
    exact ⟨next, nextControl, associatedData, nextKernel, nextFound, nextPhase⟩

/-! ### Native steps that keep the invariant fields -/

/-- A Beacon record command keeps the owner's invariant fields: an established owner keeps its control and associated data, and an inactive owner is unchanged. -/
theorem beaconImpl_key (decode : RawCtxReceive.FrameDecoder) (query : RawCtxMixedOwner.SourceSpec.Domain)
    (state : PqxdhRegistrationSchedule.Owner KemSK)
    (result : RawCtxMixedOwner.SourceSpec.Range query × PqxdhRegistrationSchedule.Owner KemSK)
    (supported : result ∈ support ((RawCtxBeaconLifecycle.beaconImpl decode query).run state)) :
    ownerKey result.2 = ownerKey state := by
  by_cases active : RawCtxBeaconLifecycle.Established state.beacon.phase
  · cases phase : state.beacon.phase with
    | established control associatedData kernel =>
        rw [PqxdhDeploymentCompileRecords.beaconImpl_established decode query state control associatedData kernel phase,
          support_map] at supported
        obtain ⟨_, _, rfl⟩ := supported
        simp [ownerKey, phase, establishedAd, controlIdentity, expectedPin]
    | _ => simp [phase, RawCtxBeaconLifecycle.Established] at active
  · rw [RawCtxBeaconLifecycle.inactive decode query state active, support_pure, Set.mem_singleton_iff] at supported
    subst supported
    rcases query with plaintext | raw <;> rfl

/-- A native Server record command only extends the BLAKE2b cache and keeps the retained Phase 1 bundles. -/
theorem serverStep_grows (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (query : RawCtxServerMixed.SourceSpec.Domain)
    (state : PqxdhDeploymentNative.State KemSK)
    (result : RawCtxServerMixed.SourceSpec.Range query × PqxdhDeploymentNative.State KemSK)
    (supported : result ∈ support ((PqxdhDeploymentNative.serverStep setup codec route query).run state)) :
    state.native.shared.2.ctx ≤ result.2.native.shared.2.ctx ∧ result.2.native.inits = state.native.inits := by
  unfold PqxdhDeploymentNative.serverStep at supported
  simp only [StateT.run, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at supported
  obtain ⟨inner, member, rfl⟩ := supported
  obtain ⟨cache, cacheEq, grow⟩ :=
    PqxdhDeploymentCompileInvariant.record_grows setup codec _ state.native inner member
  simp only [PqxdhDeploymentNative.produce, PqxdhDeploymentNative.withServer, cacheEq,
    PqxdhDeploymentRecordCache.setCtx]
  exact ⟨grow, trivial⟩

/-- A native Beacon record command only extends the BLAKE2b cache and keeps the retained Phase 1 bundles. -/
theorem beaconStep_grows (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (index : Nat)
    (query : RawCtxMixedOwner.SourceSpec.Domain) (state : PqxdhDeploymentNative.State KemSK)
    (result : RawCtxMixedOwner.SourceSpec.Range query × PqxdhDeploymentNative.State KemSK)
    (supported : result ∈ support ((PqxdhDeploymentNative.beaconStep setup codec index query).run state)) :
    state.native.shared.2.ctx ≤ result.2.native.shared.2.ctx ∧ result.2.native.inits = state.native.inits := by
  unfold PqxdhDeploymentNative.beaconStep at supported
  cases found : state.native.owners[index]? with
  | none =>
      simp only [found, StateT.run, support_pure, Set.mem_singleton_iff] at supported
      subst supported
      exact ⟨le_rfl, rfl⟩
  | some owner =>
      simp only [found, StateT.run, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at supported
      obtain ⟨inner, member, rfl⟩ := supported
      obtain ⟨cache, cacheEq, grow⟩ :=
        PqxdhDeploymentCompileInvariant.record_grows setup codec _ state.native inner member
      simp only [PqxdhDeploymentNative.produce, cacheEq, PqxdhDeploymentRecordCache.setCtx]
      exact ⟨grow, trivial⟩

/-- A native Beacon record command keeps the Server fields and every owner's invariant fields. -/
theorem beaconStep_kept (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (index : Nat)
    (query : RawCtxMixedOwner.SourceSpec.Domain) (state : PqxdhDeploymentNative.State KemSK)
    (result : RawCtxMixedOwner.SourceSpec.Range query × PqxdhDeploymentNative.State KemSK)
    (supported : result ∈ support ((PqxdhDeploymentNative.beaconStep setup codec index query).run state)) :
    Kept state.native result.2.native := by
  obtain ⟨_, _, server, pending, sessions, ghost, _, _⟩ :=
    PqxdhDeploymentNative.beaconStep_fields setup codec index query state result supported
  have grows := beaconStep_grows setup codec index query state result supported
  refine ⟨⟨by rw [server], by rw [ghost], sessions, pending, grows.1⟩, ?_, grows.2⟩
  unfold PqxdhDeploymentNative.beaconStep at supported
  cases found : state.native.owners[index]? with
  | none =>
      simp only [found, StateT.run, support_pure, Set.mem_singleton_iff] at supported
      subst supported
      exact fun _ => rfl
  | some owner =>
      simp only [found, StateT.run, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at supported
      obtain ⟨inner, member, rfl⟩ := supported
      obtain ⟨value, cache, cacheEq⟩ := PqxdhDeploymentEligibility.record_value setup codec _ state.native inner member
      have kept := beaconImpl_key codec.frameRead query ⟨owner.beacon, state.ownerRaw index⟩ _ value
      intro position
      simp only [PqxdhDeploymentNative.produce, cacheEq]
      by_cases same : position = index
      · subst same
        have bound : position < state.native.owners.length := (List.getElem?_eq_some_iff.mp found).1
        simp only [PqxdhDeploymentRecordCache.setCtx, List.getElem?_set_self bound, found, Option.map_some]
        exact congrArg some kept
      · simp only [PqxdhDeploymentRecordCache.setCtx, List.getElem?_set_ne (Ne.symm same)]

/-- A native Server record command keeps the Server fields and every owner. -/
theorem serverStep_kept (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (query : RawCtxServerMixed.SourceSpec.Domain)
    (state : PqxdhDeploymentNative.State KemSK)
    (result : RawCtxServerMixed.SourceSpec.Range query × PqxdhDeploymentNative.State KemSK)
    (supported : result ∈ support ((PqxdhDeploymentNative.serverStep setup codec route query).run state)) :
    Kept state.native result.2.native := by
  obtain ⟨owners, _, _, pending, sessions, ghost, _, _, kid⟩ :=
    PqxdhDeploymentNative.serverStep_fields setup codec route query state result supported
  have grows := serverStep_grows setup codec route query state result supported
  exact ⟨⟨kid, by rw [ghost], sessions, pending, grows.1⟩, fun k => by rw [owners], grows.2⟩

/-- The public HMAC keeps the ghost seal log. -/
theorem hmac_seals (key : PqxdhSecretInputKdf.HmacBlock) (message : Pqxdh.Bytes) (game : GameState KemSK)
    (result : PqxdhSecretInputKdf.HmacBlock × GameState KemSK)
    (supported : result ∈ support ((hmacOracle key message).run game)) : result.2.ghost.seals = game.ghost.seals := by
  unfold hmacOracle at supported
  split at supported
  · rw [StateT.run_bind, mem_support_bind_iff] at supported
    obtain ⟨⟨_, middle⟩, touched, forwarded⟩ := supported
    have touchedRun : (recordTouch (KemSK := KemSK) (.adversary message)).run game =
        pure ((), { game with ghost := { game.ghost with touches := game.ghost.touches ++ [.adversary message] } }) :=
          rfl
    rw [touchedRun, support_pure, Set.mem_singleton_iff] at touched
    cases touched
    dsimp only at forwarded
    have same : result.2 = _ := forward_support (KemSK := KemSK) (.inr (.publicHmac key message)) _ result forwarded
    rw [same]
  · dsimp only at supported
    have same : result.2 = _ := forward_support (KemSK := KemSK) (.inr (.publicHmac key message)) _ result supported
    rw [same]

/-- The public BLAKE2b oracle keeps the ghost seal log. -/
theorem hash_seals (bytes : Pqxdh.Bytes) (game : GameState KemSK) (result : CtxRomAuth.CtxDigest × GameState KemSK)
    (supported : result ∈ support ((hashOracle bytes).run game)) : result.2.ghost.seals = game.ghost.seals := by
  simp only [hashOracle, StateT.run, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at supported
  obtain ⟨_, _, rfl⟩ := supported
  rfl

/-- Coins, the public HMAC and BLAKE2b oracles and the record commands keep the Server fields and every owner's invariant fields. -/
theorem native_quiet (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (serverSeed : IdentitySeed) (query : Spec.Domain)
    (kind : match query with
      | .inr (.create _ _) | .inr (.bundle _) | .inr (.accept _) | .inr (.build _ _) | .inr (.finish _ _) => False
      | _ => True)
    (state : PqxdhDeploymentNative.State KemSK) (answer : Spec.Range query × PqxdhDeploymentNative.State KemSK)
    (member : answer ∈ support ((PqxdhDeploymentNative.handler setup codec checks route serverSeed query).run state)) :
    Kept state.native answer.2.native := by
  rcases query with coin | command
  · simp only [PqxdhDeploymentNative.handler, StateT.run_lift, mem_support_bind_iff, support_pure,
      Set.mem_singleton_iff] at member
    obtain ⟨_, _, rfl⟩ := member
    exact kept_refl _
  · cases command with
    | create => exact False.elim kind
    | bundle => exact False.elim kind
    | accept => exact False.elim kind
    | build => exact False.elim kind
    | finish => exact False.elim kind
    | hmac key message =>
        simp only [PqxdhDeploymentNative.handler] at member
        obtain ⟨inner, innerMember, rfl⟩ := PqxdhDeploymentEligibility.onNative_support _ state answer member
        simp only [PqxdhRegistrationSchedule.handler,
          ← PqxdhServerAuthNative.hmac_native setup serverSeed PqxdhRegistrationSchedule.observationScalar]
          at innerMember
        obtain ⟨owners, reached⟩ :=
          PqxdhDeploymentCompileInvariant.shared_footprint setup serverSeed _ state.native inner innerMember
        obtain ⟨_, kid, pending, sessions⟩ := PqxdhDeploymentCompileFootprint.hmac_fixed key message _ _ reached
        exact ⟨⟨kid, hmac_seals key message _ _ reached, sessions, pending,
          (PqxdhServerAuthExperiment.hmac_step (Reader := Reader) (Response := Response) (setup := setup)
            (publicValue := PqxdhJointGapDh.challenge setup.joint setup.dh serverSeed
              PqxdhRegistrationSchedule.observationScalar) key message _ _ reached).2.1.ctx⟩,
          fun k => by rw [owners],
          PqxdhDeploymentCompileInvariant.shared_inits setup serverSeed _ state.native inner innerMember⟩
    | hash bytes =>
        simp only [PqxdhDeploymentNative.handler] at member
        obtain ⟨inner, innerMember, rfl⟩ := PqxdhDeploymentEligibility.onNative_support _ state answer member
        simp only [PqxdhRegistrationSchedule.handler,
          ← PqxdhServerAuthNative.hash_native setup serverSeed PqxdhRegistrationSchedule.observationScalar]
          at innerMember
        obtain ⟨owners, reached⟩ :=
          PqxdhDeploymentCompileInvariant.shared_footprint setup serverSeed _ state.native inner innerMember
        obtain ⟨_, kid, pending, sessions⟩ := PqxdhDeploymentCompileFootprint.hash_fixed bytes _ _ reached
        exact ⟨⟨kid, hash_seals bytes _ _ reached, sessions, pending, (hashOracle_grows bytes _ _ reached).2.1⟩,
          fun k => by rw [owners],
          PqxdhDeploymentCompileInvariant.shared_inits setup serverSeed _ state.native inner innerMember⟩
    | serverSend kid plaintext => exact serverStep_kept setup codec route (.inl (plaintext, kid)) state answer member
    | serverRaw raw => exact serverStep_kept setup codec route (.inr raw) state answer member
    | beaconSend index plaintext => exact beaconStep_kept setup codec index (.inl plaintext) state answer member
    | beaconRaw index raw => exact beaconStep_kept setup codec index (.inr raw) state answer member

/-- A native-interface program that issues only coins and sends keeps the Server fields and every owner's invariant fields (the secrecy commands, `PqxdhDeploymentSecrecy.secrecy_frame`). -/
theorem coinSend_kept {Value : Type} (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (serverSeed : IdentitySeed) (program : OracleComp Spec Value)
    (bounded : program.IsQueryBoundP (fun query => PqxdhDeploymentSecrecy.coinOrSend query = false) 0)
    (state : PqxdhDeploymentNative.State KemSK) (result : Value × PqxdhDeploymentNative.State KemSK)
    (supported : result ∈ support ((simulateQ (PqxdhDeploymentNative.handler setup codec checks route serverSeed)
      program).run state)) :
    Kept state.native result.2.native := by
  induction program using OracleComp.inductionOn generalizing state with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
      subst supported
      exact kept_refl _
  | query_bind query next ih =>
      rw [isQueryBoundP_query_bind_iff] at bounded
      obtain ⟨allowed, rest⟩ := bounded
      have kind : PqxdhDeploymentSecrecy.coinOrSend query = true := by
        rcases allowed with free | impossible
        · simpa using free
        · omega
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, id_map,
        StateT.run_bind, mem_support_bind_iff] at supported
      obtain ⟨⟨reply, middle⟩, first, second⟩ := supported
      have firstKept : Kept state.native middle.native := by
        rcases query with coin | command
        · exact native_quiet setup codec checks route serverSeed (.inl coin) trivial state _ first
        · cases command with
          | serverSend kid plaintext => exact serverStep_kept setup codec route (.inl (plaintext, kid)) state _ first
          | beaconSend index plaintext => exact beaconStep_kept setup codec index (.inl plaintext) state _ first
          | _ => simp [PqxdhDeploymentSecrecy.coinOrSend] at kind
      have restBound := rest reply
      simp only [kind, Bool.true_eq_false, ite_false] at restBound
      exact kept_trans _ _ _ firstKept (ih reply restBound middle second)

/-! ### The raw accept and the build on the ghost seal log -/

/-- `get_shared_secret` keeps the ghost seal log: it appends Extract-table touches only. -/
theorem accept_seals (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (publicValue : PqxdhJointGapDh.PublicChallenge) (raw : Pqxdh.Bytes) (game : GameState KemSK)
    (result : Option Nat × GameState KemSK)
    (supported : result ∈ support ((acceptOracle setup codec checks publicValue raw).run game)) :
    result.2.ghost.seals = game.ghost.seals := by
  simp only [acceptOracle, StateT.run_bind, StateT.run_get, pure_bind] at supported
  obtain ⟨collected, lifted, supported⟩ := (mem_support_bind_iff _ _ _).1 supported
  obtain ⟨_, same⟩ := liftCoins_mem _ _ _ lifted
  simp only [StateT.run_set, pure_bind, same] at supported
  cases hc : collected.1.1 with
  | none =>
      simp only [hc, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
      subst supported
      rfl
  | some input =>
      simp only [hc, StateT.run_bind, mem_support_bind_iff] at supported
      obtain ⟨returned, derived, supported⟩ := supported
      obtain ⟨consumed, extra, eq, _, _⟩ := client_run game.sessions (binding setup publicValue) input _
        returned derived
      rcases returned with ⟨outcome, after⟩
      dsimp only at eq
      rcases outcome with (_ | token) | error | _
      · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
        subst supported
        rw [eq]
      · simp only [StateT.run_bind, StateT.run_modify, pure_bind, StateT.run_pure, support_pure,
          Set.mem_singleton_iff] at supported
        subst supported
        rw [eq]
      · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
        subst supported
        rw [eq]
      · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
        subst supported
        rw [eq]

/-- A settled build that answers a response came from an ordinary builder result with that response. -/
theorem settle_some (server : PqxdhServerRegistrationPublication.State Unit PqxdhTranscriptAd.AssociatedData (List Pqxdh.Bytes))
    (outcome : RustM (Option PqxdhServerRegistrationPublication.Response ×
      PqxdhServerRegistrationPublication.State Unit PqxdhTranscriptAd.AssociatedData (List Pqxdh.Bytes)))
    (response : PqxdhServerRegistrationPublication.Response) (found : (settle server outcome).1 = some response) :
    ∃ after, outcome = .ok (some response, after) := by
  cases outcome with
  | ok value =>
      refine ⟨value.2, ?_⟩
      simp only [settle] at found
      rw [← found]
  | fail error => simp [settle] at found
  | div => simp [settle] at found

/-- `build_registration_response` appends to the ghost seal log only contexts under the built handle, none without a pending token, and on a successful build exactly one context: the first-send context of the committed candidate, sealed under `PqxdhTranscriptAd.adOf` of the digest that the BLAKE2b cache holds after the build for the registration transcript of the token's retained Init fields and the candidate's Phase 2 fields, whose Phase 2 writer output is the response (`PqxdhServerAuthNegativeControl.tail_published` after the transcript hash of `buildOracle`). -/
theorem build_seals (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (session : Nat) (payload : Option Pqxdh.Bytes) (game : GameState KemSK)
    (result : Option PqxdhServerRegistrationPublication.Response × GameState KemSK)
    (supported : result ∈ support ((buildOracle setup codec checks session payload).run game)) :
    ∃ logged : List RawCtxSourceSend.SealContext,
      result.2.ghost.seals = game.ghost.seals ++ logged.map (fun context => (session, context)) ∧
      (game.pending session = none → logged = []) ∧
      ∀ response, result.1 = some response → ∃ (token : PqxdhServerRelatedRootConsumer.Returned)
        (candidate : beaconcrypt_core.pqxdh.ServerRegistrationCandidate)
        (frameBytes : Pqxdh.Bytes) (digest : CtxRomAuth.CtxDigest) (context : RawCtxSourceSend.SealContext),
        game.pending session = some token ∧ logged = [context] ∧
        codec.write2 ⟨candidate.key_id, candidate.ephemeral_public_key, candidate.server_identity_public_key,
          candidate.kem_ciphertext, frameBytes⟩ = some response.serialized ∧
        result.2.ctx ((), PqxdhTranscriptAd.transcript (PqxdhTranscriptAd.initOf token.init)
          (PqxdhTranscriptAd.serverResponse candidate)) = some digest ∧
        context.associatedData = PqxdhRefinement.absBytes (PqxdhTranscriptAd.adOf digest) := by
  simp only [buildOracle, StateT.run_bind, StateT.run_get, pure_bind] at supported
  cases found : game.pending session with
  | none =>
      simp only [found, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
      subst supported
      exact ⟨[], by simp, fun _ => rfl, fun _ reply => by cases reply⟩
  | some token =>
      cases passed : PqxdhServerRegistrationPublication.prehash game.server token.pending payload with
      | none =>
          simp only [found, passed, StateT.run_bind, StateT.run_set, pure_bind, StateT.run_pure, support_pure,
            Set.mem_singleton_iff] at supported
          subst supported
          exact ⟨[], by simp, ⟨fun _ => rfl, fun _ reply => by cases reply⟩⟩
      | some candidate =>
          simp only [found, passed, StateT.run_bind, mem_support_bind_iff] at supported
          obtain ⟨⟨digest, hashed⟩, hashing, supported⟩ := supported
          obtain ⟨hashedEq, _, cached⟩ := hashOracle_grows _ game _ hashing
          obtain ⟨cache, rfl⟩ : ∃ cache, hashed = { game with ctx := cache } := ⟨_, hashedEq⟩
          obtain ⟨_, currentMem, supported⟩ := supported
          rw [StateT.run_get, support_pure, Set.mem_singleton_iff] at currentMem
          subst currentMem
          obtain ⟨built, lifted, supported⟩ := supported
          obtain ⟨member, same⟩ := liftCoins_mem _ _ _ lifted
          simp only [same, StateT.run_set, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
          obtain ⟨_, rfl, rfl⟩ := supported
          refine ⟨built.1.2.1, rfl, ⟨fun missing => absurd missing (by simp), fun response reply => ?_⟩⟩
          have grown := tail_run_grows setup codec checks _ _ built.1 member
          have tailMember := member
          rw [PqxdhServerRegistrationPublication.build_prehash_some (associatedData := PqxdhTranscriptAd.adOf digest)
            setup.source _ _ payload _ game.server candidate passed] at tailMember
          obtain ⟨_, _, frameBytes, _, _, _, _, written, log⟩ :=
            PqxdhServerAuthNegativeControl.tail_published (PqxdhTranscriptAd.adOf digest)
              (PqxdhTranscriptAd.adOf digest) setup codec checks candidate token.root payload game.server cache built.1
              tailMember response reply
          exact ⟨token, candidate, frameBytes, digest, _, rfl, log, written, grown cached, rfl⟩

/-! ### Owner updates -/

/-- The Beacon invariant survives a step that appends one owner that is not InitSent and expects its own pin, keeps the retained bundles, only extends the BLAKE2b cache, and adds no successful bundle, successful finish or acceptance. -/
theorem beaconInv_append (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (before after : PqxdhDeploymentSecrecy.State KemSK)
    (inv : BeaconInv setup codec before) (next : PqxdhRegistrationSchedule.Owner KemSK)
    (owners : after.2.native.owners = before.2.native.owners ++ [next])
    (inits : after.2.native.inits = before.2.native.inits)
    (grow : before.2.native.shared.2.ctx ≤ after.2.native.shared.2.ctx)
    (bundles : ∀ k bytes, (⟨.inl (.inr (.bundle k)), some bytes⟩ : Entry) ∈ after.1.transcript →
      (⟨.inl (.inr (.bundle k)), some bytes⟩ : Entry) ∈ before.1.transcript)
    (finishes : ∀ k raw reply, (⟨.inl (.inr (.finish k raw)), some reply⟩ : Entry) ∈ after.1.transcript →
      (⟨.inl (.inr (.finish k raw)), some reply⟩ : Entry) ∈ before.1.transcript)
    (controls : ∀ control prekey oneTime kem, next.beacon.phase ≠ .initSent control prekey oneTime kem)
    (pinned : ∀ pin, expectedPin next.beacon.phase = some pin → pin = next.beacon.serverIdentity)
    (accepts : ∀ c result, accepted c (regsOf after.1.transcript) = some result →
      accepted c (regsOf before.1.transcript) = some result) : BeaconInv setup codec after := by
  have lookup : ∀ (k : Nat) (owner : PqxdhRegistrationSchedule.Owner KemSK), after.2.native.owners[k]? = some owner →
      before.2.native.owners[k]? = some owner ∨ (k = before.2.native.owners.length ∧ owner = next) := by
    intro k owner found
    rw [owners] at found
    by_cases below : k < before.2.native.owners.length
    · left
      rwa [List.getElem?_append_left below] at found
    · right
      rw [List.getElem?_append_right (Nat.le_of_not_lt below)] at found
      cases position : k - before.2.native.owners.length with
      | zero =>
          rw [position] at found
          exact ⟨by omega, by simpa using found.symm⟩
      | succ rest =>
          rw [position] at found
          simp at found
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro k owner control prekey oneTime kem found phase
    rcases lookup k owner found with old | ⟨_, rfl⟩
    · exact inv.controls k owner control prekey oneTime kem old phase
    · exact absurd phase (controls control prekey oneTime kem)
  · intro k bytes member
    rw [inits]
    exact inv.bundled k bytes (bundles k bytes member)
  · intro k init found
    rw [inits] at found
    rw [owners, List.length_append, List.length_singleton]
    exact Nat.lt_succ_of_lt (inv.initsBelow k init found)
  · intro k owner found expected unsent
    rw [inits]
    rcases lookup k owner found with old | ⟨rfl, rfl⟩
    · exact inv.freshUnretained k owner old expected unsent
    · cases retained : before.2.native.inits before.2.native.owners.length with
      | none => rfl
      | some init => exact absurd (inv.initsBelow _ init retained) (lt_irrefl _)
  · intro k raw reply member
    obtain ⟨owner, init, response, digest, found, initFound, decoded, cached, stored⟩ :=
      inv.installedTranscript k raw reply (finishes k raw reply member)
    have bound : k < before.2.native.owners.length := (List.getElem?_eq_some_iff.mp found).1
    exact ⟨owner, init, response, digest, by rw [owners, List.getElem?_append_left bound]; exact found,
      by rw [inits]; exact initFound, decoded, grow cached, stored⟩
  · intro k owner pin found expected
    rcases lookup k owner found with old | ⟨_, rfl⟩
    · exact inv.pinned k owner pin old expected
    · exact pinned pin expected
  · intro c earlier raw found
    obtain ⟨owner, control, associatedData, kernel, ownerFound, phase⟩ := inv.accepts c earlier raw (accepts c _ found)
    have bound : c < before.2.native.owners.length := (List.getElem?_eq_some_iff.mp ownerFound).1
    exact ⟨owner, control, associatedData, kernel, by rw [owners, List.getElem?_append_left bound]; exact ownerFound,
      phase⟩

/-- The Beacon invariant survives a step that replaces one owner that is not established by an owner satisfying the owner clauses, keeps the other owners' retained bundles, only extends the BLAKE2b cache, adds successful bundle and finish entries only for that owner, for which the bundle and finish clauses hold after the step, and adds only that owner's acceptance, which leaves it established. -/
theorem beaconInv_set (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (before after : PqxdhDeploymentSecrecy.State KemSK)
    (inv : BeaconInv setup codec before) (index : Nat) (old next : PqxdhRegistrationSchedule.Owner KemSK)
    (found : before.2.native.owners[index]? = some old)
    (owners : after.2.native.owners = before.2.native.owners.set index next)
    (inactive : ∀ control associatedData kernel, old.beacon.phase ≠ .established control associatedData kernel)
    (controls : ∀ control prekey oneTime kem, next.beacon.phase = .initSent control prekey oneTime kem →
      control.beacon_identity_public_key =
        PqxdhRootTableInitialization.rootArray (setup.joint.publicKeys next.beacon.identity).ed25519)
    (pinned : ∀ pin, expectedPin next.beacon.phase = some pin → pin = next.beacon.serverIdentity)
    (inits : ∀ k, k ≠ index → after.2.native.inits k = before.2.native.inits k)
    (grow : before.2.native.shared.2.ctx ≤ after.2.native.shared.2.ctx)
    (bundles : ∀ k bytes, k ≠ index → (⟨.inl (.inr (.bundle k)), some bytes⟩ : Entry) ∈ after.1.transcript →
      (⟨.inl (.inr (.bundle k)), some bytes⟩ : Entry) ∈ before.1.transcript)
    (finishes : ∀ k raw reply, k ≠ index →
      (⟨.inl (.inr (.finish k raw)), some reply⟩ : Entry) ∈ after.1.transcript →
      (⟨.inl (.inr (.finish k raw)), some reply⟩ : Entry) ∈ before.1.transcript)
    (bundled : ∀ bytes, (⟨.inl (.inr (.bundle index)), some bytes⟩ : Entry) ∈ after.1.transcript →
      ∃ init, after.2.native.inits index = some init ∧ codec.write1 init = some bytes)
    (unretained : expectedPin next.beacon.phase ≠ none → controlIdentity next.beacon.phase = none →
      after.2.native.inits index = none)
    (installed : ∀ raw reply, (⟨.inl (.inr (.finish index raw)), some reply⟩ : Entry) ∈ after.1.transcript →
      ∃ (init : PqxdhEd25519EufCma.Phase1Candidate) (response : Pqxdh.SessionTranscript.ResponseFields)
        (digest : CtxRomAuth.CtxDigest),
        after.2.native.inits index = some init ∧ responseOf codec raw = some response ∧
        after.2.native.shared.2.ctx ((), PqxdhTranscriptAd.transcript (PqxdhTranscriptAd.initOf init) response) =
          some digest ∧
        establishedAd next.beacon.phase = some (PqxdhTranscriptAd.adOf digest))
    (accepts : ∀ c result, accepted c (regsOf after.1.transcript) = some result →
      accepted c (regsOf before.1.transcript) = some result ∨
        (c = index ∧ ∃ control associatedData kernel, next.beacon.phase = .established control associatedData kernel)) :
    BeaconInv setup codec after := by
  have bound : index < before.2.native.owners.length := (List.getElem?_eq_some_iff.mp found).1
  have atIndex : after.2.native.owners[index]? = some next := by rw [owners, List.getElem?_set_self bound]
  have others : ∀ k : Nat, k ≠ index → after.2.native.owners[k]? = before.2.native.owners[k]? := by
    intro k different
    rw [owners, List.getElem?_set_ne (Ne.symm different)]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro k owner control prekey oneTime kem ownerFound phase
    by_cases same : k = index
    · rw [same, atIndex, Option.some.injEq] at ownerFound
      subst ownerFound
      exact controls control prekey oneTime kem phase
    · rw [others k same] at ownerFound
      exact inv.controls k owner control prekey oneTime kem ownerFound phase
  · intro k bytes member
    by_cases same : k = index
    · subst same
      exact bundled bytes member
    · rw [inits k same]
      exact inv.bundled k bytes (bundles k bytes same member)
  · intro k init retained
    rw [owners, List.length_set]
    by_cases same : k = index
    · rw [same]
      exact bound
    · rw [inits k same] at retained
      exact inv.initsBelow k init retained
  · intro k owner ownerFound expected unsent
    by_cases same : k = index
    · rw [same, atIndex, Option.some.injEq] at ownerFound
      subst ownerFound
      rw [same]
      exact unretained expected unsent
    · rw [others k same] at ownerFound
      rw [inits k same]
      exact inv.freshUnretained k owner ownerFound expected unsent
  · intro k raw reply member
    by_cases same : k = index
    · subst same
      obtain ⟨init, response, digest, initFound, decoded, cached, stored⟩ := installed raw reply member
      exact ⟨next, init, response, digest, atIndex, initFound, decoded, cached, stored⟩
    · obtain ⟨owner, init, response, digest, ownerFound, initFound, decoded, cached, stored⟩ :=
        inv.installedTranscript k raw reply (finishes k raw reply same member)
      exact ⟨owner, init, response, digest, by rw [others k same]; exact ownerFound,
        by rw [inits k same]; exact initFound, decoded, grow cached, stored⟩
  · intro k owner pin ownerFound expected
    by_cases same : k = index
    · rw [same, atIndex, Option.some.injEq] at ownerFound
      subst ownerFound
      exact pinned pin expected
    · rw [others k same] at ownerFound
      exact inv.pinned k owner pin ownerFound expected
  · intro c earlier raw acceptedAfter
    rcases accepts c _ acceptedAfter with previous | ⟨same, control, associatedData, kernel, phase⟩
    · obtain ⟨owner, control, associatedData, kernel, ownerFound, phase⟩ := inv.accepts c earlier raw previous
      by_cases same : c = index
      · rw [same, found, Option.some.injEq] at ownerFound
        subst ownerFound
        exact absurd phase (inactive control associatedData kernel)
      · exact ⟨owner, control, associatedData, kernel, by rw [others c same]; exact ownerFound, phase⟩
    · rw [same]
      exact ⟨next, control, associatedData, kernel, atIndex, phase⟩

/-! ### Transcript entries -/

/-- An entry of a transcript extended by one other entry was already there. -/
theorem mem_snoc_ne {transcript : List Entry} {entry other : Entry} (member : other ∈ transcript ++ [entry])
    (different : other ≠ entry) : other ∈ transcript := by
  rcases List.mem_append.mp member with old | new
  · exact old
  · exact absurd (List.mem_singleton.mp new) different

/-- A successful bundle entry equal to a bundle entry names the same owner and the reply. -/
theorem bundle_entry {k index : Nat} {bytes : Pqxdh.Bytes} {answer : Option Pqxdh.Bytes}
    (same : (⟨.inl (.inr (.bundle k)), some bytes⟩ : Entry) = ⟨.inl (.inr (.bundle index)), answer⟩) :
    k = index ∧ answer = some bytes := by
  cases same
  exact ⟨rfl, rfl⟩

/-- A successful finish entry equal to a finish entry names the same owner and input and the reply. -/
theorem finish_entry {k index : Nat} {raw input reply : Pqxdh.Bytes} {answer : Option Pqxdh.Bytes}
    (same : (⟨.inl (.inr (.finish k raw)), some reply⟩ : Entry) = ⟨.inl (.inr (.finish index input)), answer⟩) :
    k = index ∧ raw = input ∧ answer = some reply := by
  cases same
  exact ⟨rfl, rfl, rfl⟩

/-- An owner without established associated data has no successful finish entry. -/
theorem finish_absent (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (state : PqxdhDeploymentSecrecy.State KemSK) (inv : BeaconInv setup codec state) (index : Nat)
    (owner : PqxdhRegistrationSchedule.Owner KemSK) (found : state.2.native.owners[index]? = some owner)
    (inactive : establishedAd owner.beacon.phase = none) (raw reply : Pqxdh.Bytes) :
    (⟨.inl (.inr (.finish index raw)), some reply⟩ : Entry) ∉ state.1.transcript := by
  intro member
  obtain ⟨other, _, _, _, otherFound, _, _, _, stored⟩ := inv.installedTranscript index raw reply member
  rw [found, Option.some.injEq] at otherFound
  subst otherFound
  rw [inactive] at stored
  cases stored

/-- A Fresh or Fresh-with-coins owner has no successful bundle entry. -/
theorem bundle_absent (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (state : PqxdhDeploymentSecrecy.State KemSK) (inv : BeaconInv setup codec state) (index : Nat)
    (owner : PqxdhRegistrationSchedule.Owner KemSK) (found : state.2.native.owners[index]? = some owner)
    (expected : expectedPin owner.beacon.phase ≠ none) (unsent : controlIdentity owner.beacon.phase = none)
    (bytes : Pqxdh.Bytes) : (⟨.inl (.inr (.bundle index)), some bytes⟩ : Entry) ∉ state.1.transcript := by
  intro member
  obtain ⟨init, retained, _⟩ := inv.bundled index bytes member
  rw [inv.freshUnretained index owner found expected unsent] at retained
  cases retained

/-! ### Every query keeps the invariants -/

section Steps
open PqxdhDeploymentSecrecy (Ledger)
open PqxdhDeploymentHeadlineCtTrace (NotBuild)

/-- Coins, the public HMAC and BLAKE2b oracles and the record commands keep both invariants. -/
theorem quiet_step (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (serverSeed : IdentitySeed) (server : RawCtxServerRouting.Identity)
    (serverKid : Std.U64) (command : Spec.Domain)
    (kind : match command with
      | .inr (.create _ _) | .inr (.bundle _) | .inr (.accept _) | .inr (.build _ _) | .inr (.finish _ _) => False
      | _ => True)
    (ledger : Ledger) (native : PqxdhDeploymentNative.State KemSK)
    (serverInv : ServerInv codec server serverKid (ledger, native)) (beaconInv : BeaconInv setup codec (ledger, native))
    (answer : Spec.Range command × PqxdhDeploymentNative.State KemSK)
    (member : answer ∈ support ((PqxdhDeploymentNative.handler setup codec checks route serverSeed command).run
      native)) :
    ServerInv codec server serverKid (ledger.record (.inl command) answer.1, answer.2) ∧
      BeaconInv setup codec (ledger.record (.inl command) answer.1, answer.2) := by
  have kept := native_quiet setup codec checks route serverSeed command kind native answer member
  have notBuild : NotBuild (.inl command : PqxdhDeploymentInterface.Query) := by
    rcases command with coin | command
    · trivial
    · cases command <;> first | exact False.elim kind | trivial
  have notFinish : ∀ owner raw payload,
      regOfEntry ⟨.inl command, answer.1⟩ ≠ some (.finish owner raw (some payload)) := by
    intro owner raw payload found
    rcases command with coin | command
    · simp [regOfEntry] at found
    · cases command <;> first | exact False.elim kind | simp [regOfEntry] at found
  have other : ∀ k raw, (.inl (.inr (.bundle k)) : PqxdhDeploymentInterface.Query) ≠ .inl command ∧
      (.inl (.inr (.finish k raw)) : PqxdhDeploymentInterface.Query) ≠ .inl command := by
    intro k raw
    rcases command with coin | command
    · simp
    · cases command <;> first | exact False.elim kind | simp
  exact ⟨serverInv_frame codec server serverKid _ _ serverInv kept.1 ⟨.inl command, answer.1⟩ rfl notBuild,
    beaconInv_frame setup codec _ _ beaconInv kept.2.1 kept.2.2 kept.1.ctx
      (fun k bytes entry => mem_snoc_ne entry fun same => (other k []).1 (congrArg Entry.query same))
      (fun k raw reply entry => mem_snoc_ne entry fun same => (other k raw).2 (congrArg Entry.query same))
      fun c result found => by
        rw [show (ledger.record (.inl command) answer.1).transcript = ledger.transcript ++ [⟨.inl command, answer.1⟩]
          from rfl, accepted_quiet _ _ notFinish] at found
        exact found⟩

/-- A create keeps both invariants: a created owner is Fresh, expects its own pin and has no retained bundle. -/
theorem create_step (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (serverSeed : IdentitySeed) (server : RawCtxServerRouting.Identity)
    (serverKid : Std.U64) (pin : Pqxdh.Bytes) (keyId : Std.U64) (ledger : Ledger)
    (native : PqxdhDeploymentNative.State KemSK)
    (serverInv : ServerInv codec server serverKid (ledger, native)) (beaconInv : BeaconInv setup codec (ledger, native))
    (answer : Option Nat × PqxdhDeploymentNative.State KemSK)
    (member : answer ∈ support ((PqxdhDeploymentNative.handler setup codec checks route serverSeed
      (.inr (.create pin keyId))).run native)) :
    ServerInv codec server serverKid (ledger.record (.inl (.inr (.create pin keyId))) answer.1, answer.2) ∧
      BeaconInv setup codec (ledger.record (.inl (.inr (.create pin keyId))) answer.1, answer.2) := by
  have notFinish : ∀ (reply : PqxdhDeploymentInterface.FullSpec.Range (.inl (.inr (.create pin keyId))))
      owner raw payload,
      regOfEntry ⟨.inl (.inr (.create pin keyId)), reply⟩ ≠ some (.finish owner raw (some payload)) := by
    intro reply owner raw payload found
    rcases reply with _ | index
    · simp [regOfEntry] at found
    · cases parsePin pin <;> simp [regOfEntry] at found
  have accepts : ∀ (reply : PqxdhDeploymentInterface.FullSpec.Range (.inl (.inr (.create pin keyId)))) c result,
      accepted c (regsOf (ledger.record (.inl (.inr (.create pin keyId))) reply).transcript) = some result →
        accepted c (regsOf ledger.transcript) = some result := by
    intro reply c result found
    rw [show (ledger.record (.inl (.inr (.create pin keyId))) reply).transcript =
      ledger.transcript ++ [⟨.inl (.inr (.create pin keyId)), reply⟩] from rfl, accepted_quiet _ _ (notFinish reply)]
      at found
    exact found
  have bundles : ∀ (reply : PqxdhDeploymentInterface.FullSpec.Range (.inl (.inr (.create pin keyId)))) k bytes,
      (⟨.inl (.inr (.bundle k)), some bytes⟩ : Entry) ∈ (ledger.record (.inl (.inr (.create pin keyId))) reply).transcript →
        (⟨.inl (.inr (.bundle k)), some bytes⟩ : Entry) ∈ ledger.transcript :=
    fun reply k bytes entry => mem_snoc_ne entry fun same => nomatch same
  have finishes : ∀ (reply : PqxdhDeploymentInterface.FullSpec.Range (.inl (.inr (.create pin keyId)))) k raw value,
      (⟨.inl (.inr (.finish k raw)), some value⟩ : Entry) ∈
        (ledger.record (.inl (.inr (.create pin keyId))) reply).transcript →
        (⟨.inl (.inr (.finish k raw)), some value⟩ : Entry) ∈ ledger.transcript :=
    fun reply k raw value entry => mem_snoc_ne entry fun same => nomatch same
  cases parsed : parsePin pin with
  | none =>
      simp only [PqxdhDeploymentNative.handler, parsed, StateT.run_pure, support_pure, Set.mem_singleton_iff] at member
      subst member
      exact ⟨serverInv_frame codec server serverKid _ _ serverInv ⟨rfl, rfl, rfl, rfl, le_rfl⟩ _ rfl trivial,
        beaconInv_frame setup codec _ _ beaconInv (fun _ => rfl) rfl le_rfl (bundles _) (finishes _) (accepts _)⟩
  | some word =>
      simp only [PqxdhDeploymentNative.handler, parsed, StateT.run_map, support_map, Set.mem_image] at member
      obtain ⟨created, createdMember, rfl⟩ := member
      obtain ⟨inner, innerMember, rfl⟩ := PqxdhDeploymentEligibility.onNative_support _ native created createdMember
      obtain ⟨seed, prekey, keys, rfl⟩ :=
        PqxdhDeploymentEligibility.create_support setup word keyId native.native inner innerMember
      refine ⟨serverInv_frame codec server serverKid _ _ serverInv ⟨rfl, rfl, rfl, rfl, le_rfl⟩ _ rfl trivial, ?_⟩
      refine beaconInv_append setup codec _ _ beaconInv _ rfl rfl le_rfl (bundles _) (finishes _)
        (fun _ _ _ _ phase => by cases phase) (fun value expected => ?_) (accepts _)
      simp only [expectedPin, Option.some.injEq] at expected
      exact expected.symm

/-- A bundle keeps both invariants: a published bundle installs an InitSent control with the owner's own identity key and the expected binding of its Fresh control, and retains the written Phase 1 bundle of the Fresh owner, which had none; a rejected bundle keeps the owner and its retained bundle. -/
theorem bundle_step (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (serverSeed : IdentitySeed) (server : RawCtxServerRouting.Identity)
    (serverKid : Std.U64) (index : Nat) (ledger : Ledger) (native : PqxdhDeploymentNative.State KemSK)
    (serverInv : ServerInv codec server serverKid (ledger, native)) (beaconInv : BeaconInv setup codec (ledger, native))
    (answer : Option Pqxdh.Bytes × PqxdhDeploymentNative.State KemSK)
    (member : answer ∈ support ((PqxdhDeploymentNative.handler setup codec checks route serverSeed
      (.inr (.bundle index))).run native)) :
    ServerInv codec server serverKid (ledger.record (.inl (.inr (.bundle index))) answer.1, answer.2) ∧
      BeaconInv setup codec (ledger.record (.inl (.inr (.bundle index))) answer.1, answer.2) := by
  have notFinish : ∀ (reply : PqxdhDeploymentInterface.FullSpec.Range (.inl (.inr (.bundle index)))) owner raw payload,
      regOfEntry ⟨.inl (.inr (.bundle index)), reply⟩ ≠ some (.finish owner raw (some payload)) := by
    intro reply owner raw payload found
    simp [regOfEntry] at found
  have accepts : ∀ (reply : PqxdhDeploymentInterface.FullSpec.Range (.inl (.inr (.bundle index)))) c result,
      accepted c (regsOf (ledger.record (.inl (.inr (.bundle index))) reply).transcript) = some result →
        accepted c (regsOf ledger.transcript) = some result := by
    intro reply c result found
    rw [show (ledger.record (.inl (.inr (.bundle index))) reply).transcript =
      ledger.transcript ++ [⟨.inl (.inr (.bundle index)), reply⟩] from rfl, accepted_quiet _ _ (notFinish reply)]
      at found
    exact found
  have finishes : ∀ (reply : PqxdhDeploymentInterface.FullSpec.Range (.inl (.inr (.bundle index)))) k raw value,
      (⟨.inl (.inr (.finish k raw)), some value⟩ : Entry) ∈ (ledger.record (.inl (.inr (.bundle index))) reply).transcript →
        (⟨.inl (.inr (.finish k raw)), some value⟩ : Entry) ∈ ledger.transcript :=
    fun reply k raw value entry => mem_snoc_ne entry fun same => nomatch same
  simp only [PqxdhDeploymentNative.handler] at member
  obtain ⟨inner, innerMember, rfl⟩ := PqxdhDeploymentEligibility.onNative_support _ native answer member
  cases found : native.native.owners[index]? with
  | none =>
      have run : (PqxdhRegistrationSchedule.handler setup codec checks serverSeed (.inr (.bundle index))).run
          native.native = pure (none, native.native) := by
        simp only [PqxdhRegistrationSchedule.handler, PqxdhRegistrationSchedule.bundle, StateT.run_bind,
          StateT.run_get, pure_bind, found, StateT.run_pure]
      rw [run, support_pure, Set.mem_singleton_iff] at innerMember
      subst innerMember
      exact ⟨serverInv_frame codec server serverKid _ _ serverInv ⟨rfl, rfl, rfl, rfl, le_rfl⟩ _ rfl trivial,
        beaconInv_frame setup codec _ _ beaconInv (fun _ => rfl) rfl le_rfl
          (fun k bytes entry => mem_snoc_ne entry fun same => nomatch (bundle_entry same).2) (finishes _) (accepts _)⟩
  | some owner =>
      change inner ∈ support (PqxdhRegistrationSchedule.bundle setup codec index native.native) at innerMember
      rw [PqxdhRegistrationSchedule.bundle_source setup codec index native.native owner found, support_map]
        at innerMember
      obtain ⟨reached, reachedMember, rfl⟩ := innerMember
      refine ⟨serverInv_frame codec server serverKid _ _ serverInv ⟨rfl, rfl, rfl, rfl, le_rfl⟩ _ rfl trivial, ?_⟩
      have logged := PqxdhDeploymentCompileFootprint.bundle_log setup codec index owner _ reached reachedMember
      have unlogged : reached.1 ∈ support (simulateQ (PqxdhRegistrationSchedule.bundleCallbacks setup codec
          owner.beacon.identity) (PqxdhLivePhase1Bundle.bundle (PqxdhRegistrationSchedule.projection setup index) owner)) := by
        rw [← PqxdhRegistrationSchedule.bundleLog_fst setup codec owner.beacon.identity _ (native.native.inits index),
          support_map]
        exact ⟨reached, reachedMember, rfl⟩
      obtain ⟨rejected, published⟩ :=
        PqxdhDeploymentEligibility.bundle_candidate setup codec index owner reached.1 unlogged
      rcases outcome : reached.1.1 with _ | bytes
      · have same := rejected outcome
        have retained := logged.1 outcome
        have restored : native.native.owners.set index reached.1.2 = native.native.owners := by
          rw [same]
          exact PqxdhDeploymentCompileRegistration.set_found _ _ _ found
        have initsSame : Function.update native.native.inits index reached.2 = native.native.inits := by
          rw [retained]
          exact Function.update_eq_self _ _
        exact beaconInv_frame setup codec _ _ beaconInv (fun k => by simp only [restored]) initsSame le_rfl
          (fun k bytes entry => mem_snoc_ne entry fun same => nomatch (bundle_entry same).2)
          (finishes _) (accepts _)
      · obtain ⟨fresh, prekey, oneTime, kem, _, _, _, wasFresh, installed, _⟩ := published bytes outcome
        obtain ⟨candidate, retained, written⟩ := logged.2 bytes outcome
        have expected : expectedPin owner.beacon.phase ≠ none := by
          rcases wasFresh with isFresh | isFresh <;> rw [isFresh] <;> simp [expectedPin]
        have unsent : controlIdentity owner.beacon.phase = none := by
          rcases wasFresh with isFresh | isFresh <;> rw [isFresh] <;> rfl
        have inactive : establishedAd owner.beacon.phase = none := by
          rcases wasFresh with isFresh | isFresh <;> rw [isFresh] <;> rfl
        refine beaconInv_set setup codec _ _ beaconInv index owner reached.1.2 found rfl ?_ ?_ ?_ ?_ le_rfl ?_ ?_ ?_ ?_
          ?_ ?_
        · intro control associatedData kernel phase
          rcases wasFresh with isFresh | isFresh <;> rw [isFresh] at phase <;> cases phase
        · intro control prekey' oneTime' kem' phase
          rw [installed] at phase ⊢
          simp only [RawCtxBeaconLifecycle.Phase.initSent.injEq] at phase
          rw [← phase.1]
          rfl
        · intro value expectedValue
          rw [installed] at expectedValue ⊢
          simp only [expectedPin, Option.some.injEq] at expectedValue
          rw [← expectedValue]
          exact beaconInv.pinned index owner _ found
            (by rcases wasFresh with isFresh | isFresh <;> rw [isFresh] <;> rfl)
        · intro k different
          exact Function.update_of_ne different _ _
        · intro k bytes' different entry
          exact mem_snoc_ne entry fun same => different (bundle_entry same).1
        · intro k raw value _ entry
          exact finishes _ k raw value entry
        · intro bytes' entry
          rcases List.mem_append.mp entry with old | new
          · exact absurd old (bundle_absent setup codec _ beaconInv index owner found expected unsent bytes')
          · have reply := (bundle_entry (List.mem_singleton.mp new)).2
            cases reply
            refine ⟨candidate, ?_, written⟩
            change Function.update native.native.inits index reached.2 index = some candidate
            rw [Function.update_self, retained]
        · intro _ unsentNext
          rw [installed] at unsentNext
          cases unsentNext
        · intro raw value entry
          rcases List.mem_append.mp entry with old | new
          · exact absurd old (finish_absent setup codec _ beaconInv index owner found inactive raw value)
          · exact nomatch List.mem_singleton.mp new
        · intro c result found'
          exact Or.inl (accepts _ c result found')

/-- A finish keeps both invariants: a success establishes the InitSent owner with `PqxdhTranscriptAd.adOf` of the digest the BLAKE2b cache holds for the transcript of its retained bundle and the decoded finish input; a failure aborts it or keeps it. The retained bundles are kept and the cache only grows. -/
theorem finish_step (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (serverSeed : IdentitySeed) (server : RawCtxServerRouting.Identity)
    (serverKid : Std.U64) (index : Nat) (raw : Pqxdh.Bytes) (ledger : Ledger)
    (native : PqxdhDeploymentNative.State KemSK)
    (serverInv : ServerInv codec server serverKid (ledger, native)) (beaconInv : BeaconInv setup codec (ledger, native))
    (answer : Option Pqxdh.Bytes × PqxdhDeploymentNative.State KemSK)
    (member : answer ∈ support ((PqxdhDeploymentNative.handler setup codec checks route serverSeed
      (.inr (.finish index raw))).run native)) :
    ServerInv codec server serverKid (ledger.record (.inl (.inr (.finish index raw))) answer.1, answer.2) ∧
      BeaconInv setup codec (ledger.record (.inl (.inr (.finish index raw))) answer.1, answer.2) := by
  simp only [PqxdhDeploymentNative.handler] at member
  obtain ⟨inner, innerMember, rfl⟩ := PqxdhDeploymentEligibility.onNative_support _ native answer member
  have shared := PqxdhRegistrationSchedule.owner_fields setup codec checks serverSeed (.inr (.finish index raw)) trivial
    native.native inner innerMember
  have accepts := fun (reply : Option Pqxdh.Bytes) c result found =>
    accepted_finish ledger.transcript index raw reply c result found
  have bundles : ∀ (reply : Option Pqxdh.Bytes) k bytes,
      (⟨.inl (.inr (.bundle k)), some bytes⟩ : Entry) ∈ (ledger.record (.inl (.inr (.finish index raw))) reply).transcript →
        (⟨.inl (.inr (.bundle k)), some bytes⟩ : Entry) ∈ ledger.transcript :=
    fun reply k bytes entry => mem_snoc_ne entry fun same => nomatch same
  have unanswered : ∀ k input value, (⟨.inl (.inr (.finish k input)), some value⟩ : Entry) ∈
      (ledger.record (.inl (.inr (.finish index raw))) none).transcript →
      (⟨.inl (.inr (.finish k input)), some value⟩ : Entry) ∈ ledger.transcript :=
    fun k input value entry => mem_snoc_ne entry fun same => nomatch (finish_entry same).2.2
  cases found : native.native.owners[index]? with
  | none =>
      change inner ∈ support ((PqxdhRegistrationSchedule.finish setup codec index raw).run native.native) at innerMember
      rw [PqxdhRegistrationSchedule.finish_missing setup codec index raw native.native found, support_pure,
        Set.mem_singleton_iff] at innerMember
      subst innerMember
      exact ⟨serverInv_frame codec server serverKid _ _ serverInv ⟨rfl, rfl, rfl, rfl, le_rfl⟩ _ rfl trivial,
        beaconInv_frame setup codec _ _ beaconInv (fun _ => rfl) rfl le_rfl (bundles _) unanswered
          fun c result found' => (accepts _ c result found').resolve_right (by simp)⟩
  | some owner =>
      change inner ∈ support (PqxdhRegistrationSchedule.finish setup codec index raw native.native) at innerMember
      rw [PqxdhRegistrationSchedule.finish_source setup codec index raw native.native owner found, support_map]
        at innerMember
      obtain ⟨reached, reachedMember, rfl⟩ := innerMember
      obtain ⟨_, grow, failed, finished⟩ := PqxdhDeploymentCompileFootprint.ownerFinish_owner setup codec
        (native.native.inits index) raw owner native.native.shared reached reachedMember
      have serverKept : ServerKept native.native
          { native.native with shared := reached.2, owners := native.native.owners.set index reached.1.2 } :=
        ⟨by rw [shared], by rw [shared], by rw [shared], by rw [shared], grow⟩
      refine ⟨serverInv_frame codec server serverKid _ _ serverInv serverKept _ rfl trivial, ?_⟩
      have others : ∀ (answer : Option Pqxdh.Bytes) k input value, k ≠ index →
          (⟨.inl (.inr (.finish k input)), some value⟩ : Entry) ∈
            (ledger.record (.inl (.inr (.finish index raw))) answer).transcript →
          (⟨.inl (.inr (.finish k input)), some value⟩ : Entry) ∈ ledger.transcript :=
        fun answer k input value different entry => mem_snoc_ne entry fun same => different (finish_entry same).1
      have oldBundles : ∀ (answer : Option Pqxdh.Bytes) bytes, (⟨.inl (.inr (.bundle index)), some bytes⟩ : Entry) ∈
          (ledger.record (.inl (.inr (.finish index raw))) answer).transcript →
          ∃ init, native.native.inits index = some init ∧ codec.write1 init = some bytes :=
        fun answer bytes entry => beaconInv.bundled index bytes (bundles _ index bytes entry)
      rcases reply : reached.1.1 with _ | plaintext
      · rcases failed reply with unchanged | ⟨control, prekey, oneTime, kem, ownerPhase, aborted⟩
        · have restored : native.native.owners.set index reached.1.2 = native.native.owners := by
            rw [unchanged]
            exact PqxdhDeploymentCompileRegistration.set_found _ _ _ found
          exact beaconInv_frame setup codec _ _ beaconInv (fun k => by simp only [restored]) rfl grow (bundles _)
            unanswered fun c result found' => (accepts _ c result found').resolve_right (by simp)
        · have inactive : establishedAd owner.beacon.phase = none := by rw [ownerPhase]; rfl
          refine beaconInv_set setup codec _ _ beaconInv index owner reached.1.2 found rfl ?_ ?_ ?_ (fun _ _ => rfl)
            grow (fun k bytes _ entry => bundles _ k bytes entry) (fun k input value _ entry => unanswered k input value entry)
            (oldBundles _) ?_ ?_ ?_
          · intro control' associatedData kernel phase
            rw [ownerPhase] at phase
            cases phase
          · intro control' prekey' oneTime' kem' phase
            rw [aborted] at phase
            cases phase
          · intro value expected
            rw [aborted] at expected
            cases expected
          · intro expected _
            rw [aborted] at expected
            exact absurd rfl expected
          · intro input value entry
            rcases List.mem_append.mp entry with old | new
            · exact absurd old (finish_absent setup codec _ beaconInv index owner found inactive input value)
            · exact nomatch (finish_entry (List.mem_singleton.mp new)).2.2
          · intro c result found'
            exact Or.inl ((accepts _ c result found').resolve_right (by simp))
      · obtain ⟨control, prekey, oneTime, kem, response, kernel, init, fields, digest, ownerPhase, _, retained,
          decoded, cached, installed⟩ := finished plaintext reply
        have inactive : establishedAd owner.beacon.phase = none := by rw [ownerPhase]; rfl
        refine beaconInv_set setup codec _ _ beaconInv index owner reached.1.2 found rfl ?_ ?_ ?_ (fun _ _ => rfl)
          grow (fun k bytes _ entry => bundles _ k bytes entry) (others _) (oldBundles _) ?_ ?_ ?_
        · intro control' associatedData kernel' phase
          rw [ownerPhase] at phase
          cases phase
        · intro control' prekey' oneTime' kem' phase
          rw [installed] at phase
          cases phase
        · intro value expected
          rw [installed] at expected
          cases expected
        · intro expected _
          rw [installed] at expected
          exact absurd rfl expected
        · intro input value entry
          rcases List.mem_append.mp entry with old | new
          · exact absurd old (finish_absent setup codec _ beaconInv index owner found inactive input value)
          · obtain ⟨_, same, _⟩ := finish_entry (List.mem_singleton.mp new)
            subst same
            refine ⟨init, fields, digest, retained, decoded, cached, ?_⟩
            rw [installed]
            rfl
        · intro c result found'
          rcases accepts _ c result found' with previous | ⟨same, _⟩
          · exact Or.inl previous
          · exact Or.inr ⟨same, _, _, _, by rw [installed]⟩

/-- A raw accept keeps both invariants: the returned handle is the old session counter, with no seal yet, and its pending token carries the identity and the retained Init fields read from the accept bytes; the BLAKE2b cache only grows. -/
theorem accept_step (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (serverSeed : IdentitySeed) (server : RawCtxServerRouting.Identity)
    (serverKid : Std.U64) (raw : Pqxdh.Bytes) (ledger : Ledger) (native : PqxdhDeploymentNative.State KemSK)
    (serverInv : ServerInv codec server serverKid (ledger, native)) (beaconInv : BeaconInv setup codec (ledger, native))
    (answer : Option Nat × PqxdhDeploymentNative.State KemSK)
    (member : answer ∈ support ((PqxdhDeploymentNative.handler setup codec checks route serverSeed
      (.inr (.accept raw))).run native)) :
    ServerInv codec server serverKid (ledger.record (.inl (.inr (.accept raw))) answer.1, answer.2) ∧
      BeaconInv setup codec (ledger.record (.inl (.inr (.accept raw))) answer.1, answer.2) := by
  have notFinish : ∀ (reply : Option Nat) owner input payload, regOfEntry ⟨.inl (.inr (.accept raw)), reply⟩ ≠
      some (.finish owner input (some payload)) := by
    intro reply owner input payload found
    simp [regOfEntry] at found
  simp only [PqxdhDeploymentNative.handler] at member
  obtain ⟨inner, innerMember, rfl⟩ := PqxdhDeploymentEligibility.onNative_support _ native answer member
  simp only [PqxdhRegistrationSchedule.handler,
    ← PqxdhServerAuthNative.accept_native setup codec checks serverSeed PqxdhRegistrationSchedule.observationScalar]
    at innerMember
  have initsSame := PqxdhDeploymentCompileInvariant.shared_inits setup serverSeed _ native.native inner innerMember
  obtain ⟨owners, reached⟩ := PqxdhDeploymentCompileInvariant.shared_footprint setup serverSeed _ native.native inner
    innerMember
  obtain ⟨_, kid, sessions, others, rejected, returned⟩ :=
    PqxdhDeploymentCompileFootprint.accept_footprint setup codec checks _ raw _ _ reached
  have initRead := PqxdhDeploymentCompileFootprint.accept_init setup codec checks _ raw _ _ reached
  have grow := (PqxdhServerAuthExperiment.accept_step (Reader := Reader) (Response := Response) (setup := setup)
    codec checks raw _ _ reached).2.1.ctx
  have seals := accept_seals setup codec checks _ raw _ _ reached
  refine ⟨⟨?_, ?_, ?_, ?_⟩, beaconInv_frame setup codec _ _ beaconInv (fun k => by simp only [owners]) initsSame grow
    (fun k bytes entry => mem_snoc_ne entry fun same => nomatch same)
    (fun k input value entry => mem_snoc_ne entry fun same => nomatch same)
    fun c result found => ?_⟩
  · show inner.2.shared.2.server.identityKeyId = serverKid
    rw [kid]
    exact serverInv.kid
  · intro session context logged
    change (session, context) ∈ inner.2.shared.2.ghost.seals at logged
    rw [seals] at logged
    show session < inner.2.shared.2.sessions
    rw [sessions]
    exact Nat.lt_succ_of_lt (serverInv.sealsBelow session context logged)
  · intro session token found
    change inner.2.shared.2.pending session = some token at found
    show session < inner.2.shared.2.sessions ∧ sealOf inner.2.shared.2.ghost.seals session = none ∧
      ∃ input, (⟨.inl (.inr (.accept input)), some session⟩ : Entry) ∈
        ledger.transcript ++ [⟨.inl (.inr (.accept raw)), inner.1⟩] ∧
        PqxdhDeploymentCompile.identityOf codec input = some token.pending.beacon_identity_public_key ∧
        PqxdhDeploymentCompile.publicInit codec input = some (PqxdhTranscriptAd.initOf token.init)
    by_cases fresh : session = native.native.shared.2.sessions
    · rcases reply : inner.1 with _ | handle
      · rw [rejected reply] at found
        exact absurd (serverInv.pendingFresh session token found).1 (by rw [fresh]; exact lt_irrefl _)
      · obtain ⟨same, stored, storedFound, identity⟩ := returned handle reply
        rw [← same] at fresh
        subst fresh
        have init := initRead session token reply found
        rw [storedFound, Option.some.injEq] at found
        subst found
        refine ⟨by rw [sessions, same]; exact Nat.lt_succ_self _, ?_, raw,
          List.mem_append_right _ (List.mem_singleton_self _), identity, init⟩
        rw [seals, same]
        exact sealOf_none_of_below _ _ fun entry logged => serverInv.sealsBelow entry.1 entry.2 logged
    · rw [others session fresh] at found
      obtain ⟨below, sealFree, input, accept, identity, init⟩ := serverInv.pendingFresh session token found
      exact ⟨by rw [sessions]; exact Nat.lt_succ_of_lt below, by rw [seals]; exact sealFree, input,
        List.mem_append_left _ accept, identity, init⟩
  · intro session payload response built
    change _ ∈ ledger.transcript ++ [⟨.inl (.inr (.accept raw)), inner.1⟩] at built
    rcases List.mem_append.mp built with old | new
    · obtain ⟨input, init, candidate, frameBytes, digest, context, accept, initEq, written, cached, sealEq, ad⟩ :=
        serverInv.sealedTranscript session payload response old
      exact ⟨input, init, candidate, frameBytes, digest, context, List.mem_append_left _ accept, initEq, written,
        grow cached, by change sealOf inner.2.shared.2.ghost.seals session = some context; rw [seals]; exact sealEq,
        ad⟩
    · simp at new
  · rw [show (ledger.record (.inl (.inr (.accept raw))) inner.1).transcript =
      ledger.transcript ++ [⟨.inl (.inr (.accept raw)), inner.1⟩] from rfl, accepted_quiet _ _ (notFinish _)] at found
    exact found

/-- A build keeps both invariants: it seals only under a handle with a pending token, which has no seal yet, so a successful build's first-send context is the handle's first seal context, sealed under `PqxdhTranscriptAd.adOf` of the cached digest of the transcript of the token's retained Init fields (those of the accept that issued the handle) and the committed candidate's Phase 2 fields; the BLAKE2b cache only grows. -/
theorem build_step (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (serverSeed : IdentitySeed) (server : RawCtxServerRouting.Identity)
    (serverKid : Std.U64) (session : Nat) (payload : Option Pqxdh.Bytes) (ledger : Ledger)
    (native : PqxdhDeploymentNative.State KemSK)
    (serverInv : ServerInv codec server serverKid (ledger, native)) (beaconInv : BeaconInv setup codec (ledger, native))
    (answer : Option PqxdhServerRegistrationPublication.Response × PqxdhDeploymentNative.State KemSK)
    (member : answer ∈ support ((PqxdhDeploymentNative.handler setup codec checks route serverSeed
      (.inr (.build session payload))).run native)) :
    ServerInv codec server serverKid (ledger.record (.inl (.inr (.build session payload))) answer.1, answer.2) ∧
      BeaconInv setup codec (ledger.record (.inl (.inr (.build session payload))) answer.1, answer.2) := by
  have notFinish : ∀ (reply : Option PqxdhServerRegistrationPublication.Response) owner input value,
      regOfEntry ⟨.inl (.inr (.build session payload)), reply⟩ ≠ some (.finish owner input (some value)) := by
    intro reply owner input value found
    simp [regOfEntry] at found
  simp only [PqxdhDeploymentNative.handler] at member
  obtain ⟨inner, innerMember, rfl⟩ := PqxdhDeploymentEligibility.onNative_support _ native answer member
  simp only [PqxdhRegistrationSchedule.handler,
    ← PqxdhServerAuthNative.build_native setup codec checks serverSeed PqxdhRegistrationSchedule.observationScalar]
    at innerMember
  have initsSame := PqxdhDeploymentCompileInvariant.shared_inits setup serverSeed _ native.native inner innerMember
  obtain ⟨owners, reached⟩ := PqxdhDeploymentCompileInvariant.shared_footprint setup serverSeed _ native.native inner
    innerMember
  obtain ⟨_, kid, sessions, others, cleared, _, _⟩ :=
    PqxdhDeploymentCompileFootprint.build_footprint setup codec checks session payload _ _ reached
  have grow := (PqxdhServerAuthExperiment.build_step (Reader := Reader) (Response := Response) (setup := setup)
    (publicValue := PqxdhJointGapDh.challenge setup.joint setup.dh serverSeed PqxdhRegistrationSchedule.observationScalar)
    codec checks session payload _ _ reached).2.1.ctx
  obtain ⟨logged, sealsEq, empty, success⟩ := build_seals setup codec checks session payload _ _ reached
  have appended : ∀ entry ∈ logged.map (fun context => (session, context)), entry.1 = session := by
    intro entry entryMember
    obtain ⟨context, _, rfl⟩ := List.mem_map.mp entryMember
    rfl
  refine ⟨⟨?_, ?_, ?_, ?_⟩, beaconInv_frame setup codec _ _ beaconInv (fun k => by simp only [owners]) initsSame grow
    (fun k bytes entry => mem_snoc_ne entry fun same => nomatch same)
    (fun k input value entry => mem_snoc_ne entry fun same => nomatch same)
    fun c result found => ?_⟩
  · show inner.2.shared.2.server.identityKeyId = serverKid
    rw [kid]
    exact serverInv.kid
  · intro handle context member
    change (handle, context) ∈ inner.2.shared.2.ghost.seals at member
    show handle < inner.2.shared.2.sessions
    rw [sessions]
    rw [sealsEq] at member
    rcases List.mem_append.mp member with old | new
    · exact serverInv.sealsBelow handle context old
    · have same : handle = session := appended _ new
      subst same
      cases pendingFound : native.native.shared.2.pending handle with
      | none =>
          rw [empty pendingFound] at new
          cases new
      | some token => exact (serverInv.pendingFresh handle token pendingFound).1
  · intro handle token found
    change inner.2.shared.2.pending handle = some token at found
    show handle < inner.2.shared.2.sessions ∧ sealOf inner.2.shared.2.ghost.seals handle = none ∧
      ∃ input, (⟨.inl (.inr (.accept input)), some handle⟩ : Entry) ∈
        ledger.transcript ++ [⟨.inl (.inr (.build session payload)), inner.1⟩] ∧
        PqxdhDeploymentCompile.identityOf codec input = some token.pending.beacon_identity_public_key ∧
        PqxdhDeploymentCompile.publicInit codec input = some (PqxdhTranscriptAd.initOf token.init)
    by_cases same : handle = session
    · rw [same, cleared] at found
      cases found
    · rw [others handle same] at found
      obtain ⟨below, sealFree, input, accept, identityEq, initEq⟩ := serverInv.pendingFresh handle token found
      refine ⟨by rw [sessions]; exact below, ?_, input, List.mem_append_left _ accept, identityEq, initEq⟩
      rw [sealsEq,
        sealOf_append_ne _ _ _ fun entry entryMember => by rw [appended entry entryMember]; exact Ne.symm same]
      exact sealFree
  · intro handle value response built
    change _ ∈ ledger.transcript ++ [⟨.inl (.inr (.build session payload)), inner.1⟩] at built
    change ∃ (raw : Pqxdh.Bytes) (init : PqxdhEd25519EufCma.Phase1Candidate)
      (candidate : beaconcrypt_core.pqxdh.ServerRegistrationCandidate) (frameBytes : Pqxdh.Bytes)
      (digest : CtxRomAuth.CtxDigest) (context : RawCtxSourceSend.SealContext),
      (⟨.inl (.inr (.accept raw)), some handle⟩ : Entry) ∈
        ledger.transcript ++ [⟨.inl (.inr (.build session payload)), inner.1⟩] ∧
      PqxdhDeploymentCompile.publicInit codec raw = some (PqxdhTranscriptAd.initOf init) ∧
      codec.write2 ⟨candidate.key_id, candidate.ephemeral_public_key, candidate.server_identity_public_key,
        candidate.kem_ciphertext, frameBytes⟩ = some response.serialized ∧
      inner.2.shared.2.ctx ((), PqxdhTranscriptAd.transcript (PqxdhTranscriptAd.initOf init)
        (PqxdhTranscriptAd.serverResponse candidate)) = some digest ∧
      sealOf inner.2.shared.2.ghost.seals handle = some context ∧
      context.associatedData = PqxdhRefinement.absBytes (PqxdhTranscriptAd.adOf digest)
    rcases List.mem_append.mp built with old | new
    · obtain ⟨input, init, candidate, frameBytes, digest, context, accept, initEq, written, cached, sealEq, ad⟩ :=
        serverInv.sealedTranscript handle value response old
      refine ⟨input, init, candidate, frameBytes, digest, context, List.mem_append_left _ accept, initEq, written,
        grow cached, ?_, ad⟩
      rw [sealsEq]
      exact sealOf_append_of_some _ _ _ _ sealEq
    · rcases reply : inner.1 with _ | built'
      · rw [reply] at new
        simp at new
      · rw [reply] at new
        rw [List.mem_singleton] at new
        have query := congrArg PqxdhDeploymentInterface.Entry.query new
        simp only [Sum.inl.injEq, Sum.inr.injEq, PqxdhDeploymentInterface.Command.build.injEq] at query
        obtain ⟨same, _⟩ := query
        subst same
        have answered : response = built' := by
          cases new
          rfl
        subst answered
        obtain ⟨token, candidate, frameBytes, digest, context, pendingFound, loggedEq, written, cached, ad⟩ :=
          success response reply
        obtain ⟨_, sealFree, input, accept, _, initEq⟩ := serverInv.pendingFresh _ token pendingFound
        refine ⟨input, token.init, candidate, frameBytes, digest, context, List.mem_append_left _ accept, initEq,
          written, cached, ?_, ad⟩
        rw [sealsEq, loggedEq]
        exact sealOf_append_none _ _ _ [] sealFree
  · rw [show (ledger.record (.inl (.inr (.build session payload))) inner.1).transcript =
      ledger.transcript ++ [⟨.inl (.inr (.build session payload)), inner.1⟩] from rfl,
      accepted_quiet _ _ (notFinish _)] at found
    exact found

/-- A secrecy command keeps both invariants: it issues only coins and sends and appends its own entry. -/
theorem secrecy_step (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (serverSeed : IdentitySeed) (bounds : FreshBounds)
    (server : RawCtxServerRouting.Identity) (serverKid : Std.U64) (secrecy : PqxdhDeploymentInterface.Secrecy)
    (ledger : Ledger) (native : PqxdhDeploymentNative.State KemSK)
    (serverInv : ServerInv codec server serverKid (ledger, native)) (beaconInv : BeaconInv setup codec (ledger, native))
    (result : Option RawCtxSourceSend.Encrypted × PqxdhDeploymentSecrecy.State KemSK)
    (supported : result ∈ support ((PqxdhDeploymentSecrecy.handler setup codec checks route serverSeed bounds
      (.inr secrecy)).run (ledger, native))) :
    ServerInv codec server serverKid result.2 ∧ BeaconInv setup codec result.2 := by
  rw [PqxdhDeploymentEligibility.handler_run, support_map] at supported
  obtain ⟨reached, reachedMember, rfl⟩ := supported
  have value : reached.1 ∈ support ((PqxdhDeploymentSecrecy.ledgerImpl setup.source.crypto codec setup.serverKeyId
      bounds (.inr secrecy)).run ledger) := by
    apply OracleComp.support_simulateQ_run'_subset (PqxdhDeploymentNative.handler setup codec checks route serverSeed)
      _ native
    rw [StateT.run'_eq, support_map]
    exact ⟨reached, reachedMember, rfl⟩
  have recorded := PqxdhDeploymentEligibility.ledger_secrecy setup.source.crypto codec setup.serverKeyId bounds secrecy
    ledger reached.1 value
  have kept := coinSend_kept setup codec checks route serverSeed _
    (PqxdhDeploymentSecrecy.secrecy_frame setup.source.crypto codec setup.serverKeyId bounds secrecy ledger) native
    reached reachedMember
  have notFinish : ∀ owner raw payload,
      regOfEntry ⟨.inr secrecy, reached.1.1⟩ ≠ some (.finish owner raw (some payload)) := by
    intro owner raw payload found
    simp [regOfEntry] at found
  exact ⟨serverInv_frame codec server serverKid (ledger, native) (reached.1.2, reached.2) serverInv kept.1 _ recorded
    trivial, beaconInv_frame setup codec (ledger, native) (reached.1.2, reached.2) beaconInv kept.2.1 kept.2.2
      kept.1.ctx
      (fun k bytes entry => by
        change _ ∈ reached.1.2.transcript at entry
        rw [recorded] at entry
        exact mem_snoc_ne entry fun same => nomatch same)
      (fun k input value entry => by
        change _ ∈ reached.1.2.transcript at entry
        rw [recorded] at entry
        exact mem_snoc_ne entry fun same => nomatch same)
      fun c result found => by
        change accepted c (regsOf reached.1.2.transcript) = some result at found
        rw [recorded, accepted_quiet _ _ notFinish] at found
        exact found⟩

/-- Every query of the complete experiment keeps both invariants. -/
theorem inv_step (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (serverSeed : IdentitySeed) (bounds : FreshBounds)
    (server : RawCtxServerRouting.Identity) (serverKid : Std.U64) (query : PqxdhDeploymentInterface.Query)
    (state : PqxdhDeploymentSecrecy.State KemSK)
    (serverInv : ServerInv codec server serverKid state) (beaconInv : BeaconInv setup codec state)
    (result : FullSpec.Range query × PqxdhDeploymentSecrecy.State KemSK)
    (supported : result ∈ support ((PqxdhDeploymentSecrecy.handler setup codec checks route serverSeed bounds query).run
      state)) :
    ServerInv codec server serverKid result.2 ∧ BeaconInv setup codec result.2 := by
  rcases state with ⟨ledger, native⟩
  rcases query with command | secrecy
  · obtain ⟨answer, answerMember, rfl⟩ := PqxdhDeploymentHeadlineCtTrace.forward_support setup codec checks route
      serverSeed bounds command ledger native result supported
    rcases command with coin | command
    · exact quiet_step setup codec checks route serverSeed server serverKid (.inl coin) trivial ledger native serverInv
        beaconInv answer answerMember
    · cases command with
      | create pin keyId =>
          exact create_step setup codec checks route serverSeed server serverKid pin keyId ledger native
            serverInv beaconInv answer answerMember
      | bundle index =>
          exact bundle_step setup codec checks route serverSeed server serverKid index ledger native
            serverInv beaconInv answer answerMember
      | accept raw =>
          exact accept_step setup codec checks route serverSeed server serverKid raw ledger native serverInv
            beaconInv answer answerMember
      | build session payload =>
          exact build_step setup codec checks route serverSeed server serverKid session payload
            ledger native serverInv beaconInv answer answerMember
      | finish index raw =>
          exact finish_step setup codec checks route serverSeed server serverKid index raw ledger
            native serverInv beaconInv answer answerMember
      | hmac key message =>
          exact quiet_step setup codec checks route serverSeed server serverKid
            (.inr (.hmac key message)) trivial ledger native serverInv beaconInv answer answerMember
      | hash bytes =>
          exact quiet_step setup codec checks route serverSeed server serverKid (.inr (.hash bytes)) trivial
            ledger native serverInv beaconInv answer answerMember
      | serverSend kid plaintext =>
          exact quiet_step setup codec checks route serverSeed server serverKid
            (.inr (.serverSend kid plaintext)) trivial ledger native serverInv beaconInv answer answerMember
      | serverRaw raw =>
          exact quiet_step setup codec checks route serverSeed server serverKid (.inr (.serverRaw raw))
            trivial ledger native serverInv beaconInv answer answerMember
      | beaconSend index plaintext =>
          exact quiet_step setup codec checks route serverSeed server serverKid
            (.inr (.beaconSend index plaintext)) trivial ledger native serverInv beaconInv answer answerMember
      | beaconRaw index raw =>
          exact quiet_step setup codec checks route serverSeed server serverKid
            (.inr (.beaconRaw index raw)) trivial ledger native serverInv beaconInv answer answerMember
  · exact secrecy_step setup codec checks route serverSeed bounds server serverKid secrecy ledger native serverInv
      beaconInv result supported

/-- Both invariants hold at the start of the experiment: no seal, no pending token, no owner, no retained bundle, empty transcript. -/
theorem inv_initial (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (created : PqxdhLiveServerConstruction.Created Unit) (server : RawCtxServerRouting.Identity) :
    ServerInv codec server (PqxdhDeploymentNative.initial (KemSK := KemSK) created).native.shared.2.server.identityKeyId
        (Ledger.empty, PqxdhDeploymentNative.initial (KemSK := KemSK) created) ∧
      BeaconInv setup codec (Ledger.empty, PqxdhDeploymentNative.initial (KemSK := KemSK) created) := by
  refine ⟨⟨rfl, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · intro session context member
    simp [PqxdhDeploymentNative.initial, PqxdhRegistrationSchedule.initial, Ghost.empty] at member
  · intro session token found
    simp [PqxdhDeploymentNative.initial, PqxdhRegistrationSchedule.initial] at found
  · intro session payload response member
    simp [Ledger.empty] at member
  · intro k owner control prekey oneTime kem found
    simp [PqxdhDeploymentNative.initial, PqxdhRegistrationSchedule.initial] at found
  · intro k bytes member
    simp [Ledger.empty] at member
  · intro k init found
    simp [PqxdhDeploymentNative.initial, PqxdhRegistrationSchedule.initial] at found
  · intro k owner found
    simp [PqxdhDeploymentNative.initial, PqxdhRegistrationSchedule.initial] at found
  · intro k raw reply member
    simp [Ledger.empty] at member
  · intro k owner pin found
    simp [PqxdhDeploymentNative.initial, PqxdhRegistrationSchedule.initial] at found
  · intro c before raw found
    simp [Ledger.empty, regsOf, accepted, PqxdhDeploymentServerAuthEvent.acceptedFrom] at found

/-- On every outcome of the experiment with a constructed Server, the final Server identity is the pin of the protected binding, and the final state satisfies both invariants for that identity and the compiled-in Server key ID (`PqxdhDeploymentEligibility.experiment_step`, `inv_step`; the generated Server's identity and key ID from `PqxdhLiveServerConstruction.construct_origin`). -/
theorem inv_game (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (ensureInit : StateT A ProbComp Bool) (identityIndex : Nat)
    (bounds : FreshBounds) (mode : Mode) (adversary : OracleComp (ModeSpec mode) X) (runtime : A)
    (outcome : Option (PqxdhRegistrationJointServerBirth.ClientCreated Unit × X × PqxdhDeploymentSecrecy.State KemSK) ×
      A)
    (supported : outcome ∈ support ((PqxdhDeploymentSecrecy.game setup codec checks route ensureInit identityIndex
      bounds mode adversary).run runtime))
    (created : PqxdhRegistrationJointServerBirth.ClientCreated Unit) (output : X)
    (final : PqxdhDeploymentSecrecy.State KemSK) (reached : outcome.1 = some (created, output, final)) :
    final.2.native.shared.2.server.server.identity = (PqxdhDeploymentServerAuthEvent.protectedBinding setup created).1 ∧
      ServerInv codec (PqxdhDeploymentServerAuthEvent.protectedBinding setup created).1 setup.serverKeyId final ∧
      BeaconInv setup codec final := by
  simp only [PqxdhDeploymentSecrecy.game, StateT.run, mem_support_bind_iff] at supported
  obtain ⟨born, bornMember, supported⟩ := supported
  rcases born with ⟨_ | constructed, after⟩
  · simp only [support_pure, Set.mem_singleton_iff] at supported
    subst supported
    cases reached
  · simp only [support_map, Set.mem_image] at supported
    obtain ⟨executed, executedMember, rfl⟩ := supported
    cases reached
    have invariant := OracleComp.simulateQ_run_preserves_inv_of_query
      (PqxdhDeploymentSecrecy.handler setup codec checks route constructed.seed bounds)
      (fun state => PqxdhDeploymentEligibility.Agree setup codec
          (PqxdhDeploymentNative.initial (KemSK := KemSK) constructed).native.shared.2.server.server.identity
          state.1.transcript state.2.native ∧
        ServerInv codec
          (PqxdhDeploymentNative.initial (KemSK := KemSK) constructed).native.shared.2.server.server.identity
          (PqxdhDeploymentNative.initial (KemSK := KemSK) constructed).native.shared.2.server.identityKeyId state ∧
        BeaconInv setup codec state)
      (fun query state holds result member => ⟨PqxdhDeploymentEligibility.experiment_step setup codec checks route
        constructed.seed bounds _ query state holds.1 result member,
        inv_step setup codec checks route constructed.seed bounds _ _ query state holds.2.1 holds.2.2 result member⟩)
      (asModeO mode adversary) (PqxdhDeploymentSecrecy.Ledger.empty, PqxdhDeploymentNative.initial constructed)
      ⟨PqxdhDeploymentEligibility.agree_initial setup codec constructed, inv_initial setup codec constructed _⟩ _
      executedMember
    obtain ⟨seed, rfl, _⟩ := PqxdhLiveServerConstruction.construct_origin setup.joint ensureInit identityIndex
      setup.serverKeyId none runtime after constructed bornMember
    exact ⟨invariant.1.identity, invariant.2.1, invariant.2.2⟩

end Steps

end BeaconcryptCore.Computational.PqxdhDeploymentSessionFieldsInvariant

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentSessionFieldsInvariant.sealOf_append_of_some' depends on axioms: [propext,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentSessionFieldsInvariant.sealOf_append_of_some

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentSessionFieldsInvariant.sealOf_append_ne' depends on axioms: [propext,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentSessionFieldsInvariant.sealOf_append_ne

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentSessionFieldsInvariant.sealOf_append_none' depends on axioms: [propext,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentSessionFieldsInvariant.sealOf_append_none

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentSessionFieldsInvariant.sealOf_none_of_below' depends on axioms: [propext,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentSessionFieldsInvariant.sealOf_none_of_below

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentSessionFieldsInvariant.establishedAd_some' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentSessionFieldsInvariant.establishedAd_some

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentSessionFieldsInvariant.kept_refl' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentSessionFieldsInvariant.kept_refl

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentSessionFieldsInvariant.kept_trans' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentSessionFieldsInvariant.kept_trans

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentSessionFieldsInvariant.accepted_quiet' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentSessionFieldsInvariant.accepted_quiet

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentSessionFieldsInvariant.accepted_finish' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentSessionFieldsInvariant.accepted_finish

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentSessionFieldsInvariant.serverInv_frame' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentSessionFieldsInvariant.serverInv_frame

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentSessionFieldsInvariant.kept_back' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentSessionFieldsInvariant.kept_back

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentSessionFieldsInvariant.kept_forth' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentSessionFieldsInvariant.kept_forth

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentSessionFieldsInvariant.beaconInv_frame' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentSessionFieldsInvariant.beaconInv_frame

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentSessionFieldsInvariant.beaconImpl_key' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentSessionFieldsInvariant.beaconImpl_key

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentSessionFieldsInvariant.beaconStep_kept' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentSessionFieldsInvariant.beaconStep_kept

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentSessionFieldsInvariant.serverStep_kept' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentSessionFieldsInvariant.serverStep_kept

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentSessionFieldsInvariant.hmac_seals' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentSessionFieldsInvariant.hmac_seals

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentSessionFieldsInvariant.hash_seals' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentSessionFieldsInvariant.hash_seals

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentSessionFieldsInvariant.native_quiet' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentSessionFieldsInvariant.native_quiet

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentSessionFieldsInvariant.coinSend_kept' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentSessionFieldsInvariant.coinSend_kept

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentSessionFieldsInvariant.accept_seals' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentSessionFieldsInvariant.accept_seals

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentSessionFieldsInvariant.settle_some' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentSessionFieldsInvariant.settle_some

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentSessionFieldsInvariant.build_seals' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentSessionFieldsInvariant.build_seals

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentSessionFieldsInvariant.beaconInv_append' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentSessionFieldsInvariant.beaconInv_append

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentSessionFieldsInvariant.beaconInv_set' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentSessionFieldsInvariant.beaconInv_set

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentSessionFieldsInvariant.quiet_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentSessionFieldsInvariant.quiet_step

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentSessionFieldsInvariant.create_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentSessionFieldsInvariant.create_step

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentSessionFieldsInvariant.bundle_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentSessionFieldsInvariant.bundle_step

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentSessionFieldsInvariant.finish_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentSessionFieldsInvariant.finish_step

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentSessionFieldsInvariant.accept_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentSessionFieldsInvariant.accept_step

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentSessionFieldsInvariant.build_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentSessionFieldsInvariant.build_step

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentSessionFieldsInvariant.secrecy_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentSessionFieldsInvariant.secrecy_step

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentSessionFieldsInvariant.inv_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentSessionFieldsInvariant.inv_step

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentSessionFieldsInvariant.inv_initial' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentSessionFieldsInvariant.inv_initial

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentSessionFieldsInvariant.inv_game' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentSessionFieldsInvariant.inv_game

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentSessionFieldsInvariant.serverStep_grows' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentSessionFieldsInvariant.serverStep_grows

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentSessionFieldsInvariant.beaconStep_grows' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentSessionFieldsInvariant.beaconStep_grows

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentSessionFieldsInvariant.mem_snoc_ne' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentSessionFieldsInvariant.mem_snoc_ne

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentSessionFieldsInvariant.bundle_entry' does not depend on any axioms -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentSessionFieldsInvariant.bundle_entry

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentSessionFieldsInvariant.finish_entry' does not depend on any axioms -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentSessionFieldsInvariant.finish_entry

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentSessionFieldsInvariant.finish_absent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentSessionFieldsInvariant.finish_absent

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentSessionFieldsInvariant.bundle_absent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentSessionFieldsInvariant.bundle_absent
