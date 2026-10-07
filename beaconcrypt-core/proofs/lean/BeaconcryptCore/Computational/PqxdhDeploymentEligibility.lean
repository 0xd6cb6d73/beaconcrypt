-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhDeploymentCompileSecrecy

/-! Publicity of the transcript functions of the common deployment experiment (CE-5, first part). Along every run of the complete experiment, in either mode, the public transcript and the native state stay related by `Agree`: the transcript summary counts exactly the native owners, the public phase of every owner handle is the class of its native lifecycle phase (absent, Fresh or Fresh with coins, InitSent, Established, Aborted), and every created binding is the owner's pinned Server identity and pinned key ID. Every successful bundle in the transcript is the Phase 1 writer output of the candidate the owner signed honestly with its own identity key and its own KEM public key, and every successful build response is the Phase 2 writer output of fields carrying the Server's identity, which never changes. Hence `phase`, `owner` and `NoBundleFailure` are public and mean what the native state says, and the premises of the key-match lemmas hold on every run. No codec law and no security assumption is used here. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhDeploymentEligibility
open PqxdhServerAuthExperiment PqxdhServerAuthNative PqxdhJointIdentity PqxdhJointGapDh
open PqxdhDeploymentInterface (Spec Command FullSpec ModeSpec Mode Entry FreshBounds parsePin asModeO)
open PqxdhDeploymentTranscript (PublicPhase summarize phase)
open PqxdhDeploymentSecrecy (Ledger ledgerImpl)
open PqxdhBeaconPhase2Preparation (Word32)
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response A X : Type}

/-- The public phase class of a native lifecycle phase. -/
def phaseClass {D K Kernel : Type} : RawCtxBeaconLifecycle.Phase D K Kernel → PublicPhase
  | .fresh _ _ _ => .fresh
  | .freshWithCoins _ _ _ _ => .fresh
  | .initSent _ _ _ _ => .initSent
  | .established _ _ _ => .established
  | .aborted _ => .aborted

/-- The public phase class of an optional native owner. -/
def nativePhase (owner : Option (PqxdhRegistrationSchedule.Owner KemSK)) : PublicPhase :=
  match owner with
  | none => .absent
  | some owner => phaseClass owner.beacon.phase

/-- The Server key ID an owner is pinned to, in every phase. -/
def pinnedKeyId {D K Kernel : Type} : RawCtxBeaconLifecycle.Phase D K Kernel → Std.U64
  | .fresh control _ _ => control.expected_server_binding.identity_key_id
  | .freshWithCoins control _ _ _ => control.expected_server_binding.identity_key_id
  | .initSent control _ _ _ => control.expected_server_binding.identity_key_id
  | .established control _ _ => control.server_binding.identity_key_id
  | .aborted control => control.server_key_id

/-- The KEM public key an owner still holds, before finish. -/
def kemPublic {D Kernel : Type} {K : Type} :
    RawCtxBeaconLifecycle.Phase D (PqxdhKemIndCca.MlKem768PublicKey × K) Kernel → Option PqxdhKemIndCca.MlKem768PublicKey
  | .fresh _ _ kem => some kem.1
  | .freshWithCoins _ _ _ kem => some kem.1
  | .initSent _ _ _ kem => some kem.1
  | .established _ _ _ => none
  | .aborted _ => none

/-- The part of an owner that the public facts below depend on: phase class, pinned Server identity and key ID, identity seed and remaining KEM public key. -/
def view (owner : PqxdhRegistrationSchedule.Owner KemSK) :
    PublicPhase × Word32 × Std.U64 × IdentitySeed × Option PqxdhKemIndCca.MlKem768PublicKey :=
  (phaseClass owner.beacon.phase, owner.beacon.serverIdentity, pinnedKeyId owner.beacon.phase, owner.beacon.identity,
    kemPublic owner.beacon.phase)

/-- Two native states have the same Server identity, the same number of owners and the same view of every owner. -/
def Alike (before after : PqxdhRegistrationSchedule.State KemSK) : Prop :=
  after.shared.2.server.server.identity = before.shared.2.server.server.identity ∧
    after.owners.length = before.owners.length ∧
      ∀ index : Nat, (after.owners[index]?).map (view (KemSK := KemSK)) = (before.owners[index]?).map view

/-- A successful build response in the transcript is the Phase 2 writer output of fields carrying the Server identity. -/
def BuildShaped (codec : Codec Reader Response) (server : RawCtxServerRouting.Identity) (entry : Entry) : Prop :=
  match entry with
  | ⟨.inl (.inr (.build _ _)), some response⟩ =>
      ∃ fields, codec.write2 fields = some response.serialized ∧ fields.identity = server
  | _ => True

/-- A successful bundle in the transcript is the Phase 1 writer output of the candidate the owner signed with its own identity key and the KEM public key it holds until finish. -/
def BundleShaped (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (native : PqxdhRegistrationSchedule.State KemSK) (entry : Entry) : Prop :=
  match entry with
  | ⟨.inl (.inr (.bundle index)), some bytes⟩ =>
      ∃ (owner : PqxdhRegistrationSchedule.Owner KemSK) (keys : PqxdhEd25519EufCma.Phase1KeyTuple)
        (preSignature oneSignature pqSignature : PqxdhEd25519EufCma.Ed25519Signature),
        native.owners[index]? = some owner ∧
        codec.write1 (PqxdhJointPhase1SourceWriter.candidate (setup.joint.publicKeys owner.beacon.identity).ed25519 keys
          preSignature oneSignature pqSignature) = some bytes ∧
        (kemPublic owner.beacon.phase = none ∨ kemPublic owner.beacon.phase = some keys.pqKey)
  | _ => True

/-- The run invariant relating the public transcript to the native state, for a Server with identity `server`. -/
structure Agree (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (server : RawCtxServerRouting.Identity)
    (transcript : List Entry) (native : PqxdhRegistrationSchedule.State KemSK) : Prop where
  identity : native.shared.2.server.server.identity = server
  count : (summarize transcript).owners.length = native.owners.length
  phases : ∀ index : Nat, phase transcript index = nativePhase native.owners[index]?
  bindings : ∀ (index : Nat) pin keyId, (summarize transcript).owners[index]? = some (pin, keyId) →
    ∃ owner : PqxdhRegistrationSchedule.Owner KemSK, native.owners[index]? = some owner ∧ owner.beacon.serverIdentity = pin ∧
      pinnedKeyId owner.beacon.phase = keyId
  builds : ∀ entry ∈ transcript, BuildShaped codec server entry
  bundles : ∀ entry ∈ transcript, BundleShaped setup codec native entry

/-- The public phase class depends only on the view. -/
theorem nativePhase_view (first second : Option (PqxdhRegistrationSchedule.Owner KemSK))
    (same : first.map (view (KemSK := KemSK)) = second.map view) : nativePhase first = nativePhase second := by
  cases first <;> cases second <;> simp_all [view, nativePhase]

/-- Bundle shapes depend only on the views of the owners. -/
theorem bundleShaped_alike (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (before after : PqxdhRegistrationSchedule.State KemSK) (alike : Alike before after) (entry : Entry)
    (shaped : BundleShaped setup codec before entry) : BundleShaped setup codec after entry := by
  rcases entry with ⟨(coin | command) | secrecy, reply⟩
  · trivial
  · cases command with
    | bundle index =>
        cases reply with
        | none => trivial
        | some bytes =>
            obtain ⟨owner, keys, s1, s2, s3, found, written, kem⟩ := shaped
            have mapped := alike.2.2 index
            rw [found] at mapped
            cases next : after.owners[index]? with
            | none => rw [next] at mapped; cases mapped
            | some other =>
                rw [next] at mapped
                simp only [Option.map_some, Option.some.injEq, view, Prod.mk.injEq] at mapped
                obtain ⟨_, _, _, seed, kemEq⟩ := mapped
                exact ⟨other, keys, s1, s2, s3, next, by rw [seed]; exact written, by rw [kemEq]; exact kem⟩
    | _ => trivial
  · trivial

/-- The invariant survives a native step that keeps every view and the Server identity, with the transcript extended by an entry that changes no summary and is not a successful build or bundle. -/
theorem agree_alike (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (server : RawCtxServerRouting.Identity)
    (transcript : List Entry) (before after : PqxdhRegistrationSchedule.State KemSK)
    (agree : Agree setup codec server transcript before) (alike : Alike before after) :
    Agree setup codec server transcript after := by
  obtain ⟨identity, length, views⟩ := alike
  refine ⟨by rw [identity]; exact agree.identity, by rw [length]; exact agree.count, fun index => ?_, ?_, agree.builds,
    fun entry member => bundleShaped_alike setup codec before after ⟨identity, length, views⟩ entry
      (agree.bundles entry member)⟩
  · rw [agree.phases index]
    exact nativePhase_view _ _ (views index).symm
  · intro index pin keyId found
    obtain ⟨owner, ownerFound, pinEq, keyEq⟩ := agree.bindings index pin keyId found
    have mapped := views index
    rw [ownerFound] at mapped
    cases next : after.owners[index]? with
    | none => rw [next] at mapped; cases mapped
    | some other =>
        rw [next] at mapped
        simp only [Option.map_some, Option.some.injEq, view, Prod.mk.injEq] at mapped
        obtain ⟨_, server', key', _, _⟩ := mapped
        exact ⟨other, rfl, by rw [server']; exact pinEq, by rw [key']; exact keyEq⟩

/-- Alike is reflexive. -/
theorem alike_refl (native : PqxdhRegistrationSchedule.State KemSK) : Alike native native :=
  ⟨rfl, rfl, fun _ => rfl⟩

/-- Alike is transitive. -/
theorem alike_trans (first second third : PqxdhRegistrationSchedule.State KemSK) (left : Alike first second)
    (right : Alike second third) : Alike first third :=
  ⟨right.1.trans left.1, right.2.1.trans left.2.1, fun index => (right.2.2 index).trans (left.2.2 index)⟩

/-- Every result of a logged record program run on the native state carries a value of the record program and changes only the BLAKE2b cache. -/
theorem record_value {Result : Type} (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (work : OracleComp RawCtxMixedOwner.NativeSpec Result) (native : PqxdhRegistrationSchedule.State KemSK)
    (result : (Result × List PqxdhDeploymentNative.Frame) × PqxdhRegistrationSchedule.State KemSK)
    (supported : result ∈ support ((PqxdhDeploymentNative.record setup codec (PqxdhDeploymentNative.logged work)).run
      native)) :
    result.1.1 ∈ support work ∧ ∃ cache, result.2 = PqxdhDeploymentRecordCache.setCtx native cache := by
  obtain ⟨cache, cacheEq⟩ := PqxdhDeploymentNative.record_support setup codec _ native result supported
  refine ⟨?_, cache, cacheEq⟩
  rw [PqxdhDeploymentNative.record_run, support_map] at supported
  obtain ⟨inner, member, rfl⟩ := supported
  have logged : inner.1 ∈ support (PqxdhDeploymentNative.logged work) := by
    have subset := OracleComp.support_simulateQ_run'_subset (PqxdhDeploymentNative.primitives setup codec)
      (PqxdhDeploymentNative.logged work) ((), native.shared.2.ctx)
    apply subset
    rw [StateT.run'_eq, support_map]
    exact ⟨inner, member, rfl⟩
  have forget := PqxdhDeploymentNative.logged_forget work []
  rw [← forget, support_map]
  exact ⟨inner.1, logged, rfl⟩

/-- A Server record command never changes the Server identity. -/
theorem serverImpl_identity (senderId : Unit → Std.U64) (route : RawCtxServerRouting.SenderDecoder)
    (decode : RawCtxReceive.FrameDecoder) (query : RawCtxServerMixed.SourceSpec.Domain)
    (state : RawCtxServerRouting.State Unit Unit)
    (result : RawCtxServerMixed.SourceSpec.Range query × RawCtxServerRouting.State Unit Unit)
    (supported : result ∈ support ((RawCtxServerMixed.serverImpl senderId route decode query).run state)) :
    result.2.server.identity = state.server.identity := by
  cases target : PqxdhDeploymentCompile.serverTarget route query with
  | none =>
      rw [PqxdhDeploymentCompileRecords.serverImpl_absent senderId route decode query state
        (fun kid found => by simp only [target, reduceCtorEq] at found), support_pure,
        Set.mem_singleton_iff] at supported
      subst supported
      rfl
  | some kid =>
      cases found : state.server.peers kid with
      | none =>
          rw [PqxdhDeploymentCompileRecords.serverImpl_absent senderId route decode query state
            (fun other routed => by simp only [target, Option.some.injEq] at routed; subst routed; exact found),
            support_pure, Set.mem_singleton_iff] at supported
          subst supported
          rfl
      | some peer =>
          rw [PqxdhDeploymentCompileRecords.serverImpl_peer senderId route decode query state kid peer target found,
            support_map] at supported
          obtain ⟨_, _, rfl⟩ := supported
          rfl

/-- A Beacon record command keeps the owner's view: an established owner stays established with the same control, and every other owner is unchanged. -/
theorem beaconImpl_view (decode : RawCtxReceive.FrameDecoder) (query : RawCtxMixedOwner.SourceSpec.Domain)
    (state : PqxdhRegistrationSchedule.Owner KemSK)
    (result : RawCtxMixedOwner.SourceSpec.Range query × PqxdhRegistrationSchedule.Owner KemSK)
    (supported : result ∈ support ((RawCtxBeaconLifecycle.beaconImpl decode query).run state)) :
    view result.2 = view state := by
  by_cases active : RawCtxBeaconLifecycle.Established state.beacon.phase
  · cases phase : state.beacon.phase with
    | established control associatedData kernel =>
        rw [PqxdhDeploymentCompileRecords.beaconImpl_established decode query state control associatedData kernel phase,
          support_map] at supported
        obtain ⟨_, _, rfl⟩ := supported
        simp [view, phase, phaseClass, pinnedKeyId, kemPublic]
    | _ => simp [phase, RawCtxBeaconLifecycle.Established] at active
  · rw [RawCtxBeaconLifecycle.inactive decode query state active, support_pure, Set.mem_singleton_iff] at supported
    subst supported
    rcases query with plaintext | raw <;> rfl

/-- A native Server record command keeps every owner, the Server identity and therefore every view. -/
theorem serverStep_alike (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (query : RawCtxServerMixed.SourceSpec.Domain)
    (state : PqxdhDeploymentNative.State KemSK)
    (result : RawCtxServerMixed.SourceSpec.Range query × PqxdhDeploymentNative.State KemSK)
    (supported : result ∈ support ((PqxdhDeploymentNative.serverStep setup codec route query).run state)) :
    Alike state.native result.2.native := by
  have owners := (PqxdhDeploymentNative.serverStep_fields setup codec route query state result supported).1
  simp only [PqxdhDeploymentNative.serverStep, StateT.run, mem_support_bind_iff, support_pure,
    Set.mem_singleton_iff] at supported
  obtain ⟨inner, member, rfl⟩ := supported
  obtain ⟨value, cache, cacheEq⟩ := record_value setup codec _ state.native inner member
  have identity := serverImpl_identity _ route codec.frameRead query _ _ value
  refine ⟨?_, by rw [owners], fun index => by rw [owners]⟩
  simp only [PqxdhDeploymentNative.produce, PqxdhDeploymentNative.withServer]
  exact identity

/-- A native Beacon record command keeps the Server identity, the number of owners and every view. -/
theorem beaconStep_alike (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (index : Nat)
    (query : RawCtxMixedOwner.SourceSpec.Domain) (state : PqxdhDeploymentNative.State KemSK)
    (result : RawCtxMixedOwner.SourceSpec.Range query × PqxdhDeploymentNative.State KemSK)
    (supported : result ∈ support ((PqxdhDeploymentNative.beaconStep setup codec index query).run state)) :
    Alike state.native result.2.native := by
  unfold PqxdhDeploymentNative.beaconStep at supported
  cases found : state.native.owners[index]? with
  | none =>
      simp only [found, StateT.run, support_pure, Set.mem_singleton_iff] at supported
      subst supported
      exact alike_refl _
  | some owner =>
      simp only [found, StateT.run, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at supported
      obtain ⟨inner, member, rfl⟩ := supported
      obtain ⟨value, cache, cacheEq⟩ := record_value setup codec _ state.native inner member
      have kept := beaconImpl_view codec.frameRead query ⟨owner.beacon, state.ownerRaw index⟩ _ value
      refine ⟨by simp only [PqxdhDeploymentNative.produce, cacheEq]; rfl,
        by simp only [PqxdhDeploymentNative.produce, cacheEq, List.length_set]; rfl, fun position => ?_⟩
      simp only [PqxdhDeploymentNative.produce, cacheEq]
      by_cases same : position = index
      · subst same
        have bound : position < state.native.owners.length := (List.getElem?_eq_some_iff.mp found).1
        simp only [PqxdhDeploymentRecordCache.setCtx, List.getElem?_set_self bound, found, Option.map_some]
        exact congrArg some kept
      · simp only [PqxdhDeploymentRecordCache.setCtx, List.getElem?_set_ne (Ne.symm same)]

/-- A typed create appends one Fresh owner pinned to the given binding and returns its handle, the previous number of owners; nothing else changes. -/
theorem create_support (setup : Setup baseSpec KemSK) (pin : Word32) (keyId : Std.U64)
    (native : PqxdhRegistrationSchedule.State KemSK) (result : Nat × PqxdhRegistrationSchedule.State KemSK)
    (supported : result ∈ support ((PqxdhRegistrationSchedule.create setup pin keyId).run native)) :
    ∃ seed prekey keys, result = (native.owners.length, { native with
      owners := native.owners ++ [⟨⟨seed, keyId, pin, .fresh ⟨⟨pin, keyId⟩⟩ prekey keys⟩, 0⟩] }) := by
  simp only [PqxdhRegistrationSchedule.create, StateT.run_bind, StateT.run_lift, StateT.run_get, StateT.run_set,
    StateT.run_pure, bind_assoc, pure_bind, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at supported
  obtain ⟨seed, _, prekey, _, keys, _, rfl⟩ := supported
  exact ⟨seed, prekey, keys, rfl⟩

/-- A published bundle came from a Fresh owner (with or without retained coins), installs InitSent with the same expected binding and KEM pair, and is the Phase 1 writer output of the candidate signed with the owner's own identity key over its prekey, one-time key and KEM public key; a rejected bundle keeps the owner. -/
theorem bundle_candidate (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (index : Nat)
    (owner : PqxdhRegistrationSchedule.Owner KemSK)
    (result : Option Pqxdh.Bytes × PqxdhRegistrationSchedule.Owner KemSK)
    (supported : result ∈ support (simulateQ (PqxdhRegistrationSchedule.bundleCallbacks setup codec owner.beacon.identity)
      (PqxdhLivePhase1Bundle.bundle (PqxdhRegistrationSchedule.projection setup index) owner))) :
    (result.1 = none → result.2 = owner) ∧
      (∀ bytes, result.1 = some bytes → ∃ fresh prekey oneTime kem preSignature oneSignature pqSignature,
        (owner.beacon.phase = .fresh fresh prekey kem ∨ owner.beacon.phase = .freshWithCoins fresh prekey oneTime kem) ∧
        result.2 = { owner with beacon := { owner.beacon with phase := (.initSent
          ⟨fresh.expected_server_binding, PqxdhLivePhase1Bundle.identityArray
            (setup.joint.publicKeys owner.beacon.identity).ed25519⟩ prekey oneTime kem) } } ∧
        codec.write1 (PqxdhJointPhase1SourceWriter.candidate (setup.joint.publicKeys owner.beacon.identity).ed25519
          ⟨setup.dh.publicKey prekey, setup.dh.publicKey oneTime, kem.1⟩ preSignature oneSignature pqSignature) =
          some bytes) := by
  unfold PqxdhLivePhase1Bundle.bundle at supported
  cases phase : owner.beacon.phase with
  | fresh fresh prekey kem =>
      simp only [phase, simulateQ_bind, simulateQ_spec_query, mem_support_bind_iff] at supported
      obtain ⟨generated, gen, rest⟩ := supported
      simp only [PqxdhRegistrationSchedule.bundleCallbacks, support_map, Set.mem_image] at gen
      obtain ⟨oneTime, _, rfl⟩ := gen
      simp only [PqxdhLivePhase1Bundle.afterGenerated, PqxdhBeaconPhase1Publication.prepare, phase, Option.map_some,
        simulateQ_bind, PqxdhDeploymentCompileFootprint.signing_run, pure_bind,
        PqxdhDeploymentCompileFootprint.writing_run] at rest
      rw [support_pure, Set.mem_singleton_iff] at rest
      subst rest
      split
      · exact ⟨fun _ => rfl, fun bytes found => by simp at found⟩
      · rename_i bytes written
        refine ⟨fun found => by simp at found, fun other found => ?_⟩
        simp only [Option.some.injEq] at found
        subst found
        exact ⟨fresh, prekey, oneTime, kem, _, _, _, Or.inl rfl, rfl, written⟩
  | freshWithCoins fresh prekey oneTime kem =>
      simp only [phase, PqxdhLivePhase1Bundle.afterGenerated, PqxdhBeaconPhase1Publication.prepare,
        simulateQ_bind, PqxdhDeploymentCompileFootprint.signing_run, pure_bind,
        PqxdhDeploymentCompileFootprint.writing_run] at supported
      rw [support_pure, Set.mem_singleton_iff] at supported
      subst supported
      split
      · exact ⟨fun _ => rfl, fun bytes found => by simp at found⟩
      · rename_i bytes written
        refine ⟨fun found => by simp at found, fun other found => ?_⟩
        simp only [Option.some.injEq] at found
        subst found
        exact ⟨fresh, prekey, oneTime, kem, _, _, _, Or.inr rfl, rfl, written⟩
  | _ =>
      simp only [phase, simulateQ_pure, support_pure, Set.mem_singleton_iff] at supported
      subst supported
      exact ⟨fun _ => rfl, fun bytes found => by simp at found⟩

/-- A rejected finish aborts an InitSent owner and keeps every other owner. -/
theorem finish_failure (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (raw : Pqxdh.Bytes)
    (owner : PqxdhRegistrationSchedule.Owner KemSK) (shared : NativeState KemSK)
    (next : PqxdhRegistrationSchedule.Owner KemSK) (final : NativeState KemSK)
    (supported : ((none, next), final) ∈ support ((simulateQ (PqxdhRegistrationSchedule.callbacks setup codec)
      (PqxdhBeaconPhase2Publication.nativeOwner codec.frameRead raw owner)).run shared)) :
    match owner.beacon.phase with
    | .initSent control _ _ _ => next = PqxdhBeaconPhase2Preparation.abort control owner
    | _ => next = owner := by
  rw [PqxdhBeaconPhase2Publication.nativeOwner, ← QueryImpl.simulateQ_compose] at supported
  have shape := PqxdhBeaconPhase2Publication.owner_failure _ codec.frameRead raw owner next shared final supported
  revert shape
  cases owner.beacon.phase with
  | initSent control prekey oneTime kem => exact id
  | _ => exact fun shape => shape.1

/-- The invariant survives a step that keeps every view and the Server identity, when the new entry changes neither the created bindings nor the phases of the summary, is shaped as a build, and is shaped as a bundle for the new state. -/
theorem agree_extend (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (server : RawCtxServerRouting.Identity) (transcript : List Entry) (before after : PqxdhRegistrationSchedule.State KemSK)
    (entry : Entry) (agree : Agree setup codec server transcript before) (alike : Alike before after)
    (owners : (PqxdhDeploymentTranscript.step (summarize transcript) entry).owners = (summarize transcript).owners)
    (phases : (PqxdhDeploymentTranscript.step (summarize transcript) entry).phases = (summarize transcript).phases)
    (build : BuildShaped codec server entry) (bundle : BundleShaped setup codec after entry) :
    Agree setup codec server (transcript ++ [entry]) after := by
  have kept := agree_alike setup codec server transcript before after agree alike
  refine ⟨kept.identity, ?_, fun index => ?_, ?_, ?_, ?_⟩
  · rw [PqxdhDeploymentTranscript.summarize_append, owners]
    exact kept.count
  · rw [← kept.phases index]
    simp only [phase, PqxdhDeploymentTranscript.summarize_append, phases]
  · rw [PqxdhDeploymentTranscript.summarize_append, owners]
    exact kept.bindings
  · intro other member
    rcases List.mem_append.mp member with old | new
    · exact kept.builds other old
    · rw [List.mem_singleton] at new
      subst new
      exact build
  · intro other member
    rcases List.mem_append.mp member with old | new
    · exact kept.bundles other old
    · rw [List.mem_singleton] at new
      subst new
      exact bundle

/-- The invariant survives a step that replaces one owner by an owner with the same pinned identity, pinned key ID and identity seed and the same or no remaining KEM public key, when the new entry keeps the created bindings and moves that owner's public phase to the new owner's class. -/
theorem agree_update (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (server : RawCtxServerRouting.Identity) (transcript : List Entry) (before after : PqxdhRegistrationSchedule.State KemSK)
    (entry : Entry) (index : Nat) (owner replacement : PqxdhRegistrationSchedule.Owner KemSK)
    (agree : Agree setup codec server transcript before)
    (identity : after.shared.2.server.server.identity = before.shared.2.server.server.identity)
    (found : before.owners[index]? = some owner) (replaced : after.owners = before.owners.set index replacement)
    (pinned : replacement.beacon.serverIdentity = owner.beacon.serverIdentity)
    (keyId : pinnedKeyId replacement.beacon.phase = pinnedKeyId owner.beacon.phase)
    (seed : replacement.beacon.identity = owner.beacon.identity)
    (kem : kemPublic replacement.beacon.phase = none ∨ kemPublic replacement.beacon.phase = kemPublic owner.beacon.phase)
    (owners : (PqxdhDeploymentTranscript.step (summarize transcript) entry).owners = (summarize transcript).owners)
    (phases : (PqxdhDeploymentTranscript.step (summarize transcript) entry).phases =
      Function.update (summarize transcript).phases index (phaseClass replacement.beacon.phase))
    (build : BuildShaped codec server entry) (bundle : BundleShaped setup codec after entry) :
    Agree setup codec server (transcript ++ [entry]) after := by
  have bound : index < before.owners.length := (List.getElem?_eq_some_iff.mp found).1
  have at_index : after.owners[index]? = some replacement := by
    rw [replaced, List.getElem?_set_self bound]
  have others : ∀ other, other ≠ index → after.owners[other]? = before.owners[other]? := by
    intro other different
    rw [replaced, List.getElem?_set_ne (Ne.symm different)]
  refine ⟨by rw [identity]; exact agree.identity, ?_, fun position => ?_, ?_, ?_, ?_⟩
  · rw [PqxdhDeploymentTranscript.summarize_append, owners, replaced, List.length_set]
    exact agree.count
  · simp only [phase, PqxdhDeploymentTranscript.summarize_append, phases]
    by_cases same : position = index
    · subst same
      rw [Function.update_self, at_index]
      rfl
    · rw [Function.update_of_ne same, others position same]
      exact agree.phases position
  · rw [PqxdhDeploymentTranscript.summarize_append, owners]
    intro position pin key bindingFound
    obtain ⟨current, currentFound, pinEq, keyEq⟩ := agree.bindings position pin key bindingFound
    by_cases same : position = index
    · subst same
      rw [found, Option.some.injEq] at currentFound
      subst currentFound
      exact ⟨replacement, at_index, by rw [pinned]; exact pinEq, by rw [keyId]; exact keyEq⟩
    · exact ⟨current, by rw [others position same]; exact currentFound, pinEq, keyEq⟩
  · intro other member
    rcases List.mem_append.mp member with old | new
    · exact agree.builds other old
    · rw [List.mem_singleton] at new
      subst new
      exact build
  · intro other member
    rcases List.mem_append.mp member with old | new
    · have shaped := agree.bundles other old
      rcases other with ⟨(coin | command) | secrecy, reply⟩
      · trivial
      · cases command with
        | bundle position =>
            cases reply with
            | none => trivial
            | some bytes =>
                obtain ⟨current, keys, s1, s2, s3, currentFound, written, kemCurrent⟩ := shaped
                by_cases same : position = index
                · subst same
                  rw [found, Option.some.injEq] at currentFound
                  subst currentFound
                  refine ⟨replacement, keys, s1, s2, s3, at_index, by rw [seed]; exact written, ?_⟩
                  rcases kem with cleared | same
                  · exact Or.inl cleared
                  · rw [same]
                    exact kemCurrent
                · exact ⟨current, keys, s1, s2, s3, by rw [others position same]; exact currentFound, written,
                    kemCurrent⟩
        | _ => trivial
      · trivial
    · rw [List.mem_singleton] at new
      subst new
      exact bundle

/-- A registration command of the native handler is the source14 handler on the native part. -/
theorem onNative_support {Result : Type} (work : PqxdhRegistrationSchedule.Game KemSK Result)
    (state : PqxdhDeploymentNative.State KemSK) (result : Result × PqxdhDeploymentNative.State KemSK)
    (supported : result ∈ support ((PqxdhDeploymentNative.onNative work).run state)) :
    ∃ inner ∈ support (work.run state.native), result = (inner.1, { state with native := inner.2 }) := by
  rw [PqxdhDeploymentCompileStep.onNative_run, support_map] at supported
  obtain ⟨inner, member, rfl⟩ := supported
  exact ⟨inner, member, rfl⟩

/-- A shared Server command keeps every owner and the Server identity. -/
theorem shared_alike (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (serverSeed : IdentitySeed) (request : PqxdhRegistrationSchedule.Request)
    (kind : match request with
      | .accept _ | .build _ _ | .hmac _ _ | .hash _ => True
      | _ => False)
    (native : PqxdhRegistrationSchedule.State KemSK)
    (result : PqxdhRegistrationSchedule.QuerySpec request × PqxdhRegistrationSchedule.State KemSK)
    (supported : result ∈ support ((PqxdhRegistrationSchedule.handler setup codec checks serverSeed (.inr request)).run
      native)) :
    Alike native result.2 := by
  rcases request with _ | _ | raw | ⟨session, payload⟩ | _ | ⟨key, message⟩ | bytes | _
  all_goals simp only at kind
  · simp only [PqxdhRegistrationSchedule.handler,
      ← accept_native setup codec checks serverSeed PqxdhRegistrationSchedule.observationScalar] at supported
    obtain ⟨owners, reached⟩ :=
      PqxdhDeploymentCompileInvariant.shared_footprint setup serverSeed _ native result supported
    obtain ⟨server, _⟩ := PqxdhDeploymentCompileFootprint.accept_footprint setup codec checks _ raw _ _ reached
    exact ⟨by rw [server], by rw [owners], fun index => by rw [owners]⟩
  · simp only [PqxdhRegistrationSchedule.handler,
      ← build_native setup codec checks serverSeed PqxdhRegistrationSchedule.observationScalar] at supported
    obtain ⟨owners, reached⟩ :=
      PqxdhDeploymentCompileInvariant.shared_footprint setup serverSeed _ native result supported
    obtain ⟨identity, _⟩ := PqxdhDeploymentCompileFootprint.build_footprint setup codec checks session payload _ _ reached
    exact ⟨identity, by rw [owners], fun index => by rw [owners]⟩
  · simp only [PqxdhRegistrationSchedule.handler, ← hmac_native setup serverSeed PqxdhRegistrationSchedule.observationScalar]
      at supported
    obtain ⟨owners, reached⟩ :=
      PqxdhDeploymentCompileInvariant.shared_footprint setup serverSeed _ native result supported
    obtain ⟨server, _⟩ := PqxdhDeploymentCompileFootprint.hmac_fixed key message _ _ reached
    exact ⟨by rw [server], by rw [owners], fun index => by rw [owners]⟩
  · simp only [PqxdhRegistrationSchedule.handler, ← hash_native setup serverSeed PqxdhRegistrationSchedule.observationScalar]
      at supported
    obtain ⟨owners, reached⟩ :=
      PqxdhDeploymentCompileInvariant.shared_footprint setup serverSeed _ native result supported
    obtain ⟨server, _⟩ := PqxdhDeploymentCompileFootprint.hash_fixed bytes _ _ reached
    exact ⟨by rw [server], by rw [owners], fun index => by rw [owners]⟩

/-- Every successful build response is the Phase 2 writer output of fields carrying the Server's identity. -/
theorem build_shaped (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (serverSeed : IdentitySeed) (session : Nat) (payload : Option Pqxdh.Bytes)
    (native : PqxdhRegistrationSchedule.State KemSK)
    (result : Option PqxdhServerRegistrationPublication.Response × PqxdhRegistrationSchedule.State KemSK)
    (supported : result ∈ support ((PqxdhRegistrationSchedule.handler setup codec checks serverSeed
      (.inr (.build session payload))).run native)) :
    BuildShaped codec native.shared.2.server.server.identity ⟨.inl (.inr (.build session payload)), result.1⟩ := by
  simp only [PqxdhRegistrationSchedule.handler,
    ← build_native setup codec checks serverSeed PqxdhRegistrationSchedule.observationScalar] at supported
  obtain ⟨_, reached⟩ := PqxdhDeploymentCompileInvariant.shared_footprint setup serverSeed _ native result supported
  obtain ⟨_, _, _, _, _, _, published⟩ :=
    PqxdhDeploymentCompileFootprint.build_footprint setup codec checks session payload _ _ reached
  rcases outcome : result.1 with _ | response
  · trivial
  · obtain ⟨_, _, fields, _, _, _, written, identity⟩ := published response outcome
    exact ⟨fields, written, identity⟩

/-- Every coin and command of the native handler keeps the invariant, with the command and its reply appended to the transcript. -/
theorem command_step (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (serverSeed : IdentitySeed) (server : RawCtxServerRouting.Identity)
    (query : Spec.Domain) (transcript : List Entry) (state : PqxdhDeploymentNative.State KemSK)
    (agree : Agree setup codec server transcript state.native)
    (result : Spec.Range query × PqxdhDeploymentNative.State KemSK)
    (supported : result ∈ support ((PqxdhDeploymentNative.handler setup codec checks route serverSeed query).run state)) :
    Agree setup codec server (transcript ++ [⟨.inl query, result.1⟩]) result.2.native := by
  rcases query with coin | command
  · simp only [PqxdhDeploymentNative.handler, StateT.run_lift, mem_support_bind_iff, support_pure,
      Set.mem_singleton_iff] at supported
    obtain ⟨_, _, rfl⟩ := supported
    exact agree_extend setup codec server transcript _ _ _ agree (alike_refl _) rfl rfl trivial trivial
  · cases command with
    | create pin keyId =>
        cases parsed : parsePin pin with
        | none =>
            simp only [PqxdhDeploymentNative.handler, parsed, StateT.run_pure, support_pure,
              Set.mem_singleton_iff] at supported
            subst supported
            exact agree_extend setup codec server transcript _ _ _ agree (alike_refl _) rfl rfl trivial trivial
        | some word =>
            simp only [PqxdhDeploymentNative.handler, parsed, StateT.run_map, support_map, Set.mem_image] at supported
            obtain ⟨created, member, rfl⟩ := supported
            obtain ⟨inner, innerMember, rfl⟩ := onNative_support _ state created member
            obtain ⟨seed, prekey, keys, rfl⟩ := create_support setup word keyId state.native inner innerMember
            have count := agree.count
            have summaryStep : PqxdhDeploymentTranscript.step (summarize transcript)
                ⟨.inl (.inr (.create pin keyId)), some state.native.owners.length⟩ =
                { summarize transcript with
                  owners := (summarize transcript).owners ++ [(word, keyId)]
                  phases := Function.update (summarize transcript).phases state.native.owners.length .fresh } := by
              simp only [PqxdhDeploymentTranscript.step, PqxdhDeploymentTranscript.stepCommand, parsed]
            refine ⟨agree.identity, ?_, fun index => ?_, ?_, ?_, ?_⟩
            · rw [PqxdhDeploymentTranscript.summarize_append, summaryStep, List.length_append, List.length_append, count]
              rfl
            · simp only [phase, PqxdhDeploymentTranscript.summarize_append, summaryStep]
              by_cases same : index = state.native.owners.length
              · subst same
                rw [Function.update_self, List.getElem?_append_right (le_refl _), Nat.sub_self]
                rfl
              · rw [Function.update_of_ne same]
                rcases Nat.lt_or_gt_of_ne same with below | above
                · rw [List.getElem?_append_left below]
                  exact agree.phases index
                · rw [List.getElem?_eq_none (by simp; omega)]
                  have old := agree.phases index
                  rw [List.getElem?_eq_none (by omega)] at old
                  exact old
            · rw [PqxdhDeploymentTranscript.summarize_append, summaryStep]
              intro index boundPin boundKey found
              by_cases below : index < (summarize transcript).owners.length
              · rw [List.getElem?_append_left below] at found
                obtain ⟨owner, ownerFound, pinEq, keyEq⟩ := agree.bindings index boundPin boundKey found
                exact ⟨owner, by rw [List.getElem?_append_left (by omega)]; exact ownerFound, pinEq, keyEq⟩
              · have equal : index = (summarize transcript).owners.length := by
                  have := (List.getElem?_eq_some_iff.mp found).1
                  simp only [List.length_append, List.length_singleton] at this
                  omega
                subst equal
                rw [List.getElem?_append_right (le_refl _), Nat.sub_self] at found
                simp only [List.getElem?_cons_zero, Option.some.injEq, Prod.mk.injEq] at found
                obtain ⟨rfl, rfl⟩ := found
                refine ⟨_, by rw [count, List.getElem?_append_right (le_refl _), Nat.sub_self]; rfl, rfl, rfl⟩
            · intro entry member
              rcases List.mem_append.mp member with old | new
              · exact agree.builds entry old
              · rw [List.mem_singleton] at new
                subst new
                trivial
            · intro entry member
              rcases List.mem_append.mp member with old | new
              · have shaped := agree.bundles entry old
                rcases entry with ⟨(coin | command) | secrecy, reply⟩
                · trivial
                · cases command with
                  | bundle position =>
                      cases reply with
                      | none => trivial
                      | some bytes =>
                          obtain ⟨owner, keys', s1, s2, s3, ownerFound, written, kemOwner⟩ := shaped
                          have bound := (List.getElem?_eq_some_iff.mp ownerFound).1
                          exact ⟨owner, keys', s1, s2, s3, by rw [List.getElem?_append_left bound]; exact ownerFound,
                            written, kemOwner⟩
                  | _ => trivial
                · trivial
              · rw [List.mem_singleton] at new
                subst new
                trivial
    | bundle index =>
        simp only [PqxdhDeploymentNative.handler] at supported
        obtain ⟨inner, innerMember, rfl⟩ := onNative_support _ state result supported
        cases found : state.native.owners[index]? with
        | none =>
            have run : (PqxdhRegistrationSchedule.handler setup codec checks serverSeed (.inr (.bundle index))).run
                state.native = pure (none, state.native) := by
              simp only [PqxdhRegistrationSchedule.handler, PqxdhRegistrationSchedule.bundle, StateT.run_bind,
                StateT.run_get, pure_bind, found, StateT.run_pure]
            rw [run, support_pure, Set.mem_singleton_iff] at innerMember
            subst innerMember
            refine agree_extend setup codec server transcript _ _ _ agree (alike_refl _) ?_ ?_ trivial trivial
            all_goals simp only [PqxdhDeploymentTranscript.step, PqxdhDeploymentTranscript.stepCommand]
            all_goals split <;> rfl
        | some owner =>
            change inner ∈ support (PqxdhRegistrationSchedule.bundle setup codec index state.native) at innerMember
            rw [PqxdhRegistrationSchedule.bundle_source setup codec index state.native owner found,
              support_map] at innerMember
            obtain ⟨reached, reachedMember, rfl⟩ := innerMember
            obtain ⟨rejected, published⟩ := bundle_candidate setup codec index owner reached reachedMember
            rcases outcome : reached.1 with _ | bytes
            · have same := rejected outcome
              have restored : state.native.owners.set index reached.2 = state.native.owners := by
                rw [same]
                exact PqxdhDeploymentCompileRegistration.set_found _ _ _ found
              refine agree_extend setup codec server transcript _ _ _ agree ⟨rfl, ?_, fun position => ?_⟩ ?_ ?_ trivial
                trivial
              · simp only [restored]
              · simp only [restored]
              all_goals simp only [PqxdhDeploymentTranscript.step, PqxdhDeploymentTranscript.stepCommand]
              all_goals split <;> rfl
            · obtain ⟨fresh, prekey, oneTime, kem, s1, s2, s3, wasFresh, installed, written⟩ := published bytes outcome
              have publicFresh : (summarize transcript).phases index = .fresh := by
                have phases := agree.phases index
                simp only [phase, found, nativePhase] at phases
                rw [phases]
                rcases wasFresh with isFresh | isFresh <;> rw [isFresh] <;> rfl
              refine agree_update setup codec server transcript state.native _ _ index owner reached.2 agree rfl found rfl
                ?_ ?_ ?_ ?_ ?_ ?_ trivial ?_
              · rw [installed]
              · rw [installed]
                rcases wasFresh with isFresh | isFresh <;> simp [isFresh, pinnedKeyId]
              · rw [installed]
              · right
                rw [installed]
                rcases wasFresh with isFresh | isFresh <;> simp [isFresh, kemPublic]
              · simp only [PqxdhDeploymentTranscript.step, PqxdhDeploymentTranscript.stepCommand, publicFresh, ite_true]
              · simp only [PqxdhDeploymentTranscript.step, PqxdhDeploymentTranscript.stepCommand, publicFresh, ite_true,
                  installed, phaseClass]
              · refine ⟨reached.2, ⟨setup.dh.publicKey prekey, setup.dh.publicKey oneTime, kem.1⟩, s1, s2, s3, ?_, ?_, ?_⟩
                · have bound : index < state.native.owners.length := (List.getElem?_eq_some_iff.mp found).1
                  simp only [List.getElem?_set_self bound]
                · rw [installed]
                  exact written
                · right
                  rw [installed]
                  rfl
    | finish index raw =>
        simp only [PqxdhDeploymentNative.handler] at supported
        obtain ⟨inner, innerMember, rfl⟩ := onNative_support _ state result supported
        cases found : state.native.owners[index]? with
        | none =>
            change inner ∈ support ((PqxdhRegistrationSchedule.finish setup codec index raw).run state.native) at innerMember
            rw [PqxdhRegistrationSchedule.finish_missing setup codec index raw state.native found, support_pure,
              Set.mem_singleton_iff] at innerMember
            subst innerMember
            have absent := agree.phases index
            simp only [phase, found, nativePhase] at absent
            refine agree_extend setup codec server transcript _ _ _ agree (alike_refl _) ?_ ?_ trivial trivial
            all_goals simp [PqxdhDeploymentTranscript.step, PqxdhDeploymentTranscript.stepCommand, absent]
        | some owner =>
            change inner ∈ support (PqxdhRegistrationSchedule.finish setup codec index raw state.native) at innerMember
            have fields := PqxdhRegistrationSchedule.finish_fields setup codec index raw state.native inner innerMember
            have identity : inner.2.shared.2.server.server.identity = state.native.shared.2.server.server.identity := by
              rw [fields]
            rw [PqxdhRegistrationSchedule.finish_source setup codec index raw state.native owner found,
              support_map] at innerMember
            obtain ⟨reached, reachedMember, rfl⟩ := innerMember
            have phases := agree.phases index
            simp only [phase, found, nativePhase] at phases
            have bound : index < state.native.owners.length := (List.getElem?_eq_some_iff.mp found).1
            rcases outcome : reached.1.1 with _ | plaintext
            · have shape := finish_failure setup codec raw owner state.native.shared reached.1.2 reached.2
                (by rw [← outcome]; exact reachedMember)
              revert shape
              cases ownerPhase : owner.beacon.phase with
              | initSent control prekey oneTime kem =>
                  intro aborted
                  rw [ownerPhase] at phases
                  refine agree_update setup codec server transcript state.native _ _ index owner reached.1.2 agree
                    identity found rfl ?_ ?_ ?_ (Or.inl ?_) ?_ ?_ trivial trivial
                  · rw [aborted]
                    rfl
                  · rw [aborted, ownerPhase]
                    rfl
                  · rw [aborted]
                    rfl
                  · rw [aborted]
                    rfl
                  · simp only [PqxdhDeploymentTranscript.step, PqxdhDeploymentTranscript.stepCommand, phases, phaseClass]
                    rfl
                  · simp only [PqxdhDeploymentTranscript.step, PqxdhDeploymentTranscript.stepCommand, phases, phaseClass,
                      aborted, PqxdhBeaconPhase2Preparation.abort]
                    rfl
              | _ =>
                  intro same
                  rw [ownerPhase] at phases
                  have restored : state.native.owners.set index reached.1.2 = state.native.owners := by
                    rw [same]
                    exact PqxdhDeploymentCompileRegistration.set_found _ _ _ found
                  refine agree_extend setup codec server transcript _ _ _ agree
                    ⟨identity, by simp only [restored], fun position => by simp only [restored]⟩ ?_ ?_ trivial trivial
                  all_goals simp only [PqxdhDeploymentTranscript.step, PqxdhDeploymentTranscript.stepCommand, phases,
                    phaseClass]
                  all_goals rfl
            · obtain ⟨control, prekey, oneTime, kem, response, kernel, ownerPhase, _, installed⟩ :=
                (PqxdhDeploymentCompileFootprint.finish_owner setup codec raw owner state.native.shared reached
                  reachedMember).2 plaintext outcome
              rw [ownerPhase] at phases
              refine agree_update setup codec server transcript state.native _ _ index owner reached.1.2 agree
                identity found rfl ?_ ?_ ?_ (Or.inl ?_) ?_ ?_ trivial trivial
              · rw [installed]
              · rw [installed, ownerPhase]
                rfl
              · rw [installed]
              · rw [installed]
                rfl
              · simp only [PqxdhDeploymentTranscript.step, PqxdhDeploymentTranscript.stepCommand, phases, phaseClass]
                rfl
              · simp only [PqxdhDeploymentTranscript.step, PqxdhDeploymentTranscript.stepCommand, phases, phaseClass,
                  installed]
                rfl
    | accept raw =>
        simp only [PqxdhDeploymentNative.handler] at supported
        obtain ⟨inner, innerMember, rfl⟩ := onNative_support _ state result supported
        exact agree_extend setup codec server transcript _ _ _ agree
          (shared_alike setup codec checks serverSeed (.accept raw) trivial _ inner innerMember) rfl rfl trivial trivial
    | build session payload =>
        simp only [PqxdhDeploymentNative.handler] at supported
        obtain ⟨inner, innerMember, rfl⟩ := onNative_support _ state result supported
        have shaped := build_shaped setup codec checks serverSeed session payload _ inner innerMember
        rw [agree.identity] at shaped
        exact agree_extend setup codec server transcript _ _ _ agree
          (shared_alike setup codec checks serverSeed (.build session payload) trivial _ inner innerMember) rfl rfl
          shaped trivial
    | hmac key message =>
        simp only [PqxdhDeploymentNative.handler] at supported
        obtain ⟨inner, innerMember, rfl⟩ := onNative_support _ state result supported
        exact agree_extend setup codec server transcript _ _ _ agree
          (shared_alike setup codec checks serverSeed (.hmac key message) trivial _ inner innerMember) rfl rfl trivial
          trivial
    | hash bytes =>
        simp only [PqxdhDeploymentNative.handler] at supported
        obtain ⟨inner, innerMember, rfl⟩ := onNative_support _ state result supported
        exact agree_extend setup codec server transcript _ _ _ agree
          (shared_alike setup codec checks serverSeed (.hash bytes) trivial _ inner innerMember) rfl rfl trivial trivial
    | serverSend kid plaintext =>
        exact agree_extend setup codec server transcript _ _ _ agree
          (serverStep_alike setup codec route (.inl (plaintext, kid)) state result supported) rfl rfl trivial trivial
    | serverRaw raw =>
        exact agree_extend setup codec server transcript _ _ _ agree
          (serverStep_alike setup codec route (.inr raw) state result supported) rfl rfl trivial trivial
    | beaconSend index plaintext =>
        exact agree_extend setup codec server transcript _ _ _ agree
          (beaconStep_alike setup codec index (.inl plaintext) state result supported) rfl rfl trivial trivial
    | beaconRaw index raw =>
        exact agree_extend setup codec server transcript _ _ _ agree
          (beaconStep_alike setup codec index (.inr raw) state result supported) rfl rfl trivial trivial

/-- A native-interface program that issues only coins and sends keeps every view and the Server identity. -/
theorem coinSend_alike {Value : Type} (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (serverSeed : IdentitySeed) (program : OracleComp Spec Value)
    (bounded : program.IsQueryBoundP (fun query => PqxdhDeploymentSecrecy.coinOrSend query = false) 0)
    (state : PqxdhDeploymentNative.State KemSK) (result : Value × PqxdhDeploymentNative.State KemSK)
    (supported : result ∈ support ((simulateQ (PqxdhDeploymentNative.handler setup codec checks route serverSeed)
      program).run state)) :
    Alike state.native result.2.native := by
  induction program using OracleComp.inductionOn generalizing state with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
      subst supported
      exact alike_refl _
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
      have firstAlike : Alike state.native middle.native := by
        rcases query with coin | command
        · simp only [PqxdhDeploymentNative.handler, StateT.run_lift, mem_support_bind_iff, support_pure,
            Set.mem_singleton_iff] at first
          obtain ⟨_, _, same⟩ := first
          cases same
          exact alike_refl _
        · cases command with
          | serverSend kid plaintext =>
              exact serverStep_alike setup codec route (.inl (plaintext, kid)) state _ first
          | beaconSend index plaintext =>
              exact beaconStep_alike setup codec index (.inl plaintext) state _ first
          | _ => simp [PqxdhDeploymentSecrecy.coinOrSend] at kind
      have restBound := rest reply
      simp only [kind, Bool.true_eq_false, ite_false] at restBound
      exact alike_trans _ _ _ firstAlike (ih reply restBound middle second)

/-- The secrecy layer records each secrecy command once, with its reply. -/
theorem ledger_secrecy (codec : Codec Reader Response) (serverKid : Std.U64) (bounds : FreshBounds)
    (secrecy : PqxdhDeploymentInterface.Secrecy) (ledger : Ledger)
    (result : Option RawCtxSourceSend.Encrypted × Ledger)
    (supported : result ∈ support ((ledgerImpl codec serverKid bounds (.inr secrecy)).run ledger)) :
    result.2.transcript = ledger.transcript ++ [⟨.inr secrecy, result.1⟩] := by
  rcases secrecy with ⟨handle, left, right⟩ | ⟨handle, length⟩
  · simp only [ledgerImpl, StateT.run] at supported
    split at supported
    · split at supported
      · simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at supported
        obtain ⟨_, _, _, _, rfl⟩ := supported
        rfl
      · split at supported
        · simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at supported
          obtain ⟨_, _, rfl⟩ := supported
          rfl
        · simp only [support_pure, Set.mem_singleton_iff] at supported
          subst supported
          rfl
    · simp only [support_pure, Set.mem_singleton_iff] at supported
      subst supported
      rfl
  · simp only [ledgerImpl, StateT.run] at supported
    split at supported
    · simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at supported
      obtain ⟨_, _, _, _, rfl⟩ := supported
      rfl
    · simp only [support_pure, Set.mem_singleton_iff] at supported
      subst supported
      rfl

/-- One query of the complete experiment, run through the CE handler. -/
theorem handler_run (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (serverSeed : IdentitySeed) (bounds : FreshBounds)
    (query : PqxdhDeploymentInterface.Query) (ledger : Ledger) (state : PqxdhDeploymentNative.State KemSK) :
    (PqxdhDeploymentSecrecy.handler setup codec checks route serverSeed bounds query).run (ledger, state) =
      (fun result => (result.1.1, (result.1.2, result.2))) <$>
        (simulateQ (PqxdhDeploymentNative.handler setup codec checks route serverSeed)
          ((ledgerImpl codec setup.serverKeyId bounds query).run ledger)).run state := rfl

/-- Every query of the complete experiment keeps the invariant between its transcript and its native state. -/
theorem experiment_step (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (serverSeed : IdentitySeed) (bounds : FreshBounds)
    (server : RawCtxServerRouting.Identity) (query : PqxdhDeploymentInterface.Query)
    (state : PqxdhDeploymentSecrecy.State KemSK) (agree : Agree setup codec server state.1.transcript state.2.native)
    (result : FullSpec.Range query × PqxdhDeploymentSecrecy.State KemSK)
    (supported : result ∈ support ((PqxdhDeploymentSecrecy.handler setup codec checks route serverSeed bounds query).run
      state)) :
    Agree setup codec server result.2.1.transcript result.2.2.native := by
  rcases state with ⟨ledger, native⟩
  rw [handler_run, support_map] at supported
  obtain ⟨reached, member, rfl⟩ := supported
  rcases query with request | secrecy
  · rw [PqxdhDeploymentSecrecy.ledgerImpl_forward, simulateQ_map, simulateQ_spec_query, StateT.run_map,
      support_map] at member
    obtain ⟨answer, answerMember, rfl⟩ := member
    exact command_step setup codec checks route serverSeed server request ledger.transcript native agree answer
      answerMember
  · have value : reached.1 ∈ support ((ledgerImpl codec setup.serverKeyId bounds (.inr secrecy)).run ledger) := by
      apply OracleComp.support_simulateQ_run'_subset (PqxdhDeploymentNative.handler setup codec checks route serverSeed)
        _ native
      rw [StateT.run'_eq, support_map]
      exact ⟨reached, member, rfl⟩
    have recorded := ledger_secrecy codec setup.serverKeyId bounds secrecy ledger reached.1 value
    have alike := coinSend_alike setup codec checks route serverSeed _
      (PqxdhDeploymentSecrecy.secrecy_frame codec setup.serverKeyId bounds secrecy ledger) native reached member
    simp only [recorded]
    exact agree_extend setup codec server ledger.transcript native.native reached.2.native _ agree alike rfl rfl trivial
      trivial

/-- The invariant holds at the start of the experiment: empty transcript, no owner. -/
theorem agree_initial (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (created : PqxdhLiveServerConstruction.Created Unit) :
    Agree setup codec (PqxdhDeploymentNative.initial (KemSK := KemSK) created).native.shared.2.server.server.identity []
      (PqxdhDeploymentNative.initial created).native := by
  refine ⟨rfl, rfl, fun index => ?_, fun index pin keyId found => ?_, (fun _ member => nomatch member),
    (fun _ member => nomatch member)⟩
  · rfl
  · simp [summarize, PqxdhDeploymentTranscript.Summary.empty] at found

/-- Publicity along the whole experiment: in either mode, every outcome of the common deployment experiment satisfies the invariant between its final transcript and its final native state, for the Server's identity. -/
theorem agree_game (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (ensureInit : StateT A ProbComp Bool) (identityIndex : Nat)
    (bounds : FreshBounds) (mode : Mode) (adversary : OracleComp (ModeSpec mode) X) (runtime : A)
    (outcome : Option (PqxdhRegistrationJointServerBirth.ClientCreated Unit × X × PqxdhDeploymentSecrecy.State KemSK) × A)
    (supported : outcome ∈ support ((PqxdhDeploymentSecrecy.game setup codec checks route ensureInit identityIndex bounds
      mode adversary).run runtime))
    (created : PqxdhRegistrationJointServerBirth.ClientCreated Unit) (output : X)
    (final : PqxdhDeploymentSecrecy.State KemSK) (reached : outcome.1 = some (created, output, final)) :
    Agree setup codec final.2.native.shared.2.server.server.identity final.1.transcript final.2.native := by
  simp only [PqxdhDeploymentSecrecy.game, StateT.run, mem_support_bind_iff] at supported
  obtain ⟨born, _, supported⟩ := supported
  rcases born with ⟨_ | constructed, after⟩
  · simp only [support_pure, Set.mem_singleton_iff] at supported
    subst supported
    cases reached
  · simp only [support_map, Set.mem_image] at supported
    obtain ⟨executed, executedMember, rfl⟩ := supported
    cases reached
    have invariant := OracleComp.simulateQ_run_preserves_inv_of_query
      (PqxdhDeploymentSecrecy.handler setup codec checks route constructed.seed bounds)
      (fun state => Agree setup codec (PqxdhDeploymentNative.initial (KemSK := KemSK) constructed).native.shared.2.server.server.identity
        state.1.transcript state.2.native)
      (fun query state agree result member => experiment_step setup codec checks route constructed.seed bounds _ query
        state agree result member)
      (asModeO mode adversary) (Ledger.empty, PqxdhDeploymentNative.initial constructed)
      (agree_initial setup codec constructed) _ executedMember
    rw [← invariant.identity] at invariant
    exact invariant

/-- Publicity of `phase`: on every outcome of the experiment, the public phase of every owner handle is the class of its native lifecycle phase. -/
theorem phase_public (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (ensureInit : StateT A ProbComp Bool) (identityIndex : Nat)
    (bounds : FreshBounds) (mode : Mode) (adversary : OracleComp (ModeSpec mode) X) (runtime : A)
    (outcome : Option (PqxdhRegistrationJointServerBirth.ClientCreated Unit × X × PqxdhDeploymentSecrecy.State KemSK) × A)
    (supported : outcome ∈ support ((PqxdhDeploymentSecrecy.game setup codec checks route ensureInit identityIndex bounds
      mode adversary).run runtime))
    (created : PqxdhRegistrationJointServerBirth.ClientCreated Unit) (output : X)
    (final : PqxdhDeploymentSecrecy.State KemSK) (reached : outcome.1 = some (created, output, final)) (index : Nat) :
    phase final.1.transcript index = nativePhase final.2.native.owners[index]? :=
  (agree_game setup codec checks route ensureInit identityIndex bounds mode adversary runtime outcome supported created
    output final reached).phases index

/-- Publicity of `owner`: on every outcome, `owner k` names handle `k` exactly when `k` is below the number of native owners, each created by one successful `create`. -/
theorem owner_public (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (ensureInit : StateT A ProbComp Bool) (identityIndex : Nat)
    (bounds : FreshBounds) (mode : Mode) (adversary : OracleComp (ModeSpec mode) X) (runtime : A)
    (outcome : Option (PqxdhRegistrationJointServerBirth.ClientCreated Unit × X × PqxdhDeploymentSecrecy.State KemSK) × A)
    (supported : outcome ∈ support ((PqxdhDeploymentSecrecy.game setup codec checks route ensureInit identityIndex bounds
      mode adversary).run runtime))
    (created : PqxdhRegistrationJointServerBirth.ClientCreated Unit) (output : X)
    (final : PqxdhDeploymentSecrecy.State KemSK) (reached : outcome.1 = some (created, output, final)) (k : Nat) :
    PqxdhDeploymentTranscript.owner final.1.transcript k =
      if k < final.2.native.owners.length then some k else none := by
  have count := (agree_game setup codec checks route ensureInit identityIndex bounds mode adversary runtime outcome
    supported created output final reached).count
  simp only [PqxdhDeploymentTranscript.owner, count]

/-- Publicity of `NoBundleFailure`: a rejected bundle sets an owner's failure flag exactly when the owner is natively Fresh (with or without retained coins); no other entry sets a flag. -/
theorem failure_public (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (server : RawCtxServerRouting.Identity) (transcript : List Entry) (native : PqxdhRegistrationSchedule.State KemSK)
    (agree : Agree setup codec server transcript native) (index : Nat) :
    (summarize (transcript ++ [⟨.inl (.inr (.bundle index)), none⟩])).failures =
      if nativePhase native.owners[index]? = .fresh then
        Function.update (summarize transcript).failures index true
      else (summarize transcript).failures := by
  have phases := agree.phases index
  simp only [phase] at phases
  simp only [PqxdhDeploymentTranscript.summarize_append, PqxdhDeploymentTranscript.step,
    PqxdhDeploymentTranscript.stepCommand, phases]
  split <;> rfl

/-- A designated owner is natively Established, pinned to the protected key ID and to the pin of its created binding. -/
theorem designate_owner_native (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (server : RawCtxServerRouting.Identity) (serverKid : Std.U64) (transcript : List Entry)
    (native : PqxdhRegistrationSchedule.State KemSK) (agree : Agree setup codec server transcript native)
    (index session k : Nat)
    (designated : PqxdhDeploymentTranscript.designate codec serverKid transcript (.owner index) = some (session, k)) :
    k = index ∧ ∃ owner pin, native.owners[index]? = some owner ∧ phaseClass owner.beacon.phase = .established ∧
      (summarize transcript).owners[index]? = some (pin, serverKid) ∧ owner.beacon.serverIdentity = pin ∧
      pinnedKeyId owner.beacon.phase = serverKid := by
  obtain ⟨same, established, pin, _, _, _, binding, _⟩ :=
    PqxdhDeploymentTranscript.designate_owner codec serverKid transcript index session k designated
  obtain ⟨owner, found, pinEq, keyEq⟩ := agree.bindings index pin serverKid binding
  have phases := agree.phases index
  rw [established, found] at phases
  exact ⟨same, owner, pin, found, phases.symm, binding, pinEq, keyEq⟩

end BeaconcryptCore.Computational.PqxdhDeploymentEligibility

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentEligibility.nativePhase_view' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEligibility.nativePhase_view

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentEligibility.bundleShaped_alike' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEligibility.bundleShaped_alike

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentEligibility.agree_alike' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEligibility.agree_alike

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentEligibility.alike_refl' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEligibility.alike_refl

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentEligibility.alike_trans' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEligibility.alike_trans

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentEligibility.record_value' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEligibility.record_value

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentEligibility.serverImpl_identity' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEligibility.serverImpl_identity

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentEligibility.beaconImpl_view' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEligibility.beaconImpl_view

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentEligibility.serverStep_alike' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEligibility.serverStep_alike

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentEligibility.beaconStep_alike' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEligibility.beaconStep_alike

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentEligibility.create_support' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEligibility.create_support

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentEligibility.bundle_candidate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEligibility.bundle_candidate

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentEligibility.finish_failure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEligibility.finish_failure

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentEligibility.agree_extend' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEligibility.agree_extend

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentEligibility.agree_update' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEligibility.agree_update

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentEligibility.onNative_support' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEligibility.onNative_support

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentEligibility.shared_alike' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEligibility.shared_alike

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentEligibility.build_shaped' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEligibility.build_shaped

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentEligibility.command_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEligibility.command_step

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentEligibility.coinSend_alike' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEligibility.coinSend_alike

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentEligibility.ledger_secrecy' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEligibility.ledger_secrecy

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentEligibility.handler_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEligibility.handler_run

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentEligibility.experiment_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEligibility.experiment_step

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentEligibility.agree_initial' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEligibility.agree_initial

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentEligibility.agree_game' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEligibility.agree_game

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentEligibility.phase_public' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEligibility.phase_public

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentEligibility.owner_public' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEligibility.owner_public

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentEligibility.failure_public' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEligibility.failure_public

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentEligibility.designate_owner_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEligibility.designate_owner_native
