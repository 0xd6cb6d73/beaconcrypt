-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.CborAdmissionInvariant
import BeaconcryptCore.Computational.PqxdhDeploymentIdealPostGoodBuild
import BeaconcryptCore.Computational.PqxdhDeploymentIdealPostGood

/-! Assignment-counter facts for the hidden registration builder. The next-state counter is derived at the actual extracted prepare operation; the existing publication-shape existential alone does not imply it. These lemmas retain all optional writer and diagnostic branches. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
namespace BeaconcryptCore.Computational.CborRawMiddleCounter
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhServerRegistrationPublication (Response ResponseFields AuxSpec TailSpec)
open PqxdhDeploymentIdealPostGoodBuild (WBuilt candidateW_shape writeImpl)
variable {ι KemSK Reader WireResponse : Type} {baseSpec : OracleSpec ι}

def assignedAfter (query : (PqxdhDeploymentRecordCache.SourceSpec KemSK).Domain) :
    (PqxdhDeploymentRecordCache.SourceSpec KemSK).Range query → Aeneas.Std.U64 → Aeneas.Std.U64 := by
  rcases query with (coin | command) | read
  · exact fun _ previous => previous
  · cases command
    case build => exact fun response previous => (response.map Response.keyId).getD previous
    all_goals exact fun _ previous => previous
  · exact fun _ previous => previous

theorem assignedAfter_other (query : (PqxdhDeploymentRecordCache.SourceSpec KemSK).Domain)
    (other : PqxdhRegistrationJointRevealCosts.sourceKind (KemSK := KemSK) query ≠ .inl 4)
    (answer : (PqxdhDeploymentRecordCache.SourceSpec KemSK).Range query) (previous : Aeneas.Std.U64) :
    assignedAfter query answer previous = previous := by
  rcases query with (coin | command) | read
  · rfl
  · cases command
    all_goals first | rfl | exact absurd rfl other
  · rfl

theorem native_noBuild (setup : Setup baseSpec KemSK) (codec : Codec Reader WireResponse) (checks : Checks)
    (seed : PqxdhJointIdentity.IdentitySeed) (query : (PqxdhDeploymentRecordCache.SourceSpec KemSK).Domain)
    (other : PqxdhRegistrationJointRevealCosts.sourceKind (KemSK := KemSK) query ≠ .inl 4)
    (before : PqxdhRegistrationSchedule.State KemSK)
    (result : (PqxdhDeploymentRecordCache.SourceSpec KemSK).Range query × PqxdhRegistrationSchedule.State KemSK)
    (supported : result ∈ support
      ((PqxdhRegistrationJointRevealSchedule.native setup codec checks seed query).run before)) :
    result.2.shared.2.server.control.last_key_id = before.shared.2.server.control.last_key_id := by
  apply CborAdmissionInvariant.source_no_build_counter setup codec checks seed
    ((PqxdhDeploymentRecordCache.SourceSpec KemSK).query query)
    (by simp [isQueryBoundP_query_iff, other])
    before result
  simpa only [simulateQ_spec_query] using supported

/-- Every native source14 reply updates the allocation counter only through its actual successful build response. -/
theorem native_assignment (setup : Setup baseSpec KemSK) (codec : Codec Reader WireResponse) (checks : Checks)
    (seed : PqxdhJointIdentity.IdentitySeed) (query : (PqxdhDeploymentRecordCache.SourceSpec KemSK).Domain)
    (before : PqxdhRegistrationSchedule.State KemSK)
    (result : (PqxdhDeploymentRecordCache.SourceSpec KemSK).Range query × PqxdhRegistrationSchedule.State KemSK)
    (supported : result ∈ support
      ((PqxdhRegistrationJointRevealSchedule.native setup codec checks seed query).run before)) :
    assignedAfter query result.1 before.shared.2.server.control.last_key_id =
      result.2.shared.2.server.control.last_key_id := by
  by_cases build : PqxdhRegistrationJointRevealCosts.sourceKind (KemSK := KemSK) query = .inl 4
  · rcases query with (coin | command) | read
    · simp [PqxdhRegistrationJointRevealCosts.sourceKind, PqxdhRegistrationSchedule.sourceKind] at build
    · cases command
      all_goals try simp [PqxdhRegistrationJointRevealCosts.sourceKind, PqxdhRegistrationSchedule.sourceKind] at build
      rename_i session data
      rcases PqxdhRegistrationSchedule.build_counter setup codec checks seed session data before result supported with
        ⟨absent, unchanged⟩ | ⟨response, present, _, assigned⟩
      · simp only [assignedAfter, absent, Option.map_none, Option.getD_none, unchanged]
      · simpa only [assignedAfter, present, Option.map_some, Option.getD_some] using assigned
    · simp [PqxdhRegistrationJointRevealCosts.sourceKind] at build
  · rw [assignedAfter_other query build]
    exact (native_noBuild setup codec checks seed query build before result supported).symm

theorem pool_assignment (setup : Setup baseSpec KemSK) (codec : Codec Reader WireResponse) (checks : Checks)
    (seed : PqxdhJointIdentity.IdentitySeed) (pairs : List (PqxdhLiveKemReservation.Pair KemSK))
    (query : (PqxdhDeploymentRecordCache.SourceSpec KemSK).Domain) (before : PqxdhRegistrationSchedule.State KemSK)
    (result : (PqxdhDeploymentRecordCache.SourceSpec KemSK).Range query × PqxdhRegistrationSchedule.State KemSK)
    (supported : result ∈ support
      ((PqxdhDeploymentIdealPool.revealPool setup codec checks seed pairs query).run before)) :
    assignedAfter query result.1 before.shared.2.server.control.last_key_id =
      result.2.shared.2.server.control.last_key_id := by
  rcases query with (coin | command) | read
  · exact native_assignment setup codec checks seed _ before result supported
  · cases command with
    | create pin keyId =>
        obtain ⟨identity, prekey, keys, rfl⟩ :=
          PqxdhDeploymentIdealPool.createPool_support setup pairs pin keyId before result supported
        rfl
    | _ => exact native_assignment setup codec checks seed _ before result supported
  · exact native_assignment setup codec checks seed _ before result supported

/-- Private ownership annotations and the fixed KEM creation pool do not alter the public assignment counter relation. -/
theorem sourcePool_assignment (setup : Setup baseSpec KemSK) (codec : Codec Reader WireResponse) (checks : Checks)
    (seed : PqxdhJointIdentity.IdentitySeed) (identityIndex : Nat) (pairs : List (PqxdhLiveKemReservation.Pair KemSK))
    (query : (PqxdhDeploymentRecordCache.SourceSpec KemSK).Domain)
    (before : PqxdhRegistrationJointSchedule.State KemSK)
    (result : (PqxdhDeploymentRecordCache.SourceSpec KemSK).Range query × PqxdhRegistrationJointSchedule.State KemSK)
    (supported : result ∈ support ((PqxdhDeploymentIdealPoolSource.sourcePool setup codec checks seed
      identityIndex pairs query).run before)) :
    assignedAfter query result.1 before.shared.2.server.control.last_key_id =
      result.2.shared.2.server.control.last_key_id := by
  apply pool_assignment setup codec checks seed pairs query
    (PqxdhRegistrationJointSchedule.source before)
    (result.1, PqxdhRegistrationJointSchedule.source result.2)
  rw [← PqxdhDeploymentIdealPoolSource.sourcePool_native setup codec checks seed identityIndex pairs query before,
    support_map]
  exact ⟨result, supported, rfl⟩

section Generic
variable {Kernel Metadata PeerMetadata Consumed : Type} {κ : Type} {spec : OracleSpec κ}
open PqxdhInitialGenericPublication (State)

def Allocation (before : State Kernel Metadata PeerMetadata Consumed) :
    RustM (Option Response × State Kernel Metadata PeerMetadata Consumed) → Prop
  | .ok (none, after) => after.control = before.control
  | .ok (some response, after) => response.keyId = after.control.last_key_id
  | _ => True

theorem allocation_of_shape (write : ResponseFields → Option Pqxdh.Bytes)
    (before : State Kernel Metadata PeerMetadata Consumed) (metadata : PeerMetadata)
    (result : RustM (Option Response × State Kernel Metadata PeerMetadata Consumed))
    (shape : WBuilt write (fun candidate => candidate.key_id = candidate.next_state.last_key_id)
      before metadata result) : Allocation before result := by
  rcases result with ⟨(_ | response), after⟩ | error | _
  · exact congrArg (fun state => state.control) shape
  · obtain ⟨candidate, kernel, encrypted, counter, assigned, _, published, _⟩ := shape
    rw [Allocation, published, assigned]
    exact counter
  · trivial
  · trivial

/-- The generic builder's allocation relation follows from the actual successful prepare result, without assuming any property of an existential candidate. -/
theorem generic_allocation (write : ResponseFields → Option Pqxdh.Bytes)
    (associatedData : PqxdhTranscriptAd.AssociatedData) (calls : RawCtxChainOwner.Calls Kernel (OracleComp spec))
    (aux : QueryImpl AuxSpec (OracleComp spec))
    (writes : ∀ fields, ∀ bytes ∈ support (aux (.write fields)), bytes = write fields)
    (initial : RustM Kernel) (pending : pqxdh.PendingServerRegistration)
    (data : Option Pqxdh.Bytes) (metadata : PeerMetadata) (state : State Kernel Metadata PeerMetadata Consumed)
    (result : RustM (Option Response × State Kernel Metadata PeerMetadata Consumed))
    (supported : result ∈ support
      (PqxdhServerAuthSendFactor.genericBuild (associatedData := associatedData) calls aux initial pending data
        metadata state)) :
    Allocation state result := by
  apply allocation_of_shape write state metadata result
  unfold PqxdhServerAuthSendFactor.genericBuild PqxdhInitialGenericBuilder.continueRust at supported
  cases next : pqxdh.server_next_key_id state.control with
  | ok value =>
      rw [next] at supported
      rcases value with key | error
      · dsimp only at supported
        cases prepared : pqxdh.server_prepare_commit state.control pending ⟨state.server.identity, state.identityKeyId⟩
            (if (state.server.peers key).isSome then pqxdh.KeyIdAvailability.Occupied else .Available) with
        | ok value =>
            rw [prepared] at supported
            rcases value with candidate | error
            · obtain ⟨available, sameKey⟩ := PqxdhDeploymentCompileRegistration.prepare_key _ _ _ _ candidate prepared
              rw [next] at sameKey
              have keyEq : key = candidate.key_id := by cases sameKey; rfl
              have vacant : state.server.peers candidate.key_id = none := by
                rw [← keyEq]
                by_contra occupied
                rw [Option.isSome_iff_ne_none.mpr occupied] at available
                simp at available
              have counter := (PqxdhRegistrationResponse.prepared_counter state.control pending
                ⟨state.server.identity, state.identityKeyId⟩ _ candidate prepared).2.2
              exact candidateW_shape associatedData write _ calls aux writes initial candidate counter data metadata
                state vacant result supported
            · simp only [support_pure, Set.mem_singleton_iff] at supported
              subst supported
              rfl
        | fail error =>
            rw [prepared] at supported
            simp only [support_pure, Set.mem_singleton_iff] at supported
            subst supported
            trivial
        | div =>
            rw [prepared] at supported
            simp only [support_pure, Set.mem_singleton_iff] at supported
            subst supported
            trivial
      · simp only [support_pure, Set.mem_singleton_iff] at supported
        subst supported
        rfl
  | fail error =>
      rw [next] at supported
      simp only [support_pure, Set.mem_singleton_iff] at supported
      subst supported
      trivial
  | div =>
      rw [next] at supported
      simp only [support_pure, Set.mem_singleton_iff] at supported
      subst supported
      trivial

end Generic

def NativeAllocation (before : PqxdhServerAuthEntryFactor.ServerState) :
    RustM (Option Response × PqxdhServerAuthEntryFactor.ServerState) → Prop
  | .ok (none, after) => after.control = before.control
  | .ok (some response, after) => response.keyId = after.control.last_key_id
  | _ => True

/-- Replacing the private send chains by labels leaves the exact allocation relation unchanged. -/
theorem free_allocation (write : ResponseFields → Option Pqxdh.Bytes)
    (associatedData : PqxdhTranscriptAd.AssociatedData) (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (factor : PqxdhServerAuthSendFactor.Factor)
    (pending : pqxdh.PendingServerRegistration) (data : Option Pqxdh.Bytes)
    (server : PqxdhServerAuthEntryFactor.ServerState)
    (result : RustM (Option Response × PqxdhServerAuthEntryFactor.ServerState))
    (supported : result ∈ support (simulateQ (writeImpl write)
      (PqxdhDeploymentSplitFactor.freeBuild associatedData source factor pending data server))) :
    NativeAllocation server result := by
  rw [← PqxdhDeploymentSplitFactor.factored_free associatedData (writeImpl write) source factor pending data server]
    at supported
  unfold PqxdhServerAuthLoggedSendFactor.factored at supported
  rw [support_map] at supported
  obtain ⟨inner, member, rfl⟩ := supported
  have shape := generic_allocation write associatedData _ (fun request => writeImpl write (.inr request))
    (fun fields bytes written => by
      change bytes ∈ support (pure (write fields) : OracleComp TailSpec _) at written
      rw [support_pure, Set.mem_singleton_iff] at written
      exact written) _ pending data associatedData _ inner member
  rcases inner with ⟨(_ | response), after⟩ | error | _
  · change after.control = server.control
    exact shape
  · change response.keyId = after.control.last_key_id
    exact shape
  · trivial
  · trivial

/-- The actual factored hidden service inherits the allocation relation before the source scheduler settles its Rust result. -/
theorem hidden_allocation (setup : Setup baseSpec KemSK) (codec : Codec Reader WireResponse) (checks : Checks)
    (value : PqxdhRegistrationJointKemEntryFactor.Output) (token : PqxdhServerRelatedRootConsumer.Returned)
    (data : Option Pqxdh.Bytes) (associatedData : PqxdhTranscriptAd.AssociatedData)
    (server : PqxdhServerAuthEntryFactor.ServerState)
    (primitive : RawCtxSharedPrimitive.SharedState (List RawCtxSourceSend.SealContext))
    (result : RustM (Option Response × PqxdhServerAuthEntryFactor.ServerState) ×
      RawCtxSharedPrimitive.SharedState (List RawCtxSourceSend.SealContext))
    (supported : result ∈ support
      (((PqxdhRegistrationJointKemEntryFactor.factoredHidden setup codec checks value).hiddenBuild
        token data associatedData server).run primitive)) : NativeAllocation server result.1 := by
  apply free_allocation codec.write2 associatedData setup.source (PqxdhServerAuthCtxMaterial.factor value)
    token.pending data server result.1
  apply OracleComp.support_simulateQ_run'_subset (PqxdhServerAuthExperiment.tailImpl setup codec checks) _ primitive
  rw [StateT.run'_eq, support_map]
  refine ⟨result, ?_, rfl⟩
  rw [← PqxdhDeploymentIdealPostGoodBuild.factored_logged]
  exact supported

/-- Settling a hidden build updates the public counter exactly from its returned response. A failed optional write keeps the old counter, while its separate cache and seal-log effects remain unrestricted. -/
theorem hidden_build_assignment (setup : Setup baseSpec KemSK) (codec : Codec Reader WireResponse) (checks : Checks)
    (value : PqxdhRegistrationJointKemEntryFactor.Output) (session : Nat) (data : Option Pqxdh.Bytes)
    (before : PqxdhServerAuthNative.NativeState KemSK)
    (result : Option Response × PqxdhServerAuthNative.NativeState KemSK)
    (supported : result ∈ support ((PqxdhDeploymentIdealSteps.buildHidden (KemSK := KemSK)
      (PqxdhRegistrationJointKemEntryFactor.factoredHidden setup codec checks value) session data).run before)) :
    (result.1.map Response.keyId).getD before.2.server.control.last_key_id =
      result.2.2.server.control.last_key_id := by
  unfold PqxdhDeploymentIdealSteps.buildHidden at supported
  rw [PqxdhDeploymentBackend.nativeGet_bind] at supported
  split at supported
  · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
    subst supported
    rfl
  · rename_i token found
    split at supported
    · rw [PqxdhDeploymentBackend.nativeSet_run_bind] at supported
      simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
      subst supported
      rfl
    rw [StateT.run_bind, mem_support_bind_iff] at supported
    obtain ⟨hashed, hashing, supported⟩ := supported
    simp only [PqxdhServerAuthNative.nativeHash, StateT.run, support_map, Set.mem_image] at hashing
    obtain ⟨⟨digest, cache⟩, _, rfl⟩ := hashing
    rw [PqxdhDeploymentBackend.nativeGet_bind, PqxdhDeploymentBackend.nativeCoins_bind, mem_support_bind_iff]
      at supported
    obtain ⟨built, builtMember, supported⟩ := supported
    simp only [PqxdhServerAuthNative.nativeSet, StateT.run] at supported
    subst supported
    have shape := hidden_allocation setup codec checks value token data (PqxdhTranscriptAd.adOf digest)
      before.2.server ([], cache) built builtMember
    rcases built with ⟨⟨(_ | response), after⟩ | error | _, primitive⟩
    · exact (congrArg (fun control => control.last_key_id) shape).symm
    · exact shape
    · rfl
    · rfl

/-- The actual selected-accept marker tail changes session and replay bookkeeping while preserving allocation control. -/
theorem marker_tail_counter (hmac : PqxdhSecretInputKdf.HmacSha512) (index : Nat) (serverKeyId : Aeneas.Std.U64)
    (publicIdentity : PqxdhJointIdentity.PublicIdentity) (state : PqxdhServerAuthExperiment.GameState KemSK)
    (collected : Option (PqxdhRegistrationJointKemOpaqueClient.Input Reader) × List Pqxdh.Bytes)
    (marker : ∀ input, collected.1 = some input → input.shared = .challenge)
    (before : PqxdhServerAuthNative.NativeState KemSK × Option (Nat × PqxdhDeploymentIdealSlots.Coord))
    (result : Option Nat × (PqxdhServerAuthNative.NativeState KemSK ×
      Option (Nat × PqxdhDeploymentIdealSlots.Coord)))
    (supported : result ∈ support ((simulateQ (PqxdhDeploymentIdealSteps.tailCE hmac index)
      (PqxdhRegistrationJointKemOpaqueTail.tail serverKeyId publicIdentity state collected)).run before)) :
    result.2.1.2.server.control = state.server.control := by
  unfold PqxdhRegistrationJointKemOpaqueTail.tail at supported
  simp only [simulateQ_bind, StateT.run_bind, simulateQ_spec_query, mem_support_bind_iff] at supported
  obtain ⟨installed, installedMember, supported⟩ := supported
  change installed ∈ support ((fun answer => (answer.1, (answer.2, before.2))) <$>
    PqxdhDeploymentIdealSteps.liftS ((PqxdhRegistrationJointKemOpaqueTail.mutation
      (.install _)).run before.1)) at installedMember
  simp only [support_map, support_liftComp, PqxdhRegistrationJointKemOpaqueTail.mutation,
    PqxdhServerAuthNative.nativeSet, PqxdhServerAuthNative.localState, StateT.run, support_pure,
    Set.image_singleton, Set.mem_singleton_iff] at installedMember
  subst installedMember
  rcases found : collected.1 with _ | input
  · simp only [found, simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
    subst supported
    rfl
  · simp only [found, simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at supported
    obtain ⟨returned, returnedMember, supported⟩ := supported
    obtain ⟨⟨consumed, stateEq⟩, _⟩ := PqxdhDeploymentIdealPostGood.tailCE_client_footprint hmac index
      state.server.control ⟨PqxdhRootTableInitialization.rootArray publicIdentity.ed25519, serverKeyId⟩
      input (marker input found) _ returned returnedMember
    rcases outcome : returned.1 with (_ | token) | _ | _ <;> simp only [outcome] at supported
    · simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
      subst supported
      rw [stateEq]
    · simp only [simulateQ_bind, StateT.run_bind, simulateQ_spec_query, mem_support_bind_iff,
        simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
      obtain ⟨published, publishedMember, rfl⟩ := supported
      change published ∈ support ((fun answer => (answer.1, (answer.2, returned.2.2))) <$>
        PqxdhDeploymentIdealSteps.liftS
          ((PqxdhRegistrationJointKemOpaqueTail.mutation (.publish _ _)).run returned.2.1)) at publishedMember
      simp only [support_map, support_liftComp, PqxdhRegistrationJointKemOpaqueTail.mutation,
        PqxdhServerAuthNative.nativeModify, PqxdhServerAuthNative.localState, StateT.run, support_pure,
        Set.image_singleton, Set.mem_singleton_iff] at publishedMember
      subst publishedMember
      rw [stateEq]
    · simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
      subst supported
      rw [stateEq]
    · simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
      subst supported
      rw [stateEq]

/-- The selected verified accept's native prefix and marker continuation cannot allocate a response ID. -/
theorem accept_active_counter (setup : Setup baseSpec KemSK) (codec : Codec Reader WireResponse) (checks : Checks)
    (seed : PqxdhJointIdentity.IdentitySeed) (challenge : PqxdhKemIndCca.MlKem768Ciphertext)
    (verified : PqxdhServerRootPreparation.Verified Reader) (before : PqxdhServerAuthNative.NativeState KemSK)
    (result : PqxdhDeploymentIdealSteps.AcceptOut × PqxdhServerAuthNative.NativeState KemSK)
    (supported : result ∈ support
      ((PqxdhDeploymentIdealSteps.acceptActive setup codec checks seed challenge verified).run before)) :
    result.2.2.server.control = before.2.server.control := by
  unfold PqxdhDeploymentIdealSteps.acceptActive at supported
  simp only [StateT.run, mem_support_bind_iff] at supported
  obtain ⟨pre, _, supported⟩ := supported
  cases ephemeral : pre.1.1 with
  | none =>
      simp only [ephemeral, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at supported
      obtain ⟨reply, member, rfl⟩ := supported
      simp only [PqxdhDeploymentIdealSteps.liftS, support_liftComp,
        PqxdhRegistrationJointServerAccept.tail, PqxdhServerAuthNative.nativeSet,
        ] at member
      subst member
      rfl
  | some scalar =>
      simp only [ephemeral, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at supported
      obtain ⟨prepared, preparedMember, answer, answerMember, rfl⟩ := supported
      rw [PqxdhDeploymentIdealSteps.liftS, support_liftComp] at preparedMember
      have marker := PqxdhDeploymentIdealKeymatch.program_marker _ verified scalar
        (PqxdhAcceptedRegistration.ciphertextArray challenge) .challenge pre.2 prepared preparedMember
      exact marker_tail_counter setup.hmac before.2.sessions setup.serverKeyId (setup.joint.publicKeys seed)
        before.2 prepared marker (before, none) answer answerMember

/-- The inactive selected accept is the existing logged native attempt; forgetting that private log preserves its full state. -/
theorem accept_inactive_counter (setup : Setup baseSpec KemSK) (codec : Codec Reader WireResponse) (checks : Checks)
    (seed : PqxdhJointIdentity.IdentitySeed) (raw : Pqxdh.Bytes) (before : PqxdhServerAuthNative.NativeState KemSK)
    (result : PqxdhDeploymentIdealSteps.AcceptOut × PqxdhServerAuthNative.NativeState KemSK)
    (supported : result ∈ support
      ((PqxdhDeploymentIdealSteps.acceptInactive setup codec checks seed raw).run before)) :
    result.2.2.server.control.last_key_id = before.2.server.control.last_key_id := by
  simp only [PqxdhDeploymentIdealSteps.acceptInactive, StateT.run, support_map,
    PqxdhDeploymentIdealSteps.liftS, support_liftComp] at supported
  obtain ⟨logged, loggedMember, rfl⟩ := supported
  have plain : (logged.1.1, logged.2) ∈ support
      ((PqxdhServerAuthNative.nativeAccept setup codec checks seed
        PqxdhRegistrationSchedule.observationScalar raw).run before) := by
    rw [← PqxdhDeploymentLaterServerNative.acceptLogged_fst, support_map]
    exact ⟨logged, loggedMember, rfl⟩
  apply native_noBuild setup codec checks seed (.inl (.inr (.accept raw)))
    (by simp [PqxdhRegistrationJointRevealCosts.sourceKind, PqxdhRegistrationSchedule.sourceKind])
    (⟨before, [], fun _ => none⟩ : PqxdhRegistrationSchedule.State KemSK)
    (logged.1.1, ⟨logged.2, [], fun _ => none⟩)
  change _ ∈ support ((fun answer : Option Nat × PqxdhServerAuthNative.NativeState KemSK => (answer.1,
    (⟨answer.2, [], fun _ => none⟩ : PqxdhRegistrationSchedule.State KemSK))) <$> _)
  rw [support_map]
  exact ⟨(logged.1.1, logged.2), plain, rfl⟩

theorem accept_exposed_counter (setup : Setup baseSpec KemSK) (codec : Codec Reader WireResponse) (checks : Checks)
    (seed : PqxdhJointIdentity.IdentitySeed) (chosen : PqxdhLiveKemReservation.Pair KemSK)
    (challenge : PqxdhKemIndCca.MlKem768Ciphertext) (raw : Pqxdh.Bytes)
    (before : PqxdhServerAuthNative.NativeState KemSK)
    (result : PqxdhDeploymentIdealSteps.AcceptOut × PqxdhServerAuthNative.NativeState KemSK)
    (supported : result ∈ support
      ((PqxdhDeploymentIdealSteps.acceptExposed setup codec checks seed chosen challenge raw).run before)) :
    result.2.2.server.control.last_key_id = before.2.server.control.last_key_id := by
  unfold PqxdhDeploymentIdealSteps.acceptExposed at supported
  split at supported
  · split_ifs at supported
    · exact congrArg (fun control => control.last_key_id)
        (accept_active_counter setup codec checks seed challenge _ before result supported)
    · exact accept_inactive_counter setup codec checks seed raw before result supported
  · exact accept_inactive_counter setup codec checks seed raw before result supported

section Middle
open PqxdhDeploymentIdealPostSource (Mid sourceMid realMid)
open PqxdhDeploymentIdealParams (Target Params)
variable (setup : Setup baseSpec KemSK) (codec : Codec Reader WireResponse)
    (route : RawCtxServerRouting.SenderDecoder) (checks : Checks) {count : Nat}
    (target : Target count) (parameters : Params KemSK count)
    (created : PqxdhLiveServerConstruction.Created Unit)

theorem real_assignment (query : (PqxdhDeploymentRecordCache.SourceSpec KemSK).Domain)
    (before : Mid KemSK) (result : (PqxdhDeploymentRecordCache.SourceSpec KemSK).Range query × Mid KemSK)
    (supported : result ∈ support ((realMid setup codec checks target parameters created query).run before)) :
    assignedAfter query result.1 before.joint.shared.2.server.control.last_key_id =
      result.2.joint.shared.2.server.control.last_key_id := by
  unfold realMid at supported
  simp only [StateT.run] at supported
  rw [support_map] at supported
  obtain ⟨inner, member, rfl⟩ := supported
  exact sourcePool_assignment setup codec checks created.seed created.server.server.metadata.identityIndex
    (parameters.pool target) query before.joint inner member

theorem middle_hidden_build (session : Nat) (data : Option Pqxdh.Bytes) (before : Mid KemSK)
    (hidden : PqxdhDeploymentIdealPostSource.buildHiddenAt before session = true)
    (result : Option Response × Mid KemSK)
    (supported : result ∈ support ((sourceMid setup codec route checks target parameters created
      (.inl (.inr (.build session data)))).run before)) :
    (result.1.map Response.keyId).getD before.joint.shared.2.server.control.last_key_id =
      result.2.joint.shared.2.server.control.last_key_id := by
  let copies := PqxdhDeploymentCompile.Local.empty
  let logged := { copies with log := PqxdhDeploymentCompile.logReply copies.log (.build session data) result.1 }
  have forwarded : (result.1, (logged, result.2)) ∈ support
      ((PqxdhDeploymentIdealPostSource.compiledMid setup codec route checks target parameters created
        (.inr (.build session data))).run (copies, before)) := by
    change _ ∈ support ((fun value => (value.1.1, (value.1.2, value.2))) <$>
      (simulateQ (sourceMid setup codec route checks target parameters created)
        ((PqxdhDeploymentCompile.forwardLogged (.build session data) (.build session data) id).run copies)).run before)
    rw [PqxdhDeploymentIdealPostSource.compiledMid_forward, Functor.map_map, support_map]
    exact ⟨result, supported, rfl⟩
  obtain ⟨_, _, value, after, member, projected⟩ :=
    PqxdhDeploymentIdealPostGoodBuild.compiledMid_buildHidden setup codec route checks target parameters created
      session data copies before hidden (result.1, (logged, result.2)) forwarded
  have counter := congrArg (fun state => state.shared.2.server.control.last_key_id) projected
  change result.2.joint.shared.2.server.control.last_key_id = after.2.server.control.last_key_id at counter
  rw [counter]
  exact hidden_build_assignment setup codec checks value session data before.joint.shared (result.1, after) member

theorem middle_hidden_finish (address : Nat) (raw : Pqxdh.Bytes) (before : Mid KemSK)
    (hidden : PqxdhDeploymentIdealPostSource.finishHiddenAt target before address = true)
    (result : Option Pqxdh.Bytes × Mid KemSK)
    (supported : result ∈ support ((sourceMid setup codec route checks target parameters created
      (.inl (.inr (.finish address raw)))).run before)) :
    result.2.joint.shared.2.server.control.last_key_id = before.joint.shared.2.server.control.last_key_id := by
  have sent := (of_decide_eq_true hidden).2.2
  rcases found : before.joint.owners[address]? with _ | entry
  · exfalso
    unfold PqxdhDeploymentIdealSteps.initSentAt at sent
    simp [PqxdhRegistrationJointSchedule.source, List.getElem?_map, found] at sent
  rw [PqxdhDeploymentIdealPostChallenge.sourceMid_challenge setup codec route checks target parameters created
    address raw before hidden entry found, support_map] at supported
  obtain ⟨inner, member, rfl⟩ := supported
  have frame := (PqxdhDeploymentIdealPostGoodFinish.hashedOwnerCE_footprint setup codec checks parameters
    (before.joint.inits address) raw entry.owner (before.joint.shared, none) (before.backend.2.1, before.backend.1) inner member).1
  exact congrArg (fun game => game.server.control.last_key_id) frame

set_option backward.isDefEq.respectTransparency false in
theorem middle_selected_accept (raw : Pqxdh.Bytes) (before : Mid KemSK)
    (selected : before.backend.2.2.accepts = target.accept) (result : Option Nat × Mid KemSK)
    (supported : result ∈ support ((sourceMid setup codec route checks target parameters created
      (.inl (.inr (.accept raw)))).run before)) :
    result.2.joint.shared.2.server.control.last_key_id = before.joint.shared.2.server.control.last_key_id := by
  have selectedRun : (sourceMid setup codec route checks target parameters created
      (.inl (.inr (.accept raw)))).run before =
      (PqxdhDeploymentIdealPostSource.idealMid setup codec route checks target parameters created
        ⟨.accept raw, trivial⟩).run before := by
    change (if before.backend.2.2.accepts = target.accept then _ else _) = _
    exact ite_eq_left selected
  rw [selectedRun, PqxdhDeploymentIdealPostHidden.idealMid_run, support_map] at supported
  obtain ⟨inner, member, rfl⟩ := supported
  have openMember : inner.1 ∈ support
      ((PqxdhDeploymentIdealSteps.idealProg setup codec route checks target parameters
        (PqxdhRegistrationJointKemEntryFactor.factoredHidden setup codec checks) created
        ⟨.accept raw, trivial⟩).run
          (PqxdhDeploymentIdealSlots.detach (PqxdhDeploymentIdealPostSource.toX before))) := by
    apply OracleComp.support_simulateQ_run'_subset
      (PqxdhRegistrationJointKemSecondEntry.slotImpl PqxdhDeploymentSeedSplit.tableService) _
      (before.backend.2.1, before.backend.1)
    rw [StateT.run'_eq, support_map]
    exact ⟨inner, member, rfl⟩
  change inner.1 ∈ support ((PqxdhDeploymentIdealSteps.acceptStep setup codec route checks target parameters
    created raw).run (PqxdhDeploymentIdealSlots.detach (PqxdhDeploymentIdealPostSource.toX before))) at openMember
  simp only [PqxdhDeploymentIdealSteps.acceptStep, StateT.run,
    PqxdhDeploymentIdealSlots.detach, PqxdhDeploymentIdealPostSource.toX, selected, ite_true,
    support_map] at openMember
  obtain ⟨accepted, acceptedMember, same⟩ := openMember
  have counter := accept_exposed_counter setup codec checks created.seed parameters.chosen parameters.challenge
    raw before.joint.shared accepted acceptedMember
  change inner.1.2.base.native.shared.2.server.control.last_key_id = before.joint.shared.2.server.control.last_key_id
  rw [← same]
  exact counter

/-- Every source14 step of the complete middle interpreter has the exact reply-derived assignment counter, including all three hidden registration branches. -/
theorem sourceMid_assignment (query : (PqxdhDeploymentRecordCache.SourceSpec KemSK).Domain)
    (before : Mid KemSK) (result : (PqxdhDeploymentRecordCache.SourceSpec KemSK).Range query × Mid KemSK)
    (supported : result ∈ support ((sourceMid setup codec route checks target parameters created query).run before)) :
    assignedAfter query result.1 before.joint.shared.2.server.control.last_key_id =
      result.2.joint.shared.2.server.control.last_key_id := by
  rcases query with (coin | command) | read
  · exact real_assignment setup codec checks target parameters created _ before result supported
  · cases command with
    | accept raw =>
        by_cases selected : before.backend.2.2.accepts = target.accept
        · exact (middle_selected_accept setup codec route checks target parameters created raw before selected
            result supported).symm
        · apply real_assignment setup codec checks target parameters created _ before result
          simpa only [sourceMid, StateT.run, selected, ite_false] using supported
    | build session data =>
        by_cases hidden : PqxdhDeploymentIdealPostSource.buildHiddenAt before session = true
        · exact middle_hidden_build setup codec route checks target parameters created session data before hidden
            result supported
        · apply real_assignment setup codec checks target parameters created _ before result
          simpa only [sourceMid, StateT.run, hidden, Bool.false_eq_true, ite_false] using supported
    | finish address raw =>
        by_cases hidden : PqxdhDeploymentIdealPostSource.finishHiddenAt target before address = true
        · exact (middle_hidden_finish setup codec route checks target parameters created address raw before hidden
            result supported).symm
        · apply real_assignment setup codec checks target parameters created _ before result
          simpa only [sourceMid, StateT.run, hidden, Bool.false_eq_true, ite_false] using supported
    | _ => exact real_assignment setup codec checks target parameters created _ before result supported
  · exact real_assignment setup codec checks target parameters created _ before result supported

/-- A source program with no build keeps allocation control even when its other registration steps use hidden roots. -/
theorem sourceMid_noBuild {X : Type} (work : OracleComp (PqxdhDeploymentRecordCache.SourceSpec KemSK) X)
    (quiet : work.IsQueryBoundP
      (fun query => PqxdhRegistrationJointRevealCosts.sourceKind (KemSK := KemSK) query = .inl 4) 0)
    (before : Mid KemSK) (result : X × Mid KemSK)
    (supported : result ∈ support ((simulateQ (sourceMid setup codec route checks target parameters created)
      work).run before)) :
    result.2.joint.shared.2.server.control.last_key_id = before.joint.shared.2.server.control.last_key_id := by
  induction work using OracleComp.inductionOn generalizing before result with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
      subst supported
      rfl
  | query_bind query next ih =>
      rw [isQueryBoundP_query_bind_iff] at quiet
      have other : PqxdhRegistrationJointRevealCosts.sourceKind (KemSK := KemSK) query ≠ .inl 4 := by
        rcases quiet.1 with absent | impossible
        · exact absent
        · omega
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at supported
      obtain ⟨middle, reached, supported⟩ := supported
      have kept := sourceMid_assignment setup codec route checks target parameters created query before middle reached
      rw [assignedAfter_other query other] at kept
      have tail := quiet.2 middle.1
      simp only [other, ite_false] at tail
      exact (ih middle.1 tail middle.2 result supported).trans kept.symm

end Middle

end BeaconcryptCore.Computational.CborRawMiddleCounter

/-- info: 'BeaconcryptCore.Computational.CborRawMiddleCounter.hidden_allocation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawMiddleCounter.hidden_allocation

/-- info: 'BeaconcryptCore.Computational.CborRawMiddleCounter.hidden_build_assignment' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawMiddleCounter.hidden_build_assignment

/-- info: 'BeaconcryptCore.Computational.CborRawMiddleCounter.sourceMid_assignment' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawMiddleCounter.sourceMid_assignment

-- Exact dependency observations for all public helper theorems.

/-- info: 'BeaconcryptCore.Computational.CborRawMiddleCounter.assignedAfter_other' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawMiddleCounter.assignedAfter_other

/-- info: 'BeaconcryptCore.Computational.CborRawMiddleCounter.native_noBuild' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawMiddleCounter.native_noBuild

/-- info: 'BeaconcryptCore.Computational.CborRawMiddleCounter.native_assignment' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawMiddleCounter.native_assignment

/-- info: 'BeaconcryptCore.Computational.CborRawMiddleCounter.pool_assignment' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawMiddleCounter.pool_assignment

/-- info: 'BeaconcryptCore.Computational.CborRawMiddleCounter.sourcePool_assignment' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawMiddleCounter.sourcePool_assignment

/-- info: 'BeaconcryptCore.Computational.CborRawMiddleCounter.allocation_of_shape' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawMiddleCounter.allocation_of_shape

/-- info: 'BeaconcryptCore.Computational.CborRawMiddleCounter.generic_allocation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawMiddleCounter.generic_allocation

/-- info: 'BeaconcryptCore.Computational.CborRawMiddleCounter.free_allocation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawMiddleCounter.free_allocation

/-- info: 'BeaconcryptCore.Computational.CborRawMiddleCounter.marker_tail_counter' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawMiddleCounter.marker_tail_counter

/-- info: 'BeaconcryptCore.Computational.CborRawMiddleCounter.accept_active_counter' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawMiddleCounter.accept_active_counter

/-- info: 'BeaconcryptCore.Computational.CborRawMiddleCounter.accept_inactive_counter' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawMiddleCounter.accept_inactive_counter

/-- info: 'BeaconcryptCore.Computational.CborRawMiddleCounter.accept_exposed_counter' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawMiddleCounter.accept_exposed_counter

/-- info: 'BeaconcryptCore.Computational.CborRawMiddleCounter.real_assignment' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawMiddleCounter.real_assignment

/-- info: 'BeaconcryptCore.Computational.CborRawMiddleCounter.middle_hidden_build' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawMiddleCounter.middle_hidden_build

/-- info: 'BeaconcryptCore.Computational.CborRawMiddleCounter.middle_hidden_finish' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawMiddleCounter.middle_hidden_finish

/-- info: 'BeaconcryptCore.Computational.CborRawMiddleCounter.middle_selected_accept' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawMiddleCounter.middle_selected_accept

/-- info: 'BeaconcryptCore.Computational.CborRawMiddleCounter.sourceMid_noBuild' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawMiddleCounter.sourceMid_noBuild
