-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhDeploymentIdealPostReduce
import BeaconcryptCore.Computational.PqxdhDeploymentSplitFactor

/-!
# CE-3's invariant across the marked build (CE-11b, unit U6, fourth part)

The CE side of the invariant of the middle execution (`PqxdhDeploymentIdealPostReduce.MiddleInv`) must survive the marked build: the build of the marked session while it has a pending token, which the middle source handler answers by the ideal registration's hidden build, the factored Server response tail at the value stored at the mark's coordinates. CE-3's preservation of its invariant `PqxdhDeploymentCompileInvariant.Good` by a build (`good_build`) reads the footprint of the real build (`PqxdhDeploymentCompileFootprint.build_footprint`). This module proves the same footprint for the factored build at any 108-byte value, and the preservation for the marked build of the middle execution.

- The generic Server build with its Phase 2 writer: `WBuilt` (a diagnostic, no publication with the state kept, or one publication at a vacant key ID of a candidate with a given property, whose response bytes are the writer's output on the candidate's response fields) with `afterInitializationW_shape`, `continueRust_shape`, `candidateW_shape` and `genericBuildW_shape` (the candidate carries the Server's identity and the pending registration's Beacon identity, from `PqxdhServerAuthNegativeControl.prepare_commit_fields`), for a writer callback that answers the writer's output. This strengthens `PqxdhDeploymentIdealEnvBuild.genericBuild_shape`.
- The factored build with the codec's writer: `writeImpl` (the free factored build's tail requests with the Phase 2 writer answered by a writer function and every other request forwarded), `tailImpl_write` (the native logged tail factors through it), `factored_logged` (the logged factored build is the native logged tail run on the free factored build with the writer answered by the codec), `NBuilt` and `freeWrite_shape` (the native shape with the written response), and `hiddenBuild_shape` (every outcome of the hidden build of the factored services at any value).
- `buildHidden_footprint`: the marked build at any value (`PqxdhDeploymentIdealSteps.buildHidden` with `PqxdhRegistrationJointKemEntryFactor.factoredHidden`) has the footprint of CE-3's `build_footprint`.
- `BuildFootprint` and `good_of_build`: CE-3's invariant survives every Server build with that footprint that keeps the owners, with the reply logged, under the approved `Phase2ReadBack` contract (the argument of `good_build`, from the footprint alone).
- `compiledMid_buildHidden` and `good_buildHidden`: the compiled marked build of the middle execution logs the reply, keeps the accept counter, and changes the native state of the annotated source state as the marked build at some value does; hence it keeps CE-3's invariant on the local copies and the native state of the annotated source state.

These are support facts and invariant preservation under the approved Phase 2 read-back contract. They charge nothing and make no security claim.
-/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete PqxdhRefinement

set_option autoImplicit false

namespace BeaconcryptCore.Computational.PqxdhDeploymentIdealPostGoodBuild
open PqxdhServerAuthExperiment (Setup Codec Checks GameState)
open PqxdhServerRegistrationPublication (AuxSpec Response ResponseFields responseFields TailSpec)

/-! ### The generic Server build with its Phase 2 writer -/

section WriterShape
variable {Kernel Metadata PeerMetadata Consumed : Type} {ι' : Type} {spec' : OracleSpec ι'}
open PqxdhInitialGenericPublication (State)

/-- A generic Server build's result with its written response: a diagnostic, no publication with the state kept, or one publication at a key ID that was vacant, of a candidate with the given property, whose response bytes are the writer's output on the response fields of the candidate and the first-send ciphertext. -/
def WBuilt (write : ResponseFields → Option Pqxdh.Bytes) (good : pqxdh.ServerRegistrationCandidate → Prop)
    (state : State Kernel Metadata PeerMetadata Consumed) (metadata : PeerMetadata) :
    RustM (Option Response × State Kernel Metadata PeerMetadata Consumed) → Prop
  | .ok (none, after) => after = state
  | .ok (some response, after) => ∃ candidate kernel encrypted, good candidate ∧ response.keyId = candidate.key_id ∧
      state.server.peers candidate.key_id = none ∧
      after = PqxdhInitialGenericPublication.publish state candidate kernel metadata ∧
      write (responseFields candidate encrypted) = some response.serialized
  | _ => True

/-- The generic first send and Phase 2 writing, with a writer callback that answers the writer's output, publish the candidate at its key ID with the written response, or keep the state. -/
theorem afterInitializationW_shape (write : ResponseFields → Option Pqxdh.Bytes)
    (good : pqxdh.ServerRegistrationCandidate → Prop) (calls : RawCtxChainOwner.Calls Kernel (OracleComp spec'))
    (aux : QueryImpl AuxSpec (OracleComp spec'))
    (writes : ∀ fields, ∀ bytes ∈ support (aux (.write fields)), bytes = write fields)
    (candidate : pqxdh.ServerRegistrationCandidate) (holds : good candidate)
    (authenticated : Pqxdh.Bytes) (kernel : Kernel) (metadata : PeerMetadata)
    (state : State Kernel Metadata PeerMetadata Consumed) (vacant : state.server.peers candidate.key_id = none) :
    ∀ result ∈ support (PqxdhInitialGenericPublication.afterInitialization calls aux candidate authenticated kernel
      metadata state), WBuilt write good state metadata (.ok result) := by
  intro result supported
  unfold PqxdhInitialGenericPublication.afterInitialization at supported
  rw [mem_support_bind_iff] at supported
  obtain ⟨⟨advanced, encrypted⟩, _, member⟩ := supported
  rw [mem_support_bind_iff] at member
  obtain ⟨_, _, member⟩ := member
  cases encrypted with
  | none =>
      simp only [support_pure, Set.mem_singleton_iff] at member
      subst member
      rfl
  | some encrypted =>
      dsimp only at member
      rw [mem_support_bind_iff] at member
      obtain ⟨serialized, written, member⟩ := member
      cases serialized with
      | none =>
          simp only [support_pure, Set.mem_singleton_iff] at member
          subst member
          rfl
      | some serialized =>
          simp only [support_pure, Set.mem_singleton_iff] at member
          subst member
          exact ⟨candidate, advanced, encrypted, holds, rfl, vacant, rfl, (writes _ _ written).symm⟩

/-- A property of Rust results that holds at every diagnostic and on every continuation holds on the continued result (`continueRust_shape`, restated without importing that module). -/
theorem continueRust_shape {α β : Type} (value : RustM α) (next : α → OracleComp spec' (RustM β))
    (property : RustM β → Prop) (failed : ∀ error, property (.fail error)) (diverged : property .div)
    (continued : ∀ inner, ∀ result ∈ support (next inner), property result) :
    ∀ result ∈ support (PqxdhInitialGenericBuilder.continueRust value next), property result := by
  intro result supported
  cases value with
  | ok inner => exact continued inner result supported
  | fail error =>
      simp only [PqxdhInitialGenericBuilder.continueRust, support_pure, Set.mem_singleton_iff] at supported
      subst supported
      exact failed error
  | div =>
      simp only [PqxdhInitialGenericBuilder.continueRust, support_pure, Set.mem_singleton_iff] at supported
      subst supported
      exact diverged

/-- The generic candidate admission and first send, with a writer callback that answers the writer's output, publish only the given candidate, at its vacant key ID, with the written response. -/
theorem candidateW_shape (write : ResponseFields → Option Pqxdh.Bytes)
    (good : pqxdh.ServerRegistrationCandidate → Prop) (calls : RawCtxChainOwner.Calls Kernel (OracleComp spec'))
    (aux : QueryImpl AuxSpec (OracleComp spec'))
    (writes : ∀ fields, ∀ bytes ∈ support (aux (.write fields)), bytes = write fields)
    (initial : RustM Kernel) (candidate : pqxdh.ServerRegistrationCandidate) (holds : good candidate)
    (data : Option Pqxdh.Bytes) (metadata : PeerMetadata) (state : State Kernel Metadata PeerMetadata Consumed)
    (vacant : state.server.peers candidate.key_id = none) :
    ∀ result ∈ support (PqxdhInitialGenericBuilder.candidate calls aux initial candidate data metadata state),
      WBuilt write good state metadata result := by
  intro result supported
  unfold PqxdhInitialGenericBuilder.candidate at supported
  rw [mem_support_bind_iff] at supported
  obtain ⟨valid, _, member⟩ := supported
  by_cases invalid : (!valid) = true
  · simp only [invalid, ite_true, support_pure, Set.mem_singleton_iff] at member
    subst member
    rfl
  · simp only [invalid, Bool.false_eq_true, ite_false, mem_support_bind_iff] at member
    obtain ⟨reserved, _, member⟩ := member
    by_cases unreserved : (!reserved) = true
    · simp only [unreserved, ite_true, support_pure, Set.mem_singleton_iff] at member
      subst member
      rfl
    · simp only [unreserved, Bool.false_eq_true, ite_false] at member
      refine continueRust_shape _ _ _ (fun _ => trivial) trivial
        (fun kernel inner innerMember => ?_) result member
      split_ifs at innerMember with empty bounded
      · simp only [support_pure, Set.mem_singleton_iff] at innerMember
        subst innerMember
        rfl
      · rw [mem_support_bind_iff] at innerMember
        obtain ⟨allocated, _, innerMember⟩ := innerMember
        by_cases unallocated : (!allocated) = true
        · simp only [unallocated, ite_true, support_pure, Set.mem_singleton_iff] at innerMember
          subst innerMember
          rfl
        · simp only [unallocated, Bool.false_eq_true, ite_false] at innerMember
          refine continueRust_shape _ _ _ (fun _ => trivial) trivial
            (fun binding final finalMember => ?_) inner innerMember
          rw [support_map] at finalMember
          obtain ⟨published, publishedMember, rfl⟩ := finalMember
          exact afterInitializationW_shape write good calls aux writes candidate holds _ _ metadata state vacant published
            publishedMember
      · simp only [support_pure, Set.mem_singleton_iff] at innerMember
        subst innerMember
        rfl

/-- Every outcome of the generic Server build, with a writer callback that answers the writer's output, is a diagnostic, no publication with the state kept, or one publication at a key ID that was vacant, of a candidate carrying the Server's identity and the pending registration's Beacon identity, with the written response. -/
theorem genericBuildW_shape (write : ResponseFields → Option Pqxdh.Bytes)
    (calls : RawCtxChainOwner.Calls Kernel (OracleComp spec')) (aux : QueryImpl AuxSpec (OracleComp spec'))
    (writes : ∀ fields, ∀ bytes ∈ support (aux (.write fields)), bytes = write fields)
    (initial : RustM Kernel) (pending : pqxdh.PendingServerRegistration)
    (data : Option Pqxdh.Bytes) (metadata : PeerMetadata) (state : State Kernel Metadata PeerMetadata Consumed) :
    ∀ result ∈ support (PqxdhServerAuthSendFactor.genericBuild calls aux initial pending data metadata state),
      WBuilt write (fun candidate => candidate.server_identity_public_key = state.server.identity ∧
        candidate.beacon_identity_public_key = pending.beacon_identity_public_key) state metadata result := by
  intro result supported
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
              have keyEq : key = candidate.key_id := by
                cases sameKey
                rfl
              have vacant : state.server.peers candidate.key_id = none := by
                rw [← keyEq]
                by_contra occupied
                rw [Option.isSome_iff_ne_none.mpr occupied] at available
                simp at available
              have fields := PqxdhServerAuthNegativeControl.prepare_commit_fields _ _ _ _ candidate prepared
              exact candidateW_shape write _ calls aux writes initial candidate ⟨fields.2.1, fields.1⟩ data metadata state
                vacant result supported
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

end WriterShape

/-! ### The factored Server build with the codec's Phase 2 writer -/

section Factored
open PqxdhDeploymentSplitFactor (freeBuild)

/-- The free factored build's tail requests with the Phase 2 writer answered by a writer function; every other request is forwarded. -/
def writeImpl (write : ResponseFields → Option Pqxdh.Bytes) : QueryImpl TailSpec (OracleComp TailSpec)
  | .inl request => liftM (TailSpec.query (.inl request))
  | .inr (.checkIdentity identity) => liftM (TailSpec.query (.inr (.checkIdentity identity)))
  | .inr .reservePeer => liftM (TailSpec.query (.inr .reservePeer))
  | .inr (.reservePlaintext length) => liftM (TailSpec.query (.inr (.reservePlaintext length)))
  | .inr (.erase bytes) => liftM (TailSpec.query (.inr (.erase bytes)))
  | .inr (.write fields) => pure (write fields)

/-- The native logged response tail answers the Phase 2 writer with the codec's writer, so it factors through `writeImpl`. -/
theorem tailImpl_write {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type} (setup : Setup baseSpec KemSK)
    (codec : Codec Reader Response) (checks : Checks) :
    (PqxdhServerAuthExperiment.tailImpl setup codec checks ∘ₛ writeImpl codec.write2) =
      PqxdhServerAuthExperiment.tailImpl setup codec checks := by
  funext query
  rcases query with request | aux
  · simp only [QueryImpl.apply_compose, writeImpl, simulateQ_spec_query]
  · cases aux with
    | write fields =>
        simp only [QueryImpl.apply_compose, writeImpl, simulateQ_pure]
        simp only [PqxdhServerAuthExperiment.tailImpl, PqxdhServerAuthExperiment.nativeTail, QueryImpl.apply_compose,
          PqxdhServerRegistrationPublication.nativeAdapter, simulateQ_spec_query,
          PqxdhRegistrationProtocolState.registrationImpl, PqxdhServerAuthExperiment.tailAux]
    | _ => simp only [QueryImpl.apply_compose, writeImpl, simulateQ_spec_query]

/-- The logged factored build (the hidden build of the factored services) is the native logged tail run on the free factored build with the Phase 2 writer answered by the codec. -/
theorem factored_logged {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type} (setup : Setup baseSpec KemSK)
    (codec : Codec Reader Response) (checks : Checks) (value : PqxdhServerAuthSendFactor.Factor)
    (pending : pqxdh.PendingServerRegistration) (data : Option Pqxdh.Bytes)
    (server : PqxdhServerAuthEntryFactor.ServerState) :
    PqxdhServerAuthLoggedSendFactor.factored (fun entry _ _ => pure (entry, .None))
        (PqxdhServerAuthLoggedSendFactor.loggedPrim setup codec checks) setup.source
        (PqxdhServerAuthLoggedSendFactor.loggedAux setup codec checks) value pending data () server =
      simulateQ (PqxdhServerAuthExperiment.tailImpl setup codec checks)
        (simulateQ (writeImpl codec.write2) (freeBuild setup.source value pending data server)) := by
  rw [← QueryImpl.simulateQ_compose, tailImpl_write]
  exact PqxdhDeploymentSplitFactor.factored_free (PqxdhServerAuthExperiment.tailImpl setup codec checks) setup.source
    value pending data server

/-- A native Server build's result with its written response: a diagnostic, no publication with the Server kept, or one publication at a key ID that was vacant, of a candidate carrying the Server's identity and the pending registration's Beacon identity, whose response bytes are the writer's output on the candidate's response fields. -/
def NBuilt (write : ResponseFields → Option Pqxdh.Bytes) (server : PqxdhServerAuthEntryFactor.ServerState)
    (pending : pqxdh.PendingServerRegistration) :
    RustM (Option Response × PqxdhServerAuthEntryFactor.ServerState) → Prop
  | .ok (none, after) => after = server
  | .ok (some response, after) => ∃ candidate kernel encrypted,
      candidate.server_identity_public_key = server.server.identity ∧
      candidate.beacon_identity_public_key = pending.beacon_identity_public_key ∧
      response.keyId = candidate.key_id ∧ server.server.peers candidate.key_id = none ∧
      after = PqxdhServerRegistrationPublication.publish server candidate kernel () ∧
      write (responseFields candidate encrypted) = some response.serialized
  | _ => True

/-- Every outcome of the free factored build with the Phase 2 writer answered by a writer function has the native shape with its written response. -/
theorem freeWrite_shape (write : ResponseFields → Option Pqxdh.Bytes)
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (value : PqxdhServerAuthSendFactor.Factor)
    (pending : pqxdh.PendingServerRegistration) (data : Option Pqxdh.Bytes)
    (server : PqxdhServerAuthEntryFactor.ServerState) :
    ∀ result ∈ support (simulateQ (writeImpl write) (freeBuild source value pending data server)),
      NBuilt write server pending result := by
  intro result supported
  rw [← PqxdhDeploymentSplitFactor.factored_free (writeImpl write) source value pending data server] at supported
  unfold PqxdhServerAuthLoggedSendFactor.factored at supported
  rw [support_map] at supported
  obtain ⟨inner, member, rfl⟩ := supported
  have shape := genericBuildW_shape write _ (fun request => writeImpl write (.inr request))
    (fun fields bytes written => by
      change bytes ∈ support (pure (write fields) : OracleComp TailSpec _) at written
      rw [support_pure, Set.mem_singleton_iff] at written
      exact written) _ pending data () _ inner member
  have back : PqxdhInitialGenericPublication.native PqxdhServerAuthSendFactor.resolve
      (PqxdhServerAuthSendFactor.embed server) = server :=
    PqxdhServerAuthSendFactor.native_embed RawCtxSelectedChain.unusedChain server
  rcases inner with ⟨(_ | response), after⟩ | error | _
  · change after = _ at shape
    subst shape
    change PqxdhInitialGenericPublication.native PqxdhServerAuthSendFactor.resolve
      (PqxdhServerAuthSendFactor.embed server) = server
    exact back
  · obtain ⟨candidate, kernel, encrypted, ⟨identity, beacon⟩, keyEq, vacant, published, written⟩ := shape
    subst published
    refine ⟨candidate, PqxdhServerAuthSendFactor.resolve kernel, encrypted, identity, beacon, keyEq, ?_, ?_, written⟩
    · simpa only [PqxdhServerAuthSendFactor.embed, Option.map_eq_none_iff] using vacant
    · rw [PqxdhInitialGenericPublication.publish_native, back]
  · trivial
  · trivial

/-- Every outcome of the hidden build of the factored services at any 108-byte value has the native shape with the codec's Phase 2 writer output. -/
theorem hiddenBuild_shape {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type} (setup : Setup baseSpec KemSK)
    (codec : Codec Reader Response) (checks : Checks) (value : PqxdhRegistrationJointKemEntryFactor.Output)
    (token : PqxdhServerRelatedRootConsumer.Returned) (payload : Option Pqxdh.Bytes)
    (server : PqxdhServerAuthEntryFactor.ServerState)
    (s : RawCtxSharedPrimitive.SharedState (List RawCtxSourceSend.SealContext)) :
    ∀ result ∈ support (((PqxdhRegistrationJointKemEntryFactor.factoredHidden setup codec checks value).hiddenBuild
      token payload server).run s), NBuilt codec.write2 server token.pending result.1 := by
  intro result supported
  have inner : result.1 ∈ support (simulateQ (writeImpl codec.write2)
      (freeBuild setup.source (PqxdhServerAuthCtxMaterial.factor value) token.pending payload server)) := by
    apply OracleComp.support_simulateQ_run'_subset (PqxdhServerAuthExperiment.tailImpl setup codec checks) _ s
    rw [StateT.run'_eq, support_map]
    refine ⟨result, ?_, rfl⟩
    rw [← factored_logged]
    exact supported
  exact freeWrite_shape _ _ _ _ _ _ result.1 inner

end Factored

/-! ### The marked build's footprint -/

section Footprint
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type} (setup : Setup baseSpec KemSK)
  (codec : Codec Reader Response) (checks : Checks)

/-- The marked build with the factored services at any 108-byte value (`PqxdhDeploymentIdealSteps.buildHidden`), as CE-3's `PqxdhDeploymentCompileFootprint.build_footprint` for the real build: it never changes the Server identity, key ID or session counter and always removes the session's token; a rejected build keeps the peer map, and a successful build installs exactly one new peer, at the previously unoccupied key ID returned in the response, with the Beacon identity of the consumed token, and returns the Phase 2 writer output of fields carrying the Server's own identity. -/
theorem buildHidden_footprint (value : PqxdhRegistrationJointKemEntryFactor.Output) (session : ℕ)
    (payload : Option Pqxdh.Bytes) (shared : PqxdhServerAuthNative.NativeState KemSK)
    (result : Option PqxdhServerRegistrationPublication.Response × PqxdhServerAuthNative.NativeState KemSK)
    (supported : result ∈ support ((PqxdhDeploymentIdealSteps.buildHidden (KemSK := KemSK)
      (PqxdhRegistrationJointKemEntryFactor.factoredHidden setup codec checks value) session payload).run shared)) :
    result.2.2.server.server.identity = shared.2.server.server.identity ∧
      result.2.2.server.identityKeyId = shared.2.server.identityKeyId ∧ result.2.2.sessions = shared.2.sessions ∧
      (∀ other, other ≠ session → result.2.2.pending other = shared.2.pending other) ∧
      result.2.2.pending session = none ∧
      (result.1 = none → result.2.2.server.server.peers = shared.2.server.server.peers) ∧
      (∀ response, result.1 = some response → ∃ token kernel fields,
        shared.2.pending session = some token ∧ shared.2.server.server.peers response.keyId = none ∧
        result.2.2.server.server.peers = Function.update shared.2.server.server.peers response.keyId
          (some ⟨token.pending.beacon_identity_public_key, kernel, ()⟩) ∧
        codec.write2 fields = some response.serialized ∧ fields.identity = shared.2.server.server.identity) := by
  unfold PqxdhDeploymentIdealSteps.buildHidden at supported
  rw [PqxdhDeploymentBackend.nativeGet_bind] at supported
  split at supported
  · rename_i found
    simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
    subst supported
    exact ⟨rfl, rfl, rfl, fun _ _ => rfl, found, fun _ => rfl, fun _ reply => by cases reply⟩
  · rename_i token found
    rw [PqxdhDeploymentBackend.nativeCoins_bind, mem_support_bind_iff] at supported
    obtain ⟨built, builtMember, supported⟩ := supported
    simp only [PqxdhServerAuthNative.nativeSet, StateT.run] at supported
    subst supported
    have shape := hiddenBuild_shape setup codec checks value token payload shared.2.server ([], shared.2.ctx) built
      builtMember
    refine ⟨?_, ?_, rfl, fun other different => Function.update_of_ne different _ _, Function.update_self .., ?_, ?_⟩
    · rcases built with ⟨⟨(_ | response), after⟩ | error | _, _⟩
      · change after = _ at shape
        subst shape
        rfl
      · obtain ⟨candidate, kernel, encrypted, _, _, _, _, published, _⟩ := shape
        change after = _ at published
        subst published
        rfl
      · rfl
      · rfl
    · rcases built with ⟨⟨(_ | response), after⟩ | error | _, _⟩
      · change after = _ at shape
        subst shape
        rfl
      · obtain ⟨candidate, kernel, encrypted, _, _, _, _, published, _⟩ := shape
        change after = _ at published
        subst published
        rfl
      · rfl
      · rfl
    · intro none
      rcases built with ⟨⟨(_ | response), after⟩ | error | _, _⟩
      · change after = _ at shape
        subst shape
        rfl
      · cases none
      · rfl
      · rfl
    · intro response reply
      rcases built with ⟨⟨(_ | reply'), after⟩ | error | _, _⟩
      · cases reply
      · change some reply' = some response at reply
        cases reply
        obtain ⟨candidate, kernel, encrypted, identity, beacon, keyEq, vacant, published, written⟩ := shape
        change after = _ at published
        subst published
        refine ⟨token, kernel, responseFields candidate encrypted, found, by rw [keyEq]; exact vacant, ?_, written,
          identity⟩
        change Function.update shared.2.server.server.peers candidate.key_id
          (some ⟨candidate.beacon_identity_public_key, kernel, ()⟩) = _
        rw [keyEq, beacon]
      · cases reply
      · cases reply

end Footprint

/-! ### CE-3's invariant across the marked build -/

section Good
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type} (setup : Setup baseSpec KemSK)
  (codec : Codec Reader Response)
open PqxdhDeploymentCompile (Local)
open PqxdhDeploymentCompileInvariant (Good)

/-- The footprint of a Server build on the game state, as in CE-3's `PqxdhDeploymentCompileFootprint.build_footprint` (the conclusion of `buildHidden_footprint`). -/
def BuildFootprint (session : ℕ) (before after : GameState KemSK)
    (reply : Option PqxdhServerRegistrationPublication.Response) : Prop :=
  after.server.server.identity = before.server.server.identity ∧
    after.server.identityKeyId = before.server.identityKeyId ∧ after.sessions = before.sessions ∧
    (∀ other, other ≠ session → after.pending other = before.pending other) ∧ after.pending session = none ∧
    (reply = none → after.server.server.peers = before.server.server.peers) ∧
    (∀ response, reply = some response → ∃ token kernel fields,
      before.pending session = some token ∧ before.server.server.peers response.keyId = none ∧
      after.server.server.peers = Function.update before.server.server.peers response.keyId
        (some ⟨token.pending.beacon_identity_public_key, kernel, ()⟩) ∧
      codec.write2 fields = some response.serialized ∧ fields.identity = before.server.server.identity)

/-- CE-3's invariant survives every Server build with the footprint of `BuildFootprint` that keeps the owners, with the reply logged, under the approved Phase 2 read-back contract (the argument of CE-3's `PqxdhDeploymentCompileInvariant.good_build`, from the footprint alone). -/
theorem good_of_build (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec) (session : ℕ)
    (payload : Option Pqxdh.Bytes) (copies : Local) (native after : PqxdhRegistrationSchedule.State KemSK)
    (good : Good setup codec copies native) (reply : Option PqxdhServerRegistrationPublication.Response)
    (owners : after.owners = native.owners) (footprint : BuildFootprint codec session native.shared.2 after.shared.2 reply) :
    Good setup codec { copies with log := PqxdhDeploymentCompile.logReply copies.log (.build session payload) reply }
      after := by
  obtain ⟨identity, keyId, sessions, others, removed, rejected, published⟩ := footprint
  have pendingKept : ∀ other token, after.shared.2.pending other = some token →
      native.shared.2.pending other = some token := by
    intro other token found
    by_cases same : other = session
    · subst same
      rw [removed] at found
      cases found
    · rw [← others other same]
      exact found
  rcases reply with _ | response
  · have peers := rejected rfl
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
  · obtain ⟨token, kernel, fields, tokenFound, free, peers, written, fieldsIdentity⟩ := published response rfl
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
        simp only [PqxdhDeploymentCompile.peerView, Function.update_self, Option.bind_eq_bind, Option.bind_some,
          logged, PqxdhDeploymentCompile.serverIdentityOf, decodedRead, serverRead, fieldsIdentity, identified,
          Option.pure_def]
      · rw [Function.update_of_ne same] at found
        have old := good.serverVisible kid peer found
        simpa only [PqxdhDeploymentCompile.peerView, Function.update_of_ne same] using old
    · rw [owners]; exact good.count
    · intro index current copied
      rw [owners]
      exact good.copied index current copied
    · rw [owners]; exact good.owners
    · intro other token found
      rw [sessions]
      exact good.pending other token (pendingKept other token found)
    · rw [sessions]; exact good.accepts

end Good

/-! ### The marked build in the middle execution -/

section Middle
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type} (setup : Setup baseSpec KemSK)
  (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder) (checks : Checks) {count : ℕ}
  (t : PqxdhDeploymentIdealParams.Target count) (p : PqxdhDeploymentIdealParams.Params KemSK count)
  (created : PqxdhLiveServerConstruction.Created Unit)
open PqxdhDeploymentCompile (Local)
open PqxdhDeploymentCompileInvariant (Good)
open PqxdhDeploymentIdealPostSource (Mid sourceMid compiledMid idealMid buildHiddenAt)

/-- The marked build of the middle execution, as the compiled step sees it: on every outcome the local copies log the reply, the accept counter is kept, and the native state of the annotated source state has the owners before and the shared native state after the marked build at some 108-byte value. -/
theorem compiledMid_buildHidden (session : ℕ) (payload : Option Pqxdh.Bytes) (copies : Local) (m : Mid KemSK)
    (hidden : buildHiddenAt m session = true)
    (result : Option PqxdhServerRegistrationPublication.Response × (Local × Mid KemSK))
    (supported : result ∈ support ((compiledMid setup codec route checks t p created
      (.inr (.build session payload))).run (copies, m))) :
    result.2.1 = { copies with log := PqxdhDeploymentCompile.logReply copies.log (.build session payload) result.1 } ∧
      result.2.2.backend.2.2.accepts = m.backend.2.2.accepts ∧
      ∃ value shared, (result.1, shared) ∈ support ((PqxdhDeploymentIdealSteps.buildHidden (KemSK := KemSK)
        (PqxdhRegistrationJointKemEntryFactor.factoredHidden setup codec checks value) session payload).run
          m.joint.shared) ∧
        PqxdhRegistrationJointSchedule.source result.2.2.joint =
          { PqxdhRegistrationJointSchedule.source m.joint with shared := shared } := by
  change result ∈ support ((fun result => (result.1.1, (result.1.2, result.2))) <$>
    (simulateQ (sourceMid setup codec route checks t p created)
      ((PqxdhDeploymentCompile.forwardLogged (.build session payload) (.build session payload) id).run copies)).run m)
    at supported
  rw [PqxdhDeploymentIdealPostSource.compiledMid_forward, Functor.map_map, support_map] at supported
  obtain ⟨stepped, steppedMember, rfl⟩ := supported
  have middle : (sourceMid setup codec route checks t p created (.inl (.inr (.build session payload)))).run m =
      (idealMid setup codec route checks t p created ⟨.build session payload, trivial⟩).run m := by
    change (if buildHiddenAt m session then _ else _) = _
    rw [ite_eq_left_of_eq_true _ _ (eq_true hidden)]
  rw [middle, PqxdhDeploymentIdealPostHidden.idealMid_run, support_map] at steppedMember
  obtain ⟨r, rMember, rfl⟩ := steppedMember
  have inner : r.1 ∈ support ((PqxdhDeploymentIdealSteps.idealProg setup codec route checks t p
      (PqxdhRegistrationJointKemEntryFactor.factoredHidden setup codec checks) created ⟨.build session payload, trivial⟩).run
        (PqxdhDeploymentIdealSlots.detach (PqxdhDeploymentIdealPostSource.toX m))) := by
    apply OracleComp.support_simulateQ_run'_subset
      (PqxdhRegistrationJointKemSecondEntry.slotImpl PqxdhDeploymentSeedSplit.tableService) _ (m.backend.2.1, m.backend.1)
    rw [StateT.run'_eq, support_map]
    exact ⟨r, rMember, rfl⟩
  obtain ⟨coords, marked, pending⟩ : ∃ coords, m.backend.2.2.marks = some (session, coords) ∧
      (m.joint.shared.2.pending session).isSome = true := by
    unfold buildHiddenAt at hidden
    rcases found : m.backend.2.2.marks with _ | ⟨index, coords⟩
    · rw [found] at hidden
      cases hidden
    · rw [found] at hidden
      obtain ⟨same, pending⟩ := of_decide_eq_true hidden
      subst same
      exact ⟨coords, rfl, pending⟩
  change r.1 ∈ support ((PqxdhDeploymentIdealSteps.buildStep setup codec route checks
    (PqxdhRegistrationJointKemEntryFactor.factoredHidden setup codec checks) created session payload).run
      (PqxdhDeploymentIdealSlots.detach (PqxdhDeploymentIdealPostSource.toX m))) at inner
  rw [PqxdhDeploymentIdealPostHidden.buildStep_hidden_run setup codec route checks created session payload _ coords
    marked pending, mem_support_bind_iff] at inner
  obtain ⟨value, -, inner⟩ := inner
  rw [mem_support_bind_iff] at inner
  obtain ⟨rr, rrMember, inner⟩ := inner
  rw [support_pure, Set.mem_singleton_iff] at inner
  rw [PqxdhDeploymentIdealSteps.liftS, support_liftComp] at rrMember
  obtain ⟨⟨reply, y⟩, slots⟩ := r
  simp only [Prod.mk.injEq] at inner
  obtain ⟨rfl, rfl⟩ := inner
  refine ⟨rfl, rfl, value, rr.2, rrMember, ?_⟩
  simp only [PqxdhDeploymentIdealPostSource.fromX, PqxdhDeploymentIdealSlots.attach,
    PqxdhDeploymentIdealPostSource.source_rejoin]
  rfl

/-- The marked build of the middle execution keeps CE-3's invariant on the local copies and the native state of the annotated source state, and the accept counter, under the approved Phase 2 read-back contract. -/
theorem good_buildHidden (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec) (session : ℕ)
    (payload : Option Pqxdh.Bytes) (copies : Local) (m : Mid KemSK) (hidden : buildHiddenAt m session = true)
    (good : Good setup codec copies (PqxdhRegistrationJointSchedule.source m.joint))
    (result : Option PqxdhServerRegistrationPublication.Response × (Local × Mid KemSK))
    (supported : result ∈ support ((compiledMid setup codec route checks t p created
      (.inr (.build session payload))).run (copies, m))) :
    Good setup codec result.2.1 (PqxdhRegistrationJointSchedule.source result.2.2.joint) ∧
      result.2.2.backend.2.2.accepts = m.backend.2.2.accepts := by
  obtain ⟨copied, accepts, value, shared, member, joint⟩ :=
    compiledMid_buildHidden setup codec route checks t p created session payload copies m hidden result supported
  refine ⟨?_, accepts⟩
  rw [copied, joint]
  exact good_of_build setup codec phase2 session payload copies _ _ good result.1 rfl
    (buildHidden_footprint setup codec checks value session payload m.joint.shared (result.1, shared) member)

end Middle

end BeaconcryptCore.Computational.PqxdhDeploymentIdealPostGoodBuild

-- Axiom guards (generated)

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPostGoodBuild.afterInitializationW_shape' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPostGoodBuild.afterInitializationW_shape

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPostGoodBuild.continueRust_shape' depends on axioms: [propext,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPostGoodBuild.continueRust_shape

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPostGoodBuild.candidateW_shape' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPostGoodBuild.candidateW_shape

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPostGoodBuild.genericBuildW_shape' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPostGoodBuild.genericBuildW_shape

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPostGoodBuild.tailImpl_write' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPostGoodBuild.tailImpl_write

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPostGoodBuild.factored_logged' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPostGoodBuild.factored_logged

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPostGoodBuild.freeWrite_shape' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPostGoodBuild.freeWrite_shape

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPostGoodBuild.hiddenBuild_shape' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPostGoodBuild.hiddenBuild_shape

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPostGoodBuild.buildHidden_footprint' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPostGoodBuild.buildHidden_footprint

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPostGoodBuild.good_of_build' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPostGoodBuild.good_of_build

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPostGoodBuild.compiledMid_buildHidden' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPostGoodBuild.compiledMid_buildHidden

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPostGoodBuild.good_buildHidden' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPostGoodBuild.good_buildHidden
