-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvStep
import BeaconcryptCore.Computational.PqxdhDeploymentSplitFactor

/-!
# The ideal environment's marked build (CE-11b, unit U3)

The marked Server build of CE-11b's ideal environment in capability form (design-v2 section 6.1), with its split of the final split form `PqxdhDeploymentIdealDefer.idealSplit` (the build of the marked session while it has a pending token, followed by the hidden Server install `serverInstall`).

- The generic Server build under a peer-wise transformation (`mapPeers`): publishing, the first send, the candidate admission and the whole generic build commute with a transformation that fixes every vacant key ID (`publish_mapPeers`, `afterInitialization_mapPeers`, `candidate_mapPeers`, `genericBuild_mapPeers`), and its shapes (`GBuilt`, `afterInitializationG_shape`, `continueRustG_shape`, `candidateG_shape`, `genericBuild_shape`). For the free factored build of CE-11a (`PqxdhDeploymentSplitFactor.freeBuild`, the factored Server build with its callbacks left as queries) this gives CE-3's override (`freeBuild_override`, through `copyPeers`, `embed_override`, `native_override`: the build on the World-filled Server record is CE-3's override of the build on the environment's stripped record) and the shape of the real build (`freeBuild_shape`: no publication with the record kept, or one publication at a key ID that was vacant).
- The World's hidden Server install with its counts forgotten: one lookup of the persistent lazy seed table (`resolve_uncount`), the slot's Server marker set and the peer installed with the World's Server kernel of the seed (`effects_hiddenServer`); it is count-free (`countFree_hiddenServer`, `countFree_hiddenServerEffect`).
- `buildHiddenEnv`: at the slot of the marked coordinates the material is read lazily from the environment's material cache (coin effects at the first touch), then CE-11a's split hidden build of the slot (`PqxdhDeploymentEnvironment.buildSplitEnv`) runs on the session's pending token; the environment keeps the stripped state after the build (`builtSettled`, `builtEnv`) and sets the Server install ghost when a peer was published. Its World run is the lazy material read, the forwarded build read through `ctxEffects` on the World's CTX cache, then the hidden install (`buildHidden_effects`, with `buildSplitFwd_noAdmin`).
- The split form's marked build at an allocated slot with a pending token (`idealSplit_build_hidden`, through `buildHidden_run`) is the lazy material read, the free factored build at the material and the dummy seed under the native logged tail on the CTX cache, then `serverInstall`, which does nothing when no peer was published (`serverInstall_quiet`) and otherwise reads the slot's seed lazily and puts the World's Server kernel of it on the published peer (`serverInstall_published`).
- `buildHidden_law`: from an admissible joint state whose World Server marker of the slot is unused, the reassembled law of the World run is the split form's, exactly (through `strip_builtSettled_publish`, `setPeerKernel_override` and CE-11a's reassembly `PqxdhDeploymentIdealEnvReal.build_merge` with the World's kernel of the drawn seed). `buildHidden_outcome` describes every outcome (nothing published, or one peer at a key ID vacant before, installed by the World with the slot's seed, which its table now holds, and the slot's Server marker set), and `buildHidden_keeps` is the preservation of admissibility.

The premises (an allocated slot, a pending token, an unused Server marker) are those that the ideal environment's admissibility predicate `IdealInv` provides (a later module). These are equalities of programs and in law and support facts; no security claim is made here.
-/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete PqxdhRefinement

set_option autoImplicit false

namespace BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvBuild
open PqxdhServerAuthExperiment (Setup Codec Checks GameState)
open PqxdhServerRegistrationPublication (AuxSpec Response)

/-! ### The generic Server build under a peer-wise transformation -/

section GenericBuild
variable {Kernel Metadata PeerMetadata Consumed : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
open PqxdhInitialGenericPublication (State)

/-- The peers of a generic Server state, transformed key by key. -/
def mapPeers (φ : Std.U64 → RawCtxGenericRoleStorage.Peer Kernel PeerMetadata → RawCtxGenericRoleStorage.Peer Kernel PeerMetadata)
    (state : State Kernel Metadata PeerMetadata Consumed) : State Kernel Metadata PeerMetadata Consumed :=
  { state with server := { state.server with peers := fun kid => (state.server.peers kid).map (φ kid) } }

/-- Publishing at a key ID that the transformation fixes commutes with the transformation. -/
theorem publish_mapPeers
    (φ : Std.U64 → RawCtxGenericRoleStorage.Peer Kernel PeerMetadata → RawCtxGenericRoleStorage.Peer Kernel PeerMetadata)
    (state : State Kernel Metadata PeerMetadata Consumed) (candidate : pqxdh.ServerRegistrationCandidate)
    (kernel : Kernel) (metadata : PeerMetadata) (fixed : ∀ peer, φ candidate.key_id peer = peer) :
    PqxdhInitialGenericPublication.publish (mapPeers φ state) candidate kernel metadata =
      mapPeers φ (PqxdhInitialGenericPublication.publish state candidate kernel metadata) := by
  simp only [PqxdhInitialGenericPublication.publish, mapPeers]
  congr 2
  funext kid
  by_cases same : kid = candidate.key_id
  · subst same
    simp only [Function.update_self, Option.map_some, fixed]
  · simp only [Function.update_of_ne same]

/-- The first send and Phase 2 writing commute with a transformation that fixes the candidate key ID. -/
theorem afterInitialization_mapPeers (calls : RawCtxChainOwner.Calls Kernel m) (aux : QueryImpl AuxSpec m)
    (candidate : pqxdh.ServerRegistrationCandidate) (authenticated : Pqxdh.Bytes) (kernel : Kernel)
    (metadata : PeerMetadata) (state : State Kernel Metadata PeerMetadata Consumed)
    (φ : Std.U64 → RawCtxGenericRoleStorage.Peer Kernel PeerMetadata → RawCtxGenericRoleStorage.Peer Kernel PeerMetadata)
    (fixed : ∀ peer, φ candidate.key_id peer = peer) :
    PqxdhInitialGenericPublication.afterInitialization calls aux candidate authenticated kernel metadata (mapPeers φ state) =
      (fun value => (value.1, mapPeers φ value.2)) <$>
        PqxdhInitialGenericPublication.afterInitialization calls aux candidate authenticated kernel metadata state := by
  unfold PqxdhInitialGenericPublication.afterInitialization
  simp only [map_bind]
  refine bind_congr fun sent => ?_
  rcases sent with ⟨advanced, encrypted⟩
  refine bind_congr fun _ => ?_
  rcases encrypted with _ | encrypted
  · simp only [map_pure]
  · simp only [map_bind]
    refine bind_congr fun serialized => ?_
    rcases serialized with _ | serialized
    · simp only [map_pure]
    · simp only [map_pure, publish_mapPeers φ state candidate advanced metadata fixed]

/-- The candidate admission and first send commute with a transformation that fixes the candidate key ID. -/
theorem candidate_mapPeers (calls : RawCtxChainOwner.Calls Kernel m) (aux : QueryImpl AuxSpec m) (initial : RustM Kernel)
    (candidate : pqxdh.ServerRegistrationCandidate) (data : Option Pqxdh.Bytes) (metadata : PeerMetadata)
    (state : State Kernel Metadata PeerMetadata Consumed)
    (φ : Std.U64 → RawCtxGenericRoleStorage.Peer Kernel PeerMetadata → RawCtxGenericRoleStorage.Peer Kernel PeerMetadata)
    (fixed : ∀ peer, φ candidate.key_id peer = peer) :
    PqxdhInitialGenericBuilder.candidate calls aux initial candidate data metadata (mapPeers φ state) =
      Functor.map (fun value => (value.1, mapPeers φ value.2)) <$>
        PqxdhInitialGenericBuilder.candidate calls aux initial candidate data metadata state := by
  unfold PqxdhInitialGenericBuilder.candidate
  simp only [map_bind]
  refine bind_congr fun valid => ?_
  split
  · simp only [map_pure]
    rfl
  · simp only [map_bind]
    refine bind_congr fun reserved => ?_
    split
    · simp only [map_pure]
      rfl
    · unfold PqxdhInitialGenericBuilder.continueRust
      split
      · split
        · simp only [map_pure]
          rfl
        · split
          · simp only [map_bind]
            refine bind_congr fun allocated => ?_
            split
            · simp only [map_pure]
              rfl
            · split
              · simp only [afterInitialization_mapPeers calls aux candidate _ _ metadata state φ fixed, Functor.map_map]
                rfl
              · simp only [map_pure]
                rfl
              · simp only [map_pure]
                rfl
          · simp only [map_pure]
            rfl
      · simp only [map_pure]
        rfl
      · simp only [map_pure]
        rfl

/-- The generic Server build commutes with a peer-wise transformation that fixes every vacant key ID: occupancy is read only through `isSome`, and a new peer is installed only at a vacant key ID. -/
theorem genericBuild_mapPeers (calls : RawCtxChainOwner.Calls Kernel m) (aux : QueryImpl AuxSpec m)
    (initial : RustM Kernel) (pending : pqxdh.PendingServerRegistration) (data : Option Pqxdh.Bytes)
    (metadata : PeerMetadata) (state : State Kernel Metadata PeerMetadata Consumed)
    (φ : Std.U64 → RawCtxGenericRoleStorage.Peer Kernel PeerMetadata → RawCtxGenericRoleStorage.Peer Kernel PeerMetadata)
    (vacantFixed : ∀ kid, state.server.peers kid = none → ∀ peer, φ kid peer = peer) :
    PqxdhServerAuthSendFactor.genericBuild calls aux initial pending data metadata (mapPeers φ state) =
      Functor.map (fun value => (value.1, mapPeers φ value.2)) <$>
        PqxdhServerAuthSendFactor.genericBuild calls aux initial pending data metadata state := by
  have candidateStep := fun candidate fixed => candidate_mapPeers calls aux initial candidate data metadata state φ fixed
  unfold PqxdhServerAuthSendFactor.genericBuild PqxdhInitialGenericBuilder.continueRust
  simp only [mapPeers, Option.isSome_map] at candidateStep ⊢
  cases next : pqxdh.server_next_key_id state.control with
  | ok value =>
      rcases value with value | _
      · dsimp only
        cases prepared : pqxdh.server_prepare_commit state.control pending
            ⟨state.server.identity, state.identityKeyId⟩
            (if (state.server.peers value).isSome then pqxdh.KeyIdAvailability.Occupied else .Available) with
        | ok result =>
            rcases result with candidate | _
            · dsimp only
              obtain ⟨available, key⟩ := PqxdhDeploymentCompileRegistration.prepare_key _ _ _ _ candidate prepared
              rw [next] at key
              have same : candidate.key_id = value := by
                cases key
                rfl
              have free : state.server.peers value = none := by
                by_contra occupied
                rw [Option.isSome_iff_ne_none.mpr occupied] at available
                simp at available
              exact candidateStep candidate (vacantFixed candidate.key_id (same ▸ free))
            · simp only [map_pure]
              rfl
        | fail error => simp only [map_pure]; rfl
        | div => simp only [map_pure]; rfl
      · simp only [map_pure]
        rfl
  | fail error => simp only [map_pure]; rfl
  | div => simp only [map_pure]; rfl

end GenericBuild

/-! ### Shapes of the generic Server build -/

section GenericShape
variable {Kernel Metadata PeerMetadata Consumed : Type} {ι' : Type} {spec' : OracleSpec ι'}
open PqxdhInitialGenericPublication (State)

/-- A generic Server build's result: a diagnostic, no publication with the state kept, or one publication at a key ID that was vacant. -/
def GBuilt (state : State Kernel Metadata PeerMetadata Consumed) (metadata : PeerMetadata) :
    RustM (Option Response × State Kernel Metadata PeerMetadata Consumed) → Prop
  | .ok (none, after) => after = state
  | .ok (some response, after) => ∃ candidate kernel, response.keyId = candidate.key_id ∧
      state.server.peers candidate.key_id = none ∧
        after = PqxdhInitialGenericPublication.publish state candidate kernel metadata
  | _ => True

/-- The generic first send and Phase 2 writing publish at the candidate key ID or keep the state. -/
theorem afterInitializationG_shape (calls : RawCtxChainOwner.Calls Kernel (OracleComp spec'))
    (aux : QueryImpl AuxSpec (OracleComp spec')) (candidate : pqxdh.ServerRegistrationCandidate)
    (authenticated : Pqxdh.Bytes) (kernel : Kernel) (metadata : PeerMetadata)
    (state : State Kernel Metadata PeerMetadata Consumed) (vacant : state.server.peers candidate.key_id = none) :
    ∀ result ∈ support (PqxdhInitialGenericPublication.afterInitialization calls aux candidate authenticated kernel
      metadata state), GBuilt state metadata (.ok result) := by
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
      obtain ⟨serialized, _, member⟩ := member
      cases serialized with
      | none =>
          simp only [support_pure, Set.mem_singleton_iff] at member
          subst member
          rfl
      | some serialized =>
          simp only [support_pure, Set.mem_singleton_iff] at member
          subst member
          exact ⟨candidate, advanced, rfl, vacant, rfl⟩

/-- A property of Rust results that holds at every diagnostic and on every continuation holds on the continued result. -/
theorem continueRustG_shape {α β : Type} (value : RustM α) (next : α → OracleComp spec' (RustM β))
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

/-- The generic candidate admission and first send publish only at the vacant candidate key ID. -/
theorem candidateG_shape (calls : RawCtxChainOwner.Calls Kernel (OracleComp spec'))
    (aux : QueryImpl AuxSpec (OracleComp spec')) (initial : RustM Kernel) (candidate : pqxdh.ServerRegistrationCandidate)
    (data : Option Pqxdh.Bytes) (metadata : PeerMetadata) (state : State Kernel Metadata PeerMetadata Consumed)
    (vacant : state.server.peers candidate.key_id = none) :
    ∀ result ∈ support (PqxdhInitialGenericBuilder.candidate calls aux initial candidate data metadata state),
      GBuilt state metadata result := by
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
      refine continueRustG_shape _ _ _ (fun _ => trivial) trivial (fun kernel inner innerMember => ?_) result member
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
          refine continueRustG_shape _ _ _ (fun _ => trivial) trivial (fun binding final finalMember => ?_) inner
            innerMember
          rw [support_map] at finalMember
          obtain ⟨published, publishedMember, rfl⟩ := finalMember
          exact afterInitializationG_shape calls aux candidate _ _ metadata state vacant published publishedMember
      · simp only [support_pure, Set.mem_singleton_iff] at innerMember
        subst innerMember
        rfl

/-- Every outcome of the generic Server build is a diagnostic, no publication with the state kept, or one publication at a key ID that was vacant. -/
theorem genericBuild_shape (calls : RawCtxChainOwner.Calls Kernel (OracleComp spec'))
    (aux : QueryImpl AuxSpec (OracleComp spec')) (initial : RustM Kernel) (pending : pqxdh.PendingServerRegistration)
    (data : Option Pqxdh.Bytes) (metadata : PeerMetadata) (state : State Kernel Metadata PeerMetadata Consumed) :
    ∀ result ∈ support (PqxdhServerAuthSendFactor.genericBuild calls aux initial pending data metadata state),
      GBuilt state metadata result := by
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
              exact candidateG_shape calls aux initial candidate data metadata state vacant result supported
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

end GenericShape

/-! ### The free factored build: override and shape -/

section FreeBuild
open PqxdhDeploymentCompileRegistration (overrideServer mapBuilt)
open PqxdhDeploymentSplitFactor (freeBuild)

/-- CE-3's local peer copies as a peer-wise transformation of the generic Server state: a copied peer gets the known form of its local kernel. -/
def copyPeers (copies : PqxdhDeploymentCompile.Local) (kid : Std.U64)
    (peer : RawCtxGenericRoleStorage.Peer PqxdhServerAuthSendFactor.Kernel Unit) :
    RawCtxGenericRoleStorage.Peer PqxdhServerAuthSendFactor.Kernel Unit :=
  match copies.peers kid with
  | some kernel => { peer with kernel := PqxdhServerAuthSendFactor.known kernel }
  | none => peer

/-- Embedding a Server state with CE-3's override is transforming the embedded state by the copies. -/
theorem embed_override (copies : PqxdhDeploymentCompile.Local) (server : PqxdhServerAuthEntryFactor.ServerState) :
    PqxdhServerAuthSendFactor.embed (overrideServer copies server) =
      mapPeers (copyPeers copies) (PqxdhServerAuthSendFactor.embed server) := by
  simp only [PqxdhServerAuthSendFactor.embed, overrideServer, mapPeers]
  congr 2
  funext kid
  cases server.server.peers kid with
  | none => rfl
  | some peer =>
      cases copied : copies.peers kid with
      | none => simp only [Option.map_some, copyPeers, copied, PqxdhDeploymentCompile.mergePeer]
      | some kernel => simp only [Option.map_some, copyPeers, copied, PqxdhDeploymentCompile.mergePeer]

/-- The native projection of a state transformed by the copies is CE-3's override of the native projection. -/
theorem native_override (copies : PqxdhDeploymentCompile.Local)
    (state : PqxdhInitialGenericPublication.State PqxdhServerAuthSendFactor.Kernel Unit Unit (List Pqxdh.Bytes)) :
    PqxdhInitialGenericPublication.native PqxdhServerAuthSendFactor.resolve (mapPeers (copyPeers copies) state) =
      overrideServer copies (PqxdhInitialGenericPublication.native PqxdhServerAuthSendFactor.resolve state) := by
  simp only [PqxdhInitialGenericPublication.native, RawCtxGenericRoleStorage.nativeServer, mapPeers, overrideServer]
  congr 2
  funext kid
  cases state.server.peers kid with
  | none => rfl
  | some peer =>
      cases copied : copies.peers kid with
      | none => simp only [Option.map_some, copyPeers, copied, PqxdhDeploymentCompile.mergePeer]
      | some kernel =>
          simp only [Option.map_some, copyPeers, copied, PqxdhDeploymentCompile.mergePeer]
          rfl

/-- The free factored build commutes with CE-3's override when every copied peer is installed. -/
theorem freeBuild_override (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (value : PqxdhServerAuthSendFactor.Factor) (pending : pqxdh.PendingServerRegistration) (data : Option Pqxdh.Bytes)
    (copies : PqxdhDeploymentCompile.Local) (server : PqxdhServerAuthEntryFactor.ServerState)
    (installed : ∀ kid current, copies.peers kid = some current → server.server.peers kid ≠ none) :
    freeBuild source value pending data (overrideServer copies server) =
      mapBuilt copies <$> freeBuild source value pending data server := by
  unfold freeBuild PqxdhServerAuthLoggedSendFactor.factored
  rw [embed_override, genericBuild_mapPeers _ _ _ _ _ _ _ _ (fun kid vacant peer => ?_), Functor.map_map,
    Functor.map_map]
  · congr 1
    funext result
    rcases result with ⟨reply, after⟩ | error | _
    · change RustM.ok (reply, PqxdhInitialGenericPublication.native PqxdhServerAuthSendFactor.resolve
        (mapPeers (copyPeers copies) after)) = RustM.ok (reply, overrideServer copies
          (PqxdhInitialGenericPublication.native PqxdhServerAuthSendFactor.resolve after))
      rw [native_override]
    · rfl
    · rfl
  · have none : copies.peers kid = none := by
      cases copied : copies.peers kid with
      | none => rfl
      | some current =>
          refine absurd ?_ (installed kid current copied)
          simpa only [PqxdhServerAuthSendFactor.embed, Option.map_eq_none_iff] using vacant
    simp only [copyPeers, none]

/-- Every outcome of the free factored build is a diagnostic, no publication with the state kept, or one publication at a key ID that was vacant. -/
theorem freeBuild_shape (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (value : PqxdhServerAuthSendFactor.Factor) (pending : pqxdh.PendingServerRegistration) (data : Option Pqxdh.Bytes)
    (server : PqxdhServerAuthEntryFactor.ServerState) :
    ∀ result ∈ support (freeBuild source value pending data server),
      PqxdhDeploymentEnvironmentReal.Built server () result := by
  intro result supported
  unfold freeBuild PqxdhServerAuthLoggedSendFactor.factored at supported
  rw [support_map] at supported
  obtain ⟨inner, member, rfl⟩ := supported
  have shape := genericBuild_shape _ _ _ _ _ _ _ inner member
  have back : PqxdhInitialGenericPublication.native PqxdhServerAuthSendFactor.resolve
      (PqxdhServerAuthSendFactor.embed server) = server :=
    PqxdhServerAuthSendFactor.native_embed RawCtxSelectedChain.unusedChain server
  rcases inner with ⟨(_ | response), after⟩ | error | _
  · change after = _ at shape
    subst shape
    change PqxdhInitialGenericPublication.native PqxdhServerAuthSendFactor.resolve
      (PqxdhServerAuthSendFactor.embed server) = server
    exact back
  · obtain ⟨candidate, kernel, keyEq, vacant, published⟩ := shape
    subst published
    refine ⟨candidate, PqxdhServerAuthSendFactor.resolve kernel, keyEq, ?_, ?_⟩
    · simpa only [PqxdhServerAuthSendFactor.embed, Option.map_eq_none_iff] using vacant
    · rw [PqxdhInitialGenericPublication.publish_native, back]
  · trivial
  · trivial

end FreeBuild

/-! ### The World's hidden installs with its counts forgotten -/

section WorldInstalls
variable {n : ℕ}
open PqxdhDeploymentEnvironmentJoin (uncount)
open PqxdhDeploymentEnvironmentReal (installPeer effects_issue)

/-- A hidden resolution with the World's counts forgotten: one lookup of the persistent lazy seed table and the World's kernel of the seed. -/
theorem resolve_uncount (role : PqxdhRecordLiftInterface.Role) (j : PqxdhRecordLiftInterface.Slot n)
    (state : PqxdhRecordLiftWorld.State n) :
    Prod.map id uncount <$> (PqxdhRecordLiftWorld.resolve role (.hidden j)).run state =
      (fun r => (PqxdhRecordLiftWorld.kernel role r.1, uncount { state with seeds := r.2 })) <$>
        (PqxdhRecordLiftLazyTable.impl j).run state.seeds := by
  have forgot := PqxdhRecordLiftWorld.countCoin_forget ((PqxdhRecordLiftLazyTable.impl j).run state.seeds)
    state.primitive.1.uniform
  conv_rhs => rw [← forgot, Functor.map_map]
  simp only [PqxdhRecordLiftWorld.resolve, PqxdhRecordLiftWorld.sampled, StateT.run, bind_pure_comp, Functor.map_map]
  rfl

/-- An admitted hidden Server install with the World's counts forgotten: one lookup of the lazy seed table, the Server marker of the slot set, and the peer installed with the World's Server kernel of the seed. -/
theorem effects_hiddenServer (keyId : Std.U64) (identity : RawCtxServerRouting.Identity)
    (j : PqxdhRecordLiftInterface.Slot n) (w : PqxdhRecordLiftWorld.State n) (world : PqxdhRecordLiftWorld.Server)
    (found : w.server = some world) (vacant : world.records.server.peers keyId = none)
    (unused : w.used j .server = false) :
    Prod.map id uncount <$> (simulateQ PqxdhRecordLiftWorld.effects
        (PqxdhDeploymentEnvironment.issue (.installServer keyId identity (.hidden j)))).run w =
      (fun r => ((), uncount { w with
        seeds := r.2
        used := Function.update w.used j (Function.update (w.used j) .server true)
        server := some (installPeer world keyId identity (PqxdhRecordLiftWorld.kernel .server r.1)) })) <$>
        (PqxdhRecordLiftLazyTable.impl j).run w.seeds := by
  rw [effects_issue]
  have charged : (PqxdhRecordLiftWorld.chargeEffect (.inr (.installServer keyId identity (.hidden j))) w).server =
      some world := found
  have admitted : world.records.server.peers keyId = none ∧ PqxdhRecordLiftWorld.Unused
      (PqxdhRecordLiftWorld.chargeEffect (.inr (.installServer keyId identity (.hidden j))) w) .server (.hidden j) :=
    ⟨vacant, unused⟩
  change (fun result => ((), uncount result.2)) <$> (PqxdhRecordLiftWorld.installServer keyId identity (.hidden j)).run
    (PqxdhRecordLiftWorld.chargeEffect (.inr (.installServer keyId identity (.hidden j))) w) = _
  have forgot := PqxdhRecordLiftWorld.countCoin_forget ((PqxdhRecordLiftLazyTable.impl j).run w.seeds)
    (PqxdhRecordLiftWorld.chargeEffect (.inr (.installServer keyId identity (.hidden j))) w).primitive.1.uniform
  conv_rhs => rw [← forgot, Functor.map_map]
  have used' : (PqxdhRecordLiftWorld.chargeEffect (.inr (.installServer keyId identity (.hidden j))) w).used j .server =
      false := unused
  simp only [PqxdhRecordLiftWorld.installServer, StateT.run, charged, vacant, PqxdhRecordLiftWorld.Unused, used',
    and_self, ↓reduceIte, PqxdhRecordLiftWorld.resolve, PqxdhRecordLiftWorld.sampled, bind_pure_comp, Functor.map_map]
  rfl

/-- An issued hidden Server install is count-free: its World run with the counts forgotten does not depend on the counts. -/
theorem countFree_hiddenServer (keyId : Std.U64) (identity : RawCtxServerRouting.Identity)
    (j : PqxdhRecordLiftInterface.Slot n) :
    PqxdhDeploymentEnvironmentReal.CountFree
      (PqxdhDeploymentEnvironment.issue (n := n) (.installServer keyId identity (.hidden j))) := fun w => by
  by_cases admitted : ∃ world, w.server = some world ∧ world.records.server.peers keyId = none ∧ w.used j .server = false
  · obtain ⟨world, found, vacant, unused⟩ := admitted
    rw [effects_hiddenServer keyId identity j w world found vacant unused,
      effects_hiddenServer keyId identity j (uncount w) world found vacant unused]
    rfl
  · have refused : ∀ v : PqxdhRecordLiftWorld.State n, v.server = w.server → v.used = w.used →
        (PqxdhRecordLiftWorld.installServer keyId identity (.hidden j)).run v = pure (false, v) := by
      intro v server used
      refine PqxdhRecordLiftWorld.installServer_refused keyId identity _ v fun both => admitted ?_
      obtain ⟨⟨world, found, vacant⟩, unused⟩ := both
      exact ⟨world, server ▸ found, vacant, used ▸ unused⟩
    rw [effects_issue, effects_issue]
    change (fun result => ((), uncount result.2)) <$> (PqxdhRecordLiftWorld.installServer keyId identity (.hidden j)).run
      (PqxdhRecordLiftWorld.chargeEffect _ w) = (fun result => ((), uncount result.2)) <$>
        (PqxdhRecordLiftWorld.installServer keyId identity (.hidden j)).run (PqxdhRecordLiftWorld.chargeEffect _ (uncount w))
    rw [refused (PqxdhRecordLiftWorld.chargeEffect _ w) rfl rfl,
      refused (PqxdhRecordLiftWorld.chargeEffect _ (uncount w)) rfl rfl, map_pure, map_pure]
    rfl

end WorldInstalls

/-! ### The marked build in capability form -/

section HiddenBuild
variable {KemSK : Type} {ι : Type} {baseSpec : OracleSpec ι} {Reader Response : Type}
  (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
  (checks : Checks) {count : ℕ}
open PqxdhDeploymentEnvironment (EnvState strip coins ctxEffects)
open PqxdhDeploymentEnvironmentJoin (merge uncount Good)
open PqxdhDeploymentEnvironmentReal (ctxAdmin effects_then_free coins_noAdmin CountFree countFree_bind countFree_pure
  withCache)
open PqxdhDeploymentIdealSlots (Coord)
open PqxdhDeploymentIdealSteps (IdealCore SplitBk publishedKey)
open PqxdhDeploymentIdealKernel (MatCache)
open PqxdhDeploymentSeedSplit (MaterialSpec)
open PqxdhDeploymentSplitFactor (freeBuild)
open PqxdhRecordLiftInterface (EnvEffects EffectKind effectKind)

/-- The registration state after a Server build at a session with a settled result: the token consumed, the settled Server record installed and the seals logged. -/
def builtSettled (state : PqxdhRegistrationSchedule.State KemSK) (session : ℕ)
    (settled : Option PqxdhServerRegistrationPublication.Response × PqxdhServerAuthEntryFactor.ServerState)
    (log : List RawCtxSourceSend.SealContext) : PqxdhRegistrationSchedule.State KemSK :=
  { state with shared := (state.shared.1, { state.shared.2 with
      pending := Function.update state.shared.2.pending session none
      server := settled.2
      ghost := { state.shared.2.ghost with
        seals := state.shared.2.ghost.seals ++ log.map (fun context => (session, context)) } }) }

/-- The environment state after the marked build: the stripped registration state after the build, the material cache after the hidden read, and the Server install ghost set when the build published a peer. -/
noncomputable def builtEnv (e : EnvState KemSK SplitBk) (session : ℕ) (coords : Coord) (material : MatCache 2)
    (result : (Option PqxdhServerRegistrationPublication.Response × PqxdhServerAuthEntryFactor.ServerState) ×
      List RawCtxSourceSend.SealContext) : EnvState KemSK SplitBk :=
  { e with
    native := strip (builtSettled e.native session result.1 result.2)
    backend := (material, (e.backend.2.1, { e.backend.2.2 with
      peer := ((publishedKey result.1.1 result.1.2).map fun keyId => (keyId, coords)).or e.backend.2.2.peer })) }

/-- The marked build in capability form (design-v2 section 6.1): at the slot of the marked coordinates, the material is read lazily from the environment's material cache (coin effects at its first touch), then CE-11a's split hidden build of that slot runs on the session's pending token (`PqxdhDeploymentEnvironment.buildSplitEnv`: the factored build at the material and the dummy seed with its BLAKE2b request forwarded, settled, then the hidden install `installServer keyId identity (.hidden slot)` of the published peer). Without an allocated slot or a pending token it does nothing. -/
noncomputable def buildHiddenEnv (session : ℕ) (payload : Option Pqxdh.Bytes) (coords : Coord) :
    StateT (EnvState KemSK SplitBk) (OracleComp (EnvEffects 2)) (Option PqxdhServerRegistrationPublication.Response) :=
  fun e => match e.backend.2.1.1 coords, e.native.shared.2.pending session with
  | some j, some token => do
      let drawn ← coins (((MaterialSpec 2).randomOracle j).run e.backend.1)
      let result ← (PqxdhDeploymentEnvironment.buildSplitEnv setup codec checks drawn.1 j token payload
        e.native.shared.2.server).run []
      pure (result.1.1, builtEnv e session coords drawn.2 result)
  | _, _ => pure (none, e)

/-- The forwarded split build issues no administrative effect. -/
theorem buildSplitFwd_noAdmin (material : PqxdhDeploymentHiddenLayout.Material)
    (token : PqxdhServerRelatedRootConsumer.Returned) (payload : Option Pqxdh.Bytes)
    (server : PqxdhServerAuthEntryFactor.ServerState) (log : List RawCtxSourceSend.SealContext) :
    ((PqxdhDeploymentEnvironment.buildSplitFwd (n := 2) setup codec checks material token payload server).run
      log).IsQueryBoundP (fun effect => effectKind effect = .administrative) 0 := by
  have bound : ((PqxdhDeploymentEnvironment.buildSplitFwd (n := 2) setup codec checks material token payload server).run
      log).IsQueryBoundP (fun effect => effectKind effect = .administrative)
        (if (EffectKind.administrative) = .hash then 1 else 0) := by
    simp only [PqxdhDeploymentEnvironment.buildSplitFwd, PqxdhServerAuthLoggedSendFactor.factored, StateT.run_map,
      isQueryBoundP_map_iff]
    exact PqxdhDeploymentEnvironment.generic_build_bound _ _ _ _
      (fun entry context current => PqxdhDeploymentEnvironment.loggedFwd_send_bound setup codec checks _ entry context
        current .administrative) (fun query current => by
        have bound := PqxdhDeploymentEnvironment.tailFwd_bound (n := 2) setup codec checks (.inr query) current
          .administrative
        cases query <;> simpa only [PqxdhServerRegistrationPublication.callKind, PqxdhServerRegistrationPublication.auxKind,
          reduceCtorEq, and_false, ite_false] using bound) _ _ _ _ _ log
  simpa only [reduceCtorEq, ite_false] using bound

/-- Publishing a Server build at a hidden slot is count-free. -/
theorem countFree_hiddenServerEffect (j : PqxdhRecordLiftInterface.Slot 2)
    (settled : Option PqxdhServerRegistrationPublication.Response × PqxdhServerAuthEntryFactor.ServerState) :
    CountFree (PqxdhDeploymentEnvironment.hiddenServerEffect (n := 2) j settled) := by
  unfold PqxdhDeploymentEnvironment.hiddenServerEffect
  split
  · exact countFree_pure _
  · split
    · exact countFree_pure _
    · exact countFree_hiddenServer _ _ j

/-- The marked build in capability form at an allocated slot with a pending token, run by the World with its counts forgotten: the lazy material read, the forwarded split build read through `ctxEffects` on the World's CTX cache, then the hidden install of the settled build. -/
theorem buildHidden_effects (session : ℕ) (payload : Option Pqxdh.Bytes) (coords : Coord) (e : EnvState KemSK SplitBk)
    (w : PqxdhRecordLiftWorld.State 2) (j : PqxdhRecordLiftInterface.Slot 2)
    (token : PqxdhServerRelatedRootConsumer.Returned) (allocated : e.backend.2.1.1 coords = some j)
    (pending : e.native.shared.2.pending session = some token) :
    Prod.map id uncount <$> (simulateQ PqxdhRecordLiftWorld.effects
        ((buildHiddenEnv setup codec checks session payload coords).run e)).run w =
      ((MaterialSpec 2).randomOracle j).run e.backend.1 >>= fun drawn =>
        (simulateQ (ctxEffects ctxAdmin) ((PqxdhDeploymentEnvironment.buildSplitFwd (n := 2) setup codec checks drawn.1
          token payload e.native.shared.2.server).run [])).run w.primitive.2 >>= fun result =>
            Prod.map id uncount <$> (simulateQ PqxdhRecordLiftWorld.effects
              (PqxdhDeploymentEnvironment.hiddenServerEffect j
                (PqxdhServerAuthExperiment.settle e.native.shared.2.server result.1.1) >>= fun _ =>
                  pure ((PqxdhServerAuthExperiment.settle e.native.shared.2.server result.1.1).1,
                    builtEnv e session coords drawn.2
                      (PqxdhServerAuthExperiment.settle e.native.shared.2.server result.1.1, result.1.2)))).run
              (withCache w result.2) := by
  have program : (buildHiddenEnv setup codec checks session payload coords).run e =
      (coins (((MaterialSpec 2).randomOracle j).run e.backend.1) >>= fun drawn =>
        (fun r => (drawn, r)) <$> (PqxdhDeploymentEnvironment.buildSplitFwd (n := 2) setup codec checks drawn.1 token
          payload e.native.shared.2.server).run []) >>= fun value =>
        PqxdhDeploymentEnvironment.hiddenServerEffect j
          (PqxdhServerAuthExperiment.settle e.native.shared.2.server value.2.1) >>= fun _ =>
            pure ((PqxdhServerAuthExperiment.settle e.native.shared.2.server value.2.1).1,
              builtEnv e session coords value.1.2
                (PqxdhServerAuthExperiment.settle e.native.shared.2.server value.2.1, value.2.2)) := by
    change (match e.backend.2.1.1 coords, e.native.shared.2.pending session with
      | some j, some token => _
      | _, _ => _) = _
    rw [allocated, pending]
    simp only [PqxdhDeploymentEnvironment.buildSplitEnv, StateT.run_bind, StateT.run_lift, StateT.run_pure, bind_assoc,
      pure_bind, bind_map_left]
  rw [program, effects_then_free ctxAdmin _ ?noAdmin _ (fun value => countFree_bind
    (countFree_hiddenServerEffect j _) fun _ => countFree_pure _) w]
  · rw [simulateQ_bind, StateT.run_bind, PqxdhDeploymentEnvironment.ctxEffects_coins, bind_map_left, bind_assoc]
    refine bind_congr fun drawn => ?_
    rw [simulateQ_map, StateT.run_map, bind_map_left]
  · have bound := isQueryBoundP_bind (coins_noAdmin (n := 2) (((MaterialSpec 2).randomOracle j).run e.backend.1))
      (fun drawn _ => (isQueryBoundP_map_iff _ _ _).mpr (buildSplitFwd_noAdmin setup codec checks drawn.1 token payload
        e.native.shared.2.server []) :
        ∀ drawn ∈ support (coins (n := 2) (((MaterialSpec 2).randomOracle j).run e.backend.1)),
          ((fun r => (drawn, r)) <$> (PqxdhDeploymentEnvironment.buildSplitFwd (n := 2) setup codec checks drawn.1 token
            payload e.native.shared.2.server).run []).IsQueryBoundP (fun effect => effectKind effect = .administrative) 0)
    simpa only [Nat.add_zero] using bound

/-- The extended state after the final split form's marked build (before its hidden install): the game state after the build, the material cache after the hidden read, and the Server install ghost set when the build published a peer. -/
def builtX (x : PqxdhDeploymentBackend.XState KemSK SplitBk 2) (session : ℕ) (coords : Coord) (material : MatCache 2)
    (result : RustM (Option PqxdhServerRegistrationPublication.Response ×
      PqxdhServerRegistrationPublication.State Unit Unit (List Pqxdh.Bytes)) ×
        (List RawCtxSourceSend.SealContext × CtxRomAuth.CtxRO.QueryCache)) :
    PqxdhDeploymentBackend.XState KemSK SplitBk 2 :=
  { x with
    base := { x.base with native := { x.base.native with shared := (x.base.native.shared.1,
      PqxdhDeploymentEnvironmentReal.builtGame x.base.native.shared.2 session result) } }
    backend := (material, (x.backend.2.1, { x.backend.2.2 with
      peer := ((publishedKey (PqxdhServerAuthExperiment.settle x.base.native.shared.2.server result.1).1
        (PqxdhServerAuthExperiment.settle x.base.native.shared.2.server result.1).2).map fun keyId => (keyId, coords)).or
          x.backend.2.2.peer })) }

/-- One run of the marked build with the erased hidden services at a material and the dummy seed: the free factored build at that value under the native logged tail, settled. -/
theorem buildHidden_run (material : PqxdhDeploymentHiddenLayout.Material) (session : ℕ) (payload : Option Pqxdh.Bytes)
    (shared : PqxdhServerAuthNative.NativeState KemSK) :
    (PqxdhDeploymentIdealSteps.buildHidden (PqxdhDeploymentIdealSteps.erasedHidden setup codec checks
        (PqxdhDeploymentHiddenLayout.joinOutput material PqxdhDeploymentHiddenSplit.dummySeed)) session payload).run
        shared =
      match shared.2.pending session with
      | none => pure (none, shared)
      | some token => (fun result => ((PqxdhServerAuthExperiment.settle shared.2.server result.1).1,
          (shared.1, PqxdhDeploymentEnvironmentReal.builtGame shared.2 session result))) <$>
        (simulateQ (PqxdhServerAuthExperiment.tailImpl setup codec checks) (freeBuild setup.source
          (PqxdhServerAuthCtxMaterial.factor (PqxdhDeploymentHiddenLayout.joinOutput material
            PqxdhDeploymentHiddenSplit.dummySeed)) token.pending payload shared.2.server)).run ([], shared.2.ctx) := by
  rcases shared with ⟨family, game⟩
  unfold PqxdhDeploymentIdealSteps.buildHidden
  rw [PqxdhDeploymentBackend.nativeGet_bind]
  dsimp only
  cases game.pending session with
  | none => rfl
  | some token =>
      dsimp only
      rw [PqxdhDeploymentBackend.nativeCoins_bind, map_eq_bind_pure_comp]
      have free := PqxdhDeploymentSplitFactor.buildFactor_free setup codec checks material
        PqxdhDeploymentHiddenSplit.dummySeed token payload game.server
      change ((PqxdhDeploymentHiddenEntry.buildFactor setup codec checks material PqxdhDeploymentHiddenSplit.dummySeed
        token payload game.server).run ([], game.ctx)) >>= _ = _
      rw [free]
      refine bind_congr fun result => ?_
      rw [PqxdhDeploymentBackend.nativeSet_run_bind]
      rfl

/-- The final split form's marked build at an allocated slot with a pending token: the lazy material read, the free factored build at the material and the dummy seed under the native logged tail on the CTX cache, then the hidden Server install. -/
theorem idealSplit_build_hidden (t : PqxdhDeploymentIdealParams.Target count) (p : PqxdhDeploymentIdealParams.Params KemSK count)
    (created : PqxdhLiveServerConstruction.Created Unit) (session : ℕ) (payload : Option Pqxdh.Bytes)
    (x : PqxdhDeploymentBackend.XState KemSK SplitBk 2) (coords : Coord) (j : PqxdhRecordLiftInterface.Slot 2)
    (token : PqxdhServerRelatedRootConsumer.Returned) (marked : x.backend.2.2.marks = some (session, coords))
    (pending : x.base.native.shared.2.pending session = some token) (allocated : x.backend.2.1.1 coords = some j) :
    (PqxdhDeploymentIdealDefer.idealSplit setup codec route checks t p created ⟨.build session payload, trivial⟩).run x =
      ((MaterialSpec 2).randomOracle j).run x.backend.1 >>= fun drawn =>
        (simulateQ (PqxdhServerAuthExperiment.tailImpl setup codec checks) (freeBuild setup.source
          (PqxdhServerAuthCtxMaterial.factor (PqxdhDeploymentHiddenLayout.joinOutput drawn.1
            PqxdhDeploymentHiddenSplit.dummySeed)) token.pending payload x.base.native.shared.2.server)).run
              ([], x.base.native.shared.2.ctx) >>= fun result =>
          (fun r => (r.1.1, r.2)) <$> PqxdhDeploymentIdealDefer.serverInstall
            (((PqxdhServerAuthExperiment.settle x.base.native.shared.2.server result.1).1, some coords),
              builtX x session coords drawn.2 result) := by
  change (fun r => (r.1.1, r.2)) <$> ((PqxdhDeploymentIdealKernel.slotRunX PqxdhDeploymentIdealKernel.lazyDummy
    (PqxdhDeploymentIdealKernel.buildStepC setup codec checks route (PqxdhDeploymentIdealSteps.erasedHidden setup codec
      checks) created session payload)).run x >>= PqxdhDeploymentIdealDefer.serverInstall) = _
  have step : (PqxdhDeploymentIdealKernel.buildStepC setup codec checks route
      (PqxdhDeploymentIdealSteps.erasedHidden setup codec checks) created session payload).run
        (PqxdhDeploymentIdealKeys.detachX x) =
      (PqxdhDeploymentIdealKernel.buildHiddenC (PqxdhDeploymentIdealSteps.erasedHidden setup codec checks)
        session payload coords).run (PqxdhDeploymentIdealKeys.detachX x) := by
    change (match x.backend.2.2.marks with
      | some (index, coords) => if index = session ∧ (x.base.native.shared.2.pending session).isSome then _ else _
      | none => _) = _
    rw [marked]
    simp only [pending, Option.isSome_some, and_self, ↓reduceIte]
  change (fun r => (r.1.1, r.2)) <$> (((fun r => (r.1, PqxdhDeploymentIdealKeys.attachX r.2.1 r.2.2.1 r.2.2.2)) <$>
    (PqxdhDeploymentIdealErase.onPair PqxdhDeploymentIdealKernel.lazyDummy
      (PqxdhDeploymentIdealKernel.buildStepC setup codec checks route (PqxdhDeploymentIdealSteps.erasedHidden setup codec
        checks) created session payload)).run
      (PqxdhDeploymentIdealKeys.detachX x, (x.backend.2.1, (x.backend.1, x.seeds)))) >>=
        PqxdhDeploymentIdealDefer.serverInstall) = _
  rw [PqxdhDeploymentIdealErase.onPair_run, step]
  unfold PqxdhDeploymentIdealKernel.buildHiddenC
  rw [PqxdhDeploymentIdealErase.readAt_bind_run, simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
  dsimp only
  rw [PqxdhRegistrationJointKemSecondEntry.slot_some _ _ (x.backend.2.1, (x.backend.1, x.seeds)) j allocated,
    PqxdhDeploymentIdealDefer.lazyDummy_run]
  simp only [Functor.map_map, bind_map_left, map_bind, bind_assoc]
  refine bind_congr fun drawn => ?_
  rw [PqxdhDeploymentIdealErase.onSlots_run, PqxdhDeploymentIdealErase.slotImpl_coins, StateT.run_map]
  change ((fun a => (a, x.backend.2.1, drawn.2, x.seeds)) <$> (fun p => ((p.1, some coords), p.2)) <$>
    ((fun r => (r.1, { PqxdhDeploymentIdealKeys.detachX x with
      base := { (PqxdhDeploymentIdealKeys.detachX x).base with native := { (PqxdhDeploymentIdealKeys.detachX x).base.native with
        shared := r.2 } }
      backend := { (PqxdhDeploymentIdealKeys.detachX x).backend with
        peer := ((publishedKey r.1 r.2.2.server).map fun keyId => (keyId, coords)).or
          (PqxdhDeploymentIdealKeys.detachX x).backend.peer } })) <$>
      (PqxdhDeploymentIdealSteps.buildHidden (PqxdhDeploymentIdealSteps.erasedHidden setup codec checks
        (PqxdhDeploymentHiddenLayout.joinOutput drawn.1 PqxdhDeploymentHiddenSplit.dummySeed)) session payload).run
          x.base.native.shared)) >>= _ = _
  rw [buildHidden_run]
  simp only [pending, Functor.map_map, bind_map_left]
  rfl

/-- The final split form's hidden Server install when the build published no peer: nothing. -/
theorem serverInstall_quiet (reply : Option PqxdhServerRegistrationPublication.Response) (coords : Option Coord)
    (x : PqxdhDeploymentBackend.XState KemSK SplitBk 2)
    (quiet : publishedKey reply x.base.native.shared.2.server = none) :
    PqxdhDeploymentIdealDefer.serverInstall ((reply, coords), x) = pure ((reply, coords), x) := by
  unfold PqxdhDeploymentIdealDefer.serverInstall PqxdhDeploymentIdealDefer.xInstall
  rcases coords with _ | c
  · rfl
  · simp only []
    rcases x.backend.2.1.1 c with _ | j
    · rfl
    · have closed : (publishedKey reply (PqxdhDeploymentIdealKeys.detachX x).base.native.shared.2.server).isSome = false := by
        change (publishedKey reply x.base.native.shared.2.server).isSome = false
        rw [quiet]
        rfl
      simp only [closed, Bool.false_eq_true, ↓reduceIte]

/-- The final split form's hidden Server install when the build published a peer at an allocated slot: the lazy seed of the slot and the World's Server kernel of it on the published peer. -/
theorem serverInstall_published (reply : Option PqxdhServerRegistrationPublication.Response) (coords : Coord)
    (x : PqxdhDeploymentBackend.XState KemSK SplitBk 2) (j : PqxdhRecordLiftInterface.Slot 2)
    (allocated : x.backend.2.1.1 coords = some j)
    (published : (publishedKey reply x.base.native.shared.2.server).isSome = true) :
    PqxdhDeploymentIdealDefer.serverInstall ((reply, some coords), x) =
      (fun r => ((reply, some coords), { x with
        base := { x.base with native := { x.base.native with
          shared := PqxdhDeploymentIdealKernel.peerFix reply x.base.native.shared (PqxdhRecordLiftWorld.kernel .server r.1) } }
        seeds := r.2 })) <$> ((PqxdhRecordLiftWorld.SeedSpec 2).randomOracle j).run x.seeds := by
  unfold PqxdhDeploymentIdealDefer.serverInstall PqxdhDeploymentIdealDefer.xInstall
  simp only [allocated]
  have opened : (publishedKey reply (PqxdhDeploymentIdealKeys.detachX x).base.native.shared.2.server).isSome = true :=
    published
  simp only [opened, ↓reduceIte]
  change _ <$> ((fun r => (r.1, PqxdhDeploymentBackend.seedLens.set x r.2)) <$>
    ((PqxdhRecordLiftWorld.SeedSpec 2).randomOracle j).run x.seeds) = _
  rw [Functor.map_map]
  rfl

/-- Stripping does not see the kernel of a published peer. -/
theorem strip_builtSettled_publish (state : PqxdhRegistrationSchedule.State KemSK) (session : ℕ)
    (response : PqxdhServerRegistrationPublication.Response) (server : PqxdhServerAuthEntryFactor.ServerState)
    (candidate : pqxdh.ServerRegistrationCandidate) (first second : beaconcrypt_core.ratchet.concrete.ConcreteRatchetKernel)
    (log : List RawCtxSourceSend.SealContext) :
    strip (builtSettled state session
        (some response, PqxdhServerRegistrationPublication.publish server candidate first ()) log) =
      strip (builtSettled state session
        (some response, PqxdhServerRegistrationPublication.publish server candidate second ()) log) := by
  simp only [strip, builtSettled, PqxdhServerRegistrationPublication.publish]
  congr 5
  funext keyId
  by_cases same : keyId = candidate.key_id
  · subst same
    simp only [Function.update_self, Option.map_some, PqxdhDeploymentEnvironment.stripPeer]
  · simp only [Function.update_of_ne same]

/-- Setting a peer kernel at a key ID without a local copy commutes with CE-3's override. -/
theorem setPeerKernel_override (copies : PqxdhDeploymentCompile.Local) (server : PqxdhServerAuthEntryFactor.ServerState)
    (keyId : Std.U64) (kernel : beaconcrypt_core.ratchet.concrete.ConcreteRatchetKernel)
    (none : copies.peers keyId = none) :
    PqxdhDeploymentHiddenSplit.setPeerKernel (PqxdhDeploymentCompileRegistration.overrideServer copies server) keyId kernel =
      PqxdhDeploymentCompileRegistration.overrideServer copies
        (PqxdhDeploymentHiddenSplit.setPeerKernel server keyId kernel) := by
  simp only [PqxdhDeploymentHiddenSplit.setPeerKernel, PqxdhDeploymentCompileRegistration.overrideServer]
  congr 2
  funext other
  by_cases same : other = keyId
  · subst same
    simp only [Function.update_self, none]
    cases server.server.peers other <;> rfl
  · simp only [Function.update_of_ne same]

open PqxdhDeploymentEnvironmentReal (law_uncount frameGame worldCopies override_world override_publish installed_world
  run_support Built installPeer) in
/-- The marked build in capability form splits the final split form's marked build at an allocated slot with a pending token, when the World's Server marker of the slot is unused: the reassembled law is the split form's, exactly. -/
theorem buildHidden_law (t : PqxdhDeploymentIdealParams.Target count)
    (p : PqxdhDeploymentIdealParams.Params KemSK count) (created : PqxdhLiveServerConstruction.Created Unit)
    (session : ℕ) (payload : Option Pqxdh.Bytes) (e : EnvState KemSK SplitBk) (w : PqxdhRecordLiftWorld.State 2)
    (good : Good created e w) (coords : Coord) (j : PqxdhRecordLiftInterface.Slot 2)
    (token : PqxdhServerRelatedRootConsumer.Returned) (marked : e.backend.2.2.marks = some (session, coords))
    (pending : e.native.shared.2.pending session = some token) (allocated : e.backend.2.1.1 coords = some j)
    (unused : w.used j .server = false) :
    (fun result => (result.1.1, merge result.1.2 result.2)) <$> (simulateQ PqxdhRecordLiftWorld.effects
        ((buildHiddenEnv setup codec checks session payload coords).run e)).run w =
      (PqxdhDeploymentIdealDefer.idealSplit setup codec route checks t p created ⟨.build session payload, trivial⟩).run
        (merge e w) := by
  obtain ⟨world, found, sender, identity, peersRaw⟩ := good.server
  have serverEq := PqxdhDeploymentIdealEnvReal.frameGame_server created e w good world found
  rw [law_uncount, buildHidden_effects setup codec checks session payload coords e w j token allocated pending,
    idealSplit_build_hidden setup codec route checks t p created session payload (merge e w) coords j token marked pending
      allocated]
  rw [show (merge e w).base.native.shared.2.server = PqxdhDeploymentCompileRegistration.overrideServer (worldCopies world)
      e.native.shared.2.server by
    rw [← serverEq, show (merge e w).base.native = PqxdhDeploymentEnvironmentJoin.fill w e.native from rfl,
      PqxdhDeploymentEnvironmentReal.fill_some w world found],
    show (merge e w).base.native.shared.2.ctx = w.primitive.2 by
    rw [show (merge e w).base.native = PqxdhDeploymentEnvironmentJoin.fill w e.native from rfl,
      PqxdhDeploymentEnvironmentReal.fill_some w world found]
    rfl]
  rw [map_bind]
  refine bind_congr fun drawn => ?_
  rw [freeBuild_override _ _ _ _ _ _ (installed_world world e.native.shared.2 peersRaw), simulateQ_map, StateT.run_map,
    PqxdhDeploymentEnvironment.tail_factor ctxAdmin setup codec checks, Functor.map_map, bind_map_left,
    PqxdhDeploymentSplitFactor.buildSplitFwd_free, StateT.run_map, simulateQ_map, StateT.run_map, bind_map_left, map_bind]
  apply OracleComp.bind_congr_of_forall_mem_support
  rintro ⟨⟨rust, log⟩, cache⟩ member
  have built : Built e.native.shared.2.server () rust :=
    freeBuild_shape _ _ _ _ _ rust (run_support _ _ [] (rust, log) (run_support _ _ w.primitive.2 ((rust, log), cache) member))
  dsimp only
  have quiet : ∀ rust' : RustM (Option PqxdhServerRegistrationPublication.Response ×
      PqxdhServerRegistrationPublication.State Unit Unit (List Pqxdh.Bytes)),
      PqxdhServerAuthExperiment.settle e.native.shared.2.server rust' = (none, e.native.shared.2.server) →
      PqxdhServerAuthExperiment.settle e.native.shared.2.server
        (PqxdhDeploymentHiddenSplit.replaceRaw PqxdhDeploymentHiddenSplit.placeholderKernel <$> rust') =
          (none, e.native.shared.2.server) →
      (fun result => (result.1.1, merge result.1.2 result.2)) <$> Prod.map id uncount <$>
        (simulateQ PqxdhRecordLiftWorld.effects (PqxdhDeploymentEnvironment.hiddenServerEffect j
          (PqxdhServerAuthExperiment.settle e.native.shared.2.server
            (PqxdhDeploymentHiddenSplit.replaceRaw PqxdhDeploymentHiddenSplit.placeholderKernel <$> rust')) >>= fun _ =>
          pure ((PqxdhServerAuthExperiment.settle e.native.shared.2.server
            (PqxdhDeploymentHiddenSplit.replaceRaw PqxdhDeploymentHiddenSplit.placeholderKernel <$> rust')).1,
            builtEnv e session coords drawn.2 (PqxdhServerAuthExperiment.settle e.native.shared.2.server
              (PqxdhDeploymentHiddenSplit.replaceRaw PqxdhDeploymentHiddenSplit.placeholderKernel <$> rust'), log)))).run
          (withCache w cache) =
      (fun r => (r.1.1, r.2)) <$> PqxdhDeploymentIdealDefer.serverInstall
        (((PqxdhServerAuthExperiment.settle (PqxdhDeploymentCompileRegistration.overrideServer (worldCopies world)
          e.native.shared.2.server) (PqxdhDeploymentCompileRegistration.mapBuilt (worldCopies world) rust')).1,
            some coords), builtX (merge e w) session coords drawn.2
              (PqxdhDeploymentCompileRegistration.mapBuilt (worldCopies world) rust', (log, cache))) := by
    intro rust' settledQuiet replacedQuiet
    have settledNative := PqxdhDeploymentCompileRegistration.settle_override (worldCopies world) e.native.shared.2.server
      rust'
    rw [settledQuiet] at settledNative
    rw [replacedQuiet, settledNative]
    have effect : PqxdhDeploymentEnvironment.hiddenServerEffect (n := 2) j (none, e.native.shared.2.server) = pure () :=
      rfl
    rw [effect, pure_bind, simulateQ_pure, StateT.run_pure, map_pure, map_pure,
      serverInstall_quiet _ _ _ rfl, map_pure]
    have merged := PqxdhDeploymentIdealEnvReal.build_merge created session e w good world found rust' log cache world rfl
      (by rw [settledQuiet]; exact override_world world _ identity peersRaw) (by rw [settledQuiet])
    rw [PqxdhDeploymentIdealEnvReal.withCache_server w cache world found] at merged
    have nativeEq : PqxdhDeploymentEnvironmentReal.builtNative e.native session (rust', log) =
        builtSettled e.native session (none, e.native.shared.2.server) log := by
      simp only [PqxdhDeploymentEnvironmentReal.builtNative, builtSettled, settledQuiet]
    rw [nativeEq] at merged
    have baseEq := congrArg PqxdhDeploymentBackend.XState.base merged
    have fillEq := PqxdhDeploymentEnvironmentReal.fill_some w world found e.native
    congr 1
    refine Prod.ext rfl ?_
    change PqxdhDeploymentBackend.XState.mk (merge { e with
        native := strip (builtSettled e.native session (none, e.native.shared.2.server) log) }
          (uncount (withCache w cache))).base _ _ _ _ = PqxdhDeploymentBackend.XState.mk _ _ _ _ _
    rw [baseEq]
    simp only [merge, fillEq, serverEq, settledNative, builtEnv, Prod.map, id, publishedKey, Option.map_none,
      Option.none_or]
    rfl
  rcases rust with ⟨_ | response, after⟩ | error | _
  · have same : after = e.native.shared.2.server := built
    subst same
    exact quiet _ rfl rfl
  · obtain ⟨candidate, kernel, keyEq, vacant, published⟩ := built
    subst published
    have vacantWorld : world.records.server.peers candidate.key_id = none := by
      have mapped := peersRaw candidate.key_id
      rw [vacant] at mapped
      cases hworld : world.records.server.peers candidate.key_id with
      | none => rfl
      | some peer => rw [hworld] at mapped; cases mapped
    have noCopy : (worldCopies world).peers candidate.key_id = none := by
      simp only [worldCopies, vacantWorld, Option.map_none]
    have replaced : PqxdhServerAuthExperiment.settle e.native.shared.2.server
        (PqxdhDeploymentHiddenSplit.replaceRaw PqxdhDeploymentHiddenSplit.placeholderKernel <$>
          RustM.ok (some response, PqxdhServerRegistrationPublication.publish e.native.shared.2.server candidate kernel ())) =
        (some response, PqxdhServerRegistrationPublication.publish e.native.shared.2.server candidate
          PqxdhDeploymentHiddenSplit.placeholderKernel ()) := by
      change (some response, PqxdhDeploymentHiddenSplit.setPeerKernel (PqxdhServerRegistrationPublication.publish
        e.native.shared.2.server candidate kernel ()) response.keyId PqxdhDeploymentHiddenSplit.placeholderKernel) = _
      rw [keyEq, PqxdhDeploymentHiddenSplit.publish_setPeerKernel]
    have peerAt := (PqxdhServerRegistrationPublication.publish_fields e.native.shared.2.server candidate
      PqxdhDeploymentHiddenSplit.placeholderKernel ()).1
    have effect : PqxdhDeploymentEnvironment.hiddenServerEffect (n := 2) j (some response,
        PqxdhServerRegistrationPublication.publish e.native.shared.2.server candidate
          PqxdhDeploymentHiddenSplit.placeholderKernel ()) =
        PqxdhDeploymentEnvironment.issue (.installServer response.keyId candidate.beacon_identity_public_key (.hidden j)) := by
      unfold PqxdhDeploymentEnvironment.hiddenServerEffect
      simp only [keyEq, peerAt]
    rw [replaced, effect, PqxdhDeploymentEnvironmentReal.effects_issue_then,
      effects_hiddenServer response.keyId candidate.beacon_identity_public_key j (withCache w cache) world found
        (by rw [keyEq]; exact vacantWorld) unused]
    have serverM : (merge e w).base.native.shared.2.server =
        PqxdhDeploymentCompileRegistration.overrideServer (worldCopies world) e.native.shared.2.server := by
      rw [← serverEq, show (merge e w).base.native = PqxdhDeploymentEnvironmentJoin.fill w e.native from rfl,
        PqxdhDeploymentEnvironmentReal.fill_some w world found]
    have publishedNative : publishedKey (some response) (PqxdhDeploymentCompileRegistration.overrideServer
        (worldCopies world) (PqxdhServerRegistrationPublication.publish e.native.shared.2.server candidate kernel ())) =
        some response.keyId := by
      simp only [publishedKey, PqxdhDeploymentCompileRegistration.overrideServer,
        PqxdhServerRegistrationPublication.publish, keyEq, Function.update_self, Option.map_some]
    rw [serverInstall_published _ coords _ j allocated (by
      change (publishedKey (some response) (PqxdhServerAuthExperiment.settle (merge e w).base.native.shared.2.server
        (PqxdhDeploymentCompileRegistration.mapBuilt (worldCopies world) (RustM.ok (some response,
          PqxdhServerRegistrationPublication.publish e.native.shared.2.server candidate kernel ())))).2).isSome = true
      rw [serverM]
      change (publishedKey (some response) (PqxdhDeploymentCompileRegistration.overrideServer (worldCopies world)
        (PqxdhServerRegistrationPublication.publish e.native.shared.2.server candidate kernel ()))).isSome = true
      rw [publishedNative]
      rfl)]
    have project : ((PqxdhRecordLiftWorld.SeedSpec 2).randomOracle j).run w.seeds.1 =
        Prod.map id Prod.fst <$> (PqxdhRecordLiftLazyTable.impl j).run w.seeds := by
      have projected := PqxdhRecordLiftLazyTable.run_project (spec := PqxdhRecordLiftWorld.SeedSpec 2)
        (liftM ((PqxdhRecordLiftWorld.SeedSpec 2).query j)) w.seeds
      simp only [simulateQ_spec_query] at projected
      exact projected.symm
    change _ = _ <$> (_ <$> ((PqxdhRecordLiftWorld.SeedSpec 2).randomOracle j).run w.seeds.1)
    rw [project]
    change _ <$> (_ <$> (_ <$> (PqxdhRecordLiftLazyTable.impl j).run w.seeds)) = _
    simp only [Functor.map_map]
    congr 1
    funext r
    obtain ⟨seed, table⟩ := r
    have merged := PqxdhDeploymentIdealEnvReal.build_merge created session e w good world found
      (RustM.ok (some response, PqxdhServerRegistrationPublication.publish e.native.shared.2.server candidate
        (PqxdhRecordLiftWorld.kernel .server seed) ())) log cache
      (installPeer world candidate.key_id candidate.beacon_identity_public_key (PqxdhRecordLiftWorld.kernel .server seed))
      rfl (override_publish world _ identity peersRaw candidate _ vacantWorld) rfl
    have nativeEq : PqxdhDeploymentEnvironmentReal.builtNative e.native session (RustM.ok (some response,
        PqxdhServerRegistrationPublication.publish e.native.shared.2.server candidate
          (PqxdhRecordLiftWorld.kernel .server seed) ()), log) =
        builtSettled e.native session (some response, PqxdhServerRegistrationPublication.publish e.native.shared.2.server
          candidate (PqxdhRecordLiftWorld.kernel .server seed) ()) log := rfl
    have baseEq := congrArg PqxdhDeploymentBackend.XState.base merged
    rw [nativeEq, ← strip_builtSettled_publish e.native session response e.native.shared.2.server candidate
      PqxdhDeploymentHiddenSplit.placeholderKernel (PqxdhRecordLiftWorld.kernel .server seed) log] at baseEq
    have fillEq := PqxdhDeploymentEnvironmentReal.fill_some w world found e.native
    have fixed : PqxdhDeploymentHiddenSplit.setPeerKernel (PqxdhDeploymentCompileRegistration.overrideServer
        (worldCopies world) (PqxdhServerRegistrationPublication.publish e.native.shared.2.server candidate kernel ()))
          candidate.key_id (PqxdhRecordLiftWorld.kernel .server seed) =
        PqxdhDeploymentCompileRegistration.overrideServer (worldCopies world)
          (PqxdhServerRegistrationPublication.publish e.native.shared.2.server candidate
            (PqxdhRecordLiftWorld.kernel .server seed) ()) := by
      rw [setPeerKernel_override _ _ _ _ noCopy, PqxdhDeploymentHiddenSplit.publish_setPeerKernel]
    have settledM : ∀ kernel' : beaconcrypt_core.ratchet.concrete.ConcreteRatchetKernel,
        PqxdhServerAuthExperiment.settle (PqxdhDeploymentCompileRegistration.overrideServer (worldCopies world)
          e.native.shared.2.server) (PqxdhDeploymentCompileRegistration.mapBuilt (worldCopies world)
            (RustM.ok (some response, PqxdhServerRegistrationPublication.publish e.native.shared.2.server candidate
              kernel' ()))) =
        (some response, PqxdhDeploymentCompileRegistration.overrideServer (worldCopies world)
          (PqxdhServerRegistrationPublication.publish e.native.shared.2.server candidate kernel' ())) := fun _ => rfl
    have publishedEnv : publishedKey (some response) (PqxdhServerRegistrationPublication.publish e.native.shared.2.server
        candidate PqxdhDeploymentHiddenSplit.placeholderKernel ()) = some response.keyId := by
      simp only [publishedKey, PqxdhServerRegistrationPublication.publish, keyEq, Function.update_self, Option.map_some]
    rw [keyEq]
    refine Prod.ext rfl ?_
    change PqxdhDeploymentBackend.XState.mk (merge { e with native := strip (builtSettled e.native session
        (some response, PqxdhServerRegistrationPublication.publish e.native.shared.2.server candidate
          PqxdhDeploymentHiddenSplit.placeholderKernel ()) log) }
        (uncount { withCache w cache with server := some (installPeer world candidate.key_id
          candidate.beacon_identity_public_key (PqxdhRecordLiftWorld.kernel .server seed)) })).base _ _ _ _ =
      PqxdhDeploymentBackend.XState.mk _ _ _ _ _
    rw [baseEq]
    simp only [builtX, merge, fillEq, serverEq, builtEnv, Prod.map, id, PqxdhDeploymentIdealKernel.peerFix,
      PqxdhDeploymentEnvironmentReal.builtGame, settledM, publishedEnv, publishedNative, keyEq, fixed]
    rfl
  · exact quiet _ rfl rfl
  · exact quiet _ rfl rfl

open PqxdhDeploymentEnvironmentReal (worldCopies run_support Built installPeer) in
/-- Every outcome of the marked build in capability form at an allocated slot with a pending token, with the World's counts forgotten, from an admissible state whose World Server marker of the slot is unused: either nothing was published (the token consumed, the seals logged, the World's CTX cache advanced) or one peer was published at a key ID vacant before, the World installed it with its Server kernel of the slot's seed, which its seed table now holds, and set the slot's Server marker. -/
theorem buildHidden_outcome (created : PqxdhLiveServerConstruction.Created Unit) (session : ℕ)
    (payload : Option Pqxdh.Bytes) (coords : Coord) (e : EnvState KemSK SplitBk) (w : PqxdhRecordLiftWorld.State 2)
    (good : Good created e w) (j : PqxdhRecordLiftInterface.Slot 2) (token : PqxdhServerRelatedRootConsumer.Returned)
    (allocated : e.backend.2.1.1 coords = some j) (pending : e.native.shared.2.pending session = some token)
    (unused : w.used j .server = false) (world : PqxdhRecordLiftWorld.Server) (found : w.server = some world) :
    ∀ result ∈ support (Prod.map id uncount <$> (simulateQ PqxdhRecordLiftWorld.effects
        ((buildHiddenEnv setup codec checks session payload coords).run e)).run w),
      ∃ material log cache,
        (result.1.1 = none ∧ result.1.2 = builtEnv e session coords material ((none, e.native.shared.2.server), log) ∧
          result.2 = uncount (withCache w cache)) ∨
        (∃ response candidate seed table, response.keyId = candidate.key_id ∧
          e.native.shared.2.server.server.peers candidate.key_id = none ∧ table.1 j = some seed ∧
          w.seeds.1 ≤ table.1 ∧ result.1.1 = some response ∧
          result.1.2 = builtEnv e session coords material ((some response, PqxdhServerRegistrationPublication.publish
            e.native.shared.2.server candidate PqxdhDeploymentHiddenSplit.placeholderKernel ()), log) ∧
          result.2 = uncount { withCache w cache with
            seeds := table
            used := Function.update w.used j (Function.update (w.used j) .server true)
            server := some (installPeer world candidate.key_id candidate.beacon_identity_public_key
              (PqxdhRecordLiftWorld.kernel .server seed)) }) := by
  obtain ⟨world', found', _, _, peersRaw⟩ := good.server
  rw [found] at found'
  cases found'
  intro result supported
  rw [buildHidden_effects setup codec checks session payload coords e w j token allocated pending,
    mem_support_bind_iff] at supported
  obtain ⟨drawn, _, supported⟩ := supported
  rw [mem_support_bind_iff, PqxdhDeploymentSplitFactor.buildSplitFwd_free, StateT.run_map, simulateQ_map,
    StateT.run_map, support_map] at supported
  obtain ⟨_, ⟨⟨⟨rust, log⟩, cache⟩, member, rfl⟩, final⟩ := supported
  have built : Built e.native.shared.2.server () rust :=
    freeBuild_shape _ _ _ _ _ rust (run_support _ _ [] (rust, log) (run_support _ _ w.primitive.2 ((rust, log), cache) member))
  refine ⟨drawn.2, log, cache, ?_⟩
  have effect : PqxdhDeploymentEnvironment.hiddenServerEffect (n := 2) j (none, e.native.shared.2.server) = pure () :=
    rfl
  rcases rust with ⟨_ | response, after⟩ | error | _
  · have same : after = e.native.shared.2.server := built
    subst same
    change result ∈ support (Prod.map id uncount <$> (simulateQ PqxdhRecordLiftWorld.effects
      (PqxdhDeploymentEnvironment.hiddenServerEffect j (none, e.native.shared.2.server) >>= fun _ =>
        pure (none, builtEnv e session coords drawn.2 ((none, e.native.shared.2.server), log)))).run
          (withCache w cache)) at final
    rw [effect, pure_bind, simulateQ_pure, StateT.run_pure, map_pure, support_pure, Set.mem_singleton_iff] at final
    subst final
    exact Or.inl ⟨rfl, rfl, rfl⟩
  · obtain ⟨candidate, kernel, keyEq, vacant, published⟩ := built
    subst published
    have vacantWorld : world.records.server.peers candidate.key_id = none := by
      have mapped := peersRaw candidate.key_id
      rw [vacant] at mapped
      cases hworld : world.records.server.peers candidate.key_id with
      | none => rfl
      | some peer => rw [hworld] at mapped; cases mapped
    have replaced : PqxdhServerAuthExperiment.settle e.native.shared.2.server
        (PqxdhDeploymentHiddenSplit.replaceRaw PqxdhDeploymentHiddenSplit.placeholderKernel <$>
          RustM.ok (some response, PqxdhServerRegistrationPublication.publish e.native.shared.2.server candidate kernel ())) =
        (some response, PqxdhServerRegistrationPublication.publish e.native.shared.2.server candidate
          PqxdhDeploymentHiddenSplit.placeholderKernel ()) := by
      change (some response, PqxdhDeploymentHiddenSplit.setPeerKernel (PqxdhServerRegistrationPublication.publish
        e.native.shared.2.server candidate kernel ()) response.keyId PqxdhDeploymentHiddenSplit.placeholderKernel) = _
      rw [keyEq, PqxdhDeploymentHiddenSplit.publish_setPeerKernel]
    have peerAt := (PqxdhServerRegistrationPublication.publish_fields e.native.shared.2.server candidate
      PqxdhDeploymentHiddenSplit.placeholderKernel ()).1
    have effect : PqxdhDeploymentEnvironment.hiddenServerEffect (n := 2) j (some response,
        PqxdhServerRegistrationPublication.publish e.native.shared.2.server candidate
          PqxdhDeploymentHiddenSplit.placeholderKernel ()) =
        PqxdhDeploymentEnvironment.issue (.installServer response.keyId candidate.beacon_identity_public_key (.hidden j)) := by
      unfold PqxdhDeploymentEnvironment.hiddenServerEffect
      simp only [keyEq, peerAt]
    rw [replaced, effect, PqxdhDeploymentEnvironmentReal.effects_issue_then,
      effects_hiddenServer response.keyId candidate.beacon_identity_public_key j (withCache w cache) world found
        (by rw [keyEq]; exact vacantWorld) unused, Functor.map_map, support_map] at final
    obtain ⟨⟨seed, table⟩, inTable, rfl⟩ := final
    have facts := PqxdhRecordLiftLazyTable.step_facts j w.seeds (seed, table) inTable
    refine Or.inr ⟨response, candidate, seed, table, keyEq, vacant, facts.1, facts.2.1, rfl, rfl, ?_⟩
    rw [keyEq]
    rfl
  · change result ∈ support (Prod.map id uncount <$> (simulateQ PqxdhRecordLiftWorld.effects
      (PqxdhDeploymentEnvironment.hiddenServerEffect j (none, e.native.shared.2.server) >>= fun _ =>
        pure (none, builtEnv e session coords drawn.2 ((none, e.native.shared.2.server), log)))).run
          (withCache w cache)) at final
    rw [effect, pure_bind, simulateQ_pure, StateT.run_pure, map_pure, support_pure, Set.mem_singleton_iff] at final
    subst final
    exact Or.inl ⟨rfl, rfl, rfl⟩
  · change result ∈ support (Prod.map id uncount <$> (simulateQ PqxdhRecordLiftWorld.effects
      (PqxdhDeploymentEnvironment.hiddenServerEffect j (none, e.native.shared.2.server) >>= fun _ =>
        pure (none, builtEnv e session coords drawn.2 ((none, e.native.shared.2.server), log)))).run
          (withCache w cache)) at final
    rw [effect, pure_bind, simulateQ_pure, StateT.run_pure, map_pure, support_pure, Set.mem_singleton_iff] at final
    subst final
    exact Or.inl ⟨rfl, rfl, rfl⟩

open PqxdhDeploymentEnvironmentReal (worldCopies installPeer good_intro good_server good_matched keeps_uncount
  good_uncount) in
/-- The marked build in capability form keeps admissibility, from an admissible state at an allocated slot with a pending token whose World Server marker of the slot is unused. -/
theorem buildHidden_keeps (created : PqxdhLiveServerConstruction.Created Unit) (session : ℕ)
    (payload : Option Pqxdh.Bytes) (coords : Coord) (e : EnvState KemSK SplitBk) (w : PqxdhRecordLiftWorld.State 2)
    (good : Good created e w) (j : PqxdhRecordLiftInterface.Slot 2) (token : PqxdhServerRelatedRootConsumer.Returned)
    (allocated : e.backend.2.1.1 coords = some j) (pending : e.native.shared.2.pending session = some token)
    (unused : w.used j .server = false) :
    ∀ result ∈ support ((simulateQ PqxdhRecordLiftWorld.effects
        ((buildHiddenEnv setup codec checks session payload coords).run e)).run w),
      Good created result.1.2 result.2 := by
  obtain ⟨world, found, sender, identity, peers⟩ := good_server created e w good
  apply keeps_uncount _ (Good created) (good_uncount created)
  intro result supported
  obtain ⟨material, log, cache, outcome⟩ := buildHidden_outcome setup codec checks created session payload coords e w good
    j token allocated pending unused world found result supported
  rcases outcome with ⟨_, envEq, worldEq⟩ | ⟨response, candidate, seed, table, keyEq, vacant, _, _, _, envEq, worldEq⟩
  · rw [envEq, worldEq]
    exact good_intro created _ (builtSettled e.native session (none, e.native.shared.2.server) log) _ world rfl
      good.createdEq found sender identity peers good.ownersLength (good_matched created e w good)
  · rw [envEq, worldEq]
    refine good_intro created _ (builtSettled e.native session (some response, PqxdhServerRegistrationPublication.publish
      e.native.shared.2.server candidate PqxdhDeploymentHiddenSplit.placeholderKernel ()) log) _ _ rfl good.createdEq rfl
      sender identity (fun keyId => ?_) good.ownersLength (good_matched created e w good)
    simp only [builtSettled, installPeer, PqxdhServerRegistrationPublication.publish]
    by_cases same : keyId = candidate.key_id
    · subst same
      simp only [Function.update_self, Option.map_some]
      rfl
    · simp only [Function.update_of_ne same]
      exact peers keyId

end HiddenBuild

end BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvBuild

-- Axiom guards (generated)

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvBuild.publish_mapPeers' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvBuild.publish_mapPeers

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvBuild.afterInitialization_mapPeers' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvBuild.afterInitialization_mapPeers

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvBuild.candidate_mapPeers' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvBuild.candidate_mapPeers

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvBuild.genericBuild_mapPeers' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvBuild.genericBuild_mapPeers

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvBuild.afterInitializationG_shape' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvBuild.afterInitializationG_shape

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvBuild.continueRustG_shape' depends on axioms: [propext,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvBuild.continueRustG_shape

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvBuild.candidateG_shape' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvBuild.candidateG_shape

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvBuild.genericBuild_shape' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvBuild.genericBuild_shape

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvBuild.embed_override' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvBuild.embed_override

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvBuild.native_override' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvBuild.native_override

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvBuild.freeBuild_override' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvBuild.freeBuild_override

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvBuild.freeBuild_shape' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvBuild.freeBuild_shape

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvBuild.resolve_uncount' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvBuild.resolve_uncount

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvBuild.effects_hiddenServer' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvBuild.effects_hiddenServer

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvBuild.countFree_hiddenServer' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvBuild.countFree_hiddenServer

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvBuild.buildSplitFwd_noAdmin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvBuild.buildSplitFwd_noAdmin

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvBuild.countFree_hiddenServerEffect' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvBuild.countFree_hiddenServerEffect

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvBuild.buildHidden_effects' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvBuild.buildHidden_effects

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvBuild.buildHidden_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvBuild.buildHidden_run

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvBuild.idealSplit_build_hidden' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvBuild.idealSplit_build_hidden

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvBuild.serverInstall_quiet' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvBuild.serverInstall_quiet

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvBuild.serverInstall_published' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvBuild.serverInstall_published

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvBuild.strip_builtSettled_publish' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvBuild.strip_builtSettled_publish

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvBuild.setPeerKernel_override' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvBuild.setPeerKernel_override

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvBuild.buildHidden_law' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvBuild.buildHidden_law

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvBuild.buildHidden_outcome' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvBuild.buildHidden_outcome

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvBuild.buildHidden_keeps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvBuild.buildHidden_keeps
