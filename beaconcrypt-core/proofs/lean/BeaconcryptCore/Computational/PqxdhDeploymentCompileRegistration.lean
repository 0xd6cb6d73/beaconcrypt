-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhDeploymentCompileRecords

/-! Registration commands of the CE-3 trial (item a of the compile lemma). The source14 registration handlers never read a Server peer kernel or an established Beacon kernel: accept, public HMAC and BLAKE2b do not read the peer map at all, build reads it only through occupancy and installs a new peer only at an unoccupied key ID, and bundle and finish return without any effect on an established owner. Hence replacing every copied kernel by its live local copy commutes with each registration command, and the compiled program, which forwards these commands unchanged, has after merging exactly the native command's reply and deployment poststate. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhDeploymentCompileRegistration
open PqxdhServerAuthExperiment PqxdhServerAuthNative PqxdhJointIdentity PqxdhJointGapDh
open PqxdhDeploymentCompile (Kernel Local merge mergePeer mergeOwner)
open PqxdhJointDhExtractRoot (RootSpec)
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}

/-- The Server registration state with every copied peer kernel replaced by its live local copy. -/
def overrideServer (copies : Local) (server : PqxdhServerRegistrationPublication.State Unit Unit (List Pqxdh.Bytes)) :
    PqxdhServerRegistrationPublication.State Unit Unit (List Pqxdh.Bytes) :=
  { server with server := { server.server with
    peers := fun kid => (server.server.peers kid).map (mergePeer (copies.peers kid)) } }

/-- The experiment game state with the Server override. -/
def overrideGame (copies : Local) (game : GameState KemSK) : GameState KemSK :=
  { game with server := overrideServer copies game.server }

/-- A game computation that commutes with the Server override from every state. -/
def GameCommutes {Result : Type} (copies : Local) (work : Game KemSK Result) : Prop :=
  ∀ game, work.run (overrideGame copies game) = Prod.map id (overrideGame copies) <$> work.run game

/-- Pure results commute with the override. -/
theorem pure_commutes {Result : Type} (copies : Local) (value : Result) :
    GameCommutes (KemSK := KemSK) copies (pure value) := by
  intro game
  simp only [StateT.run_pure, map_pure, Prod.map, id]

/-- Sequencing preserves commuting with the override. -/
theorem bind_commutes {Result Next : Type} (copies : Local) (work : Game KemSK Result)
    (next : Result → Game KemSK Next) (first : GameCommutes copies work)
    (rest : ∀ value, GameCommutes copies (next value)) :
    GameCommutes copies (work >>= next) := by
  intro game
  simp only [StateT.run_bind, first game, bind_map_left, map_bind]
  apply bind_congr
  intro result
  exact rest result.1 result.2

/-- Lifted family requests commute with the override. -/
theorem lift_commutes {Result : Type} (copies : Local) (work : OracleComp RootSpec Result) :
    GameCommutes (KemSK := KemSK) copies (StateT.lift work) := by
  intro game
  simp only [StateT.run_lift, Functor.map_map, bind_pure_comp]
  rfl

/-- A state update commutes with the override when the update commutes with it. -/
theorem modify_commutes (copies : Local) (change : GameState KemSK → GameState KemSK)
    (same : ∀ game, change (overrideGame copies game) = overrideGame copies (change game)) :
    GameCommutes copies (modify change : Game KemSK Unit) := by
  intro game
  simp only [StateT.run_modify, map_pure, same]
  rfl

/-- The session callbacks of the Server root consumer commute with the override. -/
theorem session_commutes (copies : Local) (index : Nat) (query : PqxdhServerRelatedRootConsumer.Spec.Domain) :
    GameCommutes (KemSK := KemSK) copies (sessionImpl index query) := by
  rcases query with query | query
  · rcases query with coin | request
    · exact lift_commutes copies _
    · cases request with
      | derive message =>
          exact bind_commutes copies _ _ (lift_commutes copies _) fun reply =>
            bind_commutes copies _ _ (modify_commutes copies _ fun _ => rfl) fun _ => pure_commutes copies _
      | _ => exact lift_commutes copies _
  · cases query with
    | consume rid => exact modify_commutes copies _ fun _ => rfl
    | _ => exact pure_commutes copies _

/-- An entire session callback program commutes with the override. -/
theorem simulate_commutes {Result : Type} (copies : Local) (index : Nat)
    (program : OracleComp PqxdhServerRelatedRootConsumer.Spec Result) :
    GameCommutes (KemSK := KemSK) copies (simulateQ (sessionImpl index) program) := by
  intro game
  exact (OracleComp.map_run_simulateQ_eq_of_query_map_eq (sessionImpl (KemSK := KemSK) index) (sessionImpl index)
    (overrideGame copies) (fun query state => (session_commutes copies index query state).symm) program game).symm

/-- `get_shared_secret` never reads the peer map; it commutes with the override. -/
theorem accept_commutes (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (copies : Local) (publicValue : PublicChallenge) (raw : Pqxdh.Bytes) :
    GameCommutes copies (acceptOracle setup codec checks publicValue raw) := by
  intro game
  simp only [acceptOracle, StateT.run_bind, StateT.run_get, pure_bind, liftCoins, StateT.run_lift, bind_assoc,
    StateT.run_set, map_bind]
  apply bind_congr
  intro collected
  have rest : ∀ result : Option (PqxdhServerRootPreparation.Inputs Reader ScalarBytes PeerEncoding),
      GameCommutes copies (match result with
        | none => pure none
        | some input => do
          let returned ← simulateQ (sessionImpl game.sessions)
            (PqxdhServerRelatedRootConsumer.client (binding setup publicValue) input)
          match returned with
          | .ok (some token) => do
              modify fun current => { current with pending := Function.update current.pending game.sessions (some token) }
              pure (some game.sessions)
          | _ => pure none : Game KemSK (Option Nat)) := by
    intro result
    rcases result with _ | input
    · exact pure_commutes copies _
    · refine bind_commutes copies _ _ (simulate_commutes copies _ _) (fun returned => ?_)
      rcases returned with (_ | token) | _ | _
      all_goals first
        | exact pure_commutes copies _
        | exact bind_commutes copies _ _ (modify_commutes copies _ fun _ => rfl) fun _ => pure_commutes copies _
  exact rest collected.1 { game with sessions := game.sessions + 1, server := { game.server with consumed := collected.2 } }

/-- The public HMAC never reads the peer map; it commutes with the override. -/
theorem hmac_commutes (copies : Local) (key : PqxdhSecretInputKdf.HmacBlock) (message : Pqxdh.Bytes) :
    GameCommutes (KemSK := KemSK) copies (hmacOracle key message) := by
  unfold hmacOracle
  split
  · exact bind_commutes copies _ _ (modify_commutes copies _ fun _ => rfl) fun _ => lift_commutes copies _
  · exact lift_commutes copies _

/-- The public BLAKE2b oracle never reads the peer map; it commutes with the override. -/
theorem hash_commutes (copies : Local) (bytes : Pqxdh.Bytes) :
    GameCommutes (KemSK := KemSK) copies (hashOracle bytes) := by
  intro game
  simp only [hashOracle, StateT.run, map_bind, map_pure]
  rfl

/-- A successful commit preparation was given an available key ID, and its candidate key ID is the next key ID of the control. -/
theorem prepare_key (state : beaconcrypt_core.pqxdh.ServerState) (pending : beaconcrypt_core.pqxdh.PendingServerRegistration)
    (current : beaconcrypt_core.pqxdh.ServerBinding) (availability : beaconcrypt_core.pqxdh.KeyIdAvailability)
    (candidate : beaconcrypt_core.pqxdh.ServerRegistrationCandidate)
    (prepared : beaconcrypt_core.pqxdh.server_prepare_commit state pending current availability = .ok (.Ok candidate)) :
    availability = .Available ∧ beaconcrypt_core.pqxdh.server_next_key_id state = .ok (.Ok candidate.key_id) := by
  obtain ⟨next, hnext⟩ := BeaconcryptCore.PanicFreedom.server_next_key_id_ok state
  obtain ⟨ad, had⟩ := BeaconcryptCore.PanicFreedom.build_associated_data_ok current.identity_public_key
    pending.beacon_identity_public_key
  simp only [beaconcrypt_core.pqxdh.server_prepare_commit, PqxdhRefinement.array_eq_abs, bind_tc_ok, hnext, had] at prepared
  split_ifs at prepared
  all_goals cases next
  all_goals cases availability
  all_goals simp_all
  subst prepared
  rfl

/-- Publishing at a key ID with no local copy commutes with the override. -/
theorem publish_override (copies : Local) (state : PqxdhServerRegistrationPublication.State Unit Unit (List Pqxdh.Bytes))
    (candidate : beaconcrypt_core.pqxdh.ServerRegistrationCandidate) (kernel : Kernel)
    (unused : copies.peers candidate.key_id = none) :
    PqxdhServerRegistrationPublication.publish (overrideServer copies state) candidate kernel () =
      overrideServer copies (PqxdhServerRegistrationPublication.publish state candidate kernel ()) := by
  simp only [PqxdhServerRegistrationPublication.publish, overrideServer]
  congr 2
  funext kid
  by_cases same : kid = candidate.key_id
  · subst same
    simp only [Function.update_self, Option.map_some, unused, mergePeer]
  · simp only [Function.update_of_ne same]

/-- The post-initialization tail commutes with the override when the candidate key ID has no local copy. -/
theorem afterInitialization_override (copies : Local)
    (candidate : beaconcrypt_core.pqxdh.ServerRegistrationCandidate) (authenticated : Pqxdh.Bytes) (kernel : Kernel)
    (state : PqxdhServerRegistrationPublication.State Unit Unit (List Pqxdh.Bytes))
    (unused : copies.peers candidate.key_id = none) :
    PqxdhServerRegistrationPublication.afterInitialization candidate authenticated kernel () (overrideServer copies state) =
      (fun value => (value.1, overrideServer copies value.2)) <$>
        PqxdhServerRegistrationPublication.afterInitialization candidate authenticated kernel () state := by
  unfold PqxdhServerRegistrationPublication.afterInitialization
  simp only [map_bind]
  apply bind_congr
  rintro ⟨advanced, encrypted⟩
  apply bind_congr
  intro _
  rcases encrypted with _ | encrypted
  · simp only [map_pure]
  · simp only [map_bind]
    apply bind_congr
    intro serialized
    rcases serialized with _ | serialized
    · simp only [map_pure]
    · simp only [map_pure, publish_override copies state candidate advanced unused]

/-- Mapping a Rust result of the Server builder. -/
def mapBuilt (copies : Local) :
    RustM (Option PqxdhServerRegistrationPublication.Response ×
      PqxdhServerRegistrationPublication.State Unit Unit (List Pqxdh.Bytes)) →
    RustM (Option PqxdhServerRegistrationPublication.Response ×
      PqxdhServerRegistrationPublication.State Unit Unit (List Pqxdh.Bytes)) :=
  fun result => (fun value => (value.1, overrideServer copies value.2)) <$> result

/-- The candidate tail commutes with the override when the candidate key ID has no local copy. -/
theorem candidateTail_override (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (copies : Local)
    (candidate : beaconcrypt_core.pqxdh.ServerRegistrationCandidate) (root : PqxdhSecretInputKdf.RootOutput)
    (data : Option Pqxdh.Bytes) (state : PqxdhServerRegistrationPublication.State Unit Unit (List Pqxdh.Bytes))
    (unused : copies.peers candidate.key_id = none) :
    PqxdhServerRegistrationPublication.candidateTail source candidate root data () (overrideServer copies state) =
      mapBuilt copies <$> PqxdhServerRegistrationPublication.candidateTail source candidate root data () state := by
  unfold PqxdhServerRegistrationPublication.candidateTail
  simp only [map_bind]
  apply bind_congr
  intro valid
  split
  · simp only [map_pure]
    rfl
  · simp only [map_bind]
    apply bind_congr
    intro reserved
    split
    · simp only [map_pure]
      rfl
    · unfold PqxdhServerRegistrationPublication.continueRust
      split
      · split
        · simp only [map_pure]
          rfl
        · split
          · simp only [map_bind]
            apply bind_congr
            intro allocated
            split
            · simp only [map_pure]
              rfl
            · split
              · simp only [afterInitialization_override copies candidate _ _ state unused, Functor.map_map]
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

/-- The Server builder commutes with the override whenever every copied peer is installed: occupancy is read only through `isSome`, and a new peer is installed only at an unoccupied key ID, which then has no local copy. -/
theorem build_override (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (copies : Local)
    (pending : beaconcrypt_core.pqxdh.PendingServerRegistration) (root : PqxdhSecretInputKdf.RootOutput)
    (data : Option Pqxdh.Bytes) (state : PqxdhServerRegistrationPublication.State Unit Unit (List Pqxdh.Bytes))
    (installed : ∀ kid current, copies.peers kid = some current → state.server.peers kid ≠ none) :
    PqxdhServerRegistrationPublication.build source pending root data () (overrideServer copies state) =
      mapBuilt copies <$> PqxdhServerRegistrationPublication.build source pending root data () state := by
  unfold PqxdhServerRegistrationPublication.build PqxdhServerRegistrationPublication.continueRust
  have candidateStep := fun candidate unused => candidateTail_override source copies candidate root data state unused
  simp only [overrideServer, Option.isSome_map] at candidateStep ⊢
  cases next : beaconcrypt_core.pqxdh.server_next_key_id state.control with
  | ok value =>
      rcases value with value | _
      · dsimp only
        cases prepared : beaconcrypt_core.pqxdh.server_prepare_commit state.control pending
            ⟨state.server.identity, state.identityKeyId⟩
            (if (state.server.peers value).isSome then beaconcrypt_core.pqxdh.KeyIdAvailability.Occupied else .Available) with
        | ok result =>
            rcases result with candidate | _
            · dsimp only
              obtain ⟨available, key⟩ := prepare_key _ _ _ _ candidate prepared
              rw [next] at key
              have same : candidate.key_id = value := by
                cases key
                rfl
              have free : state.server.peers value = none := by
                by_contra occupied
                rw [Option.isSome_iff_ne_none.mpr occupied] at available
                simp at available
              have unused : copies.peers candidate.key_id = none := by
                rw [same]
                cases copied : copies.peers value with
                | none => rfl
                | some current => exact absurd free (installed value current copied)
              exact candidateStep candidate unused
            · simp only [map_pure]
              rfl
        | fail error => simp only [map_pure]; rfl
        | div => simp only [map_pure]; rfl
      · simp only [map_pure]
        rfl
  | fail error => simp only [map_pure]; rfl
  | div => simp only [map_pure]; rfl

/-- Every copied peer is installed in the Server peer map. -/
def Installed (copies : Local) (game : GameState KemSK) : Prop :=
  ∀ kid current, copies.peers kid = some current → game.server.server.peers kid ≠ none

/-- Settling a mapped builder result on the overridden Server is the override of the settled Server. -/
theorem settle_override (copies : Local) (server : PqxdhServerRegistrationPublication.State Unit Unit (List Pqxdh.Bytes))
    (result : RustM (Option PqxdhServerRegistrationPublication.Response ×
      PqxdhServerRegistrationPublication.State Unit Unit (List Pqxdh.Bytes))) :
    settle (overrideServer copies server) (mapBuilt copies result) =
      ((settle server result).1, overrideServer copies (settle server result).2) := by
  rcases result with value | error | _ <;> rfl

/-- `build_registration_response` commutes with the override when every copied peer is installed. -/
theorem build_commutes (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (copies : Local) (session : Nat) (payload : Option Pqxdh.Bytes) (game : GameState KemSK)
    (installed : Installed copies game) :
    (buildOracle setup codec checks session payload).run (overrideGame copies game) =
      Prod.map id (overrideGame copies) <$> (buildOracle setup codec checks session payload).run game := by
  simp only [buildOracle, StateT.run_bind, StateT.run_get, pure_bind]
  cases found : game.pending session with
  | none =>
      have same : (overrideGame copies game).pending session = none := found
      simp only [same, StateT.run_pure, map_pure]
      rfl
  | some token =>
      have same : (overrideGame copies game).pending session = some token := found
      simp only [same, liftCoins, StateT.run_bind, StateT.run_lift, bind_assoc, pure_bind, StateT.run_set,
        StateT.run_pure, map_bind, map_pure]
      have built := build_override setup.source copies token.pending token.root payload game.server installed
      change (familyCoins ((simulateQ (tailImpl setup codec checks)
          (PqxdhServerRegistrationPublication.build setup.source token.pending token.root payload ()
            (overrideServer copies game.server))).run ([], game.ctx)) >>= _) = _
      rw [built, simulateQ_map, StateT.run_map]
      have settled : ∀ result, settle (overrideGame copies game).server (mapBuilt copies result) =
          ((settle game.server result).1, overrideServer copies (settle game.server result).2) :=
        fun result => settle_override copies game.server result
      simp only [familyCoins, simulateQ_map, bind_map_left, settled]
      rfl

/-- The shared native state with the Server override. -/
def overrideShared (copies : Local) (shared : NativeState KemSK) : NativeState KemSK :=
  (shared.1, overrideGame copies shared.2)

/-- Family evaluation transports a commuting game computation to the shared native state. -/
theorem evaluate_commutes {Result : Type} (setup : Setup baseSpec KemSK) (seed : IdentitySeed) (scalar : ScalarBytes)
    (copies : Local) (work : Game KemSK Result) (shared : NativeState KemSK)
    (commutes : work.run (overrideGame copies shared.2) = Prod.map id (overrideGame copies) <$> work.run shared.2) :
    evaluate setup seed scalar work (overrideShared copies shared) =
      (fun result => (result.1, overrideShared copies result.2)) <$> evaluate setup seed scalar work shared := by
  simp only [evaluate, overrideShared]
  rw [commutes, simulateQ_map, StateT.run_map, Functor.map_map, Functor.map_map]
  rfl

/-- The merged registration state is the source14 state with the Server override and merged owners. -/
theorem merge_native (copies : Local) (native : PqxdhRegistrationSchedule.State KemSK) :
    (merge copies native).native = { native with
      shared := overrideShared copies native.shared
      owners := native.owners.mapIdx fun index owner => mergeOwner (copies.owners index) owner } := rfl

/-- A shared native step that commutes with the override commutes with merging, and leaves the owners alone. -/
theorem onShared_merge {Result : Type} (copies : Local) (work : NativeGame KemSK Result)
    (native : PqxdhRegistrationSchedule.State KemSK)
    (commutes : work (overrideShared copies native.shared) =
      (fun result => (result.1, overrideShared copies result.2)) <$> work native.shared) :
    (PqxdhRegistrationSchedule.onShared work).run (merge copies native).native =
      (fun result => (result.1, (merge copies result.2).native)) <$> (PqxdhRegistrationSchedule.onShared work).run native := by
  rw [PqxdhRegistrationSchedule.onShared_run, PqxdhRegistrationSchedule.onShared_run, merge_native]
  change (fun result => (result.1, _)) <$> work (overrideShared copies native.shared) = _
  rw [commutes, Functor.map_map, Functor.map_map]
  rfl

/-- The source14 accept, HMAC, BLAKE2b and build commands commute with merging; build needs every copied peer to be installed. -/
theorem shared_merge (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (serverSeed : IdentitySeed) (copies : Local) (native : PqxdhRegistrationSchedule.State KemSK)
    (request : PqxdhRegistrationSchedule.Request)
    (shared : match request with
      | .accept _ | .hmac _ _ | .hash _ | .build _ _ => True
      | _ => False)
    (installed : Installed copies native.shared.2) :
    (PqxdhRegistrationSchedule.handler setup codec checks serverSeed (.inr request)).run (merge copies native).native =
      (fun result => (result.1, (merge copies result.2).native)) <$>
        (PqxdhRegistrationSchedule.handler setup codec checks serverSeed (.inr request)).run native := by
  rcases request with _ | _ | raw | ⟨session, payload⟩ | _ | ⟨key, message⟩ | bytes | _
  all_goals simp only at shared
  · apply onShared_merge
    rw [← accept_native]
    exact evaluate_commutes setup serverSeed _ copies _ native.shared (accept_commutes setup codec checks copies _ raw _)
  · apply onShared_merge
    rw [← build_native setup codec checks serverSeed PqxdhRegistrationSchedule.observationScalar]
    exact evaluate_commutes setup serverSeed _ copies _ native.shared
      (build_commutes setup codec checks copies session payload _ installed)
  · apply onShared_merge
    rw [← hmac_native]
    exact evaluate_commutes setup serverSeed _ copies _ native.shared (hmac_commutes copies key message _)
  · apply onShared_merge
    rw [← hash_native setup serverSeed PqxdhRegistrationSchedule.observationScalar]
    exact evaluate_commutes setup serverSeed _ copies _ native.shared (hash_commutes copies bytes _)

/-- Owner creation appends a Fresh owner, which merging leaves unchanged; it commutes with merging. -/
theorem create_merge (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (serverSeed : IdentitySeed) (copies : Local) (native : PqxdhRegistrationSchedule.State KemSK)
    (pin : PqxdhBeaconPhase2Preparation.Word32) (keyId : Std.U64) :
    (PqxdhRegistrationSchedule.handler setup codec checks serverSeed (.inr (.create pin keyId))).run
        (merge copies native).native =
      (fun result => (result.1, (merge copies result.2).native)) <$>
        (PqxdhRegistrationSchedule.handler setup codec checks serverSeed (.inr (.create pin keyId))).run native := by
  simp only [PqxdhRegistrationSchedule.handler, PqxdhRegistrationSchedule.create, StateT.run_bind, StateT.run_lift,
    bind_assoc, pure_bind, StateT.run_get, StateT.run_set, StateT.run_pure, map_bind, map_pure]
  apply bind_congr
  intro identity
  apply bind_congr
  intro prekey
  apply bind_congr
  intro keys
  simp only [merge_native, List.length_mapIdx, List.mapIdx_concat]
  cases copies.owners native.owners.length <;> rfl

/-- Every locally copied owner is established in the source14 registry. -/
def Copied (copies : Local) (native : PqxdhRegistrationSchedule.State KemSK) : Prop :=
  ∀ index current, copies.owners index = some current →
    ∃ owner control associatedData kernel, native.owners[index]? = some owner ∧
      owner.beacon.phase = .established control associatedData kernel

/-- Replacing one owner commutes with merging up to the merged replacement. -/
theorem merge_set (copies : Local) (native : PqxdhRegistrationSchedule.State KemSK) (index : Nat)
    (owner : PqxdhRegistrationSchedule.Owner KemSK) :
    (merge copies { native with owners := native.owners.set index owner }).native =
      { (merge copies native).native with
        owners := (merge copies native).native.owners.set index (mergeOwner (copies.owners index) owner) } := by
  simp only [merge_native, List.mapIdx_set]

/-- Setting an owner to its current value changes nothing. -/
theorem set_found {α : Type} (list : List α) (index : Nat) (value : α) (found : list[index]? = some value) :
    list.set index value = list := by
  obtain ⟨bound, atIndex⟩ := List.getElem?_eq_some_iff.mp found
  rw [← atIndex, List.set_getElem_self bound]

/-- An owner with no local copy is unchanged by merging. -/
theorem mergeOwner_none (owner : PqxdhRegistrationSchedule.Owner KemSK) : mergeOwner none owner = owner := rfl

/-- An established owner stays established and terminal after merging. -/
theorem mergeOwner_terminal (kernel : Option Kernel) (owner : PqxdhRegistrationSchedule.Owner KemSK)
    (control : beaconcrypt_core.pqxdh.BeaconEstablished) (associatedData : Std.Array Std.U8 281#usize)
    (current : Kernel) (phase : owner.beacon.phase = .established control associatedData current) :
    PqxdhRegistrationSchedule.Terminal (mergeOwner kernel owner) := by
  cases kernel <;> simp [mergeOwner, phase, PqxdhRegistrationSchedule.Terminal]

/-- An owner that is not established has no local copy. -/
theorem uncopied (copies : Local) (native : PqxdhRegistrationSchedule.State KemSK) (copied : Copied copies native)
    (index : Nat) (owner : PqxdhRegistrationSchedule.Owner KemSK) (found : native.owners[index]? = some owner)
    (inactive : ¬ ∃ control associatedData kernel, owner.beacon.phase = .established control associatedData kernel) :
    copies.owners index = none := by
  cases copy : copies.owners index with
  | none => rfl
  | some current =>
      obtain ⟨other, control, associatedData, kernel, otherFound, phase⟩ := copied index current copy
      rw [found, Option.some.injEq] at otherFound
      subst otherFound
      exact absurd ⟨control, associatedData, kernel, phase⟩ inactive

/-- `get_registration_bundle` commutes with merging: an established owner returns without effect and every other owner has no local copy. -/
theorem bundle_merge (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (serverSeed : IdentitySeed) (copies : Local) (native : PqxdhRegistrationSchedule.State KemSK) (index : Nat)
    (copied : Copied copies native) :
    (PqxdhRegistrationSchedule.handler setup codec checks serverSeed (.inr (.bundle index))).run (merge copies native).native =
      (fun result => (result.1, (merge copies result.2).native)) <$>
        (PqxdhRegistrationSchedule.handler setup codec checks serverSeed (.inr (.bundle index))).run native := by
  simp only [PqxdhRegistrationSchedule.handler, PqxdhRegistrationSchedule.bundle, StateT.run_bind, StateT.run_get,
    pure_bind]
  rw [PqxdhDeploymentCompileRecords.merge_owner]
  cases found : native.owners[index]? with
  | none => simp only [Option.map_none, StateT.run_pure, map_pure]
  | some owner =>
      simp only [Option.map_some]
      by_cases active : ∃ control associatedData kernel, owner.beacon.phase = .established control associatedData kernel
      · obtain ⟨control, associatedData, kernel, phase⟩ := active
        rw [PqxdhRegistrationSchedule.terminal_bundle setup index _
            (mergeOwner_terminal _ owner control associatedData kernel phase),
          PqxdhRegistrationSchedule.terminal_bundle setup index owner (by simp [PqxdhRegistrationSchedule.Terminal, phase])]
        simp only [simulateQ_pure, StateT.run_bind, StateT.run_lift, pure_bind, StateT.run_modify, StateT.run_pure,
          map_pure]
        have mergedFound : (merge copies native).native.owners[index]? = some (mergeOwner (copies.owners index) owner) := by
          rw [PqxdhDeploymentCompileRecords.merge_owner, found, Option.map_some]
        rw [set_found _ index _ mergedFound, set_found _ index _ found]
      · have noCopy := uncopied copies native copied index owner found active
        simp only [noCopy, mergeOwner_none, StateT.run_bind, StateT.run_lift, bind_assoc, pure_bind, StateT.run_modify,
          StateT.run_pure, map_bind, map_pure]
        apply bind_congr
        intro result
        rw [merge_set, noCopy, mergeOwner_none]

/-- Every Beacon finish callback commutes with the override: preparation callbacks are stateless, and the root and tail callbacks touch only the Extract table and the BLAKE2b cache. -/
theorem callback_commutes (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (copies : Local)
    (query : (PqxdhBeaconPhase2Publication.NativeSpec IdentitySeed ScalarBytes
      (PqxdhKemIndCca.MlKem768PublicKey × KemSK) IdentitySeed Response).Domain)
    (shared : NativeState KemSK) :
    (PqxdhRegistrationSchedule.callbacks setup codec query).run (overrideShared copies shared) =
      (fun result => (result.1, overrideShared copies result.2)) <$>
        (PqxdhRegistrationSchedule.callbacks setup codec query).run shared := by
  rcases query with query | query
  · simp only [PqxdhRegistrationSchedule.callbacks, nativeCoins, StateT.run, Functor.map_map]
  · rcases query with query | query
    · simp only [PqxdhRegistrationSchedule.callbacks, sourceBeaconTail, PqxdhPhase2DhRootConsumer.withRoot, nativeCtx,
        StateT.run, Functor.map_map]
      rfl
    · cases query with
      | root input =>
          simp only [PqxdhRegistrationSchedule.callbacks, sourceBeaconTail, PqxdhPhase2DhRootConsumer.withRoot,
            sourceRoot, StateT.run, Functor.map_map]
          rfl
      | _ =>
          simp only [PqxdhRegistrationSchedule.callbacks, sourceBeaconTail, PqxdhPhase2DhRootConsumer.withRoot,
            nativeCtx, StateT.run, Functor.map_map]
          rfl

/-- An entire Beacon finish callback program commutes with the override. -/
theorem callbacks_commute {Result : Type} (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (copies : Local)
    (program : OracleComp (PqxdhBeaconPhase2Publication.NativeSpec IdentitySeed ScalarBytes
      (PqxdhKemIndCca.MlKem768PublicKey × KemSK) IdentitySeed Response) Result)
    (shared : NativeState KemSK) :
    (simulateQ (PqxdhRegistrationSchedule.callbacks setup codec) program).run (overrideShared copies shared) =
      (fun result => (result.1, overrideShared copies result.2)) <$>
        (simulateQ (PqxdhRegistrationSchedule.callbacks setup codec) program).run shared :=
  (OracleComp.map_run_simulateQ_eq_of_query_map_eq (PqxdhRegistrationSchedule.callbacks setup codec)
    (PqxdhRegistrationSchedule.callbacks setup codec) (overrideShared copies)
    (fun query state => (callback_commutes setup codec copies query state).symm) program shared).symm

/-- `finish_registration` commutes with merging: an established owner returns without effect and every other owner has no local copy, while the callbacks commute with the Server override. -/
theorem finish_merge (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (serverSeed : IdentitySeed) (copies : Local) (native : PqxdhRegistrationSchedule.State KemSK) (index : Nat)
    (raw : Pqxdh.Bytes) (copied : Copied copies native) :
    (PqxdhRegistrationSchedule.handler setup codec checks serverSeed (.inr (.finish index raw))).run
        (merge copies native).native =
      (fun result => (result.1, (merge copies result.2).native)) <$>
        (PqxdhRegistrationSchedule.handler setup codec checks serverSeed (.inr (.finish index raw))).run native := by
  cases found : native.owners[index]? with
  | none =>
      have mergedMissing : (merge copies native).native.owners[index]? = none := by
        rw [PqxdhDeploymentCompileRecords.merge_owner, found, Option.map_none]
      simp only [PqxdhRegistrationSchedule.handler]
      rw [PqxdhRegistrationSchedule.finish_missing setup codec index raw _ mergedMissing,
        PqxdhRegistrationSchedule.finish_missing setup codec index raw _ found, map_pure]
  | some owner =>
      have mergedFound : (merge copies native).native.owners[index]? = some (mergeOwner (copies.owners index) owner) := by
        rw [PqxdhDeploymentCompileRecords.merge_owner, found, Option.map_some]
      by_cases active : ∃ control associatedData kernel, owner.beacon.phase = .established control associatedData kernel
      · obtain ⟨control, associatedData, kernel, phase⟩ := active
        simp only [PqxdhRegistrationSchedule.handler]
        change PqxdhRegistrationSchedule.finish setup codec index raw (merge copies native).native =
          (fun result => (result.1, (merge copies result.2).native)) <$>
            PqxdhRegistrationSchedule.finish setup codec index raw native
        rw [PqxdhRegistrationSchedule.terminal_finish setup codec index raw _ _ mergedFound
            (mergeOwner_terminal _ owner control associatedData kernel phase),
          PqxdhRegistrationSchedule.terminal_finish setup codec index raw _ _ found
            (by simp [PqxdhRegistrationSchedule.Terminal, phase]), map_pure]
      · have noCopy := uncopied copies native copied index owner found active
        simp only [PqxdhRegistrationSchedule.handler]
        change PqxdhRegistrationSchedule.finish setup codec index raw (merge copies native).native =
          (fun result => (result.1, (merge copies result.2).native)) <$>
            PqxdhRegistrationSchedule.finish setup codec index raw native
        rw [PqxdhRegistrationSchedule.finish_source setup codec index raw _ _ mergedFound,
          PqxdhRegistrationSchedule.finish_source setup codec index raw _ _ found, noCopy, mergeOwner_none]
        rw [merge_native]
        change (fun result => _) <$>
            (simulateQ (PqxdhRegistrationSchedule.callbacks setup codec) _).run (overrideShared copies native.shared) = _
        rw [callbacks_commute, Functor.map_map, Functor.map_map]
        congr 1
        funext result
        rw [merge_native]
        simp only [List.mapIdx_set, noCopy, mergeOwner_none]

end BeaconcryptCore.Computational.PqxdhDeploymentCompileRegistration

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentCompileRegistration.pure_commutes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentCompileRegistration.pure_commutes

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentCompileRegistration.bind_commutes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentCompileRegistration.bind_commutes

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentCompileRegistration.lift_commutes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentCompileRegistration.lift_commutes

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentCompileRegistration.modify_commutes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentCompileRegistration.modify_commutes

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentCompileRegistration.session_commutes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentCompileRegistration.session_commutes

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentCompileRegistration.simulate_commutes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentCompileRegistration.simulate_commutes

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentCompileRegistration.accept_commutes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentCompileRegistration.accept_commutes

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentCompileRegistration.hmac_commutes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentCompileRegistration.hmac_commutes

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentCompileRegistration.hash_commutes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentCompileRegistration.hash_commutes

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentCompileRegistration.prepare_key' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentCompileRegistration.prepare_key

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentCompileRegistration.publish_override' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentCompileRegistration.publish_override

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentCompileRegistration.afterInitialization_override' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentCompileRegistration.afterInitialization_override

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentCompileRegistration.candidateTail_override' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentCompileRegistration.candidateTail_override

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentCompileRegistration.build_override' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentCompileRegistration.build_override

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentCompileRegistration.settle_override' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentCompileRegistration.settle_override

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentCompileRegistration.build_commutes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentCompileRegistration.build_commutes

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentCompileRegistration.evaluate_commutes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentCompileRegistration.evaluate_commutes

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentCompileRegistration.merge_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentCompileRegistration.merge_native

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentCompileRegistration.onShared_merge' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentCompileRegistration.onShared_merge

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentCompileRegistration.shared_merge' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentCompileRegistration.shared_merge

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentCompileRegistration.create_merge' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentCompileRegistration.create_merge

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentCompileRegistration.merge_set' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentCompileRegistration.merge_set

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentCompileRegistration.set_found' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentCompileRegistration.set_found

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentCompileRegistration.mergeOwner_none' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentCompileRegistration.mergeOwner_none

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentCompileRegistration.mergeOwner_terminal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentCompileRegistration.mergeOwner_terminal

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentCompileRegistration.uncopied' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentCompileRegistration.uncopied

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentCompileRegistration.bundle_merge' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentCompileRegistration.bundle_merge

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentCompileRegistration.callback_commutes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentCompileRegistration.callback_commutes

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentCompileRegistration.callbacks_commute' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentCompileRegistration.callbacks_commute

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentCompileRegistration.finish_merge' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentCompileRegistration.finish_merge
