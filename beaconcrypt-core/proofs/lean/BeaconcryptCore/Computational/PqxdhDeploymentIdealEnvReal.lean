-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentReal
import BeaconcryptCore.Computational.PqxdhDeploymentIdealSteps

/-!
# The real registration commands of the environment on any backend, and the pool create (CE-11b, unit U3)

CE-11a's per-command splits of the real registration (`PqxdhDeploymentEnvironmentReal`, section `Commands`) are stated for the real registration handler `PqxdhDeploymentBackend.realReg` at the unit backend with no slot (`n = 0`). CE-11b's ideal environment (`PqxdhDeploymentIdealEnv`, design-v2 section 6) runs the same real commands on the backend `PqxdhDeploymentIdealSteps.SplitBk` with two slots, so this module restates them for every backend `Bk` and slot count `n`, with the real registration handler on that backend (`PqxdhDeploymentIdealSteps.realRegAt`, which is `realReg` at the unit backend, `realRegAt_real`). The statements and proofs are CE-11a's with the backend and the slot count generalized: none of them reads the backend or the slot count.

- `realRegAt_quiet`, `realRegAt_accept`: `realRegAt` on a command other than the raw accept, and on the raw accept.
- Per command, the World run of the real environment step `PqxdhDeploymentEnvironment.realStep` with its counts forgotten (`createStep_effects`, `hmacStep_effects`, `acceptStep_effects`, `bundleStep_effects`, `buildStep_effects`, `finishStep_effects`), the reassembled law, which is `realRegAt`'s exactly (`create_law`, `hmac_law`, `accept_law`, `bundle_law`, `build_law`, `finish_law`), and the preservation of admissibility (`create_keeps` to `finish_keeps`), with their tools (`create_merge`, `bundle_outcome`, `frameGame_server`, `build_merge`, `withCache_server`, `build_outcome`, `finish_native_run`, `finish_merge_set`, `finish_outcome`). `realAt_splits_create` to `realAt_splits_hmac` pair the two per command, and `real_splitsAt` is `PqxdhDeploymentEnvironmentJoin.Splits` for `realStep` and `realRegAt` on every backend and slot count, relative to the trivial admissibility predicate.
- The pool create (design-v2 sections 3.1 and 6.1): the ideal registration's create command `PqxdhDeploymentIdealSteps.createReg` reads the new owner's KEM key pair from the challenger's pool (`createPool`, one run in `createPool_run`, the command in `createReg_run`). `createPoolStep` is its capability form (CE-11a's `createStep` with the pool create in place of the native create), `createPoolStep_effects` its World run, and `createPool_law`, `createPool_keeps` and `createPool_splits` its split: the reassembled law is `createReg`'s exactly and admissibility is kept.

The generic tools these proofs use (`PqxdhDeploymentEnvironmentReal`, sections `Bridge` to `FinishShape`, and the generic command lemmas such as `onNative_run`, `nativeBuild_run` and `builtNative`) are reused, not restated. These are equalities of programs and in law; no security claim is made here.
-/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete PqxdhRefinement

set_option autoImplicit false

namespace BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvReal
open PqxdhServerAuthExperiment (Setup Codec Checks GameState)
open PqxdhServerAuthNative (NativeState NativeGame)
open PqxdhRecordLiftInterface (Slot Capability CapabilitySpec EnvEffects EnvQuery EnvSpec Environment EffectKind
  effectKind BeaconShell InactivePhase KernelRef)
open PqxdhDeploymentEnvironment (EnvState EnvStep strip Stripped stripPeer stripOwner ctxEffects coins)
open PqxdhDeploymentEnvironmentJoin (merge fill fillOwner fillServer Good Splits uncount stripPhase)
open PqxdhDeploymentBackend (XState RegImpl handlerWith gameWith)
open PqxdhDeploymentEnvironmentReal (withCache ctxAdmin coins_noAdmin effects_coins effects_then effects_map
  effects_issue_then effects_append effects_advance installPeer effects_installServer effects_installBeacon countFree_pure
  countFree_bind effects_then_free countFree_ownerEffect countFree_ownerChange countFree_serverEffect NFrame nframe_simulateQ
  frameGame serverGame nativeHmac_nframe acceptLogged_nframe callbacks_nframe fill_some Matched fill_strip snapshotAt_fill
  fillOwner_inactive good_matched good_intro merge_uncount law_uncount keeps_uncount good_uncount matched_append
  fill_append_owner good_server uncount_good fill_set matched_set fill_inactive map_congr_support shared_run shared_fill
  shared_good Bundled bundle_shape Built build_shape ownerEffect_same ownerChange_set ownerEffect_publish
  established_terminal worldCopies override_world installed_world override_publish run_support finishFwd_noAdmin
  finishFwd_game Finished finish_shape ownerEffect_abort ownerEffect_establish fillOwner_self
  onNative_run onShared_run create_run hmac_frame accept_frame bundle_run_missing bundle_run_found builtNative builtGame
  nativeBuild_run builtNative_quiet snapFinish finishedState)
open PqxdhDeploymentIdealSteps (realRegAt createPool createReg)
open LazyOracleDiscard (LawEq)

variable {KemSK : Type}

/-! ### The real commands on any backend and slot count -/

section Commands
variable {Bk : Type} {n : Nat} {ι : Type} {baseSpec : OracleSpec ι} {Reader Response : Type}
  (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
  (route : RawCtxServerRouting.SenderDecoder) (created : PqxdhLiveServerConstruction.Created Unit)

/-- The real registration handler on a command other than the raw accept: the native handler of the deployment experiment on the deployment state, the log kept, and the LQ snapshot of a finish. -/
theorem realRegAt_quiet (query : EnvQuery) (notAccept : ∀ raw, query.val ≠ .accept raw) (state : XState KemSK Bk n) :
    (realRegAt setup codec route checks created query).run state =
      (fun result => (result.1,
          { state with base := result.2, snap := PqxdhDeploymentLater.snapshotAt state.snap state.base.native.owners (PqxdhDeploymentLater.finishOwner (.inr query.val)) })) <$>
        (PqxdhDeploymentNative.handler setup codec checks route created.seed (.inr query.val)).run state.base := by
  change (fun result => (result.1,
      { state with base := result.2.1, log := result.2.2, snap := PqxdhDeploymentLater.snapshotAt state.snap state.base.native.owners (PqxdhDeploymentLater.finishOwner (.inr query.val)) })) <$>
    (PqxdhDeploymentLaterServerGame.handler setup codec checks route created.seed (.inr query.val)).run
      (state.base, state.log) = _
  rw [PqxdhDeploymentLaterServerGame.handler_quiet setup codec checks route created.seed _
    (fun raw same => notAccept raw (Sum.inr.inj same)), Functor.map_map]

/-- The real environment's `create`, run by the World with its counts forgotten: the native owner construction on the environment's registration state, and one new fresh owner in the World. -/
theorem createStep_effects (pin : Pqxdh.Bytes) (keyId : Std.U64) (e : EnvState KemSK Bk) (w : PqxdhRecordLiftWorld.State n) :
    Prod.map id uncount <$> (simulateQ PqxdhRecordLiftWorld.effects
        ((PqxdhDeploymentEnvironment.realStep (n := n) setup codec checks ⟨.create pin keyId, trivial⟩).run e)).run w =
      match PqxdhDeploymentInterface.parsePin pin with
      | none => pure ((none, e), uncount w)
      | some word => (fun result => ((some result.1, { e with native := strip result.2 }),
          uncount { w with owners := w.owners ++ [.inactive .fresh] })) <$>
            (PqxdhRegistrationSchedule.create setup word keyId).run e.native := by
  change Prod.map id uncount <$> (simulateQ PqxdhRecordLiftWorld.effects
    ((PqxdhDeploymentEnvironment.createStep (n := n) setup pin keyId).run e)).run w = _
  unfold PqxdhDeploymentEnvironment.createStep
  rcases parsed : PqxdhDeploymentInterface.parsePin pin with _ | word
  · simp only [StateT.run_pure, simulateQ_pure, map_pure]
    rfl
  · simp only [StateT.run_bind, StateT.run_lift, StateT.run_pure, bind_assoc, pure_bind]
    rw [show (PqxdhDeploymentEnvironment.onEnv (n := n) (Bk := Bk) (PqxdhRegistrationSchedule.create setup word keyId)).run e =
      (fun result => (result.1, { e with native := strip result.2 })) <$>
        coins (n := n) ((PqxdhRegistrationSchedule.create setup word keyId).run e.native) from rfl, bind_map_left]
    rw [effects_then ctxAdmin _ (coins_noAdmin _) _ (fun result x => pure ((some result.1, { e with native := strip result.2 }),
      uncount { x with owners := x.owners ++ [.inactive .fresh] })) (fun result x => ?_) w]
    · rw [PqxdhDeploymentEnvironment.ctxEffects_coins, bind_map_left]
      simp only [bind_pure_comp]
      rfl
    · rw [effects_issue_then, effects_append, map_pure]
      rfl

/-- The reassembled state after a `create`: one fresh owner appended on both sides. -/
theorem create_merge (e : EnvState KemSK Bk) (w : PqxdhRecordLiftWorld.State n) (good : Good created e w)
    (owner : PqxdhRegistrationSchedule.Owner KemSK)
    (fresh : PqxdhRecordLiftBeacon.projectPhase owner.beacon = .inactive .fresh) :
    merge { e with native := strip { e.native with owners := e.native.owners ++ [owner] } }
        (uncount { w with owners := w.owners ++ [.inactive .fresh] }) =
      { merge e w with base := { (merge e w).base with native :=
        { fill w e.native with owners := (fill w e.native).owners ++ [owner] } } } := by
  obtain ⟨world, found, _, _, _⟩ := good.server
  have filled : fill (uncount { w with owners := w.owners ++ [.inactive .fresh] })
      (strip { e.native with owners := e.native.owners ++ [owner] }) =
        { fill w e.native with owners := (fill w e.native).owners ++ [owner] } := by
    rw [fill_strip (uncount { w with owners := w.owners ++ [.inactive .fresh] }) world found
        { e.native with owners := e.native.owners ++ [owner] }
        (matched_append w _ (good_matched created e w good) good.ownersLength owner fresh),
      fill_some (uncount { w with owners := w.owners ++ [.inactive .fresh] }) world found, fill_some w world found]
    simp only [uncount]
    rw [fill_append_owner w _ good.ownersLength owner]
  simp only [merge, filled]
  rfl

/-- The `create` command of the real environment splits the real registration handler. -/
theorem create_law (pin : Pqxdh.Bytes) (keyId : Std.U64) (e : EnvState KemSK Bk) (w : PqxdhRecordLiftWorld.State n)
    (good : Good created e w) :
    (fun result => (result.1.1, merge result.1.2 result.2)) <$> (simulateQ PqxdhRecordLiftWorld.effects
        ((PqxdhDeploymentEnvironment.realStep (n := n) setup codec checks ⟨.create pin keyId, trivial⟩).run e)).run w =
      (realRegAt setup codec route checks created ⟨.create pin keyId, trivial⟩).run (merge e w) := by
  rw [law_uncount, createStep_effects, realRegAt_quiet setup codec checks route created _ (fun raw same => by cases same)]
  rcases parsed : PqxdhDeploymentInterface.parsePin pin with _ | word
  · simp only [PqxdhDeploymentNative.handler, parsed, StateT.run_pure, map_pure]
    rfl
  · simp only [PqxdhDeploymentNative.handler, parsed, StateT.run_map, PqxdhRegistrationSchedule.handler, onNative_run,
      create_run, map_bind, map_pure]
    refine bind_congr fun identity => bind_congr fun prekey => bind_congr fun keys => ?_
    rw [create_merge created e w good _ rfl]
    simp only [merge, fill, List.length_mapIdx, PqxdhDeploymentLater.finishOwner, PqxdhDeploymentLater.snapshotAt]

/-- The `create` command of the real environment keeps admissibility. -/
theorem create_keeps (pin : Pqxdh.Bytes) (keyId : Std.U64) (e : EnvState KemSK Bk) (w : PqxdhRecordLiftWorld.State n)
    (good : Good created e w) :
    ∀ result ∈ support ((simulateQ PqxdhRecordLiftWorld.effects
        ((PqxdhDeploymentEnvironment.realStep (n := n) setup codec checks ⟨.create pin keyId, trivial⟩).run e)).run w),
      Good created result.1.2 result.2 := by
  apply keeps_uncount _ (Good created) (good_uncount created)
  rw [createStep_effects]
  rcases parsed : PqxdhDeploymentInterface.parsePin pin with _ | word
  · intro result supported
    simp only [support_pure, Set.mem_singleton_iff] at supported
    subst supported
    exact uncount_good created e w good
  · intro result supported
    rw [support_map] at supported
    obtain ⟨inner, member, rfl⟩ := supported
    rw [create_run] at member
    simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at member
    obtain ⟨identity, _, prekey, _, keys, _, rfl⟩ := member
    obtain ⟨world, found, sender, identity', peers⟩ := good_server created e w good
    refine uncount_good created _ _ (good_intro created _ _ _ world rfl good.createdEq found sender identity' peers ?_
      (matched_append w _ (good_matched created e w good) good.ownersLength _ rfl))
    simp only [List.length_append, List.length_singleton, good.ownersLength]

/-- The real environment's public HMAC, run by the World with its counts forgotten: the native HMAC on the environment's shared state, the World unchanged. -/
theorem hmacStep_effects (key : PqxdhSecretInputKdf.HmacBlock) (message : Pqxdh.Bytes) (e : EnvState KemSK Bk)
    (w : PqxdhRecordLiftWorld.State n) :
    Prod.map id uncount <$> (simulateQ PqxdhRecordLiftWorld.effects
        ((PqxdhDeploymentEnvironment.realStep (n := n) setup codec checks ⟨.hmac key message, trivial⟩).run e)).run w =
      (fun result => ((result.1, { e with native := strip { e.native with shared := result.2 } }), uncount w)) <$>
        (PqxdhServerAuthNative.nativeHmac setup e.created.seed PqxdhRegistrationSchedule.observationScalar key message).run
          e.native.shared := by
  change Prod.map id uncount <$> (simulateQ PqxdhRecordLiftWorld.effects
    ((fun result => (result.1, { e with native := strip result.2 })) <$> coins (n := n)
      ((PqxdhRegistrationSchedule.onShared (PqxdhServerAuthNative.nativeHmac setup e.created.seed
        PqxdhRegistrationSchedule.observationScalar key message)).run e.native))).run w = _
  rw [effects_map, effects_coins, onShared_run, Functor.map_map, Functor.map_map]
  rfl

/-- The public HMAC of the real environment splits the real registration handler. -/
theorem hmac_law (key : PqxdhSecretInputKdf.HmacBlock) (message : Pqxdh.Bytes) (e : EnvState KemSK Bk)
    (w : PqxdhRecordLiftWorld.State n) (good : Good created e w) :
    (fun result => (result.1.1, merge result.1.2 result.2)) <$> (simulateQ PqxdhRecordLiftWorld.effects
        ((PqxdhDeploymentEnvironment.realStep (n := n) setup codec checks ⟨.hmac key message, trivial⟩).run e)).run w =
      (realRegAt setup codec route checks created ⟨.hmac key message, trivial⟩).run (merge e w) := by
  obtain ⟨world, found, _, _, _⟩ := good.server
  rw [law_uncount, hmacStep_effects, realRegAt_quiet setup codec checks route created _ (fun raw same => by cases same)]
  simp only [PqxdhDeploymentNative.handler, onNative_run, PqxdhRegistrationSchedule.handler, onShared_run, Functor.map_map]
  rw [show (merge e w).base.native = fill w e.native from rfl, good.createdEq,
    shared_run _ (hmac_frame setup created.seed key message) e w world found, Functor.map_map]
  rw [← good.createdEq]
  apply map_congr_support
  intro result supported
  simp only [merge_uncount]
  simp only [merge, shared_fill _ (hmac_frame setup e.created.seed key message) created e w good world found result supported]
  rfl

/-- The public HMAC of the real environment keeps admissibility. -/
theorem hmac_keeps (key : PqxdhSecretInputKdf.HmacBlock) (message : Pqxdh.Bytes) (e : EnvState KemSK Bk)
    (w : PqxdhRecordLiftWorld.State n) (good : Good created e w) :
    ∀ result ∈ support ((simulateQ PqxdhRecordLiftWorld.effects
        ((PqxdhDeploymentEnvironment.realStep (n := n) setup codec checks ⟨.hmac key message, trivial⟩).run e)).run w),
      Good created result.1.2 result.2 := by
  apply keeps_uncount _ (Good created) (good_uncount created)
  rw [hmacStep_effects]
  intro result supported
  rw [support_map] at supported
  obtain ⟨inner, member, rfl⟩ := supported
  exact uncount_good created _ _ (shared_good _ (hmac_frame setup e.created.seed key message) created e _ w good inner member
    rfl rfl)

/-- The real registration handler on the raw accept: the native logged accept on the deployment state's shared state, its entry appended to the log. -/
theorem realRegAt_accept (raw : Pqxdh.Bytes) (state : XState KemSK Bk n) :
    (realRegAt setup codec route checks created ⟨.accept raw, trivial⟩).run state =
      (fun result => (result.1.1,
          { state with base := { state.base with native := { state.base.native with shared := result.2 } }, log := state.log ++ [result.1.2] })) <$>
        (PqxdhDeploymentLaterServerNative.acceptLogged setup codec checks created.seed raw).run state.base.native.shared := by
  change (fun result => (result.1,
      { state with base := result.2.1, log := result.2.2, snap := PqxdhDeploymentLater.snapshotAt state.snap state.base.native.owners none })) <$>
    ((fun result => (result.1, ({ state.base with native := result.2.1 }, result.2.2))) <$>
      ((fun result => (result.1.1, (result.2, state.log ++ [result.1.2]))) <$>
        (PqxdhRegistrationSchedule.onShared (PqxdhDeploymentLaterServerNative.acceptLogged setup codec checks created.seed
          raw)).run state.base.native)) = _
  rw [onShared_run]
  simp only [Functor.map_map]
  rfl

/-- The real environment's raw accept, run by the World with its counts forgotten: the native logged accept on the environment's shared state, its entry appended to the environment's log, the World unchanged. -/
theorem acceptStep_effects (raw : Pqxdh.Bytes) (e : EnvState KemSK Bk) (w : PqxdhRecordLiftWorld.State n) :
    Prod.map id uncount <$> (simulateQ PqxdhRecordLiftWorld.effects
        ((PqxdhDeploymentEnvironment.realStep (n := n) setup codec checks ⟨.accept raw, trivial⟩).run e)).run w =
      (fun result => ((result.1.1,
          { e with native := strip { e.native with shared := result.2 }, log := e.log ++ [result.1.2] }), uncount w)) <$>
        (PqxdhDeploymentLaterServerNative.acceptLogged setup codec checks e.created.seed raw).run e.native.shared := by
  change Prod.map id uncount <$> (simulateQ PqxdhRecordLiftWorld.effects
    ((fun result => (result.1.1, { e with native := strip result.2, log := e.log ++ [result.1.2] })) <$> coins (n := n)
      ((PqxdhRegistrationSchedule.onShared (PqxdhDeploymentLaterServerNative.acceptLogged setup codec checks e.created.seed
        raw)).run e.native))).run w = _
  rw [effects_map, effects_coins, onShared_run, Functor.map_map, Functor.map_map]
  rfl

/-- The raw accept of the real environment splits the real registration handler. -/
theorem accept_law (raw : Pqxdh.Bytes) (e : EnvState KemSK Bk) (w : PqxdhRecordLiftWorld.State n) (good : Good created e w) :
    (fun result => (result.1.1, merge result.1.2 result.2)) <$> (simulateQ PqxdhRecordLiftWorld.effects
        ((PqxdhDeploymentEnvironment.realStep (n := n) setup codec checks ⟨.accept raw, trivial⟩).run e)).run w =
      (realRegAt setup codec route checks created ⟨.accept raw, trivial⟩).run (merge e w) := by
  obtain ⟨world, found, _, _, _⟩ := good.server
  rw [law_uncount, acceptStep_effects, realRegAt_accept]
  rw [show (merge e w).base.native = fill w e.native from rfl, good.createdEq,
    shared_run _ (accept_frame setup codec checks created.seed raw) e w world found, Functor.map_map, Functor.map_map]
  rw [← good.createdEq]
  apply map_congr_support
  intro result supported
  simp only [merge_uncount]
  simp only [merge, shared_fill _ (accept_frame setup codec checks e.created.seed raw) created e w good world found result
    supported]

/-- The raw accept of the real environment keeps admissibility. -/
theorem accept_keeps (raw : Pqxdh.Bytes) (e : EnvState KemSK Bk) (w : PqxdhRecordLiftWorld.State n) (good : Good created e w) :
    ∀ result ∈ support ((simulateQ PqxdhRecordLiftWorld.effects
        ((PqxdhDeploymentEnvironment.realStep (n := n) setup codec checks ⟨.accept raw, trivial⟩).run e)).run w),
      Good created result.1.2 result.2 := by
  apply keeps_uncount _ (Good created) (good_uncount created)
  rw [acceptStep_effects]
  intro result supported
  rw [support_map] at supported
  obtain ⟨inner, member, rfl⟩ := supported
  exact uncount_good created _ _ (shared_good _ (accept_frame setup codec checks e.created.seed raw) created e _ w good inner
    member rfl rfl)

/-- The real environment's bundle, run by the World with its counts forgotten: the native bundle on the environment's registration state, then the owner's phase change published. -/
theorem bundleStep_effects (index : Nat) (e : EnvState KemSK Bk) (w : PqxdhRecordLiftWorld.State n) :
    Prod.map id uncount <$> (simulateQ PqxdhRecordLiftWorld.effects
        ((PqxdhDeploymentEnvironment.realStep (n := n) setup codec checks ⟨.bundle index, trivial⟩).run e)).run w =
      (PqxdhRegistrationSchedule.bundle setup codec index).run e.native >>= fun result =>
        Prod.map id uncount <$> (simulateQ PqxdhRecordLiftWorld.effects
          (PqxdhDeploymentEnvironment.ownerChange index e.native.owners result.2.owners >>= fun _ =>
            pure (result.1, { e with native := strip result.2 }))).run (uncount w) := by
  change Prod.map id uncount <$> (simulateQ PqxdhRecordLiftWorld.effects
    (coins ((PqxdhRegistrationSchedule.bundle setup codec index).run e.native) >>= fun result =>
      PqxdhDeploymentEnvironment.ownerChange index e.native.owners result.2.owners >>= fun _ =>
        pure (result.1, { e with native := strip result.2 }))).run w = _
  rw [effects_then_free ctxAdmin _ (coins_noAdmin _) _ (fun result => countFree_bind (countFree_ownerChange _ _ _)
    fun _ => countFree_pure _) w, PqxdhDeploymentEnvironment.ctxEffects_coins, bind_map_left]
  rfl

/-- One outcome of a bundle at a present owner that is not established: the World's phase change, the reassembled state and admissibility. -/
theorem bundle_outcome (index : Nat) (e : EnvState KemSK Bk) (w : PqxdhRecordLiftWorld.State n) (good : Good created e w)
    (owner : PqxdhRegistrationSchedule.Owner KemSK) (owned : e.native.owners[index]? = some owner)
    (inactive : ¬ RawCtxBeaconLifecycle.Established owner.beacon.phase) (reply : Option Pqxdh.Bytes)
    (after : PqxdhRegistrationSchedule.Owner KemSK) (shape : Bundled owner after) :
    ∃ w', Prod.map id uncount <$> (simulateQ PqxdhRecordLiftWorld.effects
        (PqxdhDeploymentEnvironment.ownerChange index e.native.owners (e.native.owners.set index after) >>= fun _ =>
          pure (reply, { e with native := strip { e.native with owners := e.native.owners.set index after } }))).run
          (uncount w) =
        pure ((reply, { e with native := strip { e.native with owners := e.native.owners.set index after } }), uncount w') ∧
      merge { e with native := strip { e.native with owners := e.native.owners.set index after } } w' =
        { merge e w with base := { (merge e w).base with native :=
          { fill w e.native with owners := (fill w e.native).owners.set index after } } } ∧
      Good created { e with native := strip { e.native with owners := e.native.owners.set index after } } w' := by
  obtain ⟨world, found, sender, identity, peers⟩ := good_server created e w good
  have matched := good_matched created e w good
  have below : index < e.native.owners.length := (List.getElem?_eq_some_iff.mp owned).1
  have belowWorld : index < w.owners.length := by rw [good.ownersLength]; exact below
  obtain ⟨tag, worldPhase, projected, _⟩ := fill_inactive w _ matched index owner owned inactive
  rw [ownerChange_set index _ owner after owned]
  rcases shape with same | ⟨⟨control, prekey, oneTime, kem, published⟩, fresh⟩
  · rw [same]
    refine ⟨w, ?_, ?_, ?_⟩
    · rw [ownerEffect_same, pure_bind, simulateQ_pure, StateT.run_pure, map_pure]
      rfl
    · have unchanged : e.native.owners.set index owner = e.native.owners := by
        obtain ⟨_, atIndex⟩ := List.getElem?_eq_some_iff.mp owned
        rw [← atIndex, List.set_getElem_self]
      have filledOwner : (fill w e.native).owners[index]? = some owner := by
        simp only [fill, List.getElem?_mapIdx, owned, Option.map_some, worldPhase, fillOwner_inactive]
      have unchanged' : (fill w e.native).owners.set index owner = (fill w e.native).owners := by
        obtain ⟨_, atIndex⟩ := List.getElem?_eq_some_iff.mp filledOwner
        rw [← atIndex, List.set_getElem_self]
      simp only [unchanged, unchanged', show (⟨e.native.shared, e.native.owners⟩ : PqxdhRegistrationSchedule.State KemSK) =
        e.native from rfl, show strip e.native = e.native from good.stripped]
      rfl
    · simp only [show e.native.owners.set index owner = e.native.owners by
        obtain ⟨_, atIndex⟩ := List.getElem?_eq_some_iff.mp owned
        rw [← atIndex, List.set_getElem_self]]
      exact good_intro created _ e.native w world rfl good.createdEq found sender identity peers good.ownersLength matched
  · subst published
    have legal : PqxdhRecordLiftWorld.LegalAdvance tag .initSent := by
      have tags : PqxdhDeploymentEnvironment.inactiveTag owner.beacon.phase = some tag := by
        cases phase : owner.beacon.phase <;>
          simp only [PqxdhRecordLiftBeacon.projectPhase, phase, PqxdhRecordLiftBeacon.Phase.inactive.injEq,
            reduceCtorEq] at projected inactive ⊢ <;> first | exact absurd trivial inactive | (subst projected; rfl)
      rw [tags] at fresh
      rcases fresh with fresh | fresh <;> (simp only [Option.some.injEq] at fresh; subst fresh; trivial)
    let w' : PqxdhRecordLiftWorld.State n := { w with owners := w.owners.set index (.inactive .initSent) }
    have matched' : Matched w' (e.native.owners.set index
        { owner with beacon := { owner.beacon with phase := .initSent control prekey oneTime kem } }) :=
      matched_set w _ matched index _ _ belowWorld rfl
    refine ⟨w', ?_, ?_, ?_⟩
    · rw [ownerEffect_publish index owner control prekey oneTime kem fresh, effects_issue_then,
        effects_advance index tag .initSent (uncount w) worldPhase legal, map_pure]
      rfl
    · have filled := fill_strip w' world found
        { e.native with owners := e.native.owners.set index { owner with beacon := { owner.beacon with phase := .initSent control prekey oneTime kem } } } matched'
      simp only [merge, filled]
      rw [fill_some w' world found, fill_some w world found]
      simp only [w']
      rw [fill_set _ _ index _ _ below good.ownersLength, fillOwner_inactive]
    · exact good_intro created _ _ w' world rfl good.createdEq found sender identity peers
        (by simp only [w', List.length_set, good.ownersLength]) matched'

/-- The bundle of the real environment splits the real registration handler. -/
theorem bundle_law (index : Nat) (e : EnvState KemSK Bk) (w : PqxdhRecordLiftWorld.State n) (good : Good created e w) :
    (fun result => (result.1.1, merge result.1.2 result.2)) <$> (simulateQ PqxdhRecordLiftWorld.effects
        ((PqxdhDeploymentEnvironment.realStep (n := n) setup codec checks ⟨.bundle index, trivial⟩).run e)).run w =
      (realRegAt setup codec route checks created ⟨.bundle index, trivial⟩).run (merge e w) := by
  rw [law_uncount, bundleStep_effects, realRegAt_quiet setup codec checks route created _ (fun raw same => by cases same)]
  simp only [PqxdhDeploymentNative.handler, onNative_run, PqxdhRegistrationSchedule.handler, Functor.map_map]
  rw [show (merge e w).base.native = fill w e.native from rfl]
  cases owned : e.native.owners[index]? with
  | none =>
      have filled : (fill w e.native).owners[index]? = none := by
        simp only [fill, List.getElem?_mapIdx, owned, Option.map_none]
      rw [bundle_run_missing setup codec index _ owned, bundle_run_missing setup codec index _ filled, pure_bind, map_pure]
      have quiet : PqxdhDeploymentEnvironment.ownerChange (n := n) index e.native.owners e.native.owners = pure () := by
        unfold PqxdhDeploymentEnvironment.ownerChange
        rw [owned]
      rw [quiet, pure_bind, simulateQ_pure, StateT.run_pure, map_pure, map_pure]
      simp only [show strip e.native = e.native from good.stripped]
      rfl
  | some owner =>
      by_cases established : RawCtxBeaconLifecycle.Established owner.beacon.phase
      · obtain ⟨terminal, terminal'⟩ := established_terminal (w.owners[index]?) owner established
        have filled : (fill w e.native).owners[index]? = some (fillOwner (w.owners[index]?) owner) := by
          simp only [fill, List.getElem?_mapIdx, owned, Option.map_some]
        rw [show (PqxdhRegistrationSchedule.bundle setup codec index).run e.native = pure (none, e.native) from
            PqxdhRegistrationSchedule.terminal_bundle_call setup codec index _ owner owned terminal,
          show (PqxdhRegistrationSchedule.bundle setup codec index).run (fill w e.native) = pure (none, fill w e.native) from
            PqxdhRegistrationSchedule.terminal_bundle_call setup codec index _ _ filled terminal', pure_bind, map_pure]
        have quiet : PqxdhDeploymentEnvironment.ownerChange (n := n) index e.native.owners e.native.owners = pure () := by
          unfold PqxdhDeploymentEnvironment.ownerChange
          rw [owned]
          exact ownerEffect_same index owner
        rw [quiet, pure_bind, simulateQ_pure, StateT.run_pure, map_pure, map_pure]
        simp only [show strip e.native = e.native from good.stripped]
        rfl
      · obtain ⟨tag, worldPhase, _, filledOwner⟩ := fill_inactive w _ (good_matched created e w good) index owner owned
          established
        have filled : (fill w e.native).owners[index]? = some owner := by
          simp only [fill, List.getElem?_mapIdx, owned, Option.map_some, filledOwner]
        rw [bundle_run_found setup codec index _ owner owned, bundle_run_found setup codec index _ owner filled,
          bind_map_left, map_bind, Functor.map_map, map_eq_bind_pure_comp]
        apply OracleComp.bind_congr_of_forall_mem_support
        intro result member
        obtain ⟨w', run, merged, _⟩ := bundle_outcome created index e w good owner owned established result.1 result.2
          (bundle_shape _ owner result (PqxdhDeploymentEnvironment.support_simulateQ_subset _ _ member))
        dsimp only
        rw [run, map_pure]
        dsimp only
        rw [merge_uncount, merged]
        rfl

/-- The bundle of the real environment keeps admissibility. -/
theorem bundle_keeps (index : Nat) (e : EnvState KemSK Bk) (w : PqxdhRecordLiftWorld.State n) (good : Good created e w) :
    ∀ result ∈ support ((simulateQ PqxdhRecordLiftWorld.effects
        ((PqxdhDeploymentEnvironment.realStep (n := n) setup codec checks ⟨.bundle index, trivial⟩).run e)).run w),
      Good created result.1.2 result.2 := by
  apply keeps_uncount _ (Good created) (good_uncount created)
  rw [bundleStep_effects]
  intro result supported
  rw [mem_support_bind_iff] at supported
  obtain ⟨inner, member, final⟩ := supported
  cases owned : e.native.owners[index]? with
  | none =>
      rw [bundle_run_missing setup codec index _ owned, support_pure, Set.mem_singleton_iff] at member
      subst member
      have quiet : PqxdhDeploymentEnvironment.ownerChange (n := n) index e.native.owners e.native.owners = pure () := by
        unfold PqxdhDeploymentEnvironment.ownerChange
        rw [owned]
      simp only [quiet, pure_bind, simulateQ_pure, StateT.run_pure, map_pure, support_pure, Set.mem_singleton_iff] at final
      subst final
      simp only [show strip e.native = e.native from good.stripped]
      exact uncount_good created e w good
  | some owner =>
      by_cases established : RawCtxBeaconLifecycle.Established owner.beacon.phase
      · obtain ⟨terminal, _⟩ := established_terminal (w.owners[index]?) owner established
        rw [show (PqxdhRegistrationSchedule.bundle setup codec index).run e.native = pure (none, e.native) from
          PqxdhRegistrationSchedule.terminal_bundle_call setup codec index _ owner owned terminal, support_pure,
          Set.mem_singleton_iff] at member
        subst member
        have quiet : PqxdhDeploymentEnvironment.ownerChange (n := n) index e.native.owners e.native.owners = pure () := by
          unfold PqxdhDeploymentEnvironment.ownerChange
          rw [owned]
          exact ownerEffect_same index owner
        simp only [quiet, pure_bind, simulateQ_pure, StateT.run_pure, map_pure, support_pure, Set.mem_singleton_iff] at final
        subst final
        simp only [show strip e.native = e.native from good.stripped]
        exact uncount_good created e w good
      · rw [bundle_run_found setup codec index _ owner owned, support_map] at member
        obtain ⟨bundled, bundledMember, rfl⟩ := member
        obtain ⟨w', run, _, kept⟩ := bundle_outcome created index e w good owner owned established bundled.1 bundled.2
          (bundle_shape _ owner bundled (PqxdhDeploymentEnvironment.support_simulateQ_subset _ _ bundledMember))
        dsimp only at final
        rw [run, support_pure, Set.mem_singleton_iff] at final
        subst final
        exact uncount_good created _ _ kept

/-- The real environment's Server build, run by the World with its counts forgotten: the forwarded build read through `ctxEffects` on the World's cache, then the publication of the settled build in the World. -/
theorem buildStep_effects (session : Nat) (payload : Option Pqxdh.Bytes) (e : EnvState KemSK Bk)
    (w : PqxdhRecordLiftWorld.State n) :
    Prod.map id uncount <$> (simulateQ PqxdhRecordLiftWorld.effects
        ((PqxdhDeploymentEnvironment.realStep (n := n) setup codec checks ⟨.build session payload, trivial⟩).run e)).run w =
      match e.native.shared.2.pending session with
      | none => pure ((none, e), uncount w)
      | some token => (simulateQ (ctxEffects ctxAdmin) ((simulateQ (PqxdhDeploymentEnvironment.tailFwd (n := n) setup codec
            checks) (PqxdhServerRegistrationPublication.build setup.source token.pending token.root payload ()
              e.native.shared.2.server)).run [])).run w.primitive.2 >>= fun result =>
          Prod.map id uncount <$> (simulateQ PqxdhRecordLiftWorld.effects
            (PqxdhDeploymentEnvironment.serverEffect (PqxdhServerAuthExperiment.settle e.native.shared.2.server result.1.1) >>=
              fun _ => pure ((PqxdhServerAuthExperiment.settle e.native.shared.2.server result.1.1).1,
                { e with native := strip (builtNative e.native session result.1) }))).run (withCache w result.2) := by
  change Prod.map id uncount <$> (simulateQ PqxdhRecordLiftWorld.effects
    (PqxdhDeploymentEnvironment.buildStep (n := n) setup codec checks session payload e)).run w = _
  unfold PqxdhDeploymentEnvironment.buildStep
  dsimp only
  rcases pending : e.native.shared.2.pending session with _ | token
  · simp only [simulateQ_pure, StateT.run_pure, map_pure]
    rfl
  · dsimp only
    rw [effects_then_free ctxAdmin _ ?noAdmin _ (fun result => countFree_bind (countFree_serverEffect _)
      fun _ => countFree_pure _) w]
    · rfl
    · simpa only [reduceCtorEq, ite_false] using PqxdhDeploymentEnvironment.build_fwd_bound (n := n) setup codec checks
        token.pending token.root payload e.native.shared.2.server [] .administrative

/-- The game state of the reassembled state as CE-3's override of the environment's Server record. -/
theorem frameGame_server (e : EnvState KemSK Bk) (w : PqxdhRecordLiftWorld.State n) (good : Good created e w)
    (world : PqxdhRecordLiftWorld.Server) (found : w.server = some world) :
    (frameGame w.primitive.2 world.records.server e.native.shared.2.server.identityKeyId e.native.shared.2).server =
      PqxdhDeploymentCompileRegistration.overrideServer (worldCopies world) e.native.shared.2.server := by
  obtain ⟨world', found', _, identity, peers⟩ := good.server
  rw [found] at found'
  cases found'
  rw [override_world world _ identity peers]
  rfl

/-- The reassembled state after a Server build whose settled Server record the World mirrors. -/
theorem build_merge (session : Nat) (e : EnvState KemSK Bk) (w : PqxdhRecordLiftWorld.State n) (good : Good created e w)
    (world : PqxdhRecordLiftWorld.Server) (found : w.server = some world)
    (rust : RustM (Option PqxdhServerRegistrationPublication.Response ×
      PqxdhServerRegistrationPublication.State Unit Unit (List Pqxdh.Bytes)))
    (log : List RawCtxSourceSend.SealContext) (cache : CtxRomAuth.CtxRO.QueryCache) (world' : PqxdhRecordLiftWorld.Server)
    (raw' : world'.records.rawAttempts = world.records.rawAttempts)
    (override : PqxdhDeploymentCompileRegistration.overrideServer (worldCopies world)
      (PqxdhServerAuthExperiment.settle e.native.shared.2.server rust).2 =
        { (PqxdhServerAuthExperiment.settle e.native.shared.2.server rust).2 with server := world'.records.server })
    (keyId' : (PqxdhServerAuthExperiment.settle e.native.shared.2.server rust).2.identityKeyId =
      e.native.shared.2.server.identityKeyId) :
    merge { e with native := strip (builtNative e.native session (rust, log)) }
        (uncount { withCache w cache with server := some world' }) =
      { merge e w with base := { (merge e w).base with native := { fill w e.native with shared := (e.native.shared.1,
        builtGame (frameGame w.primitive.2 world.records.server e.native.shared.2.server.identityKeyId e.native.shared.2)
          session (PqxdhDeploymentCompileRegistration.mapBuilt (worldCopies world) rust, (log, cache))) } } } := by
  have serverEq := frameGame_server created e w good world found
  have settled := PqxdhDeploymentCompileRegistration.settle_override (worldCopies world) e.native.shared.2.server rust
  rw [← serverEq] at settled
  have filled := fill_strip (uncount { withCache w cache with server := some world' }) world' rfl
    (builtNative e.native session (rust, log)) (good_matched created e w good)
  simp only [merge, filled]
  rw [fill_some _ world' rfl, fill_some w world found]
  simp only [builtGame]
  rw [settled, override]
  simp only [frameGame, builtNative, keyId', uncount, withCache, Option.map_some, Option.getD_some, raw', found]

/-- Setting the World's Server to the one it holds changes nothing. -/
theorem withCache_server (w : PqxdhRecordLiftWorld.State n) (cache : CtxRomAuth.CtxRO.QueryCache)
    (world : PqxdhRecordLiftWorld.Server) (found : w.server = some world) :
    { withCache w cache with server := some world } = withCache w cache := by
  simp only [withCache, ← found]

/-- One outcome of a Server build: the World's installation, the World's Server record after it and admissibility. -/
theorem build_outcome (session : Nat) (e : EnvState KemSK Bk) (w : PqxdhRecordLiftWorld.State n) (good : Good created e w)
    (world : PqxdhRecordLiftWorld.Server) (found : w.server = some world)
    (rust : RustM (Option PqxdhServerRegistrationPublication.Response ×
      PqxdhServerRegistrationPublication.State Unit Unit (List Pqxdh.Bytes)))
    (built : Built e.native.shared.2.server () rust) (log : List RawCtxSourceSend.SealContext)
    (cache : CtxRomAuth.CtxRO.QueryCache) :
    ∃ world', Prod.map id uncount <$> (simulateQ PqxdhRecordLiftWorld.effects
        (PqxdhDeploymentEnvironment.serverEffect (PqxdhServerAuthExperiment.settle e.native.shared.2.server rust) >>= fun _ =>
          pure ((PqxdhServerAuthExperiment.settle e.native.shared.2.server rust).1,
            { e with native := strip (builtNative e.native session (rust, log)) }))).run (withCache w cache) =
        pure (((PqxdhServerAuthExperiment.settle e.native.shared.2.server rust).1,
          { e with native := strip (builtNative e.native session (rust, log)) }),
            uncount { withCache w cache with server := some world' }) ∧
      world'.records.rawAttempts = world.records.rawAttempts ∧
      PqxdhDeploymentCompileRegistration.overrideServer (worldCopies world)
          (PqxdhServerAuthExperiment.settle e.native.shared.2.server rust).2 =
        { (PqxdhServerAuthExperiment.settle e.native.shared.2.server rust).2 with server := world'.records.server } ∧
      (PqxdhServerAuthExperiment.settle e.native.shared.2.server rust).2.identityKeyId =
        e.native.shared.2.server.identityKeyId ∧
      Good created { e with native := strip (builtNative e.native session (rust, log)) }
        (uncount { withCache w cache with server := some world' }) := by
  obtain ⟨world₀, found₀, _, _, peersRaw⟩ := good.server
  rw [found] at found₀
  cases found₀
  obtain ⟨world₁, found₁, sender, identity, peers⟩ := good_server created e w good
  rw [found] at found₁
  cases found₁
  have matched := good_matched created e w good
  have quiet : (PqxdhServerAuthExperiment.settle e.native.shared.2.server rust).2 = e.native.shared.2.server →
      (PqxdhServerAuthExperiment.settle e.native.shared.2.server rust).1 = none →
      ∃ world', Prod.map id uncount <$> (simulateQ PqxdhRecordLiftWorld.effects
        (PqxdhDeploymentEnvironment.serverEffect (PqxdhServerAuthExperiment.settle e.native.shared.2.server rust) >>= fun _ =>
          pure ((PqxdhServerAuthExperiment.settle e.native.shared.2.server rust).1,
            { e with native := strip (builtNative e.native session (rust, log)) }))).run (withCache w cache) =
        pure (((PqxdhServerAuthExperiment.settle e.native.shared.2.server rust).1,
          { e with native := strip (builtNative e.native session (rust, log)) }),
            uncount { withCache w cache with server := some world' }) ∧
      world'.records.rawAttempts = world.records.rawAttempts ∧
      PqxdhDeploymentCompileRegistration.overrideServer (worldCopies world)
          (PqxdhServerAuthExperiment.settle e.native.shared.2.server rust).2 =
        { (PqxdhServerAuthExperiment.settle e.native.shared.2.server rust).2 with server := world'.records.server } ∧
      (PqxdhServerAuthExperiment.settle e.native.shared.2.server rust).2.identityKeyId =
        e.native.shared.2.server.identityKeyId ∧
      Good created { e with native := strip (builtNative e.native session (rust, log)) }
        (uncount { withCache w cache with server := some world' }) := by
    intro settledServer settledReply
    refine ⟨world, ?_, rfl, ?_, by rw [settledServer], ?_⟩
    · have effect : PqxdhDeploymentEnvironment.serverEffect (n := n)
          (PqxdhServerAuthExperiment.settle e.native.shared.2.server rust) = pure () := by
        unfold PqxdhDeploymentEnvironment.serverEffect
        rw [settledReply]
      rw [effect, pure_bind, simulateQ_pure, StateT.run_pure, map_pure, withCache_server w cache world found]
      rfl
    · rw [settledServer, override_world world _ identity peersRaw]
    · have native := builtNative_quiet e.native session rust log settledServer
      refine good_intro created _ (builtNative e.native session (rust, log)) _ world rfl good.createdEq rfl ?_ ?_ ?_ ?_ ?_
      · rw [native]; exact sender
      · rw [native]; exact identity
      · rw [native]; exact peers
      · rw [native]; exact good.ownersLength
      · rw [native]; exact matched
  rcases rust with ⟨(_ | response), after⟩ | error | _
  · exact quiet built rfl
  · obtain ⟨candidate, kernel, keyEq, vacant, published⟩ := built
    subst published
    have vacantWorld : world.records.server.peers candidate.key_id = none := by
      have mapped := peersRaw candidate.key_id
      rw [vacant] at mapped
      cases hworld : world.records.server.peers candidate.key_id with
      | none => rfl
      | some peer => rw [hworld] at mapped; cases mapped
    refine ⟨installPeer world candidate.key_id candidate.beacon_identity_public_key kernel, ?_, rfl, ?_, rfl, ?_⟩
    · have peerFound : (PqxdhServerRegistrationPublication.publish e.native.shared.2.server candidate kernel ()).server.peers
          response.keyId = some ⟨candidate.beacon_identity_public_key, kernel, ()⟩ := by
        rw [keyEq]
        exact (PqxdhServerRegistrationPublication.publish_fields _ candidate kernel ()).1
      simp only [PqxdhServerAuthExperiment.settle, PqxdhDeploymentEnvironment.serverEffect, peerFound]
      rw [effects_issue_then, keyEq, effects_installServer candidate.key_id _ kernel (withCache w cache) world
        (by simp only [withCache, found]) vacantWorld, map_pure]
    · exact override_publish world _ identity peersRaw candidate kernel vacantWorld
    · refine good_intro created _ _ _ (installPeer world candidate.key_id candidate.beacon_identity_public_key kernel)
        rfl good.createdEq rfl sender identity (fun keyId => ?_) good.ownersLength matched
      simp only [builtNative, PqxdhServerAuthExperiment.settle, installPeer, PqxdhServerRegistrationPublication.publish]
      by_cases same : keyId = candidate.key_id
      · subst same
        simp only [Function.update_self, Option.map_some]
      · simp only [Function.update_of_ne same]
        exact peers keyId
  · exact quiet rfl rfl
  · exact quiet rfl rfl

/-- The Server build of the real environment splits the real registration handler. -/
theorem build_law (session : Nat) (payload : Option Pqxdh.Bytes) (e : EnvState KemSK Bk) (w : PqxdhRecordLiftWorld.State n)
    (good : Good created e w) :
    (fun result => (result.1.1, merge result.1.2 result.2)) <$> (simulateQ PqxdhRecordLiftWorld.effects
        ((PqxdhDeploymentEnvironment.realStep (n := n) setup codec checks ⟨.build session payload, trivial⟩).run e)).run w =
      (realRegAt setup codec route checks created ⟨.build session payload, trivial⟩).run
        (merge e w) := by
  obtain ⟨world, found, _, _, peersRaw⟩ := good.server
  rw [law_uncount, buildStep_effects, realRegAt_quiet setup codec checks route created _ (fun raw same => by cases same)]
  simp only [PqxdhDeploymentNative.handler, onNative_run, PqxdhRegistrationSchedule.handler, onShared_run, Functor.map_map]
  rw [show (merge e w).base.native = fill w e.native from rfl,
    show (fill w e.native).shared = (e.native.shared.1, frameGame w.primitive.2 world.records.server
      e.native.shared.2.server.identityKeyId e.native.shared.2) by rw [fill_some w world found], nativeBuild_run]
  have pendingEq : (frameGame w.primitive.2 world.records.server e.native.shared.2.server.identityKeyId
      e.native.shared.2).pending session = e.native.shared.2.pending session := rfl
  rw [pendingEq]
  rcases pending : e.native.shared.2.pending session with _ | token
  · simp only [map_pure, merge_uncount]
    simp only [merge, fill_some w world found]
    rfl
  · dsimp only
    rw [frameGame_server created e w good world found, PqxdhDeploymentCompileRegistration.build_override setup.source
      (worldCopies world) token.pending token.root payload _ (installed_world world _ peersRaw), simulateQ_map,
      StateT.run_map, PqxdhDeploymentEnvironment.tail_factor ctxAdmin setup codec checks]
    rw [show (frameGame w.primitive.2 world.records.server e.native.shared.2.server.identityKeyId e.native.shared.2).ctx =
      w.primitive.2 from rfl, map_bind]
    conv_rhs => simp only [Functor.map_map]; rw [map_eq_bind_pure_comp]
    apply OracleComp.bind_congr_of_forall_mem_support
    rintro ⟨⟨rust, log⟩, cache⟩ member
    have built : Built e.native.shared.2.server () rust :=
      build_shape setup.source token.pending token.root payload () e.native.shared.2.server rust
        (run_support _ _ [] (rust, log) (run_support _ _ w.primitive.2 ((rust, log), cache) member))
    obtain ⟨world', run, raw', override, keyId', _⟩ := build_outcome created session e w good world found rust built log cache
    rw [run, map_pure]
    dsimp only [Function.comp]
    rw [build_merge created session e w good world found rust log cache world' raw' override keyId',
      PqxdhDeploymentCompileRegistration.settle_override]
    rfl

/-- The Server build of the real environment keeps admissibility. -/
theorem build_keeps (session : Nat) (payload : Option Pqxdh.Bytes) (e : EnvState KemSK Bk) (w : PqxdhRecordLiftWorld.State n)
    (good : Good created e w) :
    ∀ result ∈ support ((simulateQ PqxdhRecordLiftWorld.effects
        ((PqxdhDeploymentEnvironment.realStep (n := n) setup codec checks ⟨.build session payload, trivial⟩).run e)).run w),
      Good created result.1.2 result.2 := by
  obtain ⟨world, found, _, _, _⟩ := good.server
  apply keeps_uncount _ (Good created) (good_uncount created)
  rw [buildStep_effects]
  rcases pending : e.native.shared.2.pending session with _ | token
  · intro result supported
    simp only [support_pure, Set.mem_singleton_iff] at supported
    subst supported
    exact uncount_good created e w good
  · intro result supported
    dsimp only at supported
    rw [mem_support_bind_iff] at supported
    obtain ⟨⟨⟨rust, log⟩, cache⟩, member, final⟩ := supported
    have built : Built e.native.shared.2.server () rust :=
      build_shape setup.source token.pending token.root payload () e.native.shared.2.server rust
        (run_support _ _ [] (rust, log) (run_support _ _ w.primitive.2 ((rust, log), cache) member))
    obtain ⟨world', run, _, _, _, kept⟩ := build_outcome created session e w good world found rust built log cache
    dsimp only at final
    rw [run, support_pure, Set.mem_singleton_iff] at final
    subst final
    exact kept

/-- The real environment's finish, run by the World with its counts forgotten: the snapshot, the forwarded owner finish read through `ctxEffects` on the World's cache, then the publication of the owner's change in the World. -/
theorem finishStep_effects (index : Nat) (raw : Pqxdh.Bytes) (e : EnvState KemSK Bk) (w : PqxdhRecordLiftWorld.State n) :
    Prod.map id uncount <$> (simulateQ PqxdhRecordLiftWorld.effects
        ((PqxdhDeploymentEnvironment.realStep (n := n) setup codec checks ⟨.finish index raw, trivial⟩).run e)).run w =
      match e.native.owners[index]? with
      | none => pure ((none, snapFinish e index), uncount w)
      | some before => (simulateQ (ctxEffects ctxAdmin) ((simulateQ (PqxdhDeploymentEnvironment.callbacksFwd (n := n) setup
            codec) (PqxdhBeaconPhase2Publication.nativeOwner codec.frameRead raw before)).run e.native.shared)).run
              w.primitive.2 >>= fun result =>
          Prod.map id uncount <$> (simulateQ PqxdhRecordLiftWorld.effects
            (PqxdhDeploymentEnvironment.ownerEffect index before result.1.1.2 >>= fun _ =>
              pure (result.1.1.1, { snapFinish e index with
                native := strip ⟨result.1.2, e.native.owners.set index result.1.1.2⟩ }))).run (withCache w result.2) := by
  change Prod.map id uncount <$> (simulateQ PqxdhRecordLiftWorld.effects
    (PqxdhDeploymentEnvironment.finishStep (n := n) setup codec index raw (snapFinish e index))).run w = _
  unfold PqxdhDeploymentEnvironment.finishStep
  dsimp only
  rcases owned : e.native.owners[index]? with _ | before
  · simp only [snapFinish, owned, simulateQ_pure, StateT.run_pure, map_pure]
    rfl
  · simp only [snapFinish, owned]
    rw [effects_then_free ctxAdmin _ (finishFwd_noAdmin setup codec _ _) _ (fun result => countFree_bind
      (countFree_ownerEffect _ _ _) fun _ => countFree_pure _) w]

/-- The native finish on the reassembled state at an owner that is not established: the forwarded owner finish on the environment's shared state, read through `ctxEffects` on the World's cache, with the World's routing record filled in. -/
theorem finish_native_run (index : Nat) (raw : Pqxdh.Bytes) (e : EnvState KemSK Bk) (w : PqxdhRecordLiftWorld.State n)
    (good : Good created e w) (world : PqxdhRecordLiftWorld.Server) (found : w.server = some world)
    (before : PqxdhRegistrationSchedule.Owner KemSK) (owned : e.native.owners[index]? = some before)
    (inactive : ¬ RawCtxBeaconLifecycle.Established before.beacon.phase) :
    (PqxdhRegistrationSchedule.finish setup codec index raw).run (fill w e.native) =
      (fun result => (result.1.1.1, finishedState (fill w e.native).owners world.records.server
          e.native.shared.2.server.identityKeyId index result)) <$>
        (simulateQ (ctxEffects ctxAdmin) ((simulateQ (PqxdhDeploymentEnvironment.callbacksFwd (n := n) setup codec)
          (PqxdhBeaconPhase2Publication.nativeOwner codec.frameRead raw before)).run e.native.shared)).run
            w.primitive.2 := by
  obtain ⟨_, _, _, filledOwner⟩ := fill_inactive w _ (good_matched created e w good) index before owned inactive
  have filled : (fill w e.native).owners[index]? = some before := by
    simp only [fill, List.getElem?_mapIdx, owned, Option.map_some, filledOwner]
  rw [show (PqxdhRegistrationSchedule.finish setup codec index raw).run (fill w e.native) =
    PqxdhRegistrationSchedule.finish setup codec index raw (fill w e.native) from rfl,
    PqxdhRegistrationSchedule.finish_source setup codec index raw _ before filled]
  rw [show (fill w e.native).shared = (e.native.shared.1, serverGame world.records.server
      e.native.shared.2.server.identityKeyId { e.native.shared.2 with ctx := w.primitive.2 }) by
    rw [fill_some w world found]; rfl]
  rw [nframe_simulateQ _ _ (fun query => callbacks_nframe setup codec world.records.server
      e.native.shared.2.server.identityKeyId query) _ _ _,
    PqxdhDeploymentEnvironment.owner_factor (n := n) ctxAdmin setup codec raw before,
    show ((e.native.shared.1, { e.native.shared.2 with ctx := w.primitive.2 }) : NativeState KemSK) =
      PqxdhDeploymentBackend.gameCtxLens.set e.native.shared w.primitive.2 from rfl,
    PqxdhDeploymentEnvironment.frame_program _ _ (PqxdhDeploymentEnvironment.callbacksFwd_frame setup codec),
    simulateQ_map, StateT.run_map]
  simp only [Functor.map_map]
  rfl

/-- The reassembled state after a finish that changed one owner and its World phase consistently. -/
theorem finish_merge_set (index : Nat) (e : EnvState KemSK Bk) (w : PqxdhRecordLiftWorld.State n) (good : Good created e w)
    (world : PqxdhRecordLiftWorld.Server) (found : w.server = some world) (reply : Option Pqxdh.Bytes)
    (after : PqxdhRegistrationSchedule.Owner KemSK) (shared : NativeState KemSK) (game : shared.2 = e.native.shared.2)
    (cache : CtxRomAuth.CtxRO.QueryCache) (phase : PqxdhRecordLiftBeacon.Phase) (below : index < e.native.owners.length)
    (consistent : stripPhase phase = stripPhase (PqxdhRecordLiftBeacon.projectPhase after.beacon))
    (selfFill : fillOwner (some phase) after = after) :
    merge { snapFinish e index with native := strip ⟨shared, e.native.owners.set index after⟩ }
        (uncount { withCache w cache with owners := w.owners.set index phase }) =
      { merge e w with
        base := { (merge e w).base with native := finishedState (fill w e.native).owners world.records.server e.native.shared.2.server.identityKeyId index (((reply, after), shared), cache) }
        snap := (snapFinish e index).snap } ∧
      Good created { snapFinish e index with native := strip ⟨shared, e.native.owners.set index after⟩ }
        (uncount { withCache w cache with owners := w.owners.set index phase }) := by
  obtain ⟨_, found', sender, identity, peers⟩ := good_server created e w good
  rw [found] at found'
  cases found'
  have belowWorld : index < w.owners.length := by rw [good.ownersLength]; exact below
  have matched : Matched (uncount { withCache w cache with owners := w.owners.set index phase })
      (e.native.owners.set index after) :=
    matched_set (withCache w cache) _ (good_matched created e w good) index after phase belowWorld consistent
  constructor
  · have filled := fill_strip (uncount { withCache w cache with owners := w.owners.set index phase }) world found
      ⟨shared, e.native.owners.set index after⟩ matched
    simp only [merge, filled]
    rw [fill_some (uncount { withCache w cache with owners := w.owners.set index phase }) world found,
      fill_some w world found]
    simp only [uncount, withCache, finishedState, game]
    rw [fill_set _ _ index after phase below good.ownersLength, selfFill]
    rfl
  · refine good_intro created _ ⟨shared, e.native.owners.set index after⟩ _ world rfl good.createdEq found ?_ ?_ ?_
      (by simp only [uncount, withCache, List.length_set, good.ownersLength]) matched
    · simp only [game]; exact sender
    · simp only [game]; exact identity
    · simp only [game]; exact peers

/-- One outcome of a finish at an owner that is not established: the World's publication, the reassembled state and admissibility. -/
theorem finish_outcome (index : Nat) (e : EnvState KemSK Bk) (w : PqxdhRecordLiftWorld.State n) (good : Good created e w)
    (world : PqxdhRecordLiftWorld.Server) (found : w.server = some world) (before : PqxdhRegistrationSchedule.Owner KemSK)
    (owned : e.native.owners[index]? = some before) (inactive : ¬ RawCtxBeaconLifecycle.Established before.beacon.phase)
    (reply : Option Pqxdh.Bytes) (after : PqxdhRegistrationSchedule.Owner KemSK) (shared : NativeState KemSK)
    (cache : CtxRomAuth.CtxRO.QueryCache) (shape : Finished before after) (game : shared.2 = e.native.shared.2) :
    ∃ w', Prod.map id uncount <$> (simulateQ PqxdhRecordLiftWorld.effects
        (PqxdhDeploymentEnvironment.ownerEffect index before after >>= fun _ =>
          pure (reply, { snapFinish e index with native := strip ⟨shared, e.native.owners.set index after⟩ }))).run
          (withCache w cache) =
        pure ((reply, { snapFinish e index with native := strip ⟨shared, e.native.owners.set index after⟩ }), uncount w') ∧
      merge { snapFinish e index with native := strip ⟨shared, e.native.owners.set index after⟩ } w' =
        { merge e w with
          base := { (merge e w).base with native := finishedState (fill w e.native).owners world.records.server e.native.shared.2.server.identityKeyId index (((reply, after), shared), cache) }
          snap := (snapFinish e index).snap } ∧
      Good created { snapFinish e index with native := strip ⟨shared, e.native.owners.set index after⟩ } (uncount w') := by
  have below : index < e.native.owners.length := (List.getElem?_eq_some_iff.mp owned).1
  obtain ⟨tag, worldPhase, projected, _⟩ := fill_inactive w _ (good_matched created e w good) index before owned inactive
  rcases shape with same | ⟨initSent, aborted | ⟨control, associatedData, kernel, established⟩⟩
  · subst same
    have unchanged : { withCache w cache with owners := w.owners.set index (.inactive tag) } = withCache w cache := by
      obtain ⟨_, atIndex⟩ := List.getElem?_eq_some_iff.mp worldPhase
      simp only [withCache, ← atIndex, List.set_getElem_self]
    obtain ⟨merged, kept⟩ := finish_merge_set created index e w good world found reply after shared game cache
      (.inactive tag) below (by rw [projected]) (fillOwner_inactive tag after)
    rw [unchanged] at merged kept
    refine ⟨withCache w cache, ?_, by rw [merge_uncount] at merged; exact merged, kept⟩
    rw [ownerEffect_same, pure_bind, simulateQ_pure, StateT.run_pure, map_pure]
    rfl
  · have tagEq : tag = .initSent := by
      cases phase : before.beacon.phase <;>
        simp only [phase, PqxdhDeploymentEnvironment.inactiveTag, reduceCtorEq, Option.some.injEq,
          PqxdhRecordLiftBeacon.projectPhase, PqxdhRecordLiftBeacon.Phase.inactive.injEq] at initSent projected
      exact projected.symm
    subst tagEq
    have abortedPhase : PqxdhRecordLiftBeacon.projectPhase after.beacon = .inactive .aborted := by
      cases phase : after.beacon.phase <;>
        simp only [phase, PqxdhDeploymentEnvironment.inactiveTag, reduceCtorEq, Option.some.injEq] at aborted
      simp only [PqxdhRecordLiftBeacon.projectPhase, phase]
    obtain ⟨merged, kept⟩ := finish_merge_set created index e w good world found reply after shared game cache
      (.inactive .aborted) below (by rw [abortedPhase]) (fillOwner_inactive .aborted after)
    refine ⟨{ withCache w cache with owners := w.owners.set index (.inactive .aborted) }, ?_,
      by rw [merge_uncount] at merged; exact merged, kept⟩
    rw [ownerEffect_abort index before after initSent aborted, effects_issue_then,
      effects_advance index .initSent .aborted (withCache w cache) worldPhase trivial, map_pure]
    rfl
  · have tagEq : tag = .initSent := by
      cases phase : before.beacon.phase <;>
        simp only [phase, PqxdhDeploymentEnvironment.inactiveTag, reduceCtorEq, Option.some.injEq,
          PqxdhRecordLiftBeacon.projectPhase, PqxdhRecordLiftBeacon.Phase.inactive.injEq] at initSent projected
      exact projected.symm
    subst tagEq
    obtain ⟨merged, kept⟩ := finish_merge_set created index e w good world found reply after shared game cache
      (.established ⟨after.beacon.identityKeyId, control, associatedData⟩ kernel) below
      (by simp only [PqxdhRecordLiftBeacon.projectPhase, established])
      (fillOwner_self after control associatedData kernel established)
    refine ⟨{ withCache w cache with owners := w.owners.set index (.established ⟨after.beacon.identityKeyId, control, associatedData⟩ kernel) }, ?_,
      by rw [merge_uncount] at merged; exact merged, kept⟩
    rw [ownerEffect_establish index before after initSent control associatedData kernel established, effects_issue_then,
      effects_installBeacon index _ kernel (withCache w cache) worldPhase, map_pure]
    rfl

/-- The finish of the real environment splits the real registration handler. -/
theorem finish_law (index : Nat) (raw : Pqxdh.Bytes) (e : EnvState KemSK Bk) (w : PqxdhRecordLiftWorld.State n)
    (good : Good created e w) :
    (fun result => (result.1.1, merge result.1.2 result.2)) <$> (simulateQ PqxdhRecordLiftWorld.effects
        ((PqxdhDeploymentEnvironment.realStep (n := n) setup codec checks ⟨.finish index raw, trivial⟩).run e)).run w =
      (realRegAt setup codec route checks created ⟨.finish index raw, trivial⟩).run (merge e w) := by
  obtain ⟨world, found, _, _, _⟩ := good.server
  rw [law_uncount, finishStep_effects, realRegAt_quiet setup codec checks route created _ (fun raw same => by cases same)]
  simp only [PqxdhDeploymentNative.handler, onNative_run, PqxdhRegistrationSchedule.handler, Functor.map_map]
  rw [show (merge e w).base.native = fill w e.native from rfl, snapshotAt_fill]
  rcases owned : e.native.owners[index]? with _ | before
  · have filled : (fill w e.native).owners[index]? = none := by
      simp only [fill, List.getElem?_mapIdx, owned, Option.map_none]
    rw [PqxdhRegistrationSchedule.finish_missing setup codec index raw _ filled, map_pure, map_pure]
    rfl
  · dsimp only
    by_cases established : RawCtxBeaconLifecycle.Established before.beacon.phase
    · obtain ⟨terminal, terminal'⟩ := established_terminal (w.owners[index]?) before established
      have filled : (fill w e.native).owners[index]? = some (fillOwner (w.owners[index]?) before) := by
        simp only [fill, List.getElem?_mapIdx, owned, Option.map_some]
      rw [show (PqxdhRegistrationSchedule.finish setup codec index raw).run (fill w e.native) =
          pure (none, fill w e.native) from
        PqxdhRegistrationSchedule.terminal_finish setup codec index raw _ _ filled terminal',
        PqxdhRegistrationSchedule.terminal_native codec.frameRead raw before terminal]
      simp only [simulateQ_pure, StateT.run_pure, pure_bind, ownerEffect_same, map_pure]
      have unchanged : e.native.owners.set index before = e.native.owners := by
        obtain ⟨_, atIndex⟩ := List.getElem?_eq_some_iff.mp owned
        rw [← atIndex, List.set_getElem_self]
      simp only [unchanged, show (⟨e.native.shared, e.native.owners⟩ : PqxdhRegistrationSchedule.State KemSK) =
        e.native from rfl, show strip e.native = e.native from good.stripped]
      rfl
    · rw [finish_native_run setup codec created index raw e w good world found before owned established, map_bind]
      conv_rhs => simp only [Functor.map_map]; rw [map_eq_bind_pure_comp]
      apply OracleComp.bind_congr_of_forall_mem_support
      rintro ⟨⟨⟨reply, after⟩, shared⟩, cache⟩ member
      have forwarded := run_support _ _ w.primitive.2 _ member
      have shape : Finished before after :=
        finish_shape codec.frameRead raw before (reply, after) (run_support _ _ e.native.shared _ forwarded)
      have game : shared.2 = e.native.shared.2 := finishFwd_game setup codec _ e.native.shared _ forwarded
      obtain ⟨w', run, merged, _⟩ := finish_outcome created index e w good world found before owned established reply after
        shared cache shape game
      rw [run, map_pure]
      dsimp only [Function.comp]
      rw [merge_uncount, merged]
      rfl

/-- The finish of the real environment keeps admissibility. -/
theorem finish_keeps (index : Nat) (raw : Pqxdh.Bytes) (e : EnvState KemSK Bk) (w : PqxdhRecordLiftWorld.State n)
    (good : Good created e w) :
    ∀ result ∈ support ((simulateQ PqxdhRecordLiftWorld.effects
        ((PqxdhDeploymentEnvironment.realStep (n := n) setup codec checks ⟨.finish index raw, trivial⟩).run e)).run w),
      Good created result.1.2 result.2 := by
  obtain ⟨world, found, _, _, _⟩ := good.server
  apply keeps_uncount _ (Good created) (good_uncount created)
  rw [finishStep_effects]
  rcases owned : e.native.owners[index]? with _ | before
  · intro result supported
    simp only [support_pure, Set.mem_singleton_iff] at supported
    subst supported
    exact uncount_good created _ w ⟨good.1, good.2, good.3, good.4, good.5⟩
  · intro result supported
    dsimp only at supported
    rw [mem_support_bind_iff] at supported
    obtain ⟨⟨⟨⟨reply, after⟩, shared⟩, cache⟩, member, final⟩ := supported
    by_cases established : RawCtxBeaconLifecycle.Established before.beacon.phase
    · obtain ⟨terminal, _⟩ := established_terminal (w.owners[index]?) before established
      rw [PqxdhRegistrationSchedule.terminal_native codec.frameRead raw before terminal] at member
      simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at member
      obtain ⟨⟨⟨replyEq, afterEq⟩, sharedEq⟩, cacheEq⟩ := member
      subst replyEq sharedEq cacheEq
      subst after
      simp only [ownerEffect_same, pure_bind, simulateQ_pure, StateT.run_pure, map_pure, support_pure,
        Set.mem_singleton_iff] at final
      subst final
      have unchanged : e.native.owners.set index before = e.native.owners := by
        obtain ⟨_, atIndex⟩ := List.getElem?_eq_some_iff.mp owned
        rw [← atIndex, List.set_getElem_self]
      simp only [unchanged, show (⟨e.native.shared, e.native.owners⟩ : PqxdhRegistrationSchedule.State KemSK) =
        e.native from rfl, show strip e.native = e.native from good.stripped]
      exact uncount_good created _ _ ⟨good.1, good.2, good.3, good.4, good.5⟩
    · have forwarded := run_support _ _ w.primitive.2 _ member
      have shape : Finished before after :=
        finish_shape codec.frameRead raw before (reply, after) (run_support _ _ e.native.shared _ forwarded)
      have game : shared.2 = e.native.shared.2 := finishFwd_game setup codec _ e.native.shared _ forwarded
      obtain ⟨w', run, _, kept⟩ := finish_outcome created index e w good world found before owned established reply after
        shared cache shape game
      dsimp only at final
      rw [run, support_pure, Set.mem_singleton_iff] at final
      subst final
      exact kept

/-- The `create` command of the real environment splits the real registration handler: the reassembled law is the handler's (exactly) and admissibility is kept. -/
theorem realAt_splits_create (pin : Pqxdh.Bytes) (keyId : Std.U64) (e : EnvState KemSK Bk)
    (w : PqxdhRecordLiftWorld.State n) (good : Good created e w) :
    LawEq ((fun result => (result.1.1, merge result.1.2 result.2)) <$> (simulateQ PqxdhRecordLiftWorld.effects
        ((PqxdhDeploymentEnvironment.realStep (n := n) setup codec checks ⟨.create pin keyId, trivial⟩).run e)).run w)
      ((realRegAt setup codec route checks created ⟨.create pin keyId, trivial⟩).run (merge e w)) ∧
    ∀ result ∈ support ((simulateQ PqxdhRecordLiftWorld.effects
        ((PqxdhDeploymentEnvironment.realStep (n := n) setup codec checks ⟨.create pin keyId, trivial⟩).run e)).run w),
      Good created result.1.2 result.2 :=
  ⟨LawEq.of_eq (create_law setup codec checks route created pin keyId e w good),
    create_keeps setup codec checks created pin keyId e w good⟩

/-- The `bundle` command of the real environment splits the real registration handler: the reassembled law is the handler's (exactly) and admissibility is kept. -/
theorem realAt_splits_bundle (owner : Nat) (e : EnvState KemSK Bk)
    (w : PqxdhRecordLiftWorld.State n) (good : Good created e w) :
    LawEq ((fun result => (result.1.1, merge result.1.2 result.2)) <$> (simulateQ PqxdhRecordLiftWorld.effects
        ((PqxdhDeploymentEnvironment.realStep (n := n) setup codec checks ⟨.bundle owner, trivial⟩).run e)).run w)
      ((realRegAt setup codec route checks created ⟨.bundle owner, trivial⟩).run (merge e w)) ∧
    ∀ result ∈ support ((simulateQ PqxdhRecordLiftWorld.effects
        ((PqxdhDeploymentEnvironment.realStep (n := n) setup codec checks ⟨.bundle owner, trivial⟩).run e)).run w),
      Good created result.1.2 result.2 :=
  ⟨LawEq.of_eq (bundle_law setup codec checks route created owner e w good),
    bundle_keeps setup codec checks created owner e w good⟩

/-- The `accept` command of the real environment splits the real registration handler: the reassembled law is the handler's (exactly) and admissibility is kept. -/
theorem realAt_splits_accept (raw : Pqxdh.Bytes) (e : EnvState KemSK Bk)
    (w : PqxdhRecordLiftWorld.State n) (good : Good created e w) :
    LawEq ((fun result => (result.1.1, merge result.1.2 result.2)) <$> (simulateQ PqxdhRecordLiftWorld.effects
        ((PqxdhDeploymentEnvironment.realStep (n := n) setup codec checks ⟨.accept raw, trivial⟩).run e)).run w)
      ((realRegAt setup codec route checks created ⟨.accept raw, trivial⟩).run (merge e w)) ∧
    ∀ result ∈ support ((simulateQ PqxdhRecordLiftWorld.effects
        ((PqxdhDeploymentEnvironment.realStep (n := n) setup codec checks ⟨.accept raw, trivial⟩).run e)).run w),
      Good created result.1.2 result.2 :=
  ⟨LawEq.of_eq (accept_law setup codec checks route created raw e w good),
    accept_keeps setup codec checks created raw e w good⟩

/-- The `build` command of the real environment splits the real registration handler: the reassembled law is the handler's (exactly) and admissibility is kept. -/
theorem realAt_splits_build (session : Nat) (payload : Option Pqxdh.Bytes) (e : EnvState KemSK Bk)
    (w : PqxdhRecordLiftWorld.State n) (good : Good created e w) :
    LawEq ((fun result => (result.1.1, merge result.1.2 result.2)) <$> (simulateQ PqxdhRecordLiftWorld.effects
        ((PqxdhDeploymentEnvironment.realStep (n := n) setup codec checks ⟨.build session payload, trivial⟩).run e)).run w)
      ((realRegAt setup codec route checks created ⟨.build session payload, trivial⟩).run (merge e w)) ∧
    ∀ result ∈ support ((simulateQ PqxdhRecordLiftWorld.effects
        ((PqxdhDeploymentEnvironment.realStep (n := n) setup codec checks ⟨.build session payload, trivial⟩).run e)).run w),
      Good created result.1.2 result.2 :=
  ⟨LawEq.of_eq (build_law setup codec checks route created session payload e w good),
    build_keeps setup codec checks created session payload e w good⟩

/-- The `finish` command of the real environment splits the real registration handler: the reassembled law is the handler's (exactly) and admissibility is kept. -/
theorem realAt_splits_finish (owner : Nat) (raw : Pqxdh.Bytes) (e : EnvState KemSK Bk)
    (w : PqxdhRecordLiftWorld.State n) (good : Good created e w) :
    LawEq ((fun result => (result.1.1, merge result.1.2 result.2)) <$> (simulateQ PqxdhRecordLiftWorld.effects
        ((PqxdhDeploymentEnvironment.realStep (n := n) setup codec checks ⟨.finish owner raw, trivial⟩).run e)).run w)
      ((realRegAt setup codec route checks created ⟨.finish owner raw, trivial⟩).run (merge e w)) ∧
    ∀ result ∈ support ((simulateQ PqxdhRecordLiftWorld.effects
        ((PqxdhDeploymentEnvironment.realStep (n := n) setup codec checks ⟨.finish owner raw, trivial⟩).run e)).run w),
      Good created result.1.2 result.2 :=
  ⟨LawEq.of_eq (finish_law setup codec checks route created owner raw e w good),
    finish_keeps setup codec checks created owner raw e w good⟩

/-- The `hmac` command of the real environment splits the real registration handler: the reassembled law is the handler's (exactly) and admissibility is kept. -/
theorem realAt_splits_hmac (key : PqxdhSecretInputKdf.HmacBlock) (message : Pqxdh.Bytes) (e : EnvState KemSK Bk)
    (w : PqxdhRecordLiftWorld.State n) (good : Good created e w) :
    LawEq ((fun result => (result.1.1, merge result.1.2 result.2)) <$> (simulateQ PqxdhRecordLiftWorld.effects
        ((PqxdhDeploymentEnvironment.realStep (n := n) setup codec checks ⟨.hmac key message, trivial⟩).run e)).run w)
      ((realRegAt setup codec route checks created ⟨.hmac key message, trivial⟩).run (merge e w)) ∧
    ∀ result ∈ support ((simulateQ PqxdhRecordLiftWorld.effects
        ((PqxdhDeploymentEnvironment.realStep (n := n) setup codec checks ⟨.hmac key message, trivial⟩).run e)).run w),
      Good created result.1.2 result.2 :=
  ⟨LawEq.of_eq (hmac_law setup codec checks route created key message e w good),
    hmac_keeps setup codec checks created key message e w good⟩

end Commands

/-! ### The pool create -/

section Pool
variable {Bk : Type} {n : Nat} {ι : Type} {baseSpec : OracleSpec ι}
  (setup : Setup baseSpec KemSK) (created : PqxdhLiveServerConstruction.Created Unit)
open PqxdhLiveKemReservation (Pair)

/-- One run of the pool create (`PqxdhDeploymentIdealSteps.createPool`): the identity and prekey draws, the pool entry at the new owner's index (a fresh key pair beyond the pool), and the new fresh owner appended. -/
theorem createPool_run (pool : List (Pair KemSK)) (pin : PqxdhBeaconPhase2Preparation.Word32) (keyId : Std.U64)
    (state : PqxdhRegistrationSchedule.State KemSK) :
    (createPool setup pool pin keyId).run state = (do
      let identity ← PqxdhJointIdentity.sampleSeed
      let prekey ← PqxdhJointGapDh.sampleScalar
      let keys ← (match pool[state.owners.length]? with
        | some keys => pure keys
        | none => simulateQ (PqxdhInitializerSecrecy.kemAmbientImpl setup.baseImpl) setup.kem.keygen)
      let owner : PqxdhRegistrationSchedule.Owner KemSK := ⟨⟨identity, keyId, pin, .fresh ⟨⟨pin, keyId⟩⟩ prekey keys⟩, 0⟩
      pure (state.owners.length, { state with owners := state.owners ++ [owner] })) := by
  simp only [createPool, StateT.run_bind, StateT.run_lift, bind_assoc, pure_bind, StateT.run_get, StateT.run_set,
    StateT.run_pure]
  rfl

/-- One run of the ideal registration's create command (`PqxdhDeploymentIdealSteps.createReg`): the public pin parse, then the pool create on the registration state. -/
theorem createReg_run {Γ : Type} {m : Nat} (pool : List (Pair KemSK)) (pin : Pqxdh.Bytes) (keyId : Std.U64)
    (x : XState KemSK Γ m) :
    (createReg setup pool pin keyId).run x =
      match PqxdhDeploymentInterface.parsePin pin with
      | none => pure (none, x)
      | some word => (fun r => (some r.1, { x with base := { x.base with native := r.2 } })) <$>
          (createPool setup pool word keyId).run x.base.native := by
  unfold createReg
  rcases PqxdhDeploymentInterface.parsePin pin with _ | word
  · change (fun r => (r.1, PqxdhDeploymentBackend.baseLens.set x r.2)) <$>
      (pure none : StateT (PqxdhDeploymentNative.State KemSK) ProbComp (Option ℕ)).run
        (PqxdhDeploymentBackend.baseLens.get x) = _
    rw [StateT.run_pure, map_pure]
    rfl
  · change (fun r => (r.1, PqxdhDeploymentBackend.baseLens.set x r.2)) <$>
      (some <$> PqxdhDeploymentNative.onNative (createPool setup pool word keyId)).run
        (PqxdhDeploymentBackend.baseLens.get x) = _
    rw [StateT.run_map, onNative_run, Functor.map_map, Functor.map_map]
    rfl

/-- The pool create in capability form: the public pin parse, then the pool create with its coins as coin effects and the new inactive owner appended in the world (`PqxdhDeploymentEnvironment.createStep` with the pool create in place of the native create). -/
noncomputable def createPoolStep (pool : List (Pair KemSK)) (pin : Pqxdh.Bytes) (keyId : Std.U64) :
    StateT (EnvState KemSK Bk) (OracleComp (EnvEffects n)) (Option Nat) :=
  match PqxdhDeploymentInterface.parsePin pin with
  | none => pure none
  | some word => do
      let index ← PqxdhDeploymentEnvironment.onEnv (createPool setup pool word keyId)
      StateT.lift (PqxdhDeploymentEnvironment.issue (.appendOwner keyId word .fresh))
      pure (some index)

/-- The pool create in capability form, run by the World with its counts forgotten: the pool create on the environment's registration state, and one new fresh owner in the World. -/
theorem createPoolStep_effects (pool : List (Pair KemSK)) (pin : Pqxdh.Bytes) (keyId : Std.U64) (e : EnvState KemSK Bk)
    (w : PqxdhRecordLiftWorld.State n) :
    Prod.map id uncount <$> (simulateQ PqxdhRecordLiftWorld.effects
        ((createPoolStep (n := n) setup pool pin keyId).run e)).run w =
      match PqxdhDeploymentInterface.parsePin pin with
      | none => pure ((none, e), uncount w)
      | some word => (fun result => ((some result.1, { e with native := strip result.2 }),
          uncount { w with owners := w.owners ++ [.inactive .fresh] })) <$>
            (createPool setup pool word keyId).run e.native := by
  unfold createPoolStep
  rcases parsed : PqxdhDeploymentInterface.parsePin pin with _ | word
  · simp only [StateT.run_pure, simulateQ_pure, map_pure]
    rfl
  · simp only [StateT.run_bind, StateT.run_lift, StateT.run_pure, bind_assoc, pure_bind]
    rw [show (PqxdhDeploymentEnvironment.onEnv (n := n) (Bk := Bk) (createPool setup pool word keyId)).run e =
      (fun result => (result.1, { e with native := strip result.2 })) <$>
        coins (n := n) ((createPool setup pool word keyId).run e.native) from rfl, bind_map_left]
    rw [effects_then ctxAdmin _ (coins_noAdmin _) _ (fun result x => pure ((some result.1, { e with native := strip result.2 }),
      uncount { x with owners := x.owners ++ [.inactive .fresh] })) (fun result x => ?_) w]
    · rw [PqxdhDeploymentEnvironment.ctxEffects_coins, bind_map_left]
      simp only [bind_pure_comp]
      rfl
    · rw [effects_issue_then, effects_append, map_pure]
      rfl

/-- The pool create in capability form splits the ideal registration's create command (`PqxdhDeploymentIdealSteps.createReg`): the reassembled law is the command's, exactly. -/
theorem createPool_law (pool : List (Pair KemSK)) (pin : Pqxdh.Bytes) (keyId : Std.U64) (e : EnvState KemSK Bk)
    (w : PqxdhRecordLiftWorld.State n) (good : Good created e w) :
    (fun result => (result.1.1, merge result.1.2 result.2)) <$> (simulateQ PqxdhRecordLiftWorld.effects
        ((createPoolStep (n := n) setup pool pin keyId).run e)).run w =
      (createReg setup pool pin keyId).run (merge e w) := by
  rw [law_uncount, createPoolStep_effects]
  rcases parsed : PqxdhDeploymentInterface.parsePin pin with _ | word
  · rw [createReg_run, parsed, map_pure]
    rfl
  · have length : (merge e w).base.native.owners.length = e.native.owners.length := by
      simp only [merge, fill, List.length_mapIdx]
    rw [createReg_run, parsed]
    simp only [createPool_run, map_bind, map_pure, length]
    refine bind_congr fun identity => bind_congr fun prekey => bind_congr fun keys => ?_
    rw [create_merge created e w good _ rfl]
    simp only [merge, fill]

/-- The pool create in capability form keeps admissibility. -/
theorem createPool_keeps (pool : List (Pair KemSK)) (pin : Pqxdh.Bytes) (keyId : Std.U64) (e : EnvState KemSK Bk)
    (w : PqxdhRecordLiftWorld.State n) (good : Good created e w) :
    ∀ result ∈ support ((simulateQ PqxdhRecordLiftWorld.effects
        ((createPoolStep (n := n) setup pool pin keyId).run e)).run w),
      Good created result.1.2 result.2 := by
  apply keeps_uncount _ (Good created) (good_uncount created)
  rw [createPoolStep_effects]
  rcases parsed : PqxdhDeploymentInterface.parsePin pin with _ | word
  · intro result supported
    simp only [support_pure, Set.mem_singleton_iff] at supported
    subst supported
    exact uncount_good created e w good
  · intro result supported
    rw [support_map] at supported
    obtain ⟨inner, member, rfl⟩ := supported
    rw [createPool_run] at member
    simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at member
    obtain ⟨identity, _, prekey, _, keys, _, rfl⟩ := member
    obtain ⟨world, found, sender, identity', peers⟩ := good_server created e w good
    refine uncount_good created _ _ (good_intro created _ _ _ world rfl good.createdEq found sender identity' peers ?_
      (matched_append w _ (good_matched created e w good) good.ownersLength _ rfl))
    simp only [List.length_append, List.length_singleton, good.ownersLength]

/-- The pool create in capability form splits the ideal registration's create command: the reassembled law is the command's (exactly) and admissibility is kept. -/
theorem createPool_splits (pool : List (Pair KemSK)) (pin : Pqxdh.Bytes) (keyId : Std.U64) (e : EnvState KemSK Bk)
    (w : PqxdhRecordLiftWorld.State n) (good : Good created e w) :
    LawEq ((fun result => (result.1.1, merge result.1.2 result.2)) <$> (simulateQ PqxdhRecordLiftWorld.effects
        ((createPoolStep (n := n) setup pool pin keyId).run e)).run w)
      ((createReg setup pool pin keyId).run (merge e w)) ∧
    ∀ result ∈ support ((simulateQ PqxdhRecordLiftWorld.effects
        ((createPoolStep (n := n) setup pool pin keyId).run e)).run w),
      Good created result.1.2 result.2 :=
  ⟨LawEq.of_eq (createPool_law setup created pool pin keyId e w good),
    createPool_keeps setup created pool pin keyId e w good⟩

end Pool

/-! ### The real splits on any backend and slot count -/

section Real
variable {Bk : Type} {n : Nat} {ι : Type} {baseSpec : OracleSpec ι} {Reader Response : Type}
  (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
  (route : RawCtxServerRouting.SenderDecoder)

/-- The per-command real splits on any backend and slot count: the real environment step `realStep` splits the real registration handler on that backend (`realRegAt`) of every constructed Server, relative to the trivial admissibility predicate. -/
theorem real_splitsAt (created : PqxdhLiveServerConstruction.Created Unit) :
    Splits created (realRegAt (Bk := Bk) (n := n) setup codec route checks created)
      (PqxdhDeploymentEnvironment.realStep (n := n) setup codec checks) (fun _ _ => True) := by
  rw [PqxdhDeploymentEnvironmentJoin.splits_true]
  intro query e w good
  rcases query with ⟨command, allowed⟩
  cases command with
  | create pin keyId => exact realAt_splits_create setup codec checks route created pin keyId e w good
  | bundle owner => exact realAt_splits_bundle setup codec checks route created owner e w good
  | accept raw => exact realAt_splits_accept setup codec checks route created raw e w good
  | build session payload => exact realAt_splits_build setup codec checks route created session payload e w good
  | finish owner raw => exact realAt_splits_finish setup codec checks route created owner raw e w good
  | hmac key message => exact realAt_splits_hmac setup codec checks route created key message e w good
  | hash _ => exact absurd allowed id
  | serverSend _ _ => exact absurd allowed id
  | serverRaw _ => exact absurd allowed id
  | beaconSend _ _ => exact absurd allowed id
  | beaconRaw _ _ => exact absurd allowed id

end Real

end BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvReal

-- Axiom guards (generated)

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvReal.realRegAt_quiet' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvReal.realRegAt_quiet

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvReal.createStep_effects' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvReal.createStep_effects

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvReal.create_merge' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvReal.create_merge

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvReal.create_law' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvReal.create_law

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvReal.create_keeps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvReal.create_keeps

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvReal.hmacStep_effects' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvReal.hmacStep_effects

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvReal.hmac_law' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvReal.hmac_law

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvReal.hmac_keeps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvReal.hmac_keeps

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvReal.realRegAt_accept' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvReal.realRegAt_accept

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvReal.acceptStep_effects' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvReal.acceptStep_effects

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvReal.accept_law' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvReal.accept_law

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvReal.accept_keeps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvReal.accept_keeps

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvReal.bundleStep_effects' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvReal.bundleStep_effects

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvReal.bundle_outcome' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvReal.bundle_outcome

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvReal.bundle_law' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvReal.bundle_law

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvReal.bundle_keeps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvReal.bundle_keeps

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvReal.buildStep_effects' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvReal.buildStep_effects

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvReal.frameGame_server' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvReal.frameGame_server

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvReal.build_merge' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvReal.build_merge

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvReal.withCache_server' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvReal.withCache_server

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvReal.build_outcome' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvReal.build_outcome

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvReal.build_law' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvReal.build_law

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvReal.build_keeps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvReal.build_keeps

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvReal.finishStep_effects' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvReal.finishStep_effects

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvReal.finish_native_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvReal.finish_native_run

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvReal.finish_merge_set' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvReal.finish_merge_set

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvReal.finish_outcome' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvReal.finish_outcome

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvReal.finish_law' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvReal.finish_law

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvReal.finish_keeps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvReal.finish_keeps

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvReal.realAt_splits_create' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvReal.realAt_splits_create

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvReal.realAt_splits_bundle' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvReal.realAt_splits_bundle

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvReal.realAt_splits_accept' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvReal.realAt_splits_accept

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvReal.realAt_splits_build' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvReal.realAt_splits_build

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvReal.realAt_splits_finish' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvReal.realAt_splits_finish

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvReal.realAt_splits_hmac' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvReal.realAt_splits_hmac

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvReal.createPool_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvReal.createPool_run

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvReal.createReg_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvReal.createReg_run

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvReal.createPoolStep_effects' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvReal.createPoolStep_effects

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvReal.createPool_law' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvReal.createPool_law

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvReal.createPool_keeps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvReal.createPool_keeps

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvReal.createPool_splits' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvReal.createPool_splits

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvReal.real_splitsAt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvReal.real_splitsAt
