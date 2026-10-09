-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhDeploymentIdealDefer
import BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvReal

/-!
# The ideal environment's commands without a hidden install (CE-11b, unit U3)

CE-11b's ideal environment (design-v2 section 6.1) is the capability form of the final split form of the ideal registration `PqxdhDeploymentIdealDefer.idealSplit t p` on the backend `PqxdhDeploymentIdealSteps.SplitBk` with two slots. This module gives its commands that issue no hidden install, each with its split of `idealSplit`: from every admissible joint state (`PqxdhDeploymentEnvironmentJoin.Good`), the World run of the capability form, reassembled, has the law of the split form's command, exactly, and admissibility is kept. The marked build and owner k's challenge finish, which issue the hidden installs, and the environment step `idealStep` that dispatches all commands are later modules.

- The split form's commands without hidden effect (`idealSplit_create`, `idealSplit_bundle`, `idealSplit_hmac`, `idealSplit_accept_other` with the accept counter advanced by `bump`, `idealSplit_build_real`, `idealSplit_finish_real`) are the pool create and the real commands on the split backend, through `slotRunX_coins` (a coins-only slot step run against the allocator and the lazy service is that step with the allocator, the material and the seed table reattached), `realRegAt_attach` and `createReg_attach`.
- Slot frames of the record coordinates (the CTX cache, the Server's routing record and its identity key ID, which the reassembly fills in; `gamePut`, `markPutG`): the selected accept with its encapsulation exposed neither reads nor writes them (`acceptExposed_frameG`, from `acceptActive_frameG` and `acceptInactive_frameG`, with the marker tail `tailCE_tail_frameG`, the forwarded marker client `tailCE_forward_frameG` and the native accept tail `serverTail_frameG`). `slotGame` runs a slot step against the allocator in front of a slot service as a native step, which is a native frame of the record coordinates when the slot step is a slot frame of them (`slotGame_nframe`); in front of the lazy service the seed table is a frame of the run (`slotGame_seeds`).
- The selected raw accept in capability form (`acceptSelectedEnv`): the selected accept (`acceptGame`) on the environment's stripped shared state against the allocator and the lazy material service on the environment's backend, every coin a coin effect and no record-relevant request. `idealSplit_accept_selected` is the split form's selected accept in the same shape, `acceptSelected_law` the exact reassembled law and `acceptSelected_keeps` the preservation of admissibility.
- `create_splits`, `bundle_splits`, `hmac_splits`, `accept_other_splits`, `accept_selected_splits`, `build_real_splits` and `finish_real_splits` pair the law and admissibility per command, from CE-11a's real commands on any backend (`PqxdhDeploymentIdealEnvReal`). `good_backend`, `initSentAt_fill` and `establishedAt_fill` are their tools.

The environment-specific admissibility predicate (`IdealInv`, design-v2 section 6.2) is not used here: these commands neither issue a hidden install nor read the World's used markers. These are equalities of programs and in law; no security claim is made here.
-/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete PqxdhRefinement

set_option autoImplicit false

namespace BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvStep
open PqxdhServerAuthExperiment (Setup Codec Checks GameState)
open PqxdhServerAuthNative (NativeState NativeGame)
open PqxdhRecordLiftInterface (Slot Capability CapabilitySpec EnvEffects EnvQuery EnvSpec Environment EffectKind)
open PqxdhDeploymentEnvironment (EnvState EnvStep strip Stripped coins)
open PqxdhDeploymentEnvironmentJoin (merge fill Good Splits uncount)
open PqxdhDeploymentBackend (XState RegImpl seedLens)
open PqxdhDeploymentIdealSlots (Coord SlotSpec)
open PqxdhDeploymentIdealSteps (realRegAt onSlots liftS IdealCore SplitBk createReg acceptStep acceptExposed
  initSentAt establishedAt publishedKey idealProg erasedHidden)
open PqxdhDeploymentIdealErase (onPair onPair_run onPair_onSlots)
open PqxdhDeploymentIdealKeys (slotCoreX detachX attachX)
open PqxdhDeploymentIdealKernel (slotRunX MatCache SeedCache lazyDummy buildStepC finishStepC slotCoreX_run)
open PqxdhDeploymentIdealDefer (idealSplit serverInstall beaconInstall xInstall)
open PqxdhDeploymentIdealParams (Target Params)
open PqxdhRegistrationJointKemSecondEntry (Alloc slotImpl)
open LazyOracleDiscard (LawEq StateLens)

variable {KemSK : Type}

/-! ### The real commands of the final split form -/

section Bridge
variable {ι : Type} {baseSpec : OracleSpec ι} {Reader Response : Type}
  (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
  (checks : Checks) {count : ℕ}

/-- A slot step whose run on the detached state is a coins-only step, run by `slotRunX`: that step, with the allocator, the material and the seed table reattached. -/
theorem slotRunX_coins {β : Type} (svc : PqxdhDeploymentSeedSplit.SlotService (MatCache 2 × SeedCache 2) 2)
    (step : StateT (XState KemSK IdealCore 2) (OracleComp SlotSpec) β) (x : XState KemSK SplitBk 2)
    (y : XState KemSK IdealCore 2) (work : StateT (XState KemSK IdealCore 2) ProbComp β)
    (shape : step.run (detachX x) = (onSlots work).run y) :
    (slotRunX svc step).run x =
      (fun r => (r.1, attachX r.2 x.backend.2.1 (x.backend.1, x.seeds))) <$> work.run y := by
  change (fun r => (r.1, attachX r.2.1 r.2.2.1 r.2.2.2)) <$>
    (onPair svc step).run (detachX x, (x.backend.2.1, (x.backend.1, x.seeds))) = _
  rw [onPair_run, shape]
  change (fun r => (r.1, attachX r.2.1 r.2.2.1 r.2.2.2)) <$> ((fun r => (r.1.1, (r.1.2, r.2))) <$>
    (simulateQ (slotImpl svc) (liftS (work.run y))).run (x.backend.2.1, (x.backend.1, x.seeds))) = _
  rw [PqxdhDeploymentIdealErase.slotImpl_coins, Functor.map_map, Functor.map_map]

/-- The real registration on the detached state, reattached, is the real registration on the split backend. -/
theorem realRegAt_attach (created : PqxdhLiveServerConstruction.Created Unit) (query : EnvQuery)
    (x : XState KemSK SplitBk 2) :
    (fun r => (r.1, attachX r.2 x.backend.2.1 (x.backend.1, x.seeds))) <$>
        (realRegAt setup codec route checks created query).run (detachX x) =
      (realRegAt setup codec route checks created query).run x := by
  simp only [realRegAt, StateT.run, Functor.map_map]
  rfl

/-- The pool create on the detached state, reattached, is the pool create on the split backend. -/
theorem createReg_attach (pool : List (PqxdhLiveKemReservation.Pair KemSK)) (pin : Pqxdh.Bytes) (keyId : Std.U64)
    (x : XState KemSK SplitBk 2) :
    (fun r => (r.1, attachX r.2 x.backend.2.1 (x.backend.1, x.seeds))) <$> (createReg setup pool pin keyId).run (detachX x) =
      (createReg setup pool pin keyId).run x := by
  rw [PqxdhDeploymentIdealEnvReal.createReg_run, PqxdhDeploymentIdealEnvReal.createReg_run]
  rcases PqxdhDeploymentInterface.parsePin pin with _ | word
  · rw [map_pure]
    rfl
  · rw [Functor.map_map]
    rfl

/-- The final split form's create is the pool create on the split backend. -/
theorem idealSplit_create (t : Target count) (p : Params KemSK count) (created : PqxdhLiveServerConstruction.Created Unit)
    (pin : Pqxdh.Bytes) (keyId : Std.U64) (x : XState KemSK SplitBk 2) :
    (idealSplit setup codec route checks t p created ⟨.create pin keyId, trivial⟩).run x =
      (createReg setup (p.pool t) pin keyId).run x := by
  change (slotCoreX (idealProg setup codec route checks t p (erasedHidden setup codec checks)) lazyDummy created
    ⟨.create pin keyId, trivial⟩).run x = _
  rw [slotCoreX_run]
  exact (slotRunX_coins lazyDummy _ x (detachX x) (createReg setup (p.pool t) pin keyId) rfl).trans
    (createReg_attach setup (p.pool t) pin keyId x)

/-- The final split form's bundle is the real bundle on the split backend. -/
theorem idealSplit_bundle (t : Target count) (p : Params KemSK count) (created : PqxdhLiveServerConstruction.Created Unit)
    (owner : ℕ) (x : XState KemSK SplitBk 2) :
    (idealSplit setup codec route checks t p created ⟨.bundle owner, trivial⟩).run x =
      (realRegAt setup codec route checks created ⟨.bundle owner, trivial⟩).run x := by
  change (slotCoreX (idealProg setup codec route checks t p (erasedHidden setup codec checks)) lazyDummy created
    ⟨.bundle owner, trivial⟩).run x = _
  rw [slotCoreX_run]
  exact (slotRunX_coins lazyDummy _ x (detachX x)
    (realRegAt setup codec route checks created ⟨.bundle owner, trivial⟩) rfl).trans (realRegAt_attach setup codec route
      checks created _ x)

/-- The final split form's public HMAC is the real HMAC on the split backend. -/
theorem idealSplit_hmac (t : Target count) (p : Params KemSK count) (created : PqxdhLiveServerConstruction.Created Unit)
    (key : PqxdhSecretInputKdf.HmacBlock) (message : Pqxdh.Bytes) (x : XState KemSK SplitBk 2) :
    (idealSplit setup codec route checks t p created ⟨.hmac key message, trivial⟩).run x =
      (realRegAt setup codec route checks created ⟨.hmac key message, trivial⟩).run x := by
  change (slotCoreX (idealProg setup codec route checks t p (erasedHidden setup codec checks)) lazyDummy created
    ⟨.hmac key message, trivial⟩).run x = _
  rw [slotCoreX_run]
  exact (slotRunX_coins lazyDummy _ x (detachX x)
    (realRegAt setup codec route checks created ⟨.hmac key message, trivial⟩) rfl).trans (realRegAt_attach setup codec
      route checks created _ x)

/-- The split backend with the accept counter advanced. -/
def bump (backend : SplitBk) : SplitBk :=
  (backend.1, (backend.2.1, { backend.2.2 with accepts := backend.2.2.accepts + 1 }))

/-- Every raw accept of the final split form other than the selected ordinal is the real accept on the split backend, with the accept counter advanced. -/
theorem idealSplit_accept_other (t : Target count) (p : Params KemSK count)
    (created : PqxdhLiveServerConstruction.Created Unit) (raw : Pqxdh.Bytes) (x : XState KemSK SplitBk 2)
    (other : x.backend.2.2.accepts ≠ t.accept) :
    (idealSplit setup codec route checks t p created ⟨.accept raw, trivial⟩).run x =
      (realRegAt setup codec route checks created ⟨.accept raw, trivial⟩).run { x with backend := bump x.backend } := by
  change (slotCoreX (idealProg setup codec route checks t p (erasedHidden setup codec checks)) lazyDummy created
    ⟨.accept raw, trivial⟩).run x = _
  rw [slotCoreX_run]
  exact (slotRunX_coins lazyDummy _ x (detachX { x with backend := bump x.backend })
    (realRegAt setup codec route checks created ⟨.accept raw, trivial⟩)
    (PqxdhDeploymentIdealSteps.acceptStep_other setup codec route checks t p created raw (detachX x) other)).trans
      (realRegAt_attach setup codec route checks created _ { x with backend := bump x.backend })

/-- Every build of the final split form except the build of the marked session while it has a pending token is the real build on the split backend. -/
theorem idealSplit_build_real (t : Target count) (p : Params KemSK count)
    (created : PqxdhLiveServerConstruction.Created Unit) (session : ℕ) (payload : Option Pqxdh.Bytes)
    (x : XState KemSK SplitBk 2)
    (real : ∀ index coords, x.backend.2.2.marks = some (index, coords) →
      ¬ (index = session ∧ (x.base.native.shared.2.pending session).isSome)) :
    (idealSplit setup codec route checks t p created ⟨.build session payload, trivial⟩).run x =
      (realRegAt setup codec route checks created ⟨.build session payload, trivial⟩).run x := by
  have shape : (buildStepC setup codec checks route (erasedHidden setup codec checks) created session payload).run
      (detachX x) = (onSlots ((fun a => (a, (none : Option Coord))) <$>
        realRegAt setup codec route checks created ⟨.build session payload, trivial⟩)).run (detachX x) := by
    change (match x.backend.2.2.marks with
      | some (index, coords) => if index = session ∧ (x.base.native.shared.2.pending session).isSome then _ else _
      | none => _) = _
    rw [PqxdhDeploymentIdealErase.onSlots_run, StateT.run_map, liftS, OracleComp.liftComp_map]
    rcases marked : x.backend.2.2.marks with _ | ⟨index, coords⟩
    · rfl
    · simp only [real index coords marked, ↓reduceIte]
      rfl
  change (fun r => (r.1.1, r.2)) <$> ((slotRunX lazyDummy (buildStepC setup codec checks route
    (erasedHidden setup codec checks) created session payload)).run x >>= serverInstall) = _
  rw [slotRunX_coins lazyDummy _ x (detachX x) _ shape, StateT.run_map, Functor.map_map, bind_map_left]
  have quiet : ∀ r : Option PqxdhServerRegistrationPublication.Response × XState KemSK IdealCore 2,
      serverInstall ((r.1, none), attachX r.2 x.backend.2.1 (x.backend.1, x.seeds)) =
        pure ((r.1, none), attachX r.2 x.backend.2.1 (x.backend.1, x.seeds)) := fun _ => rfl
  simp only [quiet, bind_pure_comp, Functor.map_map]
  exact realRegAt_attach setup codec route checks created _ x

/-- Every finish of the final split form except owner k's challenge finish (the selected accept active, owner k addressed in the `initSent` phase) is the real finish on the split backend. -/
theorem idealSplit_finish_real (t : Target count) (p : Params KemSK count)
    (created : PqxdhLiveServerConstruction.Created Unit) (owner : ℕ) (raw : Pqxdh.Bytes) (x : XState KemSK SplitBk 2)
    (real : ¬ (x.backend.2.2.active = true ∧ owner = t.kem.val ∧ initSentAt x.base.native.owners owner = true)) :
    (idealSplit setup codec route checks t p created ⟨.finish owner raw, trivial⟩).run x =
      (realRegAt setup codec route checks created ⟨.finish owner raw, trivial⟩).run x := by
  have shape : (finishStepC setup codec checks route t p (erasedHidden setup codec checks) created owner raw).run
      (detachX x) = (onSlots ((fun a => (a, (none : Option Coord))) <$>
        realRegAt setup codec route checks created ⟨.finish owner raw, trivial⟩)).run (detachX x) := by
    change (if x.backend.2.2.active = true ∧ owner = t.kem.val ∧ initSentAt x.base.native.owners owner = true then _
      else _) = _
    rw [PqxdhDeploymentIdealErase.onSlots_run, StateT.run_map, liftS, OracleComp.liftComp_map]
    simp only [real, ↓reduceIte]
    rfl
  change (fun r => (r.1.1, r.2)) <$> ((slotRunX lazyDummy (finishStepC setup codec checks route t p
    (erasedHidden setup codec checks) created owner raw)).run x >>= beaconInstall owner) = _
  rw [slotRunX_coins lazyDummy _ x (detachX x) _ shape, StateT.run_map, Functor.map_map, bind_map_left]
  have quiet : ∀ r : Option Pqxdh.Bytes × XState KemSK IdealCore 2,
      beaconInstall owner ((r.1, none), attachX r.2 x.backend.2.1 (x.backend.1, x.seeds)) =
        pure ((r.1, none), attachX r.2 x.backend.2.1 (x.backend.1, x.seeds)) := fun _ => rfl
  simp only [quiet, bind_pure_comp, Functor.map_map]
  exact realRegAt_attach setup codec route checks created _ x

end Bridge

/-! ### Slot frames of the record coordinates -/

section SlotFrames
variable {ι : Type} {baseSpec : OracleSpec ι} {Reader Response : Type}
  (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
open PqxdhDeploymentEnvironmentReal (NFrame frameGame nframe_bind nframe_pure nframe_local acceptRest_nframe
  acceptLogged_nframe)
open PqxdhDeploymentIdealErase (SlotFrame)
open PqxdhDeploymentIdealSteps (tailCE acceptActive acceptInactive)
open PqxdhServerAuthExperiment (GameState)

/-- The record coordinates of the shared native state that the reassembly fills in: the CTX cache, the Server's routing record and its identity key ID. -/
abbrev RecordCoords := CtxRomAuth.CtxRO.QueryCache × RawCtxServerRouting.Server Unit Unit × Std.U64

/-- The record coordinates of a shared native state replaced. -/
def gamePut (s : NativeState KemSK) (c : RecordCoords) : NativeState KemSK :=
  (s.1, frameGame c.1 c.2.1 c.2.2 s.2)

/-- The record coordinates of a shared native state with a recorded mark replaced. -/
def markPutG (s : NativeState KemSK × Option (ℕ × Coord)) (c : RecordCoords) : NativeState KemSK × Option (ℕ × Coord) :=
  (gamePut s.1 c, s.2)

/-- A native step on the native component of a marked state is a slot frame of the record coordinates when it is a frame of them. -/
theorem frame_markedG {α : Type} (step : NativeGame KemSK α)
    (frame : ∀ c : RecordCoords, NFrame (frameGame c.1 c.2.1 c.2.2) step) :
    SlotFrame markPutG (fun s => (fun r => (r.1, (r.2, s.2))) <$> liftS (step.run s.1) :
      StateT (NativeState KemSK × Option (ℕ × Coord)) (OracleComp SlotSpec) α) := fun s c => by
  rcases s with ⟨⟨family, game⟩, mark⟩
  change (fun r => (r.1, (r.2, mark))) <$> OracleComp.liftComp (step.run (family, frameGame c.1 c.2.1 c.2.2 game))
    SlotSpec = _
  rw [frame c family game, OracleComp.liftComp_map, Functor.map_map]
  change _ = (fun r => (r.1, markPutG r.2 c)) <$> ((fun r => (r.1, (r.2, mark))) <$> liftS (step.run (family, game)))
  rw [Functor.map_map]
  rfl

/-- The marker client's private root is a frame of the record coordinates. -/
theorem romRoot_nframeG (hmac : PqxdhSecretInputKdf.HmacSha512) (index : ℕ)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret) (input : PqxdhRegistrationJointKemOpaqueClient.Input Reader)
    (c : RecordCoords) :
    NFrame (frameGame c.1 c.2.1 c.2.2) (PqxdhRegistrationJointKemOpaqueClient.romRoot KemSK hmac index candidate input) := by
  unfold PqxdhRegistrationJointKemOpaqueClient.romRoot
  refine nframe_bind _ ?_ fun root => nframe_bind _ (nframe_local _ _ fun _ => rfl) fun _ => nframe_pure _ _
  intro family game
  simp only [PqxdhServerAuthNative.romRootBytes, StateT.run, Functor.map_map]

/-- Every request of the marker client under `tailCE` is a slot frame of the record coordinates. -/
theorem tailCE_client_frameG (hmac : PqxdhSecretInputKdf.HmacSha512) (index : ℕ)
    (query : (PqxdhRegistrationJointKemOpaqueClient.Spec Reader).Domain) :
    SlotFrame markPutG (tailCE (KemSK := KemSK) (Reader := Reader) hmac index (.inl query)) := by
  rcases query with input | auxiliary
  · intro s c
    simp only [tailCE]
    cases input.shared with
    | challenge => rfl
    | known secret => exact frame_markedG _ (fun c => romRoot_nframeG hmac index _ input c) s c
  · cases auxiliary with
    | eraseShared => exact frame_markedG _ (fun _ => nframe_pure _ _)
    | eraseInput => exact frame_markedG _ (fun _ => nframe_pure _ _)
    | consume rid =>
        exact frame_markedG (PqxdhServerAuthNative.nativeConsume rid) (fun _ => nframe_local _ _ fun _ => rfl)

/-- The forwarded marker client under `tailCE` is a slot frame of the record coordinates. -/
theorem tailCE_forward_frameG (hmac : PqxdhSecretInputKdf.HmacSha512) (index : ℕ) {α : Type}
    (work : OracleComp (PqxdhRegistrationJointKemOpaqueClient.Spec Reader) α) :
    SlotFrame markPutG (simulateQ (tailCE (KemSK := KemSK) hmac index)
      (simulateQ PqxdhRegistrationJointKemOpaqueTail.forward work)) := by
  induction work using OracleComp.inductionOn with
  | pure a => simp only [simulateQ_pure]; exact SlotFrame.pure _ a
  | query_bind q next ih =>
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, id_map,
        PqxdhRegistrationJointKemOpaqueTail.forward]
      exact SlotFrame.bind (tailCE_client_frameG hmac index q) ih

/-- The marker tail after its install request is a slot frame of the record coordinates under `tailCE`. -/
theorem tailRest_frameG (hmac : PqxdhSecretInputKdf.HmacSha512) (sessions : ℕ) (serverKeyId : Std.U64)
    (publicIdentity : PqxdhJointIdentity.PublicIdentity) (index : ℕ) (control : beaconcrypt_core.pqxdh.ServerState)
    (collected : Option (PqxdhRegistrationJointKemOpaqueClient.Input Reader) × List Pqxdh.Bytes) :
    SlotFrame markPutG (simulateQ (tailCE (KemSK := KemSK) hmac sessions)
      (PqxdhDeploymentIdealErase.tailRest serverKeyId publicIdentity index control collected)) := by
  unfold PqxdhDeploymentIdealErase.tailRest
  rcases collected with ⟨_ | input, consumed⟩
  · simp only [simulateQ_pure]
    exact SlotFrame.pure _ _
  · simp only [simulateQ_bind]
    refine SlotFrame.bind (tailCE_forward_frameG hmac sessions _) fun returned => ?_
    rcases returned with (_ | token) | _ | _
    · simp only [simulateQ_pure]
      exact SlotFrame.pure _ _
    · simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, id_map,
        simulateQ_pure]
      exact SlotFrame.bind (frame_markedG (PqxdhServerAuthNative.nativeModify fun current =>
        { current with pending := Function.update current.pending index (some token) })
          (fun _ => nframe_local _ _ fun _ => rfl)) fun _ => SlotFrame.pure _ _
    · simp only [simulateQ_pure]
      exact SlotFrame.pure _ _
    · simp only [simulateQ_pure]
      exact SlotFrame.pure _ _

/-- The marker tail under `tailCE`, from a game state with replaced record coordinates, is the marker tail with its final record coordinates replaced. -/
theorem tailCE_tail_frameG (hmac : PqxdhSecretInputKdf.HmacSha512) (serverKeyId : Std.U64)
    (publicIdentity : PqxdhJointIdentity.PublicIdentity) (game : GameState KemSK)
    (collected : Option (PqxdhRegistrationJointKemOpaqueClient.Input Reader) × List Pqxdh.Bytes)
    (family : PqxdhJointDhExtractFamily.State) (other : GameState KemSK) (mark : Option (ℕ × Coord))
    (c : RecordCoords) :
    (simulateQ (tailCE (KemSK := KemSK) hmac game.sessions)
        (PqxdhRegistrationJointKemOpaqueTail.tail serverKeyId publicIdentity (frameGame c.1 c.2.1 c.2.2 game)
          collected)).run ((family, other), mark) =
      (fun r => (r.1, markPutG r.2 c)) <$> (simulateQ (tailCE (KemSK := KemSK) hmac game.sessions)
        (PqxdhRegistrationJointKemOpaqueTail.tail serverKeyId publicIdentity game collected)).run ((family, game), mark) := by
  rw [PqxdhDeploymentIdealErase.tail_split, PqxdhDeploymentIdealErase.tail_split, simulateQ_bind, simulateQ_bind,
    StateT.run_bind, StateT.run_bind]
  have install : ∀ (st : GameState KemSK) (s0 : NativeState KemSK × Option (ℕ × Coord)),
      (simulateQ (tailCE (KemSK := KemSK) (Reader := Reader) hmac game.sessions)
        (liftM ((PqxdhRegistrationJointKemOpaqueTail.Spec Reader KemSK).query (.inr (.install st))))).run s0 =
        pure ((), ((s0.1.1, st), s0.2)) := by
    intro st s0
    simp only [simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, id_map]
    rfl
  rw [install, install, pure_bind, pure_bind]
  exact tailRest_frameG hmac game.sessions serverKeyId publicIdentity game.sessions game.server.control collected
    ((family, { game with sessions := game.sessions + 1, server := { game.server with consumed := collected.2 } }), mark) c

/-- The native accept tail, from a game state with replaced record coordinates, is the tail with its final record coordinates replaced. -/
theorem serverTail_frameG (publicIdentity : PqxdhJointIdentity.PublicIdentity) (game : GameState KemSK)
    (collected : Option (PqxdhServerRootPreparation.Inputs Reader PqxdhJointGapDh.ScalarBytes
      PqxdhBeaconPhase2Preparation.Word32) × List Pqxdh.Bytes)
    (family : PqxdhJointDhExtractFamily.State) (other : GameState KemSK) (c : RecordCoords) :
    (PqxdhRegistrationJointServerAccept.tail setup publicIdentity (frameGame c.1 c.2.1 c.2.2 game) collected).run
        (family, other) =
      (fun r => (r.1, gamePut r.2 c)) <$>
        (PqxdhRegistrationJointServerAccept.tail setup publicIdentity game collected).run (family, game) := by
  rw [PqxdhDeploymentBackend.tail_eq, PqxdhDeploymentBackend.tail_eq, PqxdhDeploymentBackend.nativeSet_run_bind,
    PqxdhDeploymentBackend.nativeSet_run_bind]
  exact acceptRest_nframe setup c.1 c.2.1 c.2.2 publicIdentity game collected family
    { game with sessions := game.sessions + 1, server := { game.server with consumed := collected.2 } }

/-- The active selected accept is a slot frame of the record coordinates. -/
theorem acceptActive_frameG (seed : PqxdhJointIdentity.IdentitySeed) (challenge : PqxdhKemIndCca.MlKem768Ciphertext)
    (verified : PqxdhServerRootPreparation.Verified Reader) :
    SlotFrame gamePut (acceptActive (KemSK := KemSK) setup codec checks seed challenge verified) := by
  intro s c
  rcases s with ⟨family, game⟩
  change (acceptActive setup codec checks seed challenge verified).run (family, frameGame c.1 c.2.1 c.2.2 game) =
    (fun r => (r.1, gamePut r.2 c)) <$> (acceptActive setup codec checks seed challenge verified).run (family, game)
  simp only [acceptActive, PqxdhDeploymentIdealSteps.liftS, StateT.run]
  rw [map_bind]
  refine bind_congr fun pre => ?_
  rcases pre with ⟨⟨_ | ephemeral, logged⟩, consumed⟩
  · have h := serverTail_frameG (Reader := Reader) setup (setup.joint.publicKeys seed) game (none, consumed) family
      (frameGame c.1 c.2.1 c.2.2 game) c
    simp only [StateT.run] at h
    simp only
    rw [h, OracleComp.liftComp_map, bind_map_left, map_bind]
    refine bind_congr fun r => ?_
    rw [map_pure]
  · simp only
    rw [map_bind]
    refine bind_congr fun prepared => ?_
    have h := tailCE_tail_frameG setup.hmac setup.serverKeyId (setup.joint.publicKeys seed) game prepared family
      (frameGame c.1 c.2.1 c.2.2 game) none c
    simp only [StateT.run] at h
    have sessions : (frameGame c.1 c.2.1 c.2.2 game).sessions = game.sessions := rfl
    rw [sessions, h, bind_map_left, map_bind]
    refine bind_congr fun answer => ?_
    rw [map_pure]
    rfl

/-- The inactive selected accept (the LQ-F logged accept) is a slot frame of the record coordinates. -/
theorem acceptInactive_frameG (seed : PqxdhJointIdentity.IdentitySeed) (raw : Pqxdh.Bytes) :
    SlotFrame gamePut (acceptInactive (KemSK := KemSK) setup codec checks seed raw) := fun s c => by
  rcases s with ⟨family, game⟩
  change (fun r => ((r.1, (false, none)), r.2)) <$> OracleComp.liftComp
      ((PqxdhDeploymentLaterServerNative.acceptLogged setup codec checks seed raw).run
        (family, frameGame c.1 c.2.1 c.2.2 game)) SlotSpec = _
  rw [acceptLogged_nframe setup codec checks c.1 c.2.1 c.2.2 seed raw family game, OracleComp.liftComp_map,
    Functor.map_map]
  change _ = (fun r => (r.1, gamePut r.2 c)) <$> ((fun r => ((r.1, (false, none)), r.2)) <$> OracleComp.liftComp
      ((PqxdhDeploymentLaterServerNative.acceptLogged setup codec checks seed raw).run (family, game)) SlotSpec)
  rw [Functor.map_map]
  rfl

/-- The selected accept with its encapsulation exposed is a slot frame of the record coordinates: it neither reads nor writes the CTX cache, the Server's routing record or its identity key ID. -/
theorem acceptExposed_frameG (seed : PqxdhJointIdentity.IdentitySeed) (chosen : PqxdhLiveKemReservation.Pair KemSK)
    (challenge : PqxdhKemIndCca.MlKem768Ciphertext) (raw : Pqxdh.Bytes) :
    SlotFrame gamePut (PqxdhDeploymentIdealSteps.acceptExposed setup codec checks seed chosen challenge raw) := by
  unfold PqxdhDeploymentIdealSteps.acceptExposed
  split
  · split
    · exact acceptActive_frameG setup codec checks seed challenge _
    · exact acceptInactive_frameG setup codec checks seed raw
  · exact acceptInactive_frameG setup codec checks seed raw

end SlotFrames

/-! ### Slot runs as native steps -/

section SlotGame
open PqxdhDeploymentEnvironmentReal (NFrame frameGame)
open PqxdhDeploymentIdealErase (SlotFrame)

/-- A slot step of the shared native state run against the allocator in front of a slot service, from a given allocator and service state, as a native step returning the final allocator and service state with its reply. -/
noncomputable def slotGame {S α : Type} (svc : PqxdhDeploymentSeedSplit.SlotService S 2)
    (step : StateT (NativeState KemSK) (OracleComp SlotSpec) α) (start : Alloc Coord 2 × S) :
    NativeGame KemSK (α × (Alloc Coord 2 × S)) := fun shared =>
  (fun r => ((r.1.1, r.2), r.1.2)) <$> (simulateQ (slotImpl svc) (step.run shared)).run start

/-- A slot step that is a slot frame of the record coordinates runs as a native frame of them. -/
theorem slotGame_nframe {S α : Type} (svc : PqxdhDeploymentSeedSplit.SlotService S 2)
    (step : StateT (NativeState KemSK) (OracleComp SlotSpec) α) (start : Alloc Coord 2 × S)
    (frame : SlotFrame gamePut step) (c : RecordCoords) :
    NFrame (frameGame c.1 c.2.1 c.2.2) (slotGame svc step start) := by
  intro family game
  change (fun r => ((r.1.1, r.2), r.1.2)) <$> (simulateQ (slotImpl svc) (step.run (gamePut (family, game) c))).run start =
    _
  rw [frame (family, game) c, simulateQ_map, StateT.run_map, Functor.map_map]
  change _ = (fun result => (result.1, (result.2.1, frameGame c.1 c.2.1 c.2.2 result.2.2))) <$>
    ((fun r => ((r.1.1, r.2), r.1.2)) <$> (simulateQ (slotImpl svc) (step.run (family, game))).run start)
  rw [Functor.map_map]
  rfl

/-- The allocator and the lazy service state of the split forms. -/
abbrev SlotState := Alloc Coord 2 × (MatCache 2 × SeedCache 2)

/-- In front of the lazy service the seed table is a frame of a slot run. -/
theorem slotGame_seeds {α : Type} (step : StateT (NativeState KemSK) (OracleComp SlotSpec) α) (alloc : Alloc Coord 2)
    (m : MatCache 2) (c : SeedCache 2) (shared : NativeState KemSK) :
    (slotGame lazyDummy step (alloc, (m, c))).run shared =
      (fun r => ((r.1.1, (r.1.2.1, (r.1.2.2.1, c))), r.2)) <$> (slotGame lazyDummy step (alloc, (m, ∅))).run shared := by
  change (fun r => ((r.1.1, r.2), r.1.2)) <$> (simulateQ (slotImpl lazyDummy) (step.run shared)).run
    (PqxdhDeploymentIdealDefer.pairSeeds.set (alloc, (m, ∅)) c) = _
  rw [PqxdhDeploymentIdealDefer.simulateQ_frame _ _ (fun q s c => PqxdhDeploymentIdealDefer.slotImpl_lazy_frame q s c),
    Functor.map_map]
  change _ = (fun r : (α × SlotState) × NativeState KemSK => ((r.1.1, (r.1.2.1, (r.1.2.2.1, c))), r.2)) <$>
    ((fun r : (α × NativeState KemSK) × SlotState => ((r.1.1, r.2), r.1.2)) <$>
      (simulateQ (slotImpl lazyDummy) (step.run shared)).run (alloc, (m, ∅)))
  rw [Functor.map_map]
  rfl

end SlotGame

/-! ### The selected raw accept in capability form -/

section SelectedAccept
variable {ι : Type} {baseSpec : OracleSpec ι} {Reader Response : Type}
  (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
  (checks : Checks) {count : ℕ}
open PqxdhDeploymentIdealSteps (AcceptOut)
open PqxdhDeploymentEnvironmentReal (law_uncount effects_map effects_coins shared_run shared_fill shared_good
  map_congr_support merge_uncount keeps_uncount good_uncount uncount_good)

/-- The selected accept as a native step: the selected accept with its encapsulation exposed, against the allocator in front of the lazy service. -/
noncomputable def acceptGame (p : Params KemSK count) (seed : PqxdhJointIdentity.IdentitySeed) (raw : Pqxdh.Bytes)
    (start : SlotState) : NativeGame KemSK (AcceptOut × SlotState) :=
  slotGame lazyDummy (acceptExposed setup codec checks seed p.chosen p.challenge raw) start

/-- In front of the lazy service the seed table is a frame of the selected accept. -/
theorem acceptGame_seeds (p : Params KemSK count) (seed : PqxdhJointIdentity.IdentitySeed) (raw : Pqxdh.Bytes)
    (alloc : Alloc Coord 2) (m : MatCache 2) (c : SeedCache 2) (shared : NativeState KemSK) :
    (acceptGame setup codec checks p seed raw (alloc, (m, c))).run shared =
      (fun r => ((r.1.1, (r.1.2.1, (r.1.2.2.1, c))), r.2)) <$>
        (acceptGame setup codec checks p seed raw (alloc, (m, ∅))).run shared :=
  slotGame_seeds _ alloc m c shared

/-- The ideal backend after the selected accept: the accept counter advanced, and whether it was active with its mark. -/
def acceptedCore (core : IdealCore) (out : AcceptOut) : IdealCore :=
  { core with accepts := core.accepts + 1, active := out.2.1, marks := out.2.2 }

/-- The environment state after the selected accept: the stripped native result, the logged ephemeral entry, the material cache and the allocator after the run, and the ideal backend after the accept. -/
noncomputable def acceptedEnv (e : EnvState KemSK SplitBk) (r : (AcceptOut × SlotState) × NativeState KemSK) :
    EnvState KemSK SplitBk :=
  { e with
    native := strip { e.native with shared := r.2 }
    log := e.log ++ [r.1.1.1.2]
    backend := (r.1.2.2.1, (r.1.2.1, acceptedCore e.backend.2.2 r.1.1)) }

/-- The slot program's state after the selected accept (as `PqxdhDeploymentIdealSteps.acceptStep` assembles it). -/
def acceptedY (y : XState KemSK IdealCore 2) (r : AcceptOut × NativeState KemSK) : XState KemSK IdealCore 2 :=
  { y with
    base := { y.base with native := { y.base.native with shared := r.2 } }
    log := y.log ++ [r.1.1.2]
    backend := acceptedCore y.backend r.1 }

/-- The extended state after the selected accept. -/
def acceptedX (x : XState KemSK SplitBk 2) (r : (AcceptOut × SlotState) × NativeState KemSK) : XState KemSK SplitBk 2 :=
  { x with
    base := { x.base with native := { x.base.native with shared := r.2 } }
    log := x.log ++ [r.1.1.1.2]
    backend := (r.1.2.2.1, (r.1.2.1, acceptedCore x.backend.2.2 r.1.1))
    seeds := r.1.2.2.2 }

/-- The selected raw accept in capability form (design-v2 section 6.1): the selected accept with its encapsulation exposed on the environment's stripped shared state, its hidden read answered by the allocator in front of the lazy material service on the environment's backend, every coin a coin effect; no record-relevant request. -/
noncomputable def acceptSelectedEnv (p : Params KemSK count) (raw : Pqxdh.Bytes) :
    StateT (EnvState KemSK SplitBk) (OracleComp (EnvEffects 2)) (Option ℕ) := fun e =>
  (fun r => (r.1.1.1.1, acceptedEnv e r)) <$>
    coins ((acceptGame setup codec checks p e.created.seed raw (e.backend.2.1, (e.backend.1, ∅))).run e.native.shared)

/-- The final split form's selected raw accept is the selected accept against the allocator in front of the lazy service. -/
theorem idealSplit_accept_selected (t : Target count) (p : Params KemSK count)
    (created : PqxdhLiveServerConstruction.Created Unit) (raw : Pqxdh.Bytes) (x : XState KemSK SplitBk 2)
    (selected : x.backend.2.2.accepts = t.accept) :
    (idealSplit setup codec route checks t p created ⟨.accept raw, trivial⟩).run x =
      (fun r => (r.1.1.1.1, acceptedX x r)) <$>
        (acceptGame setup codec checks p created.seed raw (x.backend.2.1, (x.backend.1, x.seeds))).run
          x.base.native.shared := by
  change (slotCoreX (idealProg setup codec route checks t p (erasedHidden setup codec checks)) lazyDummy created
    ⟨.accept raw, trivial⟩).run x = _
  rw [slotCoreX_run]
  change (fun r => (r.1, attachX r.2.1 r.2.2.1 r.2.2.2)) <$>
    (onPair lazyDummy (acceptStep setup codec route checks t p created raw)).run
      (detachX x, (x.backend.2.1, (x.backend.1, x.seeds))) = _
  rw [onPair_run]
  have step : (acceptStep setup codec route checks t p created raw).run (detachX x) =
      (fun r => (r.1.1.1, acceptedY (detachX x) r)) <$>
        (acceptExposed setup codec checks created.seed p.chosen p.challenge raw).run x.base.native.shared := by
    change (if (detachX x).backend.accepts = t.accept then _ else _) = _
    rw [ite_eq_left_iff.mpr (fun no => absurd (show (detachX x).backend.accepts = t.accept from selected) no)]
    rfl
  rw [step, simulateQ_map, StateT.run_map, Functor.map_map, Functor.map_map]
  change _ = (fun r => (r.1.1.1.1, acceptedX x r)) <$> ((fun r => ((r.1.1, r.2), r.1.2)) <$>
    (simulateQ (slotImpl lazyDummy) ((acceptExposed setup codec checks created.seed p.chosen p.challenge raw).run
      x.base.native.shared)).run (x.backend.2.1, (x.backend.1, x.seeds)))
  rw [Functor.map_map]
  rfl

/-- The selected accept in capability form, run by the World with its counts forgotten: the native selected accept on the environment's shared state against the environment's allocator and material, the World unchanged. -/
theorem acceptSelected_effects (p : Params KemSK count) (raw : Pqxdh.Bytes) (e : EnvState KemSK SplitBk)
    (w : PqxdhRecordLiftWorld.State 2) :
    Prod.map id uncount <$> (simulateQ PqxdhRecordLiftWorld.effects ((acceptSelectedEnv setup codec checks p raw).run e)).run w =
      (fun r => ((r.1.1.1.1, acceptedEnv e r), uncount w)) <$>
        (acceptGame setup codec checks p e.created.seed raw (e.backend.2.1, (e.backend.1, ∅))).run e.native.shared := by
  change Prod.map id uncount <$> (simulateQ PqxdhRecordLiftWorld.effects ((fun r => (r.1.1.1.1, acceptedEnv e r)) <$>
    coins (n := 2) ((acceptGame setup codec checks p e.created.seed raw (e.backend.2.1, (e.backend.1, ∅))).run
      e.native.shared))).run w = _
  rw [effects_map, effects_coins, Functor.map_map]
  rfl

/-- The selected accept is a native frame of the record coordinates. -/
theorem acceptGame_nframe (p : Params KemSK count) (seed : PqxdhJointIdentity.IdentitySeed) (raw : Pqxdh.Bytes)
    (start : SlotState) (cache : CtxRomAuth.CtxRO.QueryCache) (server : RawCtxServerRouting.Server Unit Unit)
    (keyId : Std.U64) :
    PqxdhDeploymentEnvironmentReal.NFrame (PqxdhDeploymentEnvironmentReal.frameGame cache server keyId)
      (acceptGame setup codec checks p seed raw start) :=
  slotGame_nframe lazyDummy _ start (acceptExposed_frameG setup codec checks seed p.chosen p.challenge raw)
    (cache, server, keyId)

/-- The selected raw accept in capability form splits the final split form's selected accept: the reassembled law is the split form's, exactly. -/
theorem acceptSelected_law (t : Target count) (p : Params KemSK count) (created : PqxdhLiveServerConstruction.Created Unit)
    (raw : Pqxdh.Bytes) (e : EnvState KemSK SplitBk) (w : PqxdhRecordLiftWorld.State 2) (good : Good created e w)
    (selected : e.backend.2.2.accepts = t.accept) :
    (fun result => (result.1.1, merge result.1.2 result.2)) <$> (simulateQ PqxdhRecordLiftWorld.effects
        ((acceptSelectedEnv setup codec checks p raw).run e)).run w =
      (idealSplit setup codec route checks t p created ⟨.accept raw, trivial⟩).run (merge e w) := by
  obtain ⟨world, found, _, _, _⟩ := good.server
  rw [law_uncount, acceptSelected_effects, idealSplit_accept_selected setup codec route checks t p created raw _ selected,
    ← good.createdEq]
  rw [show (merge e w).base.native = fill w e.native from rfl,
    shared_run _ (acceptGame_nframe setup codec checks p e.created.seed raw _) e w world found]
  rw [show (merge e w).backend = e.backend from rfl, show (merge e w).seeds = w.seeds.1 from rfl,
    acceptGame_seeds setup codec checks p e.created.seed raw e.backend.2.1 e.backend.1 w.seeds.1, Functor.map_map,
    Functor.map_map, Functor.map_map]
  apply map_congr_support
  intro r supported
  simp only [merge_uncount]
  simp only [merge, acceptedEnv, acceptedX, shared_fill _ (acceptGame_nframe setup codec checks p e.created.seed raw _)
    created e w good world found r supported]

/-- The selected raw accept in capability form keeps admissibility. -/
theorem acceptSelected_keeps (p : Params KemSK count) (created : PqxdhLiveServerConstruction.Created Unit)
    (raw : Pqxdh.Bytes) (e : EnvState KemSK SplitBk) (w : PqxdhRecordLiftWorld.State 2) (good : Good created e w) :
    ∀ result ∈ support ((simulateQ PqxdhRecordLiftWorld.effects ((acceptSelectedEnv setup codec checks p raw).run e)).run w),
      Good created result.1.2 result.2 := by
  apply keeps_uncount _ (Good created) (good_uncount created)
  rw [acceptSelected_effects]
  intro result supported
  rw [support_map] at supported
  obtain ⟨inner, member, rfl⟩ := supported
  exact uncount_good created _ _ (shared_good _ (acceptGame_nframe setup codec checks p e.created.seed raw _) created e _ w
    good inner member rfl rfl)

end SelectedAccept

/-! ### The commands without a hidden effect -/

section Commands
variable {ι : Type} {baseSpec : OracleSpec ι} {Reader Response : Type}
  (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
  (checks : Checks) {count : ℕ}
open PqxdhDeploymentIdealEnvReal (realAt_splits_create realAt_splits_bundle realAt_splits_accept realAt_splits_build
  realAt_splits_finish realAt_splits_hmac createPool_splits createPoolStep)

/-- Admissibility does not read the backend. -/
theorem good_backend {Bk Bk' : Type} (created : PqxdhLiveServerConstruction.Created Unit) (e : EnvState KemSK Bk)
    (w : PqxdhRecordLiftWorld.State 2) (good : Good created e w) (b : Bk') :
    Good created (⟨e.native, b, e.snap, e.log, e.created⟩ : EnvState KemSK Bk') w :=
  ⟨good.stripped, good.createdEq, good.server, good.ownersLength, good.owners⟩

/-- Filling the World's record coordinates keeps which owners are in the `initSent` phase. -/
theorem initSentAt_fill (w : PqxdhRecordLiftWorld.State 2) (state : PqxdhRegistrationSchedule.State KemSK) (index : ℕ) :
    initSentAt (fill w state).owners index = initSentAt state.owners index := by
  simp only [initSentAt, fill, List.getElem?_mapIdx]
  rcases state.owners[index]? with _ | owner
  · rfl
  · simp only [Option.map_some, PqxdhDeploymentEnvironmentJoin.fillOwner]
    rcases w.owners[index]? with _ | (_ | ⟨shell, kernel⟩) <;> rcases hphase : owner.beacon.phase <;> simp [hphase]

/-- Filling the World's record coordinates keeps which owners are established. -/
theorem establishedAt_fill (w : PqxdhRecordLiftWorld.State 2) (state : PqxdhRegistrationSchedule.State KemSK)
    (index : ℕ) : establishedAt (fill w state).owners index = establishedAt state.owners index := by
  simp only [establishedAt, fill, List.getElem?_mapIdx]
  rcases state.owners[index]? with _ | owner
  · rfl
  · simp only [Option.map_some, PqxdhDeploymentEnvironmentJoin.fillOwner]
    rcases w.owners[index]? with _ | (_ | ⟨shell, kernel⟩) <;> rcases hphase : owner.beacon.phase <;> simp [hphase]

/-- The pool create in capability form splits the final split form's create: the reassembled law is the split form's (exactly) and admissibility is kept. -/
theorem create_splits (t : Target count) (p : Params KemSK count) (created : PqxdhLiveServerConstruction.Created Unit)
    (pin : Pqxdh.Bytes) (keyId : Std.U64) (e : EnvState KemSK SplitBk) (w : PqxdhRecordLiftWorld.State 2)
    (good : Good created e w) :
    LawEq ((fun result => (result.1.1, merge result.1.2 result.2)) <$> (simulateQ PqxdhRecordLiftWorld.effects
        ((createPoolStep (n := 2) setup (p.pool t) pin keyId).run e)).run w)
      ((idealSplit setup codec route checks t p created ⟨.create pin keyId, trivial⟩).run (merge e w)) ∧
    ∀ result ∈ support ((simulateQ PqxdhRecordLiftWorld.effects
        ((createPoolStep (n := 2) setup (p.pool t) pin keyId).run e)).run w),
      Good created result.1.2 result.2 := by
  rw [idealSplit_create]
  exact createPool_splits setup created (p.pool t) pin keyId e w good

/-- The real bundle in capability form splits the final split form's bundle. -/
theorem bundle_splits (t : Target count) (p : Params KemSK count) (created : PqxdhLiveServerConstruction.Created Unit)
    (owner : ℕ) (e : EnvState KemSK SplitBk) (w : PqxdhRecordLiftWorld.State 2) (good : Good created e w) :
    LawEq ((fun result => (result.1.1, merge result.1.2 result.2)) <$> (simulateQ PqxdhRecordLiftWorld.effects
        ((PqxdhDeploymentEnvironment.realStep (n := 2) setup codec checks ⟨.bundle owner, trivial⟩).run e)).run w)
      ((idealSplit setup codec route checks t p created ⟨.bundle owner, trivial⟩).run (merge e w)) ∧
    ∀ result ∈ support ((simulateQ PqxdhRecordLiftWorld.effects
        ((PqxdhDeploymentEnvironment.realStep (n := 2) setup codec checks ⟨.bundle owner, trivial⟩).run e)).run w),
      Good created result.1.2 result.2 := by
  rw [idealSplit_bundle]
  exact realAt_splits_bundle setup codec checks route created owner e w good

/-- The real public HMAC in capability form splits the final split form's HMAC. -/
theorem hmac_splits (t : Target count) (p : Params KemSK count) (created : PqxdhLiveServerConstruction.Created Unit)
    (key : PqxdhSecretInputKdf.HmacBlock) (message : Pqxdh.Bytes) (e : EnvState KemSK SplitBk)
    (w : PqxdhRecordLiftWorld.State 2) (good : Good created e w) :
    LawEq ((fun result => (result.1.1, merge result.1.2 result.2)) <$> (simulateQ PqxdhRecordLiftWorld.effects
        ((PqxdhDeploymentEnvironment.realStep (n := 2) setup codec checks ⟨.hmac key message, trivial⟩).run e)).run w)
      ((idealSplit setup codec route checks t p created ⟨.hmac key message, trivial⟩).run (merge e w)) ∧
    ∀ result ∈ support ((simulateQ PqxdhRecordLiftWorld.effects
        ((PqxdhDeploymentEnvironment.realStep (n := 2) setup codec checks ⟨.hmac key message, trivial⟩).run e)).run w),
      Good created result.1.2 result.2 := by
  rw [idealSplit_hmac]
  exact realAt_splits_hmac setup codec checks route created key message e w good

/-- Every raw accept other than the selected ordinal, in capability form (the real accept with the accept counter advanced), splits the final split form's accept. -/
theorem accept_other_splits (t : Target count) (p : Params KemSK count) (created : PqxdhLiveServerConstruction.Created Unit)
    (raw : Pqxdh.Bytes) (e : EnvState KemSK SplitBk) (w : PqxdhRecordLiftWorld.State 2) (good : Good created e w)
    (other : e.backend.2.2.accepts ≠ t.accept) :
    LawEq ((fun result => (result.1.1, merge result.1.2 result.2)) <$> (simulateQ PqxdhRecordLiftWorld.effects
        ((PqxdhDeploymentEnvironment.realStep (n := 2) setup codec checks ⟨.accept raw, trivial⟩).run
          { e with backend := bump e.backend })).run w)
      ((idealSplit setup codec route checks t p created ⟨.accept raw, trivial⟩).run (merge e w)) ∧
    ∀ result ∈ support ((simulateQ PqxdhRecordLiftWorld.effects
        ((PqxdhDeploymentEnvironment.realStep (n := 2) setup codec checks ⟨.accept raw, trivial⟩).run
          { e with backend := bump e.backend })).run w),
      Good created result.1.2 result.2 := by
  rw [idealSplit_accept_other setup codec route checks t p created raw (merge e w) other]
  exact realAt_splits_accept setup codec checks route created raw { e with backend := bump e.backend } w
    (good_backend created e w good (bump e.backend))

/-- The selected raw accept in capability form splits the final split form's selected accept. -/
theorem accept_selected_splits (t : Target count) (p : Params KemSK count)
    (created : PqxdhLiveServerConstruction.Created Unit) (raw : Pqxdh.Bytes) (e : EnvState KemSK SplitBk)
    (w : PqxdhRecordLiftWorld.State 2) (good : Good created e w) (selected : e.backend.2.2.accepts = t.accept) :
    LawEq ((fun result => (result.1.1, merge result.1.2 result.2)) <$> (simulateQ PqxdhRecordLiftWorld.effects
        ((acceptSelectedEnv setup codec checks p raw).run e)).run w)
      ((idealSplit setup codec route checks t p created ⟨.accept raw, trivial⟩).run (merge e w)) ∧
    ∀ result ∈ support ((simulateQ PqxdhRecordLiftWorld.effects ((acceptSelectedEnv setup codec checks p raw).run e)).run w),
      Good created result.1.2 result.2 :=
  ⟨LawEq.of_eq (acceptSelected_law setup codec route checks t p created raw e w good selected),
    acceptSelected_keeps setup codec checks p created raw e w good⟩

/-- Every build other than the build of the marked session while it has a pending token, in capability form (the real build), splits the final split form's build. -/
theorem build_real_splits (t : Target count) (p : Params KemSK count) (created : PqxdhLiveServerConstruction.Created Unit)
    (session : ℕ) (payload : Option Pqxdh.Bytes) (e : EnvState KemSK SplitBk) (w : PqxdhRecordLiftWorld.State 2)
    (good : Good created e w)
    (real : ∀ index coords, e.backend.2.2.marks = some (index, coords) →
      ¬ (index = session ∧ (e.native.shared.2.pending session).isSome)) :
    LawEq ((fun result => (result.1.1, merge result.1.2 result.2)) <$> (simulateQ PqxdhRecordLiftWorld.effects
        ((PqxdhDeploymentEnvironment.realStep (n := 2) setup codec checks ⟨.build session payload, trivial⟩).run e)).run w)
      ((idealSplit setup codec route checks t p created ⟨.build session payload, trivial⟩).run (merge e w)) ∧
    ∀ result ∈ support ((simulateQ PqxdhRecordLiftWorld.effects
        ((PqxdhDeploymentEnvironment.realStep (n := 2) setup codec checks ⟨.build session payload, trivial⟩).run e)).run w),
      Good created result.1.2 result.2 := by
  rw [idealSplit_build_real setup codec route checks t p created session payload (merge e w) real]
  exact realAt_splits_build setup codec checks route created session payload e w good

/-- Every finish other than owner k's challenge finish, in capability form (the real finish), splits the final split form's finish. -/
theorem finish_real_splits (t : Target count) (p : Params KemSK count) (created : PqxdhLiveServerConstruction.Created Unit)
    (owner : ℕ) (raw : Pqxdh.Bytes) (e : EnvState KemSK SplitBk) (w : PqxdhRecordLiftWorld.State 2)
    (good : Good created e w)
    (real : ¬ (e.backend.2.2.active = true ∧ owner = t.kem.val ∧ initSentAt e.native.owners owner = true)) :
    LawEq ((fun result => (result.1.1, merge result.1.2 result.2)) <$> (simulateQ PqxdhRecordLiftWorld.effects
        ((PqxdhDeploymentEnvironment.realStep (n := 2) setup codec checks ⟨.finish owner raw, trivial⟩).run e)).run w)
      ((idealSplit setup codec route checks t p created ⟨.finish owner raw, trivial⟩).run (merge e w)) ∧
    ∀ result ∈ support ((simulateQ PqxdhRecordLiftWorld.effects
        ((PqxdhDeploymentEnvironment.realStep (n := 2) setup codec checks ⟨.finish owner raw, trivial⟩).run e)).run w),
      Good created result.1.2 result.2 := by
  have real' : ¬ ((merge e w).backend.2.2.active = true ∧ owner = t.kem.val ∧
      initSentAt (merge e w).base.native.owners owner = true) := by
    rw [show (merge e w).base.native = fill w e.native from rfl, initSentAt_fill]
    exact real
  rw [idealSplit_finish_real setup codec route checks t p created owner raw (merge e w) real']
  exact realAt_splits_finish setup codec checks route created owner raw e w good

end Commands

end BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvStep

-- Axiom guards (generated)

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvStep.slotRunX_coins' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvStep.slotRunX_coins

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvStep.realRegAt_attach' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvStep.realRegAt_attach

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvStep.createReg_attach' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvStep.createReg_attach

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvStep.idealSplit_create' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvStep.idealSplit_create

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvStep.idealSplit_bundle' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvStep.idealSplit_bundle

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvStep.idealSplit_hmac' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvStep.idealSplit_hmac

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvStep.idealSplit_accept_other' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvStep.idealSplit_accept_other

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvStep.idealSplit_build_real' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvStep.idealSplit_build_real

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvStep.idealSplit_finish_real' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvStep.idealSplit_finish_real

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvStep.frame_markedG' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvStep.frame_markedG

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvStep.romRoot_nframeG' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvStep.romRoot_nframeG

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvStep.tailCE_client_frameG' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvStep.tailCE_client_frameG

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvStep.tailCE_forward_frameG' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvStep.tailCE_forward_frameG

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvStep.tailRest_frameG' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvStep.tailRest_frameG

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvStep.tailCE_tail_frameG' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvStep.tailCE_tail_frameG

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvStep.serverTail_frameG' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvStep.serverTail_frameG

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvStep.acceptActive_frameG' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvStep.acceptActive_frameG

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvStep.acceptInactive_frameG' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvStep.acceptInactive_frameG

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvStep.acceptExposed_frameG' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvStep.acceptExposed_frameG

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvStep.slotGame_nframe' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvStep.slotGame_nframe

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvStep.slotGame_seeds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvStep.slotGame_seeds

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvStep.acceptGame_seeds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvStep.acceptGame_seeds

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvStep.idealSplit_accept_selected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvStep.idealSplit_accept_selected

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvStep.acceptSelected_effects' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvStep.acceptSelected_effects

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvStep.acceptGame_nframe' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvStep.acceptGame_nframe

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvStep.acceptSelected_law' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvStep.acceptSelected_law

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvStep.acceptSelected_keeps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvStep.acceptSelected_keeps

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvStep.good_backend' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvStep.good_backend

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvStep.initSentAt_fill' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvStep.initSentAt_fill

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvStep.establishedAt_fill' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvStep.establishedAt_fill

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvStep.create_splits' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvStep.create_splits

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvStep.bundle_splits' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvStep.bundle_splits

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvStep.hmac_splits' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvStep.hmac_splits

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvStep.accept_other_splits' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvStep.accept_other_splits

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvStep.accept_selected_splits' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvStep.accept_selected_splits

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvStep.build_real_splits' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvStep.build_real_splits

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvStep.finish_real_splits' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvStep.finish_real_splits
