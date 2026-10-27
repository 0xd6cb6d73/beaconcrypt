-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvBuild

/-!
# The ideal environment's challenge finish (CE-11b, unit U3)

Owner k's challenge finish of CE-11b's ideal environment in capability form (design-v2 section 6.1), with its split of the final split form `PqxdhDeploymentIdealDefer.idealSplit` (owner k's finish in the `initSent` phase after an active selected accept, followed by the hidden Beacon install `beaconInstall`).

- The World's hidden Beacon install with its counts forgotten (`effects_hiddenBeacon`, `countFree_hiddenBeacon`, `countFree_hiddenOwnerEffect`), and the forwarded pieces: item 2's native Beacon tail after the root with its BLAKE2b request as the World's `.hash` (`knownFwd`, `knownFwd_factor`, `knownFwd_noAdmin`), with `simulateQ_noAdmin` and `countFree_noAdmin` (a program without administrative effect is count-free).
- `finishChallengeEnv`: the addressed owner's preparation with the challenge handle (`PqxdhDeploymentIdealSteps.preparationCE`, coins as coin effects), then either the commit of no staged result (`commitEnv`, published by the real owner effect) or the grouped finish request (`groupEnv`): with the challenge marker and nonzero DH outputs, the hidden read at the four DH coordinates against the allocator in front of the lazy material service on the environment's backend and CE-11a's split hidden finish of the slot (`PqxdhDeploymentEnvironment.finishSplitEnv`, which commits and issues the hidden Beacon install or the abort; `hiddenBackend` records the Beacon install ghost on establishment); with zero DH outputs, the commit of no staged result; with a known decapsulation result, the native private root on the environment's shared state and the forwarded continuation after it, then the commit. `finishedEnv` is the environment state after the finish (with the LQ-F snapshot). Its World run (`finishChallenge_effects`) uses `countFree_commitEnv`, `countFree_groupEnv`, `countFree_finishSplitEnv` and `finishSplitFwd_noAdmin`.
- The split form's challenge finish in explicit form: the grouped request in front of the lazy service (`groupNative`, `group_native`), the grouped owner (`owner_native`), owner k's challenge finish (`challenge_native`) and the slot run of the finish (`finishedX`, `slotRun_finish_hidden`); the hidden Beacon install does nothing unless owner k ends established (`beaconInstall_closed`) and otherwise reads the slot's seed lazily and puts the World's Beacon kernel of it on owner k (`beaconInstall_open`).
- `finishChallenge_law`: from an admissible joint state whose selected accept was active, whose owner k is in the `initSent` phase, whose allocator has room and whose World holds no Beacon marker, the reassembled law of the World run is the split form's, exactly, in every branch (through `commit_case`, `markedRoot_game`, `lazyRead_support`, `establishedAt_set`, `strip_setOwnerKernel`, `hiddenOwnerEffect_abort`, `hiddenOwnerEffect_establish`, CE-11a's `finishSplit_factor` and the reassembly `PqxdhDeploymentIdealEnvReal.finish_merge_set`). `commit_outcome`, `hiddenFinish_outcome` and `finishChallenge_outcome` describe every outcome (a commit without hidden read that sets the owner's World phase and changes nothing else in the World, or a hidden read at an allocated slot followed by an abort or by an establishment whose seed the World's table now holds, the slot's Beacon marker set), `finishChallenge_keeps` is the preservation of admissibility (with `stripOwner_setOwnerKernel`), and `finishChallenge_splits` pairs the law and admissibility.

The premises (an active selected accept, owner k in `initSent`, room in the allocator, no Beacon marker) are those that the ideal environment's admissibility predicate `IdealInv` provides (a later module). These are equalities of programs and in law and support facts; no security claim is made here.
-/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete PqxdhRefinement

set_option autoImplicit false

namespace BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvFinish
open PqxdhServerAuthExperiment (Setup Codec Checks GameState)

/-! ### The World's hidden Beacon install with its counts forgotten -/

section WorldInstalls
variable {n : ℕ}
open PqxdhDeploymentEnvironmentJoin (uncount)
open PqxdhDeploymentEnvironmentReal (effects_issue)

/-- An admitted hidden Beacon install with the World's counts forgotten: one lookup of the lazy seed table, the Beacon marker of the slot set, and the owner established with the shell and the World's Beacon kernel of the seed. -/
theorem effects_hiddenBeacon (owner : ℕ) (shell : PqxdhRecordLiftInterface.BeaconShell)
    (j : PqxdhRecordLiftInterface.Slot n) (w : PqxdhRecordLiftWorld.State n)
    (ready : w.owners[owner]? = some (.inactive .initSent)) (unused : w.used j .beacon = false) :
    Prod.map id uncount <$> (simulateQ PqxdhRecordLiftWorld.effects
        (PqxdhDeploymentEnvironment.issue (.installBeacon owner shell (.hidden j)))).run w =
      (fun r => ((), uncount { w with
        seeds := r.2
        used := Function.update w.used j (Function.update (w.used j) .beacon true)
        owners := w.owners.set owner (.established shell (PqxdhRecordLiftWorld.kernel .beacon r.1)) })) <$>
        (PqxdhRecordLiftLazyTable.impl j).run w.seeds := by
  rw [effects_issue]
  change (fun result => ((), uncount result.2)) <$> (PqxdhRecordLiftWorld.installBeacon owner shell (.hidden j)).run
    (PqxdhRecordLiftWorld.chargeEffect (.inr (.installBeacon owner shell (.hidden j))) w) = _
  have forgot := PqxdhRecordLiftWorld.countCoin_forget ((PqxdhRecordLiftLazyTable.impl j).run w.seeds)
    (PqxdhRecordLiftWorld.chargeEffect (.inr (.installBeacon owner shell (.hidden j))) w).primitive.1.uniform
  conv_rhs => rw [← forgot, Functor.map_map]
  have ready' : PqxdhRecordLiftWorld.BeaconReady
      (PqxdhRecordLiftWorld.chargeEffect (.inr (.installBeacon owner shell (.hidden j))) w) owner := ready
  have used' : (PqxdhRecordLiftWorld.chargeEffect (.inr (.installBeacon owner shell (.hidden j))) w).used j .beacon =
      false := unused
  simp only [PqxdhRecordLiftWorld.installBeacon, StateT.run, ready', PqxdhRecordLiftWorld.Unused, used', and_self,
    ↓reduceIte, PqxdhRecordLiftWorld.resolve, PqxdhRecordLiftWorld.sampled, bind_pure_comp, Functor.map_map]
  rfl

/-- An issued hidden Beacon install is count-free. -/
theorem countFree_hiddenBeacon (owner : ℕ) (shell : PqxdhRecordLiftInterface.BeaconShell)
    (j : PqxdhRecordLiftInterface.Slot n) :
    PqxdhDeploymentEnvironmentReal.CountFree
      (PqxdhDeploymentEnvironment.issue (n := n) (.installBeacon owner shell (.hidden j))) := fun w => by
  by_cases admitted : w.owners[owner]? = some (.inactive .initSent) ∧ w.used j .beacon = false
  · rw [effects_hiddenBeacon owner shell j w admitted.1 admitted.2,
      effects_hiddenBeacon owner shell j (uncount w) admitted.1 admitted.2]
    rfl
  · have refused : ∀ v : PqxdhRecordLiftWorld.State n, v.owners = w.owners → v.used = w.used →
        (PqxdhRecordLiftWorld.installBeacon owner shell (.hidden j)).run v = pure (false, v) := by
      intro v owners used
      refine PqxdhRecordLiftWorld.installBeacon_refused owner shell _ v fun both => admitted ?_
      obtain ⟨ready, unused⟩ := both
      exact ⟨owners ▸ ready, used ▸ unused⟩
    rw [effects_issue, effects_issue]
    change (fun result => ((), uncount result.2)) <$> (PqxdhRecordLiftWorld.installBeacon owner shell (.hidden j)).run
      (PqxdhRecordLiftWorld.chargeEffect _ w) = (fun result => ((), uncount result.2)) <$>
        (PqxdhRecordLiftWorld.installBeacon owner shell (.hidden j)).run (PqxdhRecordLiftWorld.chargeEffect _ (uncount w))
    rw [refused (PqxdhRecordLiftWorld.chargeEffect _ w) rfl rfl,
      refused (PqxdhRecordLiftWorld.chargeEffect _ (uncount w)) rfl rfl, map_pure, map_pure]
    rfl

/-- Publishing a hidden owner's finish is count-free. -/
theorem countFree_hiddenOwnerEffect {KemSK : Type} (j : PqxdhRecordLiftInterface.Slot n) (owner : ℕ)
    (before after : PqxdhRegistrationSchedule.Owner KemSK) :
    PqxdhDeploymentEnvironmentReal.CountFree (PqxdhDeploymentEnvironment.hiddenOwnerEffect (n := n) j owner before after) := by
  unfold PqxdhDeploymentEnvironment.hiddenOwnerEffect
  split
  · exact PqxdhDeploymentEnvironmentReal.countFree_pure _
  · exact countFree_hiddenBeacon _ _ j
  · split
    · split
      · exact PqxdhDeploymentEnvironmentReal.countFree_pure _
      · exact PqxdhDeploymentEnvironmentReal.countFree_issue _ trivial
    · exact PqxdhDeploymentEnvironmentReal.countFree_pure _

end WorldInstalls

/-! ### Forwarded pieces of owner k's challenge finish -/

section Forwarded
variable {KemSK : Type} {ι : Type} {baseSpec : OracleSpec ι} {Reader Response : Type}
  (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
open PqxdhDeploymentEnvironment (ctxEffects)
open PqxdhRecordLiftInterface (EnvEffects EffectKind effectKind CapabilitySpec)
open PqxdhPhase2DecapsulationRouting (Shared)

/-- Item 2's native Beacon tail after the private root (`PqxdhRegistrationJointKemPostSkeleton.tailNative`) with its BLAKE2b request forwarded as the World's `.hash`. -/
noncomputable def knownFwd :
    QueryImpl (PqxdhBeaconPhase2Shared.TailSpec Response Shared) (OracleComp (EnvEffects 2))
  | .inl query => PqxdhDeploymentEnvironment.primFwd setup.source.crypto setup.source query
  | .inr (.root _) => pure none
  | .inr (.initial request) => pure (RawCtxSourceHkdf.initialResponse setup.source.crypto request)
  | .inr (.application response) => pure (codec.application response)

variable (admin : QueryImpl (CapabilitySpec 2) (StateT CtxRomAuth.CtxRO.QueryCache ProbComp))

/-- Item 2's native Beacon tail after the root, on the CTX cache, is its forwarded form read through `ctxEffects`. -/
theorem knownFwd_factor {α : Type} (work : OracleComp (PqxdhBeaconPhase2Shared.TailSpec Response Shared) α)
    (cache : CtxRomAuth.CtxRO.QueryCache) :
    (simulateQ (PqxdhRegistrationJointKemPostSkeleton.tailNative setup codec) work).run ((), cache) =
      (fun result => (result.1, ((), result.2))) <$>
        (simulateQ (ctxEffects admin) (simulateQ (knownFwd setup codec) work)).run cache := by
  induction work using OracleComp.inductionOn generalizing cache with
  | pure value => simp only [simulateQ_pure, StateT.run_pure, map_pure]
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, id_map,
        StateT.run_bind, map_bind]
      rcases query with query | request
      · change (RawCtxSharedPrimitive.nativeImpl setup.source.crypto (RawCtxSourceHkdf.kdfImpl setup.source) query).run
          ((), cache) >>= _ = _
        rw [PqxdhDeploymentEnvironment.primFwd_factor admin]
        simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_apply]
        refine bind_congr fun result => ?_
        rw [← map_eq_bind_pure_comp]
        exact ih result.1 result.2
      · cases request with
        | root input =>
            simp only [PqxdhRegistrationJointKemPostSkeleton.tailNative, knownFwd, StateT.run_pure, pure_bind,
              simulateQ_pure]
            exact ih none cache
        | initial request =>
            simp only [PqxdhRegistrationJointKemPostSkeleton.tailNative, knownFwd, PqxdhServerAuthExperiment.beaconNative,
              StateT.run_pure, pure_bind, simulateQ_pure]
            exact ih _ cache
        | application response =>
            simp only [PqxdhRegistrationJointKemPostSkeleton.tailNative, knownFwd, PqxdhServerAuthExperiment.beaconNative,
              StateT.run_pure, pure_bind, simulateQ_pure]
            exact ih _ cache

/-- A simulation whose every step issues no administrative effect issues none. -/
theorem simulateQ_noAdmin {ι' α : Type} {spec' : OracleSpec ι'} (impl : QueryImpl spec' (OracleComp (EnvEffects 2)))
    (step : ∀ query, (impl query).IsQueryBoundP (fun effect => effectKind effect = .administrative) 0)
    (work : OracleComp spec' α) :
    (simulateQ impl work).IsQueryBoundP (fun effect => effectKind effect = .administrative) 0 := by
  induction work using OracleComp.inductionOn with
  | pure value => simp only [simulateQ_pure]; trivial
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, id_map]
      simpa only [Nat.add_zero] using isQueryBoundP_bind (step query) fun result _ => ih result

/-- The forwarded Beacon tail after the root issues no administrative effect. -/
theorem knownFwd_noAdmin {α : Type} (work : OracleComp (PqxdhBeaconPhase2Shared.TailSpec Response Shared) α) :
    (simulateQ (knownFwd setup codec) work).IsQueryBoundP (fun effect => effectKind effect = .administrative) 0 :=
  simulateQ_noAdmin _ (fun query => by
    rcases query with query | request
    · show (PqxdhDeploymentEnvironment.primFwd (n := 2) setup.source.crypto setup.source query).IsQueryBoundP _ 0
      simpa only [reduceCtorEq, false_and, ite_false] using
        PqxdhDeploymentEnvironment.primFwd_bound (n := 2) setup.source.crypto setup.source query .administrative
    · cases request <;> trivial) work

/-- A program without administrative effect is count-free. -/
theorem countFree_noAdmin {α : Type} (work : OracleComp (EnvEffects 2) α)
    (noAdmin : work.IsQueryBoundP (fun effect => effectKind effect = .administrative) 0) :
    PqxdhDeploymentEnvironmentReal.CountFree work := fun w => by
  rw [PqxdhDeploymentEnvironmentReal.effects_ctx PqxdhDeploymentEnvironmentReal.ctxAdmin work noAdmin,
    PqxdhDeploymentEnvironmentReal.effects_ctx PqxdhDeploymentEnvironmentReal.ctxAdmin work noAdmin]
  rfl

end Forwarded

/-! ### Owner k's challenge finish in capability form -/

section ChallengeFinish
variable {KemSK : Type} {ι : Type} {baseSpec : OracleSpec ι} {Reader Response : Type}
  (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
  (checks : Checks) {count : ℕ}
open PqxdhDeploymentEnvironment (EnvState strip coins ctxEffects)
open PqxdhDeploymentEnvironmentJoin (merge uncount Good)
open PqxdhDeploymentIdealSlots (Coord SlotSpec)
open PqxdhDeploymentIdealSteps (IdealCore SplitBk establishedAt preparationCE)
open PqxdhDeploymentIdealKernel (MatCache SeedCache lazyDummy)
open PqxdhDeploymentIdealEnvStep (SlotState)
open PqxdhRegistrationJointKemSecondEntry (slotImpl)
open PqxdhRegistrationJointKemPostSkeleton (Pending embed message)
open PqxdhRecordLiftInterface (EnvEffects)
open PqxdhDeploymentIdealParams (Target Params)
open PqxdhServerAuthNative (NativeState)

/-- The environment state after owner k's challenge finish: the LQ-F snapshot of the owner, the stripped registration state with the new shared state and the owner after the finish, and a backend. -/
noncomputable def finishedEnv (e : EnvState KemSK SplitBk) (owner : ℕ) (shared : NativeState KemSK)
    (after : PqxdhRegistrationSchedule.Owner KemSK) (backend : SplitBk) : EnvState KemSK SplitBk :=
  { e with
    snap := PqxdhDeploymentLater.snapshotAt e.snap e.native.owners (some owner)
    native := strip ⟨shared, e.native.owners.set owner after⟩
    backend := backend }

/-- The source commit of a finish with a staged result, published by the real owner effect (an abort, or the known install of an established owner), the backend unchanged. -/
noncomputable def commitEnv (e : EnvState KemSK SplitBk) (owner : ℕ) (control : beaconcrypt_core.pqxdh.BeaconInitSent)
    (before : PqxdhRegistrationSchedule.Owner KemSK) (shared : NativeState KemSK)
    (staged : Option PqxdhBeaconPhase2Publication.Staged) :
    OracleComp (EnvEffects 2) (Option Pqxdh.Bytes × EnvState KemSK SplitBk) :=
  PqxdhDeploymentEnvironment.ownerEffect owner before (PqxdhBeaconPhase2Publication.finish control before staged).2 >>=
    fun _ => pure ((PqxdhBeaconPhase2Publication.finish control before staged).1,
      finishedEnv e owner shared (PqxdhBeaconPhase2Publication.finish control before staged).2 e.backend)

/-- The backend after owner k's hidden finish: the material cache and the allocator after the hidden read, and the Beacon install ghost set to the read's coordinates when the owner ends established. -/
def hiddenBackend (e : EnvState KemSK SplitBk) (owner : ℕ) (after : PqxdhRegistrationSchedule.Owner KemSK)
    (coords : Coord) (slots : SlotState) : SplitBk :=
  (slots.2.1, (slots.1, { e.backend.2.2 with
    beacon := if establishedAt (e.native.owners.set owner after) owner then (some coords).or e.backend.2.2.beacon
      else e.backend.2.2.beacon }))

/-- The grouped finish request of owner k in capability form (item 2's `groupStep` with the erased hidden services, as `PqxdhDeploymentIdealSteps.groupCE` runs it): with the challenge marker and nonzero DH outputs, the hidden read at the four DH coordinates against the allocator in front of the lazy material service on the environment's backend, then CE-11a's split hidden finish of the slot (`PqxdhDeploymentEnvironment.finishSplitEnv`, which commits and issues the hidden Beacon install or the abort); with zero DH outputs, the commit of no staged result; with a known decapsulation result, the native private root on the environment's shared state and the native continuation after it with its BLAKE2b request forwarded, then the commit. -/
noncomputable def groupEnv (owner : ℕ) (control : beaconcrypt_core.pqxdh.BeaconInitSent)
    (before : PqxdhRegistrationSchedule.Owner KemSK) (e : EnvState KemSK SplitBk) (pending : Pending Response) :
    OracleComp (EnvEffects 2) (Option Pqxdh.Bytes × EnvState KemSK SplitBk) :=
  match pending.root.shared with
  | .challenge =>
      if Pqxdh.dhNonZero (absBytes pending.root.dh1, absBytes pending.root.dh2, absBytes pending.root.dh3,
          absBytes pending.root.dh4) then
        coins ((slotImpl lazyDummy (.inr (message pending.root.dh1 pending.root.dh2 pending.root.dh3
          pending.root.dh4))).run (e.backend.2.1, (e.backend.1, ∅))) >>= fun read =>
          match read.2.1.1 (message pending.root.dh1 pending.root.dh2 pending.root.dh3 pending.root.dh4) with
          | some j => (fun committed => (committed.1, finishedEnv e owner e.native.shared committed.2
              (hiddenBackend e owner committed.2 (message pending.root.dh1 pending.root.dh2 pending.root.dh3
                pending.root.dh4) read.2))) <$>
              PqxdhDeploymentEnvironment.finishSplitEnv setup codec (PqxdhDeploymentHiddenLayout.splitOutput read.1).1 j
                owner control before (embed pending)
          | none => commitEnv e owner control before e.native.shared none
      else commitEnv e owner control before e.native.shared none
  | .known _ => coins ((PqxdhRegistrationJointBeaconOpaqueFinish.markedRoot setup.hmac (List.Vector.replicate 32 0)
      pending.root).run e.native.shared) >>= fun r =>
      match r.1 with
      | none => commitEnv e owner control before r.2 none
      | some root => simulateQ (knownFwd setup codec) (PqxdhBeaconPhase2Shared.afterRoot codec.frameRead pending root) >>=
          fun staged => commitEnv e owner control before r.2 staged

/-- Owner k's challenge finish in capability form (design-v2 section 6.1): the addressed owner's preparation with the challenge handle (`PqxdhDeploymentIdealSteps.preparationCE`, its coins as coin effects), then the commit of no staged result or the grouped finish request (`groupEnv`). Every finish is preceded by the LQ-F snapshot of the owner. -/
noncomputable def finishChallengeEnv (p : Params KemSK count) (owner : ℕ) (raw : Pqxdh.Bytes) :
    StateT (EnvState KemSK SplitBk) (OracleComp (EnvEffects 2)) (Option Pqxdh.Bytes) := fun e =>
  match e.native.owners[owner]? with
  | some before => match before.beacon.phase with
      | .initSent control prekey oneTime kem =>
          coins (simulateQ (preparationCE setup codec p.challenge) (PqxdhBeaconPhase2Shared.prepare control
            before.beacon.identity prekey oneTime kem raw)) >>= fun prepared =>
            match prepared with
            | none => commitEnv e owner control before e.native.shared none
            | some pending => groupEnv setup codec owner control before e pending
      | _ => pure (none, { e with snap := PqxdhDeploymentLater.snapshotAt e.snap e.native.owners (some owner) })
  | none => pure (none, { e with snap := PqxdhDeploymentLater.snapshotAt e.snap e.native.owners (some owner) })

end ChallengeFinish

/-! ### The final split form's challenge finish in explicit form -/

section NativeFinish
variable {KemSK : Type} {ι : Type} {baseSpec : OracleSpec ι} {Reader Response : Type}
  (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
  (checks : Checks) {count : ℕ}
open PqxdhDeploymentIdealSlots (Coord SlotSpec)
open PqxdhDeploymentIdealSteps (IdealCore SplitBk establishedAt preparationCE erasedHidden groupCE)
open PqxdhDeploymentIdealKernel (MatCache SeedCache lazyDummy)
open PqxdhDeploymentIdealEnvStep (SlotState)
open PqxdhDeploymentIdealErase (onPair onPair_bind onPair_map onPair_pure onPair_onSlots onPair_run)
open PqxdhRegistrationJointKemSecondEntry (slotImpl)
open PqxdhRegistrationJointKemPostSkeleton (Pending embed message)
open PqxdhDeploymentIdealParams (Target Params)
open PqxdhServerAuthNative (NativeState)
open LazyOracleDiscard (StateLens)

/-- The grouped finish request with the erased hidden services in front of the lazy service, in explicit form on the shared native state and the allocator and lazy service state: the hidden read and the erased hidden finish at its value on the CTX cache, nothing, or the native finish with a known decapsulation result. -/
noncomputable def groupNative (pending : Pending Response) (s : NativeState KemSK) (slots : SlotState) :
    ProbComp (Option PqxdhBeaconPhase2Publication.Staged × ((NativeState KemSK × Option Coord) × SlotState)) :=
  match pending.root.shared with
  | .challenge =>
      if Pqxdh.dhNonZero (absBytes pending.root.dh1, absBytes pending.root.dh2, absBytes pending.root.dh3,
          absBytes pending.root.dh4) then
        (slotImpl lazyDummy (.inr (message pending.root.dh1 pending.root.dh2 pending.root.dh3 pending.root.dh4))).run
          slots >>= fun read =>
          (fun r => (r.1, ((r.2, some (message pending.root.dh1 pending.root.dh2 pending.root.dh3 pending.root.dh4)),
            read.2))) <$>
            (PqxdhServerAuthNative.nativeCtx (PqxdhDeploymentHiddenEntry.finishErasedSvc setup codec
              (PqxdhDeploymentHiddenLayout.splitOutput read.1).1 (PqxdhDeploymentHiddenLayout.splitOutput read.1).2
                (embed pending))).run s
      else pure (none, ((s, none), slots))
  | .known _ => (fun r => (r.1, ((r.2, none), slots))) <$>
      (PqxdhDeploymentIdealErase.knownWork setup codec pending).run s

/-- The grouped finish request in front of the lazy service is `groupNative`. -/
theorem group_native (pending : Pending Response) (s : NativeState KemSK) (slots : SlotState) :
    (onPair lazyDummy (groupCE (KemSK := KemSK) setup codec (erasedHidden setup codec checks) pending)).run
        ((s, none), slots) = groupNative setup codec pending s slots := by
  rw [PqxdhDeploymentIdealErase.groupCE_explicit]
  unfold PqxdhDeploymentIdealErase.groupExplicit groupNative
  rcases shared : pending.root.shared with _ | secret
  · simp only []
    split
    · rw [onPair_bind, StateT.run_bind, PqxdhDeploymentIdealKernel.onPair_readAt, bind_map_left]
      refine bind_congr fun read => ?_
      rw [onPair_onSlots]
      simp only [StateLens.lift, StateT.run, StateLens.fst, Functor.map_map]
      rfl
    · rw [onPair_pure, StateT.run_pure]
  · rw [onPair_onSlots]
    simp only [StateLens.lift, StateT.run, StateLens.fst, Functor.map_map]

/-- Owner k's grouped native finish in front of the lazy service, from an owner in the `initSent` phase: the preparation with the challenge handle, then the commit of no staged result or of the grouped finish request's result. -/
theorem owner_native (challenge : PqxdhKemIndCca.MlKem768Ciphertext) (raw : Pqxdh.Bytes)
    (before : PqxdhRegistrationSchedule.Owner KemSK) (control : beaconcrypt_core.pqxdh.BeaconInitSent)
    (prekey oneTime : PqxdhJointGapDh.ScalarBytes) (kem : PqxdhKemIndCca.MlKem768PublicKey × KemSK)
    (phase : before.beacon.phase = .initSent control prekey oneTime kem) (s : NativeState KemSK) (slots : SlotState) :
    (onPair lazyDummy (simulateQ (PqxdhDeploymentIdealSteps.ownerImplCE setup codec (erasedHidden setup codec checks)
        challenge) (PqxdhDeploymentIdealSteps.groupedOwnerCE (Response := Response) raw before))).run ((s, none), slots) =
      simulateQ (preparationCE setup codec challenge) (PqxdhBeaconPhase2Shared.prepare control before.beacon.identity
        prekey oneTime kem raw) >>= fun prepared =>
        match prepared with
        | none => pure (PqxdhBeaconPhase2Publication.finish control before none, ((s, none), slots))
        | some pending => (fun r => (PqxdhBeaconPhase2Publication.finish control before r.1, r.2)) <$>
            groupNative setup codec pending s slots := by
  rw [PqxdhDeploymentIdealErase.owner_explicit]
  unfold PqxdhDeploymentIdealErase.ownerExplicit
  split
  · rename_i control' prekey' oneTime' kem' phase'
    rw [phase] at phase'
    cases phase'
    rw [onPair_bind, StateT.run_bind, PqxdhDeploymentIdealKernel.onPair_onSlots_lift, bind_map_left]
    refine bind_congr fun prepared => ?_
    cases prepared with
    | none => rw [onPair_pure, StateT.run_pure]
    | some pending =>
        rw [onPair_map, StateT.run_map, group_native]
  · rename_i notInitSent
    exact absurd phase (notInitSent control prekey oneTime kem)

/-- Owner k's challenge finish in front of the lazy service, from a registration state whose owner k is in the `initSent` phase: the grouped native finish of the owner on the shared state, its returned owner reinstalled. -/
theorem challenge_native (challenge : PqxdhKemIndCca.MlKem768Ciphertext) (owner : ℕ) (raw : Pqxdh.Bytes)
    (sched : PqxdhRegistrationSchedule.State KemSK) (before : PqxdhRegistrationSchedule.Owner KemSK)
    (owned : sched.owners[owner]? = some before) (slots : SlotState) :
    (onPair lazyDummy (PqxdhDeploymentIdealSteps.finishChallenge setup codec (erasedHidden setup codec checks) challenge
        owner raw)).run ((sched, none), slots) =
      (fun r => (r.1.1, ((({ shared := r.2.1.1, owners := sched.owners.set owner r.1.2 } :
          PqxdhRegistrationSchedule.State KemSK), r.2.1.2), r.2.2))) <$>
        (onPair lazyDummy (simulateQ (PqxdhDeploymentIdealSteps.ownerImplCE setup codec (erasedHidden setup codec checks)
          challenge) (PqxdhDeploymentIdealSteps.groupedOwnerCE (Response := Response) raw before))).run
            ((sched.shared, none), slots) := by
  rw [PqxdhDeploymentIdealErase.onPair_dispatch _ _ (fun st => st.1.owners[owner]?)
    (PqxdhDeploymentIdealErase.challengeBranch setup codec (erasedHidden setup codec checks) challenge owner raw)
    (PqxdhDeploymentIdealKernel.finishChallenge_branch setup codec _ challenge owner raw)]
  simp only [owned]
  exact PqxdhDeploymentIdealErase.onPair_focus lazyDummy
    (PqxdhDeploymentIdealErase.challengeBranch setup codec (erasedHidden setup codec checks) challenge owner raw
      (some before))
    (simulateQ (PqxdhDeploymentIdealSteps.ownerImplCE setup codec (erasedHidden setup codec checks) challenge)
      (PqxdhDeploymentIdealSteps.groupedOwnerCE (Response := Response) raw before))
    (fun st => (st.1.shared, st.2))
    (fun st b q => (b.1, (({ shared := q.1, owners := st.1.owners.set owner b.2 } :
      PqxdhRegistrationSchedule.State KemSK), q.2))) (fun _ => rfl) ((sched, none), slots)

/-- The extended state after owner k's challenge finish, before its hidden install: the new shared state and owner, the LQ-F snapshot, the allocator, material and seed table after the run, and the Beacon install ghost set to the recorded coordinates when the owner ends established. -/
def finishedX (x : PqxdhDeploymentBackend.XState KemSK SplitBk 2) (owner : ℕ) (shared : NativeState KemSK)
    (after : PqxdhRegistrationSchedule.Owner KemSK) (recorded : Option Coord) (slots : SlotState) :
    PqxdhDeploymentBackend.XState KemSK SplitBk 2 :=
  ⟨{ x.base with native := ⟨shared, x.base.native.owners.set owner after⟩ },
    (slots.2.1, (slots.1, { x.backend.2.2 with
      beacon := if establishedAt (x.base.native.owners.set owner after) owner then recorded.or x.backend.2.2.beacon
        else x.backend.2.2.beacon })),
    slots.2.2, PqxdhDeploymentLater.snapshotAt x.snap x.base.native.owners (some owner), x.log⟩

/-- The final split form's challenge finish (before its hidden install) in explicit form, from a state whose selected accept was active and whose owner k is in the `initSent` phase. -/
theorem slotRun_finish_hidden (t : Target count) (p : Params KemSK count)
    (created : PqxdhLiveServerConstruction.Created Unit) (owner : ℕ) (raw : Pqxdh.Bytes)
    (x : PqxdhDeploymentBackend.XState KemSK SplitBk 2) (before : PqxdhRegistrationSchedule.Owner KemSK)
    (control : beaconcrypt_core.pqxdh.BeaconInitSent) (prekey oneTime : PqxdhJointGapDh.ScalarBytes)
    (kem : PqxdhKemIndCca.MlKem768PublicKey × KemSK)
    (chosen : x.backend.2.2.active = true ∧ owner = t.kem.val ∧ PqxdhDeploymentIdealSteps.initSentAt
      x.base.native.owners owner = true)
    (owned : x.base.native.owners[owner]? = some before)
    (phase : before.beacon.phase = .initSent control prekey oneTime kem) :
    (PqxdhDeploymentIdealKernel.slotRunX lazyDummy (PqxdhDeploymentIdealKernel.finishStepC setup codec checks route t p
        (erasedHidden setup codec checks) created owner raw)).run x =
      simulateQ (preparationCE setup codec p.challenge) (PqxdhBeaconPhase2Shared.prepare control before.beacon.identity
        prekey oneTime kem raw) >>= fun prepared =>
        match prepared with
        | none => pure (((PqxdhBeaconPhase2Publication.finish control before none).1, none),
            finishedX x owner x.base.native.shared (PqxdhBeaconPhase2Publication.finish control before none).2 none
              (x.backend.2.1, (x.backend.1, x.seeds)))
        | some pending => (fun r => (((PqxdhBeaconPhase2Publication.finish control before r.1).1, r.2.1.2),
            finishedX x owner r.2.1.1 (PqxdhBeaconPhase2Publication.finish control before r.1).2 r.2.1.2 r.2.2)) <$>
            groupNative setup codec pending x.base.native.shared (x.backend.2.1, (x.backend.1, x.seeds)) := by
  have chosen' : (PqxdhDeploymentIdealKeys.detachX x).backend.active = true ∧ owner = t.kem.val ∧
      PqxdhDeploymentIdealSteps.initSentAt (PqxdhDeploymentIdealKeys.detachX x).base.native.owners owner = true := chosen
  have shape : ∀ y : PqxdhDeploymentBackend.XState KemSK IdealCore 2,
      (PqxdhDeploymentIdealKernel.finishHiddenC setup codec p (erasedHidden setup codec checks) owner raw).run y =
        (fun r => (fun y (b : Option Pqxdh.Bytes) (q : PqxdhRegistrationSchedule.State KemSK × Option Coord) =>
          (((b, q.2), PqxdhDeploymentIdealKernel.assembleF y owner q) :
            (Option Pqxdh.Bytes × Option Coord) × PqxdhDeploymentBackend.XState KemSK IdealCore 2)) y r.1 r.2) <$>
          (PqxdhDeploymentIdealSteps.finishChallenge setup codec (erasedHidden setup codec checks) p.challenge owner
            raw).run ((fun y : PqxdhDeploymentBackend.XState KemSK IdealCore 2 => (y.base.native,
              (none : Option Coord))) y) := fun _ => rfl
  change (fun r => (r.1, PqxdhDeploymentIdealKeys.attachX r.2.1 r.2.2.1 r.2.2.2)) <$>
    (onPair lazyDummy (PqxdhDeploymentIdealKernel.finishStepC setup codec checks route t p
      (erasedHidden setup codec checks) created owner raw)).run
        (PqxdhDeploymentIdealKeys.detachX x, (x.backend.2.1, (x.backend.1, x.seeds))) = _
  have branch : (onPair lazyDummy (PqxdhDeploymentIdealKernel.finishStepC setup codec checks route t p
      (erasedHidden setup codec checks) created owner raw)).run
        (PqxdhDeploymentIdealKeys.detachX x, (x.backend.2.1, (x.backend.1, x.seeds))) =
      (onPair lazyDummy (PqxdhDeploymentIdealKernel.finishHiddenC setup codec p (erasedHidden setup codec checks) owner
        raw)).run (PqxdhDeploymentIdealKeys.detachX x, (x.backend.2.1, (x.backend.1, x.seeds))) := by
    rw [onPair_run, onPair_run]
    simp only [PqxdhDeploymentIdealKernel.finishStepC, StateT.run, ite_eq_left chosen']
  rw [branch, PqxdhDeploymentIdealErase.onPair_focus lazyDummy
    (PqxdhDeploymentIdealKernel.finishHiddenC setup codec p (erasedHidden setup codec checks) owner raw)
    (PqxdhDeploymentIdealSteps.finishChallenge setup codec (erasedHidden setup codec checks) p.challenge owner raw)
    (fun y : PqxdhDeploymentBackend.XState KemSK IdealCore 2 => (y.base.native, (none : Option Coord)))
    (fun y (b : Option Pqxdh.Bytes) (q : PqxdhRegistrationSchedule.State KemSK × Option Coord) =>
      (((b, q.2), PqxdhDeploymentIdealKernel.assembleF y owner q) :
        (Option Pqxdh.Bytes × Option Coord) × PqxdhDeploymentBackend.XState KemSK IdealCore 2)) shape]
  simp only []
  rw [challenge_native setup codec checks p.challenge owner raw (PqxdhDeploymentIdealKeys.detachX x).base.native before owned,
    owner_native setup codec checks p.challenge raw before control prekey oneTime kem phase]
  simp only [map_bind, Functor.map_map]
  refine bind_congr fun prepared => ?_
  cases prepared with
  | none => simp only [map_pure]; rfl
  | some pending => simp only [Functor.map_map]; rfl

end NativeFinish

/-! ### The World run of owner k's challenge finish -/

section FinishEffects
variable {KemSK : Type} {ι : Type} {baseSpec : OracleSpec ι} {Reader Response : Type}
  (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
  (checks : Checks) {count : ℕ}
open PqxdhDeploymentEnvironment (EnvState strip coins ctxEffects)
open PqxdhDeploymentEnvironmentJoin (merge uncount Good)
open PqxdhDeploymentEnvironmentReal (CountFree countFree_bind countFree_pure countFree_ownerEffect ctxAdmin
  effects_then_free coins_noAdmin withCache)
open PqxdhDeploymentIdealSlots (Coord SlotSpec)
open PqxdhDeploymentIdealSteps (IdealCore SplitBk establishedAt preparationCE)
open PqxdhDeploymentIdealKernel (MatCache SeedCache lazyDummy)
open PqxdhDeploymentIdealEnvStep (SlotState)
open PqxdhRegistrationJointKemSecondEntry (slotImpl)
open PqxdhRegistrationJointKemPostSkeleton (Pending embed message)
open PqxdhRecordLiftInterface (EnvEffects EffectKind effectKind)
open PqxdhDeploymentIdealParams (Target Params)
open PqxdhServerAuthNative (NativeState)

/-- A mapped count-free program is count-free. -/
theorem countFree_map {α β : Type} (f : α → β) (work : OracleComp (EnvEffects 2) α) (free : CountFree work) :
    CountFree (f <$> work) := by
  rw [map_eq_bind_pure_comp]
  exact countFree_bind free fun _ => countFree_pure _

/-- The commit of a finish is count-free. -/
theorem countFree_commitEnv (e : EnvState KemSK SplitBk) (owner : ℕ) (control : beaconcrypt_core.pqxdh.BeaconInitSent)
    (before : PqxdhRegistrationSchedule.Owner KemSK) (shared : NativeState KemSK)
    (staged : Option PqxdhBeaconPhase2Publication.Staged) :
    CountFree (commitEnv e owner control before shared staged) :=
  countFree_bind (countFree_ownerEffect _ _ _) fun _ => countFree_pure _

/-- The forwarded split hidden finish issues no administrative effect. -/
theorem finishSplitFwd_noAdmin (material : PqxdhDeploymentHiddenLayout.Material)
    (pending : PqxdhPhase2DhMetadata.Prepared Response) :
    (PqxdhDeploymentEnvironment.finishSplitFwd (n := 2) setup codec material pending).IsQueryBoundP
      (fun effect => effectKind effect = .administrative) 0 := by
  unfold PqxdhDeploymentEnvironment.finishSplitFwd
  exact simulateQ_noAdmin _ (fun query => by
    show OracleComp.IsQueryBoundP (((EnvEffects 2).query (.inr (.hash query.2)) : OracleComp (EnvEffects 2) _)) _ 0
    rw [isQueryBoundP_query_iff]
    intro same
    exact absurd same (by simp only [effectKind, reduceCtorEq, not_false_eq_true])) _

/-- CE-11a's split hidden finish is count-free. -/
theorem countFree_finishSplitEnv (material : PqxdhDeploymentHiddenLayout.Material)
    (j : PqxdhRecordLiftInterface.Slot 2) (owner : ℕ) (control : beaconcrypt_core.pqxdh.BeaconInitSent)
    (before : PqxdhRegistrationSchedule.Owner KemSK) (pending : PqxdhPhase2DhMetadata.Prepared Response) :
    CountFree (PqxdhDeploymentEnvironment.finishSplitEnv setup codec material j owner control before pending) := by
  unfold PqxdhDeploymentEnvironment.finishSplitEnv
  exact countFree_bind (countFree_noAdmin _ (finishSplitFwd_noAdmin setup codec material pending)) fun _ =>
    countFree_bind (countFree_hiddenOwnerEffect _ _ _ _) fun _ => countFree_pure _

/-- The grouped finish request in capability form is count-free. -/
theorem countFree_groupEnv (owner : ℕ) (control : beaconcrypt_core.pqxdh.BeaconInitSent)
    (before : PqxdhRegistrationSchedule.Owner KemSK) (e : EnvState KemSK SplitBk) (pending : Pending Response) :
    CountFree (groupEnv setup codec owner control before e pending) := by
  unfold groupEnv
  split
  · split
    · refine countFree_bind (countFree_noAdmin _ (coins_noAdmin _)) fun read => ?_
      split
      · exact countFree_map _ _ (countFree_finishSplitEnv setup codec _ _ _ _ _ _)
      · exact countFree_commitEnv _ _ _ _ _ _
    · exact countFree_commitEnv _ _ _ _ _ _
  · refine countFree_bind (countFree_noAdmin _ (coins_noAdmin _)) fun r => ?_
    split
    · exact countFree_commitEnv _ _ _ _ _ _
    · exact countFree_bind (countFree_noAdmin _ (knownFwd_noAdmin setup codec _)) fun _ => countFree_commitEnv _ _ _ _ _ _

/-- Owner k's challenge finish in capability form from an owner in the `initSent` phase, run by the World with its counts forgotten: the preparation's coins, then the World run of the commit or the grouped finish request from the counts-free World. -/
theorem finishChallenge_effects (p : Params KemSK count) (owner : ℕ) (raw : Pqxdh.Bytes) (e : EnvState KemSK SplitBk)
    (w : PqxdhRecordLiftWorld.State 2) (before : PqxdhRegistrationSchedule.Owner KemSK)
    (control : beaconcrypt_core.pqxdh.BeaconInitSent) (prekey oneTime : PqxdhJointGapDh.ScalarBytes)
    (kem : PqxdhKemIndCca.MlKem768PublicKey × KemSK) (owned : e.native.owners[owner]? = some before)
    (phase : before.beacon.phase = .initSent control prekey oneTime kem) :
    Prod.map id uncount <$> (simulateQ PqxdhRecordLiftWorld.effects
        ((finishChallengeEnv setup codec p owner raw).run e)).run w =
      simulateQ (preparationCE setup codec p.challenge) (PqxdhBeaconPhase2Shared.prepare control before.beacon.identity
        prekey oneTime kem raw) >>= fun prepared =>
        Prod.map id uncount <$> (simulateQ PqxdhRecordLiftWorld.effects (match prepared with
          | none => commitEnv e owner control before e.native.shared none
          | some pending => groupEnv setup codec owner control before e pending)).run (withCache w w.primitive.2) := by
  have program : (finishChallengeEnv setup codec p owner raw).run e =
      coins (simulateQ (preparationCE setup codec p.challenge) (PqxdhBeaconPhase2Shared.prepare control
        before.beacon.identity prekey oneTime kem raw)) >>= fun prepared =>
        match prepared with
        | none => commitEnv e owner control before e.native.shared none
        | some pending => groupEnv setup codec owner control before e pending := by
    change (match e.native.owners[owner]? with
      | some before => _
      | none => _) = _
    rw [owned]
    simp only [phase]
  rw [program, effects_then_free ctxAdmin _ (coins_noAdmin _) _ (fun prepared => by
    cases prepared with
    | none => exact countFree_commitEnv _ _ _ _ _ _
    | some pending => exact countFree_groupEnv setup codec _ _ _ _ _) w,
    PqxdhDeploymentEnvironment.ctxEffects_coins, bind_map_left]

/-- A read of coordinates in front of the lazy service with room or a hit: the slot of the coordinates is allocated and the value is a material joined with the dummy seed. -/
theorem lazyRead_support (coords : Coord) (state : SlotState) (room : state.1.2 < 2) :
    ∀ read ∈ support ((slotImpl lazyDummy (.inr coords)).run state),
      (∃ j, read.2.1.1 coords = some j) ∧ (PqxdhDeploymentHiddenLayout.splitOutput read.1).2 =
        PqxdhDeploymentHiddenSplit.dummySeed := by
  intro read member
  rcases found : state.1.1 coords with _ | j
  · rw [PqxdhRegistrationJointKemSecondEntry.slot_none _ _ _ found room, PqxdhDeploymentIdealDefer.lazyDummy_run,
      Functor.map_map, support_map] at member
    obtain ⟨drawn, _, rfl⟩ := member
    refine ⟨⟨⟨state.1.2, room⟩, by simp only [Function.update_self]⟩, ?_⟩
    simp only [PqxdhDeploymentHiddenLayout.split_join]
  · rw [PqxdhRegistrationJointKemSecondEntry.slot_some _ _ _ j found, PqxdhDeploymentIdealDefer.lazyDummy_run,
      Functor.map_map, support_map] at member
    obtain ⟨drawn, _, rfl⟩ := member
    exact ⟨⟨j, found⟩, by simp only [PqxdhDeploymentHiddenLayout.split_join]⟩

/-- Whether the owner set at an index is established. -/
theorem establishedAt_set (owners : List (PqxdhRegistrationSchedule.Owner KemSK)) (index : ℕ)
    (owner : PqxdhRegistrationSchedule.Owner KemSK) (below : index < owners.length) :
    establishedAt (owners.set index owner) index = match owner.beacon.phase with
      | .established _ _ _ => true
      | _ => false := by
  simp only [establishedAt, List.getElem?_set_self below]
  rcases owner.beacon.phase <;> rfl

/-- Stripping does not see the kernel of an established owner. -/
theorem strip_setOwnerKernel (shared : NativeState KemSK) (owners : List (PqxdhRegistrationSchedule.Owner KemSK))
    (index : ℕ) (owner : PqxdhRegistrationSchedule.Owner KemSK)
    (first second : beaconcrypt_core.ratchet.concrete.ConcreteRatchetKernel) :
    strip (⟨shared, owners.set index (PqxdhDeploymentIdealKernel.setOwnerKernel owner first)⟩ :
        PqxdhRegistrationSchedule.State KemSK) =
      strip ⟨shared, owners.set index (PqxdhDeploymentIdealKernel.setOwnerKernel owner second)⟩ := by
  have key : PqxdhDeploymentEnvironment.stripOwner (PqxdhDeploymentIdealKernel.setOwnerKernel owner first) =
      PqxdhDeploymentEnvironment.stripOwner (PqxdhDeploymentIdealKernel.setOwnerKernel owner second) := by
    unfold PqxdhDeploymentIdealKernel.setOwnerKernel PqxdhDeploymentEnvironment.stripOwner
    rcases phase : owner.beacon.phase <;> simp only [phase]
  simp only [strip, List.map_set, key]

/-- A hidden owner that ends aborted advances its World phase. -/
theorem hiddenOwnerEffect_abort (j : PqxdhRecordLiftInterface.Slot 2) (index : ℕ)
    (before after : PqxdhRegistrationSchedule.Owner KemSK)
    (initSent : PqxdhDeploymentEnvironment.inactiveTag before.beacon.phase = some .initSent)
    (aborted : PqxdhDeploymentEnvironment.inactiveTag after.beacon.phase = some .aborted) :
    PqxdhDeploymentEnvironment.hiddenOwnerEffect (n := 2) j index before after =
      PqxdhDeploymentEnvironment.issue (.advanceOwner index .aborted) := by
  unfold PqxdhDeploymentEnvironment.hiddenOwnerEffect
  cases beforePhase : before.beacon.phase <;>
    simp only [beforePhase, PqxdhDeploymentEnvironment.inactiveTag, reduceCtorEq, Option.some.injEq] at initSent
  cases afterPhase : after.beacon.phase <;>
    simp only [afterPhase, PqxdhDeploymentEnvironment.inactiveTag, reduceCtorEq, Option.some.injEq] at aborted
  rfl

/-- A hidden owner that ends established is installed at its slot with its shell. -/
theorem hiddenOwnerEffect_establish (j : PqxdhRecordLiftInterface.Slot 2) (index : ℕ)
    (before after : PqxdhRegistrationSchedule.Owner KemSK)
    (initSent : PqxdhDeploymentEnvironment.inactiveTag before.beacon.phase = some .initSent)
    (control : beaconcrypt_core.pqxdh.BeaconEstablished) (associatedData : Std.Array Std.U8 281#usize)
    (kernel : beaconcrypt_core.ratchet.concrete.ConcreteRatchetKernel)
    (established : after.beacon.phase = .established control associatedData kernel) :
    PqxdhDeploymentEnvironment.hiddenOwnerEffect (n := 2) j index before after =
      PqxdhDeploymentEnvironment.issue (.installBeacon index ⟨after.beacon.identityKeyId, control, associatedData⟩
        (.hidden j)) := by
  unfold PqxdhDeploymentEnvironment.hiddenOwnerEffect
  cases beforePhase : before.beacon.phase <;>
    simp only [beforePhase, PqxdhDeploymentEnvironment.inactiveTag, reduceCtorEq, Option.some.injEq] at initSent
  rw [established]

/-- The final split form's hidden Beacon install when owner k is not established: nothing. -/
theorem beaconInstall_closed (owner : ℕ) (reply : Option Pqxdh.Bytes) (coords : Option Coord)
    (x : PqxdhDeploymentBackend.XState KemSK SplitBk 2)
    (closed : establishedAt x.base.native.owners owner = false) :
    PqxdhDeploymentIdealDefer.beaconInstall owner ((reply, coords), x) = pure ((reply, coords), x) := by
  unfold PqxdhDeploymentIdealDefer.beaconInstall PqxdhDeploymentIdealDefer.xInstall
  rcases coords with _ | c
  · rfl
  · simp only []
    rcases x.backend.2.1.1 c with _ | j
    · rfl
    · have closed' : establishedAt (PqxdhDeploymentIdealKeys.detachX x).base.native.owners owner = false := closed
      simp only [closed', Bool.false_eq_true, ↓reduceIte]

/-- The final split form's hidden Beacon install when owner k is established after a hidden read at an allocated slot: the lazy seed of the slot and the World's Beacon kernel of it on owner k. -/
theorem beaconInstall_open (owner : ℕ) (reply : Option Pqxdh.Bytes) (coords : Coord)
    (x : PqxdhDeploymentBackend.XState KemSK SplitBk 2) (j : PqxdhRecordLiftInterface.Slot 2)
    (allocated : x.backend.2.1.1 coords = some j) (opened : establishedAt x.base.native.owners owner = true) :
    PqxdhDeploymentIdealDefer.beaconInstall owner ((reply, some coords), x) =
      (fun r => ((reply, some coords), { x with
        base := { x.base with native := { x.base.native with
          owners := x.base.native.owners.modify owner (PqxdhDeploymentIdealKernel.setKernelAt r.1) } }
        seeds := r.2 })) <$> ((PqxdhRecordLiftWorld.SeedSpec 2).randomOracle j).run x.seeds := by
  unfold PqxdhDeploymentIdealDefer.beaconInstall PqxdhDeploymentIdealDefer.xInstall
  simp only [allocated]
  have opened' : establishedAt (PqxdhDeploymentIdealKeys.detachX x).base.native.owners owner = true := opened
  simp only [opened', ↓reduceIte]
  change _ <$> ((fun r => (r.1, PqxdhDeploymentBackend.seedLens.set x r.2)) <$>
    ((PqxdhRecordLiftWorld.SeedSpec 2).randomOracle j).run x.seeds) = _
  rw [Functor.map_map]
  rfl

/-- Stripping an owner forgets a kernel just set. -/
theorem stripOwner_setOwnerKernel (owner : PqxdhRegistrationSchedule.Owner KemSK)
    (kernel : beaconcrypt_core.ratchet.concrete.ConcreteRatchetKernel) :
    PqxdhDeploymentEnvironment.stripOwner (PqxdhDeploymentIdealKernel.setOwnerKernel owner kernel) =
      PqxdhDeploymentEnvironment.stripOwner owner := by
  unfold PqxdhDeploymentIdealKernel.setOwnerKernel PqxdhDeploymentEnvironment.stripOwner
  rcases phase : owner.beacon.phase <;> simp only [phase]

/-- The native private root of a known decapsulation result touches only the Extract family. -/
theorem markedRoot_game (hmac : PqxdhSecretInputKdf.HmacSha512) (candidate : PqxdhKemIndCca.MlKemSharedSecret)
    (secrets : PqxdhBeaconPhase2Shared.Secrets PqxdhPhase2DecapsulationRouting.Shared)
    (s : NativeState KemSK) (game : GameState KemSK) :
    (PqxdhRegistrationJointBeaconOpaqueFinish.markedRoot (KemSK := KemSK) hmac candidate secrets).run (s.1, game) =
      (fun r => (r.1, (r.2.1, game))) <$>
        (PqxdhRegistrationJointBeaconOpaqueFinish.markedRoot (KemSK := KemSK) hmac candidate secrets).run s := by
  rcases s with ⟨family, other⟩
  unfold PqxdhRegistrationJointBeaconOpaqueFinish.markedRoot
  split
  · simp only [PqxdhServerAuthNative.sourceRoot, StateT.run, Functor.map_map]
  · simp only [StateT.run_pure, map_pure]

open PqxdhDeploymentEnvironmentReal (fill_some fill_inactive good_matched snapshotAt_fill serverGame Finished
  commit_shape merge_uncount) in
/-- The commit of a finish in capability form against the final split form's commit without a hidden read: from an admissible joint state at an owner in the `initSent` phase, a shared state with the environment's game state and a CTX cache, the reassembled World run of the commit is the split form's state after the commit, whose hidden install does nothing. -/
theorem commit_case (created : PqxdhLiveServerConstruction.Created Unit) (owner : ℕ) (e : EnvState KemSK SplitBk)
    (w : PqxdhRecordLiftWorld.State 2) (good : Good created e w) (world : PqxdhRecordLiftWorld.Server)
    (found : w.server = some world) (before : PqxdhRegistrationSchedule.Owner KemSK)
    (control : beaconcrypt_core.pqxdh.BeaconInitSent) (prekey oneTime : PqxdhJointGapDh.ScalarBytes)
    (kem : PqxdhKemIndCca.MlKem768PublicKey × KemSK) (owned : e.native.owners[owner]? = some before)
    (phase : before.beacon.phase = .initSent control prekey oneTime kem) (shared : NativeState KemSK)
    (game : shared.2 = e.native.shared.2) (cache : CtxRomAuth.CtxRO.QueryCache)
    (staged : Option PqxdhBeaconPhase2Publication.Staged) :
    (fun result => (result.1.1, merge result.1.2 result.2)) <$> (Prod.map id uncount <$>
        (simulateQ PqxdhRecordLiftWorld.effects (commitEnv e owner control before shared staged)).run (withCache w cache)) =
      (fun r => (r.1.1, r.2)) <$> PqxdhDeploymentIdealDefer.beaconInstall owner
        (((PqxdhBeaconPhase2Publication.finish control before staged).1, none),
          finishedX (merge e w) owner (shared.1, serverGame world.records.server e.native.shared.2.server.identityKeyId
            { shared.2 with ctx := cache }) (PqxdhBeaconPhase2Publication.finish control before staged).2 none
            ((merge e w).backend.2.1, ((merge e w).backend.1, (merge e w).seeds))) := by
  have inactive : ¬ RawCtxBeaconLifecycle.Established before.beacon.phase := by
    rw [phase]
    simp only [RawCtxBeaconLifecycle.Established, not_false_eq_true]
  have initSent : PqxdhDeploymentEnvironment.inactiveTag before.beacon.phase = some .initSent := by rw [phase]; rfl
  obtain ⟨w', run, merged, _⟩ := PqxdhDeploymentIdealEnvReal.finish_outcome created owner e w good world found before
    owned inactive (PqxdhBeaconPhase2Publication.finish control before staged).1
    (PqxdhBeaconPhase2Publication.finish control before staged).2 shared cache
    (Or.inr ⟨initSent, commit_shape control before staged⟩) game
  change (fun result => (result.1.1, merge result.1.2 result.2)) <$> (Prod.map id uncount <$>
    (simulateQ PqxdhRecordLiftWorld.effects (PqxdhDeploymentEnvironment.ownerEffect owner before
      (PqxdhBeaconPhase2Publication.finish control before staged).2 >>= fun _ =>
        pure ((PqxdhBeaconPhase2Publication.finish control before staged).1,
          { PqxdhDeploymentEnvironmentReal.snapFinish e owner with native := strip ⟨shared, e.native.owners.set owner
            (PqxdhBeaconPhase2Publication.finish control before staged).2⟩ }))).run (withCache w cache)) = _
  rw [run, map_pure]
  change pure (_, merge _ (uncount w')) = pure _
  rw [merge_uncount, merged]
  congr 2
  simp only [finishedX, PqxdhDeploymentEnvironmentReal.finishedState, Option.none_or, ite_self,
    PqxdhDeploymentEnvironmentReal.snapFinish]
  rw [show (merge e w).base.native = PqxdhDeploymentEnvironmentJoin.fill w e.native from rfl, snapshotAt_fill]
  rfl

open PqxdhDeploymentEnvironmentReal (commit_shape ownerEffect_abort ownerEffect_establish effects_issue_then effects_advance
  effects_installBeacon fillOwner_inactive fillOwner_self) in
/-- Every outcome of the commit of a finish in capability form, with the World's counts forgotten, from a World whose owner is in the `initSent` phase: the owner's World phase is set consistently with the committed owner (aborted, or established with its known kernel), and nothing else in the World changes. -/
theorem commit_outcome (e : EnvState KemSK SplitBk) (owner : ℕ) (control : beaconcrypt_core.pqxdh.BeaconInitSent)
    (before : PqxdhRegistrationSchedule.Owner KemSK) (shared : NativeState KemSK)
    (staged : Option PqxdhBeaconPhase2Publication.Staged) (w : PqxdhRecordLiftWorld.State 2)
    (cache : CtxRomAuth.CtxRO.QueryCache)
    (initSent : PqxdhDeploymentEnvironment.inactiveTag before.beacon.phase = some .initSent)
    (worldPhase : w.owners[owner]? = some (.inactive .initSent)) :
    ∀ result ∈ support (Prod.map id uncount <$> (simulateQ PqxdhRecordLiftWorld.effects
        (commitEnv e owner control before shared staged)).run (withCache w cache)),
      ∃ phase, PqxdhDeploymentEnvironmentJoin.stripPhase phase = PqxdhDeploymentEnvironmentJoin.stripPhase
          (PqxdhRecordLiftBeacon.projectPhase (PqxdhBeaconPhase2Publication.finish control before staged).2.beacon) ∧
        PqxdhDeploymentEnvironmentJoin.fillOwner (some phase) (PqxdhBeaconPhase2Publication.finish control before staged).2 =
          (PqxdhBeaconPhase2Publication.finish control before staged).2 ∧
        result = (((PqxdhBeaconPhase2Publication.finish control before staged).1, finishedEnv e owner shared
          (PqxdhBeaconPhase2Publication.finish control before staged).2 e.backend),
            uncount { withCache w cache with owners := w.owners.set owner phase }) := by
  intro result supported
  rcases commit_shape control before staged with aborted | ⟨control', associatedData, kernel, established⟩
  · have abortedPhase : PqxdhRecordLiftBeacon.projectPhase (PqxdhBeaconPhase2Publication.finish control before
        staged).2.beacon = .inactive .aborted := by
      cases afterPhase : (PqxdhBeaconPhase2Publication.finish control before staged).2.beacon.phase <;>
        simp only [afterPhase, PqxdhDeploymentEnvironment.inactiveTag, reduceCtorEq, Option.some.injEq] at aborted
      simp only [PqxdhRecordLiftBeacon.projectPhase, afterPhase]
    unfold commitEnv at supported
    rw [ownerEffect_abort owner before _ initSent aborted, effects_issue_then,
      effects_advance owner .initSent .aborted (withCache w cache) worldPhase trivial, map_pure, support_pure,
      Set.mem_singleton_iff] at supported
    exact ⟨.inactive .aborted, by rw [abortedPhase], fillOwner_inactive .aborted _, supported⟩
  · unfold commitEnv at supported
    rw [ownerEffect_establish owner before _ initSent control' associatedData kernel established, effects_issue_then,
      effects_installBeacon owner _ kernel (withCache w cache) worldPhase, map_pure, support_pure,
      Set.mem_singleton_iff] at supported
    refine ⟨.established ⟨(PqxdhBeaconPhase2Publication.finish control before staged).2.beacon.identityKeyId, control',
      associatedData⟩ kernel, ?_, fillOwner_self _ control' associatedData kernel established, supported⟩
    simp only [PqxdhRecordLiftBeacon.projectPhase, established]

open PqxdhDeploymentEnvironmentReal (commit_shape effects_issue_then effects_advance) in
/-- Every outcome of owner k's hidden finish in capability form at an allocated slot, with the World's counts forgotten, from a World whose owner is in the `initSent` phase and whose Beacon marker of the slot is unused: the owner aborted (its World phase advanced, nothing else changed in the World), or established with the World's Beacon kernel of the slot's seed, which the seed table now holds, the slot's Beacon marker set. -/
theorem hiddenFinish_outcome (e : EnvState KemSK SplitBk) (owner : ℕ) (control : beaconcrypt_core.pqxdh.BeaconInitSent)
    (before : PqxdhRegistrationSchedule.Owner KemSK) (pending : Pending Response) (coords : Coord)
    (read : PqxdhServerAuthKeySchedule.Output × SlotState) (j : PqxdhRecordLiftInterface.Slot 2)
    (w : PqxdhRecordLiftWorld.State 2) (cache : CtxRomAuth.CtxRO.QueryCache)
    (initSent : PqxdhDeploymentEnvironment.inactiveTag before.beacon.phase = some .initSent)
    (worldPhase : w.owners[owner]? = some (.inactive .initSent)) (unused : w.used j .beacon = false) :
    ∀ result ∈ support (Prod.map id uncount <$> (simulateQ PqxdhRecordLiftWorld.effects
        ((fun committed => (committed.1, finishedEnv e owner e.native.shared committed.2
          (hiddenBackend e owner committed.2 coords read.2))) <$>
          PqxdhDeploymentEnvironment.finishSplitEnv setup codec (PqxdhDeploymentHiddenLayout.splitOutput read.1).1 j
            owner control before (embed pending))).run (withCache w cache)),
      ∃ staged cache',
        (PqxdhDeploymentEnvironment.inactiveTag (PqxdhBeaconPhase2Publication.finish control before staged).2.beacon.phase =
            some .aborted ∧
          result = (((PqxdhBeaconPhase2Publication.finish control before staged).1, finishedEnv e owner e.native.shared
            (PqxdhBeaconPhase2Publication.finish control before staged).2 (hiddenBackend e owner
              (PqxdhBeaconPhase2Publication.finish control before staged).2 coords read.2)),
            uncount { withCache w cache' with owners := w.owners.set owner (.inactive .aborted) })) ∨
        (∃ control' associatedData kernel seed table,
          (PqxdhBeaconPhase2Publication.finish control before staged).2.beacon.phase =
            .established control' associatedData kernel ∧ table.1 j = some seed ∧ w.seeds.1 ≤ table.1 ∧
          result = (((PqxdhBeaconPhase2Publication.finish control before staged).1, finishedEnv e owner e.native.shared
            (PqxdhBeaconPhase2Publication.finish control before staged).2 (hiddenBackend e owner
              (PqxdhBeaconPhase2Publication.finish control before staged).2 coords read.2)),
            uncount { withCache w cache' with
              seeds := table
              used := Function.update w.used j (Function.update (w.used j) .beacon true)
              owners := w.owners.set owner (.established ⟨(PqxdhBeaconPhase2Publication.finish control before
                staged).2.beacon.identityKeyId, control', associatedData⟩ (PqxdhRecordLiftWorld.kernel .beacon seed)) })) := by
  intro result supported
  have program : (fun committed => (committed.1, finishedEnv e owner e.native.shared committed.2
      (hiddenBackend e owner committed.2 coords read.2))) <$>
      PqxdhDeploymentEnvironment.finishSplitEnv setup codec (PqxdhDeploymentHiddenLayout.splitOutput read.1).1 j
        owner control before (embed pending) =
      PqxdhDeploymentEnvironment.finishSplitFwd setup codec (PqxdhDeploymentHiddenLayout.splitOutput read.1).1
        (embed pending) >>= fun staged =>
        PqxdhDeploymentEnvironment.hiddenOwnerEffect j owner before
          (PqxdhBeaconPhase2Publication.finish control before staged).2 >>= fun _ =>
          pure ((PqxdhBeaconPhase2Publication.finish control before staged).1, finishedEnv e owner e.native.shared
            (PqxdhBeaconPhase2Publication.finish control before staged).2
            (hiddenBackend e owner (PqxdhBeaconPhase2Publication.finish control before staged).2 coords read.2)) := by
    simp only [PqxdhDeploymentEnvironment.finishSplitEnv, map_bind, map_pure]
  rw [program, PqxdhDeploymentEnvironmentReal.effects_then_free PqxdhDeploymentEnvironmentReal.ctxAdmin _
    (finishSplitFwd_noAdmin setup codec _ _) _ (fun staged => countFree_bind (countFree_hiddenOwnerEffect _ _ _ _)
      fun _ => countFree_pure _) _, mem_support_bind_iff] at supported
  obtain ⟨⟨staged, cache'⟩, _, final⟩ := supported
  refine ⟨staged, cache', ?_⟩
  rw [show withCache (withCache w cache) cache' = withCache w cache' from rfl] at final
  rcases commit_shape control before staged with aborted | ⟨control', associatedData, kernel, established⟩
  · rw [hiddenOwnerEffect_abort j owner before _ initSent aborted, effects_issue_then,
      effects_advance owner .initSent .aborted (withCache w cache') worldPhase trivial, map_pure, support_pure,
      Set.mem_singleton_iff] at final
    exact Or.inl ⟨aborted, final⟩
  · rw [hiddenOwnerEffect_establish j owner before _ initSent control' associatedData kernel established,
      effects_issue_then, effects_hiddenBeacon owner _ j (withCache w cache') worldPhase unused, Functor.map_map,
      support_map] at final
    obtain ⟨⟨seed, table⟩, inTable, rfl⟩ := final
    have facts := PqxdhRecordLiftLazyTable.step_facts j w.seeds (seed, table) inTable
    exact Or.inr ⟨control', associatedData, kernel, seed, table, established, facts.1, facts.2.1, rfl⟩

/-- Every outcome of owner k's challenge finish in capability form from an owner in the `initSent` phase, with the World's counts forgotten, from a World whose owner is in the `initSent` phase and that holds no Beacon marker: a commit without hidden read (on a shared state with the environment's game state, the backend unchanged, the owner's World phase set consistently and nothing else in the World changed), or the hidden finish after a hidden read at an allocated slot (`hiddenFinish_outcome`). -/
theorem finishChallenge_outcome (p : Params KemSK count) (owner : ℕ) (raw : Pqxdh.Bytes) (e : EnvState KemSK SplitBk)
    (w : PqxdhRecordLiftWorld.State 2) (before : PqxdhRegistrationSchedule.Owner KemSK)
    (control : beaconcrypt_core.pqxdh.BeaconInitSent) (prekey oneTime : PqxdhJointGapDh.ScalarBytes)
    (kem : PqxdhKemIndCca.MlKem768PublicKey × KemSK) (owned : e.native.owners[owner]? = some before)
    (phase : before.beacon.phase = .initSent control prekey oneTime kem)
    (worldPhase : w.owners[owner]? = some (.inactive .initSent)) :
    ∀ result ∈ support (Prod.map id uncount <$> (simulateQ PqxdhRecordLiftWorld.effects
        ((finishChallengeEnv setup codec p owner raw).run e)).run w),
      (∃ shared staged cache phase, shared.2 = e.native.shared.2 ∧
        PqxdhDeploymentEnvironmentJoin.stripPhase phase = PqxdhDeploymentEnvironmentJoin.stripPhase
          (PqxdhRecordLiftBeacon.projectPhase (PqxdhBeaconPhase2Publication.finish control before staged).2.beacon) ∧
        PqxdhDeploymentEnvironmentJoin.fillOwner (some phase) (PqxdhBeaconPhase2Publication.finish control before staged).2 =
          (PqxdhBeaconPhase2Publication.finish control before staged).2 ∧
        result = (((PqxdhBeaconPhase2Publication.finish control before staged).1, finishedEnv e owner shared
          (PqxdhBeaconPhase2Publication.finish control before staged).2 e.backend),
            uncount { withCache w cache with owners := w.owners.set owner phase })) ∨
      (∃ (pending : Pending Response) (coords : Coord) (read : PqxdhServerAuthKeySchedule.Output × SlotState)
          (j : PqxdhRecordLiftInterface.Slot 2),
        read ∈ support ((slotImpl lazyDummy (.inr coords)).run (e.backend.2.1, (e.backend.1, ∅))) ∧
        read.2.1.1 coords = some j ∧
        result ∈ support (Prod.map id uncount <$> (simulateQ PqxdhRecordLiftWorld.effects
          ((fun committed => (committed.1, finishedEnv e owner e.native.shared committed.2
            (hiddenBackend e owner committed.2 coords read.2))) <$>
            PqxdhDeploymentEnvironment.finishSplitEnv setup codec (PqxdhDeploymentHiddenLayout.splitOutput read.1).1 j
              owner control before (embed pending))).run (withCache w w.primitive.2))) := by
  have initSent : PqxdhDeploymentEnvironment.inactiveTag before.beacon.phase = some .initSent := by rw [phase]; rfl
  intro result supported
  rw [finishChallenge_effects setup codec p owner raw e w before control prekey oneTime kem owned phase,
    mem_support_bind_iff] at supported
  obtain ⟨prepared, _, supported⟩ := supported
  rcases prepared with _ | pending
  · exact Or.inl ⟨e.native.shared, none, w.primitive.2, commit_outcome e owner control before e.native.shared none w
      w.primitive.2 initSent worldPhase result supported |>.choose, rfl,
      (commit_outcome e owner control before e.native.shared none w w.primitive.2 initSent worldPhase result
        supported).choose_spec⟩
  · simp only [] at supported
    unfold groupEnv at supported
    rcases sharedEq : pending.root.shared with _ | secret
    · rw [sharedEq] at supported
      simp only [] at supported
      split at supported
      · rw [PqxdhDeploymentEnvironmentReal.effects_then_free PqxdhDeploymentEnvironmentReal.ctxAdmin _ (coins_noAdmin _) _
          (fun read => by
            split
            · exact countFree_map _ _ (countFree_finishSplitEnv setup codec _ _ _ _ _ _)
            · exact countFree_commitEnv _ _ _ _ _ _) _,
          PqxdhDeploymentEnvironment.ctxEffects_coins, bind_map_left, mem_support_bind_iff] at supported
        obtain ⟨read, member, final⟩ := supported
        rw [show withCache (withCache w w.primitive.2) (withCache w w.primitive.2).primitive.2 =
          withCache w w.primitive.2 from rfl] at final
        split at final
        · rename_i j allocated
          exact Or.inr ⟨pending, _, read, j, member, allocated, final⟩
        · exact Or.inl ⟨e.native.shared, none, w.primitive.2, (commit_outcome e owner control before e.native.shared none
            w w.primitive.2 initSent worldPhase result final).choose, rfl,
            (commit_outcome e owner control before e.native.shared none w w.primitive.2 initSent worldPhase result
              final).choose_spec⟩
      · exact Or.inl ⟨e.native.shared, none, w.primitive.2, (commit_outcome e owner control before e.native.shared none
          w w.primitive.2 initSent worldPhase result supported).choose, rfl,
          (commit_outcome e owner control before e.native.shared none w w.primitive.2 initSent worldPhase result
            supported).choose_spec⟩
    · rw [sharedEq] at supported
      simp only [] at supported
      have program : (coins ((PqxdhRegistrationJointBeaconOpaqueFinish.markedRoot setup.hmac
          (List.Vector.replicate 32 0) pending.root).run e.native.shared) >>= fun r =>
          match r.1 with
          | none => commitEnv e owner control before r.2 none
          | some root => simulateQ (knownFwd setup codec) (PqxdhBeaconPhase2Shared.afterRoot codec.frameRead pending
              root) >>= fun staged => commitEnv e owner control before r.2 staged) =
          (coins ((PqxdhRegistrationJointBeaconOpaqueFinish.markedRoot setup.hmac (List.Vector.replicate 32 0)
            pending.root).run e.native.shared) >>= fun r =>
            match r.1 with
            | none => pure (r.2, none)
            | some root => (fun staged => (r.2, staged)) <$> simulateQ (knownFwd setup codec)
                (PqxdhBeaconPhase2Shared.afterRoot codec.frameRead pending root)) >>= fun v =>
            commitEnv e owner control before v.1 v.2 := by
        rw [bind_assoc]
        refine bind_congr fun r => ?_
        rcases r with ⟨_ | root, st⟩
        · simp only [pure_bind]
        · simp only [bind_map_left]
      rw [program, PqxdhDeploymentEnvironmentReal.effects_then_free PqxdhDeploymentEnvironmentReal.ctxAdmin _ ?noAdmin _
        (fun v => countFree_commitEnv _ _ _ _ _ _) _, mem_support_bind_iff] at supported
      · obtain ⟨⟨⟨shared, staged⟩, cache⟩, member, final⟩ := supported
        rw [show withCache (withCache w w.primitive.2) cache = withCache w cache from rfl] at final
        have game : shared.2 = e.native.shared.2 := by
          rw [simulateQ_bind, StateT.run_bind, PqxdhDeploymentEnvironment.ctxEffects_coins, bind_map_left,
            mem_support_bind_iff] at member
          obtain ⟨r, rooted, rest⟩ := member
          have same := markedRoot_game (KemSK := KemSK) setup.hmac (List.Vector.replicate 32 0) pending.root
            e.native.shared e.native.shared.2
          rw [show ((e.native.shared.1, e.native.shared.2) : NativeState KemSK) = e.native.shared from rfl] at same
          rw [same, support_map] at rooted
          obtain ⟨r', _, rfl⟩ := rooted
          rcases r' with ⟨_ | root, st⟩
          · simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at rest
            rw [rest.1.1]
          · simp only [simulateQ_map, StateT.run_map, support_map] at rest
            obtain ⟨_, _, equal⟩ := rest
            exact (congrArg (fun z => z.1.1.2) equal).symm
        exact Or.inl ⟨shared, staged, cache, (commit_outcome e owner control before shared staged w cache initSent
          worldPhase result final).choose, game,
          (commit_outcome e owner control before shared staged w cache initSent worldPhase result final).choose_spec⟩
      · rw [show (0 : ℕ) = 0 + 0 from rfl]
        refine isQueryBoundP_bind (coins_noAdmin _) fun r _ => ?_
        rcases r with ⟨_ | root, st⟩
        · exact isQueryBoundP_pure _ _ _
        · exact (isQueryBoundP_map_iff _ _ _).mpr (knownFwd_noAdmin setup codec _)

open PqxdhDeploymentEnvironmentReal (law_uncount fill_some fill_inactive good_matched snapshotAt_fill) in
/-- Owner k's challenge finish in capability form splits the final split form's challenge finish, from an admissible joint state whose selected accept was active, whose owner k is in the `initSent` phase, whose allocator has room and whose World holds no Beacon marker: the reassembled law is the split form's, exactly. -/
theorem finishChallenge_law (t : Target count) (p : Params KemSK count) (created : PqxdhLiveServerConstruction.Created Unit)
    (owner : ℕ) (raw : Pqxdh.Bytes) (e : EnvState KemSK SplitBk) (w : PqxdhRecordLiftWorld.State 2)
    (good : Good created e w)
    (chosen : e.backend.2.2.active = true ∧ owner = t.kem.val ∧
      PqxdhDeploymentIdealSteps.initSentAt e.native.owners owner = true)
    (room : e.backend.2.1.2 < 2) (unused : ∀ j, w.used j .beacon = false) :
    (fun result => (result.1.1, merge result.1.2 result.2)) <$> (simulateQ PqxdhRecordLiftWorld.effects
        ((finishChallengeEnv setup codec p owner raw).run e)).run w =
      (PqxdhDeploymentIdealDefer.idealSplit setup codec route checks t p created ⟨.finish owner raw, trivial⟩).run
        (merge e w) := by
  obtain ⟨world, found, sender, identity, peersRaw⟩ := good.server
  obtain ⟨activeEq, kemEq, initSent⟩ := chosen
  rcases owned : e.native.owners[owner]? with _ | before
  · simp only [PqxdhDeploymentIdealSteps.initSentAt, owned, Bool.false_eq_true] at initSent
  rcases phase : before.beacon.phase with _ | _ | ⟨control, prekey, oneTime, kem⟩ | _ | _
  all_goals try (simp only [PqxdhDeploymentIdealSteps.initSentAt, owned, phase, Bool.false_eq_true] at initSent)
  have inactive : ¬ RawCtxBeaconLifecycle.Established before.beacon.phase := by
    rw [phase]
    simp only [RawCtxBeaconLifecycle.Established, not_false_eq_true]
  obtain ⟨tag, worldPhase, projected, filledOwner⟩ := fill_inactive w _ (good_matched created e w good) owner before
    owned inactive
  have ownedM : (merge e w).base.native.owners[owner]? = some before := by
    change (PqxdhDeploymentEnvironmentJoin.fill w e.native).owners[owner]? = some before
    simp only [PqxdhDeploymentEnvironmentJoin.fill, List.getElem?_mapIdx, owned, Option.map_some, filledOwner]
  have chosenM : (merge e w).backend.2.2.active = true ∧ owner = t.kem.val ∧
      PqxdhDeploymentIdealSteps.initSentAt (merge e w).base.native.owners owner = true := by
    refine ⟨activeEq, kemEq, ?_⟩
    change PqxdhDeploymentIdealSteps.initSentAt (PqxdhDeploymentEnvironmentJoin.fill w e.native).owners owner = true
    rw [PqxdhDeploymentIdealEnvStep.initSentAt_fill]
    simp only [PqxdhDeploymentIdealSteps.initSentAt, owned, phase]
  change _ = (fun r => (r.1.1, r.2)) <$> ((PqxdhDeploymentIdealKernel.slotRunX lazyDummy
    (PqxdhDeploymentIdealKernel.finishStepC setup codec checks route t p
      (PqxdhDeploymentIdealSteps.erasedHidden setup codec checks) created owner raw)).run (merge e w) >>=
        PqxdhDeploymentIdealDefer.beaconInstall owner)
  rw [slotRun_finish_hidden setup codec route checks t p created owner raw (merge e w) before control prekey oneTime kem
    chosenM ownedM phase, law_uncount, finishChallenge_effects setup codec p owner raw e w before control prekey oneTime kem
      owned phase]
  simp only [map_bind, bind_assoc]
  refine bind_congr fun prepared => ?_
  have sharedM : (merge e w).base.native.shared = (e.native.shared.1, PqxdhDeploymentEnvironmentReal.serverGame
      world.records.server e.native.shared.2.server.identityKeyId { e.native.shared.2 with ctx := w.primitive.2 }) := by
    rw [show (merge e w).base.native = PqxdhDeploymentEnvironmentJoin.fill w e.native from rfl, fill_some w world found]
    rfl
  cases prepared with
  | none =>
      simp only [pure_bind]
      rw [sharedM]
      exact commit_case created owner e w good world found before control prekey oneTime kem owned phase
        e.native.shared rfl w.primitive.2 none
  | some pending =>
      simp only []
      unfold groupEnv groupNative
      rcases sharedEq : pending.root.shared with _ | secret
      · simp only []
        split
        · rename_i nonZero
          set coords' := message pending.root.dh1 pending.root.dh2 pending.root.dh3 pending.root.dh4 with coordsEq
          rw [PqxdhDeploymentEnvironmentReal.effects_then_free PqxdhDeploymentEnvironmentReal.ctxAdmin _ (coins_noAdmin _) _
            (fun read => by
              split
              · exact countFree_map _ _ (countFree_finishSplitEnv setup codec _ _ _ _ _ _)
              · exact countFree_commitEnv _ _ _ _ _ _) _,
            PqxdhDeploymentEnvironment.ctxEffects_coins, bind_map_left, map_bind]
          rw [show ((merge e w).backend.2.1, ((merge e w).backend.1, (merge e w).seeds)) =
              PqxdhDeploymentIdealDefer.pairSeeds.set (e.backend.2.1, (e.backend.1, ∅)) w.seeds.1 from rfl,
            PqxdhDeploymentIdealDefer.slotImpl_lazy_frame _ _ w.seeds.1]
          simp only [map_bind, bind_map_left, bind_assoc]
          apply OracleComp.bind_congr_of_forall_mem_support
          intro read member
          obtain ⟨⟨j, allocated⟩, dummy⟩ := lazyRead_support coords' _ room read member
          simp only [allocated]
          have program : (fun committed => (committed.1, finishedEnv e owner e.native.shared committed.2
              (hiddenBackend e owner committed.2 coords' read.2))) <$>
              PqxdhDeploymentEnvironment.finishSplitEnv setup codec (PqxdhDeploymentHiddenLayout.splitOutput read.1).1 j
                owner control before (embed pending) =
              PqxdhDeploymentEnvironment.finishSplitFwd setup codec (PqxdhDeploymentHiddenLayout.splitOutput read.1).1
                (embed pending) >>= fun staged =>
                PqxdhDeploymentEnvironment.hiddenOwnerEffect j owner before
                  (PqxdhBeaconPhase2Publication.finish control before staged).2 >>= fun _ =>
                  pure ((PqxdhBeaconPhase2Publication.finish control before staged).1, finishedEnv e owner e.native.shared
                    (PqxdhBeaconPhase2Publication.finish control before staged).2
                    (hiddenBackend e owner (PqxdhBeaconPhase2Publication.finish control before staged).2 coords' read.2)) := by
            simp only [PqxdhDeploymentEnvironment.finishSplitEnv, map_bind, map_pure]
          rw [program, PqxdhDeploymentEnvironmentReal.effects_then_free PqxdhDeploymentEnvironmentReal.ctxAdmin _
            (finishSplitFwd_noAdmin setup codec _ _) _ (fun staged => countFree_bind (countFree_hiddenOwnerEffect _ _ _ _)
              fun _ => countFree_pure _) _]
          have fac := PqxdhDeploymentSplitFactor.finishSplit_factor (n := 2) setup codec PqxdhDeploymentEnvironmentReal.ctxAdmin
            (PqxdhDeploymentHiddenLayout.splitOutput read.1).1 (embed pending) w.primitive.2
          have fwd : (simulateQ (ctxEffects PqxdhDeploymentEnvironmentReal.ctxAdmin)
              (PqxdhDeploymentEnvironment.finishSplitFwd (n := 2) setup codec (PqxdhDeploymentHiddenLayout.splitOutput
                read.1).1 (embed pending))).run w.primitive.2 =
              (fun r => (r.1.map (PqxdhDeploymentHiddenSplit.withKernel PqxdhDeploymentHiddenSplit.placeholderKernel),
                r.2.2)) <$> (PqxdhDeploymentHiddenEntry.finishErasedSvc setup codec
                  (PqxdhDeploymentHiddenLayout.splitOutput read.1).1 PqxdhDeploymentHiddenSplit.dummySeed
                    (embed pending)).run ((), w.primitive.2) := by
            have mapped := congrArg (fun work => (fun r => (r.1, r.2.2)) <$> work) fac
            simp only [Functor.map_map] at mapped
            rw [← id_map ((simulateQ (ctxEffects PqxdhDeploymentEnvironmentReal.ctxAdmin)
              (PqxdhDeploymentEnvironment.finishSplitFwd (n := 2) setup codec (PqxdhDeploymentHiddenLayout.splitOutput
                read.1).1 (embed pending))).run w.primitive.2)]
            refine mapped.symm.trans ?_
            unfold PqxdhDeploymentHiddenSplit.finishSplit
            rw [StateT.run_map, Functor.map_map]
          rw [show (withCache (withCache w w.primitive.2) (withCache w w.primitive.2).primitive.2).primitive.2 =
            w.primitive.2 from rfl, fwd, sharedM, dummy]
          change _ = (fun result => (result.1, (e.native.shared.1, { (PqxdhDeploymentEnvironmentReal.serverGame
            world.records.server e.native.shared.2.server.identityKeyId { e.native.shared.2 with ctx := w.primitive.2 })
              with ctx := result.2.2 }))) <$> (PqxdhDeploymentHiddenEntry.finishErasedSvc setup codec
                (PqxdhDeploymentHiddenLayout.splitOutput read.1).1 PqxdhDeploymentHiddenSplit.dummySeed
                  (embed pending)).run ((), w.primitive.2) >>= _
          rw [map_bind, bind_map_left, bind_map_left]
          refine bind_congr fun staged => ?_
          simp only [PqxdhDeploymentIdealKernel.finish_withKernel]
          have initSentTag : PqxdhDeploymentEnvironment.inactiveTag before.beacon.phase = some .initSent := by
            rw [phase]; rfl
          have tagEq : tag = .initSent := by
            simp only [PqxdhRecordLiftBeacon.projectPhase, phase, PqxdhRecordLiftBeacon.Phase.inactive.injEq] at projected
            exact projected.symm
          subst tagEq
          have below : owner < e.native.owners.length := (List.getElem?_eq_some_iff.mp owned).1
          rcases PqxdhDeploymentEnvironmentReal.commit_shape control before staged.1 with aborted | ⟨control', associatedData, kernel, established⟩
          · have abortedPhase : PqxdhRecordLiftBeacon.projectPhase
                (PqxdhBeaconPhase2Publication.finish control before staged.1).2.beacon = .inactive .aborted := by
              cases afterPhase : (PqxdhBeaconPhase2Publication.finish control before staged.1).2.beacon.phase <;>
                simp only [afterPhase, PqxdhDeploymentEnvironment.inactiveTag, reduceCtorEq, Option.some.injEq] at aborted
              simp only [PqxdhRecordLiftBeacon.projectPhase, afterPhase]
            have unkerneled : PqxdhDeploymentIdealKernel.setOwnerKernel
                (PqxdhBeaconPhase2Publication.finish control before staged.1).2
                  PqxdhDeploymentHiddenSplit.placeholderKernel =
                (PqxdhBeaconPhase2Publication.finish control before staged.1).2 := by
              unfold PqxdhDeploymentIdealKernel.setOwnerKernel
              cases afterPhase : (PqxdhBeaconPhase2Publication.finish control before staged.1).2.beacon.phase <;>
                simp only [afterPhase, PqxdhDeploymentEnvironment.inactiveTag, reduceCtorEq, Option.some.injEq] at aborted
              rfl
            have notEstablished : (match (PqxdhBeaconPhase2Publication.finish control before staged.1).2.beacon.phase with
                | .established _ _ _ => true
                | _ => false) = false := by
              cases afterPhase : (PqxdhBeaconPhase2Publication.finish control before staged.1).2.beacon.phase <;>
                simp only [afterPhase, PqxdhDeploymentEnvironment.inactiveTag, reduceCtorEq, Option.some.injEq] at aborted
              rfl
            rw [show withCache (withCache (withCache w w.primitive.2) (withCache w w.primitive.2).primitive.2) staged.2.2 =
              withCache w staged.2.2 from rfl]
            rw [unkerneled, hiddenOwnerEffect_abort j owner before _ initSentTag aborted,
              PqxdhDeploymentEnvironmentReal.effects_issue_then,
              PqxdhDeploymentEnvironmentReal.effects_advance owner .initSent .aborted (withCache w staged.2.2) worldPhase
                trivial, map_pure, map_pure,
              beaconInstall_closed owner _ _ _ (by
                change establishedAt ((merge e w).base.native.owners.set owner _) owner = false
                rw [establishedAt_set _ _ _ (by
                  change owner < (PqxdhDeploymentEnvironmentJoin.fill w e.native).owners.length
                  simp only [PqxdhDeploymentEnvironmentJoin.fill, List.length_mapIdx, below])]
                exact notEstablished), map_pure]
            obtain ⟨merged, _⟩ := PqxdhDeploymentIdealEnvReal.finish_merge_set created owner e w good world found
              (PqxdhBeaconPhase2Publication.finish control before staged.1).1
              (PqxdhBeaconPhase2Publication.finish control before staged.1).2 e.native.shared rfl staged.2.2
              (.inactive .aborted) below (by rw [abortedPhase]) (PqxdhDeploymentEnvironmentReal.fillOwner_inactive .aborted _)
            have baseEq := congrArg PqxdhDeploymentBackend.XState.base merged
            congr 1
            refine Prod.ext rfl ?_
            change PqxdhDeploymentBackend.XState.mk (merge { PqxdhDeploymentEnvironmentReal.snapFinish e owner with
              native := strip ⟨e.native.shared, e.native.owners.set owner
                (PqxdhBeaconPhase2Publication.finish control before staged.1).2⟩ }
              (uncount { withCache w staged.2.2 with owners := w.owners.set owner (.inactive .aborted) })).base _ _ _ _ = _
            rw [baseEq]
            have belowM : owner < (merge e w).base.native.owners.length := by
              change owner < (PqxdhDeploymentEnvironmentJoin.fill w e.native).owners.length
              simp only [PqxdhDeploymentEnvironmentJoin.fill, List.length_mapIdx, below]
            simp only [finishedX, finishedEnv, hiddenBackend, establishedAt_set _ _ _ below, establishedAt_set _ _ _ belowM,
              notEstablished, Bool.false_eq_true, ↓reduceIte]
            rw [show (merge e w).base.native = PqxdhDeploymentEnvironmentJoin.fill w e.native from rfl, snapshotAt_fill]
            rfl
          · have belowM : owner < (merge e w).base.native.owners.length := by
              change owner < (PqxdhDeploymentEnvironmentJoin.fill w e.native).owners.length
              simp only [PqxdhDeploymentEnvironmentJoin.fill, List.length_mapIdx, below]
            have kernelPhase : ∀ k : beaconcrypt_core.ratchet.concrete.ConcreteRatchetKernel,
                (PqxdhDeploymentIdealKernel.setOwnerKernel (PqxdhBeaconPhase2Publication.finish control before staged.1).2
                  k).beacon.phase = .established control' associatedData k := by
              intro k
              unfold PqxdhDeploymentIdealKernel.setOwnerKernel
              rw [established]
            have kernelId : ∀ k : beaconcrypt_core.ratchet.concrete.ConcreteRatchetKernel,
                (PqxdhDeploymentIdealKernel.setOwnerKernel (PqxdhBeaconPhase2Publication.finish control before staged.1).2
                  k).beacon.identityKeyId = (PqxdhBeaconPhase2Publication.finish control before staged.1).2.beacon.identityKeyId := by
              intro k
              unfold PqxdhDeploymentIdealKernel.setOwnerKernel
              rw [established]
            have isEstablished : (match (PqxdhBeaconPhase2Publication.finish control before staged.1).2.beacon.phase with
                | .established _ _ _ => true
                | _ => false) = true := by
              rw [established]
            have isEstablished' : (match (PqxdhDeploymentIdealKernel.setOwnerKernel
                (PqxdhBeaconPhase2Publication.finish control before staged.1).2
                  PqxdhDeploymentHiddenSplit.placeholderKernel).beacon.phase with
                | .established _ _ _ => true
                | _ => false) = true := by
              rw [kernelPhase]
            rw [show withCache (withCache (withCache w w.primitive.2) (withCache w w.primitive.2).primitive.2) staged.2.2 =
              withCache w staged.2.2 from rfl]
            rw [hiddenOwnerEffect_establish j owner before _ initSentTag control' associatedData _ (kernelPhase _),
              PqxdhDeploymentEnvironmentReal.effects_issue_then,
              effects_hiddenBeacon owner _ j (withCache w staged.2.2) worldPhase (unused j),
              beaconInstall_open owner _ coords' _ j allocated (by
                change establishedAt ((merge e w).base.native.owners.set owner _) owner = true
                rw [establishedAt_set _ _ _ belowM]
                exact isEstablished)]
            have project : ((PqxdhRecordLiftWorld.SeedSpec 2).randomOracle j).run w.seeds.1 =
                Prod.map id Prod.fst <$> (PqxdhRecordLiftLazyTable.impl j).run w.seeds := by
              have projected := PqxdhRecordLiftLazyTable.run_project (spec := PqxdhRecordLiftWorld.SeedSpec 2)
                (liftM ((PqxdhRecordLiftWorld.SeedSpec 2).query j)) w.seeds
              simp only [simulateQ_spec_query] at projected
              exact projected.symm
            change _ = _ <$> (_ <$> ((PqxdhRecordLiftWorld.SeedSpec 2).randomOracle j).run w.seeds.1)
            rw [project]
            simp only [Functor.map_map]
            congr 1
            funext r
            obtain ⟨seed, table⟩ := r
            obtain ⟨merged, _⟩ := PqxdhDeploymentIdealEnvReal.finish_merge_set created owner e w good world found
              (PqxdhBeaconPhase2Publication.finish control before staged.1).1
              (PqxdhDeploymentIdealKernel.setKernelAt seed (PqxdhBeaconPhase2Publication.finish control before staged.1).2)
              e.native.shared rfl staged.2.2
              (.established ⟨(PqxdhBeaconPhase2Publication.finish control before staged.1).2.beacon.identityKeyId, control',
                associatedData⟩ (PqxdhRecordLiftWorld.kernel .beacon seed)) below
              (by
                simp only [PqxdhDeploymentIdealKernel.setKernelAt, PqxdhRecordLiftBeacon.projectPhase, kernelPhase,
                  kernelId])
              (by
                have self := PqxdhDeploymentEnvironmentReal.fillOwner_self (PqxdhDeploymentIdealKernel.setKernelAt seed
                  (PqxdhBeaconPhase2Publication.finish control before staged.1).2) control' associatedData
                  (PqxdhRecordLiftWorld.kernel .beacon seed) (kernelPhase _)
                rw [show (PqxdhDeploymentIdealKernel.setKernelAt seed (PqxdhBeaconPhase2Publication.finish control before
                  staged.1).2).beacon.identityKeyId = (PqxdhBeaconPhase2Publication.finish control before
                    staged.1).2.beacon.identityKeyId from kernelId _] at self
                exact self)
            have baseEq := congrArg PqxdhDeploymentBackend.XState.base merged
            rw [kernelId]
            refine Prod.ext rfl ?_
            change PqxdhDeploymentBackend.XState.mk (merge { PqxdhDeploymentEnvironmentReal.snapFinish e owner with
              native := strip ⟨e.native.shared, e.native.owners.set owner (PqxdhDeploymentIdealKernel.setOwnerKernel
                (PqxdhBeaconPhase2Publication.finish control before staged.1).2
                  PqxdhDeploymentHiddenSplit.placeholderKernel)⟩ }
              (uncount { withCache w staged.2.2 with owners := w.owners.set owner (.established
                ⟨(PqxdhBeaconPhase2Publication.finish control before staged.1).2.beacon.identityKeyId, control',
                  associatedData⟩ (PqxdhRecordLiftWorld.kernel .beacon seed)) })).base _ _ _ _ = _
            rw [strip_setOwnerKernel _ _ _ _ PqxdhDeploymentHiddenSplit.placeholderKernel
              (PqxdhRecordLiftWorld.kernel .beacon seed),
              show PqxdhDeploymentIdealKernel.setOwnerKernel (PqxdhBeaconPhase2Publication.finish control before staged.1).2
                (PqxdhRecordLiftWorld.kernel .beacon seed) = PqxdhDeploymentIdealKernel.setKernelAt seed
                  (PqxdhBeaconPhase2Publication.finish control before staged.1).2 from rfl, baseEq]
            simp only [finishedX, finishedEnv, hiddenBackend, establishedAt_set _ _ _ below, establishedAt_set _ _ _ belowM,
              isEstablished, isEstablished', ↓reduceIte, Option.some_or, PqxdhDeploymentIdealKernel.set_modify]
            rw [show (merge e w).base.native = PqxdhDeploymentEnvironmentJoin.fill w e.native from rfl, snapshotAt_fill]
            rfl
        · simp only [map_pure, pure_bind]
          rw [sharedM]
          exact commit_case created owner e w good world found before control prekey oneTime kem owned phase
            e.native.shared rfl w.primitive.2 none
      · simp only []
        have program : (coins ((PqxdhRegistrationJointBeaconOpaqueFinish.markedRoot setup.hmac
            (List.Vector.replicate 32 0) pending.root).run e.native.shared) >>= fun r =>
            match r.1 with
            | none => commitEnv e owner control before r.2 none
            | some root => simulateQ (knownFwd setup codec) (PqxdhBeaconPhase2Shared.afterRoot codec.frameRead pending
                root) >>= fun staged => commitEnv e owner control before r.2 staged) =
            (coins ((PqxdhRegistrationJointBeaconOpaqueFinish.markedRoot setup.hmac (List.Vector.replicate 32 0)
              pending.root).run e.native.shared) >>= fun r =>
              match r.1 with
              | none => pure (r.2, none)
              | some root => (fun staged => (r.2, staged)) <$> simulateQ (knownFwd setup codec)
                  (PqxdhBeaconPhase2Shared.afterRoot codec.frameRead pending root)) >>= fun v =>
              commitEnv e owner control before v.1 v.2 := by
          rw [bind_assoc]
          refine bind_congr fun r => ?_
          rcases r with ⟨_ | root, st⟩
          · simp only [pure_bind]
          · simp only [bind_map_left]
        rw [program, PqxdhDeploymentEnvironmentReal.effects_then_free PqxdhDeploymentEnvironmentReal.ctxAdmin _ ?noAdmin _
          (fun v => countFree_commitEnv _ _ _ _ _ _) _]
        · rw [show (withCache w w.primitive.2).primitive.2 = w.primitive.2 from rfl, simulateQ_bind, StateT.run_bind,
            PqxdhDeploymentEnvironment.ctxEffects_coins, bind_map_left, map_bind, sharedM]
          unfold PqxdhDeploymentIdealErase.knownWork
          rw [StateT.run_bind, markedRoot_game setup.hmac _ pending.root e.native.shared
            (PqxdhDeploymentEnvironmentReal.serverGame world.records.server e.native.shared.2.server.identityKeyId
              { e.native.shared.2 with ctx := w.primitive.2 })]
          simp only [map_bind, Functor.map_map, bind_assoc, bind_map_left]
          apply OracleComp.bind_congr_of_forall_mem_support
          rintro ⟨root, family', game'⟩ member
          have gameEq : game' = e.native.shared.2 := by
            have same := markedRoot_game (KemSK := KemSK) setup.hmac (List.Vector.replicate 32 0) pending.root
              e.native.shared e.native.shared.2
            rw [show ((e.native.shared.1, e.native.shared.2) : NativeState KemSK) = e.native.shared from rfl] at same
            rw [same, support_map] at member
            obtain ⟨_, _, equal⟩ := member
            exact (congrArg (fun r => r.2.2) equal).symm
          subst gameEq
          rcases root with _ | root
          · simp only [simulateQ_pure, StateT.run_pure, pure_bind]
            have h := commit_case created owner e w good world found before control prekey oneTime kem owned phase
              (family', e.native.shared.2) rfl w.primitive.2 none
            rw [Functor.map_map] at h
            exact h
          · simp only [simulateQ_map, StateT.run_map, bind_map_left]
            change _ = (fun res => (res.1, (family', { (PqxdhDeploymentEnvironmentReal.serverGame world.records.server
              e.native.shared.2.server.identityKeyId { e.native.shared.2 with ctx := w.primitive.2 }) with
                ctx := res.2.2 }))) <$> (simulateQ (PqxdhRegistrationJointKemPostSkeleton.tailNative setup codec)
                  (PqxdhBeaconPhase2Shared.afterRoot codec.frameRead pending root)).run ((), w.primitive.2) >>= _
            rw [knownFwd_factor setup codec PqxdhDeploymentEnvironmentReal.ctxAdmin, Functor.map_map, bind_map_left]
            refine bind_congr fun staged => ?_
            have h := commit_case created owner e w good world found before control prekey oneTime kem owned phase
              (family', e.native.shared.2) rfl staged.2 staged.1
            rw [Functor.map_map] at h
            exact h
        · rw [show (0 : ℕ) = 0 + 0 from rfl]
          refine isQueryBoundP_bind (coins_noAdmin _) fun r _ => ?_
          rcases r with ⟨_ | root, st⟩
          · exact isQueryBoundP_pure _ _ _
          · exact (isQueryBoundP_map_iff _ _ _).mpr (knownFwd_noAdmin setup codec _)

open PqxdhDeploymentEnvironmentReal (keeps_uncount good_uncount good_matched fill_inactive) in
/-- Owner k's challenge finish in capability form keeps admissibility, from an admissible joint state whose owner k is in the `initSent` phase and whose World holds no Beacon marker. -/
theorem finishChallenge_keeps (created : PqxdhLiveServerConstruction.Created Unit) (p : Params KemSK count) (owner : ℕ)
    (raw : Pqxdh.Bytes) (e : EnvState KemSK SplitBk) (w : PqxdhRecordLiftWorld.State 2) (good : Good created e w)
    (initSentOwner : PqxdhDeploymentIdealSteps.initSentAt e.native.owners owner = true)
    (unused : ∀ j, w.used j .beacon = false) :
    ∀ result ∈ support ((simulateQ PqxdhRecordLiftWorld.effects
        ((finishChallengeEnv setup codec p owner raw).run e)).run w),
      Good created result.1.2 result.2 := by
  obtain ⟨world, found, _, _, _⟩ := good.server
  rcases owned : e.native.owners[owner]? with _ | before
  · simp only [PqxdhDeploymentIdealSteps.initSentAt, owned, Bool.false_eq_true] at initSentOwner
  rcases phase : before.beacon.phase with _ | _ | ⟨control, prekey, oneTime, kem⟩ | _ | _
  all_goals try (simp only [PqxdhDeploymentIdealSteps.initSentAt, owned, phase, Bool.false_eq_true] at initSentOwner)
  have inactive : ¬ RawCtxBeaconLifecycle.Established before.beacon.phase := by
    rw [phase]
    simp only [RawCtxBeaconLifecycle.Established, not_false_eq_true]
  have initSent : PqxdhDeploymentEnvironment.inactiveTag before.beacon.phase = some .initSent := by rw [phase]; rfl
  obtain ⟨tag, worldPhase, projected, _⟩ := fill_inactive w _ (good_matched created e w good) owner before owned inactive
  have tagEq : tag = .initSent := by
    simp only [PqxdhRecordLiftBeacon.projectPhase, phase, PqxdhRecordLiftBeacon.Phase.inactive.injEq] at projected
    exact projected.symm
  subst tagEq
  have below : owner < e.native.owners.length := (List.getElem?_eq_some_iff.mp owned).1
  apply keeps_uncount _ (Good created) (good_uncount created)
  intro result supported
  rcases finishChallenge_outcome setup codec p owner raw e w before control prekey oneTime kem owned phase worldPhase
    result supported with ⟨shared, staged, cache, worldPhase', game, consistent, selfFill, rfl⟩ |
      ⟨pending, coords, read, j, _, _, hidden⟩
  · exact (PqxdhDeploymentIdealEnvReal.finish_merge_set created owner e w good world found
      (PqxdhBeaconPhase2Publication.finish control before staged).1 (PqxdhBeaconPhase2Publication.finish control before
        staged).2 shared game cache worldPhase' below consistent selfFill).2
  · rcases hiddenFinish_outcome setup codec e owner control before pending coords read j w w.primitive.2 initSent
      worldPhase (unused j) result hidden with ⟨staged, cache, ⟨aborted, rfl⟩ | ⟨control', associatedData, kernel, seed,
        table, established, _, _, rfl⟩⟩
    · have abortedPhase : PqxdhRecordLiftBeacon.projectPhase (PqxdhBeaconPhase2Publication.finish control before
          staged).2.beacon = .inactive .aborted := by
        cases afterPhase : (PqxdhBeaconPhase2Publication.finish control before staged).2.beacon.phase <;>
          simp only [afterPhase, PqxdhDeploymentEnvironment.inactiveTag, reduceCtorEq, Option.some.injEq] at aborted
        simp only [PqxdhRecordLiftBeacon.projectPhase, afterPhase]
      have kept := (PqxdhDeploymentIdealEnvReal.finish_merge_set created owner e w good world found
        (PqxdhBeaconPhase2Publication.finish control before staged).1 (PqxdhBeaconPhase2Publication.finish control before
          staged).2 e.native.shared rfl cache (.inactive .aborted)
        below (by rw [abortedPhase]) (PqxdhDeploymentEnvironmentReal.fillOwner_inactive .aborted _)).2
      exact ⟨kept.stripped, kept.createdEq, kept.server, kept.ownersLength, kept.owners⟩
    · have kernelPhase : (PqxdhDeploymentIdealKernel.setOwnerKernel (PqxdhBeaconPhase2Publication.finish control before
          staged).2 (PqxdhRecordLiftWorld.kernel .beacon seed)).beacon.phase =
            .established control' associatedData (PqxdhRecordLiftWorld.kernel .beacon seed) := by
        unfold PqxdhDeploymentIdealKernel.setOwnerKernel
        rw [established]
      have kernelId : (PqxdhDeploymentIdealKernel.setOwnerKernel (PqxdhBeaconPhase2Publication.finish control before
          staged).2 (PqxdhRecordLiftWorld.kernel .beacon seed)).beacon.identityKeyId =
            (PqxdhBeaconPhase2Publication.finish control before staged).2.beacon.identityKeyId := by
        unfold PqxdhDeploymentIdealKernel.setOwnerKernel
        rw [established]
      have kept := (PqxdhDeploymentIdealEnvReal.finish_merge_set created owner e w good world found
        (PqxdhBeaconPhase2Publication.finish control before staged).1
        (PqxdhDeploymentIdealKernel.setOwnerKernel (PqxdhBeaconPhase2Publication.finish control before staged).2
          (PqxdhRecordLiftWorld.kernel .beacon seed)) e.native.shared rfl cache
        (.established ⟨(PqxdhBeaconPhase2Publication.finish control before staged).2.beacon.identityKeyId, control',
          associatedData⟩ (PqxdhRecordLiftWorld.kernel .beacon seed)) below
        (by simp only [PqxdhRecordLiftBeacon.projectPhase, kernelPhase, kernelId])
        (by
          have self := PqxdhDeploymentEnvironmentReal.fillOwner_self (PqxdhDeploymentIdealKernel.setOwnerKernel
            (PqxdhBeaconPhase2Publication.finish control before staged).2 (PqxdhRecordLiftWorld.kernel .beacon seed))
            control' associatedData (PqxdhRecordLiftWorld.kernel .beacon seed) kernelPhase
          rw [kernelId] at self
          exact self)).2
      have nativeEq : strip (⟨e.native.shared, e.native.owners.set owner (PqxdhDeploymentIdealKernel.setOwnerKernel
          (PqxdhBeaconPhase2Publication.finish control before staged).2 (PqxdhRecordLiftWorld.kernel .beacon seed))⟩ :
            PqxdhRegistrationSchedule.State KemSK) =
          strip ⟨e.native.shared, e.native.owners.set owner (PqxdhBeaconPhase2Publication.finish control before staged).2⟩ := by
        simp only [strip, List.map_set, stripOwner_setOwnerKernel]
      rw [nativeEq] at kept
      exact ⟨kept.stripped, kept.createdEq, kept.server, kept.ownersLength, kept.owners⟩

/-- Owner k's challenge finish in capability form splits the final split form's challenge finish: the reassembled law is the split form's (exactly) and admissibility is kept, from an admissible joint state whose selected accept was active, whose owner k is in the `initSent` phase, whose allocator has room and whose World holds no Beacon marker. -/
theorem finishChallenge_splits (t : Target count) (p : Params KemSK count)
    (created : PqxdhLiveServerConstruction.Created Unit) (owner : ℕ) (raw : Pqxdh.Bytes) (e : EnvState KemSK SplitBk)
    (w : PqxdhRecordLiftWorld.State 2) (good : Good created e w)
    (chosen : e.backend.2.2.active = true ∧ owner = t.kem.val ∧
      PqxdhDeploymentIdealSteps.initSentAt e.native.owners owner = true)
    (room : e.backend.2.1.2 < 2) (unused : ∀ j, w.used j .beacon = false) :
    LazyOracleDiscard.LawEq ((fun result => (result.1.1, merge result.1.2 result.2)) <$>
        (simulateQ PqxdhRecordLiftWorld.effects ((finishChallengeEnv setup codec p owner raw).run e)).run w)
      ((PqxdhDeploymentIdealDefer.idealSplit setup codec route checks t p created ⟨.finish owner raw, trivial⟩).run
        (merge e w)) ∧
    ∀ result ∈ support ((simulateQ PqxdhRecordLiftWorld.effects
        ((finishChallengeEnv setup codec p owner raw).run e)).run w),
      Good created result.1.2 result.2 :=
  ⟨LazyOracleDiscard.LawEq.of_eq (finishChallenge_law setup codec route checks t p created owner raw e w good chosen room
    unused), finishChallenge_keeps setup codec created p owner raw e w good chosen.2.2 unused⟩

end FinishEffects

end BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvFinish

-- Axiom guards (generated)

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvFinish.effects_hiddenBeacon' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvFinish.effects_hiddenBeacon

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvFinish.countFree_hiddenBeacon' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvFinish.countFree_hiddenBeacon

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvFinish.countFree_hiddenOwnerEffect' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvFinish.countFree_hiddenOwnerEffect

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvFinish.knownFwd_factor' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvFinish.knownFwd_factor

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvFinish.simulateQ_noAdmin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvFinish.simulateQ_noAdmin

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvFinish.knownFwd_noAdmin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvFinish.knownFwd_noAdmin

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvFinish.countFree_noAdmin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvFinish.countFree_noAdmin

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvFinish.group_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvFinish.group_native

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvFinish.owner_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvFinish.owner_native

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvFinish.challenge_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvFinish.challenge_native

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvFinish.slotRun_finish_hidden' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvFinish.slotRun_finish_hidden

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvFinish.countFree_map' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvFinish.countFree_map

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvFinish.countFree_commitEnv' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvFinish.countFree_commitEnv

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvFinish.finishSplitFwd_noAdmin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvFinish.finishSplitFwd_noAdmin

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvFinish.countFree_finishSplitEnv' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvFinish.countFree_finishSplitEnv

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvFinish.countFree_groupEnv' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvFinish.countFree_groupEnv

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvFinish.finishChallenge_effects' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvFinish.finishChallenge_effects

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvFinish.lazyRead_support' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvFinish.lazyRead_support

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvFinish.establishedAt_set' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvFinish.establishedAt_set

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvFinish.strip_setOwnerKernel' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvFinish.strip_setOwnerKernel

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvFinish.hiddenOwnerEffect_abort' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvFinish.hiddenOwnerEffect_abort

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvFinish.hiddenOwnerEffect_establish' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvFinish.hiddenOwnerEffect_establish

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvFinish.beaconInstall_closed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvFinish.beaconInstall_closed

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvFinish.beaconInstall_open' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvFinish.beaconInstall_open

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvFinish.stripOwner_setOwnerKernel' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvFinish.stripOwner_setOwnerKernel

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvFinish.markedRoot_game' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvFinish.markedRoot_game

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvFinish.commit_case' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvFinish.commit_case

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvFinish.commit_outcome' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvFinish.commit_outcome

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvFinish.hiddenFinish_outcome' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvFinish.hiddenFinish_outcome

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvFinish.finishChallenge_outcome' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvFinish.finishChallenge_outcome

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvFinish.finishChallenge_law' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvFinish.finishChallenge_law

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvFinish.finishChallenge_keeps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvFinish.finishChallenge_keeps

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvFinish.finishChallenge_splits' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvFinish.finishChallenge_splits
