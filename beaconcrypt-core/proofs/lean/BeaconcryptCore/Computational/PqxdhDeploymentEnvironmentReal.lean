-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentJoin

/-!
# The real registration environment joins the record world (CE-11a, increment 4)

The real registration environment `PqxdhDeploymentEnvironment.envReal` splits the real registration handler `PqxdhDeploymentBackend.realReg` (the LQ-F run-phase handler) command by command (`realReg_splits_create`, `realReg_splits_bundle`, `realReg_splits_accept`, `realReg_splits_build`, `realReg_splits_finish`, `realReg_splits_hmac`, together `real_splits`), relative to the trivial admissibility predicate: the real registration runs with no hidden slot (`n = 0`) and its environment installs only known kernels, so no used-marker condition is needed. Instantiating the generic join of increment 3 gives C1 for the real game (`c1_real`, with the projections `c1_real_classical` onto `PqxdhDeploymentSecrecy.game`, `c1_real_runPhase` onto the LQ-F run phase, `c1_real_observed` onto `PqxdhRecordLiftWorld.game`, `c1_real_analysis` onto `PqxdhRecordLiftWorld.analysis` and `c1_real_reveal` onto the run-phase reveal, and the observed and analysis projections with `PqxdhDeploymentSecrecy.game` on the left, `c1_real_classical_observed` and `c1_real_classical_analysis`), C3 (`c3_real`) and C6 (`c6_real`: the LQ-F later game against `PqxdhRecordLiftLater.run` with the environment's reveal `envReveal`, through `postNative_real`, and its public form `c6_real_public`). The per-command lemmas (section `Commands`) are stated for this handler only, at `n = 0` with the unit backend state; the tools before them (sections `Bridge` to `FinishShape`) are generic in `n` and the backend state. This is the validation (critique m12) that the hypotheses of the generic join are satisfiable for the real game; for each command the reassembled law is the real handler's exactly (`create_law`, `bundle_law`, `accept_law`, `build_law`, `finish_law`, `hmac_law`) and admissibility is kept (`create_keeps` to `hmac_keeps`).

**The World read on its cache.** A program of coin and BLAKE2b effects, run by the World with its counts forgotten, is that program read through `PqxdhDeploymentEnvironment.ctxEffects` on the World's shared CTX cache (`effects_query_ctx`, `effects_ctx`, `effects_coins`). `CountFree` programs, whose World run does not depend on the counts, include every record-relevant request with a known kernel (`countFree_issue`, `countFree_ownerEffect`, `countFree_ownerChange`, `countFree_serverEffect`), and `effects_then_free` composes a forwarded program with such a continuation. The requests the real environment issues are computed explicitly (`effects_append`, `effects_advance`, `effects_installServer`, `effects_installBeacon`).

**Frames.** `NFrame f step`: a step of the shared native state commutes with a map `f` of its game state. The native public HMAC, the logged raw accept and the Beacon finish callbacks commute with replacing the CTX cache, the Server's routing record and its identity key ID (`frameGame`, `serverGame`; `nativeHmac_nframe`, `acceptLogged_nframe`, `callbacks_nframe`), so on the reassembled state they run as on the environment's stripped state (`shared_run`, `shared_fill`, `shared_good`).

**Reassembly.** `fill_some` (filling with an initialized World Server is `frameGame` on the game state), `fill_strip` (filling a stripped state with a World that matches it is filling the state), `fill_set`, `matched_set`, `good_intro` and `good_server`.

**Shapes.** `bundle_shape` (a Phase 1 bundle leaves its owner or publishes it from a fresh phase, `Bundled`), `build_shape` (a Server build publishes at most one peer, at a key ID that was vacant, `Built`) and `finish_shape` (a finish leaves its owner or ends an initSent owner aborted or established, `Finished`).

**Build and finish.** The Server build reuses CE-3's override lemmas (`PqxdhDeploymentCompileRegistration.build_override`, `settle_override`) with the World's peer kernels as local copies (`worldCopies`, `override_world`, `override_publish`, `installed_world`) and the BLAKE2b factoring `PqxdhDeploymentEnvironment.tail_factor`; the finish reuses `owner_factor` and `frame_program`, with the forwarded finish issuing no administrative effect and keeping the game state (`finishFwd_noAdmin`, `finishFwd_game`).

These are equalities of programs and in law. No security, secrecy or authentication claim is made here.
-/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete PqxdhRefinement

set_option autoImplicit false

namespace BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentReal
open PqxdhServerAuthExperiment (Setup Codec Checks GameState)
open PqxdhServerAuthNative (NativeState NativeGame)
open PqxdhRecordLiftInterface (Slot Capability CapabilitySpec EnvEffects EnvQuery EnvSpec Environment EffectKind
  effectKind BeaconShell InactivePhase KernelRef)
open PqxdhDeploymentEnvironment (EnvState EnvStep strip Stripped stripPeer stripOwner ctxEffects coins)
open PqxdhDeploymentEnvironmentJoin (merge fill fillOwner fillServer Good Splits uncount stripPhase)
open PqxdhDeploymentBackend (XState RegImpl handlerWith gameWith)
open LazyOracleDiscard (LawEq)

variable {KemSK : Type}

/-! ### The World's effects read on its CTX cache -/

section Bridge
variable {n : Nat} (admin : QueryImpl (CapabilitySpec n) (StateT CtxRomAuth.CtxRO.QueryCache ProbComp))

/-- A World state with its counts forgotten and its shared CTX cache replaced. -/
def withCache (w : PqxdhRecordLiftWorld.State n) (cache : CtxRomAuth.CtxRO.QueryCache) : PqxdhRecordLiftWorld.State n :=
  { w with primitive := (PqxdhRecordLiftWorld.Counts.empty, cache) }

/-- One coin or BLAKE2b effect of the World, its counts forgotten, is that effect read through `ctxEffects` on the World's cache. -/
theorem effects_query_ctx (query : (EnvEffects n).Domain) (notAdmin : effectKind query ≠ .administrative)
    (w : PqxdhRecordLiftWorld.State n) :
    Prod.map id uncount <$> (PqxdhRecordLiftWorld.effects query).run w =
      (fun result => (result.1, withCache w result.2)) <$> (ctxEffects admin query).run w.primitive.2 := by
  rcases query with coin | capability
  · have forgot := congrArg (fun work => (fun value => (value, withCache w w.primitive.2)) <$> work)
      (PqxdhRecordLiftWorld.countCoin_forget (unifSpec.query coin : ProbComp _) w.primitive.1.uniform)
    simp only [Functor.map_map] at forgot
    refine Eq.trans ?_ (Eq.trans forgot ?_)
    · simp only [PqxdhRecordLiftWorld.effects, PqxdhRecordLiftWorld.sampled, StateT.run, bind_pure_comp, Functor.map_map]
      rfl
    · simp only [ctxEffects, StateT.run_lift, bind_pure_comp, Functor.map_map]
      rfl
  · cases capability with
    | hash bytes =>
        have forgot := congrArg (fun work => (fun result : CtxRomAuth.CtxDigest × CtxRomAuth.CtxRO.QueryCache =>
            (result.1, withCache w result.2)) <$> work)
          (PqxdhRecordLiftWorld.countCoin_forget ((CtxRomAuth.ctxRandomOracle ((), bytes)).run w.primitive.2)
            w.primitive.1.uniform)
        simp only [Functor.map_map] at forgot
        refine Eq.trans ?_ (Eq.trans forgot ?_)
        · simp only [PqxdhRecordLiftWorld.effects, PqxdhRecordLiftWorld.capability, PqxdhRecordLiftWorld.sampled,
            StateT.run, bind_pure_comp, Functor.map_map]
          rfl
        · rfl
    | _ => exact absurd rfl notAdmin

/-- A program of coin and BLAKE2b effects (no administrative effect), run by the World with its counts forgotten, is that program read through `ctxEffects` on the World's cache. -/
theorem effects_ctx {α : Type} (work : OracleComp (EnvEffects n) α)
    (noAdmin : work.IsQueryBoundP (fun effect => effectKind effect = .administrative) 0) (w : PqxdhRecordLiftWorld.State n) :
    Prod.map id uncount <$> (simulateQ PqxdhRecordLiftWorld.effects work).run w =
      (fun result => (result.1, withCache w result.2)) <$> (simulateQ (ctxEffects admin) work).run w.primitive.2 := by
  induction work using OracleComp.inductionOn generalizing w with
  | pure value => simp only [simulateQ_pure, StateT.run_pure, map_pure]; rfl
  | query_bind query next ih =>
      rw [isQueryBoundP_query_bind_iff] at noAdmin
      obtain ⟨notAdmin, rest⟩ := noAdmin
      have notAdmin' : effectKind query ≠ .administrative := by
        intro same
        simp only [same, not_true_eq_false, false_or, lt_self_iff_false] at notAdmin
      simp only [notAdmin', ite_false] at rest
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, id_map,
        StateT.run_bind, map_bind]
      have step := effects_query_ctx admin query notAdmin' w
      have continued : ∀ result : (EnvEffects n).Range query × PqxdhRecordLiftWorld.State n,
          Prod.map id uncount <$> (simulateQ PqxdhRecordLiftWorld.effects (next result.1)).run result.2 =
            (fun final => (final.1, withCache (uncount result.2) final.2)) <$>
              (simulateQ (ctxEffects admin) (next result.1)).run (uncount result.2).primitive.2 :=
        fun result => ih result.1 (rest result.1) result.2
      simp only [continued]
      calc _ = (Prod.map id uncount <$> (PqxdhRecordLiftWorld.effects query).run w) >>= fun result =>
              (fun final => (final.1, withCache result.2 final.2)) <$>
                (simulateQ (ctxEffects admin) (next result.1)).run result.2.primitive.2 := by
            rw [bind_map_left]
            rfl
        _ = _ := by
            rw [step, bind_map_left]
            rfl

/-- A default reading of the administrative capabilities on the CTX cache (the bridge never uses it). -/
noncomputable def ctxAdmin : QueryImpl (CapabilitySpec n) (StateT CtxRomAuth.CtxRO.QueryCache ProbComp)
  | .peerPresent _ => pure false
  | .ownerPresent _ => pure false
  | .appendOwner _ _ _ => pure 0
  | .advanceOwner _ _ => pure false
  | .installServer _ _ _ => pure false
  | .installBeacon _ _ _ => pure false
  | .hash bytes => CtxRomAuth.ctxRandomOracle ((), bytes)

/-- A registration computation's coins issue no administrative effect. -/
theorem coins_noAdmin {α : Type} (work : ProbComp α) :
    (coins (n := n) work).IsQueryBoundP (fun effect => effectKind effect = .administrative) 0 :=
  IsQueryBoundP.simulateQ_of_step (isQueryBoundP_false _ 0) (fun _ absurd => absurd.elim) fun _ _ =>
    (isQueryBoundP_query_iff _ _ _).mpr fun same => by cases same

/-- A registration computation's coins, run by the World with its counts forgotten, are the original coins with the World unchanged. -/
theorem effects_coins {α : Type} (work : ProbComp α) (w : PqxdhRecordLiftWorld.State n) :
    Prod.map id uncount <$> (simulateQ PqxdhRecordLiftWorld.effects (coins (n := n) work)).run w =
      (fun value => (value, uncount w)) <$> work := by
  rw [effects_ctx ctxAdmin _ (coins_noAdmin work), PqxdhDeploymentEnvironment.ctxEffects_coins, Functor.map_map]
  rfl

/-- A program without administrative effect followed by a continuation whose World run, counts forgotten, depends only on the counts-free World: the program read through `ctxEffects` on the World's cache, then the continuation. -/
theorem effects_then {α β : Type} (work : OracleComp (EnvEffects n) α)
    (noAdmin : work.IsQueryBoundP (fun effect => effectKind effect = .administrative) 0)
    (next : α → OracleComp (EnvEffects n) β)
    (after : α → PqxdhRecordLiftWorld.State n → ProbComp (β × PqxdhRecordLiftWorld.State n))
    (continued : ∀ value world, Prod.map id uncount <$> (simulateQ PqxdhRecordLiftWorld.effects (next value)).run world =
      after value (uncount world))
    (w : PqxdhRecordLiftWorld.State n) :
    Prod.map id uncount <$> (simulateQ PqxdhRecordLiftWorld.effects (work >>= next)).run w =
      (simulateQ (ctxEffects admin) work).run w.primitive.2 >>= fun result => after result.1 (withCache w result.2) := by
  rw [simulateQ_bind, StateT.run_bind, map_bind]
  simp only [continued]
  calc _ = (Prod.map id uncount <$> (simulateQ PqxdhRecordLiftWorld.effects work).run w) >>= fun result =>
          after result.1 result.2 := by
        rw [bind_map_left]
        rfl
    _ = _ := by
        rw [effects_ctx admin work noAdmin w, bind_map_left]

/-- A mapped program, run by the World with its counts forgotten. -/
theorem effects_map {α β : Type} (f : α → β) (work : OracleComp (EnvEffects n) α) (w : PqxdhRecordLiftWorld.State n) :
    Prod.map id uncount <$> (simulateQ PqxdhRecordLiftWorld.effects (f <$> work)).run w =
      Prod.map f id <$> (Prod.map id uncount <$> (simulateQ PqxdhRecordLiftWorld.effects work).run w) := by
  rw [simulateQ_map, StateT.run_map, Functor.map_map, Functor.map_map]
  rfl

/-- One administrative request, run by the World with its counts forgotten. -/
theorem effects_issue (capability : Capability n) (w : PqxdhRecordLiftWorld.State n) :
    Prod.map id uncount <$> (simulateQ PqxdhRecordLiftWorld.effects (PqxdhDeploymentEnvironment.issue capability)).run w =
      (fun result => ((), uncount result.2)) <$>
        (PqxdhRecordLiftWorld.capability capability).run (PqxdhRecordLiftWorld.chargeEffect (.inr capability) w) := by
  simp only [PqxdhDeploymentEnvironment.issue, PqxdhDeploymentEnvironment.request, bind_pure_comp, simulateQ_map,
    simulateQ_spec_query, StateT.run_map, Functor.map_map]
  rfl

/-- One administrative request followed by a pure reply, run by the World with its counts forgotten. -/
theorem effects_issue_then {β : Type} (capability : Capability n) (value : β) (w : PqxdhRecordLiftWorld.State n) :
    Prod.map id uncount <$> (simulateQ PqxdhRecordLiftWorld.effects
        (PqxdhDeploymentEnvironment.issue capability >>= fun _ => pure value)).run w =
      (fun result => (value, result.2)) <$> (Prod.map id uncount <$> (simulateQ PqxdhRecordLiftWorld.effects
        (PqxdhDeploymentEnvironment.issue capability)).run w) := by
  simp only [bind_pure_comp, simulateQ_map, StateT.run_map, Functor.map_map]
  rfl

/-- Appending an inactive owner, counts forgotten. -/
theorem effects_append (sender : Std.U64) (identity : RawCtxServerRouting.Identity) (phase : InactivePhase)
    (w : PqxdhRecordLiftWorld.State n) :
    Prod.map id uncount <$> (simulateQ PqxdhRecordLiftWorld.effects
        (PqxdhDeploymentEnvironment.issue (.appendOwner sender identity phase))).run w =
      pure ((), uncount { w with owners := w.owners ++ [.inactive phase] }) := by
  rw [effects_issue]
  simp only [PqxdhRecordLiftWorld.capability, StateT.run, map_pure]
  rfl

/-- A legal phase advance of an inactive owner, counts forgotten. -/
theorem effects_advance (owner : Nat) (before phase : InactivePhase) (w : PqxdhRecordLiftWorld.State n)
    (found : w.owners[owner]? = some (.inactive before)) (legal : PqxdhRecordLiftWorld.LegalAdvance before phase) :
    Prod.map id uncount <$> (simulateQ PqxdhRecordLiftWorld.effects
        (PqxdhDeploymentEnvironment.issue (.advanceOwner owner phase))).run w =
      pure ((), uncount { w with owners := w.owners.set owner (.inactive phase) }) := by
  rw [effects_issue]
  have found' : (PqxdhRecordLiftWorld.chargeEffect (.inr (.advanceOwner owner phase)) w).owners[owner]? =
      some (.inactive before) := found
  simp only [PqxdhRecordLiftWorld.capability, StateT.run, found', legal, ite_true, map_pure]
  rfl

/-- The World's Server record with one more peer installed. -/
def installPeer (world : PqxdhRecordLiftWorld.Server) (keyId : Std.U64) (identity : RawCtxServerRouting.Identity)
    (kernel : ConcreteRatchetKernel) : PqxdhRecordLiftWorld.Server :=
  { world with records := { world.records with server := { world.records.server with
    peers := Function.update world.records.server.peers keyId (some ⟨identity, kernel, ()⟩) } } }

/-- A known Server installation at a vacant key ID, counts forgotten. -/
theorem effects_installServer (keyId : Std.U64) (identity : RawCtxServerRouting.Identity) (kernel : ConcreteRatchetKernel)
    (w : PqxdhRecordLiftWorld.State n) (world : PqxdhRecordLiftWorld.Server) (found : w.server = some world)
    (vacant : world.records.server.peers keyId = none) :
    Prod.map id uncount <$> (simulateQ PqxdhRecordLiftWorld.effects
        (PqxdhDeploymentEnvironment.issue (.installServer keyId identity (.known kernel)))).run w =
      pure ((), uncount { w with server := some (installPeer world keyId identity kernel) }) := by
  rw [effects_issue]
  have found' : (PqxdhRecordLiftWorld.chargeEffect (.inr (.installServer keyId identity (.known kernel))) w).server =
      some world := found
  simp only [PqxdhRecordLiftWorld.capability, PqxdhRecordLiftWorld.installServer, StateT.run, found', vacant,
    PqxdhRecordLiftWorld.Unused, and_self, ite_true, PqxdhRecordLiftWorld.resolve]
  rfl

/-- A known Beacon installation at an initSent owner, counts forgotten. -/
theorem effects_installBeacon (owner : Nat) (shell : BeaconShell) (kernel : ConcreteRatchetKernel)
    (w : PqxdhRecordLiftWorld.State n) (ready : w.owners[owner]? = some (.inactive .initSent)) :
    Prod.map id uncount <$> (simulateQ PqxdhRecordLiftWorld.effects
        (PqxdhDeploymentEnvironment.issue (.installBeacon owner shell (.known kernel)))).run w =
      pure ((), uncount { w with owners := w.owners.set owner (.established shell kernel) }) := by
  rw [effects_issue]
  have ready' : PqxdhRecordLiftWorld.BeaconReady
      (PqxdhRecordLiftWorld.chargeEffect (.inr (.installBeacon owner shell (.known kernel))) w) owner := ready
  simp only [PqxdhRecordLiftWorld.capability, PqxdhRecordLiftWorld.installBeacon, StateT.run, ready',
    PqxdhRecordLiftWorld.Unused, and_self, ite_true, PqxdhRecordLiftWorld.resolve]
  rfl

/-- A program whose World run, counts forgotten, does not depend on the World's counts. -/
def CountFree {α : Type} (work : OracleComp (EnvEffects n) α) : Prop :=
  ∀ w, Prod.map id uncount <$> (simulateQ PqxdhRecordLiftWorld.effects work).run w =
    Prod.map id uncount <$> (simulateQ PqxdhRecordLiftWorld.effects work).run (uncount w)

/-- A pure program is count-free. -/
theorem countFree_pure {α : Type} (value : α) : CountFree (n := n) (pure value) := fun _ => by
  simp only [simulateQ_pure, StateT.run_pure, map_pure]
  rfl

/-- Count-free programs are closed under `bind`. -/
theorem countFree_bind {α β : Type} {first : OracleComp (EnvEffects n) α} {next : α → OracleComp (EnvEffects n) β}
    (head : CountFree first) (rest : ∀ value, CountFree (next value)) : CountFree (first >>= next) := fun w => by
  simp only [simulateQ_bind, StateT.run_bind, map_bind]
  calc _ = (simulateQ PqxdhRecordLiftWorld.effects first).run w >>= fun result : α × PqxdhRecordLiftWorld.State n =>
          Prod.map id uncount <$> (simulateQ PqxdhRecordLiftWorld.effects (next result.1)).run (uncount result.2) :=
        bind_congr fun (result : α × PqxdhRecordLiftWorld.State n) => rest result.1 result.2
    _ = (Prod.map id uncount <$> (simulateQ PqxdhRecordLiftWorld.effects first).run w) >>= fun result : α × PqxdhRecordLiftWorld.State n =>
          Prod.map id uncount <$> (simulateQ PqxdhRecordLiftWorld.effects (next result.1)).run result.2 := by
        rw [bind_map_left]
        rfl
    _ = (Prod.map id uncount <$> (simulateQ PqxdhRecordLiftWorld.effects first).run (uncount w)) >>= fun result : α × PqxdhRecordLiftWorld.State n =>
          Prod.map id uncount <$> (simulateQ PqxdhRecordLiftWorld.effects (next result.1)).run result.2 := by
        rw [head w]
    _ = (simulateQ PqxdhRecordLiftWorld.effects first).run (uncount w) >>= fun result : α × PqxdhRecordLiftWorld.State n =>
          Prod.map id uncount <$> (simulateQ PqxdhRecordLiftWorld.effects (next result.1)).run (uncount result.2) := by
        rw [bind_map_left]
        rfl
    _ = _ := (bind_congr fun (result : α × PqxdhRecordLiftWorld.State n) => rest result.1 result.2).symm

/-- An administrative capability with no BLAKE2b query and no hidden kernel: the record-relevant requests of the real environment. -/
def KnownAdmin : Capability n → Prop
  | .hash _ => False
  | .installServer _ _ (.hidden _) => False
  | .installBeacon _ _ (.hidden _) => False
  | _ => True

/-- An administrative request with no BLAKE2b query and no hidden kernel is count-free. -/
theorem countFree_issue (capability : Capability n) (known : KnownAdmin capability) :
    CountFree (PqxdhDeploymentEnvironment.issue capability) := fun w => by
  rw [effects_issue, effects_issue]
  cases capability with
  | hash bytes => exact known.elim
  | installServer keyId identity kernel =>
      cases kernel with
      | hidden slot => exact known.elim
      | known kernel =>
          simp only [PqxdhRecordLiftWorld.capability, PqxdhRecordLiftWorld.installServer, PqxdhRecordLiftWorld.chargeEffect,
            uncount, StateT.run]
          cases w.server with
          | none => rfl
          | some world =>
              simp only [PqxdhRecordLiftWorld.Unused, and_true, PqxdhRecordLiftWorld.resolve]
              split_ifs <;> rfl
  | installBeacon owner shell kernel =>
      cases kernel with
      | hidden slot => exact known.elim
      | known kernel =>
          simp only [PqxdhRecordLiftWorld.capability, PqxdhRecordLiftWorld.installBeacon, PqxdhRecordLiftWorld.chargeEffect,
            uncount, PqxdhRecordLiftWorld.BeaconReady, PqxdhRecordLiftWorld.Unused, and_true, StateT.run]
          by_cases ready : w.owners[owner]? = some (.inactive .initSent)
          · simp only [ready]
            rfl
          · simp only [ready]
            rfl
  | advanceOwner owner phase =>
      simp only [PqxdhRecordLiftWorld.capability, PqxdhRecordLiftWorld.chargeEffect, uncount, StateT.run]
      split
      · split <;> rfl
      · rfl
  | _ => rfl

/-- A program without administrative effect followed by count-free continuations: the program read through `ctxEffects` on the World's cache, then each continuation from the counts-free World with the resulting cache. -/
theorem effects_then_free {α β : Type} (work : OracleComp (EnvEffects n) α)
    (noAdmin : work.IsQueryBoundP (fun effect => effectKind effect = .administrative) 0)
    (next : α → OracleComp (EnvEffects n) β) (free : ∀ value, CountFree (next value)) (w : PqxdhRecordLiftWorld.State n) :
    Prod.map id uncount <$> (simulateQ PqxdhRecordLiftWorld.effects (work >>= next)).run w =
      (simulateQ (ctxEffects admin) work).run w.primitive.2 >>= fun result =>
        Prod.map id uncount <$> (simulateQ PqxdhRecordLiftWorld.effects (next result.1)).run (withCache w result.2) :=
  effects_then admin work noAdmin next
    (fun value world => Prod.map id uncount <$> (simulateQ PqxdhRecordLiftWorld.effects (next value)).run world)
    (fun value world => free value world) w

/-- Publishing one owner's change is count-free. -/
theorem countFree_ownerEffect (index : Nat) (before after : PqxdhRegistrationSchedule.Owner KemSK) :
    CountFree (PqxdhDeploymentEnvironment.ownerEffect (n := n) index before after) := by
  unfold PqxdhDeploymentEnvironment.ownerEffect
  split
  · exact countFree_pure _
  · exact countFree_issue _ trivial
  · split
    · split
      · exact countFree_pure _
      · exact countFree_issue _ trivial
    · exact countFree_pure _

/-- Publishing the change of one owner between two owner lists is count-free. -/
theorem countFree_ownerChange (index : Nat) (before after : List (PqxdhRegistrationSchedule.Owner KemSK)) :
    CountFree (PqxdhDeploymentEnvironment.ownerChange (n := n) index before after) := by
  unfold PqxdhDeploymentEnvironment.ownerChange
  split
  · exact countFree_ownerEffect _ _ _
  · exact countFree_pure _

/-- Publishing a Server build is count-free. -/
theorem countFree_serverEffect (settled : Option PqxdhServerRegistrationPublication.Response ×
    PqxdhServerRegistrationPublication.State Unit Unit (List Pqxdh.Bytes)) :
    CountFree (PqxdhDeploymentEnvironment.serverEffect (n := n) settled) := by
  unfold PqxdhDeploymentEnvironment.serverEffect
  split
  · exact countFree_pure _
  · split
    · exact countFree_pure _
    · exact countFree_issue _ trivial

end Bridge

/-! ### Frames of a map of the game state -/

section Frames

/-- A step of the shared native state commutes with a map of its game component. -/
def NFrame (f : GameState KemSK → GameState KemSK) {α : Type} (step : NativeGame KemSK α) : Prop :=
  ∀ family game, step.run (family, f game) = (fun result => (result.1, (result.2.1, f result.2.2))) <$>
    step.run (family, game)

variable (f : GameState KemSK → GameState KemSK)

/-- A pure step is a frame. -/
theorem nframe_pure {α : Type} (value : α) : NFrame f (pure value : NativeGame KemSK α) :=
  fun _ _ => by simp only [StateT.run_pure, map_pure]

/-- Frames are closed under `bind`. -/
theorem nframe_bind {α β : Type} {first : NativeGame KemSK α} {next : α → NativeGame KemSK β}
    (frame : NFrame f first) (rest : ∀ value, NFrame f (next value)) : NFrame f (first >>= next) :=
  fun family game => by
    simp only [StateT.run_bind, frame family game, bind_map_left, map_bind]
    exact bind_congr fun result => rest result.1 result.2.1 result.2.2

/-- A local step of the game state is a frame when it commutes with the map. -/
theorem nframe_local {α : Type} (step : GameState KemSK → α × GameState KemSK)
    (commute : ∀ game, step (f game) = ((step game).1, f (step game).2)) :
    NFrame f (PqxdhServerAuthNative.localState step) :=
  fun family game => by
    show (pure ((step (f game)).1, (family, (step (f game)).2)) : ProbComp (α × NativeState KemSK)) =
      (fun result => (result.1, (result.2.1, f result.2.2))) <$>
        (pure ((step game).1, (family, (step game).2)) : ProbComp (α × NativeState KemSK))
    rw [commute, map_pure]

/-- A step of the Extract family alone is a frame. -/
theorem nframe_family {α : Type} (work : StateT PqxdhJointDhExtractFamily.State ProbComp α) :
    NFrame f (fun state => (fun result => (result.1, (result.2, state.2))) <$> work.run state.1 : NativeGame KemSK α) :=
  fun family game => by
    simp only [StateT.run, Functor.map_map]

/-- An ordinary probabilistic computation is a frame. -/
theorem nframe_coins {α : Type} (work : ProbComp α) : NFrame f (PqxdhServerAuthNative.nativeCoins (KemSK := KemSK) work) :=
  fun family game => by
    simp only [PqxdhServerAuthNative.nativeCoins, StateT.run, Functor.map_map]

/-- A program of frame steps is a frame. -/
theorem nframe_simulateQ {ι' α : Type} {spec' : OracleSpec ι'} (impl : QueryImpl spec' (NativeGame KemSK))
    (steps : ∀ query, NFrame f (impl query)) (work : OracleComp spec' α) : NFrame f (simulateQ impl work) := by
  intro family game
  induction work using OracleComp.inductionOn generalizing family game with
  | pure value => simp only [simulateQ_pure, StateT.run_pure, map_pure]
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, id_map,
        StateT.run_bind, steps query family game, bind_map_left, map_bind]
      exact bind_congr fun result => ih result.1 result.2.1 result.2.2

/-- A frame step from a state that the map fixes ends in the image of the map. -/
theorem nframe_fixed {α : Type} {step : NativeGame KemSK α} (frame : NFrame f step) (family : PqxdhJointDhExtractFamily.State)
    (game : GameState KemSK) (fixed : f game = game) :
    ∀ result ∈ support (step.run (family, game)), ∃ inner, result.2.2 = f inner := by
  intro result supported
  have same := frame family game
  rw [fixed] at same
  rw [same, support_map] at supported
  obtain ⟨inner, _, rfl⟩ := supported
  exact ⟨inner.2.2, rfl⟩

/-- The game state with the CTX cache, the Server's routing record (identity and peer map) and its identity key ID replaced: the record coordinates that the reassembly fills in, with the key ID the step must keep. -/
def frameGame (cache : CtxRomAuth.CtxRO.QueryCache) (server : RawCtxServerRouting.Server Unit Unit) (keyId : Std.U64)
    (game : GameState KemSK) : GameState KemSK :=
  { game with ctx := cache, server := { game.server with server := server, identityKeyId := keyId } }

/-- The game state with the Server's routing record and identity key ID replaced, the CTX cache kept. -/
def serverGame (server : RawCtxServerRouting.Server Unit Unit) (keyId : Std.U64) (game : GameState KemSK) :
    GameState KemSK :=
  { game with server := { game.server with server := server, identityKeyId := keyId } }

end Frames

section Native
variable {ι : Type} {baseSpec : OracleSpec ι} {Reader Response : Type}
  (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
  (cache : CtxRomAuth.CtxRO.QueryCache) (server : RawCtxServerRouting.Server Unit Unit) (keyId : Std.U64)

/-- The native public HMAC reads and writes only the Extract family and the touch log. -/
theorem nativeHmac_nframe (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (key : PqxdhSecretInputKdf.HmacBlock) (message : Pqxdh.Bytes) :
    NFrame (frameGame cache server keyId) (PqxdhServerAuthNative.nativeHmac setup seed scalar key message) := by
  unfold PqxdhServerAuthNative.nativeHmac
  dsimp only
  split
  · exact nframe_bind _ (nframe_local _ _ fun _ => rfl) fun _ => nframe_family _ _
  · exact nframe_family _ _

/-- The native ROM root of a Server session reads and writes only the Extract family. -/
theorem romRoot_nframe {E : Type} (hmac : PqxdhSecretInputKdf.HmacSha512)
    (input : PqxdhServerRootPreparation.Inputs Reader E PqxdhBeaconPhase2Preparation.Word32)
    (original : beaconcrypt_core.pqxdh.PendingServerRegistration) :
    NFrame (frameGame cache server keyId) (PqxdhServerAuthNative.romRoot (A := GameState KemSK) hmac input original) :=
  fun family game => by
    simp only [PqxdhServerAuthNative.romRoot, PqxdhServerAuthNative.romRootBytes, StateT.run, Functor.map_map]

/-- The native Server client (core acceptance, root, touch and consumption) reads and writes no record coordinate. -/
theorem nativeClient_nframe (hmac : PqxdhSecretInputKdf.HmacSha512) (index : Nat)
    (control : beaconcrypt_core.pqxdh.ServerState) (binding : beaconcrypt_core.pqxdh.ServerBinding)
    (input : PqxdhServerRootPreparation.Inputs Reader PqxdhJointGapDh.ScalarBytes PqxdhBeaconPhase2Preparation.Word32) :
    NFrame (frameGame cache server keyId) (PqxdhServerAuthNative.nativeClient (KemSK := KemSK) hmac index control binding input) := by
  unfold PqxdhServerAuthNative.nativeClient
  split
  · exact nframe_pure _ _
  · exact nframe_pure _ _
  · exact nframe_pure _ _
  · refine nframe_bind _ ?_ fun root => nframe_bind _ (nframe_local _ _ fun _ => rfl) fun _ => nframe_pure _ _
    unfold PqxdhServerAuthNative.loggedRoot
    exact nframe_bind _ (romRoot_nframe cache server keyId hmac _ _) fun root =>
      nframe_bind _ (nframe_local _ _ fun _ => rfl) fun _ => nframe_pure _ _

/-- The accept tail after the native allocation reads and writes no record coordinate. -/
theorem acceptRest_nframe (publicIdentity : PqxdhJointIdentity.PublicIdentity) (game : GameState KemSK)
    (collected : Option (PqxdhServerRootPreparation.Inputs Reader PqxdhJointGapDh.ScalarBytes
      PqxdhBeaconPhase2Preparation.Word32) × List Pqxdh.Bytes) :
    NFrame (frameGame cache server keyId) (PqxdhDeploymentBackend.acceptRest setup publicIdentity game collected) := by
  unfold PqxdhDeploymentBackend.acceptRest
  rcases collected with ⟨_ | input, consumed⟩
  · exact nframe_pure _ _
  · refine nframe_bind _ (nativeClient_nframe cache server keyId _ _ _ _ _) fun returned => ?_
    rcases returned with (_ | token) | _ | _
    all_goals first
      | exact nframe_pure _ _
      | exact nframe_bind _ (nframe_local _ _ fun _ => rfl) fun _ => nframe_pure _ _

/-- The native logged raw accept reads and writes no record coordinate: it commutes with replacing the CTX cache, the Server's routing record and its identity key ID. -/
theorem acceptLogged_nframe (seed : PqxdhJointIdentity.IdentitySeed) (raw : Pqxdh.Bytes) :
    NFrame (frameGame cache server keyId) (PqxdhDeploymentLaterServerNative.acceptLogged setup codec checks seed raw) := by
  intro family game
  unfold PqxdhDeploymentLaterServerNative.acceptLogged
  rw [PqxdhDeploymentBackend.nativeGet_bind, PqxdhDeploymentBackend.nativeGet_bind,
    PqxdhDeploymentBackend.nativeCoins_bind, PqxdhDeploymentBackend.nativeCoins_bind, map_bind]
  refine bind_congr fun collected => ?_
  rw [PqxdhDeploymentBackend.tail_eq, PqxdhDeploymentBackend.tail_eq, bind_assoc, bind_assoc,
    PqxdhDeploymentBackend.nativeSet_run_bind, PqxdhDeploymentBackend.nativeSet_run_bind]
  exact (nframe_bind _ (acceptRest_nframe setup cache server keyId _ game _) fun _ => nframe_pure _ _) family
    { game with sessions := game.sessions + 1, server := { game.server with consumed := collected.2 } }

/-- Every Beacon finish callback commutes with replacing the Server's routing record and identity key ID: preparation is stateless, and the root and tail callbacks touch only the Extract family and the CTX cache. -/
theorem callbacks_nframe
    (query : (PqxdhBeaconPhase2Publication.NativeSpec PqxdhJointIdentity.IdentitySeed PqxdhJointGapDh.ScalarBytes
      (PqxdhKemIndCca.MlKem768PublicKey × KemSK) PqxdhJointIdentity.IdentitySeed Response).Domain) :
    NFrame (serverGame server keyId) (PqxdhRegistrationSchedule.callbacks setup codec query) := by
  intro family game
  rcases query with query | query
  · simp only [PqxdhRegistrationSchedule.callbacks, PqxdhServerAuthNative.nativeCoins, StateT.run, Functor.map_map]
  · rcases query with query | query
    · simp only [PqxdhRegistrationSchedule.callbacks, PqxdhServerAuthNative.sourceBeaconTail,
        PqxdhPhase2DhRootConsumer.withRoot, PqxdhServerAuthNative.nativeCtx, StateT.run, Functor.map_map]
      rfl
    · cases query with
      | root input =>
          simp only [PqxdhRegistrationSchedule.callbacks, PqxdhServerAuthNative.sourceBeaconTail,
            PqxdhPhase2DhRootConsumer.withRoot, PqxdhServerAuthNative.sourceRoot, StateT.run, Functor.map_map]
      | _ =>
          simp only [PqxdhRegistrationSchedule.callbacks, PqxdhServerAuthNative.sourceBeaconTail,
            PqxdhPhase2DhRootConsumer.withRoot, PqxdhServerAuthNative.nativeCtx, StateT.run, Functor.map_map]
          rfl

end Native

/-! ### Reassembly algebra -/

section Fill
variable {n : Nat}

/-- With an initialized World Server, filling replaces the game state's CTX cache and Server routing record (`frameGame`) and fills the owners. -/
theorem fill_some (w : PqxdhRecordLiftWorld.State n) (world : PqxdhRecordLiftWorld.Server) (found : w.server = some world)
    (state : PqxdhRegistrationSchedule.State KemSK) :
    fill w state =
      { shared := (state.shared.1, frameGame w.primitive.2 world.records.server state.shared.2.server.identityKeyId state.shared.2)
        owners := state.owners.mapIdx fun index owner => fillOwner (w.owners[index]?) owner } := by
  simp only [fill, fillServer, found]
  rfl

/-- The registration owners agree with the World's owners phase by phase up to their kernels. -/
def Matched (w : PqxdhRecordLiftWorld.State n) (owners : List (PqxdhRegistrationSchedule.Owner KemSK)) : Prop :=
  ∀ (index : Nat) (owner : PqxdhRegistrationSchedule.Owner KemSK), owners[index]? = some owner →
    (w.owners[index]?).map stripPhase = some (stripPhase (PqxdhRecordLiftBeacon.projectPhase owner.beacon))

/-- Forgetting a World phase's kernel twice forgets it once. -/
theorem stripPhase_idem (phase : PqxdhRecordLiftBeacon.Phase) : stripPhase (stripPhase phase) = stripPhase phase := by
  cases phase <;> rfl

/-- The record view of a stripped owner is the record view of the owner with its kernel forgotten. -/
theorem projectPhase_stripOwner (owner : PqxdhRegistrationSchedule.Owner KemSK) :
    PqxdhRecordLiftBeacon.projectPhase (stripOwner owner).beacon = stripPhase (PqxdhRecordLiftBeacon.projectPhase owner.beacon) := by
  unfold stripOwner
  cases phase : owner.beacon.phase <;> simp only [PqxdhRecordLiftBeacon.projectPhase, phase, stripPhase]

/-- A non-established owner has no kernel to strip. -/
theorem stripOwner_inactive (owner : PqxdhRegistrationSchedule.Owner KemSK)
    (inactive : ¬ RawCtxBeaconLifecycle.Established owner.beacon.phase) : stripOwner owner = owner := by
  unfold stripOwner
  cases phase : owner.beacon.phase <;> simp only [phase, RawCtxBeaconLifecycle.Established] at inactive ⊢
  exact absurd trivial inactive

/-- Filling a matched owner overwrites its stripped kernel. -/
theorem fillOwner_strip (phase : PqxdhRecordLiftBeacon.Phase) (owner : PqxdhRegistrationSchedule.Owner KemSK)
    (matched : stripPhase phase = stripPhase (PqxdhRecordLiftBeacon.projectPhase owner.beacon)) :
    fillOwner (some phase) (stripOwner owner) = fillOwner (some phase) owner := by
  cases phase with
  | inactive tag =>
      cases ownerPhase : owner.beacon.phase <;>
        simp only [stripPhase, PqxdhRecordLiftBeacon.projectPhase, ownerPhase, reduceCtorEq] at matched <;>
        simp only [fillOwner, stripOwner, ownerPhase]
  | established shell kernel =>
      cases ownerPhase : owner.beacon.phase <;>
        simp only [stripPhase, PqxdhRecordLiftBeacon.projectPhase, ownerPhase, reduceCtorEq] at matched
      simp only [fillOwner, stripOwner, ownerPhase]

/-- Filling a stripped state with a World that matches it is filling the state itself. -/
theorem fill_strip (w : PqxdhRecordLiftWorld.State n) (world : PqxdhRecordLiftWorld.Server) (found : w.server = some world)
    (state : PqxdhRegistrationSchedule.State KemSK) (matched : Matched w state.owners) :
    fill w (strip state) = fill w state := by
  rw [fill_some w world found, fill_some w world found]
  congr 1
  apply List.ext_getElem?
  intro index
  simp only [PqxdhDeploymentEnvironment.strip, List.getElem?_mapIdx, List.getElem?_map]
  cases owner : state.owners[index]? with
  | none => rfl
  | some owner' =>
      have consistent := matched index owner' owner
      cases phase : w.owners[index]? with
      | none => simp only [phase, Option.map_none, reduceCtorEq] at consistent
      | some phase' =>
          simp only [phase, Option.map_some, Option.some.injEq] at consistent
          simp only [Option.map_some]
          exact congrArg some (fillOwner_strip phase' owner' consistent)

/-- Filling an owner changes neither its prekey nor its one-time field. -/
theorem fillOwner_fields (phase : Option PqxdhRecordLiftBeacon.Phase) (owner : PqxdhRegistrationSchedule.Owner KemSK) :
    PqxdhRegistrationJointLiveRead.value .prekey (fillOwner phase owner) =
        PqxdhRegistrationJointLiveRead.value .prekey owner ∧
      PqxdhRegistrationJointLiveRead.value .oneTime (fillOwner phase owner) =
        PqxdhRegistrationJointLiveRead.value .oneTime owner := by
  unfold fillOwner
  split
  · rename_i shell kernel control associatedData stale ownerPhase
    simp only [PqxdhRegistrationJointLiveRead.value, PqxdhRegistrationJointLiveRead.localValue, ownerPhase, and_self]
  · exact ⟨rfl, rfl⟩

/-- The LQ snapshot of the filled owners is the snapshot of the owners. -/
theorem snapshotAt_fill (w : PqxdhRecordLiftWorld.State n) (state : PqxdhRegistrationSchedule.State KemSK)
    (snap : PqxdhDeploymentLater.Snap) (index : Option Nat) :
    PqxdhDeploymentLater.snapshotAt snap (fill w state).owners index =
      PqxdhDeploymentLater.snapshotAt snap state.owners index := by
  cases index with
  | none => rfl
  | some index =>
      simp only [PqxdhDeploymentLater.snapshotAt, PqxdhDeploymentLater.fieldOf, fill, List.getElem?_mapIdx]
      cases state.owners[index]? with
      | none => rfl
      | some owner =>
          simp only [Option.map_some, Option.bind_some, (fillOwner_fields _ owner).1, (fillOwner_fields _ owner).2]

/-- Filling with an inactive World phase changes nothing. -/
theorem fillOwner_inactive (tag : InactivePhase) (owner : PqxdhRegistrationSchedule.Owner KemSK) :
    fillOwner (some (.inactive tag)) owner = owner := by
  unfold fillOwner
  cases owner.beacon.phase <;> rfl

/-- An admissible environment state's owners match the World. -/
theorem good_matched {Bk : Type} (created : PqxdhLiveServerConstruction.Created Unit) (e : EnvState KemSK Bk)
    (w : PqxdhRecordLiftWorld.State n) (good : Good created e w) : Matched w e.native.owners := by
  intro index owner found
  have stripped : e.native.owners.map stripOwner = e.native.owners := congrArg PqxdhRegistrationSchedule.State.owners good.stripped
  have same : stripOwner owner = owner := by
    have mapped : (e.native.owners.map stripOwner)[index]? = some owner := by rw [stripped]; exact found
    rw [List.getElem?_map, found, Option.map_some, Option.some.injEq] at mapped
    exact mapped
  rw [good.owners index owner found, ← projectPhase_stripOwner, same]

/-- Admissibility of a stripped environment state from the World's Server record and matched owners. -/
theorem good_intro {Bk : Type} (created : PqxdhLiveServerConstruction.Created Unit) (e : EnvState KemSK Bk)
    (state : PqxdhRegistrationSchedule.State KemSK) (w : PqxdhRecordLiftWorld.State n) (world : PqxdhRecordLiftWorld.Server)
    (native : e.native = strip state) (createdEq : e.created = created) (found : w.server = some world)
    (sender : world.sender = state.shared.2.server.identityKeyId)
    (identity : world.records.server.identity = state.shared.2.server.server.identity)
    (peers : ∀ keyId, (world.records.server.peers keyId).map stripPeer =
      (state.shared.2.server.server.peers keyId).map stripPeer)
    (lengths : w.owners.length = state.owners.length) (matched : Matched w state.owners) :
    Good created e w := by
  rcases e with ⟨native', backend, snap, log, created'⟩
  simp only at native createdEq
  subst native
  refine ⟨PqxdhDeploymentEnvironment.strip_stripped state, createdEq, ⟨world, found, sender, identity, fun keyId => ?_⟩,
    by rw [lengths, PqxdhDeploymentEnvironment.strip_owners_length], fun index owner foundOwner => ?_⟩
  · rw [peers keyId]
    rfl
  · simp only [PqxdhDeploymentEnvironment.strip, List.getElem?_map] at foundOwner
    cases original : state.owners[index]? with
    | none => simp only [original, Option.map_none, reduceCtorEq] at foundOwner
    | some original' =>
        simp only [original, Option.map_some, Option.some.injEq] at foundOwner
        subst foundOwner
        rw [matched index original' original, projectPhase_stripOwner]

/-- Reassembly does not read the World's counts. -/
theorem merge_uncount {Bk : Type} (e : EnvState KemSK Bk) (w : PqxdhRecordLiftWorld.State n) : merge e (uncount w) = merge e w := rfl

/-- The reassembled law of a joint run is the reassembled law of its counts-free run. -/
theorem law_uncount {α Bk : Type} (run : ProbComp ((α × EnvState KemSK Bk) × PqxdhRecordLiftWorld.State n)) :
    (fun result => (result.1.1, merge result.1.2 result.2)) <$> run =
      (fun result => (result.1.1, merge result.1.2 result.2)) <$> (Prod.map id uncount <$> run) := by
  rw [Functor.map_map]
  rfl

/-- A property of joint outcomes that ignores the World's counts holds on a run when it holds on its counts-free run. -/
theorem keeps_uncount {α Bk : Type} (run : ProbComp ((α × EnvState KemSK Bk) × PqxdhRecordLiftWorld.State n))
    (property : EnvState KemSK Bk → PqxdhRecordLiftWorld.State n → Prop)
    (blind : ∀ e w, property e (uncount w) → property e w)
    (holds : ∀ result ∈ support (Prod.map id uncount <$> run), property result.1.2 result.2) :
    ∀ result ∈ support run, property result.1.2 result.2 := by
  intro result supported
  apply blind
  exact holds (Prod.map id uncount result) (by rw [support_map]; exact ⟨result, supported, rfl⟩)

/-- Admissibility does not read the World's counts. -/
theorem good_uncount {Bk : Type} (created : PqxdhLiveServerConstruction.Created Unit) (e : EnvState KemSK Bk)
    (w : PqxdhRecordLiftWorld.State n) (good : Good created e (uncount w)) : Good created e w :=
  ⟨good.1, good.2, good.3, good.4, good.5⟩

/-- Appending one owner on both sides keeps the owners matched, when the new owner is fresh. -/
theorem matched_append (w : PqxdhRecordLiftWorld.State n) (owners : List (PqxdhRegistrationSchedule.Owner KemSK))
    (matched : Matched w owners) (lengths : w.owners.length = owners.length) (owner : PqxdhRegistrationSchedule.Owner KemSK)
    (fresh : PqxdhRecordLiftBeacon.projectPhase owner.beacon = .inactive .fresh) :
    Matched { w with owners := w.owners ++ [.inactive .fresh] } (owners ++ [owner]) := by
  intro index current found
  by_cases below : index < owners.length
  · rw [List.getElem?_append_left below] at found
    have previous := matched index current found
    show ((w.owners ++ [.inactive .fresh])[index]?).map stripPhase = _
    rw [List.getElem?_append_left (by omega)]
    exact previous
  · have bound : index < owners.length + 1 := by
      have := (List.getElem?_eq_some_iff.mp found).1
      simpa only [List.length_append, List.length_singleton] using this
    have same : index = owners.length := by omega
    subst same
    rw [List.getElem?_concat_length, Option.some.injEq] at found
    subst found
    show ((w.owners ++ [.inactive .fresh])[owners.length]?).map stripPhase = _
    rw [← lengths, List.getElem?_concat_length, fresh]
    rfl

/-- Filling owners with one fresh owner appended on both sides appends the owner. -/
theorem fill_append_owner (w : PqxdhRecordLiftWorld.State n) (owners : List (PqxdhRegistrationSchedule.Owner KemSK))
    (lengths : w.owners.length = owners.length) (owner : PqxdhRegistrationSchedule.Owner KemSK) :
    (owners ++ [owner]).mapIdx (fun index current => fillOwner ((w.owners ++ [.inactive .fresh])[index]?) current) =
      owners.mapIdx (fun index current => fillOwner (w.owners[index]?) current) ++ [owner] := by
  rw [List.mapIdx_concat, ← lengths, List.getElem?_concat_length, fillOwner_inactive]
  congr 1
  apply List.ext_getElem?
  intro index
  simp only [List.getElem?_mapIdx]
  cases found : owners[index]? with
  | none => rfl
  | some current =>
      have below : index < w.owners.length := by
        rw [lengths]
        exact (List.getElem?_eq_some_iff.mp found).1
      simp only [Option.map_some, List.getElem?_append_left below]

/-- The Server clause of admissibility in the form `good_intro` takes. -/
theorem good_server {Bk : Type} (created : PqxdhLiveServerConstruction.Created Unit) (e : EnvState KemSK Bk)
    (w : PqxdhRecordLiftWorld.State n) (good : Good created e w) :
    ∃ world, w.server = some world ∧ world.sender = e.native.shared.2.server.identityKeyId ∧
      world.records.server.identity = e.native.shared.2.server.server.identity ∧
      ∀ keyId, (world.records.server.peers keyId).map stripPeer = (e.native.shared.2.server.server.peers keyId).map stripPeer := by
  obtain ⟨world, found, sender, identity, peers⟩ := good.server
  refine ⟨world, found, sender, identity, fun keyId => ?_⟩
  rw [← peers keyId, Option.map_map, PqxdhDeploymentEnvironment.stripPeer_comp]

/-- Admissibility does not read the World's counts (converse of `good_uncount`). -/
theorem uncount_good {Bk : Type} (created : PqxdhLiveServerConstruction.Created Unit) (e : EnvState KemSK Bk)
    (w : PqxdhRecordLiftWorld.State n) (good : Good created e w) : Good created e (uncount w) :=
  ⟨good.1, good.2, good.3, good.4, good.5⟩

/-- Filling the owners after one owner and its World phase change is filling them and then setting that owner. -/
theorem fill_set (owners : List (PqxdhRegistrationSchedule.Owner KemSK)) (phases : List PqxdhRecordLiftBeacon.Phase)
    (index : Nat) (owner : PqxdhRegistrationSchedule.Owner KemSK) (phase : PqxdhRecordLiftBeacon.Phase)
    (below : index < owners.length) (lengths : phases.length = owners.length) :
    (owners.set index owner).mapIdx (fun i current => fillOwner ((phases.set index phase)[i]?) current) =
      (owners.mapIdx (fun i current => fillOwner (phases[i]?) current)).set index (fillOwner (some phase) owner) := by
  apply List.ext_getElem?
  intro i
  by_cases same : index = i
  · subst same
    rw [List.getElem?_mapIdx, List.getElem?_set_self below, List.getElem?_set_self (by omega),
      List.getElem?_set_self (by simpa only [List.length_mapIdx] using below)]
    rfl
  · rw [List.getElem?_mapIdx, List.getElem?_set_ne same, List.getElem?_set_ne same, List.getElem?_set_ne same,
      List.getElem?_mapIdx]

/-- Changing one owner and its World phase consistently keeps the owners matched. -/
theorem matched_set (w : PqxdhRecordLiftWorld.State n) (owners : List (PqxdhRegistrationSchedule.Owner KemSK))
    (matched : Matched w owners) (index : Nat) (owner : PqxdhRegistrationSchedule.Owner KemSK)
    (phase : PqxdhRecordLiftBeacon.Phase) (below : index < w.owners.length)
    (consistent : stripPhase phase = stripPhase (PqxdhRecordLiftBeacon.projectPhase owner.beacon)) :
    Matched { w with owners := w.owners.set index phase } (owners.set index owner) := by
  intro i current found
  by_cases same : index = i
  · subst same
    have bound : index < owners.length := by
      have := (List.getElem?_eq_some_iff.mp found).1
      simpa only [List.length_set] using this
    rw [List.getElem?_set_self bound, Option.some.injEq] at found
    subst found
    show ((w.owners.set index phase)[index]?).map stripPhase = _
    rw [List.getElem?_set_self below, Option.map_some, consistent]
  · rw [List.getElem?_set_ne same] at found
    show ((w.owners.set index phase)[i]?).map stripPhase = _
    rw [List.getElem?_set_ne same]
    exact matched i current found

/-- A matched owner that is not established is left alone by filling. -/
theorem fill_inactive (w : PqxdhRecordLiftWorld.State n) (owners : List (PqxdhRegistrationSchedule.Owner KemSK))
    (matched : Matched w owners) (index : Nat) (owner : PqxdhRegistrationSchedule.Owner KemSK)
    (found : owners[index]? = some owner) (inactive : ¬ RawCtxBeaconLifecycle.Established owner.beacon.phase) :
    ∃ tag, w.owners[index]? = some (.inactive tag) ∧ PqxdhRecordLiftBeacon.projectPhase owner.beacon = .inactive tag ∧
      fillOwner (w.owners[index]?) owner = owner := by
  have consistent := matched index owner found
  cases phase : owner.beacon.phase <;> simp only [phase, RawCtxBeaconLifecycle.Established, not_true_eq_false] at inactive
  all_goals
    cases world : w.owners[index]? with
    | none => simp only [world, Option.map_none, reduceCtorEq] at consistent
    | some phase' =>
        simp only [world, Option.map_some, Option.some.injEq, PqxdhRecordLiftBeacon.projectPhase, phase] at consistent
        cases phase' with
        | established shell kernel => simp only [stripPhase, reduceCtorEq] at consistent
        | inactive tag =>
            simp only [stripPhase, PqxdhRecordLiftBeacon.Phase.inactive.injEq] at consistent
            subst consistent
            exact ⟨_, rfl, by simp only [PqxdhRecordLiftBeacon.projectPhase, phase], fillOwner_inactive _ owner⟩

end Fill

/-! ### Steps of the shared native state that read no record coordinate -/

section Shared
variable {n : Nat} {α : Type} (work : NativeGame KemSK α)
  (frame : ∀ cache server keyId, NFrame (frameGame cache server keyId) work)

/-- Mapping a computation by two functions that agree on its support. -/
theorem map_congr_support {β γ : Type} (run : ProbComp β) (f g : β → γ) (agree : ∀ value ∈ support run, f value = g value) :
    f <$> run = g <$> run := by
  rw [map_eq_bind_pure_comp, map_eq_bind_pure_comp]
  exact OracleComp.bind_congr_of_forall_mem_support run fun value member => congrArg pure (agree value member)

include frame in
/-- Such a step keeps the CTX cache, the Server's routing record and its identity key ID. -/
theorem shared_outcome (shared : NativeState KemSK) :
    ∀ result ∈ support (work.run shared), result.2.2.ctx = shared.2.ctx ∧
      result.2.2.server.server = shared.2.server.server ∧
      result.2.2.server.identityKeyId = shared.2.server.identityKeyId := by
  intro result supported
  obtain ⟨inner, same⟩ := nframe_fixed _ (frame shared.2.ctx shared.2.server.server shared.2.server.identityKeyId)
    shared.1 shared.2 rfl result supported
  rw [same]
  exact ⟨rfl, rfl, rfl⟩

include frame in
/-- Such a step on the reassembled state is the step on the environment's state, the record coordinates filled after. -/
theorem shared_run {Bk : Type} (e : EnvState KemSK Bk) (w : PqxdhRecordLiftWorld.State n)
    (world : PqxdhRecordLiftWorld.Server) (found : w.server = some world) :
    work.run (fill w e.native).shared = (fun result => (result.1, (result.2.1, frameGame w.primitive.2 world.records.server
      e.native.shared.2.server.identityKeyId result.2.2))) <$> work.run e.native.shared := by
  rw [fill_some w world found]
  exact frame _ _ _ e.native.shared.1 e.native.shared.2

include frame in
/-- Reassembling the environment's state after such a step is the filled step. -/
theorem shared_fill {Bk : Type} (created : PqxdhLiveServerConstruction.Created Unit) (e : EnvState KemSK Bk)
    (w : PqxdhRecordLiftWorld.State n) (good : Good created e w) (world : PqxdhRecordLiftWorld.Server)
    (found : w.server = some world) (result : α × NativeState KemSK) (supported : result ∈ support (work.run e.native.shared)) :
    fill w (strip { e.native with shared := result.2 }) =
      { fill w e.native with shared := (result.2.1, frameGame w.primitive.2 world.records.server
        e.native.shared.2.server.identityKeyId result.2.2) } := by
  rw [fill_strip w world found { e.native with shared := result.2 } (good_matched created e w good),
    fill_some w world found, fill_some w world found]
  rw [(shared_outcome work frame e.native.shared result supported).2.2]

include frame in
/-- Such a step keeps admissibility. -/
theorem shared_good {Bk : Type} (created : PqxdhLiveServerConstruction.Created Unit) (e e' : EnvState KemSK Bk)
    (w : PqxdhRecordLiftWorld.State n) (good : Good created e w) (result : α × NativeState KemSK)
    (supported : result ∈ support (work.run e.native.shared))
    (native : e'.native = strip { e.native with shared := result.2 }) (createdEq : e'.created = e.created) :
    Good created e' w := by
  obtain ⟨world, found, sender, identity, peers⟩ := good_server created e w good
  obtain ⟨_, routing, keyId⟩ := shared_outcome work frame e.native.shared result supported
  refine good_intro created e' _ w world native (createdEq.trans good.createdEq) found ?_ ?_ ?_ good.ownersLength
    (good_matched created e w good)
  · rw [sender, keyId]
  · rw [identity, routing]
  · intro keyId'
    rw [peers keyId', routing]

end Shared

/-! ### Shapes of the Phase 1 bundle and of the Server build -/

section Shapes
variable {I D K : Type}

/-- A Phase 1 bundle leaves its owner unchanged, or publishes it (initSent) from a fresh phase, with or without retained coins. -/
def Bundled (before after : RawCtxBeaconLifecycle.State I D K) : Prop :=
  after = before ∨ ((∃ control prekey oneTime kem, after = { before with beacon := { before.beacon with
    phase := .initSent control prekey oneTime kem } }) ∧
    (PqxdhDeploymentEnvironment.inactiveTag before.beacon.phase = some .fresh ∨
      PqxdhDeploymentEnvironment.inactiveTag before.beacon.phase = some .freshWithCoins))

/-- The writer step of a bundle. -/
theorem afterSigning_shape (identity : Std.Array Std.U8 32#usize) (candidate : PqxdhEd25519EufCma.Phase1Candidate)
    (generated : Option D) (state : RawCtxBeaconLifecycle.State I D K)
    (fresh : PqxdhDeploymentEnvironment.inactiveTag state.beacon.phase = some .fresh ∨
      PqxdhDeploymentEnvironment.inactiveTag state.beacon.phase = some .freshWithCoins) :
    ∀ result ∈ support (PqxdhBeaconPhase1Publication.afterSigning identity candidate generated state),
      Bundled state result.2 := by
  intro result supported
  unfold PqxdhBeaconPhase1Publication.afterSigning at supported
  split at supported
  · simp only [support_pure, Set.mem_singleton_iff] at supported
    subst supported
    exact Or.inl rfl
  · rw [mem_support_bind_iff] at supported
    obtain ⟨serialized, _, member⟩ := supported
    cases serialized with
    | none =>
        simp only [support_pure, Set.mem_singleton_iff] at member
        subst member
        exact Or.inl rfl
    | some bytes =>
        simp only [support_pure, Set.mem_singleton_iff] at member
        subst member
        exact Or.inr ⟨⟨_, _, _, _, rfl⟩, fresh⟩

/-- The signing and writing steps of a bundle. -/
theorem afterGenerated_shape (projection : PqxdhLivePhase1Bundle.Public I D K) (generated : Option D)
    (state : RawCtxBeaconLifecycle.State I D K)
    (fresh : PqxdhDeploymentEnvironment.inactiveTag state.beacon.phase = some .fresh ∨
      PqxdhDeploymentEnvironment.inactiveTag state.beacon.phase = some .freshWithCoins) :
    ∀ result ∈ support (PqxdhLivePhase1Bundle.afterGenerated projection generated state), Bundled state result.2 := by
  intro result supported
  unfold PqxdhLivePhase1Bundle.afterGenerated at supported
  split at supported
  · simp only [support_pure, Set.mem_singleton_iff] at supported
    subst supported
    exact Or.inl rfl
  · rw [mem_support_bind_iff] at supported
    obtain ⟨candidate, _, member⟩ := supported
    cases candidate with
    | none =>
        simp only [support_pure, Set.mem_singleton_iff] at member
        subst member
        exact Or.inl rfl
    | some candidate =>
        exact afterSigning_shape _ candidate generated state fresh result
          (PqxdhDeploymentEnvironment.support_simulateQ_subset _ _ (by exact member))

/-- Every outcome of a Phase 1 bundle leaves the owner unchanged or publishes it from a fresh phase. -/
theorem bundle_shape (projection : PqxdhLivePhase1Bundle.Public I D K) (state : RawCtxBeaconLifecycle.State I D K) :
    ∀ result ∈ support (PqxdhLivePhase1Bundle.bundle projection state), Bundled state result.2 := by
  intro result supported
  unfold PqxdhLivePhase1Bundle.bundle at supported
  split at supported
  · rename_i phase
    rw [mem_support_bind_iff] at supported
    obtain ⟨generated, _, member⟩ := supported
    exact afterGenerated_shape projection generated state (Or.inl (by rw [phase]; rfl)) result member
  · rename_i phase
    exact afterGenerated_shape projection none state (Or.inr (by rw [phase]; rfl)) result supported
  · simp only [support_pure, Set.mem_singleton_iff] at supported
    subst supported
    exact Or.inl rfl

section BuildShape
variable {Metadata PeerMetadata Consumed : Type}
open PqxdhServerRegistrationPublication (State Response publish)

/-- A Server build's result: a diagnostic, no publication with the state kept, or one publication at a key ID that was vacant. -/
def Built (state : State Metadata PeerMetadata Consumed) (metadata : PeerMetadata) :
    RustM (Option Response × State Metadata PeerMetadata Consumed) → Prop
  | .ok (none, after) => after = state
  | .ok (some response, after) => ∃ candidate kernel, response.keyId = candidate.key_id ∧
      state.server.peers candidate.key_id = none ∧ after = publish state candidate kernel metadata
  | _ => True

/-- The first send and Phase 2 writing of a build publish at the candidate key ID or keep the state. -/
theorem afterInitialization_shape (candidate : pqxdh.ServerRegistrationCandidate) (authenticated : Pqxdh.Bytes)
    (kernel : ConcreteRatchetKernel) (metadata : PeerMetadata) (state : State Metadata PeerMetadata Consumed)
    (vacant : state.server.peers candidate.key_id = none) :
    ∀ result ∈ support (PqxdhServerRegistrationPublication.afterInitialization candidate authenticated kernel metadata state),
      Built state metadata (.ok result) := by
  intro result supported
  unfold PqxdhServerRegistrationPublication.afterInitialization at supported
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
theorem continueRust_shape {ι' α β : Type} {spec' : OracleSpec ι'} (value : RustM α) (next : α → OracleComp spec' (RustM β))
    (property : RustM β → Prop) (failed : ∀ error, property (.fail error)) (diverged : property .div)
    (continued : ∀ inner, ∀ result ∈ support (next inner), property result) :
    ∀ result ∈ support (PqxdhServerRegistrationPublication.continueRust value next), property result := by
  intro result supported
  cases value with
  | ok inner => exact continued inner result supported
  | fail error =>
      simp only [PqxdhServerRegistrationPublication.continueRust, support_pure, Set.mem_singleton_iff] at supported
      subst supported
      exact failed error
  | div =>
      simp only [PqxdhServerRegistrationPublication.continueRust, support_pure, Set.mem_singleton_iff] at supported
      subst supported
      exact diverged

/-- The candidate admission and first send of a build publish only at the vacant candidate key ID. -/
theorem candidateTail_shape (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (candidate : pqxdh.ServerRegistrationCandidate) (root : PqxdhSecretInputKdf.RootOutput) (data : Option Pqxdh.Bytes)
    (metadata : PeerMetadata) (state : State Metadata PeerMetadata Consumed)
    (vacant : state.server.peers candidate.key_id = none) :
    ∀ result ∈ support (PqxdhServerRegistrationPublication.candidateTail source candidate root data metadata state),
      Built state metadata result := by
  intro result supported
  unfold PqxdhServerRegistrationPublication.candidateTail at supported
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
      refine continueRust_shape _ _ _ (fun _ => trivial) trivial (fun kernel inner innerMember => ?_) result member
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
          refine continueRust_shape _ _ _ (fun _ => trivial) trivial (fun binding final finalMember => ?_) inner
            innerMember
          rw [support_map] at finalMember
          obtain ⟨published, publishedMember, rfl⟩ := finalMember
          exact afterInitialization_shape candidate _ _ metadata state vacant published publishedMember
      · simp only [support_pure, Set.mem_singleton_iff] at innerMember
        subst innerMember
        rfl

/-- Every outcome of the Server build is a diagnostic, no publication with the state kept, or one publication at a key ID that was vacant. -/
theorem build_shape (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (pending : pqxdh.PendingServerRegistration)
    (root : PqxdhSecretInputKdf.RootOutput) (data : Option Pqxdh.Bytes) (metadata : PeerMetadata)
    (state : State Metadata PeerMetadata Consumed) :
    ∀ result ∈ support (PqxdhServerRegistrationPublication.build source pending root data metadata state),
      Built state metadata result := by
  intro result supported
  unfold PqxdhServerRegistrationPublication.build PqxdhServerRegistrationPublication.continueRust at supported
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
              exact candidateTail_shape source candidate root data metadata state vacant result supported
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

end BuildShape

end Shapes

/-- An owner that does not change publishes nothing. -/
theorem ownerEffect_same {n : Nat} (index : Nat) (owner : PqxdhRegistrationSchedule.Owner KemSK) :
    PqxdhDeploymentEnvironment.ownerEffect (n := n) index owner owner = pure () := by
  unfold PqxdhDeploymentEnvironment.ownerEffect
  cases owner.beacon.phase <;> simp only [PqxdhDeploymentEnvironment.inactiveTag, ite_true]

/-- Publishing the change at one index between an owner list and the list with that owner replaced. -/
theorem ownerChange_set {n : Nat} (index : Nat) (owners : List (PqxdhRegistrationSchedule.Owner KemSK))
    (owner after : PqxdhRegistrationSchedule.Owner KemSK) (found : owners[index]? = some owner) :
    PqxdhDeploymentEnvironment.ownerChange (n := n) index owners (owners.set index after) =
      PqxdhDeploymentEnvironment.ownerEffect index owner after := by
  have below : index < owners.length := (List.getElem?_eq_some_iff.mp found).1
  unfold PqxdhDeploymentEnvironment.ownerChange
  rw [found, List.getElem?_set_self below]

/-- A bundle that publishes a fresh owner advances its World phase to initSent. -/
theorem ownerEffect_publish {n : Nat} (index : Nat) (owner : PqxdhRegistrationSchedule.Owner KemSK)
    (control : beaconcrypt_core.pqxdh.BeaconInitSent) (prekey oneTime : PqxdhJointGapDh.ScalarBytes)
    (kem : PqxdhKemIndCca.MlKem768PublicKey × KemSK)
    (fresh : PqxdhDeploymentEnvironment.inactiveTag owner.beacon.phase = some .fresh ∨
      PqxdhDeploymentEnvironment.inactiveTag owner.beacon.phase = some .freshWithCoins) :
    PqxdhDeploymentEnvironment.ownerEffect (n := n) index owner
        { owner with beacon := { owner.beacon with phase := .initSent control prekey oneTime kem } } =
      PqxdhDeploymentEnvironment.issue (.advanceOwner index .initSent) := by
  unfold PqxdhDeploymentEnvironment.ownerEffect
  cases phase : owner.beacon.phase <;>
    simp only [phase, PqxdhDeploymentEnvironment.inactiveTag, reduceCtorEq, or_self, Option.some.injEq] at fresh ⊢ <;> rfl

/-- An established owner is terminal, and so is any filling of it. -/
theorem established_terminal (phase : Option PqxdhRecordLiftBeacon.Phase) (owner : PqxdhRegistrationSchedule.Owner KemSK)
    (established : RawCtxBeaconLifecycle.Established owner.beacon.phase) :
    PqxdhRegistrationSchedule.Terminal owner ∧ PqxdhRegistrationSchedule.Terminal (fillOwner phase owner) := by
  unfold fillOwner
  cases ownerPhase : owner.beacon.phase <;>
    simp only [ownerPhase, RawCtxBeaconLifecycle.Established] at established
  refine ⟨by simp only [PqxdhRegistrationSchedule.Terminal, ownerPhase], ?_⟩
  split <;> simp_all [PqxdhRegistrationSchedule.Terminal]

/-! ### The World's Server record as CE-3's local peer copies -/

section Copies
open PqxdhDeploymentCompileRegistration (overrideServer)

/-- The World's Server peer kernels as CE-3's local copies (no owner copies). -/
def worldCopies (world : PqxdhRecordLiftWorld.Server) : PqxdhDeploymentCompile.Local :=
  ⟨PqxdhDeploymentCompile.Log.empty, fun keyId => (world.records.server.peers keyId).map (·.kernel), fun _ => none, 0,
    fun _ => 0, []⟩

/-- Overriding a stripped Server record with the World's peer kernels gives the World's routing record. -/
theorem override_world (world : PqxdhRecordLiftWorld.Server)
    (server : PqxdhServerRegistrationPublication.State Unit Unit (List Pqxdh.Bytes))
    (identity : world.records.server.identity = server.server.identity)
    (peers : ∀ keyId, (world.records.server.peers keyId).map stripPeer = server.server.peers keyId) :
    overrideServer (worldCopies world) server = { server with server := world.records.server } := by
  unfold overrideServer
  congr 1
  rcases hworld : world.records.server with ⟨worldIdentity, worldPeers, worldMetadata⟩
  rcases hserver : server.server with ⟨serverIdentity, serverPeers, serverMetadata⟩
  rw [hworld] at identity peers
  rw [hserver] at identity peers
  simp only at identity peers ⊢
  subst identity
  congr 1
  funext keyId
  rw [← peers keyId]
  simp only [worldCopies, hworld]
  cases worldPeers keyId with
  | none => rfl
  | some peer => rfl

/-- Every World peer is present in a matching stripped Server record. -/
theorem installed_world (world : PqxdhRecordLiftWorld.Server) (game : GameState KemSK)
    (peers : ∀ keyId, (world.records.server.peers keyId).map stripPeer = game.server.server.peers keyId) :
    PqxdhDeploymentCompileRegistration.Installed (worldCopies world) game := by
  intro keyId current copied
  rw [← peers keyId]
  simp only [worldCopies, Option.map_eq_some_iff] at copied
  obtain ⟨peer, found, _⟩ := copied
  rw [found]
  simp only [Option.map_some, ne_eq, reduceCtorEq, not_false_eq_true]

/-- Overriding a Server record after a publication at a key ID that the World does not hold gives the World's routing record with the new peer installed. -/
theorem override_publish (world : PqxdhRecordLiftWorld.Server)
    (server : PqxdhServerRegistrationPublication.State Unit Unit (List Pqxdh.Bytes))
    (identity : world.records.server.identity = server.server.identity)
    (peers : ∀ keyId, (world.records.server.peers keyId).map stripPeer = server.server.peers keyId)
    (candidate : pqxdh.ServerRegistrationCandidate) (kernel : ConcreteRatchetKernel)
    (vacant : world.records.server.peers candidate.key_id = none) :
    overrideServer (worldCopies world) (PqxdhServerRegistrationPublication.publish server candidate kernel ()) =
      { PqxdhServerRegistrationPublication.publish server candidate kernel () with
        server := (installPeer world candidate.key_id candidate.beacon_identity_public_key kernel).records.server } := by
  unfold overrideServer
  congr 1
  simp only [PqxdhServerRegistrationPublication.publish, installPeer]
  rcases hworld : world.records.server with ⟨worldIdentity, worldPeers, worldMetadata⟩
  rcases hserver : server.server with ⟨serverIdentity, serverPeers, serverMetadata⟩
  rw [hworld] at identity peers vacant
  rw [hserver] at identity peers
  simp only at identity peers vacant ⊢
  subst identity
  congr 1
  funext keyId
  by_cases same : keyId = candidate.key_id
  · subst same
    simp only [Function.update_self, worldCopies, hworld, vacant, Option.map_none, Option.map_some]
    rfl
  · simp only [Function.update_of_ne same, ← peers keyId, worldCopies, hworld]
    cases worldPeers keyId with
    | none => rfl
    | some peer => rfl

end Copies

/-- A joint run's first components are reachable values of the simulated program. -/
theorem run_support {ι' ι'' σ α : Type} {spec' : OracleSpec ι'} {spec'' : OracleSpec ι''}
    (impl : QueryImpl spec' (StateT σ (OracleComp spec''))) (work : OracleComp spec' α) (state : σ)
    (result : α × σ) (supported : result ∈ support ((simulateQ impl work).run state)) : result.1 ∈ support work := by
  apply OracleComp.support_simulateQ_run'_subset impl work state
  rw [StateT.run'_eq, support_map]
  exact ⟨result, supported, rfl⟩

/-! ### The forwarded Beacon finish -/

section FinishFwd
variable {ι : Type} {baseSpec : OracleSpec ι} {Reader Response : Type}
  (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)

/-- A forwarded finish callback issues no administrative effect. -/
theorem callbacksFwd_noAdmin {n : Nat}
    (query : (PqxdhBeaconPhase2Publication.NativeSpec PqxdhJointIdentity.IdentitySeed PqxdhJointGapDh.ScalarBytes
      (PqxdhKemIndCca.MlKem768PublicKey × KemSK) PqxdhJointIdentity.IdentitySeed Response).Domain)
    (state : NativeState KemSK) :
    ((PqxdhDeploymentEnvironment.callbacksFwd (n := n) setup codec query).run state).IsQueryBoundP
      (fun effect => effectKind effect = .administrative) 0 := by
  rcases query with query | query
  · simp only [PqxdhDeploymentEnvironment.callbacksFwd, StateT.run_lift, bind_pure_comp, isQueryBoundP_map_iff]
    exact coins_noAdmin _
  · rcases query with query | request
    · simp only [PqxdhDeploymentEnvironment.callbacksFwd, PqxdhPhase2DhRootConsumer.withRoot, StateT.run_lift,
        bind_pure_comp, isQueryBoundP_map_iff, PqxdhDeploymentEnvironment.beaconFwd]
      rcases query with request | (bytes | input)
      · simp only [PqxdhDeploymentEnvironment.primFwd]
        trivial
      · simp only [PqxdhDeploymentEnvironment.primFwd, PqxdhDeploymentEnvironment.request, isQueryBoundP_map_iff]
        exact (isQueryBoundP_query_iff _ _ _).mpr fun same => by cases same
      · simp only [PqxdhDeploymentEnvironment.primFwd]
        trivial
    · cases request with
      | root input =>
          simp only [PqxdhDeploymentEnvironment.callbacksFwd, PqxdhPhase2DhRootConsumer.withRoot]
          exact coins_noAdmin _
      | initial request =>
          simp only [PqxdhDeploymentEnvironment.callbacksFwd, PqxdhPhase2DhRootConsumer.withRoot, StateT.run_lift,
            PqxdhDeploymentEnvironment.beaconFwd, pure_bind]
          trivial
      | application response =>
          simp only [PqxdhDeploymentEnvironment.callbacksFwd, PqxdhPhase2DhRootConsumer.withRoot, StateT.run_lift,
            PqxdhDeploymentEnvironment.beaconFwd, pure_bind]
          trivial

/-- The forwarded Beacon finish issues no administrative effect. -/
theorem finishFwd_noAdmin {n : Nat} {α : Type}
    (work : OracleComp (PqxdhBeaconPhase2Publication.NativeSpec PqxdhJointIdentity.IdentitySeed PqxdhJointGapDh.ScalarBytes
      (PqxdhKemIndCca.MlKem768PublicKey × KemSK) PqxdhJointIdentity.IdentitySeed Response) α) (state : NativeState KemSK) :
    ((simulateQ (PqxdhDeploymentEnvironment.callbacksFwd (n := n) setup codec) work).run state).IsQueryBoundP
      (fun effect => effectKind effect = .administrative) 0 :=
  IsQueryBoundP.simulateQ_run_of_step (isQueryBoundP_false _ 0) (fun _ absurd => absurd.elim)
    (fun query _ current => callbacksFwd_noAdmin setup codec query current) state

/-- A forwarded finish callback keeps the game state. -/
theorem callbacksFwd_game {n : Nat}
    (query : (PqxdhBeaconPhase2Publication.NativeSpec PqxdhJointIdentity.IdentitySeed PqxdhJointGapDh.ScalarBytes
      (PqxdhKemIndCca.MlKem768PublicKey × KemSK) PqxdhJointIdentity.IdentitySeed Response).Domain)
    (state : NativeState KemSK) :
    ∀ result ∈ support ((PqxdhDeploymentEnvironment.callbacksFwd (n := n) setup codec query).run state),
      result.2.2 = state.2 := by
  intro result supported
  rcases query with query | query
  · simp only [PqxdhDeploymentEnvironment.callbacksFwd, StateT.run_lift, mem_support_bind_iff, support_pure,
      Set.mem_singleton_iff] at supported
    obtain ⟨_, _, rfl⟩ := supported
    rfl
  · rcases query with query | request
    · simp only [PqxdhDeploymentEnvironment.callbacksFwd, PqxdhPhase2DhRootConsumer.withRoot, StateT.run_lift,
        mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at supported
      obtain ⟨_, _, rfl⟩ := supported
      rfl
    · cases request with
      | root input =>
          simp only [PqxdhDeploymentEnvironment.callbacksFwd, PqxdhPhase2DhRootConsumer.withRoot, coins,
            PqxdhServerAuthNative.sourceRoot, StateT.run, simulateQ_map, support_map] at supported
          obtain ⟨_, _, rfl⟩ := supported
          rfl
      | initial request =>
          simp only [PqxdhDeploymentEnvironment.callbacksFwd, PqxdhPhase2DhRootConsumer.withRoot, StateT.run_lift,
            PqxdhDeploymentEnvironment.beaconFwd, pure_bind, support_pure, Set.mem_singleton_iff] at supported
          subst supported
          rfl
      | application response =>
          simp only [PqxdhDeploymentEnvironment.callbacksFwd, PqxdhPhase2DhRootConsumer.withRoot, StateT.run_lift,
            PqxdhDeploymentEnvironment.beaconFwd, pure_bind, support_pure, Set.mem_singleton_iff] at supported
          subst supported
          rfl

/-- The forwarded Beacon finish keeps the game state. -/
theorem finishFwd_game {n : Nat} {α : Type}
    (work : OracleComp (PqxdhBeaconPhase2Publication.NativeSpec PqxdhJointIdentity.IdentitySeed PqxdhJointGapDh.ScalarBytes
      (PqxdhKemIndCca.MlKem768PublicKey × KemSK) PqxdhJointIdentity.IdentitySeed Response) α) (state : NativeState KemSK) :
    ∀ result ∈ support ((simulateQ (PqxdhDeploymentEnvironment.callbacksFwd (n := n) setup codec) work).run state),
      result.2.2 = state.2 := by
  induction work using OracleComp.inductionOn generalizing state with
  | pure value =>
      intro result supported
      simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
      subst supported
      rfl
  | query_bind query next ih =>
      intro result supported
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, id_map,
        StateT.run_bind, mem_support_bind_iff] at supported
      obtain ⟨middle, member, final⟩ := supported
      rw [ih middle.1 middle.2 result final]
      exact callbacksFwd_game setup codec query state middle member

end FinishFwd

/-! ### Shape of the Beacon finish -/

section FinishShape

/-- A Beacon finish leaves the owner unchanged, or ends an initSent owner aborted or established. -/
def Finished (before after : PqxdhRegistrationSchedule.Owner KemSK) : Prop :=
  after = before ∨ (PqxdhDeploymentEnvironment.inactiveTag before.beacon.phase = some .initSent ∧
    (PqxdhDeploymentEnvironment.inactiveTag after.beacon.phase = some .aborted ∨
      ∃ control associatedData kernel, after.beacon.phase = .established control associatedData kernel))

/-- The source commit of a finish aborts or publishes. -/
theorem commit_shape (control : beaconcrypt_core.pqxdh.BeaconInitSent) (before : PqxdhRegistrationSchedule.Owner KemSK)
    (staged : Option PqxdhBeaconPhase2Publication.Staged) :
    PqxdhDeploymentEnvironment.inactiveTag (PqxdhBeaconPhase2Publication.finish control before staged).2.beacon.phase =
        some .aborted ∨
      ∃ control' associatedData kernel, (PqxdhBeaconPhase2Publication.finish control before staged).2.beacon.phase =
        .established control' associatedData kernel := by
  unfold PqxdhBeaconPhase2Publication.finish
  cases staged with
  | none => exact Or.inl rfl
  | some staged =>
      dsimp only
      split_ifs
      · exact Or.inl rfl
      · exact Or.inl rfl
      · exact Or.inr ⟨_, _, _, rfl⟩

/-- Every outcome of a native owner finish leaves the owner unchanged or ends an initSent owner aborted or established. -/
theorem finish_shape {Response : Type} (decode : RawCtxReceive.FrameDecoder) (raw : Pqxdh.Bytes)
    (before : PqxdhRegistrationSchedule.Owner KemSK) :
    ∀ result ∈ support (PqxdhBeaconPhase2Publication.nativeOwner (X := PqxdhJointIdentity.IdentitySeed)
      (Response := Response) decode raw before), Finished before result.2 := by
  intro result supported
  have sourced := PqxdhDeploymentEnvironment.support_simulateQ_subset _ _ supported
  unfold PqxdhBeaconPhase2Publication.owner at sourced
  split at sourced
  · rename_i control prekey oneTime kem phase
    have initSent : PqxdhDeploymentEnvironment.inactiveTag before.beacon.phase = some .initSent := by rw [phase]; rfl
    rw [mem_support_bind_iff] at sourced
    obtain ⟨prepared, _, rest⟩ := sourced
    cases prepared with
    | none =>
        simp only [support_pure, Set.mem_singleton_iff] at rest
        subst rest
        exact Or.inr ⟨initSent, commit_shape control before none⟩
    | some prepared =>
        rw [mem_support_bind_iff] at rest
        obtain ⟨staged, _, final⟩ := rest
        simp only [support_pure, Set.mem_singleton_iff] at final
        subst final
        exact Or.inr ⟨initSent, commit_shape control before staged⟩
  · simp only [support_pure, Set.mem_singleton_iff] at sourced
    subst sourced
    exact Or.inl rfl

/-- An initSent owner that ends aborted advances its World phase. -/
theorem ownerEffect_abort {n : Nat} (index : Nat) (before after : PqxdhRegistrationSchedule.Owner KemSK)
    (initSent : PqxdhDeploymentEnvironment.inactiveTag before.beacon.phase = some .initSent)
    (aborted : PqxdhDeploymentEnvironment.inactiveTag after.beacon.phase = some .aborted) :
    PqxdhDeploymentEnvironment.ownerEffect (n := n) index before after =
      PqxdhDeploymentEnvironment.issue (.advanceOwner index .aborted) := by
  unfold PqxdhDeploymentEnvironment.ownerEffect
  cases beforePhase : before.beacon.phase <;>
    simp only [beforePhase, PqxdhDeploymentEnvironment.inactiveTag, reduceCtorEq, Option.some.injEq] at initSent
  cases afterPhase : after.beacon.phase <;>
    simp only [afterPhase, PqxdhDeploymentEnvironment.inactiveTag, reduceCtorEq, Option.some.injEq] at aborted
  rfl

/-- An initSent owner that ends established is installed with its known kernel and its shell. -/
theorem ownerEffect_establish {n : Nat} (index : Nat) (before after : PqxdhRegistrationSchedule.Owner KemSK)
    (initSent : PqxdhDeploymentEnvironment.inactiveTag before.beacon.phase = some .initSent)
    (control : beaconcrypt_core.pqxdh.BeaconEstablished) (associatedData : Std.Array Std.U8 153#usize)
    (kernel : ConcreteRatchetKernel) (established : after.beacon.phase = .established control associatedData kernel) :
    PqxdhDeploymentEnvironment.ownerEffect (n := n) index before after =
      PqxdhDeploymentEnvironment.issue (.installBeacon index ⟨after.beacon.identityKeyId, control, associatedData⟩
        (.known kernel)) := by
  unfold PqxdhDeploymentEnvironment.ownerEffect
  cases beforePhase : before.beacon.phase <;>
    simp only [beforePhase, PqxdhDeploymentEnvironment.inactiveTag, reduceCtorEq, Option.some.injEq] at initSent
  rw [established]

/-- Filling an established owner with its own shell and kernel changes nothing. -/
theorem fillOwner_self (owner : PqxdhRegistrationSchedule.Owner KemSK) (control : beaconcrypt_core.pqxdh.BeaconEstablished)
    (associatedData : Std.Array Std.U8 153#usize) (kernel : ConcreteRatchetKernel)
    (established : owner.beacon.phase = .established control associatedData kernel) :
    fillOwner (some (.established ⟨owner.beacon.identityKeyId, control, associatedData⟩ kernel)) owner = owner := by
  unfold fillOwner
  rw [established]
  rcases owner with ⟨⟨identity, identityKeyId, serverIdentity, phase⟩, rawAttempts⟩
  simp only at established ⊢
  rw [established]

end FinishShape

/-! ### The real registration commands -/

section Commands
variable {ι : Type} {baseSpec : OracleSpec ι} {Reader Response : Type}
  (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
  (route : RawCtxServerRouting.SenderDecoder) (created : PqxdhLiveServerConstruction.Created Unit)

/-- One run of a registration step on the deployment state. The same statement as `PqxdhDeploymentCompileStep.onNative_run`, which later work should cite instead. -/
theorem onNative_run {α : Type} (work : PqxdhRegistrationSchedule.Game KemSK α) (state : PqxdhDeploymentNative.State KemSK) :
    (PqxdhDeploymentNative.onNative work).run state =
      (fun result => (result.1, { state with native := result.2 })) <$> work.run state.native := rfl

/-- One run of a shared native step on the registration state. Definitionally the statement of `PqxdhRegistrationSchedule.onShared_run` (`work.run state.shared` is `work state.shared`), which later work should cite instead. -/
theorem onShared_run {α : Type} (work : NativeGame KemSK α) (state : PqxdhRegistrationSchedule.State KemSK) :
    (PqxdhRegistrationSchedule.onShared work).run state =
      (fun result => (result.1, { state with shared := result.2 })) <$> work.run state.shared := rfl

/-- One run of the native owner construction. -/
theorem create_run (pin : PqxdhBeaconPhase2Preparation.Word32) (keyId : Std.U64) (state : PqxdhRegistrationSchedule.State KemSK) :
    (PqxdhRegistrationSchedule.create setup pin keyId).run state = (do
      let identity ← PqxdhJointIdentity.sampleSeed
      let prekey ← PqxdhJointGapDh.sampleScalar
      let keys ← simulateQ (PqxdhInitializerSecrecy.kemAmbientImpl setup.baseImpl) setup.kem.keygen
      let owner : PqxdhRegistrationSchedule.Owner KemSK := ⟨⟨identity, keyId, pin, .fresh ⟨⟨pin, keyId⟩⟩ prekey keys⟩, 0⟩
      pure (state.owners.length, { state with owners := state.owners ++ [owner] })) :=
  PqxdhRegistrationSchedule.create_source setup pin keyId state

/-- The real registration handler on a command other than the raw accept: the native handler of the deployment experiment on the deployment state, the log kept, and the LQ snapshot of a finish. -/
theorem realReg_quiet (query : EnvQuery) (notAccept : ∀ raw, query.val ≠ .accept raw) (state : XState KemSK Unit 0) :
    (PqxdhDeploymentBackend.realReg setup codec route checks created query).run state =
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
theorem createStep_effects (pin : Pqxdh.Bytes) (keyId : Std.U64) (e : EnvState KemSK Unit) (w : PqxdhRecordLiftWorld.State 0) :
    Prod.map id uncount <$> (simulateQ PqxdhRecordLiftWorld.effects
        ((PqxdhDeploymentEnvironment.realStep (n := 0) setup codec checks ⟨.create pin keyId, trivial⟩).run e)).run w =
      match PqxdhDeploymentInterface.parsePin pin with
      | none => pure ((none, e), uncount w)
      | some word => (fun result => ((some result.1, { e with native := strip result.2 }),
          uncount { w with owners := w.owners ++ [.inactive .fresh] })) <$>
            (PqxdhRegistrationSchedule.create setup word keyId).run e.native := by
  change Prod.map id uncount <$> (simulateQ PqxdhRecordLiftWorld.effects
    ((PqxdhDeploymentEnvironment.createStep (n := 0) setup pin keyId).run e)).run w = _
  unfold PqxdhDeploymentEnvironment.createStep
  rcases parsed : PqxdhDeploymentInterface.parsePin pin with _ | word
  · simp only [StateT.run_pure, simulateQ_pure, map_pure]
    rfl
  · simp only [StateT.run_bind, StateT.run_lift, StateT.run_pure, bind_assoc, pure_bind]
    rw [show (PqxdhDeploymentEnvironment.onEnv (n := 0) (Bk := Unit) (PqxdhRegistrationSchedule.create setup word keyId)).run e =
      (fun result => (result.1, { e with native := strip result.2 })) <$>
        coins (n := 0) ((PqxdhRegistrationSchedule.create setup word keyId).run e.native) from rfl, bind_map_left]
    rw [effects_then ctxAdmin _ (coins_noAdmin _) _ (fun result x => pure ((some result.1, { e with native := strip result.2 }),
      uncount { x with owners := x.owners ++ [.inactive .fresh] })) (fun result x => ?_) w]
    · rw [PqxdhDeploymentEnvironment.ctxEffects_coins, bind_map_left]
      simp only [bind_pure_comp]
      rfl
    · rw [effects_issue_then, effects_append, map_pure]
      rfl

/-- The reassembled state after a `create`: one fresh owner appended on both sides. -/
theorem create_merge (e : EnvState KemSK Unit) (w : PqxdhRecordLiftWorld.State 0) (good : Good created e w)
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
theorem create_law (pin : Pqxdh.Bytes) (keyId : Std.U64) (e : EnvState KemSK Unit) (w : PqxdhRecordLiftWorld.State 0)
    (good : Good created e w) :
    (fun result => (result.1.1, merge result.1.2 result.2)) <$> (simulateQ PqxdhRecordLiftWorld.effects
        ((PqxdhDeploymentEnvironment.realStep (n := 0) setup codec checks ⟨.create pin keyId, trivial⟩).run e)).run w =
      (PqxdhDeploymentBackend.realReg setup codec route checks created ⟨.create pin keyId, trivial⟩).run (merge e w) := by
  rw [law_uncount, createStep_effects, realReg_quiet setup codec checks route created _ (fun raw same => by cases same)]
  rcases parsed : PqxdhDeploymentInterface.parsePin pin with _ | word
  · simp only [PqxdhDeploymentNative.handler, parsed, StateT.run_pure, map_pure]
    rfl
  · simp only [PqxdhDeploymentNative.handler, parsed, StateT.run_map, PqxdhRegistrationSchedule.handler, onNative_run,
      create_run, map_bind, map_pure]
    refine bind_congr fun identity => bind_congr fun prekey => bind_congr fun keys => ?_
    rw [create_merge created e w good _ rfl]
    simp only [merge, fill, List.length_mapIdx, PqxdhDeploymentLater.finishOwner, PqxdhDeploymentLater.snapshotAt]

/-- The `create` command of the real environment keeps admissibility. -/
theorem create_keeps (pin : Pqxdh.Bytes) (keyId : Std.U64) (e : EnvState KemSK Unit) (w : PqxdhRecordLiftWorld.State 0)
    (good : Good created e w) :
    ∀ result ∈ support ((simulateQ PqxdhRecordLiftWorld.effects
        ((PqxdhDeploymentEnvironment.realStep (n := 0) setup codec checks ⟨.create pin keyId, trivial⟩).run e)).run w),
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

/-- The public HMAC of the real registration reads no record coordinate. -/
theorem hmac_frame (seed : PqxdhJointIdentity.IdentitySeed) (key : PqxdhSecretInputKdf.HmacBlock) (message : Pqxdh.Bytes)
    (cache : CtxRomAuth.CtxRO.QueryCache) (server : RawCtxServerRouting.Server Unit Unit) (keyId : Std.U64) :
    NFrame (frameGame cache server keyId)
      (PqxdhServerAuthNative.nativeHmac setup seed PqxdhRegistrationSchedule.observationScalar key message) :=
  nativeHmac_nframe setup cache server keyId seed _ key message

/-- The real environment's public HMAC, run by the World with its counts forgotten: the native HMAC on the environment's shared state, the World unchanged. -/
theorem hmacStep_effects (key : PqxdhSecretInputKdf.HmacBlock) (message : Pqxdh.Bytes) (e : EnvState KemSK Unit)
    (w : PqxdhRecordLiftWorld.State 0) :
    Prod.map id uncount <$> (simulateQ PqxdhRecordLiftWorld.effects
        ((PqxdhDeploymentEnvironment.realStep (n := 0) setup codec checks ⟨.hmac key message, trivial⟩).run e)).run w =
      (fun result => ((result.1, { e with native := strip { e.native with shared := result.2 } }), uncount w)) <$>
        (PqxdhServerAuthNative.nativeHmac setup e.created.seed PqxdhRegistrationSchedule.observationScalar key message).run
          e.native.shared := by
  change Prod.map id uncount <$> (simulateQ PqxdhRecordLiftWorld.effects
    ((fun result => (result.1, { e with native := strip result.2 })) <$> coins (n := 0)
      ((PqxdhRegistrationSchedule.onShared (PqxdhServerAuthNative.nativeHmac setup e.created.seed
        PqxdhRegistrationSchedule.observationScalar key message)).run e.native))).run w = _
  rw [effects_map, effects_coins, onShared_run, Functor.map_map, Functor.map_map]
  rfl

/-- The public HMAC of the real environment splits the real registration handler. -/
theorem hmac_law (key : PqxdhSecretInputKdf.HmacBlock) (message : Pqxdh.Bytes) (e : EnvState KemSK Unit)
    (w : PqxdhRecordLiftWorld.State 0) (good : Good created e w) :
    (fun result => (result.1.1, merge result.1.2 result.2)) <$> (simulateQ PqxdhRecordLiftWorld.effects
        ((PqxdhDeploymentEnvironment.realStep (n := 0) setup codec checks ⟨.hmac key message, trivial⟩).run e)).run w =
      (PqxdhDeploymentBackend.realReg setup codec route checks created ⟨.hmac key message, trivial⟩).run (merge e w) := by
  obtain ⟨world, found, _, _, _⟩ := good.server
  rw [law_uncount, hmacStep_effects, realReg_quiet setup codec checks route created _ (fun raw same => by cases same)]
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
theorem hmac_keeps (key : PqxdhSecretInputKdf.HmacBlock) (message : Pqxdh.Bytes) (e : EnvState KemSK Unit)
    (w : PqxdhRecordLiftWorld.State 0) (good : Good created e w) :
    ∀ result ∈ support ((simulateQ PqxdhRecordLiftWorld.effects
        ((PqxdhDeploymentEnvironment.realStep (n := 0) setup codec checks ⟨.hmac key message, trivial⟩).run e)).run w),
      Good created result.1.2 result.2 := by
  apply keeps_uncount _ (Good created) (good_uncount created)
  rw [hmacStep_effects]
  intro result supported
  rw [support_map] at supported
  obtain ⟨inner, member, rfl⟩ := supported
  exact uncount_good created _ _ (shared_good _ (hmac_frame setup e.created.seed key message) created e _ w good inner member
    rfl rfl)

/-- The logged raw accept of the real registration reads no record coordinate. -/
theorem accept_frame (seed : PqxdhJointIdentity.IdentitySeed) (raw : Pqxdh.Bytes)
    (cache : CtxRomAuth.CtxRO.QueryCache) (server : RawCtxServerRouting.Server Unit Unit) (keyId : Std.U64) :
    NFrame (frameGame cache server keyId) (PqxdhDeploymentLaterServerNative.acceptLogged setup codec checks seed raw) :=
  acceptLogged_nframe setup codec checks cache server keyId seed raw

/-- The real registration handler on the raw accept: the native logged accept on the deployment state's shared state, its entry appended to the log. -/
theorem realReg_accept (raw : Pqxdh.Bytes) (state : XState KemSK Unit 0) :
    (PqxdhDeploymentBackend.realReg setup codec route checks created ⟨.accept raw, trivial⟩).run state =
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
theorem acceptStep_effects (raw : Pqxdh.Bytes) (e : EnvState KemSK Unit) (w : PqxdhRecordLiftWorld.State 0) :
    Prod.map id uncount <$> (simulateQ PqxdhRecordLiftWorld.effects
        ((PqxdhDeploymentEnvironment.realStep (n := 0) setup codec checks ⟨.accept raw, trivial⟩).run e)).run w =
      (fun result => ((result.1.1,
          { e with native := strip { e.native with shared := result.2 }, log := e.log ++ [result.1.2] }), uncount w)) <$>
        (PqxdhDeploymentLaterServerNative.acceptLogged setup codec checks e.created.seed raw).run e.native.shared := by
  change Prod.map id uncount <$> (simulateQ PqxdhRecordLiftWorld.effects
    ((fun result => (result.1.1, { e with native := strip result.2, log := e.log ++ [result.1.2] })) <$> coins (n := 0)
      ((PqxdhRegistrationSchedule.onShared (PqxdhDeploymentLaterServerNative.acceptLogged setup codec checks e.created.seed
        raw)).run e.native))).run w = _
  rw [effects_map, effects_coins, onShared_run, Functor.map_map, Functor.map_map]
  rfl

/-- The raw accept of the real environment splits the real registration handler. -/
theorem accept_law (raw : Pqxdh.Bytes) (e : EnvState KemSK Unit) (w : PqxdhRecordLiftWorld.State 0) (good : Good created e w) :
    (fun result => (result.1.1, merge result.1.2 result.2)) <$> (simulateQ PqxdhRecordLiftWorld.effects
        ((PqxdhDeploymentEnvironment.realStep (n := 0) setup codec checks ⟨.accept raw, trivial⟩).run e)).run w =
      (PqxdhDeploymentBackend.realReg setup codec route checks created ⟨.accept raw, trivial⟩).run (merge e w) := by
  obtain ⟨world, found, _, _, _⟩ := good.server
  rw [law_uncount, acceptStep_effects, realReg_accept]
  rw [show (merge e w).base.native = fill w e.native from rfl, good.createdEq,
    shared_run _ (accept_frame setup codec checks created.seed raw) e w world found, Functor.map_map, Functor.map_map]
  rw [← good.createdEq]
  apply map_congr_support
  intro result supported
  simp only [merge_uncount]
  simp only [merge, shared_fill _ (accept_frame setup codec checks e.created.seed raw) created e w good world found result
    supported]

/-- The raw accept of the real environment keeps admissibility. -/
theorem accept_keeps (raw : Pqxdh.Bytes) (e : EnvState KemSK Unit) (w : PqxdhRecordLiftWorld.State 0) (good : Good created e w) :
    ∀ result ∈ support ((simulateQ PqxdhRecordLiftWorld.effects
        ((PqxdhDeploymentEnvironment.realStep (n := 0) setup codec checks ⟨.accept raw, trivial⟩).run e)).run w),
      Good created result.1.2 result.2 := by
  apply keeps_uncount _ (Good created) (good_uncount created)
  rw [acceptStep_effects]
  intro result supported
  rw [support_map] at supported
  obtain ⟨inner, member, rfl⟩ := supported
  exact uncount_good created _ _ (shared_good _ (accept_frame setup codec checks e.created.seed raw) created e _ w good inner
    member rfl rfl)

/-- One run of the native bundle at a missing owner. -/
theorem bundle_run_missing (index : Nat) (state : PqxdhRegistrationSchedule.State KemSK) (missing : state.owners[index]? = none) :
    (PqxdhRegistrationSchedule.bundle setup codec index).run state = pure (none, state) := by
  simp only [PqxdhRegistrationSchedule.bundle, StateT.run_bind, StateT.run_get, pure_bind, missing, StateT.run_pure]

/-- One run of the native bundle at a present owner. -/
theorem bundle_run_found (index : Nat) (state : PqxdhRegistrationSchedule.State KemSK) (owner : PqxdhRegistrationSchedule.Owner KemSK)
    (found : state.owners[index]? = some owner) :
    (PqxdhRegistrationSchedule.bundle setup codec index).run state =
      (fun result => (result.1, { state with owners := state.owners.set index result.2 })) <$>
        simulateQ (PqxdhRegistrationSchedule.bundleCallbacks setup codec owner.beacon.identity)
          (PqxdhLivePhase1Bundle.bundle (PqxdhRegistrationSchedule.projection setup index) owner) :=
  PqxdhRegistrationSchedule.bundle_source setup codec index state owner found

/-- The real environment's bundle, run by the World with its counts forgotten: the native bundle on the environment's registration state, then the owner's phase change published. -/
theorem bundleStep_effects (index : Nat) (e : EnvState KemSK Unit) (w : PqxdhRecordLiftWorld.State 0) :
    Prod.map id uncount <$> (simulateQ PqxdhRecordLiftWorld.effects
        ((PqxdhDeploymentEnvironment.realStep (n := 0) setup codec checks ⟨.bundle index, trivial⟩).run e)).run w =
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
theorem bundle_outcome (index : Nat) (e : EnvState KemSK Unit) (w : PqxdhRecordLiftWorld.State 0) (good : Good created e w)
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
    let w' : PqxdhRecordLiftWorld.State 0 := { w with owners := w.owners.set index (.inactive .initSent) }
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
theorem bundle_law (index : Nat) (e : EnvState KemSK Unit) (w : PqxdhRecordLiftWorld.State 0) (good : Good created e w) :
    (fun result => (result.1.1, merge result.1.2 result.2)) <$> (simulateQ PqxdhRecordLiftWorld.effects
        ((PqxdhDeploymentEnvironment.realStep (n := 0) setup codec checks ⟨.bundle index, trivial⟩).run e)).run w =
      (PqxdhDeploymentBackend.realReg setup codec route checks created ⟨.bundle index, trivial⟩).run (merge e w) := by
  rw [law_uncount, bundleStep_effects, realReg_quiet setup codec checks route created _ (fun raw same => by cases same)]
  simp only [PqxdhDeploymentNative.handler, onNative_run, PqxdhRegistrationSchedule.handler, Functor.map_map]
  rw [show (merge e w).base.native = fill w e.native from rfl]
  cases owned : e.native.owners[index]? with
  | none =>
      have filled : (fill w e.native).owners[index]? = none := by
        simp only [fill, List.getElem?_mapIdx, owned, Option.map_none]
      rw [bundle_run_missing setup codec index _ owned, bundle_run_missing setup codec index _ filled, pure_bind, map_pure]
      have quiet : PqxdhDeploymentEnvironment.ownerChange (n := 0) index e.native.owners e.native.owners = pure () := by
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
        have quiet : PqxdhDeploymentEnvironment.ownerChange (n := 0) index e.native.owners e.native.owners = pure () := by
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
theorem bundle_keeps (index : Nat) (e : EnvState KemSK Unit) (w : PqxdhRecordLiftWorld.State 0) (good : Good created e w) :
    ∀ result ∈ support ((simulateQ PqxdhRecordLiftWorld.effects
        ((PqxdhDeploymentEnvironment.realStep (n := 0) setup codec checks ⟨.bundle index, trivial⟩).run e)).run w),
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
      have quiet : PqxdhDeploymentEnvironment.ownerChange (n := 0) index e.native.owners e.native.owners = pure () := by
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
        have quiet : PqxdhDeploymentEnvironment.ownerChange (n := 0) index e.native.owners e.native.owners = pure () := by
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

/-- The registration state after a Server build at a session: the token consumed, the settled Server record installed and the sequence-one seals logged. -/
def builtNative (state : PqxdhRegistrationSchedule.State KemSK) (session : Nat)
    (result : RustM (Option PqxdhServerRegistrationPublication.Response ×
      PqxdhServerRegistrationPublication.State Unit Unit (List Pqxdh.Bytes)) × List RawCtxSourceSend.SealContext) :
    PqxdhRegistrationSchedule.State KemSK :=
  { state with shared := (state.shared.1, { state.shared.2 with
      pending := Function.update state.shared.2.pending session none
      server := (PqxdhServerAuthExperiment.settle state.shared.2.server result.1).2
      ghost := { state.shared.2.ghost with seals := state.shared.2.ghost.seals ++ result.2.map (fun context => (session, context)) } }) }

/-- The game state after a native Server build at a session, from the logged tail's result. -/
def builtGame (game : GameState KemSK) (session : Nat)
    (result : RustM (Option PqxdhServerRegistrationPublication.Response ×
      PqxdhServerRegistrationPublication.State Unit Unit (List Pqxdh.Bytes)) ×
        (List RawCtxSourceSend.SealContext × CtxRomAuth.CtxRO.QueryCache)) : GameState KemSK :=
  { game with
    pending := Function.update game.pending session none
    server := (PqxdhServerAuthExperiment.settle game.server result.1).2
    ctx := result.2.2
    ghost := { game.ghost with seals := game.ghost.seals ++ result.2.1.map (fun context => (session, context)) } }

/-- One run of the native Server build. -/
theorem nativeBuild_run (session : Nat) (payload : Option Pqxdh.Bytes) (family : PqxdhJointDhExtractFamily.State)
    (game : GameState KemSK) :
    (PqxdhServerAuthNative.nativeBuild setup codec checks session payload).run (family, game) =
      match game.pending session with
      | none => pure (none, (family, game))
      | some token => (fun result => ((PqxdhServerAuthExperiment.settle game.server result.1).1,
          (family, builtGame game session result))) <$>
        (simulateQ (PqxdhServerAuthExperiment.tailImpl setup codec checks)
          (PqxdhServerRegistrationPublication.build setup.source token.pending token.root payload () game.server)).run
            ([], game.ctx) := by
  unfold PqxdhServerAuthNative.nativeBuild
  rw [PqxdhDeploymentBackend.nativeGet_bind]
  cases game.pending session with
  | none => rfl
  | some token =>
      dsimp only
      rw [PqxdhDeploymentBackend.nativeCoins_bind, map_eq_bind_pure_comp]
      refine bind_congr fun result => ?_
      rw [PqxdhDeploymentBackend.nativeSet_run_bind]
      rfl

/-- The real environment's Server build, run by the World with its counts forgotten: the forwarded build read through `ctxEffects` on the World's cache, then the publication of the settled build in the World. -/
theorem buildStep_effects (session : Nat) (payload : Option Pqxdh.Bytes) (e : EnvState KemSK Unit)
    (w : PqxdhRecordLiftWorld.State 0) :
    Prod.map id uncount <$> (simulateQ PqxdhRecordLiftWorld.effects
        ((PqxdhDeploymentEnvironment.realStep (n := 0) setup codec checks ⟨.build session payload, trivial⟩).run e)).run w =
      match e.native.shared.2.pending session with
      | none => pure ((none, e), uncount w)
      | some token => (simulateQ (ctxEffects ctxAdmin) ((simulateQ (PqxdhDeploymentEnvironment.tailFwd (n := 0) setup codec
            checks) (PqxdhServerRegistrationPublication.build setup.source token.pending token.root payload ()
              e.native.shared.2.server)).run [])).run w.primitive.2 >>= fun result =>
          Prod.map id uncount <$> (simulateQ PqxdhRecordLiftWorld.effects
            (PqxdhDeploymentEnvironment.serverEffect (PqxdhServerAuthExperiment.settle e.native.shared.2.server result.1.1) >>=
              fun _ => pure ((PqxdhServerAuthExperiment.settle e.native.shared.2.server result.1.1).1,
                { e with native := strip (builtNative e.native session result.1) }))).run (withCache w result.2) := by
  change Prod.map id uncount <$> (simulateQ PqxdhRecordLiftWorld.effects
    (PqxdhDeploymentEnvironment.buildStep (n := 0) setup codec checks session payload e)).run w = _
  unfold PqxdhDeploymentEnvironment.buildStep
  dsimp only
  rcases pending : e.native.shared.2.pending session with _ | token
  · simp only [simulateQ_pure, StateT.run_pure, map_pure]
    rfl
  · dsimp only
    rw [effects_then_free ctxAdmin _ ?noAdmin _ (fun result => countFree_bind (countFree_serverEffect _)
      fun _ => countFree_pure _) w]
    · rfl
    · simpa only [reduceCtorEq, ite_false] using PqxdhDeploymentEnvironment.build_fwd_bound (n := 0) setup codec checks
        token.pending token.root payload e.native.shared.2.server [] .administrative

/-- The game state of the reassembled state as CE-3's override of the environment's Server record. -/
theorem frameGame_server (e : EnvState KemSK Unit) (w : PqxdhRecordLiftWorld.State 0) (good : Good created e w)
    (world : PqxdhRecordLiftWorld.Server) (found : w.server = some world) :
    (frameGame w.primitive.2 world.records.server e.native.shared.2.server.identityKeyId e.native.shared.2).server =
      PqxdhDeploymentCompileRegistration.overrideServer (worldCopies world) e.native.shared.2.server := by
  obtain ⟨world', found', _, identity, peers⟩ := good.server
  rw [found] at found'
  cases found'
  rw [override_world world _ identity peers]
  rfl

/-- The reassembled state after a Server build whose settled Server record the World mirrors. -/
theorem build_merge (session : Nat) (e : EnvState KemSK Unit) (w : PqxdhRecordLiftWorld.State 0) (good : Good created e w)
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
theorem withCache_server (w : PqxdhRecordLiftWorld.State 0) (cache : CtxRomAuth.CtxRO.QueryCache)
    (world : PqxdhRecordLiftWorld.Server) (found : w.server = some world) :
    { withCache w cache with server := some world } = withCache w cache := by
  simp only [withCache, ← found]

/-- The registration state after a Server build that published nothing. -/
theorem builtNative_quiet (state : PqxdhRegistrationSchedule.State KemSK) (session : Nat)
    (rust : RustM (Option PqxdhServerRegistrationPublication.Response ×
      PqxdhServerRegistrationPublication.State Unit Unit (List Pqxdh.Bytes)))
    (log : List RawCtxSourceSend.SealContext)
    (settled : (PqxdhServerAuthExperiment.settle state.shared.2.server rust).2 = state.shared.2.server) :
    builtNative state session (rust, log) = { state with shared := (state.shared.1, { state.shared.2 with
      pending := Function.update state.shared.2.pending session none
      ghost := { state.shared.2.ghost with seals := state.shared.2.ghost.seals ++ log.map (fun context => (session, context)) } }) } := by
  simp only [builtNative, settled]

/-- One outcome of a Server build: the World's installation, the World's Server record after it and admissibility. -/
theorem build_outcome (session : Nat) (e : EnvState KemSK Unit) (w : PqxdhRecordLiftWorld.State 0) (good : Good created e w)
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
    · have effect : PqxdhDeploymentEnvironment.serverEffect (n := 0)
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
theorem build_law (session : Nat) (payload : Option Pqxdh.Bytes) (e : EnvState KemSK Unit) (w : PqxdhRecordLiftWorld.State 0)
    (good : Good created e w) :
    (fun result => (result.1.1, merge result.1.2 result.2)) <$> (simulateQ PqxdhRecordLiftWorld.effects
        ((PqxdhDeploymentEnvironment.realStep (n := 0) setup codec checks ⟨.build session payload, trivial⟩).run e)).run w =
      (PqxdhDeploymentBackend.realReg setup codec route checks created ⟨.build session payload, trivial⟩).run
        (merge e w) := by
  obtain ⟨world, found, _, _, peersRaw⟩ := good.server
  rw [law_uncount, buildStep_effects, realReg_quiet setup codec checks route created _ (fun raw same => by cases same)]
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
theorem build_keeps (session : Nat) (payload : Option Pqxdh.Bytes) (e : EnvState KemSK Unit) (w : PqxdhRecordLiftWorld.State 0)
    (good : Good created e w) :
    ∀ result ∈ support ((simulateQ PqxdhRecordLiftWorld.effects
        ((PqxdhDeploymentEnvironment.realStep (n := 0) setup codec checks ⟨.build session payload, trivial⟩).run e)).run w),
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

/-- The environment state after the LQ snapshot of a finish at an owner. -/
def snapFinish {Bk : Type} (e : EnvState KemSK Bk) (index : Nat) : EnvState KemSK Bk :=
  { e with snap := PqxdhDeploymentLater.snapshotAt e.snap e.native.owners (some index) }

/-- The real environment's finish, run by the World with its counts forgotten: the snapshot, the forwarded owner finish read through `ctxEffects` on the World's cache, then the publication of the owner's change in the World. -/
theorem finishStep_effects (index : Nat) (raw : Pqxdh.Bytes) (e : EnvState KemSK Unit) (w : PqxdhRecordLiftWorld.State 0) :
    Prod.map id uncount <$> (simulateQ PqxdhRecordLiftWorld.effects
        ((PqxdhDeploymentEnvironment.realStep (n := 0) setup codec checks ⟨.finish index raw, trivial⟩).run e)).run w =
      match e.native.owners[index]? with
      | none => pure ((none, snapFinish e index), uncount w)
      | some before => (simulateQ (ctxEffects ctxAdmin) ((simulateQ (PqxdhDeploymentEnvironment.callbacksFwd (n := 0) setup
            codec) (PqxdhBeaconPhase2Publication.nativeOwner codec.frameRead raw before)).run e.native.shared)).run
              w.primitive.2 >>= fun result =>
          Prod.map id uncount <$> (simulateQ PqxdhRecordLiftWorld.effects
            (PqxdhDeploymentEnvironment.ownerEffect index before result.1.1.2 >>= fun _ =>
              pure (result.1.1.1, { snapFinish e index with
                native := strip ⟨result.1.2, e.native.owners.set index result.1.1.2⟩ }))).run (withCache w result.2) := by
  change Prod.map id uncount <$> (simulateQ PqxdhRecordLiftWorld.effects
    (PqxdhDeploymentEnvironment.finishStep (n := 0) setup codec index raw (snapFinish e index))).run w = _
  unfold PqxdhDeploymentEnvironment.finishStep
  dsimp only
  rcases owned : e.native.owners[index]? with _ | before
  · simp only [snapFinish, owned, simulateQ_pure, StateT.run_pure, map_pure]
    rfl
  · simp only [snapFinish, owned]
    rw [effects_then_free ctxAdmin _ (finishFwd_noAdmin setup codec _ _) _ (fun result => countFree_bind
      (countFree_ownerEffect _ _ _) fun _ => countFree_pure _) w]

/-- The registration state after a native finish on the reassembled state, from the forwarded finish's outcome and the resulting CTX cache. -/
def finishedState (owners : List (PqxdhRegistrationSchedule.Owner KemSK)) (server : RawCtxServerRouting.Server Unit Unit)
    (keyId : Std.U64) (index : Nat)
    (result : ((Option Pqxdh.Bytes × PqxdhRegistrationSchedule.Owner KemSK) × NativeState KemSK) ×
      CtxRomAuth.CtxRO.QueryCache) : PqxdhRegistrationSchedule.State KemSK :=
  { shared := (result.1.2.1, serverGame server keyId { result.1.2.2 with ctx := result.2 })
    owners := owners.set index result.1.1.2 }

/-- The native finish on the reassembled state at an owner that is not established: the forwarded owner finish on the environment's shared state, read through `ctxEffects` on the World's cache, with the World's routing record filled in. -/
theorem finish_native_run (index : Nat) (raw : Pqxdh.Bytes) (e : EnvState KemSK Unit) (w : PqxdhRecordLiftWorld.State 0)
    (good : Good created e w) (world : PqxdhRecordLiftWorld.Server) (found : w.server = some world)
    (before : PqxdhRegistrationSchedule.Owner KemSK) (owned : e.native.owners[index]? = some before)
    (inactive : ¬ RawCtxBeaconLifecycle.Established before.beacon.phase) :
    (PqxdhRegistrationSchedule.finish setup codec index raw).run (fill w e.native) =
      (fun result => (result.1.1.1, finishedState (fill w e.native).owners world.records.server
          e.native.shared.2.server.identityKeyId index result)) <$>
        (simulateQ (ctxEffects ctxAdmin) ((simulateQ (PqxdhDeploymentEnvironment.callbacksFwd (n := 0) setup codec)
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
    PqxdhDeploymentEnvironment.owner_factor (n := 0) ctxAdmin setup codec raw before,
    show ((e.native.shared.1, { e.native.shared.2 with ctx := w.primitive.2 }) : NativeState KemSK) =
      PqxdhDeploymentBackend.gameCtxLens.set e.native.shared w.primitive.2 from rfl,
    PqxdhDeploymentEnvironment.frame_program _ _ (PqxdhDeploymentEnvironment.callbacksFwd_frame setup codec),
    simulateQ_map, StateT.run_map]
  simp only [Functor.map_map]
  rfl

/-- The reassembled state after a finish that changed one owner and its World phase consistently. -/
theorem finish_merge_set (index : Nat) (e : EnvState KemSK Unit) (w : PqxdhRecordLiftWorld.State 0) (good : Good created e w)
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
theorem finish_outcome (index : Nat) (e : EnvState KemSK Unit) (w : PqxdhRecordLiftWorld.State 0) (good : Good created e w)
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
theorem finish_law (index : Nat) (raw : Pqxdh.Bytes) (e : EnvState KemSK Unit) (w : PqxdhRecordLiftWorld.State 0)
    (good : Good created e w) :
    (fun result => (result.1.1, merge result.1.2 result.2)) <$> (simulateQ PqxdhRecordLiftWorld.effects
        ((PqxdhDeploymentEnvironment.realStep (n := 0) setup codec checks ⟨.finish index raw, trivial⟩).run e)).run w =
      (PqxdhDeploymentBackend.realReg setup codec route checks created ⟨.finish index raw, trivial⟩).run (merge e w) := by
  obtain ⟨world, found, _, _, _⟩ := good.server
  rw [law_uncount, finishStep_effects, realReg_quiet setup codec checks route created _ (fun raw same => by cases same)]
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
theorem finish_keeps (index : Nat) (raw : Pqxdh.Bytes) (e : EnvState KemSK Unit) (w : PqxdhRecordLiftWorld.State 0)
    (good : Good created e w) :
    ∀ result ∈ support ((simulateQ PqxdhRecordLiftWorld.effects
        ((PqxdhDeploymentEnvironment.realStep (n := 0) setup codec checks ⟨.finish index raw, trivial⟩).run e)).run w),
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
theorem realReg_splits_create (pin : Pqxdh.Bytes) (keyId : Std.U64) (e : EnvState KemSK Unit)
    (w : PqxdhRecordLiftWorld.State 0) (good : Good created e w) :
    LawEq ((fun result => (result.1.1, merge result.1.2 result.2)) <$> (simulateQ PqxdhRecordLiftWorld.effects
        ((PqxdhDeploymentEnvironment.realStep (n := 0) setup codec checks ⟨.create pin keyId, trivial⟩).run e)).run w)
      ((PqxdhDeploymentBackend.realReg setup codec route checks created ⟨.create pin keyId, trivial⟩).run (merge e w)) ∧
    ∀ result ∈ support ((simulateQ PqxdhRecordLiftWorld.effects
        ((PqxdhDeploymentEnvironment.realStep (n := 0) setup codec checks ⟨.create pin keyId, trivial⟩).run e)).run w),
      Good created result.1.2 result.2 :=
  ⟨LawEq.of_eq (create_law setup codec checks route created pin keyId e w good),
    create_keeps setup codec checks created pin keyId e w good⟩

/-- The `bundle` command of the real environment splits the real registration handler: the reassembled law is the handler's (exactly) and admissibility is kept. -/
theorem realReg_splits_bundle (owner : Nat) (e : EnvState KemSK Unit)
    (w : PqxdhRecordLiftWorld.State 0) (good : Good created e w) :
    LawEq ((fun result => (result.1.1, merge result.1.2 result.2)) <$> (simulateQ PqxdhRecordLiftWorld.effects
        ((PqxdhDeploymentEnvironment.realStep (n := 0) setup codec checks ⟨.bundle owner, trivial⟩).run e)).run w)
      ((PqxdhDeploymentBackend.realReg setup codec route checks created ⟨.bundle owner, trivial⟩).run (merge e w)) ∧
    ∀ result ∈ support ((simulateQ PqxdhRecordLiftWorld.effects
        ((PqxdhDeploymentEnvironment.realStep (n := 0) setup codec checks ⟨.bundle owner, trivial⟩).run e)).run w),
      Good created result.1.2 result.2 :=
  ⟨LawEq.of_eq (bundle_law setup codec checks route created owner e w good),
    bundle_keeps setup codec checks created owner e w good⟩

/-- The `accept` command of the real environment splits the real registration handler: the reassembled law is the handler's (exactly) and admissibility is kept. -/
theorem realReg_splits_accept (raw : Pqxdh.Bytes) (e : EnvState KemSK Unit)
    (w : PqxdhRecordLiftWorld.State 0) (good : Good created e w) :
    LawEq ((fun result => (result.1.1, merge result.1.2 result.2)) <$> (simulateQ PqxdhRecordLiftWorld.effects
        ((PqxdhDeploymentEnvironment.realStep (n := 0) setup codec checks ⟨.accept raw, trivial⟩).run e)).run w)
      ((PqxdhDeploymentBackend.realReg setup codec route checks created ⟨.accept raw, trivial⟩).run (merge e w)) ∧
    ∀ result ∈ support ((simulateQ PqxdhRecordLiftWorld.effects
        ((PqxdhDeploymentEnvironment.realStep (n := 0) setup codec checks ⟨.accept raw, trivial⟩).run e)).run w),
      Good created result.1.2 result.2 :=
  ⟨LawEq.of_eq (accept_law setup codec checks route created raw e w good),
    accept_keeps setup codec checks created raw e w good⟩

/-- The `build` command of the real environment splits the real registration handler: the reassembled law is the handler's (exactly) and admissibility is kept. -/
theorem realReg_splits_build (session : Nat) (payload : Option Pqxdh.Bytes) (e : EnvState KemSK Unit)
    (w : PqxdhRecordLiftWorld.State 0) (good : Good created e w) :
    LawEq ((fun result => (result.1.1, merge result.1.2 result.2)) <$> (simulateQ PqxdhRecordLiftWorld.effects
        ((PqxdhDeploymentEnvironment.realStep (n := 0) setup codec checks ⟨.build session payload, trivial⟩).run e)).run w)
      ((PqxdhDeploymentBackend.realReg setup codec route checks created ⟨.build session payload, trivial⟩).run (merge e w)) ∧
    ∀ result ∈ support ((simulateQ PqxdhRecordLiftWorld.effects
        ((PqxdhDeploymentEnvironment.realStep (n := 0) setup codec checks ⟨.build session payload, trivial⟩).run e)).run w),
      Good created result.1.2 result.2 :=
  ⟨LawEq.of_eq (build_law setup codec checks route created session payload e w good),
    build_keeps setup codec checks created session payload e w good⟩

/-- The `finish` command of the real environment splits the real registration handler: the reassembled law is the handler's (exactly) and admissibility is kept. -/
theorem realReg_splits_finish (owner : Nat) (raw : Pqxdh.Bytes) (e : EnvState KemSK Unit)
    (w : PqxdhRecordLiftWorld.State 0) (good : Good created e w) :
    LawEq ((fun result => (result.1.1, merge result.1.2 result.2)) <$> (simulateQ PqxdhRecordLiftWorld.effects
        ((PqxdhDeploymentEnvironment.realStep (n := 0) setup codec checks ⟨.finish owner raw, trivial⟩).run e)).run w)
      ((PqxdhDeploymentBackend.realReg setup codec route checks created ⟨.finish owner raw, trivial⟩).run (merge e w)) ∧
    ∀ result ∈ support ((simulateQ PqxdhRecordLiftWorld.effects
        ((PqxdhDeploymentEnvironment.realStep (n := 0) setup codec checks ⟨.finish owner raw, trivial⟩).run e)).run w),
      Good created result.1.2 result.2 :=
  ⟨LawEq.of_eq (finish_law setup codec checks route created owner raw e w good),
    finish_keeps setup codec checks created owner raw e w good⟩

/-- The `hmac` command of the real environment splits the real registration handler: the reassembled law is the handler's (exactly) and admissibility is kept. -/
theorem realReg_splits_hmac (key : PqxdhSecretInputKdf.HmacBlock) (message : Pqxdh.Bytes) (e : EnvState KemSK Unit)
    (w : PqxdhRecordLiftWorld.State 0) (good : Good created e w) :
    LawEq ((fun result => (result.1.1, merge result.1.2 result.2)) <$> (simulateQ PqxdhRecordLiftWorld.effects
        ((PqxdhDeploymentEnvironment.realStep (n := 0) setup codec checks ⟨.hmac key message, trivial⟩).run e)).run w)
      ((PqxdhDeploymentBackend.realReg setup codec route checks created ⟨.hmac key message, trivial⟩).run (merge e w)) ∧
    ∀ result ∈ support ((simulateQ PqxdhRecordLiftWorld.effects
        ((PqxdhDeploymentEnvironment.realStep (n := 0) setup codec checks ⟨.hmac key message, trivial⟩).run e)).run w),
      Good created result.1.2 result.2 :=
  ⟨LawEq.of_eq (hmac_law setup codec checks route created key message e w good),
    hmac_keeps setup codec checks created key message e w good⟩

end Commands

/-! ### The real splits, C1 and C6 for the real registration -/

section Real
variable {ι : Type} {baseSpec : OracleSpec ι} {Reader Response A X Out : Type}
  (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
  (route : RawCtxServerRouting.SenderDecoder)

/-- The per-command real splits: the real environment `realStep` splits the real registration handler `realReg` (the LQ-F run-phase handler) of every constructed Server, relative to the trivial admissibility predicate (the real environment installs only known kernels, so no used-marker condition is needed). -/
theorem real_splits (created : PqxdhLiveServerConstruction.Created Unit) :
    Splits created (PqxdhDeploymentBackend.realReg setup codec route checks created)
      (PqxdhDeploymentEnvironment.realStep (n := 0) setup codec checks) (fun _ _ => True) := by
  rw [PqxdhDeploymentEnvironmentJoin.splits_true]
  intro query e w good
  rcases query with ⟨command, allowed⟩
  cases command with
  | create pin keyId => exact realReg_splits_create setup codec checks route created pin keyId e w good
  | bundle owner => exact realReg_splits_bundle setup codec checks route created owner e w good
  | accept raw => exact realReg_splits_accept setup codec checks route created raw e w good
  | build session payload => exact realReg_splits_build setup codec checks route created session payload e w good
  | finish owner raw => exact realReg_splits_finish setup codec checks route created owner raw e w good
  | hmac key message => exact realReg_splits_hmac setup codec checks route created key message e w good
  | hash _ => exact absurd allowed id
  | serverSend _ _ => exact absurd allowed id
  | serverRaw _ => exact absurd allowed id
  | beaconSend _ _ => exact absurd allowed id
  | beaconRaw _ _ => exact absurd allowed id

/-- C1 for the real registration (cuttable validation, critique m12): the common deployment experiment with the real registration handler and the record world with the real environment `envReal` have the same law of the Server's public data, the adversary's output, the ledger and the full reassembled final state. -/
theorem c1_real (ensureInit : StateT A ProbComp Bool) (identityIndex : Nat) (runtime : A)
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (adversary : OracleComp (PqxdhDeploymentInterface.ModeSpec mode) X) :
    LawEq ((gameWith setup codec route (fun _ => ()) (PqxdhDeploymentBackend.realReg setup codec route checks) ensureInit
        identityIndex bounds mode adversary).run' runtime)
      (PqxdhDeploymentEnvironmentJoin.joined <$> PqxdhRecordLiftWorld.run setup codec route
        (PqxdhDeploymentEnvironment.envReal (n := 0) setup codec checks ensureInit identityIndex runtime) setup.serverKeyId
          bounds mode adversary) :=
  PqxdhDeploymentEnvironmentJoin.join setup codec route (fun _ => ()) (PqxdhDeploymentBackend.realReg setup codec route checks)
    (PqxdhDeploymentEnvironment.envReal setup codec checks ensureInit identityIndex runtime) ensureInit identityIndex runtime
    rfl (fun _ _ => True) PqxdhDeploymentEnvironmentJoin.stable_true (fun _ => trivial) (real_splits setup codec checks route)
    bounds mode adversary

/-- C1 for the real registration against the classical common deployment experiment: `PqxdhDeploymentSecrecy.game` has the law of the record world with the real environment, projected to the Server's public data, the adversary's output, the ledger and the reassembled deployment state. -/
theorem c1_real_classical (ensureInit : StateT A ProbComp Bool) (identityIndex : Nat) (runtime : A)
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (adversary : OracleComp (PqxdhDeploymentInterface.ModeSpec mode) X) :
    LawEq ((PqxdhDeploymentSecrecy.game setup codec checks route ensureInit identityIndex bounds mode adversary).run' runtime)
      ((fun result => result.1.map fun value => (value.1, value.2.1.1, (value.2.1.2, (merge value.2.2 result.2).base))) <$>
        PqxdhRecordLiftWorld.run setup codec route
          (PqxdhDeploymentEnvironment.envReal (n := 0) setup codec checks ensureInit identityIndex runtime) setup.serverKeyId
            bounds mode adversary) := by
  have projected := (c1_real setup codec checks route ensureInit identityIndex runtime bounds mode adversary).map
    (fun outcome => outcome.map fun result => (result.1, result.2.1, (result.2.2.1, result.2.2.2.base)))
  rw [Functor.map_map] at projected
  have classical := congrArg (fun run => Prod.fst <$> run)
    (PqxdhDeploymentBackend.gameWith_classical setup codec route checks ensureInit identityIndex bounds mode adversary runtime)
  simp only [Functor.map_map] at classical
  rw [StateT.run'_eq, ← classical]
  refine (LawEq.of_eq ?_).trans (projected.trans (LawEq.of_eq ?_))
  · rw [StateT.run'_eq, Functor.map_map]
  · congr 1
    funext result
    rcases result with ⟨_ | value, w⟩ <;> rfl

/-- C1 for the real registration against the LQ-F run phase (`PqxdhDeploymentLaterServerGame.runPhase`): its law is the record world's with the real environment, projected to the Server's public data, the adversary's output, the ledger and the LQ-F view (snapshot, reassembled deployment state, ephemeral log). -/
theorem c1_real_runPhase (ensureInit : StateT A ProbComp Bool) (identityIndex : Nat) (runtime : A)
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (adversary : OracleComp (PqxdhDeploymentInterface.ModeSpec mode) X) :
    LawEq ((PqxdhDeploymentLaterServerGame.runPhase setup codec checks route ensureInit identityIndex bounds mode
        adversary).run' runtime)
      ((fun result => result.1.map fun value => (value.1, value.2.1.1,
          (value.2.1.2, PqxdhDeploymentBackend.laterView (merge value.2.2 result.2)))) <$>
        PqxdhRecordLiftWorld.run setup codec route
          (PqxdhDeploymentEnvironment.envReal (n := 0) setup codec checks ensureInit identityIndex runtime) setup.serverKeyId
            bounds mode adversary) := by
  have projected := (c1_real setup codec checks route ensureInit identityIndex runtime bounds mode adversary).map
    (fun outcome => outcome.map fun result => (result.1, result.2.1, (result.2.2.1, PqxdhDeploymentBackend.laterView
      result.2.2.2)))
  rw [Functor.map_map] at projected
  have real := congrArg (fun run => Prod.fst <$> run)
    (PqxdhDeploymentBackend.gameWith_real setup codec route checks ensureInit identityIndex bounds mode adversary runtime)
  simp only [Functor.map_map] at real
  rw [StateT.run'_eq, ← real]
  refine (LawEq.of_eq ?_).trans (projected.trans (LawEq.of_eq ?_))
  · rw [StateT.run'_eq, Functor.map_map]
  · congr 1
    funext result
    rcases result with ⟨_ | value, w⟩ <;> rfl

/-- The observed projection of C1 for the real registration (`PqxdhRecordLiftWorld.game`): the adversary's output, the ledger and the produced frames of the common deployment experiment with the real registration handler have the law of the record world's game with the real environment. -/
theorem c1_real_observed (ensureInit : StateT A ProbComp Bool) (identityIndex : Nat) (runtime : A)
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (adversary : OracleComp (PqxdhDeploymentInterface.ModeSpec mode) X) :
    LawEq ((fun outcome => outcome.map fun value => (value.2.1, value.2.2.1, value.2.2.2.base.produced)) <$>
        (gameWith setup codec route (fun _ => ()) (PqxdhDeploymentBackend.realReg setup codec route checks) ensureInit
          identityIndex bounds mode adversary).run' runtime)
      (PqxdhRecordLiftWorld.game setup codec route
        (PqxdhDeploymentEnvironment.envReal (n := 0) setup codec checks ensureInit identityIndex runtime) setup.serverKeyId
          bounds mode adversary) :=
  PqxdhDeploymentEnvironmentJoin.join_observed setup codec route (fun _ => ())
    (PqxdhDeploymentBackend.realReg setup codec route checks)
    (PqxdhDeploymentEnvironment.envReal setup codec checks ensureInit identityIndex runtime) ensureInit identityIndex runtime
    rfl (fun _ _ => True) PqxdhDeploymentEnvironmentJoin.stable_true (fun _ => trivial) (real_splits setup codec checks route)
    bounds mode adversary

/-- C3 for the real registration: jointly with the Server's public data, the output and the ledger, the final CTX cache of the common deployment experiment with the real registration handler has the law of the World's shared cache with the real environment. -/
theorem c3_real (ensureInit : StateT A ProbComp Bool) (identityIndex : Nat) (runtime : A)
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (adversary : OracleComp (PqxdhDeploymentInterface.ModeSpec mode) X) :
    LawEq ((fun outcome => outcome.map fun value => (value.1, value.2.1, value.2.2.1,
        value.2.2.2.base.native.shared.2.ctx)) <$>
        (gameWith setup codec route (fun _ => ()) (PqxdhDeploymentBackend.realReg setup codec route checks) ensureInit
          identityIndex bounds mode adversary).run' runtime)
      ((fun result => result.1.map fun value => (value.1, value.2.1.1, value.2.1.2, result.2.primitive.2)) <$>
        PqxdhRecordLiftWorld.run setup codec route
          (PqxdhDeploymentEnvironment.envReal (n := 0) setup codec checks ensureInit identityIndex runtime) setup.serverKeyId
            bounds mode adversary) :=
  PqxdhDeploymentEnvironmentJoin.c3_shared_cache setup codec route (fun _ => ())
    (PqxdhDeploymentBackend.realReg setup codec route checks)
    (PqxdhDeploymentEnvironment.envReal setup codec checks ensureInit identityIndex runtime) ensureInit identityIndex runtime
    rfl (fun _ _ => True) PqxdhDeploymentEnvironmentJoin.stable_true (fun _ => trivial) (real_splits setup codec checks route)
    bounds mode adversary

/-- The post phase of the native later game with the real registration handler is LQ-F's post-run handler on the deployment state. -/
theorem postNative_real (created : PqxdhLiveServerConstruction.Created Unit) :
    PqxdhDeploymentEnvironmentJoin.postNative setup codec route (PqxdhDeploymentBackend.realReg setup codec route checks created) =
      PqxdhDeploymentFinishErasure.realPost setup codec checks created := by
  funext query
  rcases query with coin | (⟨key, message⟩ | bytes)
  · apply StateT.ext
    intro state
    simp only [PqxdhDeploymentEnvironmentJoin.postNative, QueryImpl.apply_compose, PqxdhDeploymentLater.postEmbed,
      simulateQ_spec_query, handlerWith, PqxdhDeploymentFinishErasure.realPost, PqxdhDeploymentLater.postImpl,
      PqxdhDeploymentBackend.onBase, StateT.run_lift]
    simp only [LazyOracleDiscard.StateLens.lift, PqxdhDeploymentBackend.baseLens, StateT.run, bind_pure_comp]
    rfl
  · apply StateT.ext
    intro state
    simp only [PqxdhDeploymentEnvironmentJoin.postNative, QueryImpl.apply_compose, PqxdhDeploymentLater.postEmbed,
      simulateQ_spec_query, handlerWith, PqxdhDeploymentFinishErasure.realPost, PqxdhDeploymentLater.postImpl]
    rw [realReg_quiet setup codec checks route created ⟨.hmac key message, trivial⟩ (fun raw same => by cases same)]
    simp only [PqxdhDeploymentNative.handler, PqxdhDeploymentBackend.onBase, LazyOracleDiscard.StateLens.lift,
      PqxdhDeploymentBackend.baseLens, StateT.run]
    rfl
  · simp only [PqxdhDeploymentEnvironmentJoin.postNative, QueryImpl.apply_compose, PqxdhDeploymentLater.postEmbed,
      simulateQ_spec_query, handlerWith, PqxdhDeploymentFinishErasure.realPost, PqxdhDeploymentLater.postImpl,
      PqxdhRegistrationSchedule.handler]

/-- C6 for the real registration (cuttable validation, critique m12): the LQ-F later game (`PqxdhDeploymentLaterServerGame.game`) has the law of the later record world (`PqxdhRecordLiftLater.run`) with the real environment and the environment's reveal `envReveal`, projected to the Server's public data, the second adversary's output, the run-phase ledger and the LQ-F view of the reassembled final state. -/
theorem c6_real (ensureInit : StateT A ProbComp Bool) (identityIndex : Nat) (runtime : A)
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (first : OracleComp (PqxdhDeploymentInterface.ModeSpec mode) X)
    (second : X → PqxdhDeploymentLaterServerGame.Reveal → OracleComp PqxdhDeploymentLater.PostSpec Out) :
    LawEq ((PqxdhDeploymentLaterServerGame.game setup codec checks route ensureInit identityIndex bounds mode first
        second).run' runtime)
      ((fun result => result.1.map fun value => (value.1, value.2.1.1,
          (value.2.1.2, PqxdhDeploymentBackend.laterView (merge value.2.2 result.2)))) <$>
        PqxdhRecordLiftLater.run setup codec route
          (PqxdhDeploymentEnvironment.envReal (n := 0) setup codec checks ensureInit identityIndex runtime) setup.serverKeyId
            bounds mode PqxdhDeploymentEnvironmentJoin.envReveal first second) := by
  have joined := PqxdhDeploymentEnvironmentJoin.join_later setup codec route (fun _ => ())
    (PqxdhDeploymentBackend.realReg setup codec route checks)
    (PqxdhDeploymentEnvironment.envReal setup codec checks ensureInit identityIndex runtime) ensureInit identityIndex runtime
    rfl (fun _ _ => True) PqxdhDeploymentEnvironmentJoin.stable_true (fun _ => trivial) (real_splits setup codec checks route)
    bounds mode first second
  rw [show (fun created => PqxdhDeploymentEnvironmentJoin.postNative setup codec route
      (PqxdhDeploymentBackend.realReg setup codec route checks created)) =
    PqxdhDeploymentFinishErasure.realPost setup codec checks from funext (postNative_real setup codec checks route)] at joined
  have projected := joined.map (fun outcome => outcome.map fun result => (result.1, result.2.1,
    (result.2.2.1, PqxdhDeploymentBackend.laterView result.2.2.2)))
  rw [Functor.map_map] at projected
  have real := congrArg (fun run => Prod.fst <$> run)
    (PqxdhDeploymentFinishErasure.laterWith_real setup codec route checks ensureInit identityIndex bounds mode first second
      runtime)
  simp only [Functor.map_map] at real
  rw [StateT.run'_eq, ← real]
  refine (LawEq.of_eq ?_).trans (projected.trans (LawEq.of_eq ?_))
  · rw [StateT.run'_eq, Functor.map_map]
  · congr 1
    funext result
    rcases result with ⟨_ | value, w⟩ <;> rfl

/-- The analysis projection of C1 for the real registration (`PqxdhRecordLiftWorld.analysis`): the adversary's output, the ledger, the produced frames and the raw-attempt counters of the common deployment experiment with the real registration handler have the law of the record world's analysis projection with the real environment. -/
theorem c1_real_analysis (ensureInit : StateT A ProbComp Bool) (identityIndex : Nat) (runtime : A)
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (adversary : OracleComp (PqxdhDeploymentInterface.ModeSpec mode) X) :
    LawEq ((fun outcome => outcome.map fun value => (value.2.1, value.2.2.1, value.2.2.2.base.produced,
        (⟨value.2.2.2.base.serverRaw, value.2.2.2.base.ownerRaw⟩ : PqxdhRecordLiftWorld.RawCounters))) <$>
        (gameWith setup codec route (fun _ => ()) (PqxdhDeploymentBackend.realReg setup codec route checks) ensureInit
          identityIndex bounds mode adversary).run' runtime)
      (PqxdhRecordLiftWorld.analysis <$> PqxdhRecordLiftWorld.run setup codec route
        (PqxdhDeploymentEnvironment.envReal (n := 0) setup codec checks ensureInit identityIndex runtime) setup.serverKeyId
          bounds mode adversary) :=
  PqxdhDeploymentEnvironmentJoin.join_analysis setup codec route (fun _ => ())
    (PqxdhDeploymentBackend.realReg setup codec route checks)
    (PqxdhDeploymentEnvironment.envReal setup codec checks ensureInit identityIndex runtime) ensureInit identityIndex runtime
    rfl (fun _ _ => True) PqxdhDeploymentEnvironmentJoin.stable_true (fun _ => trivial) (real_splits setup codec checks route)
    bounds mode adversary

/-- The run-phase reveal projection of C1 for the real registration (`join_reveal`): the Server's public data, the adversary's output, the ledger and the Beacon-side reveal with the Server ephemeral log of the final state have the same law in the common deployment experiment with the real registration handler and in the record world with the real environment. -/
theorem c1_real_reveal (ensureInit : StateT A ProbComp Bool) (identityIndex : Nat) (runtime : A)
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (adversary : OracleComp (PqxdhDeploymentInterface.ModeSpec mode) X) :
    LawEq ((fun outcome => outcome.map fun value => (value.1, value.2.1, value.2.2.1,
        (PqxdhDeploymentLater.revealOf value.2.2.2.base.native.owners value.2.2.2.snap, value.2.2.2.log))) <$>
        (gameWith setup codec route (fun _ => ()) (PqxdhDeploymentBackend.realReg setup codec route checks) ensureInit
          identityIndex bounds mode adversary).run' runtime)
      ((fun result => result.1.map fun value => (value.1, value.2.1.1, value.2.1.2,
          (PqxdhDeploymentLater.revealOf value.2.2.native.owners value.2.2.snap, value.2.2.log))) <$>
        PqxdhRecordLiftWorld.run setup codec route
          (PqxdhDeploymentEnvironment.envReal (n := 0) setup codec checks ensureInit identityIndex runtime) setup.serverKeyId
            bounds mode adversary) :=
  PqxdhDeploymentEnvironmentJoin.join_reveal setup codec route (fun _ => ())
    (PqxdhDeploymentBackend.realReg setup codec route checks)
    (PqxdhDeploymentEnvironment.envReal setup codec checks ensureInit identityIndex runtime) ensureInit identityIndex runtime
    rfl (fun _ _ => True) PqxdhDeploymentEnvironmentJoin.stable_true (fun _ => trivial) (real_splits setup codec checks route)
    bounds mode adversary

/-- The observed projection of C1 for the real registration with the classical common deployment experiment on the left: the adversary's output, the ledger and the produced frames of `PqxdhDeploymentSecrecy.game` have the law of the record world's game (`PqxdhRecordLiftWorld.game`) with the real environment. -/
theorem c1_real_classical_observed (ensureInit : StateT A ProbComp Bool) (identityIndex : Nat) (runtime : A)
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (adversary : OracleComp (PqxdhDeploymentInterface.ModeSpec mode) X) :
    LawEq ((fun outcome => outcome.map fun value => (value.2.1, value.2.2.1, value.2.2.2.produced)) <$>
        (PqxdhDeploymentSecrecy.game setup codec checks route ensureInit identityIndex bounds mode adversary).run' runtime)
      (PqxdhRecordLiftWorld.game setup codec route
        (PqxdhDeploymentEnvironment.envReal (n := 0) setup codec checks ensureInit identityIndex runtime) setup.serverKeyId
          bounds mode adversary) := by
  have projected := (c1_real_classical setup codec checks route ensureInit identityIndex runtime bounds mode adversary).map
    (fun outcome => outcome.map fun value => (value.2.1, value.2.2.1, value.2.2.2.produced))
  rw [Functor.map_map] at projected
  refine projected.trans (LawEq.of_eq ?_)
  unfold PqxdhRecordLiftWorld.game
  congr 1
  funext result
  rcases result with ⟨_ | value, w⟩ <;> rfl

/-- The analysis projection of C1 for the real registration with the classical common deployment experiment on the left: the adversary's output, the ledger, the produced frames and the raw-attempt counters of `PqxdhDeploymentSecrecy.game` have the law of the record world's analysis projection (`PqxdhRecordLiftWorld.analysis`) with the real environment. -/
theorem c1_real_classical_analysis (ensureInit : StateT A ProbComp Bool) (identityIndex : Nat) (runtime : A)
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (adversary : OracleComp (PqxdhDeploymentInterface.ModeSpec mode) X) :
    LawEq ((fun outcome => outcome.map fun value => (value.2.1, value.2.2.1, value.2.2.2.produced,
        (⟨value.2.2.2.serverRaw, value.2.2.2.ownerRaw⟩ : PqxdhRecordLiftWorld.RawCounters))) <$>
        (PqxdhDeploymentSecrecy.game setup codec checks route ensureInit identityIndex bounds mode adversary).run' runtime)
      (PqxdhRecordLiftWorld.analysis <$> PqxdhRecordLiftWorld.run setup codec route
        (PqxdhDeploymentEnvironment.envReal (n := 0) setup codec checks ensureInit identityIndex runtime) setup.serverKeyId
          bounds mode adversary) := by
  have projected := (c1_real_classical setup codec checks route ensureInit identityIndex runtime bounds mode adversary).map
    (fun outcome => outcome.map fun value => (value.2.1, value.2.2.1, value.2.2.2.produced,
      (⟨value.2.2.2.serverRaw, value.2.2.2.ownerRaw⟩ : PqxdhRecordLiftWorld.RawCounters)))
  rw [Functor.map_map] at projected
  refine projected.trans (LawEq.of_eq ?_)
  congr 1
  funext result
  rcases result with ⟨_ | value, w⟩ <;> rfl

/-- C6 for the real registration, public form (`join_later_public`): the Server's public data, the second adversary's output, the run-phase ledger, the record view (produced frames and raw-attempt counters) and the Beacon-side reveal with the Server ephemeral log of the final state have the same law in the LQ-F later game (`PqxdhDeploymentLaterServerGame.game`) and in the later record world with the real environment and `envReveal`. -/
theorem c6_real_public (ensureInit : StateT A ProbComp Bool) (identityIndex : Nat) (runtime : A)
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (first : OracleComp (PqxdhDeploymentInterface.ModeSpec mode) X)
    (second : X → PqxdhDeploymentLaterServerGame.Reveal → OracleComp PqxdhDeploymentLater.PostSpec Out) :
    LawEq ((fun outcome => outcome.map fun value => (value.1, value.2.1, value.2.2.1,
        (value.2.2.2.2.1.produced,
          (⟨value.2.2.2.2.1.serverRaw, value.2.2.2.2.1.ownerRaw⟩ : PqxdhRecordLiftWorld.RawCounters)),
        (PqxdhDeploymentLater.revealOf value.2.2.2.2.1.native.owners value.2.2.2.1, value.2.2.2.2.2))) <$>
        (PqxdhDeploymentLaterServerGame.game setup codec checks route ensureInit identityIndex bounds mode first
          second).run' runtime)
      ((fun result => result.1.map fun value => (value.1, value.2.1.1, value.2.1.2,
          PqxdhRecordLiftLater.recordView result.2,
          (PqxdhDeploymentLater.revealOf value.2.2.native.owners value.2.2.snap, value.2.2.log))) <$>
        PqxdhRecordLiftLater.run setup codec route
          (PqxdhDeploymentEnvironment.envReal (n := 0) setup codec checks ensureInit identityIndex runtime) setup.serverKeyId
            bounds mode PqxdhDeploymentEnvironmentJoin.envReveal first second) := by
  have projected := (c6_real setup codec checks route ensureInit identityIndex runtime bounds mode first second).map
    (fun outcome => outcome.map fun value => (value.1, value.2.1, value.2.2.1,
      (value.2.2.2.2.1.produced,
        (⟨value.2.2.2.2.1.serverRaw, value.2.2.2.2.1.ownerRaw⟩ : PqxdhRecordLiftWorld.RawCounters)),
      (PqxdhDeploymentLater.revealOf value.2.2.2.2.1.native.owners value.2.2.2.1, value.2.2.2.2.2)))
  rw [Functor.map_map] at projected
  refine projected.trans (LawEq.of_eq ?_)
  congr 1
  funext result
  rcases result with ⟨_ | value, w⟩
  · rfl
  · simp only [Option.map_some, Option.some.injEq]
    rw [show (PqxdhDeploymentBackend.laterView (merge value.2.2 w)).2.1.native.owners =
      (fill w value.2.2.native).owners from rfl, PqxdhDeploymentEnvironmentJoin.revealOf_fill]
    rfl

end Real

end BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentReal

-- Axiom guards (generated)

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentReal.effects_query_ctx' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentReal.effects_query_ctx

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentReal.effects_ctx' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentReal.effects_ctx

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentReal.coins_noAdmin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentReal.coins_noAdmin

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentReal.effects_coins' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentReal.effects_coins

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentReal.effects_then' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentReal.effects_then

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentReal.effects_map' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentReal.effects_map

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentReal.effects_issue' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentReal.effects_issue

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentReal.effects_issue_then' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentReal.effects_issue_then

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentReal.effects_append' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentReal.effects_append

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentReal.effects_advance' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentReal.effects_advance

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentReal.effects_installServer' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentReal.effects_installServer

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentReal.effects_installBeacon' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentReal.effects_installBeacon

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentReal.countFree_pure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentReal.countFree_pure

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentReal.countFree_bind' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentReal.countFree_bind

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentReal.countFree_issue' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentReal.countFree_issue

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentReal.effects_then_free' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentReal.effects_then_free

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentReal.countFree_ownerEffect' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentReal.countFree_ownerEffect

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentReal.countFree_ownerChange' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentReal.countFree_ownerChange

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentReal.countFree_serverEffect' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentReal.countFree_serverEffect

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentReal.nframe_pure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentReal.nframe_pure

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentReal.nframe_bind' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentReal.nframe_bind

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentReal.nframe_local' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentReal.nframe_local

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentReal.nframe_family' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentReal.nframe_family

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentReal.nframe_coins' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentReal.nframe_coins

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentReal.nframe_simulateQ' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentReal.nframe_simulateQ

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentReal.nframe_fixed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentReal.nframe_fixed

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentReal.nativeHmac_nframe' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentReal.nativeHmac_nframe

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentReal.romRoot_nframe' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentReal.romRoot_nframe

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentReal.nativeClient_nframe' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentReal.nativeClient_nframe

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentReal.acceptRest_nframe' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentReal.acceptRest_nframe

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentReal.acceptLogged_nframe' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentReal.acceptLogged_nframe

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentReal.callbacks_nframe' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentReal.callbacks_nframe

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentReal.fill_some' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentReal.fill_some

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentReal.stripPhase_idem' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentReal.stripPhase_idem

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentReal.projectPhase_stripOwner' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentReal.projectPhase_stripOwner

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentReal.stripOwner_inactive' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentReal.stripOwner_inactive

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentReal.fillOwner_strip' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentReal.fillOwner_strip

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentReal.fill_strip' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentReal.fill_strip

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentReal.fillOwner_fields' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentReal.fillOwner_fields

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentReal.snapshotAt_fill' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentReal.snapshotAt_fill

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentReal.fillOwner_inactive' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentReal.fillOwner_inactive

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentReal.good_matched' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentReal.good_matched

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentReal.good_intro' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentReal.good_intro

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentReal.merge_uncount' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentReal.merge_uncount

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentReal.law_uncount' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentReal.law_uncount

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentReal.keeps_uncount' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentReal.keeps_uncount

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentReal.good_uncount' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentReal.good_uncount

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentReal.matched_append' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentReal.matched_append

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentReal.fill_append_owner' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentReal.fill_append_owner

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentReal.good_server' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentReal.good_server

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentReal.uncount_good' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentReal.uncount_good

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentReal.fill_set' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentReal.fill_set

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentReal.matched_set' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentReal.matched_set

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentReal.fill_inactive' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentReal.fill_inactive

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentReal.map_congr_support' depends on axioms: [propext,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentReal.map_congr_support

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentReal.shared_outcome' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentReal.shared_outcome

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentReal.shared_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentReal.shared_run

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentReal.shared_fill' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentReal.shared_fill

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentReal.shared_good' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentReal.shared_good

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentReal.afterSigning_shape' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentReal.afterSigning_shape

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentReal.afterGenerated_shape' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentReal.afterGenerated_shape

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentReal.bundle_shape' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentReal.bundle_shape

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentReal.afterInitialization_shape' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentReal.afterInitialization_shape

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentReal.continueRust_shape' depends on axioms: [propext,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentReal.continueRust_shape

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentReal.candidateTail_shape' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentReal.candidateTail_shape

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentReal.build_shape' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentReal.build_shape

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentReal.ownerEffect_same' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentReal.ownerEffect_same

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentReal.ownerChange_set' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentReal.ownerChange_set

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentReal.ownerEffect_publish' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentReal.ownerEffect_publish

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentReal.established_terminal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentReal.established_terminal

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentReal.override_world' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentReal.override_world

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentReal.installed_world' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentReal.installed_world

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentReal.override_publish' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentReal.override_publish

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentReal.run_support' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentReal.run_support

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentReal.callbacksFwd_noAdmin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentReal.callbacksFwd_noAdmin

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentReal.finishFwd_noAdmin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentReal.finishFwd_noAdmin

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentReal.callbacksFwd_game' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentReal.callbacksFwd_game

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentReal.finishFwd_game' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentReal.finishFwd_game

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentReal.commit_shape' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentReal.commit_shape

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentReal.finish_shape' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentReal.finish_shape

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentReal.ownerEffect_abort' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentReal.ownerEffect_abort

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentReal.ownerEffect_establish' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentReal.ownerEffect_establish

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentReal.fillOwner_self' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentReal.fillOwner_self

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentReal.onNative_run' does not depend on any axioms
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentReal.onNative_run

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentReal.onShared_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentReal.onShared_run

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentReal.create_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentReal.create_run

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentReal.realReg_quiet' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentReal.realReg_quiet

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentReal.createStep_effects' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentReal.createStep_effects

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentReal.create_merge' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentReal.create_merge

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentReal.create_law' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentReal.create_law

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentReal.create_keeps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentReal.create_keeps

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentReal.hmac_frame' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentReal.hmac_frame

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentReal.hmacStep_effects' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentReal.hmacStep_effects

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentReal.hmac_law' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentReal.hmac_law

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentReal.hmac_keeps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentReal.hmac_keeps

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentReal.accept_frame' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentReal.accept_frame

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentReal.realReg_accept' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentReal.realReg_accept

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentReal.acceptStep_effects' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentReal.acceptStep_effects

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentReal.accept_law' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentReal.accept_law

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentReal.accept_keeps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentReal.accept_keeps

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentReal.bundle_run_missing' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentReal.bundle_run_missing

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentReal.bundle_run_found' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentReal.bundle_run_found

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentReal.bundleStep_effects' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentReal.bundleStep_effects

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentReal.bundle_outcome' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentReal.bundle_outcome

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentReal.bundle_law' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentReal.bundle_law

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentReal.bundle_keeps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentReal.bundle_keeps

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentReal.nativeBuild_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentReal.nativeBuild_run

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentReal.buildStep_effects' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentReal.buildStep_effects

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentReal.frameGame_server' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentReal.frameGame_server

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentReal.build_merge' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentReal.build_merge

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentReal.withCache_server' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentReal.withCache_server

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentReal.builtNative_quiet' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentReal.builtNative_quiet

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentReal.build_outcome' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentReal.build_outcome

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentReal.build_law' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentReal.build_law

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentReal.build_keeps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentReal.build_keeps

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentReal.finishStep_effects' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentReal.finishStep_effects

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentReal.finish_native_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentReal.finish_native_run

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentReal.finish_merge_set' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentReal.finish_merge_set

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentReal.finish_outcome' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentReal.finish_outcome

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentReal.finish_law' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentReal.finish_law

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentReal.finish_keeps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentReal.finish_keeps

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentReal.realReg_splits_create' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentReal.realReg_splits_create

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentReal.realReg_splits_bundle' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentReal.realReg_splits_bundle

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentReal.realReg_splits_accept' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentReal.realReg_splits_accept

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentReal.realReg_splits_build' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentReal.realReg_splits_build

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentReal.realReg_splits_finish' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentReal.realReg_splits_finish

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentReal.realReg_splits_hmac' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentReal.realReg_splits_hmac

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentReal.real_splits' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentReal.real_splits

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentReal.c1_real' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentReal.c1_real

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentReal.c1_real_classical' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentReal.c1_real_classical

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentReal.c1_real_runPhase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentReal.c1_real_runPhase

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentReal.c1_real_observed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentReal.c1_real_observed

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentReal.c3_real' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentReal.c3_real

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentReal.postNative_real' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentReal.postNative_real

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentReal.c6_real' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentReal.c6_real

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentReal.c1_real_analysis' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentReal.c1_real_analysis

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentReal.c1_real_reveal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentReal.c1_real_reveal

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentReal.c1_real_classical_observed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentReal.c1_real_classical_observed

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentReal.c1_real_classical_analysis' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentReal.c1_real_classical_analysis

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentReal.c6_real_public' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentReal.c6_real_public
