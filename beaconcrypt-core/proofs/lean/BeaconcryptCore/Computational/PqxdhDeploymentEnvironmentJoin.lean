-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhDeploymentEnvironment
import BeaconcryptCore.Computational.PqxdhDeploymentFinishErasure

/-!
# The join of the native deployment game and the record world (CE-11a, unit 11a-4)

C1, C3 and C6 of the record-lift hand-off in generic form: for every registration handler `reg` of the native deployment game with a pluggable registration handler (`PqxdhDeploymentBackend.gameWith`) and every environment of the record-lift capability boundary that splits it, the common deployment experiment and the record world (`PqxdhRecordLiftWorld.run`) have the same law.

**Reassembly (design-v2 section 5.9).** `merge e w` puts the World's record coordinates into the environment's stripped registration state (`fill`: the World's Server peer map with its kernels, the World's established shells and kernels, the World's shared CTX cache) and adds the World's raw-attempt counters, produced frames and seed table. It reads no instrumentation (`merge_forget`). `Good created e w` is the admissibility invariant: the environment state is stripped and holds the constructed Server, the World's Server is initialized with the environment's sender and identity and has the environment's peers up to their kernels, and the World's owners are the environment's owners phase by phase up to their kernels. `Splits created reg step` says that from every admissible joint state each registration command of the environment, interpreted by the World's effects, has the law of `reg` on the reassembled state, and keeps admissibility.

**C1.** The fixed steps join exactly: a World coin is the native coin (`coin_join`), the World's `.hash` is the native BLAKE2b oracle on the same cache (`hash_join`), and the World's Server and Beacon record steps are the native record steps on the reassembled state (`serverStep_merge`, `beaconStep_merge`); together with `Splits` this gives the per-step obligation (`worldStep_step`) and the invariant (`worldStep_keeps`), hence the main simulation `run_join`. The startup is the actual Server constructor: its coins are the World's counted coins (`coins_world`), and the constructed Server's initial environment state reassembles to the native game's initial state (`merge_initial`, `good_initial`). `join` is C1 at the full reassembled state, with the observed and analysis projections `join_observed` and `join_analysis`.

**C3.** `c3_shared_cache`: every BLAKE2b query of the common deployment experiment (adversary, record or registration) is a query on the World's shared cache; jointly with the output and the ledger, the native game's final CTX cache has the law of the World's `primitive.2`.

**C6.** `join_later` is C1 for the LQ-F later game (`PqxdhDeploymentFinishErasure.laterWith`, its post phase the run-phase handler on the post commands, `postNative`) against the later record world (`PqxdhRecordLiftLater.run`, split into the run and the post phase by `run_split`) with the environment's own reveal `envReveal`; the second adversary receives the same reveal on both sides (`reveal_merge`, `revealOf_strip`, `revealOf_fill`). `join_later_public` is its public form with the World's record view (`view_merge`).

These are equalities in law and of programs; no security claim is made here. The real-registration instances (`c1_real`, `c6_real`) and the per-command splits of the real handler are not in this module.
-/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete PqxdhRefinement

set_option autoImplicit false

namespace BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentJoin
open PqxdhServerAuthExperiment (Setup Codec Checks GameState)
open PqxdhServerAuthNative (NativeState NativeGame)
open PqxdhRecordLiftInterface (Slot Capability CapabilitySpec EnvEffects EnvQuery EnvSpec Environment EffectKind
  BeaconShell InactivePhase KernelRef)
open PqxdhDeploymentEnvironment (EnvState EnvStep strip Stripped stripPeer stripOwner)
open PqxdhDeploymentBackend (XState RegImpl handlerWith gameWith)
open LazyOracleDiscard (LawEq)

variable {KemSK : Type} {n : Nat}

/-! ### Reassembly -/

/-- The World's Server record coordinates (identity, peer map with kernels) in the registration Server state. -/
def fillServer (world : Option PqxdhRecordLiftWorld.Server)
    (server : PqxdhServerRegistrationPublication.State Unit Unit (List Pqxdh.Bytes)) :
    PqxdhServerRegistrationPublication.State Unit Unit (List Pqxdh.Bytes) :=
  match world with
  | none => server
  | some world => { server with server := world.records.server }

/-- The World's established phase (shell and kernel) in an established registration owner; any other pair leaves the owner. -/
def fillOwner (phase : Option PqxdhRecordLiftBeacon.Phase) (owner : PqxdhRegistrationSchedule.Owner KemSK) :
    PqxdhRegistrationSchedule.Owner KemSK :=
  match phase, owner.beacon.phase with
  | some (.established shell kernel), .established _ _ _ => { owner with beacon := { owner.beacon with
      identityKeyId := shell.identityKeyId
      phase := .established shell.control shell.associatedData kernel } }
  | _, _ => owner

/-- The World's record coordinates in a registration state: the Server's peer map with its kernels, the established owners' shells and kernels, and the shared CTX cache. -/
def fill (w : PqxdhRecordLiftWorld.State n) (state : PqxdhRegistrationSchedule.State KemSK) :
    PqxdhRegistrationSchedule.State KemSK :=
  { shared := (state.shared.1, { state.shared.2 with
      ctx := w.primitive.2
      server := fillServer w.server state.shared.2.server })
    owners := state.owners.mapIdx fun index owner => fillOwner w.owners[index]? owner }

/-- Reassembly (design-v2 section 5.9): the environment's registration state with the World's record coordinates filled in, the World's raw counters and produced frames, the World's seed table, and the environment's backend and LQ-F ghosts. -/
def merge {Bk : Type} (e : EnvState KemSK Bk) (w : PqxdhRecordLiftWorld.State n) : XState KemSK Bk n :=
  ⟨⟨fill w e.native, (w.server.map fun server => server.records.rawAttempts).getD 0, w.ownerRaw, w.produced⟩,
    e.backend, w.seeds.1, e.snap, e.log⟩

/-- Instrumentation forgotten (critique m6): every count of uniform, primitive and effect requests, the lazy-table counts and the used markers. -/
def forget (w : PqxdhRecordLiftWorld.State n) : PqxdhRecordLiftWorld.State n :=
  { w with
    primitive := (PqxdhRecordLiftWorld.Counts.empty, w.primitive.2)
    seeds := (w.seeds.1, (⟨0, 0⟩ : PqxdhRecordLiftLazyTable.Counts))
    used := fun _ _ => false }

/-- Reassembly does not read the instrumentation. -/
theorem merge_forget {Bk : Type} (e : EnvState KemSK Bk) (w : PqxdhRecordLiftWorld.State n) :
    merge e (forget w) = merge e w := rfl


/-- A World Beacon phase with its established kernel forgotten. -/
noncomputable def stripPhase : PqxdhRecordLiftBeacon.Phase → PqxdhRecordLiftBeacon.Phase
  | .established shell _ => .established shell PqxdhDeploymentHiddenSplit.placeholderKernel
  | phase => phase

/-- Admissibility (design-v2 section 5.9, per constructed Server, M2): the environment state is stripped and holds the constructed Server; the World's Server is initialized with the environment's sender and identity and has the environment's peers up to their kernels; the World's owners are the environment's owners, phase by phase, up to their kernels. -/
structure Good {Bk : Type} (created : PqxdhLiveServerConstruction.Created Unit) (e : EnvState KemSK Bk)
    (w : PqxdhRecordLiftWorld.State n) : Prop where
  stripped : Stripped e.native
  createdEq : e.created = created
  server : ∃ world, w.server = some world ∧ world.sender = e.native.shared.2.server.identityKeyId ∧
    world.records.server.identity = e.native.shared.2.server.server.identity ∧
    ∀ keyId, (world.records.server.peers keyId).map stripPeer = e.native.shared.2.server.server.peers keyId
  ownersLength : w.owners.length = e.native.owners.length
  owners : ∀ (index : Nat) (owner : PqxdhRegistrationSchedule.Owner KemSK), e.native.owners[index]? = some owner →
    (w.owners[index]?).map stripPhase = some (PqxdhRecordLiftBeacon.projectPhase owner.beacon)

/-! ### The joint state and the fixed steps -/

section World
variable {Bk : Type} {ι : Type} {baseSpec : OracleSpec ι} {Reader Response : Type}
  (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)

/-- The record world's interpretation of the open program on the joint state (environment state, World state): the native dispatch of `PqxdhRecordLiftInterface.native`, its world requests answered by `PqxdhRecordLiftWorld.handler`. -/
noncomputable def worldStep (env : Environment n (EnvState KemSK Bk)) :
    QueryImpl PqxdhDeploymentInterface.Spec (StateT (EnvState KemSK Bk × PqxdhRecordLiftWorld.State n) ProbComp) :=
  ((PqxdhRecordLiftWorld.handler setup codec route).mapStateTBase (PqxdhRecordLiftInterface.native env)).flattenStateT

/-- One joint step is one native dispatch step interpreted by the World. -/
theorem worldStep_run (env : Environment n (EnvState KemSK Bk)) (query : PqxdhDeploymentInterface.Spec.Domain)
    (e : EnvState KemSK Bk) (w : PqxdhRecordLiftWorld.State n) :
    (worldStep setup codec route env query).run (e, w) =
      (fun result => (result.1.1, (result.1.2, result.2))) <$>
        (simulateQ (PqxdhRecordLiftWorld.handler setup codec route)
          ((PqxdhRecordLiftInterface.native env query).run e)).run w := rfl

end World

/-- Counting a uniform computation changes nothing that reassembly reads. -/
theorem merge_sampled {Bk Y : Type} (e : EnvState KemSK Bk) (work : ProbComp Y) (w : PqxdhRecordLiftWorld.State n) :
    (fun result => (result.1, merge e result.2)) <$> (PqxdhRecordLiftWorld.sampled work).run w =
      (fun value => (value, merge e w)) <$> work := by
  have forgot := PqxdhRecordLiftWorld.countCoin_forget work w.primitive.1.uniform
  conv_rhs => rw [← forgot, Functor.map_map]
  simp only [PqxdhRecordLiftWorld.sampled, StateT.run, bind_pure_comp, Functor.map_map]
  rfl

/-- Charging an effect changes nothing that reassembly reads. -/
theorem merge_charge {Bk : Type} (e : EnvState KemSK Bk) (query : (EnvEffects n).Domain)
    (w : PqxdhRecordLiftWorld.State n) : merge e (PqxdhRecordLiftWorld.chargeEffect query w) = merge e w := rfl


section Fixed
variable {Bk : Type} {ι : Type} {baseSpec : OracleSpec ι} {Reader Response : Type}
  (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)

/-- A coin of the record world, its count forgotten, is the native game's coin on the reassembled state. -/
theorem coin_join (env : Environment n (EnvState KemSK Bk)) (reg : RegImpl KemSK Bk n) (coin : unifSpec.Domain)
    (e : EnvState KemSK Bk) (w : PqxdhRecordLiftWorld.State n) :
    Prod.map id (fun state => merge state.1 state.2) <$> (worldStep setup codec route env (.inl coin)).run (e, w) =
      (handlerWith setup codec route reg (.inl coin)).run (merge e w) := by
  rw [worldStep_run]
  simp only [PqxdhRecordLiftInterface.native, StateT.run_lift, PqxdhRecordLiftInterface.coinLift, simulateQ_bind,
    simulateQ_spec_query, simulateQ_pure, StateT.run_bind, StateT.run_pure, PqxdhRecordLiftWorld.handler,
    handlerWith, map_bind, map_pure]
  change ((PqxdhRecordLiftWorld.sampled (unifSpec.query coin : ProbComp _)).run
      (PqxdhRecordLiftWorld.chargeEffect (.inl coin) w) >>= fun result => pure (result.1, merge e result.2)) = _
  rw [bind_pure_comp, bind_pure_comp, merge_sampled, merge_charge]
  rfl

/-- A public BLAKE2b query of the record world, its counts forgotten, is the native game's BLAKE2b query on the reassembled state: both are the lazy CTX oracle on the World's shared cache. -/
theorem hash_join (env : Environment n (EnvState KemSK Bk)) (reg : RegImpl KemSK Bk n) (bytes : Pqxdh.Bytes)
    (e : EnvState KemSK Bk) (w : PqxdhRecordLiftWorld.State n) :
    Prod.map id (fun state => merge state.1 state.2) <$> (worldStep setup codec route env (.inr (.hash bytes))).run (e, w) =
      (handlerWith setup codec route reg (.inr (.hash bytes))).run (merge e w) := by
  rw [worldStep_run]
  simp only [PqxdhRecordLiftInterface.native, StateT.run_lift, PqxdhRecordLiftInterface.effectLift, simulateQ_bind,
    simulateQ_spec_query, simulateQ_pure, StateT.run_bind, StateT.run_pure, PqxdhRecordLiftWorld.handler,
    handlerWith, map_bind, map_pure]
  have forgot := congrArg (fun work => (fun result : CtxRomAuth.CtxDigest × CtxRomAuth.CtxRO.QueryCache =>
      (result.1, merge e { w with primitive := (w.primitive.1, result.2) })) <$> work)
    (PqxdhRecordLiftWorld.countCoin_forget ((CtxRomAuth.ctxRandomOracle ((), bytes)).run w.primitive.2)
      w.primitive.1.uniform)
  simp only [Functor.map_map] at forgot
  refine Eq.trans ?_ (Eq.trans forgot ?_)
  · simp only [PqxdhRecordLiftWorld.effects, PqxdhRecordLiftWorld.capability, PqxdhRecordLiftWorld.sampled,
      StateT.run, bind_pure_comp, Functor.map_map]
    rfl
  · simp only [PqxdhDeploymentBackend.onBase, LazyOracleDiscard.StateLens.lift, PqxdhDeploymentNative.onNative,
      PqxdhRegistrationSchedule.onShared, PqxdhServerAuthNative.nativeHash, StateT.run, Functor.map_map]
    rfl

/-- The World's instrumented primitives, their counts forgotten, are the native primitives on the World's shared cache, for every record program. -/
theorem world_primitives_run {Result : Type} (work : OracleComp RawCtxMixedOwner.NativeSpec Result)
    (primitive : PqxdhRecordLiftWorld.Primitive) :
    Prod.map id (fun state : PqxdhRecordLiftWorld.Primitive => (((), state.2) : RawCtxSharedPrimitive.SharedState Unit)) <$>
        (simulateQ (PqxdhRecordLiftWorld.primitives setup codec) work).run primitive =
      (simulateQ (PqxdhDeploymentNative.primitives setup codec) work).run ((), primitive.2) := by
  refine OracleComp.map_run_simulateQ_eq_of_query_map_eq _ _ _ (fun query state => ?_) work primitive
  have forgot := congrArg (fun work => Prod.map id (fun cache : CtxRomAuth.CtxRO.QueryCache =>
      (((), cache) : RawCtxSharedPrimitive.SharedState Unit)) <$> work)
    (PqxdhRecordLiftWorld.primitives_forget setup codec query state)
  simp only [Functor.map_map] at forgot
  refine forgot.trans ?_
  conv_rhs => rw [← id_map ((PqxdhDeploymentNative.primitives setup codec query).run ((), state.2))]
  congr 1

/-- The native Server record step at a state whose Server view and sender are given. -/
theorem nativeServerStep_run (query : RawCtxServerMixed.SourceSpec.Domain) (state : PqxdhDeploymentNative.State KemSK)
    (records : RawCtxServerRouting.State Unit Unit) (sender : Std.U64)
    (view : PqxdhDeploymentNative.serverView state = records)
    (senderEq : PqxdhDeploymentNative.senderId state = fun _ => sender) :
    (PqxdhDeploymentNative.serverStep setup codec route query).run state =
      (fun result => (result.1.1.1, PqxdhDeploymentNative.produce (PqxdhDeploymentNative.serverTag query) result.1.2
        (PqxdhDeploymentNative.withServer { state with native := { state.native with shared :=
          (state.native.shared.1, { state.native.shared.2 with ctx := result.2.2 }) } } result.1.1.2))) <$>
        (simulateQ (PqxdhDeploymentNative.primitives setup codec) (PqxdhDeploymentNative.logged
          ((RawCtxServerMixed.serverImpl (fun _ => sender) route codec.frameRead query).run records))).run
            ((), state.native.shared.2.ctx) := by
  change (do
    let result ← (PqxdhDeploymentNative.record setup codec (PqxdhDeploymentNative.logged
      ((RawCtxServerMixed.serverImpl (PqxdhDeploymentNative.senderId state) route codec.frameRead query).run
        (PqxdhDeploymentNative.serverView state)))).run state.native
    pure (result.1.1.1, PqxdhDeploymentNative.produce (PqxdhDeploymentNative.serverTag query) result.1.2
      (PqxdhDeploymentNative.withServer { state with native := result.2 } result.1.1.2))) = _
  rw [view, senderEq]
  simp only [PqxdhDeploymentNative.record, PqxdhRegistrationSchedule.onShared, PqxdhServerAuthNative.nativeCtx,
    StateT.run, bind_pure_comp, Functor.map_map]

/-- A Server record command of the record world, its counts forgotten, is the native Server record step on the reassembled state, when the World's Server has the environment's sender. -/
theorem serverStep_merge {Bk : Type} (query : RawCtxServerMixed.SourceSpec.Domain) (e : EnvState KemSK Bk)
    (w : PqxdhRecordLiftWorld.State n) (world : PqxdhRecordLiftWorld.Server) (found : w.server = some world)
    (sender : world.sender = e.native.shared.2.server.identityKeyId) :
    (fun result => (result.1, merge e result.2)) <$> (PqxdhRecordLiftWorld.serverStep setup codec route query).run w =
      (PqxdhDeploymentBackend.onBase (PqxdhDeploymentNative.serverStep setup codec route query)).run (merge e w) := by
  obtain ⟨worldServer, owners, ownerRaw, produced, primitive, seeds, used⟩ := w
  simp only at found
  subst found
  let W : PqxdhRecordLiftWorld.State n := ⟨some world, owners, ownerRaw, produced, primitive, seeds, used⟩
  have primitives := world_primitives_run setup codec (PqxdhDeploymentNative.logged
    ((RawCtxServerMixed.serverImpl (fun _ => world.sender) route codec.frameRead query).run world.records)) primitive
  have view : PqxdhDeploymentNative.serverView (merge e W).base = world.records := by
    simp only [W, PqxdhDeploymentNative.serverView, merge, fill, fillServer, Option.map_some, Option.getD_some]
  have senderEq : PqxdhDeploymentNative.senderId (merge e W).base = fun _ => world.sender := by
    funext metadata
    simp only [W, PqxdhDeploymentNative.senderId, merge, fill, fillServer, sender]
  change _ = (fun result => (result.1, { merge e W with base := result.2 })) <$>
    (PqxdhDeploymentNative.serverStep setup codec route query).run (merge e W).base
  rw [nativeServerStep_run setup codec route query _ world.records world.sender view senderEq, Functor.map_map,
    show (merge e _).base.native.shared.2.ctx = primitive.2 from rfl, ← primitives, Functor.map_map]
  simp only [PqxdhRecordLiftWorld.serverStep, StateT.run, bind_pure_comp, Functor.map_map]
  rfl

/-- A World phase matching an owner up to its kernel is either an inactive phase, which leaves the owner when filled in, or the owner's established shell with some kernel. -/
theorem phase_cases (phase : PqxdhRecordLiftBeacon.Phase) (owner : PqxdhRegistrationSchedule.Owner KemSK)
    (matched : stripPhase phase = PqxdhRecordLiftBeacon.projectPhase owner.beacon) :
    (fillOwner (some phase) owner = owner ∧ ∃ tag, phase = .inactive tag ∧
        ¬ RawCtxBeaconLifecycle.Established owner.beacon.phase) ∨
      ∃ control associatedData stale kernel, owner.beacon.phase = .established control associatedData stale ∧
        phase = .established ⟨owner.beacon.identityKeyId, control, associatedData⟩ kernel := by
  cases phase with
  | inactive tag =>
      refine Or.inl ⟨rfl, tag, rfl, ?_⟩
      cases hphase : owner.beacon.phase <;>
        simp_all [stripPhase, PqxdhRecordLiftBeacon.projectPhase, RawCtxBeaconLifecycle.Established]
  | established shell kernel =>
      refine Or.inr ?_
      cases hphase : owner.beacon.phase <;>
        simp only [stripPhase, PqxdhRecordLiftBeacon.projectPhase, hphase, reduceCtorEq] at matched
      case established control associatedData stale =>
        simp only [PqxdhRecordLiftBeacon.Phase.established.injEq] at matched
        exact ⟨control, associatedData, stale, kernel, rfl, by rw [matched.1]⟩

/-- Filling the owners after one World phase changes is filling them and then setting that owner. -/
theorem fill_owners_set (owners : List (PqxdhRegistrationSchedule.Owner KemSK)) (phases : List PqxdhRecordLiftBeacon.Phase)
    (index : Nat) (phase : PqxdhRecordLiftBeacon.Phase) (owner : PqxdhRegistrationSchedule.Owner KemSK)
    (found : owners[index]? = some owner) (lengths : phases.length = owners.length) :
    owners.mapIdx (fun i o => fillOwner (phases.set index phase)[i]? o) =
      (owners.mapIdx (fun i o => fillOwner phases[i]? o)).set index (fillOwner (some phase) owner) := by
  obtain ⟨below, _⟩ := List.getElem?_eq_some_iff.mp found
  apply List.ext_getElem?
  intro i
  by_cases same : index = i
  · subst same
    have inner : (phases.set index phase)[index]? = some phase := List.getElem?_set_self (by omega)
    have outer : ((owners.mapIdx (fun i o => fillOwner phases[i]? o)).set index (fillOwner (some phase) owner))[index]? =
        some (fillOwner (some phase) owner) := List.getElem?_set_self (by simpa only [List.length_mapIdx] using below)
    rw [outer, List.getElem?_mapIdx, found, inner]
    rfl
  · rw [List.getElem?_mapIdx, List.getElem?_set_ne same, List.getElem?_set_ne same, List.getElem?_mapIdx]

/-- A Beacon record command of the record world, its counts forgotten, is the native Beacon record step on the reassembled state, when the World's owners are the environment's owners up to their kernels. -/
theorem beaconStep_merge {Bk : Type} (index : Nat) (query : RawCtxMixedOwner.SourceSpec.Domain) (e : EnvState KemSK Bk)
    (w : PqxdhRecordLiftWorld.State n) (lengths : w.owners.length = e.native.owners.length)
    (owners : ∀ (i : Nat) (o : PqxdhRegistrationSchedule.Owner KemSK), e.native.owners[i]? = some o →
      (w.owners[i]?).map stripPhase = some (PqxdhRecordLiftBeacon.projectPhase o.beacon)) :
    (fun result => (result.1, merge e result.2)) <$> (PqxdhRecordLiftWorld.beaconStep setup codec index query).run w =
      (PqxdhDeploymentBackend.onBase (PqxdhDeploymentNative.beaconStep setup codec index query)).run (merge e w) := by
  change _ = (fun result => (result.1, { merge e w with base := result.2 })) <$>
    (PqxdhDeploymentNative.beaconStep setup codec index query).run (merge e w).base
  cases hfound : e.native.owners[index]? with
  | none =>
      have absentW : w.owners[index]? = none := by
        rw [List.getElem?_eq_none_iff] at hfound ⊢
        omega
      have absentM : (merge e w).base.native.owners[index]? = none := by
        simp only [merge, fill, List.getElem?_mapIdx, hfound, Option.map_none]
      simp only [PqxdhRecordLiftWorld.beaconStep, PqxdhDeploymentNative.beaconStep, StateT.run, absentW, absentM,
        map_pure]
  | some owner =>
      obtain ⟨phase, foundW, matched⟩ : ∃ phase, w.owners[index]? = some phase ∧
          stripPhase phase = PqxdhRecordLiftBeacon.projectPhase owner.beacon := by
        have h := owners index owner hfound
        cases hw : w.owners[index]? with
        | none => simp only [hw, Option.map_none, reduceCtorEq] at h
        | some phase => exact ⟨phase, rfl, by simpa only [hw, Option.map_some, Option.some.injEq] using h⟩
      have foundM : (merge e w).base.native.owners[index]? = some (fillOwner (some phase) owner) := by
        simp only [merge, fill, List.getElem?_mapIdx, hfound, foundW, Option.map_some]
      obtain ⟨belowW, elementW⟩ := List.getElem?_eq_some_iff.mp foundW
      obtain ⟨belowM, elementM⟩ := List.getElem?_eq_some_iff.mp foundM
      rcases phase_cases phase owner matched with ⟨filled, tag, rfl, notEst⟩ | ⟨control, associatedData, stale, kernel,
        ownerPhase, rfl⟩
      · have rejectW : (PqxdhRecordLiftBeacon.handler codec.frameRead query).run ⟨.inactive tag, w.ownerRaw index⟩ =
            pure (PqxdhRecordLiftBeacon.rejected query ⟨.inactive tag, w.ownerRaw index⟩) := rfl
        rw [filled] at foundM elementM
        have rejectN := RawCtxBeaconLifecycle.inactive codec.frameRead query ⟨owner.beacon, w.ownerRaw index⟩ notEst
        change (fun result => (result.1, merge e result.2)) <$> PqxdhRecordLiftWorld.beaconStep setup codec index query w =
          (fun result => (result.1, { merge e w with base := result.2 })) <$>
            PqxdhDeploymentNative.beaconStep setup codec index query (merge e w).base
        unfold PqxdhRecordLiftWorld.beaconStep PqxdhDeploymentNative.beaconStep
        simp only [foundW, foundM]
        rw [show (merge e w).base.ownerRaw index = w.ownerRaw index from rfl, rejectW, rejectN]
        simp only [PqxdhDeploymentNative.logged_pure, simulateQ_pure, StateT.run_pure, pure_bind, map_pure,
          PqxdhDeploymentNative.record, PqxdhRegistrationSchedule.onShared_run, PqxdhServerAuthNative.nativeCtx]
        have keepW : w.owners.set index (.inactive tag) = w.owners := by
          rw [← elementW, List.set_getElem_self]
        have keepM : (merge e w).base.native.owners.set index owner = (merge e w).base.native.owners := by
          rw [← elementM, List.set_getElem_self]
        cases query <;> simp only [PqxdhRecordLiftBeacon.rejected, RawCtxBeaconLifecycle.rejected, keepW, keepM] <;> rfl
      · have handlerW : (PqxdhRecordLiftBeacon.handler codec.frameRead query).run
            ⟨.established ⟨owner.beacon.identityKeyId, control, associatedData⟩ kernel, w.ownerRaw index⟩ =
            (fun result => (result.1, (⟨.established ⟨owner.beacon.identityKeyId, control, associatedData⟩
              result.2.owner.kernel, result.2.rawAttempts⟩ : PqxdhRecordLiftBeacon.State))) <$>
              (RawCtxMixedOwner.ownerImpl owner.beacon.identityKeyId codec.frameRead query).run
                ⟨⟨kernel, control.server_binding.identity_key_id, absBytes associatedData, ()⟩, w.ownerRaw index⟩ := by
          rw [map_eq_bind_pure_comp]
          rfl
        have implN : (RawCtxBeaconLifecycle.beaconImpl codec.frameRead query).run
            ⟨(fillOwner (some (.established ⟨owner.beacon.identityKeyId, control, associatedData⟩ kernel)) owner).beacon,
              w.ownerRaw index⟩ =
            (fun result => (result.1, RawCtxBeaconLifecycle.reinstall
              ⟨(fillOwner (some (.established ⟨owner.beacon.identityKeyId, control, associatedData⟩ kernel)) owner).beacon,
                w.ownerRaw index⟩ control associatedData result.2)) <$>
              (RawCtxMixedOwner.ownerImpl owner.beacon.identityKeyId codec.frameRead query).run
                ⟨⟨kernel, control.server_binding.identity_key_id, absBytes associatedData, ()⟩, w.ownerRaw index⟩ := by
          rw [map_eq_bind_pure_comp]
          simp only [fillOwner, ownerPhase]
          rfl
        have primitives := world_primitives_run setup codec (PqxdhDeploymentNative.logged
          ((RawCtxMixedOwner.ownerImpl owner.beacon.identityKeyId codec.frameRead query).run
            ⟨⟨kernel, control.server_binding.identity_key_id, absBytes associatedData, ()⟩, w.ownerRaw index⟩))
          w.primitive
        change (fun result => (result.1, merge e result.2)) <$> PqxdhRecordLiftWorld.beaconStep setup codec index query w =
          (fun result => (result.1, { merge e w with base := result.2 })) <$>
            PqxdhDeploymentNative.beaconStep setup codec index query (merge e w).base
        unfold PqxdhRecordLiftWorld.beaconStep PqxdhDeploymentNative.beaconStep
        simp only [foundW, foundM]
        rw [show (merge e w).base.ownerRaw index = w.ownerRaw index from rfl, handlerW, implN]
        simp only [PqxdhDeploymentNative.logged_map, simulateQ_map, StateT.run_map, PqxdhDeploymentNative.record,
          PqxdhRegistrationSchedule.onShared_run, PqxdhServerAuthNative.nativeCtx, bind_pure_comp,
          Functor.map_map]
        rw [show (merge e w).base.native.shared.2.ctx = w.primitive.2 from rfl, ← primitives, Functor.map_map]
        congr 1
        funext result
        obtain ⟨⟨⟨reply, ownerState⟩, frames⟩, primitive⟩ := result
        refine Prod.ext rfl ?_
        simp only [Prod.map, id, merge, fill, PqxdhRecordLiftWorld.produce]
        rw [fill_owners_set e.native.owners w.owners index _ owner hfound lengths]
        simp only [fillOwner, ownerPhase]
        rfl

end Fixed


/-! ### The admissibility invariant along the fixed steps -/

section Keeps
variable {Bk : Type} {ι : Type} {baseSpec : OracleSpec ι} {Reader Response : Type}
  (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)

/-- A logged record program interpreted by any stateful primitive handler only returns results of the program itself. -/
theorem logged_support {σ Result : Type} (impl : QueryImpl RawCtxMixedOwner.NativeSpec (StateT σ ProbComp))
    (work : OracleComp RawCtxMixedOwner.NativeSpec Result) (state : σ)
    (result : (Result × List PqxdhDeploymentNative.Frame) × σ)
    (supported : result ∈ support ((simulateQ impl (PqxdhDeploymentNative.logged work)).run state)) :
    result.1.1 ∈ support work := by
  have inLogged : result.1 ∈ support (PqxdhDeploymentNative.logged work) := by
    apply OracleComp.support_simulateQ_run'_subset impl _ state
    rw [StateT.run'_eq, support_map]
    exact ⟨result, supported, rfl⟩
  apply OracleComp.support_simulateQ_run'_subset PqxdhDeploymentNative.frameLog _ []
  rw [StateT.run'_eq, support_map]
  exact ⟨result.1, inLogged, rfl⟩

/-- Updating one peer's kernel keeps every peer's identity and metadata. -/
theorem putPeer_stripped (server : RawCtxServerRouting.Server Unit Unit) (keyId : Std.U64)
    (peer : RawCtxServerRouting.Peer Unit) (kernel : ConcreteRatchetKernel) (found : server.peers keyId = some peer) :
    (RawCtxServerRouting.putPeer server keyId peer kernel).identity = server.identity ∧
      ∀ other, ((RawCtxServerRouting.putPeer server keyId peer kernel).peers other).map stripPeer =
        (server.peers other).map stripPeer := by
  refine ⟨rfl, fun other => ?_⟩
  by_cases same : other = keyId
  · subst same
    simp only [RawCtxServerRouting.putPeer, Function.update_self, found, Option.map_some]
    rfl
  · simp only [RawCtxServerRouting.putPeer, Function.update_of_ne same]

/-- A Server record command keeps the Server identity and every peer's identity and metadata; only kernels and the raw counter change. -/
theorem serverImpl_stripped (senderId : Unit → Std.U64) (query : RawCtxServerMixed.SourceSpec.Domain)
    (state : RawCtxServerRouting.State Unit Unit)
    (result : RawCtxServerMixed.SourceSpec.Range query × RawCtxServerRouting.State Unit Unit)
    (supported : result ∈ support ((RawCtxServerMixed.serverImpl senderId route codec.frameRead query).run state)) :
    result.2.server.identity = state.server.identity ∧
      ∀ keyId, (result.2.server.peers keyId).map stripPeer = (state.server.peers keyId).map stripPeer := by
  rcases query with ⟨plaintext, keyId⟩ | raw
  · change result ∈ support (simulateQ RawCtxMixedOwner.sendLift
      (RawCtxServerSend.sendServer senderId plaintext keyId state)) at supported
    have sourced := PqxdhDeploymentEnvironment.support_simulateQ_subset _ _ supported
    unfold RawCtxServerSend.sendServer at sourced
    split at sourced
    · simp only [support_pure, Set.mem_singleton_iff] at sourced
      subst sourced
      exact ⟨rfl, fun _ => rfl⟩
    · split at sourced
      · simp only [support_pure, Set.mem_singleton_iff] at sourced
        subst sourced
        exact ⟨rfl, fun _ => rfl⟩
      · rename_i peer found
        simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at sourced
        obtain ⟨_, _, rfl⟩ := sourced
        exact putPeer_stripped _ _ _ _ found
  · change result ∈ support (RawCtxServerMixed.rawServer route codec.frameRead raw state) at supported
    unfold RawCtxServerMixed.rawServer at supported
    split at supported
    · simp only [support_pure, Set.mem_singleton_iff] at supported
      subst supported
      exact ⟨rfl, fun _ => rfl⟩
    · split at supported
      · simp only [support_pure, Set.mem_singleton_iff] at supported
        subst supported
        exact ⟨rfl, fun _ => rfl⟩
      · split at supported
        · simp only [support_pure, Set.mem_singleton_iff] at supported
          subst supported
          exact ⟨rfl, fun _ => rfl⟩
        · rename_i peer found
          simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at supported
          obtain ⟨_, _, rfl⟩ := supported
          exact putPeer_stripped _ _ _ _ found

/-- A Beacon record command keeps the phase up to its kernel. -/
theorem beaconHandler_stripped (query : RawCtxMixedOwner.SourceSpec.Domain) (state : PqxdhRecordLiftBeacon.State)
    (result : RawCtxMixedOwner.SourceSpec.Range query × PqxdhRecordLiftBeacon.State)
    (supported : result ∈ support ((PqxdhRecordLiftBeacon.handler codec.frameRead query).run state)) :
    stripPhase result.2.phase = stripPhase state.phase := by
  change result ∈ support (PqxdhRecordLiftBeacon.handler codec.frameRead query state) at supported
  unfold PqxdhRecordLiftBeacon.handler at supported
  split at supported
  · simp only [support_pure, Set.mem_singleton_iff] at supported
    subst supported
    cases query <;> rfl
  · rename_i shell kernel phase
    simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at supported
    obtain ⟨_, _, rfl⟩ := supported
    simp only [stripPhase, phase]

/-- Admissibility reads the World only through its Server and its owners. -/
theorem good_frame (created : PqxdhLiveServerConstruction.Created Unit) (e : EnvState KemSK Bk)
    (w w' : PqxdhRecordLiftWorld.State n) (good : Good created e w) (server : w'.server = w.server)
    (owners : w'.owners = w.owners) : Good created e w' := by
  obtain ⟨stripped, createdEq, serverGood, ownersLength, ownersGood⟩ := good
  exact ⟨stripped, createdEq, server ▸ serverGood, owners ▸ ownersLength, owners ▸ ownersGood⟩

/-- A coin or a public BLAKE2b query keeps the World's Server and owners. -/
theorem effects_frame (query : (EnvEffects n).Domain)
    (fixed : (∃ coin, query = .inl coin) ∨ ∃ bytes, query = .inr (.hash bytes)) (w : PqxdhRecordLiftWorld.State n) :
    ∀ result ∈ support ((PqxdhRecordLiftWorld.effects query).run w), result.2.server = w.server ∧
      result.2.owners = w.owners := by
  intro result supported
  rcases fixed with ⟨coin, rfl⟩ | ⟨bytes, rfl⟩
  · change result ∈ support ((PqxdhRecordLiftWorld.sampled (unifSpec.query coin : ProbComp _)).run
      (PqxdhRecordLiftWorld.chargeEffect (.inl coin) w)) at supported
    simp only [PqxdhRecordLiftWorld.sampled, StateT.run, mem_support_bind_iff, support_pure,
      Set.mem_singleton_iff] at supported
    obtain ⟨_, _, rfl⟩ := supported
    exact ⟨rfl, rfl⟩
  · change result ∈ support ((PqxdhRecordLiftWorld.capability (.hash bytes)).run
      (PqxdhRecordLiftWorld.chargeEffect (.inr (.hash bytes)) w)) at supported
    simp only [PqxdhRecordLiftWorld.capability, PqxdhRecordLiftWorld.sampled, StateT.run, mem_support_bind_iff,
      support_pure, Set.mem_singleton_iff] at supported
    obtain ⟨_, ⟨_, _, rfl⟩, rfl⟩ := supported
    exact ⟨rfl, rfl⟩

/-- A Server record command keeps admissibility. -/
theorem serverStep_good (created : PqxdhLiveServerConstruction.Created Unit) (query : RawCtxServerMixed.SourceSpec.Domain)
    (e : EnvState KemSK Bk) (w : PqxdhRecordLiftWorld.State n) (good : Good created e w) :
    ∀ result ∈ support ((PqxdhRecordLiftWorld.serverStep setup codec route query).run w), Good created e result.2 := by
  intro result supported
  obtain ⟨world, found, sender, identity, peers⟩ := good.server
  change result ∈ support (PqxdhRecordLiftWorld.serverStep setup codec route query w) at supported
  unfold PqxdhRecordLiftWorld.serverStep at supported
  simp only [found, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at supported
  obtain ⟨inner, member, rfl⟩ := supported
  have kept := serverImpl_stripped codec route (fun _ => world.sender) query world.records inner.1.1
    (logged_support _ _ _ _ member)
  refine ⟨good.stripped, good.createdEq, ⟨{ world with records := inner.1.1.2 }, rfl, sender, ?_, ?_⟩,
    good.ownersLength, good.owners⟩
  · rw [← identity]
    exact kept.1
  · intro keyId
    rw [← peers keyId]
    exact kept.2 keyId

/-- A Beacon record command keeps admissibility. -/
theorem beaconStep_good (created : PqxdhLiveServerConstruction.Created Unit) (index : Nat)
    (query : RawCtxMixedOwner.SourceSpec.Domain) (e : EnvState KemSK Bk) (w : PqxdhRecordLiftWorld.State n)
    (good : Good created e w) :
    ∀ result ∈ support ((PqxdhRecordLiftWorld.beaconStep setup codec index query).run w), Good created e result.2 := by
  intro result supported
  change result ∈ support (PqxdhRecordLiftWorld.beaconStep setup codec index query w) at supported
  unfold PqxdhRecordLiftWorld.beaconStep at supported
  split at supported
  · simp only [support_pure, Set.mem_singleton_iff] at supported
    subst supported
    exact good
  · rename_i phase foundW
    simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at supported
    obtain ⟨inner, member, rfl⟩ := supported
    have kept := beaconHandler_stripped codec query ⟨phase, w.ownerRaw index⟩ inner.1.1
      (logged_support _ _ _ _ member)
    obtain ⟨belowW, _⟩ := List.getElem?_eq_some_iff.mp foundW
    refine ⟨good.stripped, good.createdEq, good.server, ?_, fun i owner found => ?_⟩
    · simp only [PqxdhRecordLiftWorld.produce, List.length_set, good.ownersLength]
    · have before := good.owners i owner found
      simp only [PqxdhRecordLiftWorld.produce]
      by_cases same : index = i
      · subst same
        rw [List.getElem?_set_self belowW, Option.map_some, kept]
        rw [foundW, Option.map_some] at before
        exact before
      · rw [List.getElem?_set_ne same]
        exact before

end Keeps


/-! ### C1: the generic join -/

section Join
variable {Bk : Type} {ι : Type} {baseSpec : OracleSpec ι} {Reader Response : Type}
  (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)

/-- The registration handler `reg` splits into the environment step `step` and the record world (design-v2 section 5.9): from every admissible joint state, each registration command of the environment, interpreted by the World's effects, has the law of the registration handler on the reassembled state, and it keeps admissibility. -/
def Splits (created : PqxdhLiveServerConstruction.Created Unit) (reg : RegImpl KemSK Bk n) (step : EnvStep KemSK Bk n) :
    Prop :=
  ∀ (query : EnvQuery) (e : EnvState KemSK Bk) (w : PqxdhRecordLiftWorld.State n), Good created e w →
    LawEq ((fun result => (result.1.1, merge result.1.2 result.2)) <$>
        (simulateQ PqxdhRecordLiftWorld.effects ((step query).run e)).run w) ((reg query).run (merge e w)) ∧
      ∀ result ∈ support ((simulateQ PqxdhRecordLiftWorld.effects ((step query).run e)).run w),
        Good created result.1.2 result.2

/-- A registration command of the open program is the environment step interpreted by the World's effects. -/
theorem worldStep_reg (env : Environment n (EnvState KemSK Bk)) (query : EnvQuery) (e : EnvState KemSK Bk)
    (w : PqxdhRecordLiftWorld.State n) :
    (worldStep setup codec route env (.inr query.val)).run (e, w) =
      (fun result => (result.1.1, (result.1.2, result.2))) <$>
        (simulateQ PqxdhRecordLiftWorld.effects ((env.step query).run e)).run w := by
  rw [worldStep_run]
  rcases query with ⟨command, allowed⟩
  have composed : (PqxdhRecordLiftWorld.handler setup codec route (n := n)) ∘ₛ PqxdhRecordLiftInterface.effectLift =
      PqxdhRecordLiftWorld.effects := by
    funext request
    simp only [QueryImpl.apply_compose, PqxdhRecordLiftInterface.effectLift, simulateQ_spec_query]
    rfl
  cases command
  all_goals first
    | exact absurd allowed id
    | (simp only [PqxdhRecordLiftInterface.native, PqxdhRecordLiftInterface.environmentStep, StateT.run]
       rw [← QueryImpl.simulateQ_compose, composed]
       rfl)

/-- A lifted World request on the joint state: the request answered by the World, the environment state untouched. -/
theorem lift_run (request : (PqxdhRecordLiftInterface.WorldSpec n).Domain) (e : EnvState KemSK Bk)
    (w : PqxdhRecordLiftWorld.State n) :
    (simulateQ (PqxdhRecordLiftWorld.handler setup codec route)
      ((StateT.lift (liftM ((PqxdhRecordLiftInterface.WorldSpec n).query request)) :
        StateT (EnvState KemSK Bk) (OracleComp (PqxdhRecordLiftInterface.WorldSpec n)) _).run e)).run w =
      (fun result => ((result.1, e), result.2)) <$> (PqxdhRecordLiftWorld.handler setup codec route request).run w := by
  rw [StateT.run_lift, simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
  simp only [simulateQ_pure, StateT.run_pure, bind_pure_comp]

/-- A coin of the open program is one World coin effect. -/
theorem worldStep_coin (env : Environment n (EnvState KemSK Bk)) (coin : unifSpec.Domain) (e : EnvState KemSK Bk)
    (w : PqxdhRecordLiftWorld.State n) :
    (worldStep setup codec route env (.inl coin)).run (e, w) =
      (fun result => (result.1, (e, result.2))) <$> (PqxdhRecordLiftWorld.effects (n := n) (.inl coin)).run w := by
  rw [worldStep_run]
  erw [lift_run setup codec route (.inr (.inl (.inl coin))) e w, Functor.map_map]

/-- A public BLAKE2b query of the open program is one World `.hash` effect. -/
theorem worldStep_hash (env : Environment n (EnvState KemSK Bk)) (bytes : Pqxdh.Bytes) (e : EnvState KemSK Bk)
    (w : PqxdhRecordLiftWorld.State n) :
    (worldStep setup codec route env (.inr (.hash bytes))).run (e, w) =
      (fun result => (result.1, (e, result.2))) <$> (PqxdhRecordLiftWorld.effects (n := n) (.inr (.hash bytes))).run w := by
  rw [worldStep_run]
  erw [lift_run setup codec route (.inr (.inl (.inr (.hash bytes)))) e w, Functor.map_map]
  rfl

/-- A Server send of the open program is one World Server record step. -/
theorem worldStep_serverSend (env : Environment n (EnvState KemSK Bk)) (keyId : Std.U64) (plaintext : Pqxdh.Bytes) (e : EnvState KemSK Bk)
    (w : PqxdhRecordLiftWorld.State n) :
    (worldStep setup codec route env (.inr (.serverSend keyId plaintext))).run (e, w) =
      (fun result => (result.1, (e, result.2))) <$> (PqxdhRecordLiftWorld.serverStep (n := n) setup codec route (.inl (plaintext, keyId))).run w := by
  rw [worldStep_run]
  erw [lift_run setup codec route (.inr (.inr (.inl (.inl (plaintext, keyId))))) e w, Functor.map_map]
  rfl

/-- A Server raw receive of the open program is one World Server record step. -/
theorem worldStep_serverRaw (env : Environment n (EnvState KemSK Bk)) (raw : Pqxdh.Bytes) (e : EnvState KemSK Bk)
    (w : PqxdhRecordLiftWorld.State n) :
    (worldStep setup codec route env (.inr (.serverRaw raw))).run (e, w) =
      (fun result => (result.1, (e, result.2))) <$> (PqxdhRecordLiftWorld.serverStep (n := n) setup codec route (.inr raw)).run w := by
  rw [worldStep_run]
  erw [lift_run setup codec route (.inr (.inr (.inl (.inr raw)))) e w, Functor.map_map]
  rfl

/-- A Beacon send of the open program is one World Beacon record step. -/
theorem worldStep_beaconSend (env : Environment n (EnvState KemSK Bk)) (owner : Nat) (plaintext : Pqxdh.Bytes) (e : EnvState KemSK Bk)
    (w : PqxdhRecordLiftWorld.State n) :
    (worldStep setup codec route env (.inr (.beaconSend owner plaintext))).run (e, w) =
      (fun result => (result.1, (e, result.2))) <$> (PqxdhRecordLiftWorld.beaconStep (n := n) setup codec owner (.inl plaintext)).run w := by
  rw [worldStep_run]
  erw [lift_run setup codec route (.inr (.inr (.inr (owner, .inl plaintext)))) e w, Functor.map_map]
  rfl

/-- A Beacon raw receive of the open program is one World Beacon record step. -/
theorem worldStep_beaconRaw (env : Environment n (EnvState KemSK Bk)) (owner : Nat) (raw : Pqxdh.Bytes) (e : EnvState KemSK Bk)
    (w : PqxdhRecordLiftWorld.State n) :
    (worldStep setup codec route env (.inr (.beaconRaw owner raw))).run (e, w) =
      (fun result => (result.1, (e, result.2))) <$> (PqxdhRecordLiftWorld.beaconStep (n := n) setup codec owner (.inr raw)).run w := by
  rw [worldStep_run]
  erw [lift_run setup codec route (.inr (.inr (.inr (owner, .inr raw)))) e w, Functor.map_map]
  rfl

/-- One joint step, reassembled, has the law of the native game's step on the reassembled state, from every admissible state (the per-query obligation of C1). -/
theorem worldStep_step (env : Environment n (EnvState KemSK Bk)) (reg : RegImpl KemSK Bk n)
    (created : PqxdhLiveServerConstruction.Created Unit) (splits : Splits created reg env.step)
    (query : PqxdhDeploymentInterface.Spec.Domain) (e : EnvState KemSK Bk) (w : PqxdhRecordLiftWorld.State n)
    (good : Good created e w) :
    LawEq (Prod.map id (fun state => merge state.1 state.2) <$> (worldStep setup codec route env query).run (e, w))
      ((handlerWith setup codec route reg query).run (merge e w)) := by
  obtain ⟨world, found, sender, _, _⟩ := good.server
  rcases query with coin | command
  · exact LawEq.of_eq (coin_join setup codec route env reg coin e w)
  · cases command with
    | hash bytes => exact LawEq.of_eq (hash_join setup codec route env reg bytes e w)
    | serverSend keyId plaintext =>
        rw [worldStep_serverSend setup codec route env keyId plaintext e w, Functor.map_map]
        exact LawEq.of_eq (serverStep_merge setup codec route (.inl (plaintext, keyId)) e w world found sender)
    | serverRaw raw =>
        rw [worldStep_serverRaw setup codec route env raw e w, Functor.map_map]
        exact LawEq.of_eq (serverStep_merge setup codec route (.inr raw) e w world found sender)
    | beaconSend owner plaintext =>
        rw [worldStep_beaconSend setup codec route env owner plaintext e w, Functor.map_map]
        exact LawEq.of_eq (beaconStep_merge setup codec owner (.inl plaintext) e w good.ownersLength good.owners)
    | beaconRaw owner raw =>
        rw [worldStep_beaconRaw setup codec route env owner raw e w, Functor.map_map]
        exact LawEq.of_eq (beaconStep_merge setup codec owner (.inr raw) e w good.ownersLength good.owners)
    | create pin keyId =>
        rw [worldStep_reg setup codec route env ⟨.create pin keyId, trivial⟩ e w, Functor.map_map]
        exact (splits ⟨.create pin keyId, trivial⟩ e w good).1
    | bundle owner =>
        rw [worldStep_reg setup codec route env ⟨.bundle owner, trivial⟩ e w, Functor.map_map]
        exact (splits ⟨.bundle owner, trivial⟩ e w good).1
    | accept raw =>
        rw [worldStep_reg setup codec route env ⟨.accept raw, trivial⟩ e w, Functor.map_map]
        exact (splits ⟨.accept raw, trivial⟩ e w good).1
    | build session payload =>
        rw [worldStep_reg setup codec route env ⟨.build session payload, trivial⟩ e w, Functor.map_map]
        exact (splits ⟨.build session payload, trivial⟩ e w good).1
    | finish owner raw =>
        rw [worldStep_reg setup codec route env ⟨.finish owner raw, trivial⟩ e w, Functor.map_map]
        exact (splits ⟨.finish owner raw, trivial⟩ e w good).1
    | hmac key message =>
        rw [worldStep_reg setup codec route env ⟨.hmac key message, trivial⟩ e w, Functor.map_map]
        exact (splits ⟨.hmac key message, trivial⟩ e w good).1

/-- One joint step keeps admissibility (the invariant obligation of C1). -/
theorem worldStep_keeps (env : Environment n (EnvState KemSK Bk)) (reg : RegImpl KemSK Bk n)
    (created : PqxdhLiveServerConstruction.Created Unit) (splits : Splits created reg env.step)
    (query : PqxdhDeploymentInterface.Spec.Domain) (e : EnvState KemSK Bk) (w : PqxdhRecordLiftWorld.State n)
    (good : Good created e w) :
    ∀ result ∈ support ((worldStep setup codec route env query).run (e, w)), Good created result.2.1 result.2.2 := by
  intro result supported
  rcases query with coin | command
  · rw [worldStep_coin setup codec route env coin e w, support_map] at supported
    obtain ⟨inner, member, rfl⟩ := supported
    have framed := effects_frame (.inl coin) (Or.inl ⟨coin, rfl⟩) w inner member
    exact good_frame created e w inner.2 good framed.1 framed.2
  · cases command with
    | hash bytes =>
        rw [worldStep_hash setup codec route env bytes e w, support_map] at supported
        obtain ⟨inner, member, rfl⟩ := supported
        have framed := effects_frame (.inr (.hash bytes)) (Or.inr ⟨bytes, rfl⟩) w inner member
        exact good_frame created e w inner.2 good framed.1 framed.2
    | serverSend keyId plaintext =>
        rw [worldStep_serverSend setup codec route env keyId plaintext e w, support_map] at supported
        obtain ⟨inner, member, rfl⟩ := supported
        exact serverStep_good setup codec route created (.inl (plaintext, keyId)) e w good inner member
    | serverRaw raw =>
        rw [worldStep_serverRaw setup codec route env raw e w, support_map] at supported
        obtain ⟨inner, member, rfl⟩ := supported
        exact serverStep_good setup codec route created (.inr raw) e w good inner member
    | beaconSend owner plaintext =>
        rw [worldStep_beaconSend setup codec route env owner plaintext e w, support_map] at supported
        obtain ⟨inner, member, rfl⟩ := supported
        exact beaconStep_good setup codec created owner (.inl plaintext) e w good inner member
    | beaconRaw owner raw =>
        rw [worldStep_beaconRaw setup codec route env owner raw e w, support_map] at supported
        obtain ⟨inner, member, rfl⟩ := supported
        exact beaconStep_good setup codec created owner (.inr raw) e w good inner member
    | create pin keyId =>
        rw [worldStep_reg setup codec route env ⟨.create pin keyId, trivial⟩ e w, support_map] at supported
        obtain ⟨inner, member, rfl⟩ := supported
        exact (splits ⟨.create pin keyId, trivial⟩ e w good).2 inner member
    | bundle owner =>
        rw [worldStep_reg setup codec route env ⟨.bundle owner, trivial⟩ e w, support_map] at supported
        obtain ⟨inner, member, rfl⟩ := supported
        exact (splits ⟨.bundle owner, trivial⟩ e w good).2 inner member
    | accept raw =>
        rw [worldStep_reg setup codec route env ⟨.accept raw, trivial⟩ e w, support_map] at supported
        obtain ⟨inner, member, rfl⟩ := supported
        exact (splits ⟨.accept raw, trivial⟩ e w good).2 inner member
    | build session payload =>
        rw [worldStep_reg setup codec route env ⟨.build session payload, trivial⟩ e w, support_map] at supported
        obtain ⟨inner, member, rfl⟩ := supported
        exact (splits ⟨.build session payload, trivial⟩ e w good).2 inner member
    | finish owner raw =>
        rw [worldStep_reg setup codec route env ⟨.finish owner raw, trivial⟩ e w, support_map] at supported
        obtain ⟨inner, member, rfl⟩ := supported
        exact (splits ⟨.finish owner raw, trivial⟩ e w good).2 inner member
    | hmac key message =>
        rw [worldStep_reg setup codec route env ⟨.hmac key message, trivial⟩ e w, support_map] at supported
        obtain ⟨inner, member, rfl⟩ := supported
        exact (splits ⟨.hmac key message, trivial⟩ e w good).2 inner member

/-- The main simulation of C1: from every admissible joint state, the open program interpreted by the environment and the World, reassembled, has the law of the native game with the registration handler on the reassembled state. -/
theorem run_join {α : Type} (env : Environment n (EnvState KemSK Bk)) (reg : RegImpl KemSK Bk n)
    (created : PqxdhLiveServerConstruction.Created Unit) (splits : Splits created reg env.step)
    (work : OracleComp PqxdhDeploymentInterface.Spec α) (e : EnvState KemSK Bk) (w : PqxdhRecordLiftWorld.State n)
    (good : Good created e w) :
    LawEq ((fun result => (result.1.1, merge result.1.2 result.2)) <$>
        (simulateQ (PqxdhRecordLiftWorld.handler setup codec route)
          ((simulateQ (PqxdhRecordLiftInterface.native env) work).run e)).run w)
      ((simulateQ (handlerWith setup codec route reg) work).run (merge e w)) := by
  rw [OracleComp.simulateQ_mapStateTBase_run_eq_map_flattenStateT, Functor.map_map]
  exact PqxdhDeploymentSeedSplit.lawEq_run_simulateQ_of_proj (worldStep setup codec route env) (handlerWith setup codec route reg)
    (fun state => Good created state.1 state.2) (fun state => merge state.1 state.2)
    (fun query state holds => worldStep_step setup codec route env reg created splits query state.1 state.2 holds)
    (fun query state holds => worldStep_keeps setup codec route env reg created splits query state.1 state.2 holds)
    work (e, w) good

end Join


/-! ### Startup and the full C1 join -/

section Startup
variable {Bk : Type} {ι : Type} {baseSpec : OracleSpec ι} {Reader Response : Type}
  (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)

/-- A World state with its uniform, primitive and effect counts forgotten. -/
def uncount (w : PqxdhRecordLiftWorld.State n) : PqxdhRecordLiftWorld.State n :=
  { w with primitive := (PqxdhRecordLiftWorld.Counts.empty, w.primitive.2) }

/-- A computation whose state is never touched keeps the state. -/
theorem simulateQ_lift_run {α σ : Type} (work : ProbComp α) (state : σ) :
    (simulateQ (fun coin => (StateT.lift (unifSpec.query coin : ProbComp _) : StateT σ ProbComp _)) work).run state =
      (fun value => (value, state)) <$> work := by
  induction work using OracleComp.inductionOn with
  | pure value => simp only [simulateQ_pure, StateT.run_pure, map_pure]
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, id_map,
        StateT.run_bind, StateT.run_lift, bind_assoc, pure_bind, ih, map_bind]

/-- The World's coin route, its counts forgotten, is the plain coin route with the World unchanged. -/
theorem coins_world {α : Type} (work : ProbComp α) (w : PqxdhRecordLiftWorld.State n) :
    Prod.map id uncount <$> (simulateQ (PqxdhRecordLiftWorld.handler setup codec route)
      (simulateQ PqxdhRecordLiftInterface.coinLift work)).run w = (fun value => (value, uncount w)) <$> work := by
  rw [← QueryImpl.simulateQ_compose]
  rw [OracleComp.map_run_simulateQ_eq_of_query_map_eq _
    (fun coin => (StateT.lift (unifSpec.query coin : ProbComp _) : StateT (PqxdhRecordLiftWorld.State n) ProbComp _))
    uncount (fun coin state => ?_) work w, simulateQ_lift_run]
  have forgot := PqxdhRecordLiftWorld.countCoin_forget (unifSpec.query coin : ProbComp _) state.primitive.1.uniform
  simp only [QueryImpl.apply_compose, PqxdhRecordLiftInterface.coinLift, simulateQ_spec_query, StateT.run_lift,
    bind_pure_comp]
  conv_rhs => rw [← forgot, Functor.map_map]
  change (Prod.map id uncount <$> ((PqxdhRecordLiftWorld.sampled (unifSpec.query coin : ProbComp _)).run
    (PqxdhRecordLiftWorld.chargeEffect (.inl coin) state))) = _
  simp only [PqxdhRecordLiftWorld.sampled, StateT.run, bind_pure_comp, Functor.map_map]
  rfl

/-- The World after the startup coins and the private Server initialization, with every count forgotten. -/
def initialized (created : PqxdhLiveServerConstruction.Created Unit) (w : PqxdhRecordLiftWorld.State n) :
    PqxdhRecordLiftWorld.State n :=
  { w with server := some ⟨created.server.server.metadata.sender,
      ⟨⟨created.server.server.identity, created.server.server.peers, ()⟩, 0⟩⟩ }

/-- The constructed Server's initial environment state and its initialized World reassemble to the native game's initial state. -/
theorem merge_initial (created : PqxdhLiveServerConstruction.Created Unit) (backend : Bk) (w : PqxdhRecordLiftWorld.State n)
    (fresh : uncount w = uncount (PqxdhRecordLiftWorld.initial (n := n))) :
    merge (PqxdhDeploymentEnvironment.envInitial (KemSK := KemSK) created backend) (initialized created w) =
      PqxdhDeploymentBackend.xinitial created backend := by
  have owners : w.owners = [] := congrArg PqxdhRecordLiftWorld.State.owners fresh
  have ownerRaw : w.ownerRaw = fun _ => 0 := congrArg PqxdhRecordLiftWorld.State.ownerRaw fresh
  have produced : w.produced = [] := congrArg PqxdhRecordLiftWorld.State.produced fresh
  have cache : w.primitive.2 = ∅ := congrArg (fun state => state.primitive.2) fresh
  have seeds : w.seeds.1 = ∅ := congrArg (fun state => state.seeds.1) fresh
  simp only [merge, initialized, fill, fillServer, ownerRaw, produced, cache, seeds,
    PqxdhDeploymentEnvironment.envInitial, PqxdhDeploymentEnvironment.strip, List.map_nil, List.mapIdx_nil,
    PqxdhRegistrationSchedule.initial, Option.map_some, Option.getD_some]
  rfl

/-- The constructed Server's initial environment state and its initialized World are admissible. -/
theorem good_initial (created : PqxdhLiveServerConstruction.Created Unit) (backend : Bk) (w : PqxdhRecordLiftWorld.State n)
    (fresh : uncount w = uncount (PqxdhRecordLiftWorld.initial (n := n))) :
    Good created (PqxdhDeploymentEnvironment.envInitial (KemSK := KemSK) created backend) (initialized created w) := by
  have owners : w.owners = [] := congrArg PqxdhRecordLiftWorld.State.owners fresh
  refine ⟨PqxdhDeploymentEnvironment.envInitial_stripped created backend, rfl, ⟨_, rfl, rfl, rfl, fun keyId => rfl⟩,
    ?_, fun index owner found => ?_⟩
  · simp only [initialized, owners, PqxdhDeploymentEnvironment.envInitial, PqxdhDeploymentEnvironment.strip,
      PqxdhRegistrationSchedule.initial, List.map_nil, List.length_nil]
  · simp only [PqxdhDeploymentEnvironment.envInitial, PqxdhDeploymentEnvironment.strip,
      PqxdhRegistrationSchedule.initial, List.map_nil, List.getElem?_nil, reduceCtorEq] at found

end Startup

section Full
variable {Bk : Type} {ι : Type} {baseSpec : OracleSpec ι} {Reader Response A X : Type}
  (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)

/-- The reassembled outcome of the record world: the constructed Server's public data, the adversary's output, the ledger and the reassembled final state. -/
def joined {Out : Type} (result : Option (PqxdhRegistrationJointServerBirth.ClientCreated Unit ×
    (Out × PqxdhDeploymentSecrecy.Ledger) × EnvState KemSK Bk) × PqxdhRecordLiftWorld.State n) :
    Option (PqxdhRegistrationJointServerBirth.ClientCreated Unit × Out × PqxdhDeploymentSecrecy.Ledger × XState KemSK Bk n) :=
  result.1.map fun value => (value.1, value.2.1.1, value.2.1.2, merge value.2.2 result.2)

/-- C1 generic (design-v2 section 5.9, at the full reassembled state): if the environment starts as the actual Server constructor with the registration handler's initial backend and splits every constructed Server's registration handler, the common deployment experiment with that handler and the record world with that environment have the same law of the Server's public data, the adversary's output, the ledger and the full reassembled final state. -/
theorem join (init : PqxdhLiveServerConstruction.Created Unit → Bk)
    (reg : PqxdhLiveServerConstruction.Created Unit → RegImpl KemSK Bk n) (env : Environment n (EnvState KemSK Bk))
    (ensureInit : StateT A ProbComp Bool) (identityIndex : Nat) (runtime : A)
    (born : env.start = PqxdhDeploymentEnvironment.start setup ensureInit identityIndex runtime init)
    (splits : ∀ created, Splits created (reg created) env.step)
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (adversary : OracleComp (PqxdhDeploymentInterface.ModeSpec mode) X) :
    LawEq ((gameWith setup codec route init reg ensureInit identityIndex bounds mode adversary).run' runtime)
      (joined <$> PqxdhRecordLiftWorld.run setup codec route env setup.serverKeyId bounds mode adversary) := by
  let wrapped := PqxdhDeploymentSecrecy.wrap setup.source.crypto codec setup.serverKeyId bounds
    (PqxdhDeploymentInterface.asModeO mode adversary)
  let native : Option (PqxdhLiveServerConstruction.Created Unit × EnvState KemSK Bk) →
      ProbComp (Option (PqxdhRegistrationJointServerBirth.ClientCreated Unit × X × PqxdhDeploymentSecrecy.Ledger ×
        XState KemSK Bk n)) := fun born => match born with
    | none => pure none
    | some (created, _) => (fun result => some (PqxdhRegistrationJointServerBirth.encode created, result.1.1,
        result.1.2, result.2)) <$> (simulateQ (handlerWith setup codec route (reg created)) wrapped).run
          (PqxdhDeploymentBackend.xinitial created (init created))
  -- the native game is the constructor followed by `native`
  have nativeSide : (gameWith setup codec route init reg ensureInit identityIndex bounds mode adversary).run' runtime =
      env.start >>= native := by
    rw [born]
    simp only [gameWith, PqxdhDeploymentEnvironment.start, StateT.run', StateT.run, map_bind, bind_map_left]
    refine bind_congr fun constructed => ?_
    cases constructed.1 <;> simp only [map_pure, Functor.map_map, Option.map_none, Option.map_some, native]
    rfl
  -- the record world is the counted startup followed by its continuation
  let startup := (simulateQ (PqxdhRecordLiftWorld.handler setup codec route)
    (simulateQ PqxdhRecordLiftInterface.coinLift env.start)).run (PqxdhRecordLiftWorld.initial (n := n))
  have counted := coins_world setup codec route env.start (PqxdhRecordLiftWorld.initial (n := n))
  have startupFst : Prod.fst <$> startup = env.start := by
    have forgot := congrArg (fun work => Prod.fst <$> work) counted
    simpa only [Functor.map_map, Prod.map_fst, id_eq, Function.comp_def, id_map'] using forgot
  rw [nativeSide, ← startupFst, bind_map_left]
  simp only [PqxdhRecordLiftWorld.run, PqxdhRecordLiftInterface.program, simulateQ_bind, StateT.run_bind, map_bind]
  refine LawEq.symm (PqxdhDeploymentSeedSplit.LawEq.bind_support _ fun step member => ?_)
  have fresh : uncount step.2 = uncount (PqxdhRecordLiftWorld.initial (n := n)) := by
    have inMapped : Prod.map id uncount step ∈ support (Prod.map id uncount <$> startup) := by
      rw [support_map]
      exact ⟨step, member, rfl⟩
    rw [counted, support_map] at inMapped
    obtain ⟨_, _, same⟩ := inMapped
    exact (congrArg Prod.snd same).symm
  have started : step.1 ∈ support env.start := by
    rw [← startupFst, support_map]
    exact ⟨step, member, rfl⟩
  rcases step with ⟨_ | ⟨created, initialEnv⟩, w⟩
  · simp only [simulateQ_pure, StateT.run_pure, map_pure, joined, Option.map_none]
    exact LawEq.refl _
  · rw [born] at started
    have initialEq := PqxdhDeploymentEnvironment.start_initial setup ensureInit identityIndex runtime init created
      initialEnv started
    subst initialEq
    have vacant : w.server = none := congrArg PqxdhRecordLiftWorld.State.server fresh
    have initRun : (PqxdhRecordLiftWorld.handler setup codec route (.inl created)).run w =
        pure ((), initialized created w) := by
      change PqxdhRecordLiftWorld.initializeServer created w = _
      simp only [PqxdhRecordLiftWorld.initializeServer, vacant]
      rfl
    have joinedRun := (run_join setup codec route env (reg created) created (splits created) wrapped
      (PqxdhDeploymentEnvironment.envInitial created (init created)) (initialized created w)
      (good_initial created (init created) w fresh)).map
        (fun result => some (PqxdhRegistrationJointServerBirth.encode created, result.1.1, result.1.2, result.2))
    rw [merge_initial created (init created) w fresh, Functor.map_map] at joinedRun
    dsimp only
    rw [simulateQ_bind, StateT.run_bind, simulateQ_spec_query, initRun, pure_bind]
    simp only [bind_pure_comp,
      simulateQ_map, StateT.run_map, Functor.map_map]
    exact joinedRun

/-- C3 (critique M7): every BLAKE2b query of the common deployment experiment, whether the adversary's, a record's or the registration's, is a query on the World's shared cache; jointly with the Server's public data, the output and the ledger, the final CTX cache of the native game has the law of the World's shared cache. -/
theorem c3_shared_cache (init : PqxdhLiveServerConstruction.Created Unit → Bk)
    (reg : PqxdhLiveServerConstruction.Created Unit → RegImpl KemSK Bk n) (env : Environment n (EnvState KemSK Bk))
    (ensureInit : StateT A ProbComp Bool) (identityIndex : Nat) (runtime : A)
    (born : env.start = PqxdhDeploymentEnvironment.start setup ensureInit identityIndex runtime init)
    (splits : ∀ created, Splits created (reg created) env.step)
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (adversary : OracleComp (PqxdhDeploymentInterface.ModeSpec mode) X) :
    LawEq ((fun outcome => outcome.map fun value => (value.1, value.2.1, value.2.2.1,
        value.2.2.2.base.native.shared.2.ctx)) <$>
        (gameWith setup codec route init reg ensureInit identityIndex bounds mode adversary).run' runtime)
      ((fun result => result.1.map fun value => (value.1, value.2.1.1, value.2.1.2, result.2.primitive.2)) <$>
        PqxdhRecordLiftWorld.run setup codec route env setup.serverKeyId bounds mode adversary) := by
  have joined := (join setup codec route init reg env ensureInit identityIndex runtime born splits bounds mode
    adversary).map (fun outcome => outcome.map fun value => (value.1, value.2.1, value.2.2.1,
      value.2.2.2.base.native.shared.2.ctx))
  rw [Functor.map_map] at joined
  refine joined.trans (LawEq.of_eq ?_)
  congr 1
  funext result
  rcases result with ⟨_ | value, w⟩ <;> rfl

/-- The observed projection of C1 (`PqxdhRecordLiftWorld.game`): the adversary's output, the ledger and the produced frames of the native game have the law of the record world's game. -/
theorem join_observed (init : PqxdhLiveServerConstruction.Created Unit → Bk)
    (reg : PqxdhLiveServerConstruction.Created Unit → RegImpl KemSK Bk n) (env : Environment n (EnvState KemSK Bk))
    (ensureInit : StateT A ProbComp Bool) (identityIndex : Nat) (runtime : A)
    (born : env.start = PqxdhDeploymentEnvironment.start setup ensureInit identityIndex runtime init)
    (splits : ∀ created, Splits created (reg created) env.step)
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (adversary : OracleComp (PqxdhDeploymentInterface.ModeSpec mode) X) :
    LawEq ((fun outcome => outcome.map fun value => (value.2.1, value.2.2.1, value.2.2.2.base.produced)) <$>
        (gameWith setup codec route init reg ensureInit identityIndex bounds mode adversary).run' runtime)
      (PqxdhRecordLiftWorld.game setup codec route env setup.serverKeyId bounds mode adversary) := by
  have joined := (join setup codec route init reg env ensureInit identityIndex runtime born splits bounds mode
    adversary).map (fun outcome => outcome.map fun value => (value.2.1, value.2.2.1, value.2.2.2.base.produced))
  rw [Functor.map_map] at joined
  refine joined.trans (LawEq.of_eq ?_)
  unfold PqxdhRecordLiftWorld.game
  congr 1
  funext result
  rcases result with ⟨_ | value, w⟩ <;> rfl

/-- The analysis projection of C1 (`PqxdhRecordLiftWorld.analysis`): the adversary's output, the ledger, the produced frames and the raw-attempt counters of the native game have the law of the record world's analysis projection. -/
theorem join_analysis (init : PqxdhLiveServerConstruction.Created Unit → Bk)
    (reg : PqxdhLiveServerConstruction.Created Unit → RegImpl KemSK Bk n) (env : Environment n (EnvState KemSK Bk))
    (ensureInit : StateT A ProbComp Bool) (identityIndex : Nat) (runtime : A)
    (born : env.start = PqxdhDeploymentEnvironment.start setup ensureInit identityIndex runtime init)
    (splits : ∀ created, Splits created (reg created) env.step)
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (adversary : OracleComp (PqxdhDeploymentInterface.ModeSpec mode) X) :
    LawEq ((fun outcome => outcome.map fun value => (value.2.1, value.2.2.1, value.2.2.2.base.produced,
        (⟨value.2.2.2.base.serverRaw, value.2.2.2.base.ownerRaw⟩ : PqxdhRecordLiftWorld.RawCounters))) <$>
        (gameWith setup codec route init reg ensureInit identityIndex bounds mode adversary).run' runtime)
      (PqxdhRecordLiftWorld.analysis <$> PqxdhRecordLiftWorld.run setup codec route env setup.serverKeyId bounds mode
        adversary) := by
  have joined := (join setup codec route init reg env ensureInit identityIndex runtime born splits bounds mode
    adversary).map (fun outcome => outcome.map fun value => (value.2.1, value.2.2.1, value.2.2.2.base.produced,
      (⟨value.2.2.2.base.serverRaw, value.2.2.2.base.ownerRaw⟩ : PqxdhRecordLiftWorld.RawCounters)))
  rw [Functor.map_map] at joined
  refine joined.trans (LawEq.of_eq ?_)
  congr 1
  funext result
  rcases result with ⟨_ | value, w⟩ <;> rfl

end Full


/-! ### C6: the later game -/

section Reveal

/-- The LQ-F reveal of an environment state (design-v2 section 5.9, r6-shape reply): the Beacon-side reveal of the environment's owners and snapshot, and the environment's own copy of the Server seed with the ephemeral log. -/
def envReveal {Bk : Type} (e : EnvState KemSK Bk) : PqxdhDeploymentLaterServerGame.Reveal :=
  (PqxdhDeploymentLater.revealOf e.native.owners e.snap, (some e.created.seed, e.log))

/-- Stripping an owner's kernel changes nothing it reveals. -/
theorem revealed_strip (snap : PqxdhDeploymentLater.Snap) (index : Nat) (owner : PqxdhRegistrationSchedule.Owner KemSK) :
    PqxdhDeploymentLater.revealed snap index (stripOwner owner) = PqxdhDeploymentLater.revealed snap index owner := by
  unfold stripOwner
  cases phase : owner.beacon.phase <;> simp only []
  simp only [PqxdhDeploymentLater.revealed, PqxdhRegistrationJointLiveRead.value,
    PqxdhRegistrationJointLiveRead.localValue, phase]

/-- The reveal reads identities and scalars, not kernels (design-v2 section 5.9). -/
theorem revealOf_strip (owners : List (PqxdhRegistrationSchedule.Owner KemSK)) (snap : PqxdhDeploymentLater.Snap) :
    PqxdhDeploymentLater.revealOf (owners.map stripOwner) snap = PqxdhDeploymentLater.revealOf owners snap := by
  rw [PqxdhDeploymentLater.revealOf_eq, PqxdhDeploymentLater.revealOf_eq]
  apply List.ext_getElem?
  intro index
  simp only [List.getElem?_mapIdx, List.getElem?_map, Option.map_map]
  cases owners[index]? with
  | none => rfl
  | some owner => exact congrArg some (revealed_strip snap index owner)

/-- Filling an owner with a consistent World phase changes nothing it reveals. -/
theorem revealed_fill (snap : PqxdhDeploymentLater.Snap) (index : Nat) (phase : PqxdhRecordLiftBeacon.Phase)
    (owner : PqxdhRegistrationSchedule.Owner KemSK)
    (matched : stripPhase phase = PqxdhRecordLiftBeacon.projectPhase owner.beacon) :
    PqxdhDeploymentLater.revealed snap index (fillOwner (some phase) owner) =
      PqxdhDeploymentLater.revealed snap index owner := by
  rcases phase_cases phase owner matched with ⟨filled, _⟩ | ⟨control, associatedData, stale, kernel, ownerPhase, rfl⟩
  · rw [filled]
  · simp only [fillOwner, PqxdhDeploymentLater.revealed, PqxdhRegistrationJointLiveRead.value,
      PqxdhRegistrationJointLiveRead.localValue, ownerPhase]

/-- Filling an owner with any World phase changes nothing it reveals: only an established owner's established fields change. -/
theorem revealed_fill_any (snap : PqxdhDeploymentLater.Snap) (index : Nat) (phase : Option PqxdhRecordLiftBeacon.Phase)
    (owner : PqxdhRegistrationSchedule.Owner KemSK) :
    PqxdhDeploymentLater.revealed snap index (fillOwner phase owner) = PqxdhDeploymentLater.revealed snap index owner := by
  unfold fillOwner
  split
  · rename_i shell kernel control associatedData stale ownerPhase
    simp only [PqxdhDeploymentLater.revealed, PqxdhRegistrationJointLiveRead.value,
      PqxdhRegistrationJointLiveRead.localValue, ownerPhase]
  · rfl

/-- The Beacon-side reveal of the reassembled owners is the environment's (the reveal reads identities and scalars, never the World's kernels). -/
theorem revealOf_fill (w : PqxdhRecordLiftWorld.State n) (state : PqxdhRegistrationSchedule.State KemSK)
    (snap : PqxdhDeploymentLater.Snap) :
    PqxdhDeploymentLater.revealOf (fill w state).owners snap = PqxdhDeploymentLater.revealOf state.owners snap := by
  simp only [fill]
  rw [PqxdhDeploymentLater.revealOf_eq, PqxdhDeploymentLater.revealOf_eq, List.mapIdx_mapIdx]
  apply List.ext_getElem?
  intro index
  simp only [List.getElem?_mapIdx]
  cases state.owners[index]? with
  | none => rfl
  | some owner => exact congrArg some (revealed_fill_any snap index _ owner)

/-- C6 at the switch (design-v2 section 5.9): on an admissible joint state, the LQ-F reveal of the reassembled state is the environment's own reveal; the World's copy of the constructed Server is never read. -/
theorem reveal_merge {Bk : Type} (created : PqxdhLiveServerConstruction.Created Unit) (e : EnvState KemSK Bk)
    (w : PqxdhRecordLiftWorld.State n) (good : Good created e w) :
    PqxdhDeploymentFinishErasure.xreveal created (merge e w) = envReveal e := by
  simp only [PqxdhDeploymentFinishErasure.xreveal, envReveal, merge, fill, good.createdEq]
  congr 1
  rw [PqxdhDeploymentLater.revealOf_eq, PqxdhDeploymentLater.revealOf_eq, List.mapIdx_mapIdx]
  apply List.ext_getElem?
  intro index
  simp only [List.getElem?_mapIdx]
  cases found : e.native.owners[index]? with
  | none => rfl
  | some owner =>
      have consistent := good.owners index owner found
      cases foundW : w.owners[index]? with
      | none => simp only [foundW, Option.map_none, reduceCtorEq] at consistent
      | some phase =>
          simp only [foundW, Option.map_some, Option.some.injEq] at consistent
          simp only [Option.map_some, Function.comp_apply]
          exact congrArg some (revealed_fill e.snap index phase owner consistent)

/-- The record view of the reassembled state is the World's record view (`PqxdhRecordLiftLater.recordView`): the produced frames and the raw-attempt counters. -/
theorem view_merge {Bk : Type} (e : EnvState KemSK Bk) (w : PqxdhRecordLiftWorld.State n) :
    ((merge e (forget w)).base.produced,
      (⟨(merge e (forget w)).base.serverRaw, (merge e (forget w)).base.ownerRaw⟩ : PqxdhRecordLiftWorld.RawCounters)) =
      PqxdhRecordLiftLater.recordView w := rfl

end Reveal


section Later
variable {Bk : Type} {ι : Type} {baseSpec : OracleSpec ι} {Reader Response A X Out : Type}
  (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)

/-- An invariant kept by every step of a stateful handler is kept by every program. -/
theorem keeps_simulateQ {ι' σ α : Type} {spec' : OracleSpec ι'} (impl : QueryImpl spec' (StateT σ ProbComp))
    (inv : σ → Prop) (keeps : ∀ query state, inv state → ∀ result ∈ support ((impl query).run state), inv result.2)
    (work : OracleComp spec' α) (state : σ) (holds : inv state) :
    ∀ result ∈ support ((simulateQ impl work).run state), inv result.2 := by
  induction work using OracleComp.inductionOn generalizing state with
  | pure value =>
      intro result supported
      simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
      subst supported
      exact holds
  | query_bind query next ih =>
      intro result supported
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, id_map,
        StateT.run_bind, mem_support_bind_iff] at supported
      obtain ⟨middle, member, final⟩ := supported
      exact ih middle.1 middle.2 (keeps query state holds middle member) result final

/-- Every outcome of the open program interpreted by the environment and the World from an admissible joint state is admissible. -/
theorem run_keeps {α : Type} (env : Environment n (EnvState KemSK Bk)) (reg : RegImpl KemSK Bk n)
    (created : PqxdhLiveServerConstruction.Created Unit) (splits : Splits created reg env.step)
    (work : OracleComp PqxdhDeploymentInterface.Spec α) (e : EnvState KemSK Bk) (w : PqxdhRecordLiftWorld.State n)
    (good : Good created e w) :
    ∀ result ∈ support ((simulateQ (PqxdhRecordLiftWorld.handler setup codec route)
      ((simulateQ (PqxdhRecordLiftInterface.native env) work).run e)).run w), Good created result.1.2 result.2 := by
  intro result supported
  rw [OracleComp.simulateQ_mapStateTBase_run_eq_map_flattenStateT, support_map] at supported
  obtain ⟨flat, member, rfl⟩ := supported
  exact keeps_simulateQ (worldStep setup codec route env) (fun state => Good created state.1 state.2)
    (fun query state holds => worldStep_keeps setup codec route env reg created splits query state.1 state.2 holds)
    work (e, w) good flat member

/-- C1 with a continuation: the open program from an admissible joint state followed by a continuation of its outcome has the law of the native game followed by a continuation of the reassembled outcome, when the two continuations agree in law on admissible outcomes. -/
theorem run_join_bind {α γ : Type} (env : Environment n (EnvState KemSK Bk)) (reg : RegImpl KemSK Bk n)
    (created : PqxdhLiveServerConstruction.Created Unit) (splits : Splits created reg env.step)
    (work : OracleComp PqxdhDeploymentInterface.Spec α) (e : EnvState KemSK Bk) (w : PqxdhRecordLiftWorld.State n)
    (good : Good created e w) (worldNext : (α × EnvState KemSK Bk) × PqxdhRecordLiftWorld.State n → ProbComp γ)
    (nativeNext : α × XState KemSK Bk n → ProbComp γ)
    (next : ∀ result, Good created result.1.2 result.2 →
      LawEq (worldNext result) (nativeNext (result.1.1, merge result.1.2 result.2))) :
    LawEq ((simulateQ (PqxdhRecordLiftWorld.handler setup codec route)
        ((simulateQ (PqxdhRecordLiftInterface.native env) work).run e)).run w >>= worldNext)
      ((simulateQ (handlerWith setup codec route reg) work).run (merge e w) >>= nativeNext) := by
  refine (PqxdhDeploymentSeedSplit.LawEq.bind_support _ fun result member =>
    next result (run_keeps setup codec route env reg created splits work e w good result member)).trans ?_
  rw [← bind_map_left (fun result : (α × EnvState KemSK Bk) × PqxdhRecordLiftWorld.State n =>
    (result.1.1, merge result.1.2 result.2))]
  exact (run_join setup codec route env reg created splits work e w good).bind fun _ => LawEq.refl _

/-- The two phases of the later record world: the World run of the first adversary, then the post phase on the same environment and World from the run's final states (r6-later reply point 2). -/
theorem run_split {R : Type} (env : Environment n (EnvState KemSK Bk)) (serverKid : Std.U64)
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (reveal : EnvState KemSK Bk → R) (first : OracleComp (PqxdhDeploymentInterface.ModeSpec mode) X)
    (second : X → R → OracleComp PqxdhDeploymentLater.PostSpec Out) :
    PqxdhRecordLiftLater.run setup codec route env serverKid bounds mode reveal first second =
      PqxdhRecordLiftWorld.run setup codec route env serverKid bounds mode first >>= fun result =>
        match result.1 with
        | none => pure (none, result.2)
        | some (created, (output, ledger), state) =>
            (fun later => (some (created, (later.1.1, ledger), later.1.2), later.2)) <$>
              (simulateQ (PqxdhRecordLiftWorld.handler setup codec route)
                ((PqxdhRecordLiftLater.post env (second output (reveal state))).run state)).run result.2 := by
  simp only [PqxdhRecordLiftLater.run, PqxdhRecordLiftLater.program, PqxdhRecordLiftWorld.run, simulateQ_bind,
    StateT.run_bind]
  refine bind_congr fun result => ?_
  rcases result with ⟨_ | ⟨created, ⟨output, ledger⟩, state⟩, world⟩
  · simp only [simulateQ_pure, StateT.run_pure]
  · simp only [bind_pure_comp, simulateQ_map,
      StateT.run_map]

/-- The post phase of the native game with a registration handler: the run-phase handler on the post-run commands (coins, HMAC, BLAKE2b), as LQ-F's `postImpl` is the native handler after `postEmbed` (`PqxdhDeploymentLater.post_embed`). -/
noncomputable def postNative (reg : RegImpl KemSK Bk n) :
    QueryImpl PqxdhDeploymentLater.PostSpec (StateT (XState KemSK Bk n) ProbComp) :=
  handlerWith setup codec route reg ∘ₛ PqxdhDeploymentLater.postEmbed

/-- C6 (design-v2 section 5.9, r6-later reply): if the environment starts as the actual Server constructor with the registration handler's initial backend and splits every constructed Server's registration handler, the LQ-F later game with that handler (`PqxdhDeploymentFinishErasure.laterWith`, its post phase the run-phase handler on the post commands) and the later record world (`PqxdhRecordLiftLater.run`) with that environment and the environment's own reveal have the same law of the Server's public data, the second adversary's output, the run-phase ledger and the full reassembled final state. The second adversary receives the same reveal on both sides (`reveal_merge`). -/
theorem join_later (init : PqxdhLiveServerConstruction.Created Unit → Bk)
    (reg : PqxdhLiveServerConstruction.Created Unit → RegImpl KemSK Bk n) (env : Environment n (EnvState KemSK Bk))
    (ensureInit : StateT A ProbComp Bool) (identityIndex : Nat) (runtime : A)
    (born : env.start = PqxdhDeploymentEnvironment.start setup ensureInit identityIndex runtime init)
    (splits : ∀ created, Splits created (reg created) env.step)
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (first : OracleComp (PqxdhDeploymentInterface.ModeSpec mode) X)
    (second : X → PqxdhDeploymentLaterServerGame.Reveal → OracleComp PqxdhDeploymentLater.PostSpec Out) :
    LawEq ((PqxdhDeploymentFinishErasure.laterWith setup codec route init reg
        (fun created => postNative setup codec route (reg created)) ensureInit identityIndex bounds mode first
          second).run' runtime)
      (joined <$> PqxdhRecordLiftLater.run setup codec route env setup.serverKeyId bounds mode envReveal first
        second) := by
  let wrapped := PqxdhDeploymentSecrecy.wrap setup.source.crypto codec setup.serverKeyId bounds
    (PqxdhDeploymentInterface.asModeO mode first)
  let native : Option (PqxdhLiveServerConstruction.Created Unit × EnvState KemSK Bk) →
      ProbComp (Option (PqxdhRegistrationJointServerBirth.ClientCreated Unit × Out × PqxdhDeploymentSecrecy.Ledger ×
        XState KemSK Bk n)) := fun born => match born with
    | none => pure none
    | some (created, _) => (fun result => some (PqxdhRegistrationJointServerBirth.encode created, result)) <$> (do
        let run ← (simulateQ (handlerWith setup codec route (reg created)) wrapped).run
          (PqxdhDeploymentBackend.xinitial created (init created))
        let post ← (simulateQ (postNative setup codec route (reg created))
          (second run.1.1 (PqxdhDeploymentFinishErasure.xreveal created run.2))).run run.2
        pure (post.1, run.1.2, post.2))
  have nativeSide : (PqxdhDeploymentFinishErasure.laterWith setup codec route init reg
      (fun created => postNative setup codec route (reg created)) ensureInit identityIndex bounds mode first
        second).run' runtime = env.start >>= native := by
    rw [born]
    simp only [PqxdhDeploymentFinishErasure.laterWith, PqxdhDeploymentEnvironment.start, StateT.run', StateT.run,
      map_bind, bind_map_left]
    refine bind_congr fun constructed => ?_
    cases constructed.1 <;> simp only [map_pure, Option.map_none, Option.map_some, native, map_bind,
      StateT.run]
    rfl
  let startup := (simulateQ (PqxdhRecordLiftWorld.handler setup codec route)
    (simulateQ PqxdhRecordLiftInterface.coinLift env.start)).run (PqxdhRecordLiftWorld.initial (n := n))
  have counted := coins_world setup codec route env.start (PqxdhRecordLiftWorld.initial (n := n))
  have startupFst : Prod.fst <$> startup = env.start := by
    have forgot := congrArg (fun work => Prod.fst <$> work) counted
    simpa only [Functor.map_map, Prod.map_fst, id_eq, Function.comp_def, id_map'] using forgot
  rw [nativeSide, ← startupFst, bind_map_left, run_split]
  simp only [PqxdhRecordLiftWorld.run, PqxdhRecordLiftInterface.program, simulateQ_bind, StateT.run_bind, map_bind,
    bind_assoc]
  refine LawEq.symm (PqxdhDeploymentSeedSplit.LawEq.bind_support _ fun step member => ?_)
  have fresh : uncount step.2 = uncount (PqxdhRecordLiftWorld.initial (n := n)) := by
    have inMapped : Prod.map id uncount step ∈ support (Prod.map id uncount <$> startup) := by
      rw [support_map]
      exact ⟨step, member, rfl⟩
    rw [counted, support_map] at inMapped
    obtain ⟨_, _, same⟩ := inMapped
    exact (congrArg Prod.snd same).symm
  have started : step.1 ∈ support env.start := by
    rw [← startupFst, support_map]
    exact ⟨step, member, rfl⟩
  rcases step with ⟨_ | ⟨created, initialEnv⟩, w⟩
  · simp only [simulateQ_pure, StateT.run_pure, pure_bind, map_pure, joined, Option.map_none]
    exact LawEq.refl _
  · rw [born] at started
    have initialEq := PqxdhDeploymentEnvironment.start_initial setup ensureInit identityIndex runtime init created
      initialEnv started
    subst initialEq
    have vacant : w.server = none := congrArg PqxdhRecordLiftWorld.State.server fresh
    have initRun : (PqxdhRecordLiftWorld.handler setup codec route (.inl created)).run w =
        pure ((), initialized created w) := by
      change PqxdhRecordLiftWorld.initializeServer created w = _
      simp only [PqxdhRecordLiftWorld.initializeServer, vacant]
      rfl
    dsimp only
    rw [simulateQ_bind, StateT.run_bind, simulateQ_spec_query, initRun, pure_bind]
    simp only [simulateQ_bind, StateT.run_bind, simulateQ_pure, StateT.run_pure, bind_assoc, pure_bind]
    rw [← merge_initial created (init created) w fresh]
    refine run_join_bind setup codec route env (reg created) created (splits created) wrapped _ _
      (good_initial created (init created) w fresh) _ _ (fun result good => ?_)
    rcases result with ⟨⟨⟨output, ledger⟩, finalEnv⟩, finalWorld⟩
    dsimp only
    rw [reveal_merge created finalEnv finalWorld good]
    have posted := (run_join setup codec route env (reg created) created (splits created)
      (simulateQ PqxdhDeploymentLater.postEmbed (second output (envReveal finalEnv))) finalEnv finalWorld good).map
        (fun result => some (PqxdhRegistrationJointServerBirth.encode created, result.1, ledger, result.2))
    simp only [Functor.map_map] at posted
    simp only [postNative, QueryImpl.simulateQ_compose, map_pure, bind_pure_comp, Functor.map_map,
      PqxdhRecordLiftLater.post]
    exact posted

/-- C6, public form (r6-later reply, `join_later_public`): the Server's public data, the second adversary's output, the run-phase ledger, the record view (produced frames and raw-attempt counters) and the Beacon-side reveal with the Server ephemeral log of the final state have the same law in the LQ-F later game with the registration handler and in the later record world with the environment. -/
theorem join_later_public (init : PqxdhLiveServerConstruction.Created Unit → Bk)
    (reg : PqxdhLiveServerConstruction.Created Unit → RegImpl KemSK Bk n) (env : Environment n (EnvState KemSK Bk))
    (ensureInit : StateT A ProbComp Bool) (identityIndex : Nat) (runtime : A)
    (born : env.start = PqxdhDeploymentEnvironment.start setup ensureInit identityIndex runtime init)
    (splits : ∀ created, Splits created (reg created) env.step)
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (first : OracleComp (PqxdhDeploymentInterface.ModeSpec mode) X)
    (second : X → PqxdhDeploymentLaterServerGame.Reveal → OracleComp PqxdhDeploymentLater.PostSpec Out) :
    LawEq ((fun outcome => outcome.map fun value => (value.1, value.2.1, value.2.2.1,
        (value.2.2.2.base.produced,
          (⟨value.2.2.2.base.serverRaw, value.2.2.2.base.ownerRaw⟩ : PqxdhRecordLiftWorld.RawCounters)),
        (PqxdhDeploymentLater.revealOf value.2.2.2.base.native.owners value.2.2.2.snap, value.2.2.2.log))) <$>
        (PqxdhDeploymentFinishErasure.laterWith setup codec route init reg
          (fun created => postNative setup codec route (reg created)) ensureInit identityIndex bounds mode first
            second).run' runtime)
      ((fun result => result.1.map fun value => (value.1, value.2.1.1, value.2.1.2,
          PqxdhRecordLiftLater.recordView result.2,
          (PqxdhDeploymentLater.revealOf value.2.2.native.owners value.2.2.snap, value.2.2.log))) <$>
        PqxdhRecordLiftLater.run setup codec route env setup.serverKeyId bounds mode envReveal first second) := by
  have joinedLater := (join_later setup codec route init reg env ensureInit identityIndex runtime born splits bounds mode
    first second).map (fun outcome => outcome.map fun value => (value.1, value.2.1, value.2.2.1,
      (value.2.2.2.base.produced,
        (⟨value.2.2.2.base.serverRaw, value.2.2.2.base.ownerRaw⟩ : PqxdhRecordLiftWorld.RawCounters)),
      (PqxdhDeploymentLater.revealOf value.2.2.2.base.native.owners value.2.2.2.snap, value.2.2.2.log)))
  rw [Functor.map_map] at joinedLater
  refine joinedLater.trans (LawEq.of_eq ?_)
  congr 1
  funext result
  rcases result with ⟨_ | value, w⟩
  · rfl
  · simp only [joined, Option.map_some, Option.some.injEq]
    rw [show (merge value.2.2 w).base.native.owners = (fill w value.2.2.native).owners from rfl, revealOf_fill]
    rfl

end Later

end BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentJoin

-- Axiom guards (generated)

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentJoin.merge_forget' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentJoin.merge_forget

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentJoin.worldStep_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentJoin.worldStep_run

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentJoin.merge_sampled' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentJoin.merge_sampled

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentJoin.merge_charge' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentJoin.merge_charge

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentJoin.coin_join' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentJoin.coin_join

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentJoin.hash_join' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentJoin.hash_join

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentJoin.world_primitives_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentJoin.world_primitives_run

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentJoin.nativeServerStep_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentJoin.nativeServerStep_run

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentJoin.serverStep_merge' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentJoin.serverStep_merge

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentJoin.phase_cases' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentJoin.phase_cases

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentJoin.fill_owners_set' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentJoin.fill_owners_set

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentJoin.beaconStep_merge' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentJoin.beaconStep_merge

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentJoin.logged_support' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentJoin.logged_support

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentJoin.putPeer_stripped' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentJoin.putPeer_stripped

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentJoin.serverImpl_stripped' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentJoin.serverImpl_stripped

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentJoin.beaconHandler_stripped' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentJoin.beaconHandler_stripped

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentJoin.good_frame' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentJoin.good_frame

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentJoin.effects_frame' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentJoin.effects_frame

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentJoin.serverStep_good' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentJoin.serverStep_good

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentJoin.beaconStep_good' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentJoin.beaconStep_good

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentJoin.worldStep_reg' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentJoin.worldStep_reg

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentJoin.lift_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentJoin.lift_run

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentJoin.worldStep_coin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentJoin.worldStep_coin

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentJoin.worldStep_hash' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentJoin.worldStep_hash

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentJoin.worldStep_serverSend' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentJoin.worldStep_serverSend

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentJoin.worldStep_serverRaw' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentJoin.worldStep_serverRaw

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentJoin.worldStep_beaconSend' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentJoin.worldStep_beaconSend

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentJoin.worldStep_beaconRaw' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentJoin.worldStep_beaconRaw

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentJoin.worldStep_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentJoin.worldStep_step

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentJoin.worldStep_keeps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentJoin.worldStep_keeps

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentJoin.run_join' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentJoin.run_join

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentJoin.simulateQ_lift_run' depends on axioms: [propext,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentJoin.simulateQ_lift_run

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentJoin.coins_world' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentJoin.coins_world

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentJoin.merge_initial' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentJoin.merge_initial

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentJoin.good_initial' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentJoin.good_initial

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentJoin.join' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentJoin.join

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentJoin.c3_shared_cache' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentJoin.c3_shared_cache

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentJoin.join_observed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentJoin.join_observed

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentJoin.join_analysis' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentJoin.join_analysis

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentJoin.revealed_strip' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentJoin.revealed_strip

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentJoin.revealOf_strip' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentJoin.revealOf_strip

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentJoin.revealed_fill' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentJoin.revealed_fill

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentJoin.revealed_fill_any' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentJoin.revealed_fill_any

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentJoin.revealOf_fill' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentJoin.revealOf_fill

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentJoin.reveal_merge' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentJoin.reveal_merge

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentJoin.view_merge' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentJoin.view_merge

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentJoin.keeps_simulateQ' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentJoin.keeps_simulateQ

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentJoin.run_keeps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentJoin.run_keeps

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentJoin.run_join_bind' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentJoin.run_join_bind

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentJoin.run_split' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentJoin.run_split

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentJoin.join_later' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentJoin.join_later

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentJoin.join_later_public' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentJoin.join_later_public
