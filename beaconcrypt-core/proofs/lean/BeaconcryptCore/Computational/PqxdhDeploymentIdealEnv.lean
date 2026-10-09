-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvFacts
import BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentDraw

/-!
# The ideal environment of the common deployment experiment (CE-11b, unit U3)

CE-11b's ideal environment (design-v2 section 6) and its C1 with the final split form `PqxdhDeploymentIdealDefer.idealSplit`.

- `idealStep`: the capability form of `idealSplit t p` per command (pool create, real bundle and HMAC, selected raw accept and every other accept with the accept counter advanced, the marked build of the marked session while it has a pending token and every other build, owner k's challenge finish after an active selected accept and every other finish), with its branches (`idealStep_selected`, `idealStep_accept_other`, `idealStep_build`, `idealStep_challenge`, `idealStep_finish_real`). The marked build reads its slot's material from the environment's material cache without a draw (`buildCachedEnv`); at a cached slot it is `PqxdhDeploymentIdealEnvBuild.buildHiddenEnv` (`buildCached_hit`), it leaves the cache unchanged (`buildCached_cache`), and the build class stays within the first-touch allowance at every environment state (`buildCached_bound`, `idealStep_build_bound`).
- `IdealInv`, the admissibility predicate: the World's used markers are the slots of the install ghosts, the seed table holds exactly the used slots' seeds, the material cache holds every allocated slot's material, and the allocator, marks and ghosts satisfy the guards each hidden command needs. `idealInv_stable`, `idealInv_start`; the guards (`initSent_open`, `idealInv_build_ready`, `idealInv_finish_ready`); preservation by moves without hidden effect (`idealInv_move`, `idealInv_realStep`), by the selected accept (`idealInv_selected`), the marked build (`idealInv_build`) and owner k's challenge finish (`idealInv_finish`), from the facts of `PqxdhDeploymentIdealEnvFacts`.
- `ideal_splits`: the ideal step splits `idealSplit t p` relative to `IdealInv t` for every constructed Server.
- The environments `envG` (fixed parameters) and `envGD` (the challenger's parameters drawn at startup, `PqxdhDeploymentEnvironmentDraw.paramEnv`). C1 at the full reassembled state (`c1_split`, `join_param` with `ideal_splits`). C1 for the ideal game itself at the observed projection (the adversary's output, the ledger and the produced frames): `c1_ideal`, through `ideal_to_split` pointwise under the draw, and `c1_idealGame` for `PqxdhDeploymentIdealSteps.idealGame`. For the draw followed by the final split game, not for the ideal game itself (`ideal_to_split` reads both games through `splitView`, which empties the CTX cache): the same final CTX cache (`c3_ideal`) and the same reveal (`ideal_reveal`) as the record world with `envGD`.
- On every outcome of the record world with `envGD`: admissibility (`world_keeps`, generic, and `env_admitted`), at most one slot per role among the World's markers (`server_once`, `beacon_once`, `hidden_server_once`, `hidden_beacon_once`), and F4 at the reassembled state (`seed_at_install`).

Not here: the frames `frame_ideal`/`frame_idealD` beyond the build class, and `c4_ideal` (see the U3 guide). These are equalities in law, support facts and query bounds; no security claim is made here.
-/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete PqxdhRefinement

set_option autoImplicit false

namespace BeaconcryptCore.Computational.PqxdhDeploymentIdealEnv
open PqxdhServerAuthExperiment (Setup Codec Checks GameState)
open PqxdhDeploymentEnvironment (EnvState EnvStep strip coins)
open PqxdhDeploymentEnvironmentJoin (merge uncount Good Splits Stable fixedView initialized)
open PqxdhDeploymentIdealSlots (Coord)
open PqxdhDeploymentIdealSteps (IdealCore SplitBk splitInit initSentAt establishedAt)
open PqxdhDeploymentIdealParams (Target Params)
open PqxdhRecordLiftInterface (EnvEffects EffectKind effectKind)
open PqxdhDeploymentIdealEnvFacts (terminalAt SessionMove AllocMove RealMove AllocCached)

variable {KemSK : Type}

/-! ### The ideal environment step -/

section Step
variable {ι : Type} {baseSpec : OracleSpec ι} {Reader Response : Type}
  (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks) {count : ℕ}

/-- The marked build reading its slot's material from the environment's material cache, without a draw: at the slot of the marked coordinates, with the session's pending token and the slot's material cached, CE-11a's split hidden build of that slot (`PqxdhDeploymentEnvironment.buildSplitEnv`) runs on the cached material; the environment keeps the stripped state after the build and sets the Server install ghost when a peer was published (`PqxdhDeploymentIdealEnvBuild.builtEnv`, the material cache unchanged). Without an allocated slot, a pending token or a cached material it does nothing. At a slot whose material is cached it is the lazy-read form `PqxdhDeploymentIdealEnvBuild.buildHiddenEnv` (`buildCached_hit`), and the admissibility predicate `IdealInv` keeps every allocated slot's material cached (`allocCached`), so the build class draws no coin (`idealStep_build_bound`). -/
noncomputable def buildCachedEnv (session : ℕ) (payload : Option Pqxdh.Bytes) (coords : Coord) :
    StateT (EnvState KemSK SplitBk) (OracleComp (EnvEffects 2)) (Option PqxdhServerRegistrationPublication.Response) :=
  fun e => match e.backend.2.1.1 coords, e.native.shared.2.pending session with
  | some j, some token => match e.backend.1 j with
      | some material => do
          let result ← (PqxdhDeploymentEnvironment.buildSplitEnv setup codec checks material j token payload
            e.native.shared.2.server).run []
          pure (result.1.1, PqxdhDeploymentIdealEnvBuild.builtEnv e session coords e.backend.1 result)
      | none => pure (none, e)
  | _, _ => pure (none, e)

/-- The ideal environment step (design-v2 section 6.1), the capability form of the final split form `PqxdhDeploymentIdealDefer.idealSplit t p`: the pool create, the real bundle and HMAC, the selected raw accept (`PqxdhDeploymentIdealEnvStep.acceptSelectedEnv`) and every other raw accept with the accept counter advanced, the marked build while its session has a pending token (`buildCachedEnv`, reading the cached material of its slot) and every other build, owner k's challenge finish after an active selected accept (`PqxdhDeploymentIdealEnvFinish.finishChallengeEnv`) and every other finish. -/
noncomputable def idealStep (t : Target count) (p : Params KemSK count) : EnvStep KemSK SplitBk 2 := fun query =>
  StateT.mk fun e => match query with
  | ⟨.create pin keyId, _⟩ => (PqxdhDeploymentIdealEnvReal.createPoolStep (n := 2) setup (p.pool t) pin keyId).run e
  | ⟨.bundle owner, allowed⟩ => (PqxdhDeploymentEnvironment.realStep setup codec checks ⟨.bundle owner, allowed⟩).run e
  | ⟨.accept raw, allowed⟩ =>
      if e.backend.2.2.accepts = t.accept then
        (PqxdhDeploymentIdealEnvStep.acceptSelectedEnv setup codec checks p raw).run e
      else (PqxdhDeploymentEnvironment.realStep setup codec checks ⟨.accept raw, allowed⟩).run
        { e with backend := PqxdhDeploymentIdealEnvStep.bump e.backend }
  | ⟨.build session payload, allowed⟩ =>
      match e.backend.2.2.marks with
      | some (index, coords) =>
          if index = session ∧ (e.native.shared.2.pending session).isSome then
            (buildCachedEnv setup codec checks session payload coords).run e
          else (PqxdhDeploymentEnvironment.realStep setup codec checks ⟨.build session payload, allowed⟩).run e
      | none => (PqxdhDeploymentEnvironment.realStep setup codec checks ⟨.build session payload, allowed⟩).run e
  | ⟨.finish owner raw, allowed⟩ =>
      if e.backend.2.2.active = true ∧ owner = t.kem.val ∧ initSentAt e.native.owners owner = true then
        (PqxdhDeploymentIdealEnvFinish.finishChallengeEnv setup codec p owner raw).run e
      else (PqxdhDeploymentEnvironment.realStep setup codec checks ⟨.finish owner raw, allowed⟩).run e
  | ⟨.hmac key message, allowed⟩ =>
      (PqxdhDeploymentEnvironment.realStep setup codec checks ⟨.hmac key message, allowed⟩).run e
  | ⟨.hash _, notEnv⟩ => absurd notEnv id
  | ⟨.serverSend _ _, notEnv⟩ => absurd notEnv id
  | ⟨.serverRaw _, notEnv⟩ => absurd notEnv id
  | ⟨.beaconSend _ _, notEnv⟩ => absurd notEnv id
  | ⟨.beaconRaw _ _, notEnv⟩ => absurd notEnv id

end Step

/-! ### The admissibility predicate of the ideal environment -/

/-- The ideal environment's admissibility predicate (design-v2 section 6.2, with the layout of the U3 guide), tying the World's used markers and seed table to the ideal backend: the allocator is well formed (`allocBound`, `allocBelow`); while the accept counter has not passed the selected ordinal nothing is marked, active, installed or allocated (`before`, I5 first clause); the World's Server markers are exactly the slot of the Server install ghost and its Beacon markers exactly the slot of the Beacon install ghost (`serverMarks` I1, `beaconMarks` I2); a marked session with a pending token has no Server install ghost (`pendingPeer`, I3), and a marked session lies below the session counter at allocated coordinates (`markedSession`); while owner k is not terminal there is no Beacon install ghost and at most one allocated slot (`ownerOpen`, I4 and I5 third clause); the Server install ghost is at the marked coordinates (`peerMarked`, I5 last clause); the World's seed table holds exactly the seeds of the used slots (`seeds`, F4 `seed_at_install`); and the material cache holds the material of every allocated slot (`allocCached`, so the marked build reads its slot's material without a draw). -/
structure IdealInv {count : ℕ} (t : Target count) (e : EnvState KemSK SplitBk) (w : PqxdhRecordLiftWorld.State 2) :
    Prop where
  allocBound : e.backend.2.1.2 ≤ 2
  allocBelow : ∀ c j, e.backend.2.1.1 c = some j → j.val < e.backend.2.1.2
  before : e.backend.2.2.accepts ≤ t.accept → e.backend.2.2.marks = none ∧ e.backend.2.2.active = false ∧
    e.backend.2.2.peer = none ∧ e.backend.2.2.beacon = none ∧ e.backend.2.1.2 = 0
  serverMarks : ∀ j, w.used j .server = true ↔ ∃ kid c, e.backend.2.2.peer = some (kid, c) ∧ e.backend.2.1.1 c = some j
  beaconMarks : ∀ j, w.used j .beacon = true ↔ ∃ c, e.backend.2.2.beacon = some c ∧ e.backend.2.1.1 c = some j
  pendingPeer : ∀ s c, e.backend.2.2.marks = some (s, c) → (e.native.shared.2.pending s).isSome = true →
    e.backend.2.2.peer = none
  markedSession : ∀ s c, e.backend.2.2.marks = some (s, c) → s < e.native.shared.2.sessions ∧
    (e.backend.2.1.1 c).isSome = true
  ownerOpen : ¬ terminalAt e.native.owners t.kem.val → e.backend.2.2.beacon = none ∧ e.backend.2.1.2 ≤ 1
  peerMarked : ∀ kid c, e.backend.2.2.peer = some (kid, c) → ∃ s, e.backend.2.2.marks = some (s, c)
  seeds : ∀ j, (w.seeds.1 j).isSome = true ↔ (w.used j .server = true ∨ w.used j .beacon = true)
  allocCached : AllocCached e.backend.2.1 e.backend.1

/-- The ideal admissibility predicate reads the World only through its used markers and its seed table, so it is stable. -/
theorem idealInv_stable {count : ℕ} (t : Target count) : Stable (KemSK := KemSK) (IdealInv t) := by
  intro e w w' same holds
  have used : w'.used = w.used := congrArg Prod.fst same
  have seeds : w'.seeds = w.seeds := congrArg (fun view => view.2.1) same
  exact ⟨holds.allocBound, holds.allocBelow, holds.before, by rw [used]; exact holds.serverMarks,
    by rw [used]; exact holds.beaconMarks, holds.pendingPeer, holds.markedSession, holds.ownerOpen, holds.peerMarked,
    by rw [used, seeds]; exact holds.seeds, holds.allocCached⟩

/-- The ideal admissibility predicate holds at the startup: the empty allocator, the initial ideal backend, no used marker and an empty seed table. -/
theorem idealInv_start {count : ℕ} (t : Target count) (created : PqxdhLiveServerConstruction.Created Unit) :
    IdealInv t (PqxdhDeploymentEnvironment.envInitial (KemSK := KemSK) created (splitInit created))
      (initialized created (PqxdhRecordLiftWorld.initial (n := 2))) := by
  refine ⟨Nat.zero_le 2, fun _ _ found => ?_, fun _ => ⟨rfl, rfl, rfl, rfl, rfl⟩, fun j => ?_, fun j => ?_,
    fun _ _ marked => ?_, fun _ _ marked => ?_, fun _ => ⟨rfl, Nat.zero_le 1⟩, fun _ _ peer => ?_, fun j => ?_,
    fun _ _ found => ?_⟩
  · simp [PqxdhDeploymentEnvironment.envInitial, splitInit, PqxdhRegistrationJointKemSecondEntry.emptyAlloc] at found
  · simp [initialized, PqxdhRecordLiftWorld.initial, PqxdhDeploymentEnvironment.envInitial, splitInit,
      IdealCore.initial]
  · simp [initialized, PqxdhRecordLiftWorld.initial, PqxdhDeploymentEnvironment.envInitial, splitInit,
      IdealCore.initial]
  · simp [PqxdhDeploymentEnvironment.envInitial, splitInit, IdealCore.initial] at marked
  · simp [PqxdhDeploymentEnvironment.envInitial, splitInit, IdealCore.initial] at marked
  · simp [PqxdhDeploymentEnvironment.envInitial, splitInit, IdealCore.initial] at peer
  · simp [initialized, PqxdhRecordLiftWorld.initial, PqxdhRecordLiftLazyTable.initial]
  · simp [PqxdhDeploymentEnvironment.envInitial, splitInit, PqxdhRegistrationJointKemSecondEntry.emptyAlloc] at found

/-! ### Preservation of the admissibility predicate -/

section Preservation
variable {count : ℕ}

/-- An owner in the `initSent` phase is not terminal. -/
theorem initSent_open (owners : List (PqxdhRegistrationSchedule.Owner KemSK)) (index : ℕ)
    (initSent : initSentAt owners index = true) : ¬ terminalAt owners index := by
  rintro ⟨owner, found, terminal⟩
  simp only [initSentAt, found] at initSent
  unfold PqxdhRegistrationSchedule.Terminal at terminal
  cases phase : owner.beacon.phase <;> simp_all

/-- Under the admissibility predicate, a marked session with a pending token has an allocated slot whose World Server marker is unused and whose material is cached, and no Server install ghost. -/
theorem idealInv_build_ready (t : Target count) (e : EnvState KemSK SplitBk) (w : PqxdhRecordLiftWorld.State 2)
    (holds : IdealInv t e w) (session : ℕ) (coords : Coord) (marked : e.backend.2.2.marks = some (session, coords))
    (pending : (e.native.shared.2.pending session).isSome = true) :
    e.backend.2.2.peer = none ∧ ∃ j, e.backend.2.1.1 coords = some j ∧ w.used j .server = false ∧
      (e.backend.1 j).isSome = true := by
  have noPeer := holds.pendingPeer session coords marked pending
  obtain ⟨j, found⟩ := Option.isSome_iff_exists.mp (holds.markedSession session coords marked).2
  refine ⟨noPeer, j, found, ?_, holds.allocCached coords j found⟩
  cases used : w.used j .server
  · rfl
  · obtain ⟨_, _, wrong, _⟩ := (holds.serverMarks j).mp used
    rw [noPeer] at wrong
    cases wrong

/-- Under the admissibility predicate, owner k in the `initSent` phase leaves room in the allocator, no Beacon install ghost and no World Beacon marker. -/
theorem idealInv_finish_ready (t : Target count) (e : EnvState KemSK SplitBk) (w : PqxdhRecordLiftWorld.State 2)
    (holds : IdealInv t e w) (initSent : initSentAt e.native.owners t.kem.val = true) :
    e.backend.2.2.beacon = none ∧ e.backend.2.1.2 < 2 ∧ ∀ j, w.used j .beacon = false := by
  obtain ⟨noBeacon, small⟩ := holds.ownerOpen (initSent_open _ _ initSent)
  refine ⟨noBeacon, by omega, fun j => ?_⟩
  cases used : w.used j .beacon
  · rfl
  · obtain ⟨_, wrong, _⟩ := (holds.beaconMarks j).mp used
    rw [noBeacon] at wrong
    cases wrong

/-- The admissibility predicate is kept by a move that leaves the material cache, the allocator and every ideal backend field but the accept counter unchanged, does not lower the accept counter, moves the Server's sessions, keeps owner k terminal, and leaves the World's used markers and seed table unchanged. -/
theorem idealInv_move (t : Target count) (e e' : EnvState KemSK SplitBk) (w w' : PqxdhRecordLiftWorld.State 2)
    (holds : IdealInv t e w) (cache : e'.backend.1 = e.backend.1) (alloc : e'.backend.2.1 = e.backend.2.1)
    (accepts : e.backend.2.2.accepts ≤ e'.backend.2.2.accepts) (active : e'.backend.2.2.active = e.backend.2.2.active)
    (marks : e'.backend.2.2.marks = e.backend.2.2.marks) (peer : e'.backend.2.2.peer = e.backend.2.2.peer)
    (beacon : e'.backend.2.2.beacon = e.backend.2.2.beacon)
    (sessions : SessionMove e.native.shared.2 e'.native.shared.2)
    (terminal : terminalAt e.native.owners t.kem.val → terminalAt e'.native.owners t.kem.val)
    (used : w'.used = w.used) (seeds : w'.seeds.1 = w.seeds.1) : IdealInv t e' w' := by
  refine ⟨by rw [alloc]; exact holds.allocBound, by rw [alloc]; exact holds.allocBelow, fun le => ?_, fun j => ?_,
    fun j => ?_, fun s c found present => ?_, fun s c found => ?_, fun notTerminal => ?_, fun kid c found => ?_,
    fun j => ?_, by rw [alloc, cache]; exact holds.allocCached⟩
  · rw [marks, active, peer, beacon, alloc]
    exact holds.before (le_trans accepts le)
  · rw [used, peer, alloc]
    exact holds.serverMarks j
  · rw [used, beacon, alloc]
    exact holds.beaconMarks j
  · rw [marks] at found
    rw [peer]
    exact holds.pendingPeer s c found (sessions.2 s (holds.markedSession s c found).1 present)
  · rw [marks] at found
    rw [alloc]
    exact ⟨lt_of_lt_of_le (holds.markedSession s c found).1 sessions.1, (holds.markedSession s c found).2⟩
  · rw [beacon, alloc]
    exact holds.ownerOpen (fun wasTerminal => notTerminal (terminal wasTerminal))
  · rw [peer] at found
    rw [marks]
    exact holds.peerMarked kid c found
  · rw [used, seeds]
    exact holds.seeds j

/-- The admissibility predicate is kept by the selected accept: from the empty state before it, the accept counter passes the selected ordinal, the mark is at a session below the new counter with an allocated slot, at most one slot is allocated, nothing is installed, every allocated slot's material stays cached, and the World's used markers and seed table are unchanged. -/
theorem idealInv_selected (t : Target count) (e e' : EnvState KemSK SplitBk) (w w' : PqxdhRecordLiftWorld.State 2)
    (holds : IdealInv t e w) (selected : e.backend.2.2.accepts = t.accept)
    (move : SessionMove e.native.shared.2 e'.native.shared.2 ∧ AllocMove e.backend.2.1 e'.backend.2.1 ∧
        e'.backend.2.1.2 ≤ e.backend.2.1.2 + 1 ∧
        (∀ i c, e'.backend.2.2.marks = some (i, c) → i = e.native.shared.2.sessions ∧
          e.native.shared.2.sessions < e'.native.shared.2.sessions ∧
          ((e'.backend.2.1.1 c).isSome = true ∨ 2 ≤ e'.backend.2.1.2)) ∧
        e'.backend.2.2.accepts = e.backend.2.2.accepts + 1 ∧ e'.backend.2.2.peer = e.backend.2.2.peer ∧
        e'.backend.2.2.beacon = e.backend.2.2.beacon ∧ e'.native.owners = (strip e.native).owners ∧
        (AllocCached e.backend.2.1 e.backend.1 → AllocCached e'.backend.2.1 e'.backend.1))
    (used : w'.used = w.used) (seeds : w'.seeds.1 = w.seeds.1) : IdealInv t e' w' := by
  obtain ⟨_, alloc, counter, marked, accepts, peer, beacon, _, cached⟩ := move
  obtain ⟨_, _, noPeer, noBeacon, empty⟩ := holds.before (le_of_eq selected)
  have small : e'.backend.2.1.2 ≤ 1 := by omega
  have peer' : e'.backend.2.2.peer = none := peer.trans noPeer
  have beacon' : e'.backend.2.2.beacon = none := beacon.trans noBeacon
  refine ⟨by omega, alloc.below holds.allocBelow, fun le => absurd le (by omega), fun j => ?_, fun j => ?_,
    fun _ _ _ _ => peer', fun s c found => ?_, fun _ => ⟨beacon', small⟩,
    fun _ _ wrong => (by rw [peer'] at wrong; cases wrong), fun j => by rw [used, seeds]; exact holds.seeds j,
    cached holds.allocCached⟩
  · rw [used, peer']
    constructor
    · intro usedTrue
      obtain ⟨_, _, wrong, _⟩ := (holds.serverMarks j).mp usedTrue
      rw [noPeer] at wrong
      cases wrong
    · rintro ⟨_, _, wrong, _⟩
      cases wrong
  · rw [used, beacon']
    constructor
    · intro usedTrue
      obtain ⟨_, wrong, _⟩ := (holds.beaconMarks j).mp usedTrue
      rw [noBeacon] at wrong
      cases wrong
    · rintro ⟨_, wrong, _⟩
      cases wrong
  · obtain ⟨same, below, slotted⟩ := marked s c found
    exact ⟨by rw [same]; exact below, slotted.resolve_right (by omega)⟩

/-- The admissibility predicate is kept by the marked build of a session with a pending token, the material cache unchanged: the token is consumed, and either nothing is installed or the Server install ghost is at the marked coordinates, whose slot's World Server marker is set and whose seed is present. -/
theorem idealInv_build (t : Target count) (e e' : EnvState KemSK SplitBk) (w w' : PqxdhRecordLiftWorld.State 2)
    (holds : IdealInv t e w) (session : ℕ) (coords : Coord) (marked : e.backend.2.2.marks = some (session, coords))
    (j : PqxdhRecordLiftInterface.Slot 2) (allocated : e.backend.2.1.1 coords = some j)
    (noPeer : e.backend.2.2.peer = none) (cache : e'.backend.1 = e.backend.1)
    (move : SessionMove e.native.shared.2 e'.native.shared.2 ∧ e'.native.shared.2.pending session = none ∧
        e'.native.owners = (strip e.native).owners ∧ e'.backend.2.1 = e.backend.2.1 ∧
        e'.backend.2.2 = { e.backend.2.2 with peer := e'.backend.2.2.peer } ∧
        ((e'.backend.2.2.peer = e.backend.2.2.peer ∧ w'.used = w.used ∧ w'.seeds.1 = w.seeds.1) ∨
          (∃ key, e'.backend.2.2.peer = some (key, coords) ∧
            w'.used = Function.update w.used j (Function.update (w.used j) .server true) ∧
            (w'.seeds.1 j).isSome = true ∧ ∀ k, k ≠ j → w'.seeds.1 k = w.seeds.1 k))) :
    IdealInv t e' w' := by
  obtain ⟨sessions, consumed, owners, alloc, core, quiet | ⟨key, peer', used', seeded, other⟩⟩ := move
  · have accepts : e'.backend.2.2.accepts = e.backend.2.2.accepts := by rw [core]
    exact idealInv_move t e e' w w' holds cache alloc (le_of_eq accepts.symm) (by rw [core])
      (by rw [core]) quiet.1 (by rw [core]) sessions
      (fun terminal => by rw [owners, PqxdhDeploymentIdealEnvFacts.terminalAt_strip]; exact terminal) quiet.2.1 quiet.2.2
  · have accepts : e'.backend.2.2.accepts = e.backend.2.2.accepts := by rw [core]
    have marks : e'.backend.2.2.marks = e.backend.2.2.marks := by rw [core]
    have beacon : e'.backend.2.2.beacon = e.backend.2.2.beacon := by rw [core]
    have serverFalse : ∀ j', w.used j' .server = false := fun j' => by
      cases usedTrue : w.used j' .server
      · rfl
      · obtain ⟨_, _, wrong, _⟩ := (holds.serverMarks j').mp usedTrue
        rw [noPeer] at wrong
        cases wrong
    have usedServer : ∀ j', w'.used j' .server = true ↔ j' = j := fun j' => by
      rw [used']
      by_cases same : j' = j
      · subst same
        simp
      · simp [serverFalse j', same]
    have usedBeacon : ∀ j', w'.used j' .beacon = w.used j' .beacon := fun j' => by
      rw [used']
      by_cases same : j' = j
      · subst same
        simp
      · simp [Function.update_of_ne same]
    refine ⟨by rw [alloc]; exact holds.allocBound, by rw [alloc]; exact holds.allocBelow, fun le => ?_, fun j' => ?_,
      fun j' => ?_, fun s c found present => ?_, fun s c found => ?_, fun notTerminal => ?_, fun kid c found => ?_,
      fun j' => ?_, by rw [alloc, cache]; exact holds.allocCached⟩
    · rw [accepts] at le
      rw [(holds.before le).1] at marked
      cases marked
    · rw [usedServer, peer', alloc]
      constructor
      · rintro rfl
        exact ⟨key, coords, rfl, allocated⟩
      · rintro ⟨_, c, same, found⟩
        simp only [Option.some.injEq, Prod.mk.injEq] at same
        obtain ⟨_, rfl⟩ := same
        rw [allocated] at found
        cases found
        rfl
    · rw [usedBeacon, beacon, alloc]
      exact holds.beaconMarks j'
    · rw [marks, marked] at found
      simp only [Option.some.injEq, Prod.mk.injEq] at found
      obtain ⟨rfl, rfl⟩ := found
      rw [consumed] at present
      cases present
    · rw [marks] at found
      rw [alloc]
      exact ⟨lt_of_lt_of_le (holds.markedSession s c found).1 sessions.1, (holds.markedSession s c found).2⟩
    · rw [beacon, alloc]
      exact holds.ownerOpen (fun wasTerminal => notTerminal (by
        rw [owners, PqxdhDeploymentIdealEnvFacts.terminalAt_strip]; exact wasTerminal))
    · rw [peer'] at found
      simp only [Option.some.injEq, Prod.mk.injEq] at found
      obtain ⟨_, rfl⟩ := found
      exact ⟨session, by rw [marks, marked]⟩
    · by_cases same : j' = j
      · subst same
        rw [seeded, (usedServer j').2 rfl]
        simp
      · rw [other j' same, usedBeacon, show w'.used j' .server = w.used j' .server from by
          rw [serverFalse j']; cases h : w'.used j' .server
          · rfl
          · exact absurd ((usedServer j').1 h) same]
        exact holds.seeds j'

/-- The admissibility predicate is kept by owner k's challenge finish after an active selected accept: owner k ends terminal, the allocator moves by at most one slot, every allocated slot's material stays cached, and either nothing is installed or the Beacon install ghost is at coordinates with a slot whose World Beacon marker is set and whose seed is present. -/
theorem idealInv_finish (t : Target count) (e e' : EnvState KemSK SplitBk) (w w' : PqxdhRecordLiftWorld.State 2)
    (holds : IdealInv t e w) (active : e.backend.2.2.active = true)
    (initSent : initSentAt e.native.owners t.kem.val = true)
    (move : e'.native.shared.2.sessions = e.native.shared.2.sessions ∧
        e'.native.shared.2.pending = e.native.shared.2.pending ∧
        terminalAt e'.native.owners t.kem.val ∧
        AllocMove e.backend.2.1 e'.backend.2.1 ∧ e'.backend.2.1.2 ≤ e.backend.2.1.2 + 1 ∧
        e'.backend.2.2 = { e.backend.2.2 with beacon := e'.backend.2.2.beacon } ∧
        ((e'.backend.2.2.beacon = e.backend.2.2.beacon ∧ w'.used = w.used ∧ w'.seeds.1 = w.seeds.1) ∨
          (∃ c j, e'.backend.2.2.beacon = some c ∧ e'.backend.2.1.1 c = some j ∧
            w'.used = Function.update w.used j (Function.update (w.used j) .beacon true) ∧
            (w'.seeds.1 j).isSome = true ∧ ∀ k, k ≠ j → w'.seeds.1 k = w.seeds.1 k)) ∧
        (AllocCached e.backend.2.1 e.backend.1 → AllocCached e'.backend.2.1 e'.backend.1)) :
    IdealInv t e' w' := by
  obtain ⟨sessions, pending, terminal, alloc, counter, core, installed, cached⟩ := move
  obtain ⟨noBeacon, room, unused⟩ := idealInv_finish_ready t e w holds initSent
  have accepts : e'.backend.2.2.accepts = e.backend.2.2.accepts := by rw [core]
  have marks : e'.backend.2.2.marks = e.backend.2.2.marks := by rw [core]
  have peer : e'.backend.2.2.peer = e.backend.2.2.peer := by rw [core]
  have activeEq : e'.backend.2.2.active = e.backend.2.2.active := by rw [core]
  have peerSlot : ∀ kid c, e.backend.2.2.peer = some (kid, c) → ∃ j0, e.backend.2.1.1 c = some j0 := fun kid c found => by
    obtain ⟨s, markedS⟩ := holds.peerMarked kid c found
    exact Option.isSome_iff_exists.mp (holds.markedSession s c markedS).2
  have usedServer : ∀ j', w'.used j' .server = w.used j' .server := fun j' => by
    rcases installed with ⟨_, same, _⟩ | ⟨_, j, _, _, used', _, _⟩
    · rw [same]
    · rw [used']
      by_cases at_ : j' = j
      · subst at_
        simp
      · simp [Function.update_of_ne at_]
  have serverIff : ∀ j', (∃ kid c, e'.backend.2.2.peer = some (kid, c) ∧ e'.backend.2.1.1 c = some j') ↔
      (∃ kid c, e.backend.2.2.peer = some (kid, c) ∧ e.backend.2.1.1 c = some j') := fun j' => by
    rw [peer]
    constructor
    · rintro ⟨kid, c, found, slotted⟩
      obtain ⟨j0, old⟩ := peerSlot kid c found
      rw [alloc.keeps c j0 old] at slotted
      cases slotted
      exact ⟨kid, c, found, old⟩
    · rintro ⟨kid, c, found, slotted⟩
      exact ⟨kid, c, found, alloc.keeps c j' slotted⟩
  refine ⟨by omega, alloc.below holds.allocBelow, fun le => ?_, fun j' => ?_, fun j' => ?_,
    fun s c found present => ?_, fun s c found => ?_, fun notTerminal => absurd terminal notTerminal,
    fun kid c found => ?_, fun j' => ?_, cached holds.allocCached⟩
  · rw [accepts] at le
    rw [(holds.before le).2.1] at active
    cases active
  · rw [usedServer, serverIff]
    exact holds.serverMarks j'
  · rcases installed with ⟨same, used', _⟩ | ⟨c, j, beacon', slotted, used', _, _⟩
    · rw [used', same, noBeacon]
      constructor
      · intro usedTrue
        obtain ⟨_, wrong, _⟩ := (holds.beaconMarks j').mp usedTrue
        rw [noBeacon] at wrong
        cases wrong
      · rintro ⟨_, wrong, _⟩
        cases wrong
    · rw [used', beacon']
      have beaconFalse : w.used j' .beacon = false := unused j'
      by_cases at_ : j' = j
      · subst at_
        simp only [Function.update_self, true_iff]
        exact ⟨c, rfl, slotted⟩
      · simp only [Function.update_of_ne at_, beaconFalse, Bool.false_eq_true, false_iff]
        rintro ⟨c', same, found⟩
        cases same
        rw [slotted] at found
        cases found
        exact at_ rfl
  · rw [marks] at found
    rw [peer]
    rw [pending] at present
    exact holds.pendingPeer s c found present
  · rw [marks] at found
    obtain ⟨below, slotted⟩ := holds.markedSession s c found
    obtain ⟨j0, old⟩ := Option.isSome_iff_exists.mp slotted
    exact ⟨by rw [sessions]; exact below, by rw [alloc.keeps c j0 old]; rfl⟩
  · rw [peer] at found
    rw [marks]
    exact holds.peerMarked kid c found
  · rcases installed with ⟨_, used', seeds'⟩ | ⟨c, j, _, _, used', seeded, other⟩
    · rw [used', seeds']
      exact holds.seeds j'
    · by_cases at_ : j' = j
      · subst at_
        rw [seeded, used']
        simp
      · rw [other j' at_, used']
        simp only [Function.update_of_ne at_]
        exact holds.seeds j'

end Preservation

/-! ### The ideal environment splits the final split form -/

section Splits
variable {ι : Type} {baseSpec : OracleSpec ι} {Reader Response : Type}
  (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
  (checks : Checks) {count : ℕ}
open PqxdhDeploymentIdealEnvFacts (world_support run_keep realStep_move realStep_free createPool_move createPool_free
  acceptSelected_move acceptSelected_free buildHidden_move finishChallenge_move)
open PqxdhDeploymentIdealEnvStep (bump)

/-- The selected raw accept of the ideal step. -/
theorem idealStep_selected (t : Target count) (p : Params KemSK count) (raw : Pqxdh.Bytes)
    (allowed : PqxdhRecordLiftInterface.IsEnvironment (.accept raw)) (e : EnvState KemSK SplitBk)
    (selected : e.backend.2.2.accepts = t.accept) :
    (idealStep setup codec checks t p ⟨.accept raw, allowed⟩).run e =
      (PqxdhDeploymentIdealEnvStep.acceptSelectedEnv setup codec checks p raw).run e := by
  change (if e.backend.2.2.accepts = t.accept then _ else _) = _
  rw [ite_eq_left_of_eq_true _ _ (eq_true selected)]

/-- Every other raw accept of the ideal step: the real accept with the accept counter advanced. -/
theorem idealStep_accept_other (t : Target count) (p : Params KemSK count) (raw : Pqxdh.Bytes)
    (allowed : PqxdhRecordLiftInterface.IsEnvironment (.accept raw)) (e : EnvState KemSK SplitBk)
    (other : e.backend.2.2.accepts ≠ t.accept) :
    (idealStep setup codec checks t p ⟨.accept raw, allowed⟩).run e =
      (PqxdhDeploymentEnvironment.realStep setup codec checks ⟨.accept raw, allowed⟩).run
        { e with backend := bump e.backend } := by
  change (if e.backend.2.2.accepts = t.accept then _ else _) = _
  rw [ite_eq_right_of_eq_false _ _ (eq_false other)]

/-- The build of the ideal step: the marked build of the marked session while it has a pending token (reading its slot's cached material), the real build otherwise. -/
theorem idealStep_build (t : Target count) (p : Params KemSK count) (session : ℕ) (payload : Option Pqxdh.Bytes)
    (allowed : PqxdhRecordLiftInterface.IsEnvironment (.build session payload)) (e : EnvState KemSK SplitBk) :
    (∃ coords, e.backend.2.2.marks = some (session, coords) ∧ (e.native.shared.2.pending session).isSome = true ∧
      (idealStep setup codec checks t p ⟨.build session payload, allowed⟩).run e =
        (buildCachedEnv setup codec checks session payload coords).run e) ∨
    ((∀ index coords, e.backend.2.2.marks = some (index, coords) →
        ¬ (index = session ∧ (e.native.shared.2.pending session).isSome)) ∧
      (idealStep setup codec checks t p ⟨.build session payload, allowed⟩).run e =
        (PqxdhDeploymentEnvironment.realStep setup codec checks ⟨.build session payload, allowed⟩).run e) := by
  change (∃ coords, _ ∧ _ ∧ (match e.backend.2.2.marks with
      | some (index, coords) =>
          if index = session ∧ (e.native.shared.2.pending session).isSome then
            (buildCachedEnv setup codec checks session payload coords).run e
          else (PqxdhDeploymentEnvironment.realStep setup codec checks ⟨.build session payload, allowed⟩).run e
      | none => (PqxdhDeploymentEnvironment.realStep setup codec checks ⟨.build session payload, allowed⟩).run e) = _) ∨
    (_ ∧ (match e.backend.2.2.marks with
      | some (index, coords) =>
          if index = session ∧ (e.native.shared.2.pending session).isSome then
            (buildCachedEnv setup codec checks session payload coords).run e
          else (PqxdhDeploymentEnvironment.realStep setup codec checks ⟨.build session payload, allowed⟩).run e
      | none => (PqxdhDeploymentEnvironment.realStep setup codec checks ⟨.build session payload, allowed⟩).run e) = _)
  rcases marked : e.backend.2.2.marks with _ | ⟨index, coords⟩
  · exact Or.inr ⟨fun _ _ wrong => (by cases wrong), rfl⟩
  · by_cases chosen : index = session ∧ (e.native.shared.2.pending session).isSome = true
    · obtain ⟨rfl, pending⟩ := chosen
      exact Or.inl ⟨coords, rfl, pending, ite_eq_left_of_eq_true _ _ (eq_true ⟨rfl, pending⟩)⟩
    · refine Or.inr ⟨fun i c same => ?_, ite_eq_right_of_eq_false _ _ (eq_false chosen)⟩
      simp only [Option.some.injEq, Prod.mk.injEq] at same
      obtain ⟨rfl, rfl⟩ := same
      exact chosen

/-- At an allocated slot whose material is cached, the marked build reading the cached material is the marked build reading it lazily (`PqxdhDeploymentIdealEnvBuild.buildHiddenEnv`), whose lazy read is then a cache hit. -/
theorem buildCached_hit (session : ℕ) (payload : Option Pqxdh.Bytes) (coords : Coord) (e : EnvState KemSK SplitBk)
    (j : PqxdhRecordLiftInterface.Slot 2) (material : PqxdhDeploymentHiddenLayout.Material)
    (allocated : e.backend.2.1.1 coords = some j) (cached : e.backend.1 j = some material) :
    (buildCachedEnv setup codec checks session payload coords).run e =
      (PqxdhDeploymentIdealEnvBuild.buildHiddenEnv setup codec checks session payload coords).run e := by
  change buildCachedEnv setup codec checks session payload coords e =
    PqxdhDeploymentIdealEnvBuild.buildHiddenEnv setup codec checks session payload coords e
  unfold buildCachedEnv PqxdhDeploymentIdealEnvBuild.buildHiddenEnv
  rw [allocated]
  cases e.native.shared.2.pending session with
  | none => rfl
  | some token =>
      dsimp only
      rw [cached, LazyOracleDiscard.query_of_some cached]
      simp only [PqxdhDeploymentEnvironment.coins, simulateQ_pure, pure_bind]

/-- The marked build reading the cached material leaves the material cache unchanged. -/
theorem buildCached_cache (session : ℕ) (payload : Option Pqxdh.Bytes) (coords : Coord) (e : EnvState KemSK SplitBk) :
    ∀ v ∈ support ((buildCachedEnv setup codec checks session payload coords).run e), v.2.backend.1 = e.backend.1 := by
  intro v member
  change v ∈ support (buildCachedEnv setup codec checks session payload coords e) at member
  unfold buildCachedEnv at member
  split at member
  · split at member
    · rw [mem_support_bind_iff] at member
      obtain ⟨_, _, final⟩ := member
      rw [support_pure, Set.mem_singleton_iff] at final
      subst final
      rfl
    · rw [support_pure, Set.mem_singleton_iff] at member
      subst member
      rfl
  · rw [support_pure, Set.mem_singleton_iff] at member
    subst member
    rfl

/-- The marked build reading the cached material stays within the real allowance of the build class at every environment state: no coin, at most one BLAKE2b query (its sequence-one seal) and at most one administrative effect (the hidden Server install), from `PqxdhDeploymentEnvironment.buildSplit_env_cost`. -/
theorem buildCached_bound (caps : PqxdhServerAuthSourceCosts.KemCaps) (session : ℕ) (payload : Option Pqxdh.Bytes)
    (coords : Coord) (e : EnvState KemSK SplitBk) (kind : EffectKind) :
    ((buildCachedEnv setup codec checks session payload coords).run e).IsQueryBoundP
      (fun effect => effectKind effect = kind) (PqxdhDeploymentEnvironment.baseAllowance caps 4 kind) := by
  change IsQueryBoundP (buildCachedEnv setup codec checks session payload coords e) _ _
  unfold buildCachedEnv
  split
  · split
    · apply (isQueryBoundP_bind (m := 0) (PqxdhDeploymentEnvironment.buildSplit_env_cost setup codec checks _ _ _ payload
        _ [] kind) fun _ _ => isQueryBoundP_pure _ _ _).mono
      cases kind <;> simp [PqxdhDeploymentEnvironment.baseAllowance]
    · trivial
  · trivial

/-- The build class of the ideal step at every environment state stays within the first-touch allowance of plan sections 31, 33 and 35 (`PqxdhDeploymentEnvironment.allowanceG` of the real allowance with the first-touch classes `ceFirstTouch`, accept and finish), whose build class has no coin: the marked build reads its slot's cached material (`buildCached_bound`) and every other build is the real build (`PqxdhDeploymentEnvironment.buildStep_bound`). This is the build-class part of the frame `frame_idealD`; the other classes are not proved here. -/
theorem idealStep_build_bound (caps : PqxdhServerAuthSourceCosts.KemCaps) (t : Target count) (p : Params KemSK count)
    (session : ℕ) (payload : Option Pqxdh.Bytes) (allowed : PqxdhRecordLiftInterface.IsEnvironment (.build session payload))
    (e : EnvState KemSK SplitBk) (kind : EffectKind) :
    ((idealStep setup codec checks t p ⟨.build session payload, allowed⟩).run e).IsQueryBoundP
      (fun effect => effectKind effect = kind)
      (PqxdhDeploymentEnvironment.allowanceG (PqxdhDeploymentEnvironment.baseAllowance caps)
        PqxdhDeploymentEnvironment.ceFirstTouch
        (PqxdhDeploymentInterface.queryClass (.inl (.inr (.build session payload)))) kind) := by
  have base : ((idealStep setup codec checks t p ⟨.build session payload, allowed⟩).run e).IsQueryBoundP
      (fun effect => effectKind effect = kind) (PqxdhDeploymentEnvironment.baseAllowance caps 4 kind) := by
    rcases idealStep_build setup codec checks t p session payload allowed e with ⟨_, _, _, run⟩ | ⟨_, run⟩
    · rw [run]
      exact buildCached_bound setup codec checks caps session payload _ e kind
    · rw [run]
      exact PqxdhDeploymentEnvironment.buildStep_bound setup codec checks caps session payload _ kind
  exact base.mono (Nat.le_add_right _ _)

/-- Owner k's challenge finish of the ideal step after an active selected accept. -/
theorem idealStep_challenge (t : Target count) (p : Params KemSK count) (owner : ℕ) (raw : Pqxdh.Bytes)
    (allowed : PqxdhRecordLiftInterface.IsEnvironment (.finish owner raw)) (e : EnvState KemSK SplitBk)
    (chosen : e.backend.2.2.active = true ∧ owner = t.kem.val ∧ initSentAt e.native.owners owner = true) :
    (idealStep setup codec checks t p ⟨.finish owner raw, allowed⟩).run e =
      (PqxdhDeploymentIdealEnvFinish.finishChallengeEnv setup codec p owner raw).run e := by
  change (if e.backend.2.2.active = true ∧ owner = t.kem.val ∧ initSentAt e.native.owners owner = true then _ else _) = _
  rw [ite_eq_left_of_eq_true _ _ (eq_true chosen)]

/-- Every other finish of the ideal step: the real finish. -/
theorem idealStep_finish_real (t : Target count) (p : Params KemSK count) (owner : ℕ) (raw : Pqxdh.Bytes)
    (allowed : PqxdhRecordLiftInterface.IsEnvironment (.finish owner raw)) (e : EnvState KemSK SplitBk)
    (real : ¬ (e.backend.2.2.active = true ∧ owner = t.kem.val ∧ initSentAt e.native.owners owner = true)) :
    (idealStep setup codec checks t p ⟨.finish owner raw, allowed⟩).run e =
      (PqxdhDeploymentEnvironment.realStep setup codec checks ⟨.finish owner raw, allowed⟩).run e := by
  change (if e.backend.2.2.active = true ∧ owner = t.kem.val ∧ initSentAt e.native.owners owner = true then _ else _) = _
  rw [ite_eq_right_of_eq_false _ _ (eq_false real)]

/-- A real environment step keeps the ideal admissibility predicate. -/
theorem idealInv_realStep (t : Target count) (query : PqxdhRecordLiftInterface.EnvQuery) (e : EnvState KemSK SplitBk)
    (w : PqxdhRecordLiftWorld.State 2) (holds : IdealInv t e w) :
    ∀ result ∈ support ((simulateQ PqxdhRecordLiftWorld.effects
        ((PqxdhDeploymentEnvironment.realStep (n := 2) setup codec checks query).run e)).run w),
      IdealInv t result.1.2 result.2 := by
  intro result member
  have move := world_support _ w _ (realStep_move setup codec checks t.kem.val query e) result member
  obtain ⟨used, seeds⟩ := run_keep _ (realStep_free setup codec checks query e) w result member
  exact idealInv_move t e _ w _ holds (by rw [move.backend]) (by rw [move.backend]) (by rw [move.backend])
    (by rw [move.backend]) (by rw [move.backend]) (by rw [move.backend]) (by rw [move.backend]) move.sessions
    move.terminal used (congrArg Prod.fst seeds)

/-- The ideal environment's step splits the final split form `PqxdhDeploymentIdealDefer.idealSplit t p` relative to the ideal admissibility predicate (design-v2 section 6.2): every command, interpreted by the World's effects from an admissible joint state, has the law of the split form on the reassembled state and keeps `Good` and `IdealInv`. -/
theorem ideal_splits (t : Target count) (p : Params KemSK count) (created : PqxdhLiveServerConstruction.Created Unit) :
    Splits created (PqxdhDeploymentIdealDefer.idealSplit setup codec route checks t p created)
      (idealStep setup codec checks t p) (IdealInv t) := by
  intro query e w good holds
  rcases query with ⟨command, allowed⟩
  cases command with
  | create pin keyId =>
      obtain ⟨law, keeps⟩ := PqxdhDeploymentIdealEnvStep.create_splits setup codec route checks t p created pin keyId e w
        good
      refine ⟨law, fun result member => ⟨keeps result member, ?_⟩⟩
      have move := world_support _ w _ (createPool_move setup t.kem.val (p.pool t) pin keyId e) result member
      obtain ⟨used, seeds⟩ := run_keep _ (createPool_free setup (p.pool t) pin keyId e) w result member
      exact idealInv_move t e _ w _ holds (by rw [move.backend]) (by rw [move.backend]) (by rw [move.backend])
        (by rw [move.backend]) (by rw [move.backend]) (by rw [move.backend]) (by rw [move.backend]) move.sessions
        move.terminal used (congrArg Prod.fst seeds)
  | bundle owner =>
      obtain ⟨law, keeps⟩ := PqxdhDeploymentIdealEnvStep.bundle_splits setup codec route checks t p created owner e w good
      exact ⟨law, fun result member => ⟨keeps result member,
        idealInv_realStep setup codec checks t ⟨.bundle owner, trivial⟩ e w holds result member⟩⟩
  | accept raw =>
      by_cases selected : e.backend.2.2.accepts = t.accept
      · rw [idealStep_selected setup codec checks t p raw allowed e selected]
        obtain ⟨law, keeps⟩ := PqxdhDeploymentIdealEnvStep.accept_selected_splits setup codec route checks t p created
          raw e w good selected
        refine ⟨law, fun result member => ⟨keeps result member, ?_⟩⟩
        have move := world_support _ w _ (acceptSelected_move setup codec checks p raw e) result member
        obtain ⟨used, seeds⟩ := run_keep _ (acceptSelected_free setup codec checks p raw e) w result member
        exact idealInv_selected t e _ w _ holds selected move used (congrArg Prod.fst seeds)
      · rw [idealStep_accept_other setup codec checks t p raw allowed e selected]
        obtain ⟨law, keeps⟩ := PqxdhDeploymentIdealEnvStep.accept_other_splits setup codec route checks t p created raw e
          w good selected
        refine ⟨law, fun result member => ⟨keeps result member, ?_⟩⟩
        have move := world_support _ w _ (realStep_move setup codec checks t.kem.val ⟨.accept raw, trivial⟩
          { e with backend := bump e.backend }) result member
        obtain ⟨used, seeds⟩ := run_keep _ (realStep_free setup codec checks ⟨.accept raw, trivial⟩
          { e with backend := bump e.backend }) w result member
        exact idealInv_move t e _ w _ holds (by rw [move.backend]; rfl) (by rw [move.backend]; rfl)
          (by rw [move.backend]; exact Nat.le_succ _)
          (by rw [move.backend]; rfl) (by rw [move.backend]; rfl) (by rw [move.backend]; rfl) (by rw [move.backend]; rfl)
          move.sessions move.terminal used (congrArg Prod.fst seeds)
  | build session payload =>
      rcases idealStep_build setup codec checks t p session payload allowed e with
        ⟨coords, marked, pendingSome, run⟩ | ⟨real, run⟩
      · obtain ⟨noPeer, j, allocated, unused, cachedSome⟩ := idealInv_build_ready t e w holds session coords marked
          pendingSome
        obtain ⟨token, pending⟩ := Option.isSome_iff_exists.mp pendingSome
        obtain ⟨material, cached⟩ := Option.isSome_iff_exists.mp cachedSome
        have cache := world_support _ w _ (buildCached_cache setup codec checks session payload coords e)
        rw [buildCached_hit setup codec checks session payload coords e j material allocated cached] at cache
        rw [run, buildCached_hit setup codec checks session payload coords e j material allocated cached]
        refine ⟨LazyOracleDiscard.LawEq.of_eq (PqxdhDeploymentIdealEnvBuild.buildHidden_law setup codec route checks t p
          created session payload e w good coords j token marked pending allocated unused), fun result member =>
            ⟨PqxdhDeploymentIdealEnvBuild.buildHidden_keeps setup codec checks created session payload coords e w good j
              token allocated pending unused result member, ?_⟩⟩
        exact idealInv_build t e _ w _ holds session coords marked j allocated noPeer (cache result member)
          (buildHidden_move setup codec checks created session payload coords e w good j token allocated pending unused
            result member)
      · rw [run]
        obtain ⟨law, keeps⟩ := PqxdhDeploymentIdealEnvStep.build_real_splits setup codec route checks t p created session
          payload e w good real
        exact ⟨law, fun result member => ⟨keeps result member,
          idealInv_realStep setup codec checks t ⟨.build session payload, trivial⟩ e w holds result member⟩⟩
  | finish owner raw =>
      by_cases chosen : e.backend.2.2.active = true ∧ owner = t.kem.val ∧ initSentAt e.native.owners owner = true
      · rw [idealStep_challenge setup codec checks t p owner raw allowed e chosen]
        obtain ⟨activeEq, rfl, initSent⟩ := chosen
        obtain ⟨_, room, unused⟩ := idealInv_finish_ready t e w holds initSent
        obtain ⟨law, keeps⟩ := PqxdhDeploymentIdealEnvFinish.finishChallenge_splits setup codec route checks t p created
          t.kem.val raw e w good ⟨activeEq, rfl, initSent⟩ room unused
        refine ⟨law, fun result member => ⟨keeps result member, ?_⟩⟩
        exact idealInv_finish t e _ w _ holds activeEq initSent
          (finishChallenge_move setup codec created p t.kem.val raw e w good initSent unused result member)
      · rw [idealStep_finish_real setup codec checks t p owner raw allowed e chosen]
        obtain ⟨law, keeps⟩ := PqxdhDeploymentIdealEnvStep.finish_real_splits setup codec route checks t p created owner
          raw e w good chosen
        exact ⟨law, fun result member => ⟨keeps result member,
          idealInv_realStep setup codec checks t ⟨.finish owner raw, trivial⟩ e w holds result member⟩⟩
  | hmac key message =>
      obtain ⟨law, keeps⟩ := PqxdhDeploymentIdealEnvStep.hmac_splits setup codec route checks t p created key message e
        w good
      exact ⟨law, fun result member => ⟨keeps result member,
        idealInv_realStep setup codec checks t ⟨.hmac key message, trivial⟩ e w holds result member⟩⟩
  | hash _ => exact absurd allowed id
  | serverSend _ _ => exact absurd allowed id
  | serverRaw _ => exact absurd allowed id
  | beaconSend _ _ => exact absurd allowed id
  | beaconRaw _ _ => exact absurd allowed id

end Splits

/-! ### The ideal environments and C1 -/

section Environments
variable {ι : Type} {baseSpec : OracleSpec ι} {Reader Response A X : Type}
  (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
  (checks : Checks) {count : ℕ}
open PqxdhDeploymentIdealParams (drawParams)
open PqxdhDeploymentIdealSteps (idealInit idealReg)
open PqxdhDeploymentBackend (gameWith)
open PqxdhDeploymentEnvironmentJoin (joined)
open PqxdhDeploymentEnvironmentDraw (paramEnv withX)
open LazyOracleDiscard (LawEq)

/-- The ideal environment at fixed parameters (design-v2 section 6.1): the actual Server constructor with the split form's initial backend `splitInit`, and the ideal step. -/
noncomputable def envG (t : Target count) (p : Params KemSK count) (ensureInit : StateT A ProbComp Bool)
    (identityIndex : ℕ) (runtime : A) : PqxdhRecordLiftInterface.Environment 2 (EnvState KemSK SplitBk) :=
  ⟨PqxdhDeploymentEnvironment.start setup ensureInit identityIndex runtime splitInit, idealStep setup codec checks t p⟩

/-- The ideal environment of a target (design-v2 sections 6.1 and 21): the challenger's parameters drawn at startup (`drawParams`, startup coins) and kept in the backend (`PqxdhDeploymentEnvironmentDraw.paramEnv`), then the actual Server constructor with `splitInit`; its step is the ideal step at the drawn parameters. -/
noncomputable def envGD (t : Target count) (ensureInit : StateT A ProbComp Bool) (identityIndex : ℕ) (runtime : A) :
    PqxdhRecordLiftInterface.Environment 2 (EnvState KemSK (Params KemSK count × SplitBk)) :=
  paramEnv setup (drawParams setup count) (idealStep setup codec checks t) ensureInit identityIndex runtime splitInit

/-- C1 for the ideal environment at the full reassembled state (`PqxdhDeploymentEnvironmentDraw.join_param` with `ideal_splits`): the draw of the challenger's parameters followed by the final split game at them (the parameters added to the final backend) and the record world with `envGD` have the same law of the Server's public data, the adversary's output, the ledger and the full reassembled final state. -/
theorem c1_split (t : Target count) (ensureInit : StateT A ProbComp Bool) (identityIndex : ℕ) (runtime : A)
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (adversary : OracleComp (PqxdhDeploymentInterface.ModeSpec mode) X) :
    LawEq (drawParams setup count >>= fun p => (fun outcome => outcome.map fun value => (value.1, value.2.1, value.2.2.1,
        withX p value.2.2.2)) <$>
        (gameWith setup codec route splitInit (PqxdhDeploymentIdealDefer.idealSplit setup codec route checks t p)
          ensureInit identityIndex bounds mode adversary).run' runtime)
      (joined <$> PqxdhRecordLiftWorld.run setup codec route (envGD setup codec checks t ensureInit identityIndex runtime)
        setup.serverKeyId bounds mode adversary) :=
  PqxdhDeploymentEnvironmentDraw.join_param setup codec route (drawParams setup count) splitInit
    (fun p => PqxdhDeploymentIdealDefer.idealSplit setup codec route checks t p) (idealStep setup codec checks t)
    ensureInit identityIndex runtime (fun _ => IdealInv t) (fun _ => idealInv_stable t)
    (fun _ created => idealInv_start t created) (fun p created => ideal_splits setup codec route checks t p created)
    bounds mode adversary

/-- C1 for the ideal environment (design-v2 section 6.3, `c1_ideal`): the draw of the challenger's parameters followed by the ideal game at them (`PqxdhDeploymentIdealSteps.idealReg` with `idealInit`) and the record world with `envGD` have the same law of the adversary's output, the ledger and the produced frames (the observed projection), through `PqxdhDeploymentIdealDefer.ideal_to_split` pointwise under the draw and `c1_split`. -/
theorem c1_ideal (t : Target count) (ensureInit : StateT A ProbComp Bool) (identityIndex : ℕ) (runtime : A)
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (adversary : OracleComp (PqxdhDeploymentInterface.ModeSpec mode) X) :
    LawEq (drawParams setup count >>= fun p => (fun outcome => outcome.map fun value =>
        (value.2.1, value.2.2.1, value.2.2.2.base.produced)) <$>
        (gameWith setup codec route idealInit (idealReg setup codec route checks t p) ensureInit identityIndex bounds mode
          adversary).run' runtime)
      ((fun outcome => outcome.map fun value => (value.2.1, value.2.2.1, value.2.2.2.base.produced)) <$>
        (joined <$> PqxdhRecordLiftWorld.run setup codec route (envGD setup codec checks t ensureInit identityIndex runtime)
          setup.serverKeyId bounds mode adversary)) := by
  have pointwise : ∀ p : Params KemSK count,
      LawEq ((fun outcome => outcome.map fun value => (value.2.1, value.2.2.1, value.2.2.2.base.produced)) <$>
          (gameWith setup codec route idealInit (idealReg setup codec route checks t p) ensureInit identityIndex bounds mode
            adversary).run' runtime)
        ((fun outcome => outcome.map fun value => (value.2.1, value.2.2.1, value.2.2.2.base.produced)) <$>
          (gameWith setup codec route splitInit (PqxdhDeploymentIdealDefer.idealSplit setup codec route checks t p)
            ensureInit identityIndex bounds mode adversary).run' runtime) := by
    intro p
    have viewed := (PqxdhDeploymentIdealDefer.ideal_to_split setup codec route checks t p ensureInit identityIndex bounds
      mode adversary runtime).map (fun outcome => outcome.1.map fun value => (value.2.1, value.2.2.1,
        value.2.2.2.1.produced))
    simp only [Functor.map_map, StateT.run'_eq] at viewed ⊢
    refine (LawEq.of_eq ?_).trans (viewed.trans (LawEq.of_eq ?_))
    · congr 1
      funext a
      rcases a with ⟨_ | v, after⟩ <;> rfl
    · congr 1
      funext a
      rcases a with ⟨_ | v, after⟩ <;> rfl
  have joinedLaw := (c1_split setup codec route checks t ensureInit identityIndex runtime bounds mode adversary).map
    (fun outcome => outcome.map fun value => (value.2.1, value.2.2.1, value.2.2.2.base.produced))
  rw [map_bind] at joinedLaw
  simp only [Functor.map_map] at joinedLaw
  refine (LawEq.bind (LawEq.refl _) pointwise).trans ?_
  simp only [Functor.map_map]
  refine (LawEq.of_eq ?_).trans joinedLaw
  refine bind_congr fun p => ?_
  congr 1
  funext outcome
  rcases outcome with _ | value <;> rfl

/-- C1 for CE's ideal game itself (`PqxdhDeploymentIdealSteps.idealGame`, its draw included) at the observed projection: it has the law of the record world with `envGD` at the target of `g`. -/
theorem c1_idealGame (budget : PqxdhDeploymentInterface.Budget) (g : Fin budget.accept × Fin budget.capacity)
    (ensureInit : StateT A ProbComp Bool) (runtime : A) (bounds : PqxdhDeploymentInterface.FreshBounds)
    (mode : PqxdhDeploymentInterface.Mode) (adversary : OracleComp (PqxdhDeploymentInterface.ModeSpec mode) X) :
    LawEq ((fun outcome => outcome.map fun value => (value.2.1, value.2.2.1, value.2.2.2.base.produced)) <$>
        (PqxdhDeploymentIdealSteps.idealGame setup codec route checks budget g ensureInit bounds mode adversary).run'
          runtime)
      ((fun outcome => outcome.map fun value => (value.2.1, value.2.2.1, value.2.2.2.base.produced)) <$>
        (joined <$> PqxdhRecordLiftWorld.run setup codec route
          (envGD setup codec checks (Target.ofCE budget g) ensureInit 0 runtime) setup.serverKeyId bounds mode
            adversary)) := by
  refine (LawEq.of_eq ?_).trans (c1_ideal setup codec route checks (Target.ofCE budget g) ensureInit 0 runtime bounds
    mode adversary)
  simp only [PqxdhDeploymentIdealSteps.idealGame, StateT.run'_eq, StateT.run, map_bind, Functor.map_map]

/-- C3 for the ideal environment (design-v2 section 6.3, `c3_ideal`, a map of `c1_split`): the draw followed by the final split game and the record world with `envGD` have the same law of the Server's public data, the adversary's output, the ledger and the final CTX cache, the World's cache on the record side. -/
theorem c3_ideal (t : Target count) (ensureInit : StateT A ProbComp Bool) (identityIndex : ℕ) (runtime : A)
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (adversary : OracleComp (PqxdhDeploymentInterface.ModeSpec mode) X) :
    LawEq (drawParams setup count >>= fun p => (fun outcome => outcome.map fun value => (value.1, value.2.1, value.2.2.1,
        value.2.2.2.base.native.shared.2.ctx)) <$>
        (gameWith setup codec route splitInit (PqxdhDeploymentIdealDefer.idealSplit setup codec route checks t p)
          ensureInit identityIndex bounds mode adversary).run' runtime)
      ((fun result => result.1.map fun value => (value.1, value.2.1.1, value.2.1.2, result.2.primitive.2)) <$>
        PqxdhRecordLiftWorld.run setup codec route (envGD setup codec checks t ensureInit identityIndex runtime)
          setup.serverKeyId bounds mode adversary) := by
  have projected := (c1_split setup codec route checks t ensureInit identityIndex runtime bounds mode adversary).map
    (fun outcome => outcome.map fun value => (value.1, value.2.1, value.2.2.1, value.2.2.2.base.native.shared.2.ctx))
  rw [map_bind, Functor.map_map] at projected
  simp only [Functor.map_map] at projected
  refine (LawEq.of_eq ?_).trans (projected.trans (LawEq.of_eq ?_))
  · refine bind_congr fun p => ?_
    congr 1
    funext outcome
    rcases outcome with _ | value <;> rfl
  · congr 1
    funext result
    rcases result with ⟨_ | value, w⟩ <;> rfl

/-- The reveal projection for the ideal environment (a map of `c1_split`): the draw followed by the final split game and the record world with `envGD` have the same law of the Server's public data, the adversary's output, the ledger, and the reveal (owners' revealed scalars at the LQ-F snapshot) with the Server ephemeral log; the record side reads them from the environment state. -/
theorem ideal_reveal (t : Target count) (ensureInit : StateT A ProbComp Bool) (identityIndex : ℕ) (runtime : A)
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (adversary : OracleComp (PqxdhDeploymentInterface.ModeSpec mode) X) :
    LawEq (drawParams setup count >>= fun p => (fun outcome => outcome.map fun value => (value.1, value.2.1, value.2.2.1,
        (PqxdhDeploymentLater.revealOf value.2.2.2.base.native.owners value.2.2.2.snap, value.2.2.2.log))) <$>
        (gameWith setup codec route splitInit (PqxdhDeploymentIdealDefer.idealSplit setup codec route checks t p)
          ensureInit identityIndex bounds mode adversary).run' runtime)
      ((fun result => result.1.map fun value => (value.1, value.2.1.1, value.2.1.2,
          (PqxdhDeploymentLater.revealOf value.2.2.native.owners value.2.2.snap, value.2.2.log))) <$>
        PqxdhRecordLiftWorld.run setup codec route (envGD setup codec checks t ensureInit identityIndex runtime)
          setup.serverKeyId bounds mode adversary) := by
  have projected := (c1_split setup codec route checks t ensureInit identityIndex runtime bounds mode adversary).map
    (fun outcome => outcome.map fun value => (value.1, value.2.1, value.2.2.1,
      (PqxdhDeploymentLater.revealOf value.2.2.2.base.native.owners value.2.2.2.snap, value.2.2.2.log)))
  rw [map_bind, Functor.map_map] at projected
  simp only [Functor.map_map] at projected
  refine (LawEq.of_eq ?_).trans (projected.trans (LawEq.of_eq ?_))
  · refine bind_congr fun p => ?_
    congr 1
    funext outcome
    rcases outcome with _ | value <;> rfl
  · congr 1
    funext result
    rcases result with ⟨_ | value, w⟩
    · rfl
    · simp only [joined, Option.map_some, Option.some.injEq]
      rw [show (PqxdhDeploymentEnvironmentJoin.merge value.2.2 w).base.native.owners =
        (PqxdhDeploymentEnvironmentJoin.fill w value.2.2.native).owners from rfl,
        PqxdhDeploymentEnvironmentJoin.revealOf_fill]
      rfl

end Environments

/-! ### Admissibility on every outcome of the record world -/

section Outcomes
variable {ι : Type} {baseSpec : OracleSpec ι} {Reader Response A X : Type}
  (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
  (checks : Checks) {count : ℕ}
open PqxdhDeploymentEnvironmentDraw (paramInv paramStep paramReg dropE)

/-- Every outcome of the record world with an environment whose every startup outcome is a constructed Server with an initial environment state at which the stable predicate `inv` holds with the initialized fresh World, and whose step splits every constructed Server's registration handler relative to `inv`: the final environment state and World are admissible (`Good` and `inv`). -/
theorem world_keeps {Bk : Type} (env : PqxdhRecordLiftInterface.Environment 2 (EnvState KemSK Bk))
    (reg : PqxdhLiveServerConstruction.Created Unit → PqxdhDeploymentBackend.RegImpl KemSK Bk 2)
    (inv : EnvState KemSK Bk → PqxdhRecordLiftWorld.State 2 → Prop) (stable : Stable inv)
    (splits : ∀ created, Splits created (reg created) env.step inv)
    (born : ∀ created start, some (created, start) ∈ support env.start →
      ∃ backend, start = PqxdhDeploymentEnvironment.envInitial created backend ∧
        inv start (initialized created (PqxdhRecordLiftWorld.initial (n := 2))))
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (adversary : OracleComp (PqxdhDeploymentInterface.ModeSpec mode) X) :
    ∀ result ∈ support (PqxdhRecordLiftWorld.run setup codec route env setup.serverKeyId bounds mode adversary),
      ∀ value, result.1 = some value → ∃ created, Good created value.2.2 result.2 ∧ inv value.2.2 result.2 := by
  intro result member value found
  rw [PqxdhRecordLiftWorld.run, PqxdhDeploymentEnvironmentDraw.program_rest, simulateQ_bind, StateT.run_bind,
    mem_support_bind_iff] at member
  obtain ⟨step, stepMember, rest⟩ := member
  have counted := PqxdhDeploymentEnvironmentJoin.coins_world setup codec route env.start
    (PqxdhRecordLiftWorld.initial (n := 2))
  have inMapped : Prod.map id uncount step ∈ support (Prod.map id uncount <$>
      (simulateQ (PqxdhRecordLiftWorld.handler setup codec route)
        (simulateQ PqxdhRecordLiftInterface.coinLift env.start)).run (PqxdhRecordLiftWorld.initial (n := 2))) := by
    rw [support_map]
    exact ⟨step, stepMember, rfl⟩
  rw [counted, support_map] at inMapped
  obtain ⟨startValue, startMember, same⟩ := inMapped
  have started : step.1 ∈ support env.start := by
    have first := congrArg Prod.fst same
    simp only [Prod.map_fst, id_eq] at first
    rw [← first]
    exact startMember
  have fresh : uncount step.2 = uncount (PqxdhRecordLiftWorld.initial (n := 2)) := by
    have second := congrArg Prod.snd same
    simp only [Prod.map_snd] at second
    exact second.symm
  rcases step with ⟨_ | ⟨created, start⟩, w⟩
  · simp only [PqxdhDeploymentEnvironmentDraw.worldRest, simulateQ_pure, StateT.run_pure, support_pure,
      Set.mem_singleton_iff] at rest
    subst rest
    cases found
  · obtain ⟨backend, rfl, holds⟩ := born created _ started
    have vacant : w.server = none := congrArg PqxdhRecordLiftWorld.State.server fresh
    have initRun : (PqxdhRecordLiftWorld.handler setup codec route (.inl created)).run w =
        pure ((), initialized created w) := by
      change PqxdhRecordLiftWorld.initializeServer created w = _
      simp only [PqxdhRecordLiftWorld.initializeServer, vacant]
      rfl
    dsimp only [PqxdhDeploymentEnvironmentDraw.worldRest] at rest
    rw [simulateQ_bind, StateT.run_bind, simulateQ_spec_query, initRun, pure_bind, simulateQ_bind, StateT.run_bind,
      mem_support_bind_iff] at rest
    obtain ⟨middle, middleMember, final⟩ := rest
    rw [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at final
    subst final
    simp only [Option.some.injEq] at found
    subst found
    exact ⟨created, PqxdhDeploymentEnvironmentJoin.run_keeps setup codec route env (reg created) created inv stable
      (splits created) _ _ _ (PqxdhDeploymentEnvironmentJoin.good_initial created backend w fresh)
      (stable _ _ _ (PqxdhDeploymentEnvironmentJoin.initialized_view created w fresh) holds) middle middleMember⟩

/-- Every outcome of the record world with the ideal environment of a target (`envGD`): the final environment state and World are admissible, `Good` and `IdealInv` at the drawn parameters' target (design-v2 section 6.3, `env_admitted`). The World's used markers are then exactly the slots of the environment's install ghosts (`IdealInv`'s `serverMarks` and `beaconMarks`); the guard of each hidden step (its slot's World marker unused) comes from `IdealInv` at the state before the step (`idealInv_build_ready`, `idealInv_finish_ready`, used inside `ideal_splits`). -/
theorem env_admitted (t : Target count) (ensureInit : StateT A ProbComp Bool) (identityIndex : ℕ) (runtime : A)
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (adversary : OracleComp (PqxdhDeploymentInterface.ModeSpec mode) X) :
    ∀ result ∈ support (PqxdhRecordLiftWorld.run setup codec route
        (envGD setup codec checks t ensureInit identityIndex runtime) setup.serverKeyId bounds mode adversary),
      ∀ value, result.1 = some value →
        ∃ created, Good created value.2.2 result.2 ∧ IdealInv t (dropE value.2.2) result.2 := by
  refine world_keeps setup codec route _
    (fun created => paramReg (fun p => PqxdhDeploymentIdealDefer.idealSplit setup codec route checks t p created))
    (paramInv (fun _ => IdealInv t)) (PqxdhDeploymentEnvironmentDraw.stable_param _ (fun _ => idealInv_stable t))
    (fun created => PqxdhDeploymentEnvironmentDraw.splits_param created _ _ _
      (fun p => ideal_splits setup codec route checks t p created)) ?_ bounds mode adversary
  intro created start started
  change some (created, start) ∈ support (PqxdhDeploymentIdealParams.drawParams setup count >>= fun p =>
    PqxdhDeploymentEnvironment.start setup ensureInit identityIndex runtime (fun created => (p, splitInit created)))
    at started
  rw [mem_support_bind_iff] at started
  obtain ⟨p, _, startedAt⟩ := started
  have initial := PqxdhDeploymentEnvironment.start_initial setup ensureInit identityIndex runtime _ created start
    startedAt
  subst initial
  exact ⟨_, rfl, idealInv_start t created⟩

/-- Under the ideal admissibility predicate, the World's Server markers are at one slot at most. -/
theorem server_once (t : Target count) (e : EnvState KemSK SplitBk) (w : PqxdhRecordLiftWorld.State 2)
    (holds : IdealInv t e w) (j j' : PqxdhRecordLiftInterface.Slot 2) (first : w.used j .server = true)
    (second : w.used j' .server = true) : j = j' := by
  obtain ⟨kid, c, peer, slotted⟩ := (holds.serverMarks j).mp first
  obtain ⟨kid', c', peer', slotted'⟩ := (holds.serverMarks j').mp second
  rw [peer] at peer'
  simp only [Option.some.injEq, Prod.mk.injEq] at peer'
  obtain ⟨_, rfl⟩ := peer'
  rw [slotted] at slotted'
  exact Option.some.inj slotted'

/-- Under the ideal admissibility predicate, the World's Beacon markers are at one slot at most. -/
theorem beacon_once (t : Target count) (e : EnvState KemSK SplitBk) (w : PqxdhRecordLiftWorld.State 2)
    (holds : IdealInv t e w) (j j' : PqxdhRecordLiftInterface.Slot 2) (first : w.used j .beacon = true)
    (second : w.used j' .beacon = true) : j = j' := by
  obtain ⟨c, beacon, slotted⟩ := (holds.beaconMarks j).mp first
  obtain ⟨c', beacon', slotted'⟩ := (holds.beaconMarks j').mp second
  rw [beacon] at beacon'
  cases beacon'
  rw [slotted] at slotted'
  exact Option.some.inj slotted'

/-- On every outcome of the record world with `envGD`, the World's Server markers are at one slot at most (design-v2 section 6.3, `hidden_server_once`). -/
theorem hidden_server_once (t : Target count) (ensureInit : StateT A ProbComp Bool) (identityIndex : ℕ) (runtime : A)
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (adversary : OracleComp (PqxdhDeploymentInterface.ModeSpec mode) X) :
    ∀ result ∈ support (PqxdhRecordLiftWorld.run setup codec route
        (envGD setup codec checks t ensureInit identityIndex runtime) setup.serverKeyId bounds mode adversary),
      ∀ value, result.1 = some value → ∀ j j', result.2.used j .server = true → result.2.used j' .server = true →
        j = j' := by
  intro result member value found j j' first second
  obtain ⟨_, _, holds⟩ := env_admitted setup codec route checks t ensureInit identityIndex runtime bounds mode adversary
    result member value found
  exact server_once t _ _ holds j j' first second

/-- On every outcome of the record world with `envGD`, the World's Beacon markers are at one slot at most (design-v2 section 6.3, `hidden_beacon_once`). -/
theorem hidden_beacon_once (t : Target count) (ensureInit : StateT A ProbComp Bool) (identityIndex : ℕ) (runtime : A)
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (adversary : OracleComp (PqxdhDeploymentInterface.ModeSpec mode) X) :
    ∀ result ∈ support (PqxdhRecordLiftWorld.run setup codec route
        (envGD setup codec checks t ensureInit identityIndex runtime) setup.serverKeyId bounds mode adversary),
      ∀ value, result.1 = some value → ∀ j j', result.2.used j .beacon = true → result.2.used j' .beacon = true →
        j = j' := by
  intro result member value found j j' first second
  obtain ⟨_, _, holds⟩ := env_admitted setup codec route checks t ensureInit identityIndex runtime bounds mode adversary
    result member value found
  exact beacon_once t _ _ holds j j' first second

/-- F4 on every outcome of the record world with `envGD` (design-v2 section 5.2, `seed_at_install`, at the reassembled state): the seed table of the reassembled final state holds a slot's seed exactly when the slot carries a hidden install ghost, the Server ghost (`peer` at coordinates allocated to the slot) or the Beacon ghost (`beacon` at coordinates allocated to the slot). -/
theorem seed_at_install (t : Target count) (ensureInit : StateT A ProbComp Bool) (identityIndex : ℕ) (runtime : A)
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (adversary : OracleComp (PqxdhDeploymentInterface.ModeSpec mode) X) :
    ∀ result ∈ support (PqxdhRecordLiftWorld.run setup codec route
        (envGD setup codec checks t ensureInit identityIndex runtime) setup.serverKeyId bounds mode adversary),
      ∀ value, result.1 = some value → ∀ j,
        ((merge value.2.2 result.2).seeds j).isSome = true ↔
          ((∃ kid c, (merge value.2.2 result.2).backend.2.2.2.peer = some (kid, c) ∧
              (merge value.2.2 result.2).backend.2.2.1.1 c = some j) ∨
            ∃ c, (merge value.2.2 result.2).backend.2.2.2.beacon = some c ∧
              (merge value.2.2 result.2).backend.2.2.1.1 c = some j) := by
  intro result member value found j
  obtain ⟨_, _, holds⟩ := env_admitted setup codec route checks t ensureInit identityIndex runtime bounds mode adversary
    result member value found
  exact (holds.seeds j).trans (or_congr (holds.serverMarks j) (holds.beaconMarks j))

end Outcomes


end BeaconcryptCore.Computational.PqxdhDeploymentIdealEnv

-- Axiom guards (generated)

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealEnv.idealInv_stable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealEnv.idealInv_stable

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealEnv.idealInv_start' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealEnv.idealInv_start

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealEnv.initSent_open' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealEnv.initSent_open

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealEnv.idealInv_build_ready' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealEnv.idealInv_build_ready

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealEnv.idealInv_finish_ready' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealEnv.idealInv_finish_ready

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealEnv.idealInv_move' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealEnv.idealInv_move

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealEnv.idealInv_selected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealEnv.idealInv_selected

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealEnv.idealInv_build' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealEnv.idealInv_build

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealEnv.idealInv_finish' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealEnv.idealInv_finish

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealEnv.idealStep_selected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealEnv.idealStep_selected

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealEnv.idealStep_accept_other' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealEnv.idealStep_accept_other

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealEnv.idealStep_build' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealEnv.idealStep_build

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealEnv.buildCached_hit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealEnv.buildCached_hit

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealEnv.buildCached_cache' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealEnv.buildCached_cache

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealEnv.buildCached_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealEnv.buildCached_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealEnv.idealStep_build_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealEnv.idealStep_build_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealEnv.idealStep_challenge' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealEnv.idealStep_challenge

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealEnv.idealStep_finish_real' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealEnv.idealStep_finish_real

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealEnv.idealInv_realStep' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealEnv.idealInv_realStep

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealEnv.ideal_splits' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealEnv.ideal_splits

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealEnv.c1_split' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealEnv.c1_split

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealEnv.c1_ideal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealEnv.c1_ideal

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealEnv.c1_idealGame' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealEnv.c1_idealGame

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealEnv.c3_ideal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealEnv.c3_ideal

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealEnv.ideal_reveal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealEnv.ideal_reveal

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealEnv.world_keeps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealEnv.world_keeps

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealEnv.env_admitted' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealEnv.env_admitted

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealEnv.server_once' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealEnv.server_once

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealEnv.beacon_once' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealEnv.beacon_once

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealEnv.hidden_server_once' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealEnv.hidden_server_once

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealEnv.hidden_beacon_once' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealEnv.hidden_beacon_once

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealEnv.seed_at_install' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealEnv.seed_at_install
