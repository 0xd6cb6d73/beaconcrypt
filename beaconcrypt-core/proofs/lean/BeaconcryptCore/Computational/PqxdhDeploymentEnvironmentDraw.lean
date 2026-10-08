-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentJoin

/-!
# C1 for environments that draw parameters at startup (CE-11b, generic)

CE-11b's ideal environment for a target `g` draws the challenger's parameters `p` (`PqxdhDeploymentIdealParams.drawParams`) as startup coins of the environment, before the actual Server constructor, and keeps them in its backend (design-v2 section 6.1, `envGD`). Then every record-lift reduction for the target samples `p` itself, and the native side is the challenger's draw followed by the common deployment experiment with the registration handler at `p` (the shape of `CE.idealGame g`). `PqxdhDeploymentEnvironmentJoin.join` covers environments whose startup is exactly the Server constructor; this module extends it to a startup that draws first.

- `worldRest` is the record world's open program after the startup (the private Server initialization and the wrapped adversary under the environment's native dispatch), so that `PqxdhRecordLiftInterface.program` is the counted startup followed by `worldRest` (`program_rest`).
- `join_from` is `join` from any World state whose counts alone differ from the initial World (`PqxdhDeploymentEnvironmentJoin.uncount`), which is where the World stands after counted startup coins.
- `join_draw`: if the environment's startup is a draw `draw` followed by the actual Server constructor with the initial backend `init p`, and for every drawn `p` an admissibility predicate `inv p` is stable, holds at the constructed Server's initial environment state and the initialized fresh World, and the environment splits the registration handler `reg p` relative to `inv p`, then the draw followed by the common deployment experiment with `init p` and `reg p` has the law of the record world with that environment, at the full reassembled state. `join_draw_observed` and `join_draw_analysis` are its observed and analysis projections.
- A parameter in the backend: `paramReg`, `paramStep` and `paramInv` turn families of registration handlers, environment steps and admissibility predicates indexed by a parameter into one handler, step and predicate that read the parameter from the backend (`withX`, `withE` add it, `dropX`, `dropE` remove it). The parameterized step splits the parameterized handler when each member does (`splits_param`, `stable_param`), and the experiment with the parameterized handler and the parameter in the initial backend is the experiment with the handler at that parameter (`gameWith_param`, through `handlerWith_param` and `simulateQ_embed`). `paramEnv` draws the parameter at startup and keeps it in the backend; `join_param` is C1 for it: the draw followed by the common deployment experiment with the registration handler at the drawn parameter has the law of the record world with `paramEnv`. This is the form CE-11b's `envGD` instantiates with the challenger's draws.

The startup draw goes through the World's counted coin route (`PqxdhDeploymentEnvironmentJoin.coins_world`); the World only counts it. These are equalities in law; no security claim is made here.
-/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc

set_option autoImplicit false

namespace BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentDraw
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhRecordLiftInterface (Environment WorldSpec)
open PqxdhDeploymentEnvironment (EnvState)
open PqxdhDeploymentBackend (RegImpl gameWith)
open PqxdhDeploymentEnvironmentJoin (Splits Stable joined uncount initialized coins_world run_join good_initial
  merge_initial initialized_view)
open LazyOracleDiscard (LawEq)

variable {KemSK : Type} {n : Nat}

/-- The record world's open program after the startup: on a constructed Server, its private initialization and the wrapped adversary under the environment's native dispatch. -/
noncomputable def worldRest {E X Reader Response : Type} (env : Environment n E) (crypto : Pqxdh.Crypto)
    (codec : Codec Reader Response) (serverKid : Std.U64) (bounds : PqxdhDeploymentInterface.FreshBounds)
    (mode : PqxdhDeploymentInterface.Mode) (adversary : OracleComp (PqxdhDeploymentInterface.ModeSpec mode) X)
    (born : Option (PqxdhLiveServerConstruction.Created Unit × E)) :
    OracleComp (WorldSpec n) (Option (PqxdhRegistrationJointServerBirth.ClientCreated Unit ×
      (X × PqxdhDeploymentSecrecy.Ledger) × E)) :=
  match born with
  | none => pure none
  | some (created, initial) => do
      let _ ← (WorldSpec n).query (.inl created)
      let result ← (simulateQ (PqxdhRecordLiftInterface.native env)
        (PqxdhDeploymentSecrecy.wrap crypto codec serverKid bounds
          (PqxdhDeploymentInterface.asModeO mode adversary))).run initial
      pure (some (PqxdhRegistrationJointServerBirth.encode created, result))

/-- The record world's open program is the counted startup followed by `worldRest`. -/
theorem program_rest {E X Reader Response : Type} (env : Environment n E) (crypto : Pqxdh.Crypto)
    (codec : Codec Reader Response) (serverKid : Std.U64) (bounds : PqxdhDeploymentInterface.FreshBounds)
    (mode : PqxdhDeploymentInterface.Mode) (adversary : OracleComp (PqxdhDeploymentInterface.ModeSpec mode) X) :
    PqxdhRecordLiftInterface.program env crypto codec serverKid bounds mode adversary =
      simulateQ PqxdhRecordLiftInterface.coinLift env.start >>=
        worldRest env crypto codec serverKid bounds mode adversary := by
  unfold PqxdhRecordLiftInterface.program worldRest
  refine bind_congr fun born => ?_
  rcases born with _ | ⟨created, initial⟩ <;> rfl

section Draw
variable {Bk : Type} {ι : Type} {baseSpec : OracleSpec ι} {Reader Response A X : Type}
  (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)

/-- `PqxdhDeploymentEnvironmentJoin.join` from a World state that differs from the initial World only in its counts: the common deployment experiment with the registration handler `reg` has the law of the record world's counted startup (the actual Server constructor with the initial backend `init`) and continuation run from that World state, reassembled. -/
theorem join_from (init : PqxdhLiveServerConstruction.Created Unit → Bk)
    (reg : PqxdhLiveServerConstruction.Created Unit → RegImpl KemSK Bk n) (env : Environment n (EnvState KemSK Bk))
    (ensureInit : StateT A ProbComp Bool) (identityIndex : Nat) (runtime : A)
    (inv : EnvState KemSK Bk → PqxdhRecordLiftWorld.State n → Prop) (stable : Stable inv)
    (startInv : ∀ created, inv (PqxdhDeploymentEnvironment.envInitial created (init created))
      (initialized created (PqxdhRecordLiftWorld.initial (n := n))))
    (splits : ∀ created, Splits created (reg created) env.step inv)
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (adversary : OracleComp (PqxdhDeploymentInterface.ModeSpec mode) X) (w₀ : PqxdhRecordLiftWorld.State n)
    (fresh₀ : uncount w₀ = uncount (PqxdhRecordLiftWorld.initial (n := n))) :
    LawEq ((gameWith setup codec route init reg ensureInit identityIndex bounds mode adversary).run' runtime)
      (joined <$> (simulateQ (PqxdhRecordLiftWorld.handler setup codec route)
        (simulateQ PqxdhRecordLiftInterface.coinLift
            (PqxdhDeploymentEnvironment.start setup ensureInit identityIndex runtime init) >>=
          worldRest env setup.source.crypto codec setup.serverKeyId bounds mode adversary)).run w₀) := by
  let wrapped := PqxdhDeploymentSecrecy.wrap setup.source.crypto codec setup.serverKeyId bounds
    (PqxdhDeploymentInterface.asModeO mode adversary)
  let native : Option (PqxdhLiveServerConstruction.Created Unit × EnvState KemSK Bk) →
      ProbComp (Option (PqxdhRegistrationJointServerBirth.ClientCreated Unit × X × PqxdhDeploymentSecrecy.Ledger ×
        PqxdhDeploymentBackend.XState KemSK Bk n)) := fun born => match born with
    | none => pure none
    | some (created, _) => (fun result => some (PqxdhRegistrationJointServerBirth.encode created, result.1.1,
        result.1.2, result.2)) <$> (simulateQ (PqxdhDeploymentBackend.handlerWith setup codec route (reg created))
          wrapped).run (PqxdhDeploymentBackend.xinitial created (init created))
  -- the native game is the constructor followed by `native`
  have nativeSide : (gameWith setup codec route init reg ensureInit identityIndex bounds mode adversary).run' runtime =
      PqxdhDeploymentEnvironment.start setup ensureInit identityIndex runtime init >>= native := by
    simp only [gameWith, PqxdhDeploymentEnvironment.start, StateT.run', StateT.run, map_bind, bind_map_left]
    refine bind_congr fun constructed => ?_
    cases constructed.1 <;> simp only [map_pure, Functor.map_map, Option.map_none, Option.map_some, native]
    rfl
  -- the record world is the counted startup followed by its continuation
  let startup := (simulateQ (PqxdhRecordLiftWorld.handler setup codec route)
    (simulateQ PqxdhRecordLiftInterface.coinLift
      (PqxdhDeploymentEnvironment.start setup ensureInit identityIndex runtime init))).run w₀
  have counted := coins_world setup codec route
    (PqxdhDeploymentEnvironment.start setup ensureInit identityIndex runtime init) w₀
  have startupFst : Prod.fst <$> startup = PqxdhDeploymentEnvironment.start setup ensureInit identityIndex runtime init := by
    have forgot := congrArg (fun work => Prod.fst <$> work) counted
    simpa only [Functor.map_map, Prod.map_fst, id_eq, Function.comp_def, id_map'] using forgot
  have lhs : PqxdhDeploymentEnvironment.start setup ensureInit identityIndex runtime init >>= native =
      startup >>= fun step => native step.1 := by
    rw [← startupFst, bind_map_left]
  rw [nativeSide, lhs]
  simp only [simulateQ_bind, StateT.run_bind, map_bind]
  refine LawEq.symm (PqxdhDeploymentSeedSplit.LawEq.bind_support _ fun step member => ?_)
  have fresh : uncount step.2 = uncount (PqxdhRecordLiftWorld.initial (n := n)) := by
    have inMapped : Prod.map id uncount step ∈ support (Prod.map id uncount <$> startup) := by
      rw [support_map]
      exact ⟨step, member, rfl⟩
    rw [counted, support_map] at inMapped
    obtain ⟨_, _, same⟩ := inMapped
    exact (congrArg Prod.snd same).symm.trans fresh₀
  have started : step.1 ∈ support (PqxdhDeploymentEnvironment.start setup ensureInit identityIndex runtime init) := by
    rw [← startupFst, support_map]
    exact ⟨step, member, rfl⟩
  rcases step with ⟨_ | ⟨created, initialEnv⟩, w⟩
  · simp only [worldRest, simulateQ_pure, StateT.run_pure, map_pure, joined, Option.map_none]
    exact LawEq.refl _
  · have initialEq := PqxdhDeploymentEnvironment.start_initial setup ensureInit identityIndex runtime init created
      initialEnv started
    subst initialEq
    have vacant : w.server = none := congrArg PqxdhRecordLiftWorld.State.server fresh
    have initRun : (PqxdhRecordLiftWorld.handler setup codec route (.inl created)).run w =
        pure ((), initialized created w) := by
      change PqxdhRecordLiftWorld.initializeServer created w = _
      simp only [PqxdhRecordLiftWorld.initializeServer, vacant]
      rfl
    have joinedRun := (run_join setup codec route env (reg created) created inv stable (splits created) wrapped
      (PqxdhDeploymentEnvironment.envInitial created (init created)) (initialized created w)
      (good_initial created (init created) w fresh)
      (stable _ _ _ (initialized_view created w fresh) (startInv created))).map
        (fun result => some (PqxdhRegistrationJointServerBirth.encode created, result.1.1, result.1.2, result.2))
    rw [merge_initial created (init created) w fresh, Functor.map_map] at joinedRun
    dsimp only [worldRest]
    rw [simulateQ_bind, StateT.run_bind, simulateQ_spec_query, initRun, pure_bind]
    simp only [bind_pure_comp, simulateQ_map, StateT.run_map, Functor.map_map]
    exact joinedRun

/-- C1 for an environment that draws parameters at startup: if the environment's startup is the draw `draw` followed by the actual Server constructor with the initial backend `init p`, and for every drawn `p` the stable admissibility predicate `inv p` holds at the constructed Server's initial environment state and the initialized fresh World and the environment splits every constructed Server's registration handler `reg p` relative to `inv p`, then the draw followed by the common deployment experiment with `init p` and `reg p` and the record world with that environment have the same law of the Server's public data, the adversary's output, the ledger and the full reassembled final state. -/
theorem join_draw {P : Type} (draw : ProbComp P) (init : P → PqxdhLiveServerConstruction.Created Unit → Bk)
    (reg : P → PqxdhLiveServerConstruction.Created Unit → RegImpl KemSK Bk n) (env : Environment n (EnvState KemSK Bk))
    (ensureInit : StateT A ProbComp Bool) (identityIndex : Nat) (runtime : A)
    (born : env.start = draw >>= fun p => PqxdhDeploymentEnvironment.start setup ensureInit identityIndex runtime (init p))
    (inv : P → EnvState KemSK Bk → PqxdhRecordLiftWorld.State n → Prop) (stable : ∀ p, Stable (inv p))
    (startInv : ∀ p created, inv p (PqxdhDeploymentEnvironment.envInitial created (init p created))
      (initialized created (PqxdhRecordLiftWorld.initial (n := n))))
    (splits : ∀ p created, Splits created (reg p created) env.step (inv p))
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (adversary : OracleComp (PqxdhDeploymentInterface.ModeSpec mode) X) :
    LawEq (draw >>= fun p => (gameWith setup codec route (init p) (reg p) ensureInit identityIndex bounds mode
        adversary).run' runtime)
      (joined <$> PqxdhRecordLiftWorld.run setup codec route env setup.serverKeyId bounds mode adversary) := by
  let drawn := (simulateQ (PqxdhRecordLiftWorld.handler setup codec route)
    (simulateQ PqxdhRecordLiftInterface.coinLift draw)).run (PqxdhRecordLiftWorld.initial (n := n))
  have counted := coins_world setup codec route draw (PqxdhRecordLiftWorld.initial (n := n))
  have drawnFst : Prod.fst <$> drawn = draw := by
    have forgot := congrArg (fun work => Prod.fst <$> work) counted
    simpa only [Functor.map_map, Prod.map_fst, id_eq, Function.comp_def, id_map'] using forgot
  have lhs : (draw >>= fun p => (gameWith setup codec route (init p) (reg p) ensureInit identityIndex bounds mode
      adversary).run' runtime) = drawn >>= fun step => (gameWith setup codec route (init step.1) (reg step.1) ensureInit
        identityIndex bounds mode adversary).run' runtime := by
    rw [← drawnFst, bind_map_left]
  rw [lhs, PqxdhRecordLiftWorld.run, program_rest, born]
  simp only [simulateQ_bind, bind_assoc, StateT.run_bind, map_bind]
  refine PqxdhDeploymentSeedSplit.LawEq.bind_support _ fun step member => ?_
  have fresh : uncount step.2 = uncount (PqxdhRecordLiftWorld.initial (n := n)) := by
    have inMapped : Prod.map id uncount step ∈ support (Prod.map id uncount <$> drawn) := by
      rw [support_map]
      exact ⟨step, member, rfl⟩
    rw [counted, support_map] at inMapped
    obtain ⟨_, _, same⟩ := inMapped
    exact (congrArg Prod.snd same).symm
  have joinedStep := join_from setup codec route (init step.1) (reg step.1) env ensureInit identityIndex runtime
    (inv step.1) (stable step.1) (startInv step.1) (splits step.1) bounds mode adversary step.2 fresh
  simp only [simulateQ_bind, StateT.run_bind, map_bind] at joinedStep
  exact joinedStep

/-- The observed projection of `join_draw` (`PqxdhRecordLiftWorld.game`): the draw followed by the adversary's output, the ledger and the produced frames of the native game has the law of the record world's game. -/
theorem join_draw_observed {P : Type} (draw : ProbComp P) (init : P → PqxdhLiveServerConstruction.Created Unit → Bk)
    (reg : P → PqxdhLiveServerConstruction.Created Unit → RegImpl KemSK Bk n) (env : Environment n (EnvState KemSK Bk))
    (ensureInit : StateT A ProbComp Bool) (identityIndex : Nat) (runtime : A)
    (born : env.start = draw >>= fun p => PqxdhDeploymentEnvironment.start setup ensureInit identityIndex runtime (init p))
    (inv : P → EnvState KemSK Bk → PqxdhRecordLiftWorld.State n → Prop) (stable : ∀ p, Stable (inv p))
    (startInv : ∀ p created, inv p (PqxdhDeploymentEnvironment.envInitial created (init p created))
      (initialized created (PqxdhRecordLiftWorld.initial (n := n))))
    (splits : ∀ p created, Splits created (reg p created) env.step (inv p))
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (adversary : OracleComp (PqxdhDeploymentInterface.ModeSpec mode) X) :
    LawEq (draw >>= fun p => (fun outcome => outcome.map fun value => (value.2.1, value.2.2.1,
        value.2.2.2.base.produced)) <$>
        (gameWith setup codec route (init p) (reg p) ensureInit identityIndex bounds mode adversary).run' runtime)
      (PqxdhRecordLiftWorld.game setup codec route env setup.serverKeyId bounds mode adversary) := by
  have joinedDraw := (join_draw setup codec route draw init reg env ensureInit identityIndex runtime born inv stable
    startInv splits bounds mode adversary).map (fun outcome => outcome.map fun value => (value.2.1, value.2.2.1,
      value.2.2.2.base.produced))
  rw [Functor.map_map, map_bind] at joinedDraw
  refine joinedDraw.trans (LawEq.of_eq ?_)
  unfold PqxdhRecordLiftWorld.game
  congr 1
  funext result
  rcases result with ⟨_ | value, w⟩ <;> rfl

/-- The analysis projection of `join_draw` (`PqxdhRecordLiftWorld.analysis`): the draw followed by the adversary's output, the ledger, the produced frames and the raw-attempt counters of the native game has the law of the record world's analysis projection. -/
theorem join_draw_analysis {P : Type} (draw : ProbComp P) (init : P → PqxdhLiveServerConstruction.Created Unit → Bk)
    (reg : P → PqxdhLiveServerConstruction.Created Unit → RegImpl KemSK Bk n) (env : Environment n (EnvState KemSK Bk))
    (ensureInit : StateT A ProbComp Bool) (identityIndex : Nat) (runtime : A)
    (born : env.start = draw >>= fun p => PqxdhDeploymentEnvironment.start setup ensureInit identityIndex runtime (init p))
    (inv : P → EnvState KemSK Bk → PqxdhRecordLiftWorld.State n → Prop) (stable : ∀ p, Stable (inv p))
    (startInv : ∀ p created, inv p (PqxdhDeploymentEnvironment.envInitial created (init p created))
      (initialized created (PqxdhRecordLiftWorld.initial (n := n))))
    (splits : ∀ p created, Splits created (reg p created) env.step (inv p))
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (adversary : OracleComp (PqxdhDeploymentInterface.ModeSpec mode) X) :
    LawEq (draw >>= fun p => (fun outcome => outcome.map fun value => (value.2.1, value.2.2.1,
        value.2.2.2.base.produced,
        (⟨value.2.2.2.base.serverRaw, value.2.2.2.base.ownerRaw⟩ : PqxdhRecordLiftWorld.RawCounters))) <$>
        (gameWith setup codec route (init p) (reg p) ensureInit identityIndex bounds mode adversary).run' runtime)
      (PqxdhRecordLiftWorld.analysis <$> PqxdhRecordLiftWorld.run setup codec route env setup.serverKeyId bounds mode
        adversary) := by
  have joinedDraw := (join_draw setup codec route draw init reg env ensureInit identityIndex runtime born inv stable
    startInv splits bounds mode adversary).map (fun outcome => outcome.map fun value => (value.2.1, value.2.2.1,
      value.2.2.2.base.produced,
      (⟨value.2.2.2.base.serverRaw, value.2.2.2.base.ownerRaw⟩ : PqxdhRecordLiftWorld.RawCounters)))
  rw [Functor.map_map, map_bind] at joinedDraw
  refine joinedDraw.trans (LawEq.of_eq ?_)
  congr 1
  funext result
  rcases result with ⟨_ | value, w⟩ <;> rfl

end Draw

/-! ### A parameter in the backend -/

section Param
variable {P Bk : Type}

/-- An extended state whose backend also holds a parameter, without the parameter. -/
def dropX (x : PqxdhDeploymentBackend.XState KemSK (P × Bk) n) : PqxdhDeploymentBackend.XState KemSK Bk n :=
  ⟨x.base, x.backend.2, x.seeds, x.snap, x.log⟩

/-- An extended state with a parameter added to its backend. -/
def withX (p : P) (y : PqxdhDeploymentBackend.XState KemSK Bk n) : PqxdhDeploymentBackend.XState KemSK (P × Bk) n :=
  ⟨y.base, (p, y.backend), y.seeds, y.snap, y.log⟩

/-- An environment state whose backend also holds a parameter, without the parameter. -/
def dropE (e : EnvState KemSK (P × Bk)) : EnvState KemSK Bk := ⟨e.native, e.backend.2, e.snap, e.log, e.created⟩

/-- An environment state with a parameter added to its backend. -/
def withE (p : P) (e : EnvState KemSK Bk) : EnvState KemSK (P × Bk) := ⟨e.native, (p, e.backend), e.snap, e.log, e.created⟩

/-- A family of registration handlers indexed by a parameter, as one handler that reads the parameter from its backend. -/
noncomputable def paramReg (regs : P → RegImpl KemSK Bk n) : RegImpl KemSK (P × Bk) n :=
  fun query => StateT.mk fun x => Prod.map id (withX x.backend.1) <$> (regs x.backend.1 query).run (dropX x)

/-- A family of environment steps indexed by a parameter, as one step that reads the parameter from its backend. -/
noncomputable def paramStep (steps : P → PqxdhDeploymentEnvironment.EnvStep KemSK Bk n) :
    PqxdhDeploymentEnvironment.EnvStep KemSK (P × Bk) n :=
  fun query => StateT.mk fun e => Prod.map id (withE e.backend.1) <$> (steps e.backend.1 query).run (dropE e)

/-- A family of admissibility predicates indexed by a parameter, read at the parameter of the backend. -/
def paramInv (inv : P → EnvState KemSK Bk → PqxdhRecordLiftWorld.State n → Prop) :
    EnvState KemSK (P × Bk) → PqxdhRecordLiftWorld.State n → Prop :=
  fun e w => inv e.backend.1 (dropE e) w

/-- Reassembly commutes with adding the parameter. -/
theorem merge_withE (p : P) (e : EnvState KemSK Bk) (w : PqxdhRecordLiftWorld.State n) :
    PqxdhDeploymentEnvironmentJoin.merge (withE p e) w = withX p (PqxdhDeploymentEnvironmentJoin.merge e w) := rfl

/-- Admissibility does not read the backend. -/
theorem good_withE (created : PqxdhLiveServerConstruction.Created Unit) (p : P) (e : EnvState KemSK Bk)
    (w : PqxdhRecordLiftWorld.State n) :
    PqxdhDeploymentEnvironmentJoin.Good created (withE p e) w ↔ PqxdhDeploymentEnvironmentJoin.Good created e w :=
  ⟨fun good => ⟨good.stripped, good.createdEq, good.server, good.ownersLength, good.owners⟩,
    fun good => ⟨good.stripped, good.createdEq, good.server, good.ownersLength, good.owners⟩⟩

/-- The parameterized predicate of stable predicates is stable. -/
theorem stable_param (inv : P → EnvState KemSK Bk → PqxdhRecordLiftWorld.State n → Prop) (stable : ∀ p, Stable (inv p)) :
    Stable (paramInv inv) :=
  fun e w w' view holds => stable e.backend.1 (dropE e) w w' view holds

/-- If the environment step at each parameter splits the registration handler at that parameter relative to the predicate at that parameter, the parameterized step splits the parameterized handler relative to the parameterized predicate. -/
theorem splits_param (created : PqxdhLiveServerConstruction.Created Unit) (regs : P → RegImpl KemSK Bk n)
    (steps : P → PqxdhDeploymentEnvironment.EnvStep KemSK Bk n)
    (inv : P → EnvState KemSK Bk → PqxdhRecordLiftWorld.State n → Prop)
    (splits : ∀ p, Splits created (regs p) (steps p) (inv p)) :
    Splits created (paramReg regs) (paramStep steps) (paramInv inv) := by
  intro query e w good holds
  have inner := splits e.backend.1 query (dropE e) w ((good_withE created e.backend.1 (dropE e) w).mp good) holds
  have run : (paramStep steps query).run e = Prod.map id (withE e.backend.1) <$> (steps e.backend.1 query).run (dropE e) :=
    rfl
  rw [run, simulateQ_map, StateT.run_map]
  refine ⟨?_, ?_⟩
  · have mapped := inner.1.map (Prod.map id (withX e.backend.1))
    rw [Functor.map_map] at mapped
    have rhs : (paramReg regs query).run (PqxdhDeploymentEnvironmentJoin.merge e w) =
        Prod.map id (withX e.backend.1) <$> (regs e.backend.1 query).run (PqxdhDeploymentEnvironmentJoin.merge (dropE e) w) :=
      rfl
    rw [Functor.map_map, rhs]
    exact mapped
  · intro result member
    rw [support_map] at member
    obtain ⟨original, originalMember, rfl⟩ := member
    obtain ⟨goodAfter, invAfter⟩ := inner.2 original originalMember
    exact ⟨(good_withE created e.backend.1 original.1.2 original.2).mpr goodAfter, invAfter⟩

section Native
variable {ι : Type} {baseSpec : OracleSpec ι} {Reader Response A X : Type}
  (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)

/-- One step of the native handler with the parameterized registration handler, from a state holding the parameter, is the step with the handler at that parameter, with the parameter added. -/
theorem handlerWith_param (regs : P → RegImpl KemSK Bk n) (p : P) (query : PqxdhDeploymentInterface.Spec.Domain)
    (y : PqxdhDeploymentBackend.XState KemSK Bk n) :
    (PqxdhDeploymentBackend.handlerWith setup codec route (paramReg regs) query).run (withX p y) =
      Prod.map id (withX p) <$> (PqxdhDeploymentBackend.handlerWith setup codec route (regs p) query).run y := by
  rcases query with coin | command
  · simp only [PqxdhDeploymentBackend.handlerWith, StateT.run_lift, map_bind, map_pure]
    rfl
  · cases command
    all_goals first
      | rfl
      | (simp only [PqxdhDeploymentBackend.handlerWith, PqxdhDeploymentBackend.onBase, LazyOracleDiscard.StateLens.lift,
          PqxdhDeploymentBackend.baseLens, StateT.run, Functor.map_map]
         rfl)

/-- A simulation whose every step from an embedded state is the embedded step of a second simulation is the embedded second simulation. -/
theorem simulateQ_embed {ι' σ₁ σ₂ α : Type} {spec' : OracleSpec ι'} (impl₁ : QueryImpl spec' (StateT σ₁ ProbComp))
    (impl₂ : QueryImpl spec' (StateT σ₂ ProbComp)) (embed : σ₂ → σ₁)
    (step : ∀ query state, (impl₁ query).run (embed state) = Prod.map id embed <$> (impl₂ query).run state)
    (work : OracleComp spec' α) (state : σ₂) :
    (simulateQ impl₁ work).run (embed state) = Prod.map id embed <$> (simulateQ impl₂ work).run state := by
  induction work using OracleComp.inductionOn generalizing state with
  | pure value => simp only [simulateQ_pure, StateT.run_pure, map_pure, Prod.map_apply, id_eq]
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, id_map,
        StateT.run_bind, step, bind_map_left, map_bind, Prod.map_fst, Prod.map_snd, id_eq, ih]

/-- The common deployment experiment with the parameterized registration handler and the parameter `p` in the initial backend is the experiment with the handler at `p`, with `p` added to the final backend. -/
theorem gameWith_param (init : PqxdhLiveServerConstruction.Created Unit → Bk)
    (regs : P → PqxdhLiveServerConstruction.Created Unit → RegImpl KemSK Bk n) (p : P) (ensureInit : StateT A ProbComp Bool)
    (identityIndex : Nat) (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (adversary : OracleComp (PqxdhDeploymentInterface.ModeSpec mode) X) (runtime : A) :
    (gameWith setup codec route (fun created => (p, init created)) (fun created => paramReg (fun q => regs q created))
        ensureInit identityIndex bounds mode adversary).run runtime =
      PqxdhDeploymentFinishErasure.outcomeMap (withX p) <$>
        (gameWith setup codec route init (regs p) ensureInit identityIndex bounds mode adversary).run runtime := by
  simp only [gameWith, StateT.run, map_bind]
  refine bind_congr fun born => ?_
  rcases born with ⟨_ | created, after⟩
  · simp only [map_pure, PqxdhDeploymentFinishErasure.outcomeMap, Option.map_none]
  · dsimp only
    have embedded := simulateQ_embed _ _ (withX p) (fun query state => handlerWith_param setup codec route
      (fun q => regs q created) p query state) (PqxdhDeploymentSecrecy.wrap setup.source.crypto codec setup.serverKeyId
        bounds (PqxdhDeploymentInterface.asModeO mode adversary)) (PqxdhDeploymentBackend.xinitial created (init created))
    simp only [StateT.run] at embedded
    rw [show (PqxdhDeploymentBackend.xinitial created (p, init created) : PqxdhDeploymentBackend.XState KemSK (P × Bk) n) =
      withX p (PqxdhDeploymentBackend.xinitial created (init created)) from rfl, embedded, Functor.map_map,
      Functor.map_map]
    rfl

/-- The environment with a parameter drawn at startup and kept in its backend: the draw, then the actual Server constructor with the parameter added to the initial backend; its step is the parameterized step. -/
noncomputable def paramEnv (draw : ProbComp P) (steps : P → PqxdhDeploymentEnvironment.EnvStep KemSK Bk n)
    (ensureInit : StateT A ProbComp Bool) (identityIndex : Nat) (runtime : A)
    (init : PqxdhLiveServerConstruction.Created Unit → Bk) : Environment n (EnvState KemSK (P × Bk)) :=
  ⟨draw >>= fun p => PqxdhDeploymentEnvironment.start setup ensureInit identityIndex runtime
      (fun created => (p, init created)), paramStep steps⟩

/-- C1 for a parameter drawn at startup: if, at every parameter `p`, the stable admissibility predicate `inv p` holds at the constructed Server's initial environment state and the initialized fresh World and the environment step `steps p` splits every constructed Server's registration handler `regs p` relative to `inv p`, then the draw followed by the common deployment experiment with `regs p` (the parameter added to the final backend) and the record world with the environment that draws the parameter at startup (`paramEnv`) have the same law of the Server's public data, the adversary's output, the ledger and the full reassembled final state. -/
theorem join_param (draw : ProbComp P) (init : PqxdhLiveServerConstruction.Created Unit → Bk)
    (regs : P → PqxdhLiveServerConstruction.Created Unit → RegImpl KemSK Bk n)
    (steps : P → PqxdhDeploymentEnvironment.EnvStep KemSK Bk n) (ensureInit : StateT A ProbComp Bool)
    (identityIndex : Nat) (runtime : A) (inv : P → EnvState KemSK Bk → PqxdhRecordLiftWorld.State n → Prop)
    (stable : ∀ p, Stable (inv p))
    (startInv : ∀ p created, inv p (PqxdhDeploymentEnvironment.envInitial created (init created))
      (initialized created (PqxdhRecordLiftWorld.initial (n := n))))
    (splits : ∀ p created, Splits created (regs p created) (steps p) (inv p))
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (adversary : OracleComp (PqxdhDeploymentInterface.ModeSpec mode) X) :
    LawEq (draw >>= fun p => (fun outcome => outcome.map fun value => (value.1, value.2.1, value.2.2.1,
        withX p value.2.2.2)) <$>
        (gameWith setup codec route init (regs p) ensureInit identityIndex bounds mode adversary).run' runtime)
      (joined <$> PqxdhRecordLiftWorld.run setup codec route
        (paramEnv setup draw steps ensureInit identityIndex runtime init) setup.serverKeyId bounds mode adversary) := by
  have drawn := join_draw setup codec route draw (fun p created => (p, init created))
    (fun _ created => paramReg (fun q => regs q created)) (paramEnv setup draw steps ensureInit identityIndex runtime init)
    ensureInit identityIndex runtime rfl (fun _ => paramInv inv) (fun _ => stable_param inv stable)
    (fun p created => startInv p created)
    (fun _ created => splits_param created (fun q => regs q created) steps inv (fun q => splits q created))
    bounds mode adversary
  refine LawEq.trans (LawEq.of_eq ?_) drawn
  refine bind_congr fun p => ?_
  rw [StateT.run'_eq, StateT.run'_eq, gameWith_param setup codec route init regs p, Functor.map_map, Functor.map_map]
  rfl

end Native

end Param

end BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentDraw

-- Axiom guards (generated)

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentDraw.program_rest' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentDraw.program_rest

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentDraw.join_from' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentDraw.join_from

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentDraw.join_draw' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentDraw.join_draw

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentDraw.join_draw_observed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentDraw.join_draw_observed

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentDraw.join_draw_analysis' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentDraw.join_draw_analysis

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentDraw.merge_withE' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentDraw.merge_withE

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentDraw.good_withE' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentDraw.good_withE

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentDraw.stable_param' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentDraw.stable_param

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentDraw.splits_param' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentDraw.splits_param

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentDraw.handlerWith_param' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentDraw.handlerWith_param

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentDraw.simulateQ_embed' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentDraw.simulateQ_embed

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentDraw.gameWith_param' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentDraw.gameWith_param

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentDraw.join_param' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentDraw.join_param
