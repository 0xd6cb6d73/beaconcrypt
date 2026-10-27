-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterGame
import BeaconcryptCore.Computational.PqxdhDeploymentIdealDefer
import BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentDraw

/-! LQ-F upstream, unit C1: the generic later forms of CE-11b's split chain and of the hand-off obligation C1 with drawn parameters (unit 11b-L of the CE plan, LQ-F upstream design-v2 section 4.2). CE-11b proved, for the run-phase experiment `PqxdhDeploymentBackend.gameWith`, the represent step, the seed relocation, the seed deferral with lists of points, the parameter in the backend and the obligation C1 for an environment that draws its parameters at startup. This module proves the same steps for the LQ-F later game `PqxdhDeploymentFinishErasure.laterWith`, whose post phase runs after the run phase from the run's final state and whose second adversary receives the LQ-F reveal of that state.

- Transport along a state map (`laterTail_map`, `laterWith_map`, `laterWith_proj`): when the post handlers commute with a map of the extended state and the reveal does not see what the map changes, the later games with two registration handlers are related exactly (`laterWith_map`, the run phases related exactly per command) or in law (`laterWith_proj`, the run phases related in law per constructed Server), up to the map of the final state.
- The represent step (`represent_later`, `represent_split_later`): for a natural registration core and a service projection, the later games with the two services and the fixed real post phase `realPost` have the same law up to the service projection of the final state. The real post phase runs on the deployment state only, so it commutes with every replacement of the service state (`realPost_mapBackend`), and the reveal reads neither the service state (`xreveal_mapBackend`) nor the seed table.
- Seed relocation (`game_moveSeeds_later`): for slot programs that keep the seed table, the later game with the seeds in the service state, read with the seeds moved into the extended state, is exactly the later game with the seeds in the extended state (`realPost_moveSeeds`).
- The parameter in the backend (`postNative_param`, `laterWith_param`): the later game with the parameterized registration handler, its own post phase and the parameter in the initial backend is the later game with the handler at that parameter, the parameter added to the final backend.
- C6 with drawn parameters (`run_split_from`, `join_later_from`, `later_program_draw`, `join_later_draw`, `join_later_param`): `PqxdhDeploymentEnvironmentJoin.join_later` from any World state whose counts alone differ from the initial World, then for an environment that draws a parameter at startup before the actual Server constructor (the later forms of `PqxdhDeploymentEnvironmentDraw.join_from`, `join_draw` and `join_param`).
- The seed deferral with lists of points (`defer_seeds_later`): `PqxdhDeploymentIdealDefer.defer_seeds` for the later game. The post phase only has to commute with seed completions; it need not keep the invariant, because `PqxdhDeploymentIdealDefer.discard_erase_list` uses the invariant only inside the run and asks only blindness of the continuation (`PqxdhDeploymentFinishErasure.laterTail_blind`).

The instances at CE-11b's ideal registration are in `PqxdhDeploymentIdealLaterEnv`. These are equalities of programs and in law; they charge nothing, add no assumption and make no security claim. LQ-F claims confidentiality only. -/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc

set_option autoImplicit false

namespace BeaconcryptCore.Computational.PqxdhDeploymentIdealLater
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhDeploymentInterface (Spec FreshBounds Mode ModeSpec asModeO)
open PqxdhDeploymentBackend (XState RegImpl handlerWith xinitial seedLens)
open PqxdhDeploymentFinishErasure (outcomeMap laterWith laterTail realPost xreveal)
open PqxdhDeploymentSeedSplit (SlotService ServiceProj CoreNatural mapBackend seedFree)
open PqxdhDeploymentIdealDefer (PointedSeeds pointedWithSeeds)
open PqxdhDeploymentIdealSlots (Coord SlotProgram slotCore)
open PqxdhDeploymentIdealKeys (moveSeeds slotCoreX seedPut)
open PqxdhDeploymentIdealErase (SlotFrame)
open PqxdhRegistrationJointKemSecondEntry (Alloc)
open PqxdhDeploymentEnvironment (EnvState EnvStep)
open PqxdhDeploymentEnvironmentJoin (Splits Stable joined uncount initialized postNative envReveal)
open PqxdhDeploymentEnvironmentDraw (paramReg paramInv paramEnv withX)
open PqxdhDeploymentLater (PostSpec)
open PqxdhRecordLiftInterface (EnvQuery Environment)
open LazyOracleDiscard (Commutes LawEq)

/-! ### Transport along a map of the extended state -/

section Transport
variable {KemSK : Type} {n : ℕ}
variable {ι : Type} {baseSpec : OracleSpec ι} {Reader Response A X Out : Type}
  (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)

/-- The post phase transported along a map of the extended state: when the post handlers commute with the map and the reveal does not see what it changes, the post phase from the mapped run's result is the post phase from the run's result, its final state mapped. -/
theorem laterTail_map {Bk₁ Bk₂ : Type} (proj : XState KemSK Bk₁ n → XState KemSK Bk₂ n)
    (post₁ : PqxdhLiveServerConstruction.Created Unit → QueryImpl PostSpec (StateT (XState KemSK Bk₁ n) ProbComp))
    (post₂ : PqxdhLiveServerConstruction.Created Unit → QueryImpl PostSpec (StateT (XState KemSK Bk₂ n) ProbComp))
    (postStep : ∀ created query x,
      Prod.map id proj <$> (post₁ created query).run x = (post₂ created query).run (proj x))
    (reveal : ∀ created x, xreveal created (proj x) = xreveal created x)
    (created : PqxdhLiveServerConstruction.Created Unit)
    (second : X → PqxdhDeploymentLaterServerGame.Reveal → OracleComp PostSpec Out) (after : A)
    (run : (X × PqxdhDeploymentSecrecy.Ledger) × XState KemSK Bk₁ n) :
    outcomeMap proj <$> laterTail post₁ created second id after run =
      laterTail post₂ created second id after (Prod.map id proj run) := by
  simp only [laterTail, Prod.map_fst, Prod.map_snd, id_eq, reveal]
  rw [← OracleComp.map_run_simulateQ_eq_of_query_map_eq (post₁ created) (post₂ created) proj (postStep created)
    (second run.1.1 (xreveal created run.2)) run.2, bind_map_left, map_bind]
  refine bind_congr fun post => ?_
  simp only [map_pure, Prod.map_fst, Prod.map_snd, id_eq]
  rfl

/-- The later game transported exactly along a map of the extended state: when the map carries every command of the first handler to the second (the fixed steps included), the initial states to each other and the first post handler to the second, and the reveal does not see what it changes, the later game with the second handler is the later game with the first, its final state mapped. -/
theorem laterWith_map {Bk₁ Bk₂ : Type} (proj : XState KemSK Bk₁ n → XState KemSK Bk₂ n)
    (init₁ : PqxdhLiveServerConstruction.Created Unit → Bk₁) (init₂ : PqxdhLiveServerConstruction.Created Unit → Bk₂)
    (reg₁ : PqxdhLiveServerConstruction.Created Unit → RegImpl KemSK Bk₁ n)
    (reg₂ : PqxdhLiveServerConstruction.Created Unit → RegImpl KemSK Bk₂ n)
    (post₁ : PqxdhLiveServerConstruction.Created Unit → QueryImpl PostSpec (StateT (XState KemSK Bk₁ n) ProbComp))
    (post₂ : PqxdhLiveServerConstruction.Created Unit → QueryImpl PostSpec (StateT (XState KemSK Bk₂ n) ProbComp))
    (handlerStep : ∀ created query x, Prod.map id proj <$> (handlerWith setup codec route (reg₁ created) query).run x =
      (handlerWith setup codec route (reg₂ created) query).run (proj x))
    (initial : ∀ created, proj (xinitial created (init₁ created)) = xinitial created (init₂ created))
    (postStep : ∀ created query x,
      Prod.map id proj <$> (post₁ created query).run x = (post₂ created query).run (proj x))
    (reveal : ∀ created x, xreveal created (proj x) = xreveal created x)
    (ensureInit : StateT A ProbComp Bool) (identityIndex : ℕ) (bounds : FreshBounds) (mode : Mode)
    (first : OracleComp (ModeSpec mode) X)
    (second : X → PqxdhDeploymentLaterServerGame.Reveal → OracleComp PostSpec Out) (runtime : A) :
    outcomeMap proj <$> (laterWith setup codec route init₁ reg₁ post₁ ensureInit identityIndex bounds mode first
        second).run runtime =
      (laterWith setup codec route init₂ reg₂ post₂ ensureInit identityIndex bounds mode first second).run runtime := by
  rw [PqxdhDeploymentIdealLaterGame.laterWith_split, PqxdhDeploymentIdealLaterGame.laterWith_split, map_bind]
  refine bind_congr fun born => ?_
  rcases born with ⟨_ | created, after⟩
  · simp only [map_pure]
    rfl
  · dsimp only
    rw [map_bind]
    simp only [laterTail_map proj post₁ post₂ postStep reveal]
    rw [← initial created, ← OracleComp.map_run_simulateQ_eq_of_query_map_eq _ _ proj (handlerStep created),
      bind_map_left]

/-- The later game transported in law along a map of the extended state: when, for every constructed Server, the run phase with the first handler, its final state mapped, has the law of the run phase with the second, the map carries the first post handler to the second and the reveal does not see what it changes, the later games have the same law up to the map of the final state. -/
theorem laterWith_proj {Bk₁ Bk₂ : Type} (proj : XState KemSK Bk₁ n → XState KemSK Bk₂ n)
    (init₁ : PqxdhLiveServerConstruction.Created Unit → Bk₁) (init₂ : PqxdhLiveServerConstruction.Created Unit → Bk₂)
    (reg₁ : PqxdhLiveServerConstruction.Created Unit → RegImpl KemSK Bk₁ n)
    (reg₂ : PqxdhLiveServerConstruction.Created Unit → RegImpl KemSK Bk₂ n)
    (post₁ : PqxdhLiveServerConstruction.Created Unit → QueryImpl PostSpec (StateT (XState KemSK Bk₁ n) ProbComp))
    (post₂ : PqxdhLiveServerConstruction.Created Unit → QueryImpl PostSpec (StateT (XState KemSK Bk₂ n) ProbComp))
    (postStep : ∀ created query x,
      Prod.map id proj <$> (post₁ created query).run x = (post₂ created query).run (proj x))
    (reveal : ∀ created x, xreveal created (proj x) = xreveal created x)
    (ensureInit : StateT A ProbComp Bool) (identityIndex : ℕ) (bounds : FreshBounds) (mode : Mode)
    (first : OracleComp (ModeSpec mode) X)
    (second : X → PqxdhDeploymentLaterServerGame.Reveal → OracleComp PostSpec Out)
    (runStep : ∀ created, LawEq (Prod.map id proj <$> (simulateQ (handlerWith setup codec route (reg₁ created))
        (PqxdhDeploymentSecrecy.wrap setup.source.crypto codec setup.serverKeyId bounds (asModeO mode first))).run
          (xinitial created (init₁ created)))
      ((simulateQ (handlerWith setup codec route (reg₂ created))
        (PqxdhDeploymentSecrecy.wrap setup.source.crypto codec setup.serverKeyId bounds (asModeO mode first))).run
          (xinitial created (init₂ created))))
    (runtime : A) :
    LawEq (outcomeMap proj <$> (laterWith setup codec route init₁ reg₁ post₁ ensureInit identityIndex bounds mode first
        second).run runtime)
      ((laterWith setup codec route init₂ reg₂ post₂ ensureInit identityIndex bounds mode first second).run runtime) := by
  rw [PqxdhDeploymentIdealLaterGame.laterWith_split, PqxdhDeploymentIdealLaterGame.laterWith_split, map_bind]
  refine LawEq.bind (LawEq.refl _) fun born => ?_
  rcases born with ⟨_ | created, after⟩
  · exact LawEq.of_eq (by simp only [map_pure]; rfl)
  · dsimp only
    rw [map_bind]
    simp only [laterTail_map proj post₁ post₂ postStep reveal]
    have bound := (runStep created).bind (f := laterTail post₂ created second id after)
      (g := laterTail post₂ created second id after) fun _ => LawEq.refl _
    rw [bind_map_left] at bound
    exact bound

end Transport

/-! ### The represent step for the later game -/

section Represent
variable {KemSK Γ : Type} {n : ℕ}
variable {ι : Type} {baseSpec : OracleSpec ι} {Reader Response A X Out : Type}
  (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
  (checks : Checks)

/-- The reveal does not see the service state of the backend. -/
theorem xreveal_mapBackend {S₁ S₂ : Type} (proj : S₁ → S₂) (created : PqxdhLiveServerConstruction.Created Unit)
    (x : XState KemSK (S₁ × Γ) n) : xreveal created (mapBackend proj x) = xreveal created x := rfl

/-- The real post phase runs on the deployment state only, so it commutes with every replacement of the service state. -/
theorem realPost_mapBackend {S₁ S₂ : Type} (proj : S₁ → S₂) (created : PqxdhLiveServerConstruction.Created Unit)
    (query : PostSpec.Domain) (x : XState KemSK (S₁ × Γ) n) :
    Prod.map id (mapBackend proj) <$> (realPost setup codec checks created query).run x =
      (realPost setup codec checks created query).run (mapBackend proj x) := by
  simp only [realPost, PqxdhDeploymentBackend.onBase, LazyOracleDiscard.StateLens.lift,
    PqxdhDeploymentBackend.baseLens, StateT.run, Functor.map_map]
  rfl

/-- The run phase of the represent step, per constructed Server (the step inside `PqxdhDeploymentSeedSplit.represent`): for a natural core and a service projection, the run with the first service, its final state read through the service projection, has the law of the run with the second service. -/
theorem represent_run
    (core : ∀ {S : Type}, SlotService S n → PqxdhLiveServerConstruction.Created Unit → RegImpl KemSK (S × Γ) n)
    (natural : CoreNatural core) {S₁ S₂ : Type} (inv : S₁ → Prop) (proj : S₁ → S₂)
    (svc₁ : SlotService S₁ n) (svc₂ : SlotService S₂ n) (related : ServiceProj inv proj svc₁ svc₂)
    (created : PqxdhLiveServerConstruction.Created Unit) {α : Type} (work : OracleComp Spec α)
    (state : XState KemSK (S₁ × Γ) n) (holds : inv state.backend.1) :
    LawEq (Prod.map id (mapBackend proj) <$> (simulateQ (handlerWith setup codec route (core svc₁ created)) work).run
        state)
      ((simulateQ (handlerWith setup codec route (core svc₂ created)) work).run (mapBackend proj state)) := by
  refine PqxdhDeploymentSeedSplit.lawEq_run_simulateQ_of_proj (handlerWith setup codec route (core svc₁ created))
    (handlerWith setup codec route (core svc₂ created)) (fun state => inv state.backend.1) (mapBackend proj)
    (fun query state holds => ?step) (fun query state holds => ?keeps) work state holds
  case step =>
    by_cases env : ∃ command : EnvQuery, query = .inr command.val
    · obtain ⟨⟨command, isEnv⟩, rfl⟩ := env
      cases command
      case create pin keyId => exact (natural inv proj svc₁ svc₂ related created ⟨.create pin keyId, trivial⟩ state holds).1
      case bundle owner => exact (natural inv proj svc₁ svc₂ related created ⟨.bundle owner, trivial⟩ state holds).1
      case accept raw => exact (natural inv proj svc₁ svc₂ related created ⟨.accept raw, trivial⟩ state holds).1
      case build session payload =>
        exact (natural inv proj svc₁ svc₂ related created ⟨.build session payload, trivial⟩ state holds).1
      case finish owner raw => exact (natural inv proj svc₁ svc₂ related created ⟨.finish owner raw, trivial⟩ state holds).1
      case hmac key message => exact (natural inv proj svc₁ svc₂ related created ⟨.hmac key message, trivial⟩ state holds).1
      all_goals exact isEnv.elim
    · exact LawEq.of_eq (PqxdhDeploymentSeedSplit.fixed_mapBackend setup codec route proj _ _ query
        (fun command same => env ⟨command, same⟩) state)
  case keeps =>
    by_cases env : ∃ command : EnvQuery, query = .inr command.val
    · obtain ⟨⟨command, isEnv⟩, rfl⟩ := env
      cases command
      case create pin keyId => exact (natural inv proj svc₁ svc₂ related created ⟨.create pin keyId, trivial⟩ state holds).2
      case bundle owner => exact (natural inv proj svc₁ svc₂ related created ⟨.bundle owner, trivial⟩ state holds).2
      case accept raw => exact (natural inv proj svc₁ svc₂ related created ⟨.accept raw, trivial⟩ state holds).2
      case build session payload =>
        exact (natural inv proj svc₁ svc₂ related created ⟨.build session payload, trivial⟩ state holds).2
      case finish owner raw => exact (natural inv proj svc₁ svc₂ related created ⟨.finish owner raw, trivial⟩ state holds).2
      case hmac key message => exact (natural inv proj svc₁ svc₂ related created ⟨.hmac key message, trivial⟩ state holds).2
      all_goals exact isEnv.elim
    · intro result member
      rw [PqxdhDeploymentSeedSplit.fixed_backend setup codec route _ query (fun command same => env ⟨command, same⟩) state
        result member]
      exact holds

/-- The represent step for the later game with the real post phase (the later form of `PqxdhDeploymentSeedSplit.represent`): for a natural core and a service projection, the later games with the first and the second service have the same law up to the service projection of the final state. The real post phase commutes with the projection (`realPost_mapBackend`), and the reveal does not see the service state (`xreveal_mapBackend`). -/
theorem represent_later
    (core : ∀ {S : Type}, SlotService S n → PqxdhLiveServerConstruction.Created Unit → RegImpl KemSK (S × Γ) n)
    (natural : CoreNatural core) {S₁ S₂ : Type} (inv : S₁ → Prop) (proj : S₁ → S₂)
    (svc₁ : SlotService S₁ n) (svc₂ : SlotService S₂ n) (related : ServiceProj inv proj svc₁ svc₂)
    (init : PqxdhLiveServerConstruction.Created Unit → S₁ × Γ) (initial : ∀ created, inv (init created).1)
    (ensureInit : StateT A ProbComp Bool) (identityIndex : ℕ) (bounds : FreshBounds) (mode : Mode)
    (first : OracleComp (ModeSpec mode) X)
    (second : X → PqxdhDeploymentLaterServerGame.Reveal → OracleComp PostSpec Out) (runtime : A) :
    LawEq (outcomeMap (mapBackend proj) <$> (laterWith setup codec route init (fun created => core svc₁ created)
        (realPost setup codec checks) ensureInit identityIndex bounds mode first second).run runtime)
      ((laterWith setup codec route (fun created => (proj (init created).1, (init created).2))
        (fun created => core svc₂ created) (realPost setup codec checks) ensureInit identityIndex bounds mode first
          second).run runtime) :=
  laterWith_proj setup codec route (mapBackend proj) init (fun created => (proj (init created).1, (init created).2))
    (fun created => core svc₁ created) (fun created => core svc₂ created) (realPost setup codec checks)
    (realPost setup codec checks) (fun created query x => realPost_mapBackend setup codec checks proj created query x)
    (fun created x => xreveal_mapBackend proj created x) ensureInit identityIndex bounds mode first second
    (fun created => represent_run setup codec route core natural inv proj svc₁ svc₂ related created _
      (xinitial created (init created)) (initial created))
    runtime

/-- The table and the split representations of the hidden-slot outputs in the later game, through the lazy representation (the later form of `PqxdhDeploymentSeedSplit.represent_split`): the later game with the S7 table service, read through the table's cache, and the later game with the split service, read through the joined table, have the same law. -/
theorem represent_split_later
    (core : ∀ {S : Type}, SlotService S n → PqxdhLiveServerConstruction.Created Unit → RegImpl KemSK (S × Γ) n)
    (natural : CoreNatural core) (init : PqxdhLiveServerConstruction.Created Unit → Γ)
    (ensureInit : StateT A ProbComp Bool) (identityIndex : ℕ) (bounds : FreshBounds) (mode : Mode)
    (first : OracleComp (ModeSpec mode) X)
    (second : X → PqxdhDeploymentLaterServerGame.Reveal → OracleComp PostSpec Out) (runtime : A) :
    LawEq (outcomeMap (mapBackend Prod.fst) <$> (laterWith setup codec route
        (fun created => (PqxdhRecordLiftLazyTable.initial, init created))
        (fun created => core PqxdhDeploymentSeedSplit.tableService created) (realPost setup codec checks) ensureInit
        identityIndex bounds mode first second).run runtime)
      (outcomeMap (mapBackend PqxdhDeploymentSeedSplit.joinTable) <$> (laterWith setup codec route
        (fun created => ((∅, ∅), init created)) (fun created => core PqxdhDeploymentSeedSplit.splitService created)
        (realPost setup codec checks) ensureInit identityIndex bounds mode first second).run runtime) := by
  have table := represent_later setup codec route checks core natural (fun _ => True) Prod.fst
    PqxdhDeploymentSeedSplit.tableService PqxdhDeploymentSeedSplit.lazyService
    PqxdhDeploymentSeedSplit.table_service_proj (fun created => (PqxdhRecordLiftLazyTable.initial, init created))
    (fun _ => trivial) ensureInit identityIndex bounds mode first second runtime
  have split := represent_later setup codec route checks core natural PqxdhDeploymentSeedSplit.BothOrNeither
    PqxdhDeploymentSeedSplit.joinTable PqxdhDeploymentSeedSplit.splitService PqxdhDeploymentSeedSplit.lazyService
    PqxdhDeploymentSeedSplit.split_service_proj (fun created => ((∅, ∅), init created)) (fun _ _ => rfl)
    ensureInit identityIndex bounds mode first second runtime
  have tableInit : (fun created => (Prod.fst (PqxdhRecordLiftLazyTable.initial
      (spec := PqxdhDeploymentSeedSplit.OutputSpec n)), init created)) =
      (fun created => (PqxdhDeploymentSeedSplit.joinTable ((∅, ∅) : (PqxdhDeploymentSeedSplit.MaterialSpec n).QueryCache ×
        (PqxdhRecordLiftWorld.SeedSpec n).QueryCache), init created)) := by
    funext created
    congr 1
  simp only [tableInit] at table
  exact table.trans split.symm

end Represent

/-! ### Seed relocation for the later game -/

section GameMove
variable {KemSK : Type} {n : ℕ}
variable {ι : Type} {baseSpec : OracleSpec ι} {Reader Response A X Out : Type}
  (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
  (checks : Checks)

/-- The real post phase runs on the deployment state only, so it commutes with moving the seeds. -/
theorem realPost_moveSeeds {M Γ : Type} (created : PqxdhLiveServerConstruction.Created Unit) (query : PostSpec.Domain)
    (x : XState KemSK ((M × (PqxdhRecordLiftWorld.SeedSpec n).QueryCache) × (Alloc Coord n × Γ)) n) :
    Prod.map id moveSeeds <$> (realPost setup codec checks created query).run x =
      (realPost setup codec checks created query).run (moveSeeds x) := by
  simp only [realPost, PqxdhDeploymentBackend.onBase, LazyOracleDiscard.StateLens.lift,
    PqxdhDeploymentBackend.baseLens, StateT.run, Functor.map_map]
  rfl

/-- Seed relocation for the later game with the real post phase (the later form of `PqxdhDeploymentIdealKeys.game_moveSeeds`): for slot programs that do not read or write the seed table, the later game with a slot core whose service keeps the seeds in its backend, read with the seeds moved into the extended state, is exactly the later game with the slot core whose service keeps them in the extended state's seed table. -/
theorem game_moveSeeds_later {M Γ : Type} (prog : PqxdhLiveServerConstruction.Created Unit → SlotProgram KemSK Γ n)
    (frame : ∀ created query, SlotFrame seedPut (prog created query))
    (svc : SlotService (M × (PqxdhRecordLiftWorld.SeedSpec n).QueryCache) n)
    (init : PqxdhLiveServerConstruction.Created Unit → M × (Alloc Coord n × Γ)) (ensureInit : StateT A ProbComp Bool)
    (identityIndex : ℕ) (bounds : FreshBounds) (mode : Mode) (first : OracleComp (ModeSpec mode) X)
    (second : X → PqxdhDeploymentLaterServerGame.Reveal → OracleComp PostSpec Out) (runtime : A) :
    outcomeMap moveSeeds <$> (laterWith setup codec route (fun created => (((init created).1, ∅), (init created).2))
        (fun created => slotCore prog svc created) (realPost setup codec checks) ensureInit identityIndex bounds mode
          first second).run runtime =
      (laterWith setup codec route init (fun created => slotCoreX prog svc created) (realPost setup codec checks)
        ensureInit identityIndex bounds mode first second).run runtime := by
  refine laterWith_map setup codec route moveSeeds _ init _ _ (realPost setup codec checks) (realPost setup codec checks)
    (fun created query x => ?step) (fun _ => rfl) (fun created query x => realPost_moveSeeds setup codec checks created
      query x) (fun _ _ => rfl) ensureInit identityIndex bounds mode first second runtime
  by_cases env : ∃ command : EnvQuery, query = .inr command.val
  · obtain ⟨⟨command, isEnv⟩, rfl⟩ := env
    cases command
    case create pin keyId =>
      exact PqxdhDeploymentIdealKeys.slotCore_moveSeeds prog frame svc created ⟨.create pin keyId, trivial⟩ x
    case bundle owner => exact PqxdhDeploymentIdealKeys.slotCore_moveSeeds prog frame svc created ⟨.bundle owner, trivial⟩ x
    case accept raw => exact PqxdhDeploymentIdealKeys.slotCore_moveSeeds prog frame svc created ⟨.accept raw, trivial⟩ x
    case build session payload =>
      exact PqxdhDeploymentIdealKeys.slotCore_moveSeeds prog frame svc created ⟨.build session payload, trivial⟩ x
    case finish owner raw =>
      exact PqxdhDeploymentIdealKeys.slotCore_moveSeeds prog frame svc created ⟨.finish owner raw, trivial⟩ x
    case hmac key message =>
      exact PqxdhDeploymentIdealKeys.slotCore_moveSeeds prog frame svc created ⟨.hmac key message, trivial⟩ x
    all_goals exact isEnv.elim
  · exact PqxdhDeploymentIdealKeys.fixed_moveSeeds setup codec route _ _ query (fun command same => env ⟨command, same⟩) x

end GameMove

/-! ### A parameter in the backend of the later game -/

section Param
variable {KemSK Bk P : Type} {n : ℕ}
variable {ι : Type} {baseSpec : OracleSpec ι} {Reader Response A X Out : Type}
  (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)

/-- The post phase of the native game with the parameterized registration handler, from a state holding the parameter, is the post phase with the handler at that parameter, with the parameter added. -/
theorem postNative_param (regs : P → RegImpl KemSK Bk n) (p : P) (query : PostSpec.Domain)
    (y : XState KemSK Bk n) :
    (postNative setup codec route (paramReg regs) query).run (withX p y) =
      Prod.map id (withX p) <$> (postNative setup codec route (regs p) query).run y := by
  simp only [postNative, QueryImpl.apply_compose]
  exact PqxdhDeploymentEnvironmentDraw.simulateQ_embed _ _ (withX p)
    (fun query state => PqxdhDeploymentEnvironmentDraw.handlerWith_param setup codec route regs p query state) _ y

/-- The later game with the parameterized registration handler, its own post phase and the parameter `p` in the initial backend is the later game with the handler at `p` and its post phase, with `p` added to the final backend (the later form of `PqxdhDeploymentEnvironmentDraw.gameWith_param`). -/
theorem laterWith_param (init : PqxdhLiveServerConstruction.Created Unit → Bk)
    (regs : P → PqxdhLiveServerConstruction.Created Unit → RegImpl KemSK Bk n) (p : P)
    (ensureInit : StateT A ProbComp Bool) (identityIndex : ℕ) (bounds : FreshBounds) (mode : Mode)
    (first : OracleComp (ModeSpec mode) X)
    (second : X → PqxdhDeploymentLaterServerGame.Reveal → OracleComp PostSpec Out) (runtime : A) :
    (laterWith setup codec route (fun created => (p, init created)) (fun created => paramReg (fun q => regs q created))
        (fun created => postNative setup codec route (paramReg (fun q => regs q created))) ensureInit identityIndex
        bounds mode first second).run runtime =
      outcomeMap (withX p) <$> (laterWith setup codec route init (regs p)
        (fun created => postNative setup codec route (regs p created)) ensureInit identityIndex bounds mode first
          second).run runtime :=
  (laterWith_map setup codec route (withX p) init (fun created => (p, init created)) (regs p)
    (fun created => paramReg (fun q => regs q created)) (fun created => postNative setup codec route (regs p created))
    (fun created => postNative setup codec route (paramReg (fun q => regs q created)))
    (fun created query x => (PqxdhDeploymentEnvironmentDraw.handlerWith_param setup codec route
      (fun q => regs q created) p query x).symm)
    (fun _ => rfl)
    (fun created query x => (postNative_param setup codec route (fun q => regs q created) p query x).symm)
    (fun _ _ => rfl) ensureInit identityIndex bounds mode first second runtime).symm

end Param

/-! ### C6 with parameters drawn at startup -/

section Draw
variable {KemSK Bk : Type} {n : ℕ}
variable {ι : Type} {baseSpec : OracleSpec ι} {Reader Response A X Out : Type}
  (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)

/-- The two phases of the later record world from any World state (`PqxdhDeploymentEnvironmentJoin.run_split` from `w₀`): the World run of the first adversary, then the post phase on the same environment and World from the run's final states. -/
theorem run_split_from {R : Type} (env : Environment n (EnvState KemSK Bk)) (serverKid : Std.U64)
    (bounds : FreshBounds) (mode : Mode) (reveal : EnvState KemSK Bk → R) (first : OracleComp (ModeSpec mode) X)
    (second : X → R → OracleComp PostSpec Out) (w₀ : PqxdhRecordLiftWorld.State n) :
    (simulateQ (PqxdhRecordLiftWorld.handler setup codec route)
        (PqxdhRecordLiftLater.program env setup.source.crypto codec serverKid bounds mode reveal first second)).run w₀ =
      (simulateQ (PqxdhRecordLiftWorld.handler setup codec route)
        (PqxdhRecordLiftInterface.program env setup.source.crypto codec serverKid bounds mode first)).run w₀ >>=
          fun result => match result.1 with
          | none => pure (none, result.2)
          | some (created, (output, ledger), state) =>
              (fun later => (some (created, (later.1.1, ledger), later.1.2), later.2)) <$>
                (simulateQ (PqxdhRecordLiftWorld.handler setup codec route)
                  ((PqxdhRecordLiftLater.post env (second output (reveal state))).run state)).run result.2 := by
  simp only [PqxdhRecordLiftLater.program, simulateQ_bind, StateT.run_bind]
  refine bind_congr fun result => ?_
  rcases result with ⟨_ | ⟨created, ⟨output, ledger⟩, state⟩, world⟩
  · simp only [simulateQ_pure, StateT.run_pure]
  · simp only [bind_pure_comp, simulateQ_map, StateT.run_map]

/-- C6 from a World state that differs from the initial World only in its counts (the later form of `PqxdhDeploymentEnvironmentDraw.join_from`; `PqxdhDeploymentEnvironmentJoin.join_later` is its case at the initial World): the LQ-F later game with the registration handler and its own post phase has the law of the later record world's program with the environment run from that World state, reassembled. -/
theorem join_later_from (init : PqxdhLiveServerConstruction.Created Unit → Bk)
    (reg : PqxdhLiveServerConstruction.Created Unit → RegImpl KemSK Bk n) (env : Environment n (EnvState KemSK Bk))
    (ensureInit : StateT A ProbComp Bool) (identityIndex : ℕ) (runtime : A)
    (born : env.start = PqxdhDeploymentEnvironment.start setup ensureInit identityIndex runtime init)
    (inv : EnvState KemSK Bk → PqxdhRecordLiftWorld.State n → Prop) (stable : Stable inv)
    (startInv : ∀ created, inv (PqxdhDeploymentEnvironment.envInitial created (init created))
      (initialized created (PqxdhRecordLiftWorld.initial (n := n))))
    (splits : ∀ created, Splits created (reg created) env.step inv)
    (bounds : FreshBounds) (mode : Mode) (first : OracleComp (ModeSpec mode) X)
    (second : X → PqxdhDeploymentLaterServerGame.Reveal → OracleComp PostSpec Out)
    (w₀ : PqxdhRecordLiftWorld.State n) (fresh₀ : uncount w₀ = uncount (PqxdhRecordLiftWorld.initial (n := n))) :
    LawEq ((laterWith setup codec route init reg (fun created => postNative setup codec route (reg created)) ensureInit
        identityIndex bounds mode first second).run' runtime)
      (joined <$> (simulateQ (PqxdhRecordLiftWorld.handler setup codec route)
        (PqxdhRecordLiftLater.program env setup.source.crypto codec setup.serverKeyId bounds mode envReveal first
          second)).run w₀) := by
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
    (simulateQ PqxdhRecordLiftInterface.coinLift env.start)).run w₀
  have counted := PqxdhDeploymentEnvironmentJoin.coins_world setup codec route env.start w₀
  have startupFst : Prod.fst <$> startup = env.start := by
    have forgot := congrArg (fun work => Prod.fst <$> work) counted
    simpa only [Functor.map_map, Prod.map_fst, id_eq, Function.comp_def, id_map'] using forgot
  rw [nativeSide, ← startupFst, bind_map_left, run_split_from]
  simp only [PqxdhRecordLiftInterface.program, simulateQ_bind, StateT.run_bind, map_bind, bind_assoc]
  refine LawEq.symm (PqxdhDeploymentSeedSplit.LawEq.bind_support _ fun step member => ?_)
  have fresh : uncount step.2 = uncount (PqxdhRecordLiftWorld.initial (n := n)) := by
    have inMapped : Prod.map id uncount step ∈ support (Prod.map id uncount <$> startup) := by
      rw [support_map]
      exact ⟨step, member, rfl⟩
    rw [counted, support_map] at inMapped
    obtain ⟨_, _, same⟩ := inMapped
    exact (congrArg Prod.snd same).symm.trans fresh₀
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
    rw [← PqxdhDeploymentEnvironmentJoin.merge_initial created (init created) w fresh]
    refine PqxdhDeploymentEnvironmentJoin.run_join_bind setup codec route env (reg created) created inv stable
      (splits created) wrapped _ _ (PqxdhDeploymentEnvironmentJoin.good_initial created (init created) w fresh)
      (stable _ _ _ (PqxdhDeploymentEnvironmentJoin.initialized_view created w fresh) (startInv created))
      _ _ (fun result good holds => ?_)
    rcases result with ⟨⟨⟨output, ledger⟩, finalEnv⟩, finalWorld⟩
    dsimp only
    rw [PqxdhDeploymentEnvironmentJoin.reveal_merge created finalEnv finalWorld good]
    have posted := (PqxdhDeploymentEnvironmentJoin.run_join setup codec route env (reg created) created inv stable
      (splits created) (simulateQ PqxdhDeploymentLater.postEmbed (second output (envReveal finalEnv))) finalEnv
      finalWorld good holds).map
        (fun result => some (PqxdhRegistrationJointServerBirth.encode created, result.1, ledger, result.2))
    simp only [Functor.map_map] at posted
    simp only [postNative, QueryImpl.simulateQ_compose, map_pure, bind_pure_comp, Functor.map_map,
      PqxdhRecordLiftLater.post]
    exact posted

/-- The later record world's program for an environment whose startup draws a parameter first is the counted draw followed by the program of the environment with the actual Server constructor at the drawn parameter and the same step. -/
theorem later_program_draw {P R : Type} (draw : ProbComp P) (init : P → PqxdhLiveServerConstruction.Created Unit → Bk)
    (env : Environment n (EnvState KemSK Bk)) (ensureInit : StateT A ProbComp Bool) (identityIndex : ℕ) (runtime : A)
    (born : env.start = draw >>= fun p => PqxdhDeploymentEnvironment.start setup ensureInit identityIndex runtime (init p))
    (crypto : Pqxdh.Crypto) (serverKid : Std.U64) (bounds : FreshBounds) (mode : Mode)
    (reveal : EnvState KemSK Bk → R) (first : OracleComp (ModeSpec mode) X) (second : X → R → OracleComp PostSpec Out) :
    PqxdhRecordLiftLater.program env crypto codec serverKid bounds mode reveal first second =
      simulateQ PqxdhRecordLiftInterface.coinLift draw >>= fun p =>
        PqxdhRecordLiftLater.program ⟨PqxdhDeploymentEnvironment.start setup ensureInit identityIndex runtime (init p),
          env.step⟩ crypto codec serverKid bounds mode reveal first second := by
  simp only [PqxdhRecordLiftLater.program, PqxdhRecordLiftInterface.program, born, simulateQ_bind, bind_assoc]
  rfl

/-- C6 for an environment that draws parameters at startup (the later form of `PqxdhDeploymentEnvironmentDraw.join_draw`): if the environment's startup is the draw `draw` followed by the actual Server constructor with the initial backend `init p`, and for every drawn `p` the stable admissibility predicate `inv p` holds at the constructed Server's initial environment state and the initialized fresh World and the environment splits every constructed Server's registration handler `reg p` relative to `inv p`, then the draw followed by the LQ-F later game with `init p`, `reg p` and its own post phase and the later record world with that environment and the environment's reveal have the same law of the Server's public data, the second adversary's output, the run-phase ledger and the full reassembled final state. -/
theorem join_later_draw {P : Type} (draw : ProbComp P) (init : P → PqxdhLiveServerConstruction.Created Unit → Bk)
    (reg : P → PqxdhLiveServerConstruction.Created Unit → RegImpl KemSK Bk n) (env : Environment n (EnvState KemSK Bk))
    (ensureInit : StateT A ProbComp Bool) (identityIndex : ℕ) (runtime : A)
    (born : env.start = draw >>= fun p => PqxdhDeploymentEnvironment.start setup ensureInit identityIndex runtime (init p))
    (inv : P → EnvState KemSK Bk → PqxdhRecordLiftWorld.State n → Prop) (stable : ∀ p, Stable (inv p))
    (startInv : ∀ p created, inv p (PqxdhDeploymentEnvironment.envInitial created (init p created))
      (initialized created (PqxdhRecordLiftWorld.initial (n := n))))
    (splits : ∀ p created, Splits created (reg p created) env.step (inv p))
    (bounds : FreshBounds) (mode : Mode) (first : OracleComp (ModeSpec mode) X)
    (second : X → PqxdhDeploymentLaterServerGame.Reveal → OracleComp PostSpec Out) :
    LawEq (draw >>= fun p => (laterWith setup codec route (init p) (reg p)
        (fun created => postNative setup codec route (reg p created)) ensureInit identityIndex bounds mode first
          second).run' runtime)
      (joined <$> PqxdhRecordLiftLater.run setup codec route env setup.serverKeyId bounds mode envReveal first
        second) := by
  let drawn := (simulateQ (PqxdhRecordLiftWorld.handler setup codec route)
    (simulateQ PqxdhRecordLiftInterface.coinLift draw)).run (PqxdhRecordLiftWorld.initial (n := n))
  have counted := PqxdhDeploymentEnvironmentJoin.coins_world setup codec route draw
    (PqxdhRecordLiftWorld.initial (n := n))
  have drawnFst : Prod.fst <$> drawn = draw := by
    have forgot := congrArg (fun work => Prod.fst <$> work) counted
    simpa only [Functor.map_map, Prod.map_fst, id_eq, Function.comp_def, id_map'] using forgot
  have lhs : (draw >>= fun p => (laterWith setup codec route (init p) (reg p)
      (fun created => postNative setup codec route (reg p created)) ensureInit identityIndex bounds mode first
        second).run' runtime) = drawn >>= fun step => (laterWith setup codec route (init step.1) (reg step.1)
          (fun created => postNative setup codec route (reg step.1 created)) ensureInit identityIndex bounds mode first
            second).run' runtime := by
    rw [← drawnFst, bind_map_left]
  rw [lhs, PqxdhRecordLiftLater.run, later_program_draw setup codec draw init env ensureInit identityIndex runtime born]
  simp only [simulateQ_bind, StateT.run_bind, map_bind]
  refine PqxdhDeploymentSeedSplit.LawEq.bind_support _ fun step member => ?_
  have fresh : uncount step.2 = uncount (PqxdhRecordLiftWorld.initial (n := n)) := by
    have inMapped : Prod.map id uncount step ∈ support (Prod.map id uncount <$> drawn) := by
      rw [support_map]
      exact ⟨step, member, rfl⟩
    rw [counted, support_map] at inMapped
    obtain ⟨_, _, same⟩ := inMapped
    exact (congrArg Prod.snd same).symm
  exact join_later_from setup codec route (init step.1) (reg step.1)
    ⟨PqxdhDeploymentEnvironment.start setup ensureInit identityIndex runtime (init step.1), env.step⟩ ensureInit
    identityIndex runtime rfl (inv step.1) (stable step.1) (startInv step.1) (splits step.1) bounds mode first second
    step.2 fresh

/-- C6 for a parameter drawn at startup (the later form of `PqxdhDeploymentEnvironmentDraw.join_param`): if, at every parameter `p`, the stable admissibility predicate `inv p` holds at the constructed Server's initial environment state and the initialized fresh World and the environment step `steps p` splits every constructed Server's registration handler `regs p` relative to `inv p`, then the draw followed by the LQ-F later game with `regs p` and its own post phase (the parameter added to the final backend) and the later record world with the environment that draws the parameter at startup (`paramEnv`) and the environment's reveal have the same law of the Server's public data, the second adversary's output, the run-phase ledger and the full reassembled final state. -/
theorem join_later_param {P : Type} (draw : ProbComp P) (init : PqxdhLiveServerConstruction.Created Unit → Bk)
    (regs : P → PqxdhLiveServerConstruction.Created Unit → RegImpl KemSK Bk n) (steps : P → EnvStep KemSK Bk n)
    (ensureInit : StateT A ProbComp Bool) (identityIndex : ℕ) (runtime : A)
    (inv : P → EnvState KemSK Bk → PqxdhRecordLiftWorld.State n → Prop) (stable : ∀ p, Stable (inv p))
    (startInv : ∀ p created, inv p (PqxdhDeploymentEnvironment.envInitial created (init created))
      (initialized created (PqxdhRecordLiftWorld.initial (n := n))))
    (splits : ∀ p created, Splits created (regs p created) (steps p) (inv p))
    (bounds : FreshBounds) (mode : Mode) (first : OracleComp (ModeSpec mode) X)
    (second : X → PqxdhDeploymentLaterServerGame.Reveal → OracleComp PostSpec Out) :
    LawEq (draw >>= fun p => (fun outcome => outcome.map fun value => (value.1, value.2.1, value.2.2.1,
        withX p value.2.2.2)) <$>
        (laterWith setup codec route init (regs p) (fun created => postNative setup codec route (regs p created))
          ensureInit identityIndex bounds mode first second).run' runtime)
      (joined <$> PqxdhRecordLiftLater.run setup codec route
        (paramEnv setup draw steps ensureInit identityIndex runtime init) setup.serverKeyId bounds mode envReveal first
          second) := by
  have drawn := join_later_draw setup codec route draw (fun p created => (p, init created))
    (fun _ created => paramReg (fun q => regs q created)) (paramEnv setup draw steps ensureInit identityIndex runtime init)
    ensureInit identityIndex runtime rfl (fun _ => paramInv inv)
    (fun _ => PqxdhDeploymentEnvironmentDraw.stable_param inv stable) (fun p created => startInv p created)
    (fun _ created => PqxdhDeploymentEnvironmentDraw.splits_param created (fun q => regs q created) steps inv
      (fun q => splits q created))
    bounds mode first second
  refine LawEq.trans (LawEq.of_eq ?_) drawn
  refine bind_congr fun p => ?_
  rw [StateT.run'_eq, StateT.run'_eq, laterWith_param setup codec route init regs p, Functor.map_map, Functor.map_map]
  rfl

end Draw

/-! ### The seed deferral with lists of points for the later game -/

section DeferList
variable {KemSK Bk : Type} {n : ℕ}
variable {ι : Type} {baseSpec : OracleSpec ι} {Reader Response A X Out : Type}
  (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)

/-- The seed deferral with lists of points under an invariant for the LQ-F later game (the later form of `PqxdhDeploymentIdealDefer.defer_seeds`, with the continuation `PqxdhDeploymentFinishErasure.laterTail`): if each constructed Server's registration handler is, from states satisfying the invariant, a pointed handler followed by the completion of the reported seed-table points, the invariant holds initially and is kept by the fixed steps, and the post phase commutes with seed completions, then the later games with the handler and with its erased handler have the same law of the Server's public data, the second adversary's output, the ledger and the final state with the seed table emptied. The post phase need not keep the invariant: `PqxdhDeploymentIdealDefer.discard_erase_list` uses it only inside the run and asks only blindness of the continuation. -/
theorem defer_seeds_later (inv : XState KemSK Bk n → Prop)
    (pair : PqxdhLiveServerConstruction.Created Unit → PointedSeeds inv)
    (init : PqxdhLiveServerConstruction.Created Unit → Bk) (initial : ∀ created, inv (xinitial created (init created)))
    (fixedKeeps : ∀ created (query : Spec.Domain), (∀ command : EnvQuery, query ≠ .inr command.val) →
      ∀ x, inv x → ∀ r ∈ support ((handlerWith setup codec route (pair created).reg query).run x), inv r.2)
    (postWith : PqxdhLiveServerConstruction.Created Unit →
      QueryImpl PostSpec (StateT (XState KemSK Bk n) ProbComp))
    (postCommutes : ∀ created query, Commutes seedLens (postWith created query))
    (ensureInit : StateT A ProbComp Bool) (identityIndex : ℕ) (bounds : FreshBounds) (mode : Mode)
    (first : OracleComp (ModeSpec mode) X)
    (second : X → PqxdhDeploymentLaterServerGame.Reveal → OracleComp PostSpec Out) (runtime : A) :
    LawEq (outcomeMap seedFree <$> (laterWith setup codec route init (fun created => (pair created).reg) postWith
        ensureInit identityIndex bounds mode first second).run runtime)
      (outcomeMap seedFree <$> (laterWith setup codec route init (fun created => (pair created).erased) postWith
        ensureInit identityIndex bounds mode first second).run runtime) := by
  simp only [laterWith, StateT.run, map_bind]
  refine LawEq.bind (LawEq.refl _) fun born => ?_
  rcases born with ⟨_ | created, after⟩
  · exact LawEq.refl _
  · have erased := PqxdhDeploymentIdealDefer.discard_erase_list seedLens inv
      (handlerWith setup codec route (pair created).reg)
      (pointedWithSeeds setup codec route (pair created)) (fun query x holds => ?factor)
      (fun query x holds => ?keeps) (fun query => ?oblivious)
      (laterTail postWith created second seedFree after)
      (PqxdhDeploymentFinishErasure.laterTail_blind postWith postCommutes (fun _ _ _ => rfl) created second seedFree
        PqxdhDeploymentSeedSplit.seedFree_set after)
      (PqxdhDeploymentSecrecy.wrap setup.source.crypto codec setup.serverKeyId bounds (asModeO mode first))
      (xinitial created (init created)) (initial created)
    case factor =>
      rcases query with coin | command
      · exact LawEq.of_eq (by simp only [pointedWithSeeds, handlerWith, StateT.run_map, bind_map_left,
          PqxdhDeploymentIdealDefer.completeList, map_pure, Prod.mk.eta, bind_pure])
      · cases command
        case create pin keyId => exact (pair created).factor _ x holds
        case bundle owner => exact (pair created).factor _ x holds
        case accept raw => exact (pair created).factor _ x holds
        case build session payload => exact (pair created).factor _ x holds
        case finish owner raw => exact (pair created).factor _ x holds
        case hmac key message => exact (pair created).factor _ x holds
        all_goals exact LawEq.of_eq (by simp only [pointedWithSeeds, StateT.run_map, bind_map_left,
          PqxdhDeploymentIdealDefer.completeList, map_pure, Prod.mk.eta, bind_pure])
    case keeps =>
      have fixedCase : ∀ (query' : Spec.Domain), (∀ command : EnvQuery, query' ≠ .inr command.val) →
          ∀ r ∈ support ((((·, []) <$> handlerWith setup codec route (pair created).reg query' :
            StateT (XState KemSK Bk n) ProbComp (Spec.Range query' × List (PqxdhRecordLiftInterface.Slot n)))).run x >>=
              fun r => (r.1.1, ·) <$> PqxdhDeploymentIdealDefer.completeList seedLens r.1.2 r.2), inv r.2 := by
        intro query' notEnv r member
        simp only [StateT.run_map, bind_map_left, PqxdhDeploymentIdealDefer.completeList, map_pure, support_bind,
          support_pure, Set.mem_iUnion, Set.mem_singleton_iff] at member
        obtain ⟨inner, innerMember, rfl⟩ := member
        exact fixedKeeps created query' notEnv x holds inner innerMember
      rcases query with coin | command
      · exact fixedCase _ fun _ same => by cases same
      · cases command
        case create pin keyId => exact (pair created).keeps ⟨.create pin keyId, trivial⟩ x holds
        case bundle owner => exact (pair created).keeps ⟨.bundle owner, trivial⟩ x holds
        case accept raw => exact (pair created).keeps ⟨.accept raw, trivial⟩ x holds
        case build session payload =>
          exact (pair created).keeps ⟨.build session payload, trivial⟩ x holds
        case finish owner raw => exact (pair created).keeps ⟨.finish owner raw, trivial⟩ x holds
        case hmac key message => exact (pair created).keeps ⟨.hmac key message, trivial⟩ x holds
        all_goals exact fixedCase _ (fun command same => by
          cases command with | mk command isEnv => cases same; exact isEnv.elim)
    case oblivious =>
      have fixedCase : ∀ (query' : Spec.Domain), (∀ command : EnvQuery, query' ≠ .inr command.val) →
          Commutes seedLens (Prod.fst <$> ((·, []) <$> handlerWith setup codec route (pair created).reg query' :
            StateT (XState KemSK Bk n) ProbComp (Spec.Range query' × List (PqxdhRecordLiftInterface.Slot n)))) := by
        intro query' notEnv
        rw [Functor.map_map]
        simpa only [id_map'] using PqxdhDeploymentBackend.fixed_commute_seed setup codec route _ query' notEnv
      rcases query with coin | command
      · exact fixedCase _ fun _ same => by cases same
      · cases command
        case create pin keyId => exact (pair created).oblivious ⟨.create pin keyId, trivial⟩
        case bundle owner => exact (pair created).oblivious ⟨.bundle owner, trivial⟩
        case accept raw => exact (pair created).oblivious ⟨.accept raw, trivial⟩
        case build session payload => exact (pair created).oblivious ⟨.build session payload, trivial⟩
        case finish owner raw => exact (pair created).oblivious ⟨.finish owner raw, trivial⟩
        case hmac key message => exact (pair created).oblivious ⟨.hmac key message, trivial⟩
        all_goals exact fixedCase _ (fun command same => by
          cases command with | mk command isEnv => cases same; exact isEnv.elim)
    rw [PqxdhDeploymentIdealDefer.pointedWithSeeds_erased] at erased
    simp only [map_bind, map_pure, outcomeMap, Option.map_some]
    exact erased

end DeferList

end BeaconcryptCore.Computational.PqxdhDeploymentIdealLater

-- Axiom guards (generated)

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealLater.laterTail_map' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealLater.laterTail_map

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealLater.laterWith_map' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealLater.laterWith_map

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealLater.laterWith_proj' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealLater.laterWith_proj

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealLater.xreveal_mapBackend' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealLater.xreveal_mapBackend

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealLater.realPost_mapBackend' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealLater.realPost_mapBackend

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealLater.represent_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealLater.represent_run

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealLater.represent_later' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealLater.represent_later

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealLater.represent_split_later' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealLater.represent_split_later

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealLater.realPost_moveSeeds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealLater.realPost_moveSeeds

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealLater.game_moveSeeds_later' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealLater.game_moveSeeds_later

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealLater.postNative_param' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealLater.postNative_param

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealLater.laterWith_param' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealLater.laterWith_param

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealLater.run_split_from' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealLater.run_split_from

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealLater.join_later_from' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealLater.join_later_from

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealLater.later_program_draw' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealLater.later_program_draw

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealLater.join_later_draw' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealLater.join_later_draw

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealLater.join_later_param' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealLater.join_later_param

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealLater.defer_seeds_later' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealLater.defer_seeds_later
