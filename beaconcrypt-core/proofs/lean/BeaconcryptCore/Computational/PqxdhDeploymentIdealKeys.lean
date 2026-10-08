-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhDeploymentIdealErase

/-!
# The first-touch split of the ideal registration's hidden slots (CE-11b, unit U2)

The first steps of the split chain of CE-11b design-v2 section 5.2 for the C7-erased ideal registration `PqxdhDeploymentIdealSteps.idealCoreErased`, pointwise in the target `t` and the challenger's draws `p`, composed with C7 (`PqxdhDeploymentIdealErase.erase_ideal`).

- `represent_ideal` is CE-11a's `PqxdhDeploymentSeedSplit.represent_split` at the C7-erased ideal core (its naturality premise is `idealCoreErased_natural`): the game with item 2's persistent lazy table, read through the table's cache, and the game with CE-11a's split service (material and seed of a slot, each lazily sampled at the slot's first touch), read through the joined table, have the same law.
- Every command of the ideal registration's slot program, with any hidden services, keeps the extended state's seed table whatever it holds (`idealProg_seedFrame`; `seedPut` replaces the seed table).
- Seed relocation (generic): `slotCoreX prog svc` is the slot core whose slot service keeps its material in the backend and its seeds in the extended state's seed table (`XState.seeds`, where the record world's seeds are merged by `PqxdhDeploymentEnvironmentJoin.merge`); for slot programs that keep the seed table, the game with `slotCore prog svc` (seeds in the service state), read with the seeds moved into the extended state (`moveSeeds`), is exactly the game with `slotCoreX prog svc` (`slotCore_moveSeeds`, `game_moveSeeds`). `seed_move` is the instance at the C7-erased ideal core and the split service; its right side is the first-touch split form `idealSplitX t p`, on the backend `SplitBk` of `PqxdhDeploymentIdealSteps`.
- `ideal_to_splitX` composes C7, the represent step and the seed relocation: the common deployment experiment with the ideal registration `idealReg t p` and with `idealSplitX t p` have the same law of the Server's public data, the adversary's output, the ledger and `splitView` of the final state (the native deployment state with the CTX cache emptied, the allocator, the ideal backend, the LQ-F snapshot and the ephemeral log).

The rest of the chain of design-v2 section 5.2 is not in this module: the kernel identities with seed reads conditional on the hidden installs, the deferral of the seed draws from the first touch to the hidden installs (the final split form), the fact that a slot's seed is present exactly when it carries a hidden install (F4, `seed_at_install`), and their composition `ideal_to_split`.

These are equalities of programs and in law of lazily sampled tables. They charge nothing and make no security claim.
-/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open PqxdhRefinement

set_option autoImplicit false

namespace BeaconcryptCore.Computational.PqxdhDeploymentIdealKeys
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhDeploymentBackend (XState RegImpl ctxLens seedLens handlerWith gameWith xinitial)
open PqxdhDeploymentIdealSlots (Coord SlotSpec SlotProgram slotCore detach attach)
open PqxdhDeploymentIdealSteps (realRegAt onSlots liftS)
open PqxdhDeploymentIdealErase (SlotFrame readAt)
open PqxdhRegistrationJointKemSecondEntry (Alloc slotImpl emptyAlloc)
open PqxdhDeploymentSeedSplit (SlotService MaterialSpec mapBackend joinTable splitService)
open PqxdhDeploymentFinishErasure (outcomeMap fullX)
open LazyOracleDiscard (Commutes StateLens CacheLens LawEq)
open PqxdhRecordLiftInterface (EnvQuery EnvSpec)

variable {KemSK : Type} {n : ℕ}

/-! ### Slot cores with the seeds in the extended state -/

section CoreX
variable {M Γ : Type}

/-- The seed table of the extended state replaced. -/
def seedPut {Bk : Type} (x : XState KemSK Bk n) (c : (PqxdhRecordLiftWorld.SeedSpec n).QueryCache) : XState KemSK Bk n :=
  { x with seeds := c }

/-- The slot program's state inside the state of a slot core with the seeds in the extended state: the backend without the material and the allocator, and an empty seed table (slot programs do not read it). -/
def detachX (x : XState KemSK (M × (Alloc Coord n × Γ)) n) : XState KemSK Γ n :=
  ⟨x.base, x.backend.2.2, ∅, x.snap, x.log⟩

/-- A state of a slot core with the seeds in the extended state, from a slot program's state, an allocator, and a material and seed state. -/
def attachX (y : XState KemSK Γ n) (a : Alloc Coord n) (s : M × (PqxdhRecordLiftWorld.SeedSpec n).QueryCache) :
    XState KemSK (M × (Alloc Coord n × Γ)) n :=
  ⟨y.base, (s.1, (a, y.backend)), s.2, y.snap, y.log⟩

/-- A registration core from slot programs whose slot service keeps its material in the backend and its seeds in the extended state's seed table (`XState.seeds`, where the record world's seeds are merged). -/
noncomputable def slotCoreX (prog : PqxdhLiveServerConstruction.Created Unit → SlotProgram KemSK Γ n)
    (svc : SlotService (M × (PqxdhRecordLiftWorld.SeedSpec n).QueryCache) n)
    (created : PqxdhLiveServerConstruction.Created Unit) : RegImpl KemSK (M × (Alloc Coord n × Γ)) n :=
  fun query => StateT.mk fun x =>
    (fun r => (r.1.1, attachX r.1.2 r.2.1 r.2.2)) <$>
      (simulateQ (slotImpl svc) ((prog created query).run (detachX x))).run (x.backend.2.1, (x.backend.1, x.seeds))

/-- Move the seed table from the service state of a slot core into the extended state's seed table. -/
def moveSeeds (x : XState KemSK ((M × (PqxdhRecordLiftWorld.SeedSpec n).QueryCache) × (Alloc Coord n × Γ)) n) :
    XState KemSK (M × (Alloc Coord n × Γ)) n :=
  ⟨x.base, (x.backend.1.1, x.backend.2), x.backend.1.2, x.snap, x.log⟩

/-- A slot core whose slot programs do not read or write the seed table is, after moving the seeds, the slot core with the seeds in the extended state. -/
theorem slotCore_moveSeeds (prog : PqxdhLiveServerConstruction.Created Unit → SlotProgram KemSK Γ n)
    (frame : ∀ created query, SlotFrame seedPut (prog created query))
    (svc : SlotService (M × (PqxdhRecordLiftWorld.SeedSpec n).QueryCache) n)
    (created : PqxdhLiveServerConstruction.Created Unit) (query : EnvQuery)
    (x : XState KemSK ((M × (PqxdhRecordLiftWorld.SeedSpec n).QueryCache) × (Alloc Coord n × Γ)) n) :
    Prod.map id moveSeeds <$> (slotCore prog svc created query).run x =
      (slotCoreX prog svc created query).run (moveSeeds x) := by
  rw [PqxdhDeploymentIdealSlots.slotCore_run]
  change _ = (fun r => (r.1.1, attachX r.1.2 r.2.1 r.2.2)) <$>
    (simulateQ (slotImpl svc) ((prog created query).run (seedPut (detach x) ∅))).run
      (x.backend.2.1, (x.backend.1.1, x.backend.1.2))
  rw [frame created query (detach x) ∅, simulateQ_map, StateT.run_map, Functor.map_map, Functor.map_map]
  rfl

end CoreX

/-! ### The ideal registration does not read the seed table -/

section SeedFrames
variable {ι : Type} {baseSpec : OracleSpec ι} {Reader Response : Type}
  (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
  (checks : Checks) {count : ℕ}
open PqxdhDeploymentIdealSteps (idealProg acceptStep buildStep finishStep createReg IdealCore)
open PqxdhDeploymentIdealParams (Target Params)
open PqxdhRegistrationJointKemPostSkeleton (Hidden)

/-- A step of the native deployment state, on the extended state, keeps the seed table whatever it holds. -/
theorem onBase_seedFrame {Bk α : Type} (step : StateT (PqxdhDeploymentNative.State KemSK) ProbComp α)
    (x : XState KemSK Bk n) (c : (PqxdhRecordLiftWorld.SeedSpec n).QueryCache) :
    (PqxdhDeploymentBackend.onBase step).run (seedPut x c) =
      (fun r => (r.1, seedPut r.2 c)) <$> (PqxdhDeploymentBackend.onBase step).run x := by
  simp only [PqxdhDeploymentBackend.onBase, StateLens.lift, StateT.run, Functor.map_map]
  rfl

/-- The real registration handler on any backend keeps the seed table whatever it holds. -/
theorem realRegAt_seedFrame {Bk : Type} (created : PqxdhLiveServerConstruction.Created Unit) (query : EnvQuery)
    (x : XState KemSK Bk n) (c : (PqxdhRecordLiftWorld.SeedSpec n).QueryCache) :
    (realRegAt setup codec route checks created query).run (seedPut x c) =
      (fun r => (r.1, seedPut r.2 c)) <$> (realRegAt setup codec route checks created query).run x := by
  simp only [realRegAt, StateT.run, Functor.map_map]
  rfl

/-- Every command of the ideal registration's slot program keeps the seed table whatever it holds. -/
theorem idealProg_seedFrame (t : Target count) (p : Params KemSK count)
    (hidden : PqxdhServerAuthKeySchedule.Output → Hidden Response) (created : PqxdhLiveServerConstruction.Created Unit)
    (query : EnvQuery) : SlotFrame seedPut (idealProg setup codec route checks t p hidden created query) := by
  rcases query with ⟨command, isEnv⟩
  cases command
  case create pin keyId =>
    exact SlotFrame.onSlots _ fun x c => onBase_seedFrame _ x c
  case bundle owner =>
    exact SlotFrame.onSlots _ fun x c => realRegAt_seedFrame setup codec route checks created _ x c
  case hmac key message =>
    exact SlotFrame.onSlots _ fun x c => realRegAt_seedFrame setup codec route checks created _ x c
  case accept raw =>
    intro x c
    change (acceptStep setup codec route checks t p created raw).run (seedPut x c) =
      (fun r => (r.1, seedPut r.2 c)) <$> (acceptStep setup codec route checks t p created raw).run x
    by_cases selected : x.backend.accepts = t.accept
    · have selected' : (seedPut x c).backend.accepts = t.accept := selected
      simp only [acceptStep, StateT.run, selected, selected', ↓reduceIte, Functor.map_map]
      rfl
    · have selected' : ¬ (seedPut x c).backend.accepts = t.accept := selected
      simp only [acceptStep, StateT.run, selected, selected', ↓reduceIte, onSlots, liftS]
      have h := realRegAt_seedFrame setup codec route checks created ⟨.accept raw, trivial⟩
        { x with backend := { x.backend with accepts := x.backend.accepts + 1 } } c
      simp only [StateT.run] at h
      rw [← OracleComp.liftComp_map, ← h]
      rfl
  case build session payload =>
    intro x c
    change (buildStep setup codec route checks hidden created session payload).run (seedPut x c) =
      (fun r => (r.1, seedPut r.2 c)) <$> (buildStep setup codec route checks hidden created session payload).run x
    have h := realRegAt_seedFrame setup codec route checks created ⟨.build session payload, trivial⟩ x c
    simp only [StateT.run] at h
    rcases marked : x.backend.marks with _ | ⟨index, coords⟩
    · have marked' : (seedPut x c).backend.marks = none := marked
      simp only [buildStep, StateT.run, marked, marked', onSlots, liftS]
      rw [h, OracleComp.liftComp_map]
    · have marked' : (seedPut x c).backend.marks = some (index, coords) := marked
      by_cases chosen : index = session ∧ (x.base.native.shared.2.pending session).isSome = true
      · have chosen' : index = session ∧ ((seedPut x c).base.native.shared.2.pending session).isSome = true := chosen
        simp only [buildStep, StateT.run, marked, marked', chosen, chosen', and_self, ↓reduceIte, map_bind, map_pure]
        rfl
      · have chosen' : ¬ (index = session ∧ ((seedPut x c).base.native.shared.2.pending session).isSome = true) :=
          chosen
        simp only [buildStep, StateT.run, marked, marked', chosen, chosen', ↓reduceIte, onSlots, liftS]
        rw [h, OracleComp.liftComp_map]
  case finish owner raw =>
    intro x c
    change (finishStep setup codec route checks t p hidden created owner raw).run (seedPut x c) =
      (fun r => (r.1, seedPut r.2 c)) <$> (finishStep setup codec route checks t p hidden created owner raw).run x
    by_cases chosen : x.backend.active = true ∧ owner = t.kem.val ∧
        PqxdhDeploymentIdealSteps.initSentAt x.base.native.owners owner = true
    · have chosen' : (seedPut x c).backend.active = true ∧ owner = t.kem.val ∧
          PqxdhDeploymentIdealSteps.initSentAt (seedPut x c).base.native.owners owner = true := chosen
      simp only [finishStep, StateT.run, ite_eq_left chosen, ite_eq_left chosen', map_bind, map_pure]
      rfl
    · have chosen' : ¬ ((seedPut x c).backend.active = true ∧ owner = t.kem.val ∧
          PqxdhDeploymentIdealSteps.initSentAt (seedPut x c).base.native.owners owner = true) := chosen
      have h := realRegAt_seedFrame setup codec route checks created ⟨.finish owner raw, trivial⟩ x c
      simp only [StateT.run] at h
      simp only [finishStep, StateT.run, ite_eq_right chosen, ite_eq_right chosen', onSlots, liftS]
      rw [h, OracleComp.liftComp_map]
  all_goals exact absurd isEnv id

end SeedFrames

/-! ### Moving the seeds into the extended state, at the game level -/

section GameMove
variable {ι : Type} {baseSpec : OracleSpec ι} {Reader Response A X : Type}
  (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
open PqxdhDeploymentInterface (Spec FreshBounds Mode ModeSpec asModeO)

/-- The fixed steps (coins, BLAKE2b, records) commute with moving the seeds, whatever the registration handlers. -/
theorem fixed_moveSeeds {M Γ : Type}
    (reg₁ : RegImpl KemSK ((M × (PqxdhRecordLiftWorld.SeedSpec n).QueryCache) × (Alloc Coord n × Γ)) n)
    (reg₂ : RegImpl KemSK (M × (Alloc Coord n × Γ)) n) (query : Spec.Domain)
    (notEnv : ∀ command : EnvQuery, query ≠ .inr command.val)
    (x : XState KemSK ((M × (PqxdhRecordLiftWorld.SeedSpec n).QueryCache) × (Alloc Coord n × Γ)) n) :
    Prod.map id moveSeeds <$> (handlerWith setup codec route reg₁ query).run x =
      (handlerWith setup codec route reg₂ query).run (moveSeeds x) := by
  rcases query with coin | command
  · simp only [handlerWith, StateT.run_lift, map_bind, map_pure]
    rfl
  · cases command
    case create pin keyId => exact absurd rfl (notEnv ⟨.create pin keyId, trivial⟩)
    case bundle owner => exact absurd rfl (notEnv ⟨.bundle owner, trivial⟩)
    case accept raw => exact absurd rfl (notEnv ⟨.accept raw, trivial⟩)
    case build session payload => exact absurd rfl (notEnv ⟨.build session payload, trivial⟩)
    case finish owner raw => exact absurd rfl (notEnv ⟨.finish owner raw, trivial⟩)
    case hmac key message => exact absurd rfl (notEnv ⟨.hmac key message, trivial⟩)
    all_goals
      simp only [handlerWith, PqxdhDeploymentBackend.onBase, StateLens.lift, PqxdhDeploymentBackend.baseLens,
        StateT.run, Functor.map_map]
      rfl

/-- Seed relocation (design-v2 section 5.2, step 2): for slot programs that do not read or write the seed table, the game with a slot core whose service keeps the seeds in its backend, read with the seeds moved into the extended state, is exactly the game with the slot core whose service keeps them in the extended state's seed table. -/
theorem game_moveSeeds {M Γ : Type} (prog : PqxdhLiveServerConstruction.Created Unit → SlotProgram KemSK Γ n)
    (frame : ∀ created query, SlotFrame seedPut (prog created query))
    (svc : SlotService (M × (PqxdhRecordLiftWorld.SeedSpec n).QueryCache) n)
    (init : PqxdhLiveServerConstruction.Created Unit → M × (Alloc Coord n × Γ)) (ensureInit : StateT A ProbComp Bool)
    (identityIndex : ℕ) (bounds : FreshBounds) (mode : Mode) (adversary : OracleComp (ModeSpec mode) X) (runtime : A) :
    outcomeMap moveSeeds <$> (gameWith setup codec route (fun created => (((init created).1, ∅), (init created).2))
        (fun created => slotCore prog svc created) ensureInit identityIndex bounds mode adversary).run runtime =
      (gameWith setup codec route init (fun created => slotCoreX prog svc created) ensureInit identityIndex bounds mode
        adversary).run runtime := by
  simp only [gameWith, StateT.run, map_bind]
  refine bind_congr fun born => ?_
  rcases born with ⟨_ | created, after⟩
  · simp only [map_pure, outcomeMap, Option.map_none]
  · have moved := OracleComp.map_run_simulateQ_eq_of_query_map_eq
      (handlerWith setup codec route (slotCore prog svc created))
      (handlerWith setup codec route (slotCoreX prog svc created)) moveSeeds (fun query x => ?step)
      (PqxdhDeploymentSecrecy.wrap setup.source.crypto codec setup.serverKeyId bounds (asModeO mode adversary))
      (xinitial created (((init created).1, ∅), (init created).2))
    case step =>
      by_cases env : ∃ command : EnvQuery, query = .inr command.val
      · obtain ⟨⟨command, isEnv⟩, rfl⟩ := env
        cases command
        case create pin keyId => exact slotCore_moveSeeds prog frame svc created ⟨.create pin keyId, trivial⟩ x
        case bundle owner => exact slotCore_moveSeeds prog frame svc created ⟨.bundle owner, trivial⟩ x
        case accept raw => exact slotCore_moveSeeds prog frame svc created ⟨.accept raw, trivial⟩ x
        case build session payload =>
          exact slotCore_moveSeeds prog frame svc created ⟨.build session payload, trivial⟩ x
        case finish owner raw => exact slotCore_moveSeeds prog frame svc created ⟨.finish owner raw, trivial⟩ x
        case hmac key message => exact slotCore_moveSeeds prog frame svc created ⟨.hmac key message, trivial⟩ x
        all_goals exact isEnv.elim
      · exact fixed_moveSeeds setup codec route _ _ query (fun command same => env ⟨command, same⟩) x
    have initial : moveSeeds (xinitial (KemSK := KemSK) (n := n) created (((init created).1, ∅), (init created).2)) =
        xinitial created (init created) := rfl
    rw [initial] at moved
    simp only [StateT.run] at moved
    simp only [← moved, Functor.map_map, outcomeMap, Option.map_some, Prod.map_fst, Prod.map_snd, id_eq]

end GameMove

/-! ### The chain from `CE.idealGame g` to the first-touch split form -/

section Chain
variable {ι : Type} {baseSpec : OracleSpec ι} {Reader Response A X : Type}
  (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
  (checks : Checks) {count : ℕ}
open PqxdhDeploymentIdealSteps (idealProg idealReg idealCoreErased erasedHidden IdealCore IdealBk TableState idealInit
  SplitBk splitInit)
open PqxdhDeploymentIdealParams (Target Params)
open PqxdhDeploymentInterface (FreshBounds Mode ModeSpec)

/-- The ideal registration in first-touch split form (design-v2 section 5.2, after step 2): the C7-erased slot program with the split service, whose material is kept in the backend's material cache and whose seeds are kept in the extended state's seed table; both are drawn at the first touch of a slot. -/
noncomputable def idealSplitX (t : Target count) (p : Params KemSK count) :
    PqxdhLiveServerConstruction.Created Unit → RegImpl KemSK SplitBk 2 :=
  fun created => slotCoreX (idealProg setup codec route checks t p (erasedHidden setup codec checks)) splitService created

/-- What the split chain keeps of a final state: the native deployment state with the CTX cache emptied, the allocator and the ideal backend, the LQ-F snapshot and the ephemeral log (neither the slot service state nor the seed table). -/
def splitView {S : Type} (x : XState KemSK (S × (Alloc Coord n × IdealCore)) n) :
    PqxdhDeploymentNative.State KemSK × (Alloc Coord n × IdealCore) × PqxdhDeploymentLater.Snap ×
      PqxdhDeploymentLaterServerSource.Log :=
  ((fullX x).base, x.backend.2, x.snap, x.log)

/-- Reading an outcome through two projections in turn reads it through their composition. -/
theorem outcomeMap_comp {Bk Bk' υ : Type} {n' : ℕ} (f : XState KemSK Bk n → XState KemSK Bk' n')
    (g : XState KemSK Bk' n' → υ)
    (outcome : Option (PqxdhRegistrationJointServerBirth.ClientCreated Unit × X × PqxdhDeploymentSecrecy.Ledger ×
      XState KemSK Bk n) × A) :
    PqxdhDeploymentFinishErasure.outcomeMap (X := X) (A := A) g
        (PqxdhDeploymentFinishErasure.outcomeMap (X := X) (A := A) f outcome) =
      PqxdhDeploymentFinishErasure.outcomeMap (X := X) (A := A) (g ∘ f) outcome := by
  rcases outcome with ⟨_ | result, after⟩ <;> rfl

/-- The represent step for the C7-erased ideal registration (design-v2 section 5.2, step 1; CE-11a's `represent_split` with `idealCoreErased_natural`): the game with item 2's persistent lazy table, read through the table's cache, and the game with the split service, read through the joined table, have the same law. -/
theorem represent_ideal (t : Target count) (p : Params KemSK count) (ensureInit : StateT A ProbComp Bool)
    (identityIndex : ℕ) (bounds : FreshBounds) (mode : Mode) (adversary : OracleComp (ModeSpec mode) X) (runtime : A) :
    LawEq (outcomeMap (mapBackend Prod.fst) <$> (gameWith setup codec route idealInit
        (fun created => idealCoreErased setup codec route checks t p PqxdhDeploymentSeedSplit.tableService created)
        ensureInit identityIndex bounds mode adversary).run runtime)
      (outcomeMap (mapBackend joinTable) <$> (gameWith setup codec route
        (fun _ => ((∅, ∅), (emptyAlloc, IdealCore.initial)))
        (fun created => idealCoreErased setup codec route checks t p splitService created)
        ensureInit identityIndex bounds mode adversary).run runtime) :=
  PqxdhDeploymentSeedSplit.represent_split setup codec route
    (fun {S} svc created => idealCoreErased setup codec route checks t p (S := S) svc created)
    (PqxdhDeploymentIdealSteps.idealCoreErased_natural setup codec route checks t p)
    (fun _ => (emptyAlloc, IdealCore.initial)) ensureInit identityIndex bounds mode adversary runtime

/-- Seed relocation for the C7-erased ideal registration (design-v2 section 5.2, step 2): the game with the split service, with the seeds moved from the service state into the extended state's seed table, is exactly the game with `idealSplitX`. -/
theorem seed_move (t : Target count) (p : Params KemSK count) (ensureInit : StateT A ProbComp Bool)
    (identityIndex : ℕ) (bounds : FreshBounds) (mode : Mode) (adversary : OracleComp (ModeSpec mode) X) (runtime : A) :
    outcomeMap moveSeeds <$> (gameWith setup codec route (fun _ => ((∅, ∅), (emptyAlloc, IdealCore.initial)))
        (fun created => idealCoreErased setup codec route checks t p splitService created)
        ensureInit identityIndex bounds mode adversary).run runtime =
      (gameWith setup codec route splitInit (idealSplitX setup codec route checks t p) ensureInit identityIndex bounds
        mode adversary).run runtime :=
  game_moveSeeds setup codec route (idealProg setup codec route checks t p (erasedHidden setup codec checks))
    (fun created query => idealProg_seedFrame setup codec route checks t p _ created query) splitService splitInit
    ensureInit identityIndex bounds mode adversary runtime

/-- From `CE.idealGame g`'s registration to the first-touch split form: C7 (`PqxdhDeploymentIdealErase.erase_ideal`), the represent step and the seed relocation, read through `splitView`. -/
theorem ideal_to_splitX (t : Target count) (p : Params KemSK count) (ensureInit : StateT A ProbComp Bool)
    (identityIndex : ℕ) (bounds : FreshBounds) (mode : Mode) (adversary : OracleComp (ModeSpec mode) X) (runtime : A) :
    LawEq (outcomeMap splitView <$> (gameWith setup codec route idealInit (idealReg setup codec route checks t p)
        ensureInit identityIndex bounds mode adversary).run runtime)
      (outcomeMap splitView <$> (gameWith setup codec route splitInit (idealSplitX setup codec route checks t p)
        ensureInit identityIndex bounds mode adversary).run runtime) := by
  have erased := (PqxdhDeploymentIdealErase.erase_ideal setup codec route checks t p ensureInit identityIndex bounds
    mode adversary runtime).map (outcomeMap (X := X) (A := A) (fun x : XState KemSK (IdealBk TableState) 2 =>
      ((x.base, x.backend.2, x.snap, x.log) :
        PqxdhDeploymentNative.State KemSK × (Alloc Coord 2 × IdealCore) × PqxdhDeploymentLater.Snap ×
          PqxdhDeploymentLaterServerSource.Log)))
  have represented := (represent_ideal setup codec route checks t p ensureInit identityIndex bounds mode adversary
    runtime).map (outcomeMap (X := X) (A := A) (fun x : XState KemSK ((PqxdhDeploymentSeedSplit.OutputSpec 2).QueryCache ×
      (Alloc Coord 2 × IdealCore)) 2 => splitView x))
  have moved := congrArg (fun work => outcomeMap (X := X) (A := A)
    (fun x : XState KemSK SplitBk 2 => splitView x) <$> work)
    (seed_move setup codec route checks t p ensureInit identityIndex bounds mode adversary runtime)
  simp only [Functor.map_map, outcomeMap_comp] at erased represented moved
  refine (LawEq.of_eq ?_).trans (erased.trans ((LawEq.of_eq ?_).trans (represented.trans (LawEq.of_eq ?_))))
  · rfl
  · rfl
  · rw [← moved]
    rfl

end Chain

end BeaconcryptCore.Computational.PqxdhDeploymentIdealKeys

-- Axiom guards (generated)

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealKeys.slotCore_moveSeeds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealKeys.slotCore_moveSeeds

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealKeys.onBase_seedFrame' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealKeys.onBase_seedFrame

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealKeys.realRegAt_seedFrame' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealKeys.realRegAt_seedFrame

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealKeys.idealProg_seedFrame' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealKeys.idealProg_seedFrame

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealKeys.fixed_moveSeeds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealKeys.fixed_moveSeeds

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealKeys.game_moveSeeds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealKeys.game_moveSeeds

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealKeys.outcomeMap_comp' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealKeys.outcomeMap_comp

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealKeys.represent_ideal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealKeys.represent_ideal

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealKeys.seed_move' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealKeys.seed_move

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealKeys.ideal_to_splitX' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealKeys.ideal_to_splitX
