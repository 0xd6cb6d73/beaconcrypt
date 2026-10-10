-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhDeploymentIdealDefer

/-!
# `CE.idealGame g` and the final split form with the message key first or last (CE-11b, unit U8)

The native key-first and key-last forms of plan section 49 Q3 (design-v2 section 10.2), the analogue of item 2's stage S6 (`PqxdhRegistrationJointKemKeyFirst`) for the common deployment experiment. Slot 0 is the first slot the first-touch allocator assigns, that of the selected accept's hidden read; its 108-byte key-schedule output is the 32-byte message key `key32` and a 76-byte residual (`PqxdhServerAuthCtxMaterial.output`). The statements hold for every view of the outcome that erases the hidden-slot service state (`eraseService`): the Server's public data, the adversary's output, the ledger and every other coordinate of the final extended state.

- Generic eager sampling (`cacheLens`, `game_eager`): when every step of the deployment handler commutes with completions of a lazy cache in the backend (`LazyOracleDiscard.Commutes`), the game whose cache starts with one point holding a uniform answer drawn before the game has the law of the game with the empty cache, through `LazyOracleDiscard.commutes_simulateQ`; the completion moved to the end of the run is dropped by the view (`LazyOracleDiscard.lawEq_drop`).
- The allocator in front of a slot service commutes with completions of a lazy cache inside the service state when the service does (`slotImpl_commutes`, `slotImpl_commutes_of`); hence every command of a core built from slot programs over VCVio's lazy slot cache does (`slotCore_commutes`, `handler_commutes`).
- `CE.idealGame g` (`PqxdhDeploymentIdealSteps.idealGame`, over item 2's counted lazy table `tableService`) is first replaced by its lazy representation over `lazyService` (`idealGame_lazy`, by `PqxdhDeploymentSeedSplit.represent` with `table_service_proj` and `idealCore_natural`): the table's draw counter breaks the exact commutation of the steps with completions. Then `idealGame_key_first`: the game that draws slot 0's message key before everything else, then its residual and the challenger's draws, and starts with slot 0 holding the reassembled output (`idealGameKeyFirst`); `idealGame_key_last`: the residual first and the key after it (`idealGameKeyLast`, `idealGame_keyFirst_keyLast`).
- The final split form (`PqxdhDeploymentIdealDefer.idealSplit`) keeps slot material `(key32, nonce12)` in a lazy material cache and seeds in the world's seed table; its slot steps and hidden installs commute with completions of the material cache (`slotRunX_commutes`, `installStep_commutes`, `split_handler_commutes`), so `split_key_first`: the split game has the law of the game that draws slot 0's `key32` and then its `nonce12` before the game and starts with slot 0's material in the cache (`materialInit`); `split_key_last` swaps the two draws. `key32` is environment material; slot 0's seed stays a world seed, drawn at its hidden install.

`world_key_first` is not built (design-v2 section 10.2, S14). These are equalities in law of lazily sampled caches and uniform bytes; no security claim is made here.
-/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc

set_option autoImplicit false

namespace BeaconcryptCore.Computational.PqxdhDeploymentIdealKeyFirst
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhDeploymentBackend (XState RegImpl handlerWith gameWith)
open PqxdhDeploymentSeedSplit (OutputSpec lazyService mapBackend)
open PqxdhDeploymentIdealSlots (Coord SlotSpec slotCore)
open PqxdhRegistrationJointKemSecondEntry (Alloc slotImpl)
open LazyOracleDiscard (Commutes CacheLens StateLens LawEq)


/-! ### Generic eager sampling of one point of a lazy cache in the backend -/

section Generic
variable {ι₀ : Type} {spec₀ : OracleSpec ι₀} {KemSK Γ : Type} {n : ℕ}

/-- The lazy cache that a backend holds in its first component, inside an extended state. -/
def cacheLens : CacheLens spec₀ (XState KemSK (spec₀.QueryCache × Γ) n) where
  get x := x.backend.1
  set x c := mapBackend (fun _ => c) x
  get_set _ _ := rfl
  set_get _ := rfl
  set_set _ _ _ := rfl

/-- The final state with the backend's service state erased: every coordinate of the extended state except the service state. -/
def eraseService {S : Type} : XState KemSK (S × Γ) n → XState KemSK (Unit × Γ) n := mapBackend (fun _ => ())

variable {A X : Type}
open PqxdhDeploymentFinishErasure (outcomeMap)

/-- Erasing the service state after replacing it is erasing it. -/
theorem outcomeMap_erase {S₁ S₂ : Type} (proj : S₁ → S₂) :
    (fun outcome => outcomeMap (KemSK := KemSK) (n := n) (A := A) (X := X) eraseService
        (outcomeMap (mapBackend (Γ := Γ) proj) outcome)) = outcomeMap eraseService := by
  funext outcome
  rcases outcome with ⟨_ | value, after⟩ <;> rfl

variable [DecidableEq ι₀] [∀ t : spec₀.Domain, SampleableType (spec₀.Range t)]
  {ι : Type} {baseSpec : OracleSpec ι} {Reader Response : Type}
  (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
open PqxdhDeploymentInterface (FreshBounds Mode ModeSpec)

set_option maxRecDepth 100000 in
/-- Eager sampling of one point (`LazyOracleDiscard.commutes_simulateQ`): when every step of the deployment handler commutes with completions of the lazy cache in the backend, the game whose cache starts with point `j` holding a uniform answer drawn before the game has the law of the game with the empty cache, for every view of the outcome that erases the service state; the completion of point `j` that the commutation moves to the end of the run is dropped by the view (`LazyOracleDiscard.lawEq_drop`). -/
theorem game_eager (reg : PqxdhLiveServerConstruction.Created Unit → RegImpl KemSK (spec₀.QueryCache × Γ) n)
    (commutes : ∀ created query, Commutes (cacheLens (spec₀ := spec₀) (KemSK := KemSK) (Γ := Γ) (n := n))
      (handlerWith setup codec route (reg created) query))
    (j : spec₀.Domain) (gamma : PqxdhLiveServerConstruction.Created Unit → Γ)
    (ensureInit : StateT A ProbComp Bool) (identityIndex : ℕ) (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) (runtime : A) :
    LawEq (($ᵗ spec₀.Range j) >>= fun v => outcomeMap eraseService <$>
        (gameWith setup codec route (fun created => (((∅ : spec₀.QueryCache).cacheQuery j v), gamma created)) reg
          ensureInit identityIndex bounds mode adversary).run runtime)
      (outcomeMap eraseService <$> (gameWith setup codec route (fun created => (∅, gamma created)) reg ensureInit
        identityIndex bounds mode adversary).run runtime) := by
  simp only [gameWith, StateT.run, map_bind]
  refine (LazyOracleDiscard.lawEq_swap _ _ _).trans (LawEq.bind (LawEq.refl _) fun born => ?_)
  rcases born with ⟨_ | created, after⟩
  · exact LazyOracleDiscard.lawEq_drop _ _
  · dsimp only
    have commuted := LazyOracleDiscard.commutes_simulateQ cacheLens (handlerWith setup codec route (reg created))
      (commutes created) (PqxdhDeploymentSecrecy.wrap setup.source.crypto codec setup.serverKeyId bounds
        (PqxdhDeploymentInterface.asModeO mode adversary)) j
      (PqxdhDeploymentBackend.xinitial created (∅, gamma created))
    have start : StateLens.complete cacheLens j (PqxdhDeploymentBackend.xinitial (KemSK := KemSK) (n := n) created
        ((∅ : spec₀.QueryCache), gamma created)) =
        (fun v => PqxdhDeploymentBackend.xinitial (KemSK := KemSK) (n := n) created
          (((∅ : spec₀.QueryCache).cacheQuery j v), gamma created)) <$> ($ᵗ spec₀.Range j) := by
      change (fun c => mapBackend (fun _ => c) (PqxdhDeploymentBackend.xinitial (KemSK := KemSK) (n := n) created
        ((∅ : spec₀.QueryCache), gamma created))) <$> LazyOracleDiscard.complete j (∅ : spec₀.QueryCache) = _
      rw [LazyOracleDiscard.complete_of_none (show (∅ : spec₀.QueryCache) j = none from rfl), Functor.map_map]
      exact congrArg (· <$> ($ᵗ spec₀.Range j)) (funext fun _ => rfl)
    let F := fun result : (X × PqxdhDeploymentSecrecy.Ledger) × XState KemSK (spec₀.QueryCache × Γ) n =>
      outcomeMap eraseService (some (PqxdhRegistrationJointServerBirth.encode created, result.1.1, result.1.2, result.2),
        after)
    refine (LawEq.of_eq ?_).trans ((commuted.map F).trans ?_)
    · rw [start, bind_map_left, map_bind]
      exact bind_congr fun _ => (Functor.map_map _ _ _)
    · rw [map_bind, Functor.map_map, map_eq_bind_pure_comp]
      refine LawEq.bind (LawEq.refl _) fun r => ?_
      rw [Functor.map_map, StateLens.complete, Functor.map_map]
      change LawEq ((fun c => F (r.1, mapBackend (fun _ => c) r.2)) <$> LazyOracleDiscard.complete j r.2.backend.1) _
      rw [map_eq_bind_pure_comp]
      refine (LawEq.of_eq (bind_congr fun c => ?_)).trans
        (LazyOracleDiscard.lawEq_drop (LazyOracleDiscard.complete j r.2.backend.1) _)
      rfl

end Generic

/-! ### The lazy slot cache commutes with completions -/

section Slots
variable {n : ℕ}

/-- The lazy cache inside the allocator-and-service state. -/
abbrev serviceLens : CacheLens (OutputSpec n) (Alloc Coord n × (OutputSpec n).QueryCache) :=
  StateLens.snd (Alloc Coord n) (OutputSpec n).QueryCache

/-- Every request of the first-touch allocator in front of the lazy service commutes, in law, with completing any slot of the lazy cache: a coin and a request beyond the slots are frames of the cache, and a request at a slot is one lazy query, which commutes with completions (`LazyOracleDiscard.complete_query_swap`). -/
theorem slotImpl_commutes (query : SlotSpec.Domain) :
    Commutes (serviceLens (n := n)) (slotImpl (lazyService (n := n)) query) := by
  rcases query with coin | point
  · refine LazyOracleDiscard.commutes_frame _ _ fun s c => ?_
    rw [PqxdhRegistrationJointKemSecondEntry.slot_coin, PqxdhRegistrationJointKemSecondEntry.slot_coin,
      Functor.map_map]
  · intro t s
    have complete : StateLens.complete serviceLens t s = (fun c => (s.1, c)) <$> LazyOracleDiscard.complete t s.2 := rfl
    have swap : ∀ (j : PqxdhRecordLiftInterface.Slot n) (alloc : Alloc Coord n),
        (∀ c, (slotImpl (lazyService (n := n)) (.inr point)).run (s.1, c) =
          (fun r => (r.1, (alloc, r.2))) <$> ((OutputSpec n).randomOracle j).run c) →
        LawEq (StateLens.complete serviceLens t s >>= (slotImpl (lazyService (n := n)) (.inr point)).run)
          ((slotImpl (lazyService (n := n)) (.inr point)).run s >>= fun r =>
            (fun x => (r.1, x)) <$> StateLens.complete serviceLens t r.2) := by
      intro j alloc shape
      have shape' : (slotImpl (lazyService (n := n)) (.inr point)).run s =
          (fun r => (r.1, (alloc, r.2))) <$> ((OutputSpec n).randomOracle j).run s.2 := shape s.2
      rw [complete, bind_map_left, shape']
      simp only [shape]
      refine (LawEq.of_eq ?_).trans (((LazyOracleDiscard.complete_query_swap t j s.2).map
        (fun r => (r.1, (alloc, r.2)))).trans (LawEq.of_eq ?_))
      · rw [map_bind]
      · simp only [map_bind, bind_map_left, Functor.map_map, StateLens.complete]
        rfl
    rcases found : s.1.1 point with _ | slot
    · by_cases room : s.1.2 < n
      · exact swap ⟨s.1.2, room⟩ (Function.update s.1.1 point (some ⟨s.1.2, room⟩), s.1.2 + 1) fun c =>
          PqxdhRegistrationJointKemSecondEntry.slot_none lazyService point (s.1, c) found room
      · have shape : ∀ c, (slotImpl (lazyService (n := n)) (.inr point)).run (s.1, c) =
            (fun answer => (answer, (s.1, c))) <$> ($ᵗ PqxdhServerAuthKeySchedule.Output) := fun c => by
          simp [slotImpl, found, room]
        have shape' := shape s.2
        rw [complete, bind_map_left, shape', bind_map_left]
        refine (LawEq.of_eq (bind_congr fun c => ?_)).trans ((LazyOracleDiscard.lawEq_swap
          (LazyOracleDiscard.complete t s.2) ($ᵗ PqxdhServerAuthKeySchedule.Output)
          (fun c answer => (pure (answer, (s.1, c)) : ProbComp _))).trans (LawEq.of_eq (bind_congr fun answer => ?_)))
        · rw [shape, map_eq_bind_pure_comp]
          rfl
        · change _ = (fun x => (answer, x)) <$> ((fun c => (s.1, c)) <$> LazyOracleDiscard.complete t s.2)
          rw [Functor.map_map, map_eq_bind_pure_comp]
          rfl
    · exact swap slot s.1 fun c =>
        PqxdhRegistrationJointKemSecondEntry.slot_some lazyService point (s.1, c) slot found


/-- Every request of the first-touch allocator in front of a slot service commutes, in law, with completing any point of a lazy cache inside the service state, when every step of the service does: a coin and a request beyond the slots are frames of the cache, a request at a known slot is the service step on the service state, and a request that allocates a new slot is that service step followed by the allocator's update, a frame of the cache. -/
theorem slotImpl_commutes_of {ι₀ : Type} [DecidableEq ι₀] {spec₀ : OracleSpec ι₀}
    [∀ t : spec₀.Domain, SampleableType (spec₀.Range t)] {S : Type}
    (svc : PqxdhDeploymentSeedSplit.SlotService S n) (L : CacheLens spec₀ S) (h : ∀ j, Commutes L (svc j))
    (query : SlotSpec.Domain) :
    Commutes ((StateLens.snd (Alloc Coord n) S).comp L) (slotImpl svc query) := by
  rcases query with coin | point
  · refine LazyOracleDiscard.commutes_frame _ _ fun s c => ?_
    rw [PqxdhRegistrationJointKemSecondEntry.slot_coin, PqxdhRegistrationJointKemSecondEntry.slot_coin,
      Functor.map_map]
  · refine PqxdhDeploymentBackend.commutes_dispatch _ _ (fun s => s.1) (fun _ _ => rfl)
      (fun a => match a.1 point with
        | some slot => (StateLens.snd (Alloc Coord n) S).lift (svc slot)
        | none => if room : a.2 < n then
            (StateLens.snd (Alloc Coord n) S).lift (svc ⟨a.2, room⟩) >>= fun v =>
              StateT.mk fun s => pure (v, ((Function.update a.1 point (some ⟨a.2, room⟩), a.2 + 1), s.2))
          else StateT.mk fun s => (fun answer => (answer, s)) <$> ($ᵗ PqxdhServerAuthKeySchedule.Output))
      (fun s => ?_) (fun a => ?_)
    · rcases found : s.1.1 point with _ | slot
      · by_cases room : s.1.2 < n
        · rw [PqxdhRegistrationJointKemSecondEntry.slot_none svc point s found room]
          simp only [room, ↓reduceDIte, StateT.run_bind, StateT.run_mk, bind_pure_comp]
          rw [show ((StateLens.snd (Alloc Coord n) S).lift (svc ⟨s.1.2, room⟩)).run s =
            (fun r => (r.1, (s.1, r.2))) <$> (svc ⟨s.1.2, room⟩).run s.2 from rfl, Functor.map_map]
        · change (match s.1.1 point with
            | some slot => (fun result : PqxdhServerAuthKeySchedule.Output × S => (result.1, (s.1, result.2))) <$>
                (svc slot).run s.2
            | none => if room : s.1.2 < n then
                (fun result : PqxdhServerAuthKeySchedule.Output × S => (result.1, ((Function.update s.1.1 point
                  (some ⟨s.1.2, room⟩), s.1.2 + 1), result.2))) <$> (svc ⟨s.1.2, room⟩).run s.2
              else (fun answer => (answer, s)) <$> ($ᵗ PqxdhServerAuthKeySchedule.Output)) = _
          rw [found]
          simp only [room, ↓reduceDIte, StateT.run_mk]
          rfl
      · rw [PqxdhRegistrationJointKemSecondEntry.slot_some svc point s slot found]
        rfl
    · rcases found : a.1 point with _ | slot
      · by_cases room : a.2 < n
        · simp only [room, ↓reduceDIte]
          refine LazyOracleDiscard.commutes_bind _ (LazyOracleDiscard.commutes_lift _ _ _ (h _)) fun v => ?_
          exact LazyOracleDiscard.commutes_frame _ _ fun s c => by simp only [StateT.run_mk, map_pure]; rfl
        · simp only [room, ↓reduceDIte]
          exact LazyOracleDiscard.commutes_frame _ _ fun s c => by simp only [StateT.run_mk, Functor.map_map]
      · exact LazyOracleDiscard.commutes_lift _ _ _ (h slot)

end Slots

/-! ### The lazy representation of the ideal game commutes with completions of its slot cache -/

section Core
variable {KemSK Γ : Type} {n : ℕ}

/-- Every command of a registration core built from slot programs over the lazy service commutes, in law, with completing any slot of its lazy cache: the slot program's state and the allocator are frames of the cache, and the allocator's requests commute (`slotImpl_commutes`). -/
theorem slotCore_commutes (prog : PqxdhLiveServerConstruction.Created Unit → PqxdhDeploymentIdealSlots.SlotProgram KemSK Γ n)
    (created : PqxdhLiveServerConstruction.Created Unit) (query : PqxdhRecordLiftInterface.EnvQuery) :
    Commutes (cacheLens (spec₀ := OutputSpec n) (KemSK := KemSK) (Γ := Alloc Coord n × Γ) (n := n)) (slotCore prog lazyService created query) :=
  PqxdhDeploymentBackend.commutes_focus cacheLens serviceLens _ (fun x => (x.backend.2.1, x.backend.1))
    (fun x => simulateQ (slotImpl lazyService) ((prog created query).run (PqxdhDeploymentIdealSlots.detach x)))
    (fun _ b r => (b.1, PqxdhDeploymentIdealSlots.attach b.2 r.1 r.2))
    (fun x => PqxdhDeploymentIdealSlots.slotCore_run prog lazyService created query x)
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ _ _ => rfl) (fun _ _ _ _ => rfl)
    (fun _ => LazyOracleDiscard.commutes_simulateQ _ _ slotImpl_commutes _)

variable {ι : Type} {baseSpec : OracleSpec ι} {Reader Response : Type}
  (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)

/-- Every step of the deployment handler with such a core commutes with completing any slot of the lazy cache: the registration commands by `slotCore_commutes`, the fixed steps because they keep the backend (`PqxdhDeploymentSeedSplit.fixed_mapBackend`). -/
theorem handler_commutes (prog : PqxdhLiveServerConstruction.Created Unit → PqxdhDeploymentIdealSlots.SlotProgram KemSK Γ n)
    (created : PqxdhLiveServerConstruction.Created Unit) (query : PqxdhDeploymentInterface.Spec.Domain) :
    Commutes (cacheLens (spec₀ := OutputSpec n) (KemSK := KemSK) (Γ := Alloc Coord n × Γ) (n := n))
      (handlerWith setup codec route (slotCore prog lazyService created) query) := by
  by_cases env : ∃ command : PqxdhRecordLiftInterface.EnvQuery, query = .inr command.val
  · obtain ⟨⟨command, isEnv⟩, rfl⟩ := env
    cases command
    case create pin keyId => exact slotCore_commutes prog created ⟨.create pin keyId, trivial⟩
    case bundle owner => exact slotCore_commutes prog created ⟨.bundle owner, trivial⟩
    case accept raw => exact slotCore_commutes prog created ⟨.accept raw, trivial⟩
    case build session payload => exact slotCore_commutes prog created ⟨.build session payload, trivial⟩
    case finish owner raw => exact slotCore_commutes prog created ⟨.finish owner raw, trivial⟩
    case hmac key message => exact slotCore_commutes prog created ⟨.hmac key message, trivial⟩
    all_goals exact isEnv.elim
  · exact LazyOracleDiscard.commutes_frame _ _ fun x c =>
      (PqxdhDeploymentSeedSplit.fixed_mapBackend setup codec route (fun _ => c) _ _ query
        (fun command same => env ⟨command, same⟩) x).symm

end Core


/-! ### `CE.idealGame` with the message key first or last -/

section Ideal
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response A X : Type}
  (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
  (checks : Checks)
open PqxdhDeploymentInterface (Budget FreshBounds Mode ModeSpec)
open PqxdhDeploymentIdealParams (Target drawParams)
open PqxdhDeploymentIdealSteps (IdealCore IdealBk idealCore idealGame idealInit)
open PqxdhDeploymentFinishErasure (outcomeMap)
open PqxdhServerAuthCtxMaterial (Residual output)
open PqxdhSecretInputKdf (RootOutput)

/-- A uniform 108-byte output is the 32-byte message key and the 76-byte residual drawn in that order, in law (`PqxdhServerAuthCtxMaterial.key_first`). -/
theorem output_key_first {β : Type} (continuation : PqxdhServerAuthKeySchedule.Output → ProbComp β) :
    LawEq (($ᵗ PqxdhServerAuthKeySchedule.Output) >>= continuation)
      (($ᵗ RootOutput) >>= fun key => ($ᵗ Residual) >>= fun rest => continuation (output key rest)) := by
  intro γ _ k
  simp only [bind_assoc]
  exact evalDist_eq_of_evalSPMF_eq _ _ (PqxdhServerAuthCtxMaterial.key_first fun full => continuation full >>= k)

/-- Slot 0 of the two hidden slots, the first slot the allocator assigns. -/
def slot0 : PqxdhRecordLiftInterface.Slot 2 := ⟨0, by decide⟩

/-- The initial backend of the lazy representation of `CE.idealGame g`: the empty lazy slot cache, the empty allocator and the initial ideal backend. -/
def lazyInit (_ : PqxdhLiveServerConstruction.Created Unit) : IdealBk (OutputSpec 2).QueryCache :=
  (∅, (PqxdhRegistrationJointKemSecondEntry.emptyAlloc, IdealCore.initial))

/-- The initial backend of the lazy representation with slot 0 holding a given 108-byte output. -/
def keyInit (value : PqxdhServerAuthKeySchedule.Output) (_ : PqxdhLiveServerConstruction.Created Unit) :
    IdealBk (OutputSpec 2).QueryCache :=
  ((∅ : (OutputSpec 2).QueryCache).cacheQuery slot0 value, (PqxdhRegistrationJointKemSecondEntry.emptyAlloc,
    IdealCore.initial))

/-- `CE.idealGame g` with the message key first (plan section 49 Q3, native form): the 32-byte message key of slot 0, the selected accept's slot, drawn before everything else, then the 76-byte residual and the challenger's draws, then the common deployment experiment with the ideal registration over VCVio's lazy slot cache (`PqxdhDeploymentSeedSplit.lazyService`) whose slot 0 already holds the reassembled 108-byte output (`PqxdhServerAuthCtxMaterial.output`). -/
noncomputable def idealGameKeyFirst (budget : Budget) (g : Fin budget.accept × Fin budget.capacity)
    (ensureInit : StateT A ProbComp Bool) (bounds : FreshBounds) (mode : Mode) (adversary : OracleComp (ModeSpec mode) X) :
    StateT A ProbComp (Option (PqxdhRegistrationJointServerBirth.ClientCreated Unit × X ×
      PqxdhDeploymentSecrecy.Ledger × XState KemSK (IdealBk (OutputSpec 2).QueryCache) 2)) := fun runtime => do
  let key ← $ᵗ RootOutput
  let rest ← $ᵗ Residual
  let p ← drawParams setup budget.create
  (gameWith setup codec route (keyInit (output key rest))
    (idealCore setup codec route checks (Target.ofCE budget g) p lazyService) ensureInit 0 bounds mode adversary).run runtime

/-- `CE.idealGame g` with the message key last: the 76-byte residual of slot 0 first, then the message key, both before the challenger's draws and the game. -/
noncomputable def idealGameKeyLast (budget : Budget) (g : Fin budget.accept × Fin budget.capacity)
    (ensureInit : StateT A ProbComp Bool) (bounds : FreshBounds) (mode : Mode) (adversary : OracleComp (ModeSpec mode) X) :
    StateT A ProbComp (Option (PqxdhRegistrationJointServerBirth.ClientCreated Unit × X ×
      PqxdhDeploymentSecrecy.Ledger × XState KemSK (IdealBk (OutputSpec 2).QueryCache) 2)) := fun runtime => do
  let rest ← $ᵗ Residual
  let key ← $ᵗ RootOutput
  let p ← drawParams setup budget.create
  (gameWith setup codec route (keyInit (output key rest))
    (idealCore setup codec route checks (Target.ofCE budget g) p lazyService) ensureInit 0 bounds mode adversary).run runtime

/-- The lazy representation of `CE.idealGame g`: the ideal registration over item 2's counted lazy table and over VCVio's lazy slot cache give the same law of every view that erases the service state (`PqxdhDeploymentSeedSplit.represent` with `table_service_proj` and `PqxdhDeploymentIdealSteps.idealCore_natural`). -/
theorem idealGame_lazy (budget : Budget) (g : Fin budget.accept × Fin budget.capacity)
    (ensureInit : StateT A ProbComp Bool) (bounds : FreshBounds) (mode : Mode) (adversary : OracleComp (ModeSpec mode) X)
    (runtime : A) :
    LawEq (outcomeMap eraseService <$> (idealGame setup codec route checks budget g ensureInit bounds mode adversary).run
        runtime)
      (drawParams setup budget.create >>= fun p => outcomeMap eraseService <$>
        (gameWith setup codec route lazyInit (idealCore setup codec route checks (Target.ofCE budget g) p lazyService)
          ensureInit 0 bounds mode adversary).run runtime) := by
  simp only [idealGame, StateT.run, map_bind]
  refine LawEq.bind (LawEq.refl _) fun p => ?_
  have law := (PqxdhDeploymentSeedSplit.represent setup codec route
    (fun {S} svc created => idealCore setup codec route checks (Target.ofCE budget g) p (S := S) svc created)
    (PqxdhDeploymentIdealSteps.idealCore_natural setup codec route checks (Target.ofCE budget g) p)
    (fun _ => True) Prod.fst PqxdhDeploymentSeedSplit.tableService lazyService
    PqxdhDeploymentSeedSplit.table_service_proj idealInit (fun _ => trivial) ensureInit 0 bounds mode adversary
    runtime).map (outcomeMap eraseService)
  rw [Functor.map_map] at law
  rw [outcomeMap_erase] at law
  exact law

/-- `CE.idealGame g` with the message key first (plan section 49 Q3, native form): for every view of the outcome that erases the hidden-slot service state, `CE.idealGame g` has the law of the game that draws slot 0's 32-byte message key before everything else, then its 76-byte residual and the challenger's draws, and starts the lazy representation with slot 0 holding the reassembled output. Route: the lazy representation (`idealGame_lazy`), eager sampling of slot 0 (`game_eager`), the key-first split of a uniform output (`output_key_first`), and moving both draws before the challenger's draws (`LazyOracleDiscard.lawEq_swap`). -/
theorem idealGame_key_first (budget : Budget) (g : Fin budget.accept × Fin budget.capacity)
    (ensureInit : StateT A ProbComp Bool) (bounds : FreshBounds) (mode : Mode) (adversary : OracleComp (ModeSpec mode) X)
    (runtime : A) :
    LawEq (outcomeMap eraseService <$> (idealGame setup codec route checks budget g ensureInit bounds mode adversary).run
        runtime)
      (outcomeMap eraseService <$> (idealGameKeyFirst setup codec route checks budget g ensureInit bounds mode
        adversary).run runtime) := by
  refine (idealGame_lazy setup codec route checks budget g ensureInit bounds mode adversary runtime).trans ?_
  simp only [idealGameKeyFirst, StateT.run, map_bind]
  have perP : ∀ p : PqxdhDeploymentIdealParams.Params KemSK budget.create,
      LawEq (outcomeMap eraseService <$> (gameWith setup codec route lazyInit
          (idealCore setup codec route checks (Target.ofCE budget g) p lazyService) ensureInit 0 bounds mode
            adversary).run runtime)
        (($ᵗ RootOutput) >>= fun key => ($ᵗ Residual) >>= fun rest => outcomeMap eraseService <$>
          (gameWith setup codec route (keyInit (output key rest))
            (idealCore setup codec route checks (Target.ofCE budget g) p lazyService) ensureInit 0 bounds mode
              adversary).run runtime) := fun p =>
    (game_eager setup codec route (fun created => idealCore setup codec route checks (Target.ofCE budget g) p lazyService
      created) (fun created => handler_commutes setup codec route _ created) slot0
      (fun _ => (PqxdhRegistrationJointKemSecondEntry.emptyAlloc, IdealCore.initial)) ensureInit 0 bounds mode adversary
      runtime).symm.trans (output_key_first _)
  refine (LawEq.bind (LawEq.refl _) perP).trans ?_
  refine (LazyOracleDiscard.lawEq_swap _ _ _).trans (LawEq.bind (LawEq.refl _) fun key => ?_)
  exact LazyOracleDiscard.lawEq_swap _ _ _

/-- The message key first and the message key last give the same law: the two draws before the game are swapped (`LazyOracleDiscard.lawEq_swap`). -/
theorem idealGame_keyFirst_keyLast (budget : Budget) (g : Fin budget.accept × Fin budget.capacity)
    (ensureInit : StateT A ProbComp Bool) (bounds : FreshBounds) (mode : Mode) (adversary : OracleComp (ModeSpec mode) X)
    (runtime : A) :
    LawEq ((idealGameKeyFirst setup codec route checks budget g ensureInit bounds mode adversary).run runtime)
      ((idealGameKeyLast setup codec route checks budget g ensureInit bounds mode adversary).run runtime) :=
  LazyOracleDiscard.lawEq_swap _ _ _

/-- `CE.idealGame g` with the message key last: for every view of the outcome that erases the hidden-slot service state, `CE.idealGame g` has the law of the game that draws slot 0's 76-byte residual first and its 32-byte message key after it, both before the challenger's draws (`idealGame_key_first`, `idealGame_keyFirst_keyLast`). -/
theorem idealGame_key_last (budget : Budget) (g : Fin budget.accept × Fin budget.capacity)
    (ensureInit : StateT A ProbComp Bool) (bounds : FreshBounds) (mode : Mode) (adversary : OracleComp (ModeSpec mode) X)
    (runtime : A) :
    LawEq (outcomeMap eraseService <$> (idealGame setup codec route checks budget g ensureInit bounds mode adversary).run
        runtime)
      (outcomeMap eraseService <$> (idealGameKeyLast setup codec route checks budget g ensureInit bounds mode
        adversary).run runtime) :=
  (idealGame_key_first setup codec route checks budget g ensureInit bounds mode adversary runtime).trans
    ((idealGame_keyFirst_keyLast setup codec route checks budget g ensureInit bounds mode adversary runtime).map _)

end Ideal

/-! ### The final split form with the message key of slot 0 first -/

section Split
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response A X : Type}
  (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
  (checks : Checks) {count : ℕ}
open PqxdhDeploymentInterface (FreshBounds Mode ModeSpec)
open PqxdhDeploymentIdealParams (Target Params)
open PqxdhDeploymentIdealSteps (IdealCore SplitBk splitInit)
open PqxdhDeploymentIdealKernel (slotRunX MatCache SeedCache lazyDummy)
open PqxdhDeploymentIdealKeys (detachX attachX)
open PqxdhDeploymentIdealDefer (idealSplit installStep)
open PqxdhDeploymentSeedSplit (MaterialSpec)
open PqxdhDeploymentFinishErasure (outcomeMap)
open RawCtxKdfRequestTable (KeyPart NoncePart)

/-- The material cache inside the allocator and the split service state. -/
abbrev materialLens : CacheLens (MaterialSpec 2) (Alloc Coord 2 × (MatCache 2 × SeedCache 2)) :=
  (StateLens.snd (Alloc Coord 2) (MatCache 2 × SeedCache 2)).comp (StateLens.fst (MatCache 2) (SeedCache 2))

/-- A slot step of the final split form in front of the lazy material service commutes with completing any slot of the material cache. -/
theorem slotRunX_commutes {β : Type} (step : StateT (XState KemSK IdealCore 2) (OracleComp SlotSpec) β) :
    Commutes (cacheLens (spec₀ := MaterialSpec 2) (KemSK := KemSK) (Γ := Alloc Coord 2 × IdealCore) (n := 2))
      (slotRunX lazyDummy step) :=
  PqxdhDeploymentBackend.commutes_focus cacheLens materialLens _ (fun x => (x.backend.2.1, (x.backend.1, x.seeds)))
    (fun x => simulateQ (slotImpl lazyDummy) (step.run (detachX x)))
    (fun _ b r => (b.1, attachX b.2 r.1 r.2))
    (fun x => by
      change (fun r => (r.1, attachX r.2.1 r.2.2.1 r.2.2.2)) <$>
        (PqxdhDeploymentIdealErase.onPair lazyDummy step).run (detachX x, (x.backend.2.1, (x.backend.1, x.seeds))) = _
      rw [PqxdhDeploymentIdealErase.onPair_run, Functor.map_map])
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ _ _ => rfl) (fun _ _ _ _ => rfl)
    (fun _ => LazyOracleDiscard.commutes_simulateQ _ _
      (slotImpl_commutes_of lazyDummy (StateLens.fst (MatCache 2) (SeedCache 2))
        (fun j => LazyOracleDiscard.commutes_map _ _ (LazyOracleDiscard.commutes_query _ j))) _)

/-- A hidden install reads only the seed table, so it is a frame of the material cache. -/
theorem installStep_commutes {β : Type} (coords : β × XState KemSK IdealCore 2 → Option Coord)
    (gate : β × XState KemSK IdealCore 2 → Bool)
    (apply : PqxdhRecordLiftSeed.Seed → β × XState KemSK IdealCore 2 → β × XState KemSK IdealCore 2) (b : β) :
    Commutes (cacheLens (spec₀ := MaterialSpec 2) (KemSK := KemSK) (Γ := Alloc Coord 2 × IdealCore) (n := 2))
      (installStep coords gate apply b) := by
  refine LazyOracleDiscard.commutes_frame _ _ fun x c => ?_
  change PqxdhDeploymentIdealDefer.xInstall coords gate apply (b, mapBackend (fun _ => c) x) =
    (fun r => (r.1, mapBackend (fun _ => c) r.2)) <$> PqxdhDeploymentIdealDefer.xInstall coords gate apply (b, x)
  unfold PqxdhDeploymentIdealDefer.xInstall
  have detached : detachX (mapBackend (fun _ => c) x) = detachX x := rfl
  have alloc : (mapBackend (fun _ => c) x).backend.2.1 = x.backend.2.1 := rfl
  simp only [detached, alloc]
  rcases hc : coords (b, detachX x) with _ | point
  · simp only [map_pure]
  · simp only []
    rcases ha : x.backend.2.1.1 point with _ | j
    · simp only [map_pure]
    · simp only []
      cases hg : gate (b, detachX x)
      · simp only [Bool.false_eq_true, ↓reduceIte, map_pure]
      · simp only [↓reduceIte, StateLens.query, StateT.run, Functor.map_map]
        rfl

/-- Every step of the deployment handler with the final split form commutes with completing any slot of the material cache: its slot steps by `slotRunX_commutes`, its hidden installs, which read only the seed table, by `installStep_commutes`, and the fixed steps because they keep the backend. -/
theorem split_handler_commutes (t : Target count) (p : Params KemSK count)
    (created : PqxdhLiveServerConstruction.Created Unit) (query : PqxdhDeploymentInterface.Spec.Domain) :
    Commutes (cacheLens (spec₀ := MaterialSpec 2) (KemSK := KemSK) (Γ := Alloc Coord 2 × IdealCore) (n := 2))
      (handlerWith setup codec route (idealSplit setup codec route checks t p created) query) := by
  by_cases env : ∃ command : PqxdhRecordLiftInterface.EnvQuery, query = .inr command.val
  · obtain ⟨⟨command, isEnv⟩, rfl⟩ := env
    have plain : ∀ q : PqxdhRecordLiftInterface.EnvQuery, Commutes (cacheLens (spec₀ := MaterialSpec 2) (KemSK := KemSK)
        (Γ := Alloc Coord 2 × IdealCore) (n := 2)) (PqxdhDeploymentIdealKeys.slotCoreX
          (PqxdhDeploymentIdealSteps.idealProg setup codec route checks t p
            (PqxdhDeploymentIdealSteps.erasedHidden setup codec checks)) lazyDummy created q) := fun q => by
      rw [PqxdhDeploymentIdealKernel.slotCoreX_run]
      exact slotRunX_commutes _
    cases command
    case create pin keyId => exact plain ⟨.create pin keyId, trivial⟩
    case bundle owner => exact plain ⟨.bundle owner, trivial⟩
    case accept raw => exact plain ⟨.accept raw, trivial⟩
    case hmac key message => exact plain ⟨.hmac key message, trivial⟩
    case build session payload =>
      let gate := fun r : (Option PqxdhServerRegistrationPublication.Response × Option Coord) × XState KemSK IdealCore 2 =>
        (PqxdhDeploymentIdealSteps.publishedKey r.1.1 r.2.base.native.shared.2.server).isSome
      have shape : idealSplit setup codec route checks t p created ⟨.build session payload, isEnv⟩ =
          (fun b => b.1) <$> (slotRunX lazyDummy (PqxdhDeploymentIdealKernel.buildStepC setup codec checks route
            (PqxdhDeploymentIdealSteps.erasedHidden setup codec checks) created session payload) >>= fun b =>
              installStep (fun r => r.1.2) gate PqxdhDeploymentIdealKernel.buildApply b) := by
        apply StateT.ext
        intro x
        rw [StateT.run_map, StateT.run_bind]
        change (fun r => (r.1.1, r.2)) <$> ((slotRunX lazyDummy _).run x >>=
          PqxdhDeploymentIdealDefer.serverInstall) = _
        rfl
      change Commutes (cacheLens (spec₀ := MaterialSpec 2) (KemSK := KemSK) (Γ := Alloc Coord 2 × IdealCore) (n := 2))
        (idealSplit setup codec route checks t p created ⟨.build session payload, isEnv⟩)
      rw [shape]
      exact LazyOracleDiscard.commutes_map _ _ (LazyOracleDiscard.commutes_bind _ (slotRunX_commutes _)
        fun b => installStep_commutes _ _ _ b)
    case finish owner raw =>
      let gate := fun r : (Option Pqxdh.Bytes × Option Coord) × XState KemSK IdealCore 2 =>
        PqxdhDeploymentIdealSteps.establishedAt r.2.base.native.owners owner
      have shape : idealSplit setup codec route checks t p created ⟨.finish owner raw, isEnv⟩ =
          (fun b => b.1) <$> (slotRunX lazyDummy (PqxdhDeploymentIdealKernel.finishStepC setup codec checks route t p
            (PqxdhDeploymentIdealSteps.erasedHidden setup codec checks) created owner raw) >>= fun b =>
              installStep (fun r => r.1.2) gate (PqxdhDeploymentIdealKernel.stepApply owner) b) := by
        apply StateT.ext
        intro x
        rw [StateT.run_map, StateT.run_bind]
        change (fun r => (r.1.1, r.2)) <$> ((slotRunX lazyDummy _).run x >>=
          PqxdhDeploymentIdealDefer.beaconInstall owner) = _
        rfl
      change Commutes (cacheLens (spec₀ := MaterialSpec 2) (KemSK := KemSK) (Γ := Alloc Coord 2 × IdealCore) (n := 2))
        (idealSplit setup codec route checks t p created ⟨.finish owner raw, isEnv⟩)
      rw [shape]
      exact LazyOracleDiscard.commutes_map _ _ (LazyOracleDiscard.commutes_bind _ (slotRunX_commutes _)
        fun b => installStep_commutes _ _ _ b)
    all_goals exact isEnv.elim
  · exact LazyOracleDiscard.commutes_frame _ _ fun x c =>
      (PqxdhDeploymentSeedSplit.fixed_mapBackend setup codec route (fun _ => c) _ _ query
        (fun command same => env ⟨command, same⟩) x).symm

/-- The initial backend of the final split form with slot 0's material already in the material cache. -/
def materialInit (material : PqxdhDeploymentHiddenLayout.Material) (_ : PqxdhLiveServerConstruction.Created Unit) :
    SplitBk :=
  ((∅ : MatCache 2).cacheQuery slot0 material, (PqxdhRegistrationJointKemSecondEntry.emptyAlloc, IdealCore.initial))

/-- The final split form with the message key first (design-v2 section 10.2, `split_key_first`): for every view of the outcome that erases the material cache, the final split game of a target at given parameters has the law of the game that draws slot 0's 32-byte message key `key32` and then its 12-byte nonce before the game and starts with slot 0's material `(key32, nonce12)` in the material cache. `key32` is environment material: the seed of slot 0 (next32, right32) stays a world seed, drawn at its hidden install. Route: eager sampling of slot 0 of the material cache (`game_eager` with `split_handler_commutes`) and the product draw of the material (`PqxdhFullSecretInputKdf.pairSample`). -/
theorem split_key_first (t : Target count) (p : Params KemSK count) (ensureInit : StateT A ProbComp Bool)
    (identityIndex : ℕ) (bounds : FreshBounds) (mode : Mode) (adversary : OracleComp (ModeSpec mode) X) (runtime : A) :
    LawEq (outcomeMap eraseService <$> (gameWith setup codec route splitInit
        (idealSplit setup codec route checks t p) ensureInit identityIndex bounds mode adversary).run runtime)
      (($ᵗ KeyPart) >>= fun key => ($ᵗ NoncePart) >>= fun nonce => outcomeMap eraseService <$>
        (gameWith setup codec route (materialInit (key, nonce)) (idealSplit setup codec route checks t p) ensureInit
          identityIndex bounds mode adversary).run runtime) := by
  refine (game_eager setup codec route (idealSplit setup codec route checks t p)
    (fun created => split_handler_commutes setup codec route checks t p created) slot0
    (fun _ => (PqxdhRegistrationJointKemSecondEntry.emptyAlloc, IdealCore.initial)) ensureInit identityIndex bounds mode
    adversary runtime).symm.trans (LawEq.of_eq ?_)
  rw [← PqxdhFullSecretInputKdf.pairSample]
  simp only [bind_assoc, pure_bind]
  rfl

/-- The final split form with the message key last: slot 0's nonce drawn first and its message key after it, both before the game (`split_key_first`, `LazyOracleDiscard.lawEq_swap`). -/
theorem split_key_last (t : Target count) (p : Params KemSK count) (ensureInit : StateT A ProbComp Bool)
    (identityIndex : ℕ) (bounds : FreshBounds) (mode : Mode) (adversary : OracleComp (ModeSpec mode) X) (runtime : A) :
    LawEq (outcomeMap eraseService <$> (gameWith setup codec route splitInit
        (idealSplit setup codec route checks t p) ensureInit identityIndex bounds mode adversary).run runtime)
      (($ᵗ NoncePart) >>= fun nonce => ($ᵗ KeyPart) >>= fun key => outcomeMap eraseService <$>
        (gameWith setup codec route (materialInit (key, nonce)) (idealSplit setup codec route checks t p) ensureInit
          identityIndex bounds mode adversary).run runtime) :=
  (split_key_first setup codec route checks t p ensureInit identityIndex bounds mode adversary runtime).trans
    (LazyOracleDiscard.lawEq_swap _ _ _)

end Split

end BeaconcryptCore.Computational.PqxdhDeploymentIdealKeyFirst

-- Axiom guards (generated)

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealKeyFirst.outcomeMap_erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealKeyFirst.outcomeMap_erase

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealKeyFirst.game_eager' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealKeyFirst.game_eager

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealKeyFirst.slotImpl_commutes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealKeyFirst.slotImpl_commutes

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealKeyFirst.slotImpl_commutes_of' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealKeyFirst.slotImpl_commutes_of

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealKeyFirst.slotCore_commutes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealKeyFirst.slotCore_commutes

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealKeyFirst.handler_commutes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealKeyFirst.handler_commutes

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealKeyFirst.output_key_first' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealKeyFirst.output_key_first

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealKeyFirst.idealGame_lazy' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealKeyFirst.idealGame_lazy

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealKeyFirst.idealGame_key_first' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealKeyFirst.idealGame_key_first

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealKeyFirst.idealGame_keyFirst_keyLast' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealKeyFirst.idealGame_keyFirst_keyLast

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealKeyFirst.idealGame_key_last' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealKeyFirst.idealGame_key_last

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealKeyFirst.slotRunX_commutes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealKeyFirst.slotRunX_commutes

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealKeyFirst.installStep_commutes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealKeyFirst.installStep_commutes

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealKeyFirst.split_handler_commutes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealKeyFirst.split_handler_commutes

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealKeyFirst.split_key_first' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealKeyFirst.split_key_first

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealKeyFirst.split_key_last' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealKeyFirst.split_key_last
