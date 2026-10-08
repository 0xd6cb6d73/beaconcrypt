-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhDeploymentSeedSplit
import BeaconcryptCore.Computational.PqxdhRegistrationJointKemSecondEntryTable

/-!
# Registration cores from slot programs, and their naturality (CE-11b, generic)

The ideal registration of the common deployment experiment (CE-11b) reads its hidden 108-byte key-schedule outputs at item 2's coordinates (the 128 bytes of DH outputs of a hidden root, `Coord`) through item 2's first-touch allocator `PqxdhRegistrationJointKemSecondEntry.slotImpl`, which maps a new coordinate to the next free slot and reads the slot's value only through a slot service. This module is the generic part of that construction; it contains no protocol step.

- A slot program (`SlotProgram KemSK Γ n`) answers each registration command as a stateful client of coins and of value requests at coordinates (`SlotSpec`), on the extended deployment state with a backend `Γ` that holds neither the allocator nor the service state.
- `slotCore prog svc created` turns a family of slot programs into a registration handler (`PqxdhDeploymentBackend.RegImpl`) on the backend `S × (Alloc Coord n × Γ)`: the service state `S`, the allocator and `Γ`. Each command detaches the slot program's state (`detach`), runs the program under `slotImpl svc` from the allocator and service state of the backend, and attaches the results (`attach`).
- `slot_natural_law` is the in-law variant of item 2's `PqxdhRegistrationJointKemSecondEntry.slot_natural` (item 2 plan section 21, note 5): a projection of service states that carries every service step to the corresponding step of another service in law (`LazyOracleDiscard.LawEq`), from states satisfying an invariant, and keeps the invariant, carries every allocator client in law with the allocator unchanged. `slot_natural_proj` is the same with the premise bundled as CE-11a's `PqxdhDeploymentSeedSplit.ServiceProj`.
- `slotCore_natural`: every core built by `slotCore` is natural in CE-11a's sense (`PqxdhDeploymentSeedSplit.CoreNatural`), whatever its slot programs. This is the naturality premise of `PqxdhDeploymentSeedSplit.represent` and `represent_split` for the ideal registration of CE-11b, which is built by `slotCore`.

These are program equalities and equalities in law of lazily sampled tables; they charge nothing and make no security claim.
-/

open OracleComp OracleSpec

set_option autoImplicit false

namespace BeaconcryptCore.Computational.PqxdhDeploymentIdealSlots
open PqxdhDeploymentBackend (XState RegImpl)
open PqxdhDeploymentSeedSplit (ServiceProj CoreNatural mapBackend lawEq_run_simulateQ_of_proj)
open PqxdhRegistrationJointKemSecondEntry (Alloc slotImpl slot_coin slot_some slot_none)
open LazyOracleDiscard (LawEq)
open PqxdhRecordLiftInterface (EnvQuery EnvSpec)

/-! ### Invariants of stateful simulations -/

/-- An invariant kept by every step of a stateful handler is kept by every program it simulates. -/
theorem simulateQ_keeps {ι' σ α : Type} {spec' : OracleSpec ι'} (impl : QueryImpl spec' (StateT σ ProbComp))
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

/-! ### Naturality of the first-touch allocator in law -/

section Allocator
variable {D R : Type} [DecidableEq D] [SampleableType R] {n : ℕ}

/-- Every step of the allocator in front of a slot service keeps an invariant of the service state that every service step keeps. -/
theorem slot_keeps {S : Type} (service : PqxdhRegistrationJointKemSecondEntry.SlotService S R n) (inv : S → Prop)
    (keeps : ∀ slot state, inv state → ∀ result ∈ support ((service slot).run state), inv result.2)
    (query : (PqxdhRegistrationJointKemSecondEntry.Spec D R).Domain) (current : Alloc D n × S) (good : inv current.2) :
    ∀ result ∈ support ((slotImpl service query).run current), inv result.2.2 := by
  intro result member
  rcases query with coin | point
  · rw [slot_coin, support_map] at member
    obtain ⟨reply, -, rfl⟩ := member
    exact good
  · rcases found : current.1.1 point with _ | slot
    · by_cases room : current.1.2 < n
      · rw [slot_none _ _ _ found room, support_map] at member
        obtain ⟨inner, innerMember, rfl⟩ := member
        exact keeps _ _ good inner innerMember
      · simp only [slotImpl, QueryImpl.add_apply_inr, StateT.run_mk, found, room, dite_false,
          support_map] at member
        obtain ⟨answer, -, rfl⟩ := member
        exact good
    · rw [slot_some _ _ _ _ found, support_map] at member
      obtain ⟨inner, innerMember, rfl⟩ := member
      exact keeps _ _ good inner innerMember

/-- One step of the allocator transports in law along a projection of the service state that carries every service step in law: a coin and the no-room branch are the same program on both sides, and a found or newly allocated slot is the service step with the allocator update attached. -/
theorem slot_step_law {S₁ S₂ : Type} (service₁ : PqxdhRegistrationJointKemSecondEntry.SlotService S₁ R n)
    (service₂ : PqxdhRegistrationJointKemSecondEntry.SlotService S₂ R n) (inv : S₁ → Prop) (proj : S₁ → S₂)
    (step : ∀ slot state, inv state →
      LawEq (Prod.map id proj <$> (service₁ slot).run state) ((service₂ slot).run (proj state)))
    (query : (PqxdhRegistrationJointKemSecondEntry.Spec D R).Domain) (allocNow : Alloc D n) (inner : S₁)
    (good : inv inner) :
    LawEq (Prod.map id (Prod.map id proj) <$> (slotImpl service₁ query).run (allocNow, inner))
      ((slotImpl service₂ query).run (allocNow, proj inner)) := by
  rcases query with coin | point
  · refine LawEq.of_eq ?_
    rw [slot_coin, slot_coin, Functor.map_map]
    rfl
  · rcases found : allocNow.1 point with _ | slot
    · by_cases room : allocNow.2 < n
      · rw [slot_none (state := (allocNow, inner)) _ _ found room,
          slot_none (state := (allocNow, proj inner)) _ _ found room, Functor.map_map]
        have mapped := (step ⟨allocNow.2, room⟩ inner good).map
          (fun result => (result.1, ((Function.update allocNow.1 point (some ⟨allocNow.2, room⟩), allocNow.2 + 1),
            result.2)))
        rw [Functor.map_map] at mapped
        exact mapped
      · refine LawEq.of_eq ?_
        have left : (slotImpl service₁ (.inr point)).run (allocNow, inner) =
            (fun answer => (answer, (allocNow, inner))) <$> ($ᵗ R) := by
          simp [slotImpl, found, room]
        have right : (slotImpl service₂ (.inr point)).run (allocNow, proj inner) =
            (fun answer => (answer, (allocNow, proj inner))) <$> ($ᵗ R) := by
          simp [slotImpl, found, room]
        rw [left, right, Functor.map_map]
        rfl
    · rw [slot_some (state := (allocNow, inner)) _ _ _ found, slot_some (state := (allocNow, proj inner)) _ _ _ found,
        Functor.map_map]
      have mapped := (step slot inner good).map (fun result => (result.1, (allocNow, result.2)))
      rw [Functor.map_map] at mapped
      exact mapped

/-- In-law naturality of the first-touch allocator (item 2 plan section 21, note 5; the `LawEq` variant of `PqxdhRegistrationJointKemSecondEntry.slot_natural`): a projection of service states that carries every step of one slot service to the corresponding step of another in law, from states satisfying an invariant, and keeps the invariant, carries every client of the allocator in law, with the allocator state unchanged, and the invariant holds on every outcome. -/
theorem slot_natural_law {S₁ S₂ α : Type} (service₁ : PqxdhRegistrationJointKemSecondEntry.SlotService S₁ R n)
    (service₂ : PqxdhRegistrationJointKemSecondEntry.SlotService S₂ R n) (inv : S₁ → Prop) (proj : S₁ → S₂)
    (step : ∀ slot state, inv state →
      LawEq (Prod.map id proj <$> (service₁ slot).run state) ((service₂ slot).run (proj state)))
    (keeps : ∀ slot state, inv state → ∀ result ∈ support ((service₁ slot).run state), inv result.2)
    (client : OracleComp (PqxdhRegistrationJointKemSecondEntry.Spec D R) α) (alloc : Alloc D n) (state : S₁)
    (holds : inv state) :
    LawEq (Prod.map id (Prod.map id proj) <$> (simulateQ (slotImpl service₁) client).run (alloc, state))
        ((simulateQ (slotImpl service₂) client).run (alloc, proj state)) ∧
      ∀ result ∈ support ((simulateQ (slotImpl service₁) client).run (alloc, state)), inv result.2.2 :=
  ⟨lawEq_run_simulateQ_of_proj (slotImpl service₁) (slotImpl service₂) (fun current => inv current.2)
      (Prod.map id proj) (fun query current good => slot_step_law service₁ service₂ inv proj step query current.1
        current.2 good)
      (fun query current good => slot_keeps service₁ inv keeps query current good) client (alloc, state) holds,
    simulateQ_keeps (slotImpl service₁) (fun current => inv current.2)
      (fun query current good => slot_keeps service₁ inv keeps query current good) client (alloc, state) holds⟩

end Allocator

/-- `slot_natural_law` for CE-11a's slot services, with the premise bundled as a service projection (`PqxdhDeploymentSeedSplit.ServiceProj`). -/
theorem slot_natural_proj {D S₁ S₂ α : Type} [DecidableEq D] {n : ℕ}
    (svc₁ : PqxdhDeploymentSeedSplit.SlotService S₁ n) (svc₂ : PqxdhDeploymentSeedSplit.SlotService S₂ n)
    (inv : S₁ → Prop) (proj : S₁ → S₂) (related : ServiceProj inv proj svc₁ svc₂)
    (client : OracleComp (PqxdhRegistrationJointKemSecondEntry.Spec D PqxdhServerAuthKeySchedule.Output) α)
    (alloc : Alloc D n) (state : S₁) (holds : inv state) :
    LawEq (Prod.map id (Prod.map id proj) <$> (simulateQ (slotImpl svc₁) client).run (alloc, state))
        ((simulateQ (slotImpl svc₂) client).run (alloc, proj state)) ∧
      ∀ result ∈ support ((simulateQ (slotImpl svc₁) client).run (alloc, state)), inv result.2.2 :=
  slot_natural_law svc₁ svc₂ inv proj (fun slot state good => (related slot state good).1)
    (fun slot state good => (related slot state good).2) client alloc state holds

/-! ### Slot programs and the slot core -/

/-- Item 2's hidden-read coordinates: the 128 bytes of DH outputs of a hidden root. -/
abbrev Coord := PqxdhCorrelatedExtractFamily.Message

/-- The client interface of a registration step: coins, and value requests at coordinates. -/
abbrev SlotSpec := PqxdhRegistrationJointKemSecondEntry.Spec Coord PqxdhServerAuthKeySchedule.Output

/-- A slot program: every registration command as a stateful client of coins and of value requests at coordinates, on the extended deployment state with a backend that holds neither the allocator nor the service state. -/
abbrev SlotProgram (KemSK Γ : Type) (n : ℕ) :=
  (query : EnvQuery) → StateT (XState KemSK Γ n) (OracleComp SlotSpec) (EnvSpec.Range query)

section Core
variable {KemSK Γ : Type} {n : ℕ}

/-- The slot program's state inside a slot core's state: the backend without the service state and the allocator. -/
def detach {S : Type} (x : XState KemSK (S × (Alloc Coord n × Γ)) n) : XState KemSK Γ n :=
  ⟨x.base, x.backend.2.2, x.seeds, x.snap, x.log⟩

/-- A slot core's state from a slot program's state, an allocator and a service state. -/
def attach {S : Type} (y : XState KemSK Γ n) (a : Alloc Coord n) (s : S) : XState KemSK (S × (Alloc Coord n × Γ)) n :=
  ⟨y.base, (s, (a, y.backend)), y.seeds, y.snap, y.log⟩

/-- Detaching after attaching gives the slot program's state back. -/
theorem detach_attach {S : Type} (y : XState KemSK Γ n) (a : Alloc Coord n) (s : S) : detach (attach y a s) = y := rfl

/-- Attaching the detached state, the allocator and the service state of a slot core's state gives that state back. -/
theorem attach_detach {S : Type} (x : XState KemSK (S × (Alloc Coord n × Γ)) n) :
    attach (detach x) x.backend.2.1 x.backend.1 = x := rfl

/-- Replacing the service state commutes with attaching. -/
theorem mapBackend_attach {S₁ S₂ : Type} (proj : S₁ → S₂) (y : XState KemSK Γ n) (a : Alloc Coord n) (s : S₁) :
    mapBackend proj (attach y a s) = attach y a (proj s) := rfl

/-- Replacing the service state does not change the detached state. -/
theorem detach_mapBackend {S₁ S₂ : Type} (proj : S₁ → S₂) (x : XState KemSK (S₁ × (Alloc Coord n × Γ)) n) :
    detach (mapBackend proj x) = detach x := rfl

/-- A registration core from slot programs: each command runs its slot program on the detached state, with the program's value requests answered by the first-touch allocator in front of the slot service, from the allocator and the service state of the backend, and attaches the results. -/
noncomputable def slotCore (prog : PqxdhLiveServerConstruction.Created Unit → SlotProgram KemSK Γ n) {S : Type}
    (svc : PqxdhDeploymentSeedSplit.SlotService S n) (created : PqxdhLiveServerConstruction.Created Unit) :
    RegImpl KemSK (S × (Alloc Coord n × Γ)) n :=
  fun query => StateT.mk fun x =>
    (fun r => (r.1.1, attach r.1.2 r.2.1 r.2.2)) <$>
      (simulateQ (slotImpl svc) ((prog created query).run (detach x))).run (x.backend.2.1, x.backend.1)

/-- One step of a slot core, unfolded. -/
theorem slotCore_run (prog : PqxdhLiveServerConstruction.Created Unit → SlotProgram KemSK Γ n) {S : Type}
    (svc : PqxdhDeploymentSeedSplit.SlotService S n) (created : PqxdhLiveServerConstruction.Created Unit)
    (query : EnvQuery) (x : XState KemSK (S × (Alloc Coord n × Γ)) n) :
    (slotCore prog svc created query).run x =
      (fun r => (r.1.1, attach r.1.2 r.2.1 r.2.2)) <$>
        (simulateQ (slotImpl svc) ((prog created query).run (detach x))).run (x.backend.2.1, x.backend.1) := rfl

/-- Every core built from slot programs is natural (`PqxdhDeploymentSeedSplit.CoreNatural`): it reads slot outputs only through its slot service, so every command transports in law along every service projection and keeps the projection's invariant. -/
theorem slotCore_natural (prog : PqxdhLiveServerConstruction.Created Unit → SlotProgram KemSK Γ n) :
    CoreNatural (KemSK := KemSK) (Γ := Alloc Coord n × Γ) (fun {S} svc created => slotCore prog (S := S) svc created) := by
  intro S₁ S₂ inv proj svc₁ svc₂ related created query state holds
  have moved := slot_natural_proj svc₁ svc₂ inv proj related ((prog created query).run (detach state))
    state.backend.2.1 state.backend.1 holds
  refine ⟨?_, ?_⟩
  · rw [slotCore_run, slotCore_run, detach_mapBackend, Functor.map_map]
    have mapped := moved.1.map (fun r : (EnvSpec.Range query × XState KemSK Γ n) × (Alloc Coord n × S₂) =>
      (r.1.1, attach r.1.2 r.2.1 r.2.2))
    rw [Functor.map_map] at mapped
    exact mapped
  · intro result member
    rw [slotCore_run, support_map] at member
    obtain ⟨inner, innerMember, rfl⟩ := member
    exact moved.2 inner innerMember

end Core

end BeaconcryptCore.Computational.PqxdhDeploymentIdealSlots

-- Axiom guards (generated)

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealSlots.simulateQ_keeps' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealSlots.simulateQ_keeps

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealSlots.slot_keeps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealSlots.slot_keeps

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealSlots.slot_step_law' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealSlots.slot_step_law

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealSlots.slot_natural_law' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealSlots.slot_natural_law

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealSlots.slot_natural_proj' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealSlots.slot_natural_proj

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealSlots.detach_attach' does not depend on any axioms
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealSlots.detach_attach

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealSlots.attach_detach' does not depend on any axioms
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealSlots.attach_detach

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealSlots.mapBackend_attach' does not depend on any axioms
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealSlots.mapBackend_attach

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealSlots.detach_mapBackend' does not depend on any axioms
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealSlots.detach_mapBackend

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealSlots.slotCore_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealSlots.slotCore_run

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealSlots.slotCore_natural' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealSlots.slotCore_natural
