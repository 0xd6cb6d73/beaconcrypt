-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhDeploymentIdealPostChallenge

/-!
# Item 2's side of the middle execution: invariant, steps and simulation (CE-11b, unit U6, fourth part)

`PqxdhDeploymentIdealPostSim.sim_option` reduces item 2's side of the post-challenge simulation to two per-request obligations: every simulated request of the middle source handler is answered by item 2's two layers as its projection (`step`), and every middle step keeps an invariant and accounts for the costly requests against a room (`keep`). This module states the invariant, discharges both obligations at item 2's view without table counters (`PqxdhDeploymentIdealPostHidden.StepAtC`, `encodeMidC`, `lowerEC`), and instantiates the simulation.

- The classes: `Allowed` (every source request but an identity or a KEM field read), `Costly` (the creations) and `room` (the challenger's pool entries not yet created).
- The invariant `ItemInv`: item 2's ownership of the annotated state with the Server's identity slot and one KEM key pair per owner (`PqxdhDeploymentIdealPoolSource.PoolOwned`), a prefix KEM pool, the owner positions (`PqxdhDeploymentIdealCut.PoolIndexed`), the selected accept done and active, a good allocator state and a stored value at the mark's coordinates.
- `step_all`: every simulated request at a middle state with the invariant and room for a creation, by the third and fourth parts' steps (coins, BLAKE2b, kernel reveal, HMAC, local field reads, creates, bundles, raw accepts other than the selected one, real and marked builds, and every finish by `PqxdhDeploymentIdealPostChallenge.step_finishActive`).
- The pool: `indices_set`, `source_indices` (every request but a creation keeps the owners' KEM indices), `not_costly` and `sourcePool_keep` (item 2's annotated pool source keeps the invariant at the pool, with one more key pair exactly after a creation).
- The middle steps: `groupedOwnerCE_fields` and `challenge_fields` (owner k's challenge finish returns the owner with its identity and at most its own live KEM key pair, through VCVio's `support_simulateQ_run'_subset`), `bump_facts`, `keep_real`, `keep_buildHidden`, `keep_challenge` and `keep_all`.
- `item_sim`: item 2's two layers on a source program with only simulated requests and at most the room's number of creations, from item 2's view of a middle state with the invariant, run without stopping as the projection of the program's middle run. It needs the constructed Server's public identity to be its seed's.

These are program equalities and support facts. They charge nothing and make no security claim.
-/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc

set_option autoImplicit false

namespace BeaconcryptCore.Computational.PqxdhDeploymentIdealPostInvariant
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhDeploymentIdealPostSource (Mid sourceMid realMid)
open PqxdhDeploymentIdealPostHidden (StepAtC encodeMidC lowerEC stepAtC_of_stepAt)
open PqxdhDeploymentIdealParams (Target Params)
open PqxdhRegistrationJointRevealCosts (sourceKind)

variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}

/-! ### The request classes and the room -/

section Classes

/-- The source requests that item 2's side simulates: every request but an identity or a KEM field read (the prekey, one-time prekey and kernel reads are local). -/
def Allowed (query : (PqxdhRegistrationJointRevealSchedule.Spec KemSK).Domain) : Prop :=
  sourceKind query ≠ .inr 0 ∧ sourceKind query ≠ .inr 1

/-- Deciding the simulated requests. -/
instance : DecidablePred (Allowed (KemSK := KemSK)) := fun _ => by
  unfold Allowed
  infer_instance

/-- The costly source requests: the creations, which take a key pair from the challenger's pool. -/
def Costly (query : (PqxdhRegistrationJointRevealSchedule.Spec KemSK).Domain) : Prop :=
  sourceKind query = .inl 1

/-- Deciding the costly requests. -/
instance : DecidablePred (Costly (KemSK := KemSK)) := fun _ => by
  unfold Costly
  infer_instance

/-- The room for creations at a middle state: the challenger's pool entries not yet created. -/
def room {count : ℕ} (t : Target count) (p : Params KemSK count) (m : Mid KemSK) : ℕ :=
  (p.pool t).length - m.joint.pool.2.keys.length

end Classes

/-! ### The invariant of item 2's side -/

/-- The invariant of the middle execution that item 2's steps need: item 2's ownership of the annotated state with the Server's identity slot and one KEM key pair per owner, a prefix KEM pool, the owner positions, the selected accept done and active, a good allocator state, and a stored value at the mark's coordinates. -/
structure ItemInv {count : ℕ} (created : PqxdhLiveServerConstruction.Created Unit) (t : Target count)
    (p : Params KemSK count) (m : Mid KemSK) : Prop where
  owned : PqxdhDeploymentIdealPoolSource.PoolOwned created.seed created.server.server.metadata.identityIndex m.joint
  prefixed : PqxdhDeploymentIdealPoolSource.PoolPrefix (p.pool t) m.joint.pool.2
  indexed : PqxdhDeploymentIdealCut.PoolIndexed m.joint
  active : m.backend.2.2.active = true
  done : t.accept < m.backend.2.2.accepts
  good : PqxdhRegistrationJointKemSecondEntry.SlotGood (m.backend.2.1, m.backend.1)
  stored : ∀ mark, m.backend.2.2.marks = some mark →
    (PqxdhRegistrationJointKemSecondEntry.cacheOf (m.backend.2.1, m.backend.1) mark.2).isSome

/-! ### Every simulated request -/

section Steps
variable (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
  (checks : Checks) {count : ℕ} (t : Target count) (p : Params KemSK count)
  (created : PqxdhLiveServerConstruction.Created Unit)

/-- Every simulated source request at a middle state with the invariant, with room for a creation: item 2's two layers answer it from item 2's view without table counters as the middle source handler does (`sim_option`'s per-request obligation). It needs the constructed Server's public identity to be its seed's. -/
theorem step_all (identity : created.publicIdentity = setup.joint.publicKeys created.seed)
    (query : (PqxdhRegistrationJointRevealSchedule.Spec KemSK).Domain) (m : Mid KemSK) (inv : ItemInv created t p m)
    (allowed : Allowed query) (fits : Costly query → 0 < room t p m) :
    StepAtC setup codec route checks t p created query m := by
  rcases query with (coin | request) | ⟨address, field⟩
  · exact stepAtC_of_stepAt setup codec route checks t p created _ m
      (PqxdhDeploymentIdealPostSteps.step_coin setup codec route checks t p created coin m)
  · cases request with
    | create pin keyId =>
        have positive := fits rfl
        unfold room at positive
        exact stepAtC_of_stepAt setup codec route checks t p created _ m
          (PqxdhDeploymentIdealPostRequests.step_create setup codec route checks t p created pin keyId m inv.owned.2
            inv.prefixed (by omega))
    | bundle address =>
        exact stepAtC_of_stepAt setup codec route checks t p created _ m
          (PqxdhDeploymentIdealPostRequests.step_bundle setup codec route checks t p created address m inv.owned.1.1
            inv.prefixed)
    | accept raw =>
        exact stepAtC_of_stepAt setup codec route checks t p created _ m
          (PqxdhDeploymentIdealPostServer.step_accept setup codec route checks t p created raw m (Nat.ne_of_gt inv.done)
            inv.owned.1.2 identity inv.prefixed)
    | build session payload =>
        cases hidden : PqxdhDeploymentIdealPostSource.buildHiddenAt m session
        · exact stepAtC_of_stepAt setup codec route checks t p created _ m
            (PqxdhDeploymentIdealPostServer.step_build setup codec route checks t p created session payload m hidden)
        · rcases marked : m.backend.2.2.marks with _ | ⟨index, coords⟩
          · simp [PqxdhDeploymentIdealPostSource.buildHiddenAt, marked] at hidden
          · have facts : index = session ∧ (m.joint.shared.2.pending session).isSome = true := by
              simpa [PqxdhDeploymentIdealPostSource.buildHiddenAt, marked] using hidden
            obtain ⟨rfl, pending⟩ := facts
            obtain ⟨value, held⟩ := Option.isSome_iff_exists.mp (inv.stored (index, coords) marked)
            rcases allocated : m.backend.2.1.1 coords with _ | slot
            · simp [PqxdhRegistrationJointKemSecondEntry.cacheOf, allocated] at held
            · have stored : m.backend.1.1 slot = some value := by
                simpa [PqxdhRegistrationJointKemSecondEntry.cacheOf, allocated] using held
              exact PqxdhDeploymentIdealPostHidden.step_build_hidden setup codec route checks t p created index payload m
                coords marked pending slot allocated value stored
    | finish address raw =>
        exact PqxdhDeploymentIdealPostChallenge.step_finishActive setup codec route checks t p created address raw m
          inv.active inv.owned.1.1
          (fun entry found => PqxdhDeploymentIdealCut.indexed_entry m.joint inv.indexed address entry found)
          inv.prefixed inv.good inv.stored
    | hmac key message =>
        exact stepAtC_of_stepAt setup codec route checks t p created _ m
          (PqxdhDeploymentIdealPostRequests.step_hmac setup codec route checks t p created key message m)
    | hash bytes =>
        exact stepAtC_of_stepAt setup codec route checks t p created _ m
          (PqxdhDeploymentIdealPostSteps.step_hash setup codec route checks t p created bytes m)
    | reveal keyId =>
        exact stepAtC_of_stepAt setup codec route checks t p created _ m
          (PqxdhDeploymentIdealPostSteps.step_reveal setup codec route checks t p created keyId m)
  · cases field
    · exact absurd rfl allowed.1
    · exact absurd rfl allowed.2
    · exact stepAtC_of_stepAt setup codec route checks t p created _ m
        (PqxdhDeploymentIdealPostRequests.step_read setup codec route checks t p created address .prekey trivial m)
    · exact stepAtC_of_stepAt setup codec route checks t p created _ m
        (PqxdhDeploymentIdealPostRequests.step_read setup codec route checks t p created address .oneTime trivial m)
    · exact stepAtC_of_stepAt setup codec route checks t p created _ m
        (PqxdhDeploymentIdealPostRequests.step_read setup codec route checks t p created address .kernel trivial m)

end Steps

/-! ### Item 2's annotated pool source keeps the invariant at the pool -/

section Pool
open PqxdhDeploymentIdealPoolSource (PoolOwned PoolPrefix sourcePool)
open PqxdhRegistrationJointOwnership (Entry)
variable (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)

/-- Replacing an owner entry by one with the same KEM index keeps the list of KEM indices. -/
theorem indices_set (owners : List (Entry KemSK)) (address : ℕ) (entry : Entry KemSK)
    (found : owners[address]? = some entry) (owner : PqxdhRegistrationSchedule.Owner KemSK) :
    (owners.set address { entry with owner := owner }).map Entry.kemIndex = owners.map Entry.kemIndex := by
  apply List.ext_getElem?
  intro index
  rw [List.getElem?_map, List.getElem?_map, List.getElem?_set]
  by_cases same : address = index
  · subst same
    obtain ⟨bound, equal⟩ := List.getElem?_eq_some_iff.mp found
    simp [bound, ← equal]
  · simp [same]

/-- Every request of the annotated source schedule other than a creation keeps every owner entry's KEM index. -/
theorem source_indices (seed : PqxdhJointIdentity.IdentitySeed) (identityIndex : ℕ)
    (query : (PqxdhRegistrationJointRevealSchedule.Spec KemSK).Domain)
    (notCreate : ∀ pin keyId, query ≠ .inl (.inr (.create pin keyId))) (state : PqxdhRegistrationJointSchedule.State KemSK)
    (result : (PqxdhRegistrationJointRevealSchedule.Spec KemSK).Range query × PqxdhRegistrationJointSchedule.State KemSK)
    (supported : result ∈ support
      ((PqxdhRegistrationJointServerSchedule.source setup codec checks seed identityIndex query).run state)) :
    result.2.owners.map Entry.kemIndex = state.owners.map Entry.kemIndex := by
  have shared : ∀ {Value : Type} (work : PqxdhServerAuthNative.NativeGame KemSK Value)
      (result : Value × PqxdhRegistrationJointSchedule.State KemSK),
      result ∈ support ((PqxdhRegistrationJointSchedule.onShared work).run state) →
        result.2.owners.map Entry.kemIndex = state.owners.map Entry.kemIndex := by
    intro Value work result member
    simp only [PqxdhRegistrationJointSchedule.onShared, StateT.run, support_map, Set.mem_image] at member
    obtain ⟨reached, _, rfl⟩ := member
    rfl
  rcases query with (coin | request) | read
  case inl.inl =>
    simp only [PqxdhRegistrationJointServerSchedule.source, PqxdhRegistrationJointRevealSchedule.source,
      PqxdhRegistrationJointSchedule.handler, StateT.run_lift, bind_pure_comp, support_map, Set.mem_image] at supported
    obtain ⟨_, _, rfl⟩ := supported
    rfl
  case inl.inr =>
    cases request with
    | create pin keyId => exact absurd rfl (notCreate pin keyId)
    | accept raw =>
        change result ∈ support ((PqxdhRegistrationJointServerSchedule.onBackend
          (PqxdhRegistrationJointServerAccept.source setup codec checks seed identityIndex raw)).run state) at supported
        obtain ⟨reached, -, rfl⟩ : ∃ reached ∈ support
            ((PqxdhRegistrationJointServerAccept.source setup codec checks seed identityIndex raw).run
              (state.pool, state.shared)),
            (reached.1, { state with pool := reached.2.1, shared := reached.2.2 }) = result := by
          simpa only [PqxdhRegistrationJointServerSchedule.onBackend, StateT.run, support_map, Set.mem_image]
            using supported
        rfl
    | bundle address =>
        cases found : state.owners[address]? <;>
          simp only [PqxdhRegistrationJointServerSchedule.source, PqxdhRegistrationJointRevealSchedule.source,
            PqxdhRegistrationJointSchedule.handler, PqxdhRegistrationJointSchedule.bundle, StateT.run, found,
            support_map, Set.mem_image, mem_support_pure_iff] at supported
        case none => exact supported ▸ rfl
        case some entry =>
          obtain ⟨reached, _, rfl⟩ := supported
          exact indices_set state.owners address entry found _
    | finish address raw =>
        cases found : state.owners[address]? <;>
          simp only [PqxdhRegistrationJointServerSchedule.source, PqxdhRegistrationJointRevealSchedule.source,
            PqxdhRegistrationJointSchedule.handler, PqxdhRegistrationJointSchedule.finish, StateT.run, found,
            support_map, Set.mem_image, mem_support_pure_iff] at supported
        case none => exact supported ▸ rfl
        case some entry =>
          obtain ⟨reached, _, rfl⟩ := supported
          exact indices_set state.owners address entry found _
    | build session payload => exact shared _ result supported
    | hmac key message => exact shared _ result supported
    | hash bytes => exact shared _ result supported
    | reveal keyId => exact shared _ result supported
  case inr =>
    have reached : result = PqxdhRegistrationJointLiveRead.sourceStep read state := by
      simpa only [PqxdhRegistrationJointServerSchedule.source, PqxdhRegistrationJointRevealSchedule.source, StateT.run,
        support_pure, Set.mem_singleton_iff] using supported
    subst reached
    cases found : state.owners[read.1]? with
    | none => simp [PqxdhRegistrationJointLiveRead.sourceStep, found]
    | some entry => simp [PqxdhRegistrationJointLiveRead.sourceStep, found]

/-- A request other than a creation is not costly. -/
theorem not_costly (query : (PqxdhRegistrationJointRevealSchedule.Spec KemSK).Domain)
    (notCreate : ∀ pin keyId, query ≠ .inl (.inr (.create pin keyId))) : ¬ Costly query := by
  rcases query with (coin | request) | read
  · simp [Costly, sourceKind, PqxdhRegistrationSchedule.sourceKind]
  · cases request with
    | create pin keyId => exact absurd rfl (notCreate pin keyId)
    | _ => simp [Costly, sourceKind, PqxdhRegistrationSchedule.sourceKind]
  · simp [Costly, sourceKind]

/-- Every request of item 2's annotated pool source keeps the invariant at the pool (the source-side representation invariant, a prefix KEM pool and the owner positions), with one more key pair exactly after a creation, when a creation has room in the challenger's pool. -/
theorem sourcePool_keep (seed : PqxdhJointIdentity.IdentitySeed) (identityIndex : ℕ)
    (pairs : List (PqxdhLiveKemReservation.Pair KemSK)) (query : (PqxdhRegistrationJointRevealSchedule.Spec KemSK).Domain)
    (state : PqxdhRegistrationJointSchedule.State KemSK) (owned : PoolOwned seed identityIndex state)
    (prefixed : PoolPrefix pairs state.pool.2) (indexed : PqxdhDeploymentIdealCut.PoolIndexed state)
    (fits : Costly query → state.pool.2.keys.length < pairs.length)
    (result : (PqxdhRegistrationJointRevealSchedule.Spec KemSK).Range query × PqxdhRegistrationJointSchedule.State KemSK)
    (supported : result ∈ support ((sourcePool setup codec checks seed identityIndex pairs query).run state)) :
    PoolOwned seed identityIndex result.2 ∧ PoolPrefix pairs result.2.pool.2 ∧
      PqxdhDeploymentIdealCut.PoolIndexed result.2 ∧
      result.2.pool.2.keys.length = state.pool.2.keys.length + (if Costly query then 1 else 0) := by
  refine ⟨PqxdhDeploymentIdealPoolSource.query_poolOwned setup codec checks seed identityIndex pairs query state result owned
    supported, ?_⟩
  by_cases creation : ∃ pin keyId, query = .inl (.inr (.create pin keyId))
  · obtain ⟨pin, keyId, rfl⟩ := creation
    change result ∈ support (PqxdhRegistrationJointSchedule.created setup pin keyId state <$>
      PqxdhDeploymentIdealPoolSource.materialPool setup pairs state.owners.length) at supported
    rw [support_map] at supported
    obtain ⟨material, member, rfl⟩ := supported
    have length : state.owners.length = state.pool.2.keys.length := owned.2.symm
    have below : state.pool.2.keys.length < pairs.length := fits rfl
    obtain ⟨keys, atLength⟩ : ∃ keys, pairs[state.owners.length]? = some keys :=
      ⟨pairs[state.owners.length]'(by omega), List.getElem?_eq_getElem _⟩
    have chosen : material.keys = keys := by
      simp only [PqxdhDeploymentIdealPoolSource.materialPool, atLength, support_bind, support_pure, Set.mem_iUnion,
        Set.mem_singleton_iff, exists_prop] at member
      obtain ⟨_, -, _, -, _, rfl, rfl⟩ := member
      rfl
    refine ⟨?_, ?_, ?_⟩
    · change state.pool.2.keys ++ [material.keys] = pairs.take (state.pool.2.keys ++ [material.keys]).length
      rw [List.length_append, List.length_singleton, List.take_add_one, ← prefixed, ← length, atLength, chosen]
      rfl
    · change (state.owners ++ [PqxdhRegistrationJointSchedule.birth pin keyId state.pool material]).map
        PqxdhRegistrationJointOwnership.Entry.kemIndex = List.range (state.owners ++ _).length
      rw [List.map_append, indexed, List.length_append, List.length_singleton, List.range_succ]
      simp [PqxdhRegistrationJointSchedule.birth, length]
    · have costly : Costly (KemSK := KemSK) (.inl (.inr (.create pin keyId))) := rfl
      change (state.pool.2.keys ++ [material.keys]).length = _
      simp [costly]
  · have notCreate : ∀ pin keyId, query ≠ .inl (.inr (.create pin keyId)) := fun pin keyId same =>
      creation ⟨pin, keyId, same⟩
    have same : sourcePool setup codec checks seed identityIndex pairs query =
        PqxdhRegistrationJointServerSchedule.source setup codec checks seed identityIndex query := by
      rcases query with (coin | request) | read
      · rfl
      · cases request with
        | create pin keyId => exact absurd rfl (notCreate pin keyId)
        | _ => rfl
      · rfl
    rw [same] at supported
    have counts := PqxdhDeploymentIdealPoolSource.source_counts setup codec checks seed identityIndex query notCreate state
      result supported
    have indices := source_indices setup codec checks seed identityIndex query notCreate state result supported
    refine ⟨?_, ?_, ?_⟩
    · unfold PoolPrefix
      rw [counts.1]
      exact prefixed
    · unfold PqxdhDeploymentIdealCut.PoolIndexed
      rw [indices, counts.2]
      exact indexed
    · rw [counts.1]
      simp [not_costly query notCreate]

end Pool

/-! ### Every middle step keeps the invariant -/

section Keep
open PqxdhRegistrationJointOwnership (Entry Owned activeKey)
open PqxdhDeploymentIdealSteps (groupedOwnerCE ownerImplCE)
open PqxdhRegistrationJointKemEntryFactor (Output factoredHidden)

/-- The native grouped owner returns the owner with its identity, and at most with its own live KEM key pair. -/
theorem groupedOwnerCE_fields (raw : Pqxdh.Bytes) (owner : PqxdhRegistrationSchedule.Owner KemSK)
    (result : Option Pqxdh.Bytes × PqxdhRegistrationSchedule.Owner KemSK)
    (member : result ∈ support (groupedOwnerCE (Response := Response) raw owner)) :
    result.2.beacon.identity = owner.beacon.identity ∧ ∀ keys, activeKey result.2 = some keys → activeKey owner = some keys := by
  unfold groupedOwnerCE at member
  rcases phase : owner.beacon.phase with _ | _ | ⟨control, prekey, oneTime, kem⟩ | _ | _
  all_goals simp only [phase, support_pure, Set.mem_singleton_iff] at member
  all_goals try (subst member; exact ⟨rfl, fun _ live => live⟩)
  simp only [support_bind, Set.mem_iUnion, exists_prop] at member
  obtain ⟨prepared, -, member⟩ := member
  rcases prepared with _ | prepared
  · simp only [support_pure, Set.mem_singleton_iff] at member
    subst member
    exact ⟨(PqxdhRegistrationJointOwnership.finish_fields control owner none).1, fun keys live => by
      rw [(PqxdhRegistrationJointOwnership.finish_fields control owner none).2] at live
      cases live⟩
  · simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff, exists_prop] at member
    obtain ⟨staged, -, rfl⟩ := member
    exact ⟨(PqxdhRegistrationJointOwnership.finish_fields control owner staged).1, fun keys live => by
      rw [(PqxdhRegistrationJointOwnership.finish_fields control owner staged).2] at live
      cases live⟩

/-- Owner k's challenge finish on the CE side returns the owner with its identity, and at most with its own live KEM key pair. -/
theorem challenge_fields (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (challenge : PqxdhKemIndCca.MlKem768Ciphertext) (raw : Pqxdh.Bytes) (owner : PqxdhRegistrationSchedule.Owner KemSK)
    (state : PqxdhServerAuthNative.NativeState KemSK × Option PqxdhDeploymentIdealSlots.Coord)
    (slots : PqxdhDeploymentIdealPostSim.SlotState)
    (result : ((Option Pqxdh.Bytes × PqxdhRegistrationSchedule.Owner KemSK) ×
      (PqxdhServerAuthNative.NativeState KemSK × Option PqxdhDeploymentIdealSlots.Coord)) ×
        PqxdhDeploymentIdealPostSim.SlotState)
    (member : result ∈ support ((simulateQ (PqxdhRegistrationJointKemSecondEntry.slotImpl
      PqxdhDeploymentSeedSplit.tableService) ((simulateQ (ownerImplCE setup codec (factoredHidden setup codec checks)
        challenge) (groupedOwnerCE raw owner)).run state)).run slots)) :
    result.1.1.2.beacon.identity = owner.beacon.identity ∧
      ∀ keys, activeKey result.1.1.2 = some keys → activeKey owner = some keys := by
  have outer : result.1 ∈ support ((simulateQ (ownerImplCE setup codec (factoredHidden setup codec checks) challenge)
      (groupedOwnerCE raw owner)).run state) := by
    apply OracleComp.support_simulateQ_run'_subset
      (PqxdhRegistrationJointKemSecondEntry.slotImpl PqxdhDeploymentSeedSplit.tableService) _ slots
    rw [StateT.run'_eq, support_map]
    exact ⟨result, member, rfl⟩
  have inner : result.1.1 ∈ support (groupedOwnerCE (Response := Response) raw owner) := by
    apply OracleComp.support_simulateQ_run'_subset (ownerImplCE setup codec (factoredHidden setup codec checks) challenge)
      _ state
    rw [StateT.run'_eq, support_map]
    exact ⟨result.1, outer, rfl⟩
  exact groupedOwnerCE_fields raw owner result.1.1 inner

end Keep

section KeepSteps
open PqxdhRegistrationJointOwnership (Entry Owned activeKey)
open PqxdhRegistrationJointKemEntryFactor (Output factoredHidden)
variable (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
  (checks : Checks) {count : ℕ} (t : Target count) (p : Params KemSK count)
  (created : PqxdhLiveServerConstruction.Created Unit)

/-- Advancing the accept counter on a raw accept changes no other part of the backend, and only increases the counter. -/
theorem bump_facts (query : (PqxdhRegistrationJointRevealSchedule.Spec KemSK).Domain)
    (backend : PqxdhDeploymentIdealSteps.IdealBk PqxdhDeploymentIdealSteps.TableState) :
    (PqxdhDeploymentIdealPostSource.bumpSource query backend).1 = backend.1 ∧
      (PqxdhDeploymentIdealPostSource.bumpSource query backend).2.1 = backend.2.1 ∧
      (PqxdhDeploymentIdealPostSource.bumpSource query backend).2.2.active = backend.2.2.active ∧
      (PqxdhDeploymentIdealPostSource.bumpSource query backend).2.2.marks = backend.2.2.marks ∧
      backend.2.2.accepts ≤ (PqxdhDeploymentIdealPostSource.bumpSource query backend).2.2.accepts := by
  unfold PqxdhDeploymentIdealPostSource.bumpSource
  split <;> simp

/-- A real middle step keeps the invariant, with one unit of room used exactly by a creation. -/
theorem keep_real (query : (PqxdhRegistrationJointRevealSchedule.Spec KemSK).Domain) (m : Mid KemSK)
    (inv : ItemInv created t p m) (fits : Costly query → 0 < room t p m)
    (result : (PqxdhRegistrationJointRevealSchedule.Spec KemSK).Range query × Mid KemSK)
    (member : result ∈ support ((realMid setup codec checks t p created query).run m)) :
    ItemInv created t p result.2 ∧ room t p m ≤ room t p result.2 + (if Costly query then 1 else 0) := by
  change result ∈ support ((fun r : (PqxdhRegistrationJointRevealSchedule.Spec KemSK).Range query ×
      PqxdhRegistrationJointSchedule.State KemSK =>
        (r.1, ({ m with joint := r.2, backend := PqxdhDeploymentIdealPostSource.bumpSource query m.backend } : Mid KemSK))) <$>
      (PqxdhDeploymentIdealPoolSource.sourcePool setup codec checks created.seed
        created.server.server.metadata.identityIndex (p.pool t) query).run m.joint) at member
  rw [support_map] at member
  obtain ⟨reached, inner, rfl⟩ := member
  have pool := sourcePool_keep setup codec checks created.seed created.server.server.metadata.identityIndex (p.pool t) query
    m.joint inv.owned inv.prefixed inv.indexed (fun costly => by have := fits costly; unfold room at this; omega) reached
    inner
  obtain ⟨tables, slots, active, marks, accepts⟩ := bump_facts query m.backend
  refine ⟨⟨pool.1, pool.2.1, pool.2.2.1, active.trans inv.active, lt_of_lt_of_le inv.done accepts, ?_, ?_⟩, ?_⟩
  · simp only [tables, slots]
    exact inv.good
  · intro mark found
    simp only [tables, slots]
    exact inv.stored mark (marks ▸ found)
  · unfold room
    simp only
    rw [pool.2.2.2]
    split <;> omega

/-- The marked build keeps the invariant and the room. -/
theorem keep_buildHidden (session : ℕ) (payload : Option Pqxdh.Bytes) (m : Mid KemSK) (inv : ItemInv created t p m)
    (hidden : PqxdhDeploymentIdealPostSource.buildHiddenAt m session = true)
    (result : Option PqxdhServerRegistrationPublication.Response × Mid KemSK)
    (member : result ∈ support ((sourceMid setup codec route checks t p created (.inl (.inr (.build session payload)))).run
      m)) :
    ItemInv created t p result.2 ∧ room t p m ≤ room t p result.2 := by
  rcases marked : m.backend.2.2.marks with _ | ⟨index, coords⟩
  · simp [PqxdhDeploymentIdealPostSource.buildHiddenAt, marked] at hidden
  have facts : index = session ∧ (m.joint.shared.2.pending session).isSome = true := by
    simpa [PqxdhDeploymentIdealPostSource.buildHiddenAt, marked] using hidden
  obtain ⟨rfl, pending⟩ := facts
  obtain ⟨value, held⟩ := Option.isSome_iff_exists.mp (inv.stored (index, coords) marked)
  rcases allocated : m.backend.2.1.1 coords with _ | slot
  · simp [PqxdhRegistrationJointKemSecondEntry.cacheOf, allocated] at held
  have stored : m.backend.1.1 slot = some value := by
    simpa [PqxdhRegistrationJointKemSecondEntry.cacheOf, allocated] using held
  rw [PqxdhDeploymentIdealPostHidden.sourceMid_build_hidden setup codec route checks t p created index payload m coords
    marked pending slot allocated value stored, support_map] at member
  obtain ⟨reached, -, rfl⟩ := member
  exact ⟨⟨inv.owned, inv.prefixed, inv.indexed, inv.active, inv.done, inv.good, inv.stored⟩, le_rfl⟩

/-- Owner k's challenge finish keeps the invariant and the room. -/
theorem keep_challenge (address : ℕ) (raw : Pqxdh.Bytes) (m : Mid KemSK) (inv : ItemInv created t p m)
    (hidden : PqxdhDeploymentIdealPostSource.finishHiddenAt t m address = true)
    (result : Option Pqxdh.Bytes × Mid KemSK)
    (member : result ∈ support ((sourceMid setup codec route checks t p created (.inl (.inr (.finish address raw)))).run
      m)) :
    ItemInv created t p result.2 ∧ room t p m ≤ room t p result.2 := by
  have condition : m.backend.2.2.active = true ∧ address = t.kem.val ∧
      PqxdhDeploymentIdealSteps.initSentAt (PqxdhRegistrationJointSchedule.source m.joint).owners address = true := by
    simpa [PqxdhDeploymentIdealPostSource.finishHiddenAt] using hidden
  rcases found : m.joint.owners[address]? with _ | entry
  · have absent : (PqxdhRegistrationJointSchedule.source m.joint).owners[address]? = none := by
      simp [PqxdhRegistrationJointSchedule.source, List.getElem?_map, found]
    have := condition.2.2
    simp [PqxdhDeploymentIdealSteps.initSentAt, absent] at this
  rw [PqxdhDeploymentIdealPostChallenge.sourceMid_challenge setup codec route checks t p created address raw m hidden entry
    found, support_map] at member
  obtain ⟨reached, inner, rfl⟩ := member
  have fields := challenge_fields setup codec checks p.challenge raw entry.owner _ _ reached inner
  obtain ⟨good, keep⟩ := PqxdhDeploymentIdealPostChallenge.slot_keepProgram _ _ inv.good reached inner
  have entryOwned := inv.owned.1.1 entry (List.mem_of_getElem? found)
  have replacement : Owned m.joint.pool { entry with owner := reached.1.1.2 } :=
    ⟨by rw [show ({ entry with owner := reached.1.1.2 } : Entry KemSK).owner.beacon.identity = entry.owner.beacon.identity
        from fields.1]; exact entryOwned.1, fun keys live => entryOwned.2 keys (fields.2 keys live)⟩
  refine ⟨⟨⟨⟨PqxdhRegistrationJointSchedule.updated_owned m.joint m.joint.pool reached.1.2.1 address
      { entry with owner := reached.1.1.2 } inv.owned.1.1 rfl rfl replacement, inv.owned.1.2⟩, ?_⟩,
    inv.prefixed, ?_, inv.active, inv.done, good, ?_⟩, le_rfl⟩
  · change m.joint.pool.2.keys.length = (m.joint.owners.set address _).length
    rw [List.length_set]
    exact inv.owned.2
  · change (m.joint.owners.set address _).map Entry.kemIndex = List.range (m.joint.owners.set address _).length
    rw [indices_set m.joint.owners address entry found, List.length_set]
    exact inv.indexed
  · intro mark marked
    obtain ⟨value, held⟩ := Option.isSome_iff_exists.mp (inv.stored mark marked)
    exact Option.isSome_iff_exists.mpr ⟨value, keep _ _ held⟩

/-- Every simulated middle step at a middle state with the invariant and room for a creation keeps the invariant, with one unit of room used exactly by a creation (`sim_option`'s preservation obligation). -/
theorem keep_all (query : (PqxdhRegistrationJointRevealSchedule.Spec KemSK).Domain) (m : Mid KemSK)
    (inv : ItemInv created t p m) (fits : Costly query → 0 < room t p m)
    (result : (PqxdhRegistrationJointRevealSchedule.Spec KemSK).Range query × Mid KemSK)
    (member : result ∈ support ((sourceMid setup codec route checks t p created query).run m)) :
    ItemInv created t p result.2 ∧ room t p m ≤ room t p result.2 + (if Costly query then 1 else 0) := by
  have real : ∀ (other : (sourceMid setup codec route checks t p created query).run m =
      (realMid setup codec checks t p created query).run m), ItemInv created t p result.2 ∧
        room t p m ≤ room t p result.2 + (if Costly query then 1 else 0) := fun other =>
    keep_real setup codec checks t p created query m inv fits result (other ▸ member)
  rcases query with (coin | request) | read
  · exact real rfl
  · cases request with
    | accept raw =>
        refine real ?_
        change (if m.backend.2.2.accepts = t.accept then _ else _) = _
        rw [ite_eq_right_of_eq_false _ _ (eq_false (Nat.ne_of_gt inv.done))]
    | build session payload =>
        cases hidden : PqxdhDeploymentIdealPostSource.buildHiddenAt m session
        · refine real ?_
          change (if PqxdhDeploymentIdealPostSource.buildHiddenAt m session then _ else _) = _
          rw [hidden]
          rfl
        · have kept := keep_buildHidden setup codec route checks t p created session payload m inv hidden result member
          have free : ¬ Costly (KemSK := KemSK) (.inl (.inr (.build session payload))) := by
            simp [Costly, sourceKind, PqxdhRegistrationSchedule.sourceKind]
          simp only [free, ↓reduceIte, Nat.add_zero]
          exact kept
    | finish address raw =>
        cases hidden : PqxdhDeploymentIdealPostSource.finishHiddenAt t m address
        · refine real ?_
          change (if PqxdhDeploymentIdealPostSource.finishHiddenAt t m address then _ else _) = _
          rw [hidden]
          rfl
        · have kept := keep_challenge setup codec route checks t p created address raw m inv hidden result member
          have free : ¬ Costly (KemSK := KemSK) (.inl (.inr (.finish address raw))) := by
            simp [Costly, sourceKind, PqxdhRegistrationSchedule.sourceKind]
          simp only [free, ↓reduceIte, Nat.add_zero]
          exact kept
    | _ => exact real rfl
  · exact real rfl

/-- Item 2's two layers on a source program with only simulated requests and at most the room's number of creations, from item 2's view without table counters of a middle state with the invariant, run without stopping as the projection of the program's middle run (`PqxdhDeploymentIdealPostSim.sim_option` with `step_all` and `keep_all`). It needs the constructed Server's public identity to be its seed's. -/
theorem item_sim (identity : created.publicIdentity = setup.joint.publicKeys created.seed) {α : Type}
    (work : OracleComp (PqxdhRegistrationJointRevealSchedule.Spec KemSK) α)
    (onlyAllowed : work.IsQueryBoundP (fun query => ¬ Allowed (KemSK := KemSK) query) 0) (budget : ℕ)
    (bounded : work.IsQueryBoundP (Costly (KemSK := KemSK)) budget) (m : Mid KemSK) (fits : budget ≤ room t p m)
    (holds : ItemInv created t p m) :
    ((simulateQ (lowerEC setup t p) ((simulateQ (PqxdhDeploymentIdealPostSteps.upperE setup codec checks t p created)
        work).run (encodeMidC setup m).1)).run).run (encodeMidC setup m).2 =
      (fun result => (some (result.1, (encodeMidC setup result.2).1), (encodeMidC setup result.2).2)) <$>
        (simulateQ (sourceMid setup codec route checks t p created) work).run m :=
  PqxdhDeploymentIdealPostSim.sim_option (PqxdhDeploymentIdealPostSteps.upperE setup codec checks t p created)
    (lowerEC setup t p) (sourceMid setup codec route checks t p created) (encodeMidC setup) (ItemInv created t p) Allowed
    Costly (room t p)
    (fun query state holds allowed fits => step_all setup codec route checks t p created identity query state holds allowed
      fits)
    (fun query state holds _ fits => keep_all setup codec route checks t p created query state holds fits)
    work onlyAllowed budget bounded m fits holds

end KeepSteps

end BeaconcryptCore.Computational.PqxdhDeploymentIdealPostInvariant

-- Axiom guards (generated)

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPostInvariant.step_all' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPostInvariant.step_all

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPostInvariant.indices_set' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPostInvariant.indices_set

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPostInvariant.source_indices' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPostInvariant.source_indices

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPostInvariant.not_costly' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPostInvariant.not_costly

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPostInvariant.sourcePool_keep' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPostInvariant.sourcePool_keep

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPostInvariant.groupedOwnerCE_fields' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPostInvariant.groupedOwnerCE_fields

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPostInvariant.challenge_fields' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPostInvariant.challenge_fields

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPostInvariant.bump_facts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPostInvariant.bump_facts

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPostInvariant.keep_real' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPostInvariant.keep_real

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPostInvariant.keep_buildHidden' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPostInvariant.keep_buildHidden

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPostInvariant.keep_challenge' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPostInvariant.keep_challenge

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPostInvariant.keep_all' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPostInvariant.keep_all

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPostInvariant.item_sim' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPostInvariant.item_sim
