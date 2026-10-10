-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhDeploymentIdealAnomalyBound
import BeaconcryptCore.Computational.PqxdhPhase2KemHandles

/-!
# Owner k's KEM secret key replaced in the final split game (CE-11b, unit U4)

Program equalities for the anomaly guesser of `PqxdhDeploymentIdealAnomalyGuesser` (plan section 84). The guesser runs the final split game of a target from the selected public key alone; in its state, owner `k`'s KEM key pair holds the selected public key with another secret key. This module shows that, before the selected raw accept, every step of the final split game other than owner `k`'s finish is unchanged by that replacement, up to the replacement of its final state, and keeps owner `k`'s key; the finish, which decapsulates, is handled by the guesser's decapsulation oracle in the guesser module.

- The replacement (`withSecret`, `swapOwner`, `swapSched`, `swapNative`, `swapX`): the secret half of owner `index`'s KEM key pair, the only KEM secret an owner state holds (in the `fresh`, `freshWithCoins` and `initSent` phases), replaced through `PqxdhBeaconPhase1Publication.mapState`; `Holds` says that owner `index` holds a given secret key; `Swaps swap inv first second` relates two stateful steps by a replacement under an invariant.
- Per command (`onShared_swaps`, `createPool_swaps`, `bundle_swaps`, `finish_other_swaps`, `serverStep_swaps`, `beaconStep_swaps`, `realRegAt_swaps`, `realAccept_swaps`, `createReg_swaps`, `nativeHandler_swaps`): steps on the shared native state are frames of the owners; the bundle is natural in the KEM key pair through the public projection (`PqxdhLivePhase1Bundle.bundle_map`); the Beacon record interpreter is natural in it (`beaconImpl_map`: inactive phases reject without reading it, the established phase holds none); the LQ finish snapshot reads only scalars (`snapshotAt_swap`); the pool create installs the replaced key pair at owner `index` from the pool with that entry replaced (`pool_withChosen`).
- `split_swaps`: before the selected raw accept (the selected accept neither active nor marking), every query of the final split game other than a finish of owner `k` commutes with replacing owner `k`'s secret key in the state and in the challenger's parameters (`withChosen`), and keeps owner `k`'s secret key.
- Decapsulation counts (`collect_decapsulate`, `prepare_decapsulate`, `nativeOwner_decapsulate`): the native Beacon finish program decapsulates at most once.

These are program equalities and query counts; no security claim is made here.
-/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open PqxdhRefinement

set_option autoImplicit false

namespace BeaconcryptCore.Computational.PqxdhDeploymentIdealKeySwap
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhKemIndCca (MlKem768PublicKey MlKem768Ciphertext MlKemSharedSecret)
open PqxdhRegistrationSchedule (Owner)
open PqxdhDeploymentBackend (XState)

/-! ### Replacing owner k's KEM secret key -/

section Swap
variable {KemSK : Type}

/-- A KEM key pair with its secret half replaced. -/
def withSecret (secret : KemSK) (keys : MlKem768PublicKey × KemSK) : MlKem768PublicKey × KemSK :=
  (keys.1, secret)

/-- An owner with the secret half of its KEM key pair replaced; every other field, the public key included, is unchanged. -/
def swapOwner (secret : KemSK) (owner : Owner KemSK) : Owner KemSK :=
  PqxdhBeaconPhase1Publication.mapState id (withSecret secret) owner

/-- Replacing the secret key twice is replacing it once, by the second key. -/
theorem swapOwner_swapOwner (first second : KemSK) (owner : Owner KemSK) :
    swapOwner first (swapOwner second owner) = swapOwner first owner := by
  rcases owner with ⟨⟨identity, keyId, pin, phase⟩, attempts⟩
  cases phase <;> rfl

/-- The registration state with the KEM secret key of owner `index` replaced. -/
def swapSched (index : ℕ) (secret : KemSK) (state : PqxdhRegistrationSchedule.State KemSK) :
    PqxdhRegistrationSchedule.State KemSK :=
  { state with owners := state.owners.modify index (swapOwner secret) }

/-- The native deployment state with the KEM secret key of owner `index` replaced. -/
def swapNative (index : ℕ) (secret : KemSK) (state : PqxdhDeploymentNative.State KemSK) :
    PqxdhDeploymentNative.State KemSK :=
  { state with native := swapSched index secret state.native }

/-- The extended state with the KEM secret key of owner `index` replaced. -/
def swapX {Bk : Type} {n : ℕ} (index : ℕ) (secret : KemSK) (x : XState KemSK Bk n) : XState KemSK Bk n :=
  { x with base := swapNative index secret x.base }

/-- Owner `index`, if present, holds the secret key `secret` in its KEM key pair (when its phase holds one). -/
def Holds (index : ℕ) (secret : KemSK) (owners : List (Owner KemSK)) : Prop :=
  ∀ owner, owners[index]? = some owner → swapOwner secret owner = owner

/-- Two stateful steps related by a state replacement under an invariant: from a state satisfying the invariant, the second step at the replaced state is the first step with its final state replaced, and the first step keeps the invariant. -/
def Swaps {σ α : Type} (swap : σ → σ) (inv : σ → Prop) (first second : StateT σ ProbComp α) : Prop :=
  ∀ s, inv s → second.run (swap s) = Prod.map id swap <$> first.run s ∧ ∀ r ∈ support (first.run s), inv r.2

/-- Modifying one entry of a list and setting another commute. -/
theorem modify_set_comm {α : Type} (l : List α) (index other : ℕ) (f : α → α) (a : α) (ne : other ≠ index) :
    (l.modify index f).set other a = (l.set other a).modify index f := by
  apply List.ext_getElem?
  intro j
  simp only [List.getElem?_set, List.getElem?_modify, List.length_modify]
  by_cases hj : other = j
  · subst hj
    simp [ne.symm]
  · by_cases hi : index = j
    · subst hi
      simp [hj]
    · simp [hj, hi]

/-- Modifying an entry other than the appended one commutes with appending. -/
theorem modify_append_ne {α : Type} (l : List α) (index : ℕ) (f : α → α) (a : α) (ne : index ≠ l.length) :
    l.modify index f ++ [a] = (l ++ [a]).modify index f := by
  apply List.ext_getElem?
  intro j
  simp only [List.getElem?_append, List.getElem?_modify, List.length_modify]
  by_cases hj : j < l.length
  · simp [hj]
  · simp only [hj, ↓reduceIte, List.getElem?_singleton]
    by_cases hi : index = j
    · subst hi
      have : index - l.length ≠ 0 := by omega
      simp [this]
    · simp [hi]

/-- Modifying the appended entry modifies the appended value. -/
theorem modify_append_eq {α : Type} (l : List α) (f : α → α) (a : α) :
    (l ++ [a]).modify l.length f = l ++ [f a] := by
  apply List.ext_getElem?
  intro j
  simp only [List.getElem?_modify, List.getElem?_append]
  by_cases hj : j < l.length
  · simp [hj, Nat.ne_of_gt hj]
  · by_cases hi : l.length = j
    · subst hi
      simp
    · have : j - l.length ≠ 0 := by omega
      simp [hj, hi, this]

/-- Modifying beyond the end of a list changes nothing. -/
theorem modify_beyond {α : Type} (l : List α) (index : ℕ) (f : α → α) (beyond : l.length ≤ index) :
    l.modify index f = l := by
  apply List.ext_getElem?
  intro j
  simp only [List.getElem?_modify]
  by_cases hi : index = j
  · subst hi
    simp [List.getElem?_eq_none beyond]
  · simp [hi]

/-- Setting an entry to a modified value after modifying it is modifying after setting. -/
theorem modify_set_same {α : Type} (l : List α) (index : ℕ) (f : α → α) (a : α) :
    (l.modify index f).set index (f a) = (l.set index a).modify index f := by
  apply List.ext_getElem?
  intro j
  simp only [List.getElem?_set, List.getElem?_modify, List.length_modify]
  by_cases hj : index = j
  · subst hj
    by_cases bound : index < l.length <;> simp [bound]
  · simp [hj]

end Swap

/-! ### Registration steps under the replacement -/

section Sched
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}
  (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)

/-- A step on the shared native state alone commutes with every replacement and keeps the owners. -/
theorem onShared_swaps {α : Type} (index : ℕ) (old new : KemSK) (work : PqxdhServerAuthNative.NativeGame KemSK α) :
    Swaps (swapSched index new) (fun s => Holds index old s.owners) (PqxdhRegistrationSchedule.onShared work)
      (PqxdhRegistrationSchedule.onShared work) := by
  intro s held
  refine ⟨?_, ?_⟩
  · rw [PqxdhRegistrationSchedule.onShared_run, PqxdhRegistrationSchedule.onShared_run, Functor.map_map]
    rfl
  · intro r member
    rw [PqxdhRegistrationSchedule.onShared_run, support_map] at member
    obtain ⟨r', _, rfl⟩ := member
    exact held

/-- A step on the shared native state alone keeps the owners. -/
theorem onShared_owners {α : Type} (work : PqxdhServerAuthNative.NativeGame KemSK α)
    (state : PqxdhRegistrationSchedule.State KemSK) :
    ∀ r ∈ support ((PqxdhRegistrationSchedule.onShared work).run state), r.2.owners = state.owners := by
  intro r member
  rw [PqxdhRegistrationSchedule.onShared_run, support_map] at member
  obtain ⟨r', _, rfl⟩ := member
  rfl

/-- The pool create at a pool whose entry `index` holds the secret key `old`, against the pool with that secret key replaced: the new owner at `index` gets the replaced key pair, every other new owner the same one. -/
theorem createPool_swaps (index : ℕ) (old new : KemSK) (pool : List (PqxdhLiveKemReservation.Pair KemSK))
    (pin : PqxdhBeaconPhase2Preparation.Word32) (keyId : Std.U64) (inPool : index < pool.length)
    (holds : ∀ keys, pool[index]? = some keys → withSecret old keys = keys) :
    Swaps (swapSched index new) (fun s => Holds index old s.owners)
      (PqxdhDeploymentIdealSteps.createPool setup pool pin keyId)
      (PqxdhDeploymentIdealSteps.createPool setup (pool.modify index (withSecret new)) pin keyId) := by
  intro s held
  simp only [PqxdhDeploymentIdealSteps.createPool, StateT.run_bind, StateT.run_lift, StateT.run_get, StateT.run_set,
    StateT.run_pure, bind_assoc, pure_bind]
  have length : (swapSched index new s).owners.length = s.owners.length := List.length_modify _ _ _
  refine ⟨?_, ?_⟩
  · simp only [map_bind, map_pure, Prod.map, id_eq, length]
    refine bind_congr fun identity => bind_congr fun prekey => ?_
    by_cases here : s.owners.length = index
    · obtain ⟨keys, found⟩ : ∃ keys, pool[index]? = some keys := ⟨pool[index], List.getElem?_eq_getElem inPool⟩
      have found' : (pool.modify index (withSecret new))[index]? = some (withSecret new keys) := by
        rw [List.getElem?_modify, found]; simp
      rw [here, found, found']
      simp only [pure_bind, swapSched]
      congr 3
      rw [modify_beyond _ _ _ (by omega), ← here, modify_append_eq]
      rfl
    · have same : (pool.modify index (withSecret new))[s.owners.length]? = pool[s.owners.length]? := by
        rw [List.getElem?_modify]; simp [Ne.symm here]
      rw [same]
      refine bind_congr fun keys => ?_
      simp only [swapSched]
      congr 3
      exact modify_append_ne _ _ _ _ (Ne.symm here)
  · intro r member
    simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at member
    obtain ⟨identity, -, prekey, -, keys, keysMember, rfl⟩ := member
    intro owner found
    change (s.owners ++ _)[index]? = some owner at found
    rw [List.getElem?_append] at found
    split at found
    · exact held owner found
    · rename_i beyond
      have here : index = s.owners.length := by
        rw [List.getElem?_singleton] at found
        split at found <;> first | omega | cases found
      subst here
      simp only [Nat.sub_self, List.getElem?_singleton, ↓reduceIte, Option.some.injEq] at found
      subst found
      obtain ⟨kp, kpFound⟩ : ∃ kp, pool[s.owners.length]? = some kp := ⟨pool[s.owners.length], List.getElem?_eq_getElem inPool⟩
      rw [kpFound] at keysMember
      simp only [support_pure, Set.mem_singleton_iff] at keysMember
      subst keysMember
      have fixed := holds _ kpFound
      change PqxdhBeaconPhase1Publication.mapState id (withSecret old) _ = _
      simp only [PqxdhBeaconPhase1Publication.mapState, PqxdhBeaconPhase1Publication.mapPhase, fixed, id_eq]

/-- Lift through `onNative`. -/
theorem onNative_swaps {α : Type} (index : ℕ) (old new : KemSK) (first second : PqxdhRegistrationSchedule.Game KemSK α)
    (swaps : Swaps (swapSched index new) (fun s => Holds index old s.owners) first second) :
    Swaps (swapNative index new) (fun s => Holds index old s.native.owners)
      (PqxdhDeploymentNative.onNative first) (PqxdhDeploymentNative.onNative second) := by
  intro s held
  obtain ⟨same, keeps⟩ := swaps s.native held
  refine ⟨?_, ?_⟩
  · change (fun result => (result.1, { swapNative index new s with native := result.2 })) <$>
        second.run (swapSched index new s.native) =
      Prod.map id (swapNative index new) <$> ((fun result => (result.1, { s with native := result.2 })) <$>
        first.run s.native)
    rw [same, Functor.map_map, Functor.map_map]
    rfl
  · intro r member
    change r ∈ support ((fun result => (result.1, { s with native := result.2 })) <$> first.run s.native) at member
    rw [support_map] at member
    obtain ⟨r', member', rfl⟩ := member
    exact keeps r' member'

/-- A missing owner's bundle answers nothing and changes nothing. -/
theorem bundle_missing (owner : ℕ) (s : PqxdhRegistrationSchedule.State KemSK) (missing : s.owners[owner]? = none) :
    (PqxdhRegistrationSchedule.bundle setup codec owner).run s = pure (none, s) := by
  simp only [PqxdhRegistrationSchedule.bundle, StateT.run_bind, StateT.run_get, pure_bind, missing, StateT.run_pure]

/-- The bundle of every owner commutes with replacing owner `index`'s KEM secret key (`PqxdhLivePhase1Bundle.bundle_map`; the public projection reads only the public key) and keeps owner `index`'s secret key. -/
theorem bundle_swaps (index : ℕ) (old new : KemSK) (owner : ℕ) :
    Swaps (swapSched index new) (fun s => Holds index old s.owners) (PqxdhRegistrationSchedule.bundle setup codec owner)
      (PqxdhRegistrationSchedule.bundle setup codec owner) := by
  intro s held
  rcases found : s.owners[owner]? with _ | o
  · have found' : (swapSched index new s).owners[owner]? = none := by
      simp [swapSched, List.getElem?_modify, found]
    refine ⟨by rw [bundle_missing setup codec owner _ found', bundle_missing setup codec owner _ found, map_pure]; rfl, ?_⟩
    intro r member
    rw [bundle_missing setup codec owner _ found] at member
    simp only [support_pure, Set.mem_singleton_iff] at member
    subst member
    exact held
  · have natural : ∀ secret : KemSK, simulateQ (PqxdhRegistrationSchedule.bundleCallbacks setup codec o.beacon.identity)
        (PqxdhLivePhase1Bundle.bundle (PqxdhRegistrationSchedule.projection setup owner) (swapOwner secret o)) =
        (fun r => (r.1, swapOwner secret r.2)) <$> simulateQ (PqxdhRegistrationSchedule.bundleCallbacks setup codec
          o.beacon.identity) (PqxdhLivePhase1Bundle.bundle (PqxdhRegistrationSchedule.projection setup owner) o) := by
      intro secret
      rw [← simulateQ_map]
      congr 1
      exact (PqxdhLivePhase1Bundle.bundle_map id (withSecret secret) _ _ (fun _ => rfl) (fun _ => rfl) rfl
        (fun _ => rfl) o).symm
    by_cases same : owner = index
    · subst same
      have found' : (swapSched owner new s).owners[owner]? = some (swapOwner new o) := by
        simp [swapSched, found]
      refine ⟨?_, ?_⟩
      · change PqxdhRegistrationSchedule.bundle setup codec owner (swapSched owner new s) =
          Prod.map id (swapSched owner new) <$> PqxdhRegistrationSchedule.bundle setup codec owner s
        rw [PqxdhRegistrationSchedule.bundle_source setup codec owner _ _ found',
          PqxdhRegistrationSchedule.bundle_source setup codec owner _ _ found]
        change _ <$> simulateQ (PqxdhRegistrationSchedule.bundleCallbacks setup codec o.beacon.identity) _ = _
        rw [natural, Functor.map_map, Functor.map_map]
        refine congrArg (fun f => f <$> _) (funext fun r => ?_)
        simp only [Prod.map, id_eq, swapSched]
        rw [modify_set_same]
      · intro r member
        change r ∈ support (PqxdhRegistrationSchedule.bundle setup codec owner s) at member
        rw [PqxdhRegistrationSchedule.bundle_source setup codec owner _ _ found, support_map] at member
        obtain ⟨r', member', rfl⟩ := member
        have fixed := natural old
        rw [held o found] at fixed
        rw [fixed, support_map] at member'
        obtain ⟨r'', -, rfl⟩ := member'
        intro o' found''
        have bound : owner < s.owners.length := (List.getElem?_eq_some_iff.mp found).1
        simp only [List.getElem?_set_self bound, Option.some.injEq] at found''
        subst found''
        exact swapOwner_swapOwner _ _ _
    · have found' : (swapSched index new s).owners[owner]? = some o := by
        simp [swapSched, found, Ne.symm same]
      refine ⟨?_, ?_⟩
      · change PqxdhRegistrationSchedule.bundle setup codec owner (swapSched index new s) =
          Prod.map id (swapSched index new) <$> PqxdhRegistrationSchedule.bundle setup codec owner s
        rw [PqxdhRegistrationSchedule.bundle_source setup codec owner _ _ found',
          PqxdhRegistrationSchedule.bundle_source setup codec owner _ _ found, Functor.map_map]
        refine congrArg (fun f => f <$> _) (funext fun r => ?_)
        simp only [Prod.map, id_eq, swapSched]
        rw [modify_set_comm _ _ _ _ _ same]
      · intro r member
        change r ∈ support (PqxdhRegistrationSchedule.bundle setup codec owner s) at member
        rw [PqxdhRegistrationSchedule.bundle_source setup codec owner _ _ found, support_map] at member
        obtain ⟨r', -, rfl⟩ := member
        intro o' found''
        change (s.owners.set owner r'.2)[index]? = some o' at found''
        rw [List.getElem?_set_ne same] at found''
        exact held o' found''

/-- The registration finish of an owner other than `index` commutes with replacing owner `index`'s KEM secret key and keeps it. -/
theorem finish_other_swaps (index : ℕ) (old new : KemSK) (owner : ℕ) (raw : Pqxdh.Bytes) (other : owner ≠ index) :
    Swaps (swapSched index new) (fun s => Holds index old s.owners) (PqxdhRegistrationSchedule.finish setup codec owner raw)
      (PqxdhRegistrationSchedule.finish setup codec owner raw) := by
  intro s held
  rcases found : s.owners[owner]? with _ | o
  · have found' : (swapSched index new s).owners[owner]? = none := by
      simp [swapSched, List.getElem?_modify, found]
    refine ⟨by rw [PqxdhRegistrationSchedule.finish_missing setup codec owner raw _ found',
      PqxdhRegistrationSchedule.finish_missing setup codec owner raw _ found, map_pure]; rfl, ?_⟩
    intro r member
    rw [PqxdhRegistrationSchedule.finish_missing setup codec owner raw _ found] at member
    simp only [support_pure, Set.mem_singleton_iff] at member
    subst member
    exact held
  · have found' : (swapSched index new s).owners[owner]? = some o := by
      simp [swapSched, found, Ne.symm other]
    refine ⟨?_, ?_⟩
    · change PqxdhRegistrationSchedule.finish setup codec owner raw (swapSched index new s) =
        Prod.map id (swapSched index new) <$> PqxdhRegistrationSchedule.finish setup codec owner raw s
      rw [PqxdhRegistrationSchedule.finish_source setup codec owner raw _ _ found',
        PqxdhRegistrationSchedule.finish_source setup codec owner raw _ _ found, Functor.map_map]
      refine congrArg (fun f => f <$> _) (funext fun r => ?_)
      simp only [Prod.map, id_eq, swapSched]
      rw [modify_set_comm _ _ _ _ _ other]
    · intro r member
      change r ∈ support (PqxdhRegistrationSchedule.finish setup codec owner raw s) at member
      rw [PqxdhRegistrationSchedule.finish_source setup codec owner raw _ _ found, support_map] at member
      obtain ⟨r', -, rfl⟩ := member
      intro o' found''
      change (s.owners.set owner r'.1.2)[index]? = some o' at found''
      rw [List.getElem?_set_ne other] at found''
      exact held o' found''

end Sched

/-! ### Native deployment steps under the replacement -/

section Native
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}
  (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
  (route : RawCtxServerRouting.SenderDecoder)

/-- A record program's result mapped before the record run is the record run's result mapped. -/
theorem record_map {α β : Type} (f : α → β) (work : OracleComp RawCtxMixedOwner.NativeSpec α)
    (state : PqxdhRegistrationSchedule.State KemSK) :
    (PqxdhDeploymentNative.record setup codec (f <$> work)).run state =
      Prod.map f id <$> (PqxdhDeploymentNative.record setup codec work).run state := by
  rw [PqxdhDeploymentNative.record_run, PqxdhDeploymentNative.record_run, simulateQ_map, StateT.run_map,
    Functor.map_map, Functor.map_map]
  rfl

/-- Logging the frames of a mapped record program maps its result. -/
theorem logged_map {α β : Type} (f : α → β) (work : OracleComp RawCtxMixedOwner.NativeSpec α) :
    PqxdhDeploymentNative.logged (f <$> work) = Prod.map f id <$> PqxdhDeploymentNative.logged work := by
  unfold PqxdhDeploymentNative.logged
  rw [simulateQ_map, StateT.run_map]
  rfl

/-- The native Beacon record interpreter is natural in the KEM key pair representation: inactive phases reject without reading it, and the established phase holds none. -/
theorem beaconImpl_map {I D K K' : Type} (g : K → K') (decode : RawCtxReceive.FrameDecoder)
    (query : RawCtxMixedOwner.SourceSpec.Domain) (state : RawCtxBeaconLifecycle.State I D K) :
    (RawCtxBeaconLifecycle.beaconImpl decode query).run (PqxdhBeaconPhase1Publication.mapState id g state) =
      Prod.map id (PqxdhBeaconPhase1Publication.mapState id g) <$>
        (RawCtxBeaconLifecycle.beaconImpl decode query).run state := by
  rcases state with ⟨⟨identity, keyId, pin, phase⟩, attempts⟩
  cases phase <;> rcases query with q | q <;>
    simp [RawCtxBeaconLifecycle.beaconImpl, PqxdhBeaconPhase1Publication.mapState,
      PqxdhBeaconPhase1Publication.mapPhase, RawCtxBeaconLifecycle.rejected, RawCtxBeaconLifecycle.reinstall,
      RawCtxBeaconLifecycle.selected, StateT.run]

/-- A Server record step reads and writes no owner: it commutes with every replacement and keeps the owners. -/
theorem serverStep_swaps (index : ℕ) (old new : KemSK) (query : RawCtxServerMixed.SourceSpec.Domain) :
    Swaps (swapNative index new) (fun s => Holds index old s.native.owners)
      (PqxdhDeploymentNative.serverStep setup codec route query) (PqxdhDeploymentNative.serverStep setup codec route query) := by
  intro s held
  have shape : ∀ t : PqxdhDeploymentNative.State KemSK, (PqxdhDeploymentNative.serverStep setup codec route query).run t =
      (fun result => (result.1.1.1, PqxdhDeploymentNative.produce (PqxdhDeploymentNative.serverTag query) result.1.2
        (PqxdhDeploymentNative.withServer { t with native := result.2 } result.1.1.2))) <$>
        (PqxdhDeploymentNative.record setup codec (PqxdhDeploymentNative.logged
          ((RawCtxServerMixed.serverImpl (PqxdhDeploymentNative.senderId t) route codec.frameRead query).run
            (PqxdhDeploymentNative.serverView t)))).run t.native := fun t => by
    change (do let result ← _; pure _) = _
    rw [map_eq_bind_pure_comp]
    rfl
  obtain ⟨recorded, keeps⟩ := onShared_swaps index old new (PqxdhServerAuthNative.nativeCtx (simulateQ
    (PqxdhDeploymentNative.primitives setup codec) (PqxdhDeploymentNative.logged
      ((RawCtxServerMixed.serverImpl (PqxdhDeploymentNative.senderId s) route codec.frameRead query).run
        (PqxdhDeploymentNative.serverView s))))) s.native held
  have sender : PqxdhDeploymentNative.senderId (swapNative index new s) = PqxdhDeploymentNative.senderId s := rfl
  have view : PqxdhDeploymentNative.serverView (swapNative index new s) = PqxdhDeploymentNative.serverView s := rfl
  refine ⟨?_, ?_⟩
  · rw [shape, shape, sender, view]
    change _ <$> (PqxdhRegistrationSchedule.onShared _).run (swapSched index new s.native) = _
    rw [recorded, Functor.map_map, Functor.map_map]
    rfl
  · intro r member
    rw [shape, support_map] at member
    obtain ⟨r', member', rfl⟩ := member
    exact keeps r' member'

/-- The Beacon record step of every owner commutes with replacing owner `index`'s KEM secret key and keeps it: other owners are a frame, and owner `index`'s record interpreter is natural in its key pair (`beaconImpl_map`). -/
theorem beaconStep_swaps (index : ℕ) (old new : KemSK) (owner : ℕ) (query : RawCtxMixedOwner.SourceSpec.Domain) :
    Swaps (swapNative index new) (fun s => Holds index old s.native.owners)
      (PqxdhDeploymentNative.beaconStep setup codec owner query)
      (PqxdhDeploymentNative.beaconStep setup codec owner query) := by
  intro s held
  have foundShape : ∀ (t : PqxdhDeploymentNative.State KemSK) (o : Owner KemSK), t.native.owners[owner]? = some o →
      (PqxdhDeploymentNative.beaconStep setup codec owner query).run t =
        (fun result => (result.1.1.1, PqxdhDeploymentNative.produce (PqxdhDeploymentNative.beaconTag owner) result.1.2
          { t with
            native := { result.2 with owners := result.2.owners.set owner { o with beacon := result.1.1.2.beacon } }
            ownerRaw := Function.update t.ownerRaw owner result.1.1.2.rawAttempts })) <$>
        (PqxdhDeploymentNative.record setup codec (PqxdhDeploymentNative.logged
          ((RawCtxBeaconLifecycle.beaconImpl codec.frameRead query).run ⟨o.beacon, t.ownerRaw owner⟩))).run t.native := by
    intro t o found
    change (match t.native.owners[owner]? with | none => _ | some o => _) = _
    rw [found, map_eq_bind_pure_comp]
    rfl
  have missingShape : ∀ t : PqxdhDeploymentNative.State KemSK, t.native.owners[owner]? = none →
      (PqxdhDeploymentNative.beaconStep setup codec owner query).run t = pure (PqxdhDeploymentNative.absent query, t) := by
    intro t missing
    change (match t.native.owners[owner]? with | none => _ | some o => _) = _
    rw [missing]
  have recorded := fun work : OracleComp RawCtxMixedOwner.NativeSpec
      ((RawCtxMixedOwner.SourceSpec.Range query × RawCtxBeaconLifecycle.State PqxdhJointIdentity.IdentitySeed
        PqxdhJointGapDh.ScalarBytes (MlKem768PublicKey × KemSK)) × List PqxdhDeploymentNative.Frame) =>
    onShared_swaps index old new (PqxdhServerAuthNative.nativeCtx (simulateQ (PqxdhDeploymentNative.primitives setup codec)
      work)) s.native held
  rcases found : s.native.owners[owner]? with _ | o
  · have found' : (swapNative index new s).native.owners[owner]? = none := by
      simp [swapNative, swapSched, List.getElem?_modify, found]
    refine ⟨by rw [missingShape _ found', missingShape _ found, map_pure]; rfl, ?_⟩
    intro r member
    rw [missingShape _ found] at member
    simp only [support_pure, Set.mem_singleton_iff] at member
    subst member
    exact held
  · have bound : owner < s.native.owners.length := (List.getElem?_eq_some_iff.mp found).1
    by_cases same : owner = index
    · subst same
      have found' : (swapNative owner new s).native.owners[owner]? = some (swapOwner new o) := by
        simp [swapNative, swapSched, found]
      have inner : ∀ secret : KemSK, (RawCtxBeaconLifecycle.beaconImpl codec.frameRead query).run
          ⟨(swapOwner secret o).beacon, s.ownerRaw owner⟩ =
          Prod.map id (PqxdhBeaconPhase1Publication.mapState id (withSecret secret)) <$>
            (RawCtxBeaconLifecycle.beaconImpl codec.frameRead query).run ⟨o.beacon, s.ownerRaw owner⟩ :=
        fun secret => beaconImpl_map (withSecret secret) codec.frameRead query ⟨o.beacon, s.ownerRaw owner⟩
      refine ⟨?_, ?_⟩
      · rw [foundShape _ _ found', foundShape _ _ found]
        change _ <$> (PqxdhDeploymentNative.record setup codec (PqxdhDeploymentNative.logged
          ((RawCtxBeaconLifecycle.beaconImpl codec.frameRead query).run ⟨(swapOwner new o).beacon, s.ownerRaw owner⟩))).run
            (swapSched owner new s.native) = _
        rw [inner, logged_map, record_map]
        change _ <$> (Prod.map (Prod.map _ id) id <$> (PqxdhRegistrationSchedule.onShared _).run
          (swapSched owner new s.native)) = _
        rw [(recorded _).1, Functor.map_map, Functor.map_map, Functor.map_map]
        refine congrArg (fun f => f <$> _) (funext fun r => ?_)
        simp only [Prod.map, id_eq, swapNative, swapSched, PqxdhDeploymentNative.produce]
        rw [← modify_set_same]
        rfl
      · intro r member
        rw [foundShape _ _ found, support_map] at member
        obtain ⟨r', member', rfl⟩ := member
        have fixed := inner old
        rw [held o found] at fixed
        rw [fixed, logged_map, record_map, support_map] at member'
        obtain ⟨r'', member'', rfl⟩ := member'
        have owners := onShared_owners _ s.native r'' member''
        intro o' found''
        change ((r''.2.owners).set owner _)[owner]? = some o' at found''
        rw [owners, List.getElem?_set_self bound, Option.some.injEq] at found''
        subst found''
        change swapOwner old ⟨(PqxdhBeaconPhase1Publication.mapState id (withSecret old) r''.1.1.2).beacon, o.rawAttempts⟩ = _
        rcases r'' with ⟨⟨⟨reply, ⟨⟨identity, keyId, pin, phase⟩, attempts⟩⟩, frames⟩, after⟩
        cases phase <;> rfl
    · have found' : (swapNative index new s).native.owners[owner]? = some o := by
        simp [swapNative, swapSched, found, Ne.symm same]
      refine ⟨?_, ?_⟩
      · rw [foundShape _ _ found', foundShape _ _ found]
        change _ <$> (PqxdhRegistrationSchedule.onShared _).run (swapSched index new s.native) = _
        rw [(recorded _).1, Functor.map_map, Functor.map_map]
        refine congrArg (fun f => f <$> _) (funext fun r => ?_)
        simp only [Prod.map, id_eq, swapNative, swapSched, PqxdhDeploymentNative.produce]
        rw [modify_set_comm _ _ _ _ _ same]
      · intro r member
        rw [foundShape _ _ found, support_map] at member
        obtain ⟨r', member', rfl⟩ := member
        have owners := onShared_owners _ s.native r' member'
        intro o' found''
        change ((r'.2.owners).set owner _)[index]? = some o' at found''
        rw [List.getElem?_set_ne same, owners] at found''
        exact held o' found''

end Native

/-! ### Extended-state steps under the replacement -/

section Extended
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}
  (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
  (route : RawCtxServerRouting.SenderDecoder) {Bk : Type} {n : ℕ}

/-- The invariant at an extended state: owner `index` holds the secret key `secret`. -/
abbrev HoldsX (index : ℕ) (secret : KemSK) (x : XState KemSK Bk n) : Prop :=
  Holds index secret x.base.native.owners

/-- Lift through the extended state's base lens. -/
theorem onBase_swaps {α : Type} (index : ℕ) (old new : KemSK)
    (first second : StateT (PqxdhDeploymentNative.State KemSK) ProbComp α)
    (swaps : Swaps (swapNative index new) (fun s => Holds index old s.native.owners) first second) :
    Swaps (swapX (Bk := Bk) (n := n) index new) (HoldsX index old) (PqxdhDeploymentBackend.onBase first)
      (PqxdhDeploymentBackend.onBase second) := by
  intro x held
  obtain ⟨same, keeps⟩ := swaps x.base held
  refine ⟨?_, ?_⟩
  · change (fun r => (r.1, PqxdhDeploymentBackend.baseLens.set (swapX index new x) r.2)) <$>
        second.run (swapNative index new x.base) =
      Prod.map id (swapX index new) <$> ((fun r => (r.1, PqxdhDeploymentBackend.baseLens.set x r.2)) <$>
        first.run x.base)
    rw [same, Functor.map_map, Functor.map_map]
    rfl
  · intro r member
    change r ∈ support ((fun r => (r.1, PqxdhDeploymentBackend.baseLens.set x r.2)) <$> first.run x.base) at member
    rw [support_map] at member
    obtain ⟨r', member', rfl⟩ := member
    exact keeps r' member'

/-- The prekey and one-time fields of an owner do not depend on its KEM key pair. -/
theorem value_swap (secret : KemSK) (owner : Owner KemSK) :
    PqxdhRegistrationJointLiveRead.value .prekey (swapOwner secret owner) =
        PqxdhRegistrationJointLiveRead.value .prekey owner ∧
      PqxdhRegistrationJointLiveRead.value .oneTime (swapOwner secret owner) =
        PqxdhRegistrationJointLiveRead.value .oneTime owner := by
  rcases owner with ⟨⟨identity, keyId, pin, phase⟩, attempts⟩
  cases phase <;> exact ⟨rfl, rfl⟩

/-- The LQ finish snapshot reads only the prekey and one-time scalars, so the replacement does not change it. -/
theorem snapshotAt_swap (index : ℕ) (secret : KemSK) (snap : PqxdhDeploymentLater.Snap) (owners : List (Owner KemSK))
    (target : Option ℕ) :
    PqxdhDeploymentLater.snapshotAt snap (owners.modify index (swapOwner secret)) target =
      PqxdhDeploymentLater.snapshotAt snap owners target := by
  rcases target with _ | j
  · rfl
  · simp only [PqxdhDeploymentLater.snapshotAt, PqxdhDeploymentLater.fieldOf, List.getElem?_modify]
    rcases owners[j]? with _ | o
    · rfl
    · by_cases same : index = j
      · simp only [same, ↓reduceIte, Option.map_eq_map, Option.map_some, Option.bind_some, (value_swap secret o).1,
          (value_swap secret o).2]
      · simp [same]

/-- The real registration on a command other than the raw accept commutes with the replacement whenever the native handler does. -/
theorem realRegAt_swaps (created : PqxdhLiveServerConstruction.Created Unit) (index : ℕ) (old new : KemSK)
    (query : PqxdhRecordLiftInterface.EnvQuery) (notAccept : ∀ raw, query.val ≠ .accept raw)
    (swaps : Swaps (swapNative index new) (fun s => Holds index old s.native.owners)
      (PqxdhDeploymentNative.handler setup codec checks route created.seed (.inr query.val))
      (PqxdhDeploymentNative.handler setup codec checks route created.seed (.inr query.val))) :
    Swaps (swapX (Bk := Bk) (n := n) index new) (HoldsX index old)
      (PqxdhDeploymentIdealSteps.realRegAt setup codec route checks created query)
      (PqxdhDeploymentIdealSteps.realRegAt setup codec route checks created query) := by
  intro x held
  obtain ⟨same, keeps⟩ := swaps x.base held
  refine ⟨?_, ?_⟩
  · rw [PqxdhDeploymentIdealEnvReal.realRegAt_quiet setup codec checks route created _ notAccept,
      PqxdhDeploymentIdealEnvReal.realRegAt_quiet setup codec checks route created _ notAccept]
    change _ <$> (PqxdhDeploymentNative.handler setup codec checks route created.seed (.inr query.val)).run
      (swapNative index new x.base) = _
    rw [same, Functor.map_map, Functor.map_map]
    refine congrArg (fun f => f <$> _) (funext fun r => ?_)
    have owners : (swapX (Bk := Bk) (n := n) index new x).base.native.owners =
        x.base.native.owners.modify index (swapOwner new) := rfl
    simp only [Prod.map, id_eq, owners, snapshotAt_swap]
    rfl
  · intro r member
    rw [PqxdhDeploymentIdealEnvReal.realRegAt_quiet setup codec checks route created _ notAccept, support_map] at member
    obtain ⟨r', member', rfl⟩ := member
    exact keeps r' member'

/-- The real raw accept reads and writes no owner. -/
theorem realAccept_swaps (created : PqxdhLiveServerConstruction.Created Unit) (index : ℕ) (old new : KemSK)
    (raw : Pqxdh.Bytes) :
    Swaps (swapX (Bk := Bk) (n := n) index new) (HoldsX index old)
      (PqxdhDeploymentIdealSteps.realRegAt setup codec route checks created ⟨.accept raw, trivial⟩)
      (PqxdhDeploymentIdealSteps.realRegAt setup codec route checks created ⟨.accept raw, trivial⟩) := by
  intro x held
  refine ⟨?_, ?_⟩
  · rw [PqxdhDeploymentIdealEnvReal.realRegAt_accept setup codec checks route created,
      PqxdhDeploymentIdealEnvReal.realRegAt_accept setup codec checks route created, Functor.map_map]
    rfl
  · intro r member
    rw [PqxdhDeploymentIdealEnvReal.realRegAt_accept setup codec checks route created, support_map] at member
    obtain ⟨r', _, rfl⟩ := member
    exact held

/-- The pool create at a pool whose entry `index` holds the secret key `old`, against the pool with it replaced, on the extended state. -/
theorem createReg_swaps (index : ℕ) (old new : KemSK) (pool : List (PqxdhLiveKemReservation.Pair KemSK))
    (pin : Pqxdh.Bytes) (keyId : Std.U64) (inPool : index < pool.length)
    (holds : ∀ keys, pool[index]? = some keys → withSecret old keys = keys) :
    Swaps (swapX (Bk := Bk) (n := n) index new) (HoldsX index old)
      (PqxdhDeploymentIdealSteps.createReg setup pool pin keyId)
      (PqxdhDeploymentIdealSteps.createReg setup (pool.modify index (withSecret new)) pin keyId) := by
  intro x held
  rw [PqxdhDeploymentIdealEnvReal.createReg_run, PqxdhDeploymentIdealEnvReal.createReg_run]
  rcases PqxdhDeploymentInterface.parsePin pin with _ | word
  · refine ⟨by rw [map_pure]; rfl, ?_⟩
    intro r member
    simp only [support_pure, Set.mem_singleton_iff] at member
    subst member
    exact held
  · obtain ⟨same, keeps⟩ := createPool_swaps setup index old new pool word keyId inPool holds x.base.native held
    refine ⟨?_, ?_⟩
    · change _ <$> (PqxdhDeploymentIdealSteps.createPool setup (pool.modify index (withSecret new)) word keyId).run
        (swapSched index new x.base.native) = _
      rw [same, Functor.map_map, Functor.map_map]
      rfl
    · intro r member
      rw [support_map] at member
      obtain ⟨r', member', rfl⟩ := member
      exact keeps r' member'

/-- Every native handler command other than the create, the raw accept and owner `index`'s finish commutes with replacing owner `index`'s KEM secret key and keeps it. -/
theorem nativeHandler_swaps (serverSeed : PqxdhJointIdentity.IdentitySeed) (index : ℕ) (old new : KemSK)
    (command : PqxdhDeploymentInterface.Command) (notCreate : ∀ pin keyId, command ≠ .create pin keyId)
    (notAccept : ∀ raw, command ≠ .accept raw) (notFinish : ∀ raw, command ≠ .finish index raw) :
    Swaps (swapNative index new) (fun s => Holds index old s.native.owners)
      (PqxdhDeploymentNative.handler setup codec checks route serverSeed (.inr command))
      (PqxdhDeploymentNative.handler setup codec checks route serverSeed (.inr command)) := by
  cases command with
  | create pin keyId => exact absurd rfl (notCreate pin keyId)
  | bundle owner => exact onNative_swaps index old new _ _ (bundle_swaps setup codec index old new owner)
  | accept raw => exact absurd rfl (notAccept raw)
  | build session payload => exact onNative_swaps index old new _ _ (onShared_swaps index old new _)
  | finish owner raw =>
      exact onNative_swaps index old new _ _
        (finish_other_swaps setup codec index old new owner raw fun same => notFinish raw (by rw [same]))
  | hmac key message => exact onNative_swaps index old new _ _ (onShared_swaps index old new _)
  | hash bytes => exact onNative_swaps index old new _ _ (onShared_swaps index old new _)
  | serverSend keyId plaintext => exact serverStep_swaps setup codec route index old new _
  | serverRaw raw => exact serverStep_swaps setup codec route index old new _
  | beaconSend owner plaintext => exact beaconStep_swaps setup codec index old new owner _
  | beaconRaw owner raw => exact beaconStep_swaps setup codec index old new owner _

end Extended

/-! ### The final split game before the selected raw accept under the replacement -/

section Split
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}
  (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
  (route : RawCtxServerRouting.SenderDecoder) {count : ℕ}
open PqxdhDeploymentIdealParams (Target Params)
open PqxdhDeploymentIdealSteps (SplitBk)
open PqxdhDeploymentBackend (handlerWith)

/-- The challenger's parameters with the selected secret key replaced. -/
def withChosen (p : Params KemSK count) (secret : KemSK) : Params KemSK count :=
  { p with chosen := withSecret secret p.chosen }

/-- The pool of the parameters with the selected secret key replaced is the pool with entry `t.kem` replaced. -/
theorem pool_withChosen (t : Target count) (p : Params KemSK count) (secret : KemSK) :
    (withChosen p secret).pool t = (p.pool t).modify t.kem.val (withSecret secret) := by
  apply List.ext_getElem?
  intro j
  rw [List.getElem?_modify]
  by_cases bound : j < count + 1
  · obtain ⟨i, rfl⟩ : ∃ i : Fin (count + 1), i.val = j := ⟨⟨j, bound⟩, rfl⟩
    rcases Fin.eq_self_or_eq_succAbove t.kem i with same | ⟨i', rfl⟩
    · subst same
      rw [PqxdhDeploymentIdealParams.pool_kem, PqxdhDeploymentIdealParams.pool_kem]
      simp [withChosen]
    · rw [PqxdhDeploymentIdealParams.pool_other, PqxdhDeploymentIdealParams.pool_other]
      have ne : t.kem.val ≠ (t.kem.succAbove i').val := fun same => Fin.succAbove_ne t.kem i' (Fin.ext same).symm
      simp [ne, withChosen]
  · have beyond : (p.pool t).length ≤ j := by rw [PqxdhDeploymentIdealParams.pool_length]; omega
    have beyond' : ((withChosen p secret).pool t).length ≤ j := by rw [PqxdhDeploymentIdealParams.pool_length]; omega
    rw [List.getElem?_eq_none beyond, List.getElem?_eq_none beyond']
    rfl

/-- Before the selected raw accept (the selected accept neither active nor marking, the query not the selected raw accept), every query of the final split game other than a finish of owner `k` commutes with replacing owner `k`'s KEM secret key in the state and in the parameters, and keeps owner `k`'s secret key. -/
theorem split_swaps (t : Target count) (p : Params KemSK count) (new : KemSK)
    (created : PqxdhLiveServerConstruction.Created Unit) (query : PqxdhDeploymentInterface.Spec.Domain)
    (x : XState KemSK SplitBk 2) (inactive : x.backend.2.2.active = false) (unmarked : x.backend.2.2.marks = none)
    (other : ¬ PqxdhDeploymentIdealAnomalyBound.SelectedAt t x query)
    (notOwner : ∀ raw, query ≠ .inr (.finish t.kem.val raw)) (held : HoldsX t.kem.val p.chosen.2 x) :
    (handlerWith setup codec route (PqxdhDeploymentIdealDefer.idealSplit setup codec route checks t (withChosen p new)
        created) query).run (swapX t.kem.val new x) =
      Prod.map id (swapX t.kem.val new) <$> (handlerWith setup codec route
        (PqxdhDeploymentIdealDefer.idealSplit setup codec route checks t p created) query).run x ∧
    ∀ r ∈ support ((handlerWith setup codec route (PqxdhDeploymentIdealDefer.idealSplit setup codec route checks t p
        created) query).run x), HoldsX t.kem.val p.chosen.2 r.2 := by
  have quietNative := fun (query : PqxdhRecordLiftInterface.EnvQuery) notCreate notAccept notFinish =>
    realRegAt_swaps setup codec checks route created t.kem.val p.chosen.2 new query notAccept
      (nativeHandler_swaps setup codec checks route created.seed t.kem.val p.chosen.2 new query.val notCreate notAccept
        notFinish) x held
  rcases query with coin | command
  · refine ⟨?_, ?_⟩
    · simp only [handlerWith, StateT.run_lift, map_bind, map_pure]
      rfl
    · intro r member
      simp only [handlerWith, StateT.run_lift, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at member
      obtain ⟨_, _, rfl⟩ := member
      exact held
  · cases command with
    | create pin keyId =>
        simp only [handlerWith]
        rw [PqxdhDeploymentIdealEnvStep.idealSplit_create, PqxdhDeploymentIdealEnvStep.idealSplit_create,
          pool_withChosen]
        exact createReg_swaps setup t.kem.val p.chosen.2 new (p.pool t) pin keyId
          (by rw [PqxdhDeploymentIdealParams.pool_length]; exact t.kem.isLt)
          (fun keys found => by
            rw [PqxdhDeploymentIdealParams.pool_kem, Option.some.injEq] at found
            subst found
            rfl) x held
    | bundle owner =>
        simp only [handlerWith]
        rw [PqxdhDeploymentIdealEnvStep.idealSplit_bundle, PqxdhDeploymentIdealEnvStep.idealSplit_bundle]
        exact quietNative ⟨.bundle owner, trivial⟩ (fun _ _ same => by cases same) (fun _ same => by cases same) (fun _ same => by cases same)
    | accept raw =>
        have notSelected : x.backend.2.2.accepts ≠ t.accept := other
        simp only [handlerWith]
        rw [PqxdhDeploymentIdealEnvStep.idealSplit_accept_other setup codec route checks t (withChosen p new) created raw
            (swapX t.kem.val new x) notSelected,
          PqxdhDeploymentIdealEnvStep.idealSplit_accept_other setup codec route checks t p created raw x notSelected]
        exact realAccept_swaps setup codec checks route created t.kem.val p.chosen.2 new raw
          { x with backend := PqxdhDeploymentIdealEnvStep.bump x.backend } held
    | build session payload =>
        have real : ∀ index coords, x.backend.2.2.marks = some (index, coords) →
            ¬ (index = session ∧ (x.base.native.shared.2.pending session).isSome) := fun _ _ marked => by
          rw [unmarked] at marked; cases marked
        simp only [handlerWith]
        rw [PqxdhDeploymentIdealEnvStep.idealSplit_build_real setup codec route checks t (withChosen p new) created session
            payload (swapX t.kem.val new x) real,
          PqxdhDeploymentIdealEnvStep.idealSplit_build_real setup codec route checks t p created session payload x real]
        exact quietNative ⟨.build session payload, trivial⟩ (fun _ _ same => by cases same) (fun _ same => by cases same) (fun _ same => by cases same)
    | finish owner raw =>
        have ne : owner ≠ t.kem.val := fun same => notOwner raw (by rw [same])
        have real : ¬ (x.backend.2.2.active = true ∧ owner = t.kem.val ∧
            PqxdhDeploymentIdealSteps.initSentAt x.base.native.owners owner = true) := fun chosen => by
          rw [inactive] at chosen; cases chosen.1
        have real' : ¬ ((swapX t.kem.val new x).backend.2.2.active = true ∧ owner = t.kem.val ∧
            PqxdhDeploymentIdealSteps.initSentAt (swapX t.kem.val new x).base.native.owners owner = true) :=
          fun chosen => ne chosen.2.1
        simp only [handlerWith]
        rw [PqxdhDeploymentIdealEnvStep.idealSplit_finish_real setup codec route checks t (withChosen p new) created owner raw
            (swapX t.kem.val new x) real',
          PqxdhDeploymentIdealEnvStep.idealSplit_finish_real setup codec route checks t p created owner raw x real]
        exact quietNative ⟨.finish owner raw, trivial⟩ (fun _ _ same => by cases same) (fun _ same => by cases same)
          (fun raw' same => ne (by cases same; rfl))
    | hmac key message =>
        simp only [handlerWith]
        rw [PqxdhDeploymentIdealEnvStep.idealSplit_hmac, PqxdhDeploymentIdealEnvStep.idealSplit_hmac]
        exact quietNative ⟨.hmac key message, trivial⟩ (fun _ _ same => by cases same) (fun _ same => by cases same) (fun _ same => by cases same)
    | hash bytes =>
        exact onBase_swaps t.kem.val p.chosen.2 new _ _ (nativeHandler_swaps setup codec checks route created.seed
          t.kem.val p.chosen.2 new (.hash bytes) (fun _ _ same => by cases same) (fun _ same => by cases same)
          (fun _ same => by cases same)) x held
    | serverSend keyId plaintext =>
        exact onBase_swaps t.kem.val p.chosen.2 new _ _
          (serverStep_swaps setup codec route t.kem.val p.chosen.2 new (.inl (plaintext, keyId))) x held
    | serverRaw raw =>
        exact onBase_swaps t.kem.val p.chosen.2 new _ _
          (serverStep_swaps setup codec route t.kem.val p.chosen.2 new (.inr raw)) x held
    | beaconSend owner plaintext =>
        exact onBase_swaps t.kem.val p.chosen.2 new _ _
          (beaconStep_swaps setup codec t.kem.val p.chosen.2 new owner (.inl plaintext)) x held
    | beaconRaw owner raw =>
        exact onBase_swaps t.kem.val p.chosen.2 new _ _
          (beaconStep_swaps setup codec t.kem.val p.chosen.2 new owner (.inr raw)) x held

/-- The replacement keeps the initial extended state, which has no owner. -/
theorem swapX_initial (index : ℕ) (secret : KemSK) (created : PqxdhLiveServerConstruction.Created Unit) (backend : SplitBk) :
    swapX index secret (PqxdhDeploymentBackend.xinitial (KemSK := KemSK) (n := 2) created backend) =
      PqxdhDeploymentBackend.xinitial created backend := by
  have owners : (PqxdhDeploymentNative.initial (KemSK := KemSK) created).native.owners = [] := rfl
  simp only [swapX, swapNative, swapSched, PqxdhDeploymentBackend.xinitial, owners, List.modify_nil]
  rfl

end Split

/-! ### Counting decapsulations -/

section Count
variable {I D K X Response : Type}

/-- Whether a request of the opaque Phase 2 preparation interface is a KEM decapsulation. -/
def isDecapsulate : (PqxdhBeaconPhase2Preparation.Spec I D K X Response).Domain → Bool
  | .decapsulate _ _ => true
  | _ => false

/-- The collection decapsulates at most once. -/
theorem collect_decapsulate (identity : I) (prekey oneTime : D) (kem : K) (raw : PqxdhBeaconPhase2Preparation.Bytes) :
    (PqxdhBeaconPhase2Preparation.collect (X := X) (Response := Response) identity prekey oneTime kem raw).IsQueryBoundP
      (fun query => isDecapsulate query = true) 1 := by
  simp only [PqxdhBeaconPhase2Preparation.collect, OptionT.run_bind, OptionT.run_mk, OptionT.run_pure,
    OptionT.run_monadLift, Option.elimM, bind_map_left]
  repeat' (first
    | (rw [isQueryBoundP_query_bind_iff]; refine ⟨by simp [isDecapsulate], fun reply => ?_⟩)
    | (simp only [isDecapsulate, Bool.false_eq_true, ↓reduceIte, Nat.sub_self]; done)
    | (cases reply <;> simp only [Option.elim_none, Option.elim_some, isDecapsulate,
        Bool.false_eq_true, ↓reduceIte, Nat.sub_self, isQueryBoundP_pure]))



/-- The opaque preparation decapsulates at most once: the collection once, the core preparation and erasure never. -/
theorem prepare_decapsulate (control : beaconcrypt_core.pqxdh.BeaconInitSent) (identity : I) (prekey oneTime : D)
    (kem : K) (raw : PqxdhBeaconPhase2Preparation.Bytes) :
    (PqxdhBeaconPhase2Preparation.prepare (X := X) (Response := Response) control identity prekey oneTime kem
      raw).IsQueryBoundP (fun query => isDecapsulate query = true) 1 := by
  unfold PqxdhBeaconPhase2Preparation.prepare
  rw [show (1 : ℕ) = 1 + 0 from rfl]
  refine isQueryBoundP_bind (collect_decapsulate identity prekey oneTime kem raw) fun inputs _ => ?_
  rcases inputs with _ | inputs
  · exact isQueryBoundP_pure _ _ _
  · simp only [PqxdhBeaconPhase2Preparation.afterInputs]
    rw [isQueryBoundP_query_bind_iff]
    exact ⟨by simp [isDecapsulate], fun _ => isQueryBoundP_pure _ _ _⟩

/-- Whether a request of the native finish callback interface is a KEM decapsulation. -/
def isDecapsulateNative :
    (PqxdhBeaconPhase2Publication.NativeSpec I D K X Response).Domain → Bool
  | .inl query => isDecapsulate query
  | .inr _ => false

/-- The native owner program decapsulates at most once: only its preparation decapsulates, and only once. -/
theorem nativeOwner_decapsulate (decode : RawCtxReceive.FrameDecoder) (raw : PqxdhBeaconPhase2Preparation.Bytes)
    (state : PqxdhBeaconPhase2Preparation.State I D K) :
    (PqxdhBeaconPhase2Publication.nativeOwner (X := X) (Response := Response) decode raw state).IsQueryBoundP
      (fun query => isDecapsulateNative query = true) 1 := by
  let isDecapsulateFull : (PqxdhBeaconPhase2Publication.FullSpec I D K X Response).Domain → Bool
    | .inl query => isDecapsulate query
    | .inr _ => false
  have owner : (PqxdhBeaconPhase2Publication.owner (X := X) (Response := Response) decode raw state).IsQueryBoundP
      (fun query => isDecapsulateFull query = true) 1 := by
    unfold PqxdhBeaconPhase2Publication.owner
    split
    · refine isQueryBoundP_bind (p := fun query => isDecapsulateFull query = true) (n := 1) (m := 0) ?_
        fun prepared _ => ?_
      · refine (prepare_decapsulate _ _ _ _ _ raw).simulateQ_of_step (fun query decap => ?_) (fun query other => ?_)
        · simp [PqxdhBeaconPhase2Publication.preLift, isQueryBoundP_query_iff]
        · simp only [PqxdhBeaconPhase2Publication.preLift]
          rw [isQueryBoundP_query_iff]
          intro decap
          exact absurd decap other
      · rcases prepared with _ | prepared
        · exact isQueryBoundP_pure _ _ _
        · refine isQueryBoundP_bind (p := fun query => isDecapsulateFull query = true) (n := 0) (m := 0) ?_
            fun _ _ => isQueryBoundP_pure _ _ _
          refine (OracleComp.isQueryBoundP_false _ 0).simulateQ_of_step (fun _ impossible => impossible.elim)
            (fun query _ => ?_)
          simp only [PqxdhBeaconPhase2Publication.tailLift]
          rw [isQueryBoundP_query_iff]
          intro decap
          cases decap
    · exact isQueryBoundP_pure _ _ _
  refine owner.simulateQ_of_step (fun query decap => ?_) (fun query other => ?_)
  · rcases query with query | query
    · simp only [PqxdhBeaconPhase2Publication.nativeAdapter]
      rw [isQueryBoundP_query_iff]
      intro _
      exact Nat.one_pos
    · cases decap
  · rcases query with query | query
    · simp only [PqxdhBeaconPhase2Publication.nativeAdapter]
      rw [isQueryBoundP_query_iff]
      intro decap
      exact absurd decap other
    · simp only [PqxdhBeaconPhase2Publication.nativeAdapter]
      refine (OracleComp.isQueryBoundP_false _ 0).simulateQ_of_step (fun _ impossible => impossible.elim)
        (fun query _ => ?_)
      simp only [PqxdhBeaconPhase2Publication.nativeTailLift]
      rw [isQueryBoundP_query_iff]
      intro decap
      cases decap

end Count

end BeaconcryptCore.Computational.PqxdhDeploymentIdealKeySwap

-- Axiom guards (generated)

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealKeySwap.swapOwner_swapOwner' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealKeySwap.swapOwner_swapOwner

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealKeySwap.modify_set_comm' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealKeySwap.modify_set_comm

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealKeySwap.modify_append_ne' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealKeySwap.modify_append_ne

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealKeySwap.modify_append_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealKeySwap.modify_append_eq

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealKeySwap.modify_beyond' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealKeySwap.modify_beyond

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealKeySwap.modify_set_same' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealKeySwap.modify_set_same

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealKeySwap.onShared_swaps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealKeySwap.onShared_swaps

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealKeySwap.onShared_owners' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealKeySwap.onShared_owners

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealKeySwap.createPool_swaps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealKeySwap.createPool_swaps

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealKeySwap.onNative_swaps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealKeySwap.onNative_swaps

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealKeySwap.bundle_missing' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealKeySwap.bundle_missing

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealKeySwap.bundle_swaps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealKeySwap.bundle_swaps

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealKeySwap.finish_other_swaps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealKeySwap.finish_other_swaps

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealKeySwap.record_map' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealKeySwap.record_map

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealKeySwap.logged_map' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealKeySwap.logged_map

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealKeySwap.beaconImpl_map' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealKeySwap.beaconImpl_map

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealKeySwap.serverStep_swaps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealKeySwap.serverStep_swaps

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealKeySwap.beaconStep_swaps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealKeySwap.beaconStep_swaps

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealKeySwap.onBase_swaps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealKeySwap.onBase_swaps

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealKeySwap.value_swap' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealKeySwap.value_swap

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealKeySwap.snapshotAt_swap' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealKeySwap.snapshotAt_swap

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealKeySwap.realRegAt_swaps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealKeySwap.realRegAt_swaps

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealKeySwap.realAccept_swaps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealKeySwap.realAccept_swaps

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealKeySwap.createReg_swaps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealKeySwap.createReg_swaps

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealKeySwap.nativeHandler_swaps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealKeySwap.nativeHandler_swaps

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealKeySwap.pool_withChosen' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealKeySwap.pool_withChosen

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealKeySwap.split_swaps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealKeySwap.split_swaps

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealKeySwap.swapX_initial' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealKeySwap.swapX_initial

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealKeySwap.collect_decapsulate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealKeySwap.collect_decapsulate

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealKeySwap.prepare_decapsulate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealKeySwap.prepare_decapsulate

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealKeySwap.nativeOwner_decapsulate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealKeySwap.nativeOwner_decapsulate
