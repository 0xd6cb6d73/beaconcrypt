-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhDeploymentQuiet

/-! Publicity of `owner` in the annotated execution (CE-5): the owner handle created `k`-th holds KEM creation index `k`. In the annotated initialized source14 execution that the KEM theorems are stated for, started from an empty KEM pool, every step keeps the KEM key list exactly as long as the owner list and keeps every owner's KEM creation index equal to its position: a Beacon creation appends one owner at the end together with one KEM pair, and no other step adds a key, removes an owner or changes a recorded index. Together with the existing ownership invariant `PqxdhRegistrationJointSchedule.Invariant` (each present KEM pair of an owner is the pool's pair at its creation index), this identifies the transcript's `owner k` with KEM creation index `k`, for every program. No assumption is used. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhDeploymentKemIndex
open PqxdhServerAuthExperiment PqxdhServerAuthNative PqxdhJointIdentity PqxdhJointGapDh
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response A Result : Type}

/-- The KEM key list is as long as the owner list, and every owner's KEM creation index is its position. -/
def Positional (state : PqxdhRegistrationJointSchedule.State KemSK) : Prop :=
  state.pool.2.keys.length = state.owners.length ∧
    ∀ (index : Nat) entry, state.owners[index]? = some entry → entry.kemIndex = index

/-- Replacing the owner of one entry keeps every recorded index. -/
theorem positional_set (state : PqxdhRegistrationJointSchedule.State KemSK) (positional : Positional state)
    (address : Nat) (entry : PqxdhRegistrationJointOwnership.Entry KemSK)
    (found : state.owners[address]? = some entry) (owner : PqxdhRegistrationSchedule.Owner KemSK)
    (pool : PqxdhRegistrationJointPreparation.Pool KemSK) (keys : pool.2.keys = state.pool.2.keys)
    (shared : NativeState KemSK) :
    Positional ⟨pool, shared, state.owners.set address { entry with owner := owner }⟩ := by
  refine ⟨?_, fun index other otherFound => ?_⟩
  · show pool.2.keys.length = (state.owners.set address { entry with owner := owner }).length
    rw [keys, List.length_set]
    exact positional.1
  by_cases same : index = address
  · subst same
    have bound := (List.getElem?_eq_some_iff.mp found).1
    rw [List.getElem?_set_self bound, Option.some.injEq] at otherFound
    subst otherFound
    exact positional.2 index entry found
  · rw [List.getElem?_set_ne (Ne.symm same)] at otherFound
    exact positional.2 index other otherFound

/-- The Server's raw-accept prefix keeps the KEM key list. -/
theorem accept_keys (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (seed : IdentitySeed) (identityIndex : Nat) (raw : Pqxdh.Bytes) (state : PqxdhRegistrationJointFinish.State KemSK)
    (result : Option Nat × PqxdhRegistrationJointFinish.State KemSK)
    (supported : result ∈ support ((PqxdhRegistrationJointServerAccept.source setup codec checks seed identityIndex
      raw).run state)) :
    result.2.1.2.keys = state.1.2.keys := by
  have prefixKeys : ∀ (start : PqxdhRegistrationJointServerPrefix.State KemSK (List Pqxdh.Bytes)),
      ∀ reached ∈ support ((simulateQ (PqxdhRegistrationJointServerPrefix.annotated setup.joint seed identityIndex
        (serverAux setup codec checks)) (PqxdhServerRootPreparation.collect raw)).run start),
        reached.2.1.2.keys = start.1.2.keys := by
    intro start
    refine OracleComp.simulateQ_run_preserves_inv_of_query (spec' := unifSpec) _
      (fun current => current.1.2.keys = start.1.2.keys) ?_ _ start rfl
    intro query current currentKeys reached member
    rw [(PqxdhRegistrationJointServerPrefix.query_slots setup.joint seed identityIndex _ query current reached member).2]
    exact currentKeys
  simp only [PqxdhRegistrationJointServerAccept.source, PqxdhRegistrationJointServerAccept.run, StateT.run_bind,
    mem_support_bind_iff] at supported
  obtain ⟨⟨_, afterGet⟩, getMember, ⟨collected, afterPrepare⟩, prepareMember, tailMember⟩ := supported
  simp only [PqxdhRegistrationJointFinish.onNative, StateT.run, support_map, Set.mem_image] at getMember tailMember
  obtain ⟨_, _, getEq⟩ := getMember
  obtain ⟨_, _, rfl⟩ := tailMember
  simp only [Prod.mk.injEq] at getEq
  obtain ⟨_, rfl⟩ := getEq
  simp only [PqxdhRegistrationJointServerAccept.sourcePrepare, StateT.run, support_map, Set.mem_image] at prepareMember
  obtain ⟨reached, reachedMember, same⟩ := prepareMember
  simp only [Prod.mk.injEq] at same
  obtain ⟨_, rfl⟩ := same
  exact prefixKeys _ reached reachedMember

/-- A finish keeps the KEM key list. -/
theorem finish_keys (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (identityIndex kemIndex : Nat)
    (raw : Pqxdh.Bytes) (owner : PqxdhRegistrationSchedule.Owner KemSK) (state : PqxdhRegistrationJointFinish.State KemSK)
    (result : (Option Pqxdh.Bytes × PqxdhRegistrationSchedule.Owner KemSK) × PqxdhRegistrationJointFinish.State KemSK)
    (supported : result ∈ support ((simulateQ (PqxdhRegistrationJointFinish.annotated setup codec identityIndex kemIndex)
      (PqxdhBeaconPhase2Publication.nativeOwner codec.frameRead raw owner)).run state)) :
    result.2.1.2.keys = state.1.2.keys := by
  refine OracleComp.simulateQ_run_preserves_inv_of_query (spec' := unifSpec) _
    (fun current => current.1.2.keys = state.1.2.keys) ?_ _ state rfl result supported
  intro query current currentKeys reached member
  rcases query with query | query
  · simp only [PqxdhRegistrationJointFinish.annotated, PqxdhRegistrationJointFinish.onPool, StateT.run, support_map,
      Set.mem_image] at member
    obtain ⟨inner, innerMember, rfl⟩ := member
    cases query with
    | decapsulate ciphertext key =>
        simp only [PqxdhRegistrationJointPreparation.annotated, support_map, Set.mem_image] at innerMember
        obtain ⟨_, _, rfl⟩ := innerMember
        exact currentKeys
    | dhIdentity seed point =>
        simp only [PqxdhRegistrationJointPreparation.annotated, support_pure, Set.mem_singleton_iff] at innerMember
        subst innerMember
        exact currentKeys
    | _ =>
        simp only [PqxdhRegistrationJointPreparation.annotated, support_map, Set.mem_image] at innerMember
        obtain ⟨_, _, rfl⟩ := innerMember
        exact currentKeys
  · simp only [PqxdhRegistrationJointFinish.annotated, PqxdhRegistrationJointFinish.onNative, StateT.run, support_map,
      Set.mem_image] at member
    obtain ⟨_, _, rfl⟩ := member
    exact currentKeys

/-- Every annotated source step keeps the positional invariant. -/
theorem positional_step (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (seed : IdentitySeed) (identityIndex : Nat) (query : (PqxdhRegistrationJointRevealSchedule.Spec KemSK).Domain)
    (state : PqxdhRegistrationJointSchedule.State KemSK) (positional : Positional state)
    (result : (PqxdhRegistrationJointRevealSchedule.Spec KemSK).Range query × PqxdhRegistrationJointSchedule.State KemSK)
    (supported : result ∈ support ((PqxdhRegistrationJointServerSchedule.source setup codec checks seed identityIndex
      query).run state)) :
    Positional result.2 := by
  have sharedKept : ∀ {Value : Type} (work : NativeGame KemSK Value)
      (reached : Value × PqxdhRegistrationJointSchedule.State KemSK),
      reached ∈ support ((PqxdhRegistrationJointSchedule.onShared work).run state) → Positional reached.2 := by
    intro Value work reached member
    simp only [PqxdhRegistrationJointSchedule.onShared, StateT.run, support_map, Set.mem_image] at member
    obtain ⟨_, _, rfl⟩ := member
    exact positional
  rcases query with request | ⟨index, field⟩
  · rcases request with coin | command
    · simp only [PqxdhRegistrationJointServerSchedule.source, PqxdhRegistrationJointRevealSchedule.source,
        PqxdhRegistrationJointSchedule.handler, StateT.run_lift, mem_support_bind_iff, support_pure,
        Set.mem_singleton_iff] at supported
      obtain ⟨_, _, rfl⟩ := supported
      exact positional
    · cases command with
      | create pin keyId =>
          simp only [PqxdhRegistrationJointServerSchedule.source, PqxdhRegistrationJointRevealSchedule.source,
            PqxdhRegistrationJointSchedule.handler, PqxdhRegistrationJointSchedule.create, StateT.run, support_map,
            Set.mem_image] at supported
          obtain ⟨material, _, rfl⟩ := supported
          refine ⟨?_, fun position entry found => ?_⟩
          · simp [PqxdhRegistrationJointSchedule.created, PqxdhRegistrationJointCreation.serviceView,
              PqxdhLiveKemBirth.created, PqxdhLiveKemBirth.record, positional.1]
          · simp only [PqxdhRegistrationJointSchedule.created, List.getElem?_append] at found
            split at found
            · exact positional.2 position entry found
            · rename_i outside
              simp only [List.getElem?_singleton] at found
              split at found
              · rename_i zero
                simp only [Option.some.injEq] at found
                subst found
                simp only [PqxdhRegistrationJointSchedule.birth]
                have lengths := positional.1
                omega
              · cases found
      | bundle address =>
          simp only [PqxdhRegistrationJointServerSchedule.source, PqxdhRegistrationJointRevealSchedule.source,
            PqxdhRegistrationJointSchedule.handler, PqxdhRegistrationJointSchedule.bundle, StateT.run] at supported
          split at supported
          · simp only [support_pure, Set.mem_singleton_iff] at supported
            subst supported
            exact positional
          · rename_i entry found
            simp only [support_map, Set.mem_image] at supported
            obtain ⟨traced, _, rfl⟩ := supported
            exact positional_set state positional address entry found traced.1.2 _ rfl state.shared
      | accept raw =>
          simp only [PqxdhRegistrationJointServerSchedule.source, PqxdhRegistrationJointServerSchedule.onBackend,
            StateT.run, support_map, Set.mem_image] at supported
          obtain ⟨accepted, acceptedMember, rfl⟩ := supported
          have keys := accept_keys setup codec checks seed identityIndex raw (state.pool, state.shared) accepted
            acceptedMember
          exact ⟨by simp only [keys]; exact positional.1, positional.2⟩
      | build session payload => exact sharedKept _ result supported
      | finish address raw =>
          simp only [PqxdhRegistrationJointServerSchedule.source, PqxdhRegistrationJointRevealSchedule.source,
            PqxdhRegistrationJointSchedule.handler, PqxdhRegistrationJointSchedule.finish, StateT.run] at supported
          split at supported
          · simp only [support_pure, Set.mem_singleton_iff] at supported
            subst supported
            exact positional
          · rename_i entry found
            simp only [support_map, Set.mem_image] at supported
            obtain ⟨finished, finishedMember, rfl⟩ := supported
            exact positional_set state positional address entry found finished.1.2 finished.2.1
              (finish_keys setup codec entry.identityIndex entry.kemIndex raw entry.owner (state.pool, state.shared)
                finished finishedMember) finished.2.2
      | hmac key message => exact sharedKept _ result supported
      | hash bytes => exact sharedKept _ result supported
      | reveal keyId => exact sharedKept _ result supported
  · simp only [PqxdhRegistrationJointServerSchedule.source, PqxdhRegistrationJointRevealSchedule.source, StateT.run,
      support_pure, Set.mem_singleton_iff] at supported
    subst supported
    simp only [PqxdhRegistrationJointLiveRead.sourceStep]
    split
    · exact positional
    · rename_i entry _
      refine ⟨?_, positional.2⟩
      cases field with
      | identity => exact positional.1
      | kem =>
          simp only [PqxdhRegistrationJointLiveRead.entrySource]
          split
          · exact positional.1
          · exact positional.1
      | prekey => exact positional.1
      | oneTime => exact positional.1
      | kernel => exact positional.1

/-- In the whole initialized annotated execution of any program from an empty KEM pool, the KEM key list of the final state is as long as its owner list and every owner's KEM creation index is its position. -/
theorem positional_initialized (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes)
    (program : OracleComp (PqxdhRegistrationJointRevealSchedule.Spec KemSK) Result)
    (state : PqxdhRegistrationJointServerPrefix.State KemSK A) (empty : state.1.2.keys = [])
    (after : PqxdhRegistrationJointServerPrefix.State KemSK A)
    (outcome : PqxdhRegistrationJointInitializedSchedule.SourceOutcome KemSK Result)
    (supported : (some outcome, after) ∈ support ((PqxdhRegistrationJointInitializedSchedule.source setup codec checks
      ensureInit supplied program).run state)) :
    Positional outcome.2.2 ∧ after.1 = outcome.2.2.pool := by
  simp only [PqxdhRegistrationJointInitializedSchedule.source, StateT.run, mem_support_bind_iff] at supported
  obtain ⟨⟨_ | created, bornState⟩, born, reached⟩ := supported
  · simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq, reduceCtorEq, false_and] at reached
  · simp only [support_map, Set.mem_image, Prod.mk.injEq, Option.some.injEq] at reached
    obtain ⟨finished, member, rfl, rfl⟩ := reached
    have bornKeys : bornState.1.2.keys = [] := by
      simp only [PqxdhRegistrationJointServerBirth.source, StateT.run, support_map, Set.mem_image] at born
      obtain ⟨constructed, _, same⟩ := born
      simp only [Prod.mk.injEq] at same
      obtain ⟨wasCreated, rfl⟩ := same
      rw [wasCreated]
      simp only [PqxdhRegistrationJointServerBirth.install]
      exact empty
    have start : Positional (PqxdhRegistrationJointSchedule.initial bornState.1
        (PqxdhRegistrationSchedule.initial created).shared) :=
      ⟨by simp [PqxdhRegistrationJointSchedule.initial, bornKeys], fun _ _ found => by
        simp [PqxdhRegistrationJointSchedule.initial] at found⟩
    refine ⟨OracleComp.simulateQ_run_preserves_inv_of_query (spec' := unifSpec) _ Positional
      (fun query current positional reached step => positional_step setup codec checks created.seed _ query current
        positional reached step) program _ start finished member, rfl⟩

/-- The owner handle created `k`-th holds KEM creation index `k`, and the final KEM pool has exactly one key per owner, in every completed initialized annotated execution from an empty KEM pool. -/
theorem owner_kemIndex (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes)
    (program : OracleComp (PqxdhRegistrationJointRevealSchedule.Spec KemSK) Result) (runtime : A)
    (after : PqxdhRegistrationJointServerPrefix.State KemSK A)
    (outcome : PqxdhRegistrationJointInitializedSchedule.SourceOutcome KemSK Result)
    (supported : (some outcome, after) ∈ support ((PqxdhRegistrationJointInitializedSchedule.source setup codec checks
      ensureInit supplied program).run ((PqxdhDynamicIdentityPool.initialState, PqxdhLiveKemBirth.empty), runtime)))
    (k : Nat) (entry : PqxdhRegistrationJointOwnership.Entry KemSK) (found : outcome.2.2.owners[k]? = some entry) :
    entry.kemIndex = k ∧ after.1.2.keys.length = outcome.2.2.owners.length := by
  obtain ⟨positional, poolEq⟩ := positional_initialized setup codec checks ensureInit supplied program _ rfl after
    outcome supported
  rw [poolEq]
  exact ⟨positional.2 k entry found, positional.1⟩

end BeaconcryptCore.Computational.PqxdhDeploymentKemIndex

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentKemIndex.positional_set' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentKemIndex.positional_set

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentKemIndex.accept_keys' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentKemIndex.accept_keys

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentKemIndex.finish_keys' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentKemIndex.finish_keys

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentKemIndex.positional_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentKemIndex.positional_step

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentKemIndex.positional_initialized' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentKemIndex.positional_initialized

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentKemIndex.owner_kemIndex' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentKemIndex.owner_kemIndex
