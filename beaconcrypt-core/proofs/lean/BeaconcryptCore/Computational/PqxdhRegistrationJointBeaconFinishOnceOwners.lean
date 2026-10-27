import BeaconcryptCore.Computational.PqxdhRegistrationJointBeaconFinishOnceTools
import BeaconcryptCore.Computational.PqxdhRegistrationJointKemPostSkeletonGroup

/-!
# Beacon owners holding a KEM creation index (item 2, stage T, owners)

Stage T bounds by one the Beacon finishes after the challenge whose decapsulation handle is the challenge marker. The marker needs the owner's KEM handle to carry the selected creation index (`PqxdhRegistrationJointBeaconOpaqueFinish.markedPreparation`), and a finish acts only on an owner in phase `initSent`. This module tracks, in the source client's owner list, how many owners hold a given KEM creation index in a phase that can still lead to a finish (`fresh`, `freshWithCoins` or `initSent`; `phaseKem`, `ownerCount`), and how each source request changes that number, for every reply of the interfaces below the client:

- a raw `create` appends one owner whose fresh phase holds the KEM index returned by the KEM pool (`create_run`, `ownerCount_birth`); the index itself is fixed by the router, which a later module tracks;
- a `bundle` keeps the owner's KEM handle (`PqxdhLivePhase1Bundle.bundle` publishes `initSent` with the fresh phase's handle; `bundle_kem`);
- a finish (the source's `nativeOwner` and the grouped owner of stage S1b) acts only on `initSent` and then ends in `aborted` or `established`, which hold no KEM handle (`owner_settles`, `groupedOwner_settles`); this is the Lean counterpart of the Rust Beacon's terminal abort (`finish_registration` returns `None` unless the Beacon is in `InitSent`, and every outcome leaves it);
- every other request keeps the owner list.

So no request other than `create` increases the count (`client_count`, `groupedClient_count`), and a grouped finish of an owner that awaits its finish with the selected index decreases it by one (`groupedFinish_count`, with `finishMark`).

These are structural facts about the source programs; they charge nothing.
-/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc

set_option autoImplicit false
set_option maxRecDepth 100000

namespace BeaconcryptCore.Computational.PqxdhRegistrationJointBeaconFinishOnce

open PqxdhServerAuthExperiment
open PqxdhRegistrationJointGeneratedFinish (EncodedEntry)

/-! ### Counting owners by KEM creation index -/

section Count

/-- The KEM creation index held by an owner's phase: the KEM handle of a `fresh`, `freshWithCoins` or `initSent` owner; an `established` or `aborted` owner holds none. -/
def phaseKem (owner : PqxdhRegistrationJointBundle.Owner) : Option Nat :=
  match owner.beacon.phase with
  | .fresh _ _ kem => some kem.2
  | .freshWithCoins _ _ _ kem => some kem.2
  | .initSent _ _ _ kem => some kem.2
  | .established _ _ _ => none
  | .aborted _ => none

/-- The KEM creation index held by an owner entry. -/
def entryKem (entry : EncodedEntry) : Option Nat := phaseKem entry.2.2

/-- The number of owners whose phase holds the KEM creation index `selected`. -/
def ownerCount (selected : Nat) (owners : List EncodedEntry) : Nat :=
  owners.countP fun entry => decide (entryKem entry = some selected)

/-- Whether an owner is in phase `initSent` with the KEM creation index `selected`. -/
def awaits (selected : Nat) (owner : PqxdhRegistrationJointBundle.Owner) : Bool :=
  match owner.beacon.phase with
  | .initSent _ _ _ kem => decide (kem.2 = selected)
  | _ => false

/-- One if the owner at `address` is in phase `initSent` with the KEM creation index `selected`. -/
def finishMark (selected : Nat) (owners : List EncodedEntry) (address : Nat) : Nat :=
  match owners[address]? with
  | some entry => if awaits selected entry.2.2 then 1 else 0
  | none => 0

theorem awaits_kem (selected : Nat) (owner : PqxdhRegistrationJointBundle.Owner) (holds : awaits selected owner = true) :
    phaseKem owner = some selected := by
  unfold awaits at holds
  unfold phaseKem
  split at holds <;> simp_all

/-- An owner that awaits its finish with the selected KEM index is counted. -/
theorem finishMark_le (selected : Nat) (owners : List EncodedEntry) (address : Nat) :
    finishMark selected owners address ≤ ownerCount selected owners := by
  unfold finishMark
  split
  · rename_i entry found
    split
    · rename_i holds
      have : 0 < ownerCount selected owners := List.countP_pos_iff.mpr
        ⟨entry, List.mem_of_getElem? found, by simp [entryKem, awaits_kem selected _ holds]⟩
      omega
    · omega
  · omega

theorem ownerCount_append (selected : Nat) (owners : List EncodedEntry) (entry : EncodedEntry) :
    ownerCount selected (owners ++ [entry]) = ownerCount selected owners + if entryKem entry = some selected then 1 else 0 := by
  simp [ownerCount, List.countP_append]

/-- Replacing the owner at an address changes the count by the replaced and the new owner's contributions. -/
theorem ownerCount_set (selected : Nat) (owners : List EncodedEntry) (address : Nat) (entry new : EncodedEntry)
    (found : owners[address]? = some entry) :
    ownerCount selected (owners.set address new) + (if entryKem entry = some selected then 1 else 0) =
      ownerCount selected owners + if entryKem new = some selected then 1 else 0 := by
  induction owners generalizing address with
  | nil => simp at found
  | cons head tail ih =>
      cases address with
      | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at found
          subst found
          simp only [ownerCount, List.set_cons_zero, List.countP_cons, decide_eq_true_eq]
          omega
      | succ address =>
          simp only [List.getElem?_cons_succ] at found
          have step := ih address found
          simp only [ownerCount] at step
          simp only [ownerCount, List.set_cons_succ, List.countP_cons]
          omega

/-- A replacement that keeps the KEM index or clears it does not increase the count. -/
theorem ownerCount_set_le (selected : Nat) (owners : List EncodedEntry) (address : Nat) (entry new : EncodedEntry)
    (found : owners[address]? = some entry) (kept : entryKem new = entryKem entry ∨ entryKem new = none) :
    ownerCount selected (owners.set address new) ≤ ownerCount selected owners := by
  have := ownerCount_set selected owners address entry new found
  rcases kept with kept | kept <;> rw [kept] at this <;> split at this <;> simp_all; omega

/-- A replacement that clears the selected KEM index decreases the count by one. -/
theorem ownerCount_set_drop (selected : Nat) (owners : List EncodedEntry) (address : Nat) (entry new : EncodedEntry)
    (found : owners[address]? = some entry) (was : entryKem entry = some selected) (cleared : entryKem new = none) :
    ownerCount selected (owners.set address new) + 1 = ownerCount selected owners := by
  have := ownerCount_set selected owners address entry new found
  simp only [was, cleared, ite_true, reduceCtorEq, ite_false, add_zero] at this
  exact this

end Count

/-! ### The owner's phase after a finish and a bundle -/

section Phase

open PqxdhRegistrationJointBundle (Identity Key)
open PqxdhJointGapDh (ScalarBytes)

/-- An owner's state after a finish attempt: unchanged if it was not in `initSent`, otherwise holding no KEM handle. -/
def Settled (before after : PqxdhRegistrationJointBundle.Owner) : Prop :=
  (after = before ∧ ∀ control prekey oneTime kem, before.beacon.phase ≠ .initSent control prekey oneTime kem) ∨
    phaseKem after = none

/-- The finish's result state holds no KEM handle: it is aborted or established. -/
theorem finish_phaseKem (control : beaconcrypt_core.pqxdh.BeaconInitSent) (state : PqxdhRegistrationJointBundle.Owner)
    (staged : Option PqxdhBeaconPhase2Publication.Staged) :
    phaseKem (PqxdhBeaconPhase2Publication.finish control state staged).2 = none := by
  unfold PqxdhBeaconPhase2Publication.finish
  cases staged with
  | none => rfl
  | some staged =>
      dsimp only
      split
      · rfl
      · split
        · rfl
        · rfl

/-- The source's Beacon finish owner acts only on `initSent` and leaves an aborted or established owner. -/
theorem owner_settles {X Response : Type} (decode : RawCtxReceive.FrameDecoder) (raw : Pqxdh.Bytes)
    (state : PqxdhRegistrationJointBundle.Owner) :
    ∀ result ∈ support (PqxdhBeaconPhase2Publication.owner (X := X) (Response := Response) decode raw state),
      Settled state result.2 := by
  intro result member
  unfold PqxdhBeaconPhase2Publication.owner at member
  split at member
  · right
    rw [mem_support_bind_iff] at member
    obtain ⟨prepared, -, member⟩ := member
    cases prepared with
    | none =>
        simp only [support_pure, Set.mem_singleton_iff] at member
        rw [member]
        exact finish_phaseKem _ _ _
    | some prepared =>
        simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at member
        obtain ⟨staged, -, member⟩ := member
        rw [member]
        exact finish_phaseKem _ _ _
  · left
    simp only [support_pure, Set.mem_singleton_iff] at member
    rw [member]
    refine ⟨rfl, fun control prekey oneTime kem active => ?_⟩
    rename_i notActive
    exact notActive control prekey oneTime kem active

/-- The grouped Beacon owner of stage S1b acts only on `initSent` and leaves an aborted or established owner. -/
theorem groupedOwner_settles {Response : Type} (raw : Pqxdh.Bytes) (state : PqxdhRegistrationJointBundle.Owner) :
    ∀ result ∈ support (PqxdhRegistrationJointKemPostSkeleton.groupedOwner (Response := Response) raw state),
      Settled state result.2 := by
  intro result member
  unfold PqxdhRegistrationJointKemPostSkeleton.groupedOwner at member
  split at member
  · right
    rw [mem_support_bind_iff] at member
    obtain ⟨prepared, -, member⟩ := member
    cases prepared with
    | none =>
        simp only [support_pure, Set.mem_singleton_iff] at member
        rw [member]
        exact finish_phaseKem _ _ _
    | some prepared =>
        simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at member
        obtain ⟨staged, -, member⟩ := member
        rw [member]
        exact finish_phaseKem _ _ _
  · left
    simp only [support_pure, Set.mem_singleton_iff] at member
    rw [member]
    refine ⟨rfl, fun control prekey oneTime kem active => ?_⟩
    rename_i notActive
    exact notActive control prekey oneTime kem active

/-- A settled owner keeps or clears its KEM index. -/
theorem settled_kept {before after : PqxdhRegistrationJointBundle.Owner} (settled : Settled before after) :
    phaseKem after = phaseKem before ∨ phaseKem after = none := by
  rcases settled with ⟨rfl, -⟩ | cleared
  · exact Or.inl rfl
  · exact Or.inr cleared

/-- A settled owner that awaited its finish holds no KEM index. -/
theorem settled_awaits {selected : Nat} {before after : PqxdhRegistrationJointBundle.Owner} (settled : Settled before after)
    (holds : awaits selected before = true) : phaseKem after = none := by
  rcases settled with ⟨-, inactive⟩ | cleared
  · unfold awaits at holds
    split at holds
    · rename_i control prekey oneTime kem active
      exact absurd active (inactive control prekey oneTime kem)
    · simp at holds
  · exact cleared

/-- The publication after a successful bundle keeps the KEM handle of the fresh phase. -/
theorem afterSigning_kem (identity : Std.Array Std.U8 32#usize) (bundle : PqxdhEd25519EufCma.Phase1Candidate)
    (generated : Option ScalarBytes) (state : PqxdhRegistrationJointBundle.Owner) :
    ∀ result ∈ support (PqxdhBeaconPhase1Publication.afterSigning identity bundle generated state),
      phaseKem result.2 = phaseKem state := by
  intro result member
  unfold PqxdhBeaconPhase1Publication.afterSigning at member
  split at member
  · simp only [support_pure, Set.mem_singleton_iff] at member
    rw [member]
  · rename_i prepared found
    simp only [mem_support_bind_iff] at member
    obtain ⟨serialized, -, member⟩ := member
    split at member
    · simp only [support_pure, Set.mem_singleton_iff] at member
      rw [member]
    · simp only [support_pure, Set.mem_singleton_iff] at member
      rw [member]
      unfold PqxdhBeaconPhase1Publication.prepare at found
      unfold PqxdhBeaconPhase1Publication.publish phaseKem
      split at found
      · rename_i control prekey kem active
        cases generated with
        | none => simp at found
        | some oneTime =>
            simp only [Option.map_some, Option.some.injEq] at found
            subst found
            simp [active]
      · rename_i control prekey oneTime kem active
        simp only [Option.some.injEq] at found
        subst found
        simp [active]
      · simp at found

/-- A bundle keeps the owner's KEM handle. -/
theorem bundle_kem (projection : PqxdhLivePhase1Bundle.Public Identity ScalarBytes Key)
    (state : PqxdhRegistrationJointBundle.Owner) :
    ∀ result ∈ support (PqxdhLivePhase1Bundle.bundle projection state), phaseKem result.2 = phaseKem state := by
  have after : ∀ generated, ∀ result ∈ support (PqxdhLivePhase1Bundle.afterGenerated projection generated state),
      phaseKem result.2 = phaseKem state := by
    intro generated result member
    unfold PqxdhLivePhase1Bundle.afterGenerated at member
    split at member
    · simp only [support_pure, Set.mem_singleton_iff] at member
      rw [member]
    · rw [mem_support_bind_iff] at member
      obtain ⟨bundle, -, member⟩ := member
      split at member
      · simp only [support_pure, Set.mem_singleton_iff] at member
        rw [member]
      · exact afterSigning_kem _ _ generated state result
          (simulate_support _ _ member)
  intro result member
  unfold PqxdhLivePhase1Bundle.bundle at member
  split at member
  · rw [mem_support_bind_iff] at member
    obtain ⟨generated, -, member⟩ := member
    exact after generated result member
  · exact after none result member
  · simp only [support_pure, Set.mem_singleton_iff] at member
    rw [member]

end Phase

/-! ### Source requests and the count -/

section Client

variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}

/-- The source's raw `create` request. -/
def CreateKind : (PqxdhRegistrationJointRevealSchedule.Spec KemSK).Domain → Prop
  | .inl (.inr (.create _ _)) => True
  | _ => False

/-- The source's Beacon finish request at an address. -/
def FinishAt : (PqxdhRegistrationJointRevealSchedule.Spec KemSK).Domain → Option (Nat × Pqxdh.Bytes)
  | .inl (.inr (.finish address raw)) => some (address, raw)
  | _ => none

/-- The born owner holds the KEM index returned by the KEM pool. -/
theorem entryKem_birth (pin : PqxdhBeaconPhase2Preparation.Word32) (keyId : Std.U64)
    (value : PqxdhRegistrationJointCreation.Birth) :
    entryKem (PqxdhRegistrationJointServiceSchedule.birth pin keyId value) = some value.kemIndex := rfl

theorem ownerCount_birth (selected : Nat) (owners : List EncodedEntry) (pin : PqxdhBeaconPhase2Preparation.Word32)
    (keyId : Std.U64) (value : PqxdhRegistrationJointCreation.Birth) :
    ownerCount selected (owners ++ [PqxdhRegistrationJointServiceSchedule.birth pin keyId value]) =
      ownerCount selected owners + if value.kemIndex = selected then 1 else 0 := by
  rw [ownerCount_append, entryKem_birth]
  simp

/-- The raw `create` request runs the joint creation client and appends the born owner if there is one. -/
theorem create_run (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (pin : PqxdhBeaconPhase2Preparation.Word32) (keyId : Std.U64) (owners : List EncodedEntry) :
    (PqxdhRegistrationJointRevealSchedule.client setup codec (.inl (.inr (.create pin keyId)))).run owners =
      (fun value => (owners.length, match value with
        | none => owners
        | some value => owners ++ [PqxdhRegistrationJointServiceSchedule.birth pin keyId value])) <$>
        simulateQ PqxdhRegistrationJointServiceSchedule.poolLift (PqxdhRegistrationJointCreation.client (KemSK := KemSK)) := by
  simp only [PqxdhRegistrationJointRevealSchedule.client, PqxdhRegistrationJointServiceSchedule.handler,
    PqxdhRegistrationJointServiceSchedule.create, StateT.run, map_eq_bind_pure_comp]
  rfl

/-- The source's finish request leaves a settled owner at its address. -/
theorem finish_count (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (selected : Nat)
    (address : Nat) (raw : Pqxdh.Bytes) (owners : List EncodedEntry) :
    ∀ result ∈ support ((PqxdhRegistrationJointServiceSchedule.finish setup codec address raw).run owners),
      ownerCount selected result.2 ≤ ownerCount selected owners := by
  intro result member
  simp only [PqxdhRegistrationJointServiceSchedule.finish, StateT.run] at member
  split at member
  · simp only [support_pure, Set.mem_singleton_iff] at member
    rw [member]
  · rename_i entry found
    rw [support_map] at member
    obtain ⟨inner, reached, rfl⟩ := member
    have settled := owner_settles _ _ _ inner (simulate_support _ _
      (simulate_support _ _ (simulate_support _ _ reached)))
    exact ownerCount_set_le selected owners address entry _ found (settled_kept settled)

/-- The source's bundle request keeps the owner's KEM handle. -/
theorem bundle_count (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (selected : Nat)
    (address : Nat) (owners : List EncodedEntry) :
    ∀ result ∈ support ((PqxdhRegistrationJointServiceSchedule.bundle setup codec address).run owners),
      ownerCount selected result.2 ≤ ownerCount selected owners := by
  intro result member
  simp only [PqxdhRegistrationJointServiceSchedule.bundle, StateT.run] at member
  split at member
  · simp only [support_pure, Set.mem_singleton_iff] at member
    rw [member]
  · rename_i entry found
    rw [support_map] at member
    obtain ⟨inner, reached, rfl⟩ := member
    have kept := bundle_kem _ _ inner (simulate_support _ _ (simulate_support _ _ reached))
    exact ownerCount_set_le selected owners address entry _ found (Or.inl kept)

/-- No source request other than `create` increases the number of owners holding a KEM index. -/
theorem client_count (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (selected : Nat)
    (query : (PqxdhRegistrationJointRevealSchedule.Spec KemSK).Domain) (notCreate : ¬ CreateKind query)
    (owners : List EncodedEntry) :
    ∀ result ∈ support ((PqxdhRegistrationJointRevealSchedule.client setup codec query).run owners),
      ownerCount selected result.2 ≤ ownerCount selected owners := by
  intro result member
  rcases query with (coin | request) | read
  · simp only [PqxdhRegistrationJointRevealSchedule.client, PqxdhRegistrationJointServiceSchedule.handler,
      StateT.run_lift, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at member
    obtain ⟨_, -, rfl⟩ := member
    exact le_rfl
  · cases request with
    | create pin keyId => exact absurd trivial notCreate
    | bundle address => exact bundle_count setup codec selected address owners result member
    | finish address raw => exact finish_count setup codec selected address raw owners result member
    | _ =>
        simp only [PqxdhRegistrationJointRevealSchedule.client, PqxdhRegistrationJointServiceSchedule.handler,
          StateT.run_lift, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at member
        obtain ⟨_, -, rfl⟩ := member
        exact le_rfl
  · simp only [PqxdhRegistrationJointRevealSchedule.client, PqxdhRegistrationJointLiveRead.clientStep, StateT.run] at member
    split at member
    · simp only [support_pure, Set.mem_singleton_iff] at member
      rw [member]
    · rw [support_map] at member
      obtain ⟨_, -, rfl⟩ := member
      exact le_rfl

/-- The grouped Beacon finish leaves a settled owner at its address, and clears the selected KEM index of an owner that awaited its finish with it. -/
theorem groupedFinish_count (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (selected : Nat)
    (challenge : PqxdhKemIndCca.MlKem768Ciphertext) (marker : Nat) (address : Nat) (raw : Pqxdh.Bytes)
    (owners : List EncodedEntry) :
    ∀ result ∈ support ((PqxdhRegistrationJointKemPostSkeleton.groupedFinish setup codec marker challenge address
        raw).run owners),
      ownerCount selected result.2 + finishMark selected owners address ≤ ownerCount selected owners := by
  intro result member
  simp only [PqxdhRegistrationJointKemPostSkeleton.groupedFinish, StateT.run] at member
  split at member
  · rename_i missing
    simp only [support_pure, Set.mem_singleton_iff] at member
    rw [member]
    simp [finishMark, missing]
  · rename_i entry found
    rw [support_map] at member
    obtain ⟨inner, reached, rfl⟩ := member
    have settled := groupedOwner_settles _ _ inner (simulate_support _ _ reached)
    simp only [finishMark, found]
    split
    · rename_i holds
      have := ownerCount_set_drop selected owners address entry (entry.1, entry.2.1, inner.2) found
        (awaits_kem selected _ holds) (settled_awaits settled holds)
      omega
    · simpa using ownerCount_set_le selected owners address entry (entry.1, entry.2.1, inner.2) found
        (settled_kept settled)

/-- No request of the grouped client other than `create` increases the count, and a grouped finish of an owner that awaits its finish with the selected index decreases it by one. -/
theorem groupedClient_count (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (selected : Nat)
    (challenge : PqxdhKemIndCca.MlKem768Ciphertext) (marker : Nat)
    (query : (PqxdhRegistrationJointRevealSchedule.Spec KemSK).Domain) (notCreate : ¬ CreateKind query)
    (owners : List EncodedEntry) :
    ∀ result ∈ support ((PqxdhRegistrationJointKemPostSkeleton.groupedClient setup codec marker challenge query).run
        owners),
      ownerCount selected result.2 + (match FinishAt query with
        | some request => finishMark selected owners request.1
        | none => 0) ≤ ownerCount selected owners := by
  intro result member
  rcases query with (coin | request) | read
  · have := client_count setup codec selected _ notCreate owners result
      (simulate_support _ _ member)
    simpa [FinishAt] using this
  · cases request with
    | finish address raw =>
        exact groupedFinish_count setup codec selected challenge marker address raw owners result member
    | create pin keyId => exact absurd trivial notCreate
    | _ =>
        have := client_count setup codec selected _ notCreate owners result
          (simulate_support _ _ member)
        simpa [FinishAt] using this
  · have := client_count setup codec selected _ notCreate owners result
      (simulate_support _ _ member)
    simpa [FinishAt] using this

end Client

end BeaconcryptCore.Computational.PqxdhRegistrationJointBeaconFinishOnce

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointBeaconFinishOnce.awaits_kem' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointBeaconFinishOnce.awaits_kem

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointBeaconFinishOnce.finishMark_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointBeaconFinishOnce.finishMark_le

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointBeaconFinishOnce.ownerCount_append' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointBeaconFinishOnce.ownerCount_append

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointBeaconFinishOnce.ownerCount_set' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointBeaconFinishOnce.ownerCount_set

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointBeaconFinishOnce.ownerCount_set_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointBeaconFinishOnce.ownerCount_set_le

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointBeaconFinishOnce.ownerCount_set_drop' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointBeaconFinishOnce.ownerCount_set_drop

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointBeaconFinishOnce.finish_phaseKem' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointBeaconFinishOnce.finish_phaseKem

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointBeaconFinishOnce.owner_settles' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointBeaconFinishOnce.owner_settles

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointBeaconFinishOnce.groupedOwner_settles' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointBeaconFinishOnce.groupedOwner_settles

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointBeaconFinishOnce.settled_kept' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointBeaconFinishOnce.settled_kept

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointBeaconFinishOnce.settled_awaits' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointBeaconFinishOnce.settled_awaits

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointBeaconFinishOnce.afterSigning_kem' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointBeaconFinishOnce.afterSigning_kem

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointBeaconFinishOnce.bundle_kem' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointBeaconFinishOnce.bundle_kem

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointBeaconFinishOnce.entryKem_birth' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointBeaconFinishOnce.entryKem_birth

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointBeaconFinishOnce.ownerCount_birth' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointBeaconFinishOnce.ownerCount_birth

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointBeaconFinishOnce.create_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointBeaconFinishOnce.create_run

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointBeaconFinishOnce.finish_count' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointBeaconFinishOnce.finish_count

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointBeaconFinishOnce.bundle_count' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointBeaconFinishOnce.bundle_count

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointBeaconFinishOnce.client_count' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointBeaconFinishOnce.client_count

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointBeaconFinishOnce.groupedFinish_count' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointBeaconFinishOnce.groupedFinish_count

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointBeaconFinishOnce.groupedClient_count' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointBeaconFinishOnce.groupedClient_count
