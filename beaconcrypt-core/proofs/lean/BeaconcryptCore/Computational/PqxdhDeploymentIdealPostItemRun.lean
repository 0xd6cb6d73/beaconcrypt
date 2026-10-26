-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhDeploymentIdealPostAccept

/-!
# Item 2's post-challenge phase as the middle run (CE-11b, unit U6, fourth part)

On an active cut, item 2's post-challenge phase (`PqxdhDeploymentIdealBranch.itemPost`) first resumes the Server's selected raw accept and then runs the tagged compiled continuation through its post-challenge layers. This module shows that the whole phase is the middle run: the ideal registration's steps after encapsulation through the allocator (`PqxdhDeploymentIdealActive.acceptAfter`), then the tagged continuation under the middle source handler from the middle state after the selected accept, read off as its output. This discharges item 2's side of the active branch.

- `AcceptRun`, `afterSelected` (the middle state after the selected accept: the cut's annotated source state with the native state after the accept, the accept counter past the selected ordinal, the accept's activity flag and mark, the allocator and the table after its read), `acceptAfter_keeps` (the accept keeps the allocator good and leaves the mark stored) and `itemInv_after` (item 2's invariant there).
- `bind_clean` and `itemPost_middle`: through `PqxdhDeploymentIdealPostItem.itemPost_clean`, item 2's view without table counters, `PqxdhDeploymentIdealPostAccept.resume_clean` and `resume_accept` for the resumption, and `PqxdhDeploymentIdealPostInvariant.item_sim` for the continuation. Premises: item 2's facts at the pool at the cut (`PoolOwned`, a prefix KEM pool, the owner positions), the constructed Server's public identity, the selected PQ key, and a continuation with only simulated requests and at most the room's number of creations.

These are program equalities. They charge nothing and make no security claim.
-/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc

set_option autoImplicit false

namespace BeaconcryptCore.Computational.PqxdhDeploymentIdealPostItemRun
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhKemIndCca (MlKem768PublicKey MlKem768Ciphertext MlKemSharedSecret)
open PqxdhDeploymentIdealParams (Target Params)
open PqxdhDeploymentIdealPostSource (Mid sourceMid)
open PqxdhDeploymentIdealPostHidden (lowerEC eraseServiceC encodeMidC)
open PqxdhDeploymentIdealPostAccept (marksOf Stored)
open PqxdhRegistrationJointKemPostSkeleton (clean)

/-! ### The middle state after the selected accept -/

section After
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}
  (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks) {count : ℕ}
  (t : Target count) (p : Params KemSK count)

/-- The outcome of the selected accept's steps after encapsulation through the allocator: the accept's output, the native state and the allocator with the table. -/
abbrev AcceptRun (KemSK : Type) :=
  (PqxdhDeploymentIdealSteps.AcceptOut × PqxdhServerAuthNative.NativeState KemSK) × PqxdhDeploymentIdealPostSim.SlotState

/-- The middle state after the selected accept: the annotated source state at the cut with the native state after the accept, the accept counter past the selected ordinal, the accept's activity flag and mark, the allocator and the table after its read, and no seed. -/
def afterSelected (joint : PqxdhRegistrationJointSchedule.State KemSK) (w : AcceptRun KemSK) : Mid KemSK where
  joint := { joint with shared := w.1.2 }
  backend := (w.2.2, (w.2.1, ⟨t.accept + 1, w.1.1.2.1, w.1.1.2.2, none, none⟩))
  seeds := ∅

/-- The steps after encapsulation through the allocator, from a good allocator state with a free slot, keep the allocator good and leave the mark stored. -/
theorem acceptAfter_keeps (seed : PqxdhJointIdentity.IdentitySeed) (value : PqxdhServerRootPreparation.Verified Reader)
    (ephemeral : PqxdhServerRootPreparation.Ephemeral PqxdhJointGapDh.ScalarBytes) (consumed : List Pqxdh.Bytes)
    (logged : Option PqxdhJointGapDh.ScalarBytes) (native : PqxdhServerAuthNative.NativeState KemSK)
    (slots : PqxdhDeploymentIdealPostSim.SlotState) (good : PqxdhRegistrationJointKemSecondEntry.SlotGood slots)
    (room : slots.1.2 < 2) (w : AcceptRun KemSK)
    (member : w ∈ support ((simulateQ (PqxdhRegistrationJointKemSecondEntry.slotImpl PqxdhDeploymentSeedSplit.tableService)
      ((PqxdhDeploymentIdealActive.acceptAfter setup codec checks seed p.challenge value ephemeral consumed
        logged).run native)).run slots)) :
    PqxdhRegistrationJointKemSecondEntry.SlotGood w.2 ∧ Stored w.1.1.2.2 w.2 := by
  change w ∈ support ((simulateQ (PqxdhRegistrationJointKemSecondEntry.slotImpl PqxdhDeploymentSeedSplit.tableService)
    (PqxdhDeploymentIdealSteps.liftS _ >>= _)).run slots) at member
  rw [simulateQ_bind, StateT.run_bind, PqxdhDeploymentIdealCut.slotImpl_lift, bind_map_left, mem_support_bind_iff]
    at member
  obtain ⟨prepared, preparedMember, member⟩ := member
  have marker := PqxdhDeploymentIdealKeymatch.program_marker _ value ephemeral
    (PqxdhAcceptedRegistration.ciphertextArray p.challenge) .challenge consumed prepared preparedMember
  rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at member
  obtain ⟨z, zMember, member⟩ := member
  simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at member
  subst member
  exact (PqxdhDeploymentIdealPostAccept.splitC_tail setup codec checks (setup.joint.publicKeys seed) native.2 prepared
    marker native none slots good (fun _ => room) (fun mark none => by cases none)).2 z zMember

/-- Item 2's invariant at the middle state after the selected accept, from the cut's facts at the pool and the accept's activity, allocator and mark. -/
theorem itemInv_after (created : PqxdhLiveServerConstruction.Created Unit) (joint : PqxdhRegistrationJointSchedule.State KemSK)
    (owned : PqxdhDeploymentIdealPoolSource.PoolOwned created.seed created.server.server.metadata.identityIndex joint)
    (prefixed : PqxdhDeploymentIdealPoolSource.PoolPrefix (p.pool t) joint.pool.2)
    (indexed : PqxdhDeploymentIdealCut.PoolIndexed joint) (w : AcceptRun KemSK) (active : w.1.1.2.1 = true)
    (good : PqxdhRegistrationJointKemSecondEntry.SlotGood w.2) (stored : Stored w.1.1.2.2 w.2) :
    PqxdhDeploymentIdealPostInvariant.ItemInv created t p (afterSelected t joint w) :=
  ⟨owned, prefixed, indexed, active, Nat.lt_succ_self _, good, stored⟩

end After

/-! ### Item 2's post-challenge phase as the middle run -/

section Item
open PqxdhRegistrationJointKemEntryFactor (Output factoredServices)
open PqxdhDeploymentIdealPostItem (cleanSkel cleanUpper)
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}
  (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
  (checks : Checks) {count : ℕ} (t : Target count) (p : Params KemSK count)

/-- A continuation that reads the skeleton state only without game observers does not see the observers of the program before it. -/
theorem bind_clean {ι' α β : Type} {spec : OracleSpec ι'}
    (first second : OracleComp spec (α × PqxdhRegistrationJointKemPostSkeleton.SkelState KemSK Output))
    (same : Prod.map id cleanSkel <$> first = Prod.map id cleanSkel <$> second)
    (next : α → PqxdhRegistrationJointKemPostSkeleton.SkelState KemSK Output → OracleComp spec β) :
    (first >>= fun answer => next answer.1 (cleanSkel answer.2)) =
      (second >>= fun answer => next answer.1 (cleanSkel answer.2)) := by
  have left : (first >>= fun answer => next answer.1 (cleanSkel answer.2)) =
      (Prod.map id cleanSkel <$> first) >>= fun answer => next answer.1 answer.2 := by
    rw [bind_map_left]
    rfl
  rw [left, same, bind_map_left]
  rfl

/-- Item 2's post-challenge phase on an active cut (a pending context whose verified PQ key is the selected one) is the middle run: the ideal registration's steps after encapsulation through the allocator from the empty allocator and table, then the tagged continuation under the middle source handler from the middle state after the selected accept, read off as its output. It needs item 2's facts at the pool at the cut, the constructed Server's public identity, and a continuation with only simulated requests and at most the room's number of creations. -/
theorem itemPost_middle {A Y : Type} (decision : Y × PqxdhDeploymentCompile.Local → Bool)
    (created : PqxdhLiveServerConstruction.Created Unit)
    (identity : created.publicIdentity = setup.joint.publicKeys created.seed) (raw : Pqxdh.Bytes)
    (value : PqxdhServerRootPreparation.Verified Reader) (matched : value.keys.pqKey = p.chosen.1)
    (ephemeral : PqxdhServerRootPreparation.Ephemeral PqxdhJointGapDh.ScalarBytes) (consumed : List Pqxdh.Bytes)
    (logged : Option PqxdhJointGapDh.ScalarBytes) (joint : PqxdhRegistrationJointSchedule.State KemSK)
    (owned : PqxdhDeploymentIdealPoolSource.PoolOwned created.seed created.server.server.metadata.identityIndex joint)
    (prefixed : PqxdhDeploymentIdealPoolSource.PoolPrefix (p.pool t) joint.pool.2)
    (indexed : PqxdhDeploymentIdealCut.PoolIndexed joint)
    (next : Option ℕ → OracleComp (PqxdhRegistrationJointKemCommands.SourceSpec KemSK) (Y × PqxdhDeploymentCompile.Local))
    (onlyAllowed : ∀ answer, (next answer).IsQueryBoundP
      (fun query => ¬ PqxdhDeploymentIdealPostInvariant.Allowed (KemSK := KemSK) query) 0)
    (budget : ℕ) (bounded : ∀ answer, (next answer).IsQueryBoundP
      (PqxdhDeploymentIdealPostInvariant.Costly (KemSK := KemSK)) budget)
    (fits : budget ≤ (p.pool t).length - joint.pool.2.keys.length) (after : A) :
    PqxdhDeploymentIdealBranch.itemPost setup codec checks t p decision
        (.ready (PqxdhRegistrationJointServerBirth.encode created) p.others
          (some (.pending raw value ephemeral consumed joint.shared
            (PqxdhRegistrationJointGeneratedFinish.encodeState setup joint).owners next))
          (joint.pool.1, PqxdhDeploymentIdealPoolSource.routerOf joint.pool.2) after) =
      (simulateQ (PqxdhRegistrationJointKemSecondEntry.slotImpl PqxdhDeploymentSeedSplit.tableService)
          ((PqxdhDeploymentIdealActive.acceptAfter setup codec checks created.seed p.challenge value ephemeral consumed
            logged).run joint.shared)).run
          (PqxdhRegistrationJointKemSecondEntry.emptyAlloc, PqxdhRecordLiftLazyTable.initial) >>= fun w =>
        (fun result => result.1) <$> (simulateQ (sourceMid setup codec route checks t p created)
          (PqxdhRegistrationJointAcceptKemCut.tagged (PqxdhRegistrationJointAcceptCutTag.decideTag decision) raw next
            w.1.1.1.1)).run (afterSelected t joint w) := by
  rw [PqxdhDeploymentIdealPostItem.itemPost_clean setup codec checks t p decision _ p.others raw value matched ephemeral
    consumed joint.shared _ next _ after]
  have counts : (PqxdhRegistrationJointKemObserverFree.eraseJoint (joint.pool.1,
      PqxdhDeploymentIdealPoolSource.routerOf joint.pool.2), (joint.shared.1.cache,
        (PqxdhRegistrationJointKemSecondEntry.emptyAlloc, PqxdhRecordLiftLazyTable.initial))) =
      PqxdhDeploymentIdealPostSim.eraseService ((joint.pool.1, PqxdhDeploymentIdealPoolSource.routerOf joint.pool.2),
        (joint.shared.1.cache, ((PqxdhRegistrationJointKemSecondEntry.emptyAlloc : PqxdhRegistrationJointKemSecondEntry.Alloc
          PqxdhCorrelatedExtractFamily.Message 2), (PqxdhRecordLiftLazyTable.initial : PqxdhDeploymentIdealSteps.TableState)))) :=
    rfl
  rw [counts]
  have toC : ∀ work : OracleComp (PqxdhRegistrationJointKemPostSkeleton.Enc KemSK +
      PqxdhRegistrationJointKemPostSkeleton.TSpec Output) ((Bool × List PqxdhRegistrationJointGeneratedFinish.EncodedEntry) ×
        PqxdhRegistrationJointKemPostSkeleton.SkelState KemSK Output),
      PqxdhRegistrationJointKemPostSkeleton.skelDecide <$> ((simulateQ (PqxdhDeploymentIdealPostSteps.lowerE setup t p)
        work).run).run (PqxdhDeploymentIdealPostSim.eraseService ((joint.pool.1,
          PqxdhDeploymentIdealPoolSource.routerOf joint.pool.2), (joint.shared.1.cache,
            ((PqxdhRegistrationJointKemSecondEntry.emptyAlloc : PqxdhRegistrationJointKemSecondEntry.Alloc
              PqxdhCorrelatedExtractFamily.Message 2), (PqxdhRecordLiftLazyTable.initial : PqxdhDeploymentIdealSteps.TableState))))) =
      PqxdhRegistrationJointKemPostSkeleton.skelDecide <$> ((simulateQ (lowerEC setup t p) work).run).run
        (eraseServiceC ((joint.pool.1, PqxdhDeploymentIdealPoolSource.routerOf joint.pool.2), (joint.shared.1.cache,
          ((PqxdhRegistrationJointKemSecondEntry.emptyAlloc : PqxdhRegistrationJointKemSecondEntry.Alloc
            PqxdhCorrelatedExtractFamily.Message 2), (PqxdhRecordLiftLazyTable.initial : PqxdhDeploymentIdealSteps.TableState))))) := by
    intro work
    rw [PqxdhDeploymentIdealPostFinish.lowerEC_run, Functor.map_map]
    rfl
  rw [toC]
  refine Eq.trans (congrArg (fun work => PqxdhRegistrationJointKemPostSkeleton.skelDecide <$>
    ((simulateQ (lowerEC setup t p) work).run).run (eraseServiceC ((joint.pool.1,
      PqxdhDeploymentIdealPoolSource.routerOf joint.pool.2), (joint.shared.1.cache,
        ((PqxdhRegistrationJointKemSecondEntry.emptyAlloc : PqxdhRegistrationJointKemSecondEntry.Alloc
          PqxdhCorrelatedExtractFamily.Message 2), (PqxdhRecordLiftLazyTable.initial : PqxdhDeploymentIdealSteps.TableState))))))
    (bind_clean _ _ (PqxdhDeploymentIdealPostAccept.resume_clean setup codec checks (factoredServices setup codec checks)
      (PqxdhRegistrationJointServerBirth.encode created).server.server.metadata.identityIndex
      (PqxdhRegistrationJointServerBirth.encode created).publicIdentity raw value ephemeral
      (PqxdhAcceptedRegistration.ciphertextArray p.challenge) joint.shared.2 consumed none)
      (fun answer skel => (fun result => ((result.1, result.2.1), result.2.2)) <$>
        (simulateQ (PqxdhDeploymentIdealPostSteps.upperE setup codec checks t p created)
          (PqxdhRegistrationJointAcceptKemCut.tagged (PqxdhRegistrationJointAcceptCutTag.decideTag decision) raw next
            answer)).run ((PqxdhRegistrationJointGeneratedFinish.encodeState setup joint).owners, skel)))) ?_
  rw [show (PqxdhRegistrationJointServerBirth.encode created).publicIdentity = setup.joint.publicKeys created.seed
      from identity, simulateQ_bind, OptionT.run_bind, Option.elimM, StateT.run_bind,
    PqxdhDeploymentIdealPostAccept.resume_accept setup codec checks t p created.seed
      (PqxdhRegistrationJointServerBirth.encode created).server.server.metadata.identityIndex raw value ephemeral consumed
      logged joint.shared joint.pool.1 joint.pool.2 prefixed owned.1.2 _
      PqxdhRegistrationJointKemSecondEntry.slotGood_empty (by decide),
    bind_map_left, map_bind]
  refine bind_congr_of_forall_mem_support _ fun w member => ?_
  have produced : w.1 ∈ support ((PqxdhDeploymentIdealActive.acceptAfter setup codec checks created.seed p.challenge value
      ephemeral consumed logged).run joint.shared) := by
    apply OracleComp.support_simulateQ_run'_subset
      (PqxdhRegistrationJointKemSecondEntry.slotImpl PqxdhDeploymentSeedSplit.tableService) _
      (PqxdhRegistrationJointKemSecondEntry.emptyAlloc, PqxdhRecordLiftLazyTable.initial)
    rw [StateT.run'_eq, support_map]
    exact ⟨w, member, rfl⟩
  have active := (PqxdhDeploymentIdealPostMark.acceptAfter_mark setup codec checks created.seed p.challenge value ephemeral
    consumed logged joint.shared w.1 produced).1
  obtain ⟨good, stored⟩ := acceptAfter_keeps setup codec checks p created.seed value ephemeral consumed logged joint.shared
    _ PqxdhRegistrationJointKemSecondEntry.slotGood_empty (by decide) w member
  have holds := itemInv_after t p created joint owned prefixed indexed w active good stored
  have encodeAfter : encodeMidC setup (afterSelected t joint w) =
      (((PqxdhRegistrationJointGeneratedFinish.encodeState setup joint).owners, (clean w.1.2.2, marksOf w.1.1.2.2 w.2)),
        eraseServiceC ((joint.pool.1, PqxdhDeploymentIdealPoolSource.routerOf joint.pool.2), (w.1.2.1.cache, w.2))) := by
    simp only [encodeMidC, PqxdhDeploymentIdealPostSteps.encodeMid, eraseServiceC, Prod.map,
      PqxdhRegistrationJointKemObserverFree.eraseJoint_idem]
    rfl
  have sim := PqxdhDeploymentIdealPostInvariant.item_sim setup codec route checks t p created identity
    (PqxdhRegistrationJointAcceptKemCut.tagged (PqxdhRegistrationJointAcceptCutTag.decideTag decision) raw next w.1.1.1.1)
    (by unfold PqxdhRegistrationJointAcceptKemCut.tagged; exact (OracleComp.isQueryBoundP_map_iff _ _ _).mpr (onlyAllowed _)) budget
    (by unfold PqxdhRegistrationJointAcceptKemCut.tagged; exact (OracleComp.isQueryBoundP_map_iff _ _ _).mpr (bounded _))
    (afterSelected t joint w) fits holds
  rw [encodeAfter] at sim
  simp only [Option.elim_some, simulateQ_map, OptionT.run_map, StateT.run_map]
  rw [show cleanSkel (clean w.1.2.2, marksOf w.1.1.2.2 w.2) = (clean w.1.2.2, marksOf w.1.1.2.2 w.2) from rfl, sim,
    Functor.map_map, Functor.map_map]
  rfl

end Item

end BeaconcryptCore.Computational.PqxdhDeploymentIdealPostItemRun

-- Axiom guards (generated)

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPostItemRun.acceptAfter_keeps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPostItemRun.acceptAfter_keeps

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPostItemRun.itemInv_after' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPostItemRun.itemInv_after

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPostItemRun.bind_clean' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPostItemRun.bind_clean

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPostItemRun.itemPost_middle' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPostItemRun.itemPost_middle
