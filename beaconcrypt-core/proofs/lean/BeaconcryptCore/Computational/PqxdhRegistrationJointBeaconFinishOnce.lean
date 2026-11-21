import BeaconcryptCore.Computational.PqxdhRegistrationJointBeaconFinishOncePrefix
import BeaconcryptCore.Computational.PqxdhRegistrationJointKemSecondEntry

/-!
# Stage T: at most two hidden reads (item 2)

Stage S2 counted one hidden read for the Server's private resumption root and one for every Beacon finish request after the cut, `1 + qFinish` in all (`PqxdhRegistrationJointKemRootExpand.rootClient_root`). Stage T tightens this to 2 (item 2 plan sections 3, 5 and 17): after the challenge, at most one grouped Beacon finish carries the challenge marker.

The reason is the Beacon's terminal finish together with the uniqueness of KEM creation indices. The Rust Beacon (`finish_registration` in `beaconcrypt/src/beacon.rs`) acts only in `InitSent` and leaves it on every outcome (success, or `abort_registration`), and every Beacon generates its own ML-KEM key pair, so the owner of a KEM key decapsulates at most once. In the Lean model:

- a Beacon finish acts only on an owner in phase `initSent` and leaves it aborted or established, and a bundle keeps the owner's KEM handle (`PqxdhRegistrationJointBeaconFinishOnceOwners`);
- a grouped finish carries the challenge marker only for an owner whose KEM handle has the selected creation index (`PqxdhRegistrationJointBeaconFinishOnceMarked`);
- the KEM router hands out every creation index once, from a counter that only grows, and a raw `create` gives the born owner exactly that index (`PqxdhRegistrationJointBeaconFinishOnceRouter`);
- so the number of owners holding the selected index, plus one while the router has not yet handed it out, starts at one, is not increased by any request before or after the cut, and drops by one at every marked finish (`PqxdhRegistrationJointBeaconFinishOncePrefix`, `PqxdhRegistrationJointBeaconFinishOncePost`).

This needs no premise at all: the bound 2 holds for every source program, not only for programs within the source budget.

The module restates the consequences with 2 in place of `1 + qFinish`, as new theorems beside the existing ones:

- `rootClient_two` and `entryClient_two`: the root client of stage S2 and the factored root client of stage S3b make at most two root (hidden) requests;
- `opaqueBranch_uniform_two`: stages S1c and S2 with the PRF sum over two slots;
- `opaqueBranch_idealKeys_two`: theorem T7 with the PRF sum over two slots;
- `opaqueBranch_allIdeal_two` and `opaqueBranch_slots_two`: stage S7 with both sums over two entries, and its slot form through the first-touch allocator on `PqxdhRecordLiftInterface.Slot 2`, the slot count of the CE-11 hand-off (`slotGame_two`).

The decorrelation caveat of T7 (route R1) and the premises `certified` (for the S1c term only) and `SourceFullCorrect` apply unchanged.
-/

open OracleComp OracleSpec ENNReal

set_option autoImplicit false
set_option maxRecDepth 100000

namespace BeaconcryptCore.Computational.PqxdhRegistrationJointBeaconFinishOnce

open PqxdhKemIndCca PqxdhInitializerSecrecy PqxdhServerAuthExperiment PqxdhJointIdentity
open PqxdhSecretInputKdf (hmacPrfRealGame hmacPrfRandomGame extractRealGame extractUniformGame)
open PqxdhFullSecretInputKdf (SourceFullCorrect)
open PqxdhServerAuthKeySchedule (uniform32 initExtractReduction initExpandReduction stepExtractReduction
  stepExpandReduction)
open PqxdhCorrelatedExpandHybrid (IsRoot uniformGame indexedReduction)
open PqxdhRegistrationJointKemCommands (SourceSpec)
open PqxdhRegistrationJointKemRawOpaque (opaqueBranch)
open PqxdhRegistrationJointKemRootExpand (rootClient)
open PqxdhRegistrationJointKemPostSkeleton (sharedStart sharedClient)
open PqxdhRegistrationJointKemEntryFactor (Output entryClient entryD)
open PqxdhRegistrationJointKemIdealKeys (idealKeysBranch)
open PqxdhRegistrationJointKemSecondEntry (IsValue keyScheduleBound entryDk allIdealBranch slotGame)
open PqxdhExtractRomHiddenSuffix (splitGame)

variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response A X : Type}

/-! ### Two hidden reads -/

/-- Stage T. The root client of stage S2 makes at most two root requests, repeated requests included: one at the Server's private resumption root and at most one at a grouped Beacon finish on the challenge marker. No premise is needed. -/
theorem rootClient_two (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes)
    (decision : X → Bool) (work : OracleComp (SourceSpec KemSK) X) (runtime : A)
    (count : Nat) (selected : Fin (count + 1)) (index : Nat) :
    (rootClient (Reader := Reader) setup codec checks ensureInit supplied decision work runtime count selected
      index).IsQueryBoundP IsRoot 2 := by
  unfold rootClient PqxdhRegistrationJointKemRootExpand.internalize
  rw [← Nat.zero_add 2]
  refine isQueryBoundP_bind (PqxdhCorrelatedExpandQueryBounds.rootCoins_roots _) fun start reached => ?_
  rw [StateT.run'_eq, isQueryBoundP_map_iff]
  refine IsQueryBoundP.simulateQ_run_StateT_of_step ?_
    (fun query cache => PqxdhRegistrationJointKemRootExpand.publicLocal_root query cache) start.1
  refine postSkel_two setup codec checks decision count selected _ start.2.1 start.2.2.2 start.2.2.1 ?_
  exact sharedStart_once setup codec checks ensureInit supplied decision work runtime count selected index start
    (OracleComp.mem_support_of_mem_support_liftComp _ _ start reached)

/-- Stage T for the factored root client of stage S3b: at most two hidden reads. -/
theorem entryClient_two (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes)
    (decision : X → Bool) (work : OracleComp (SourceSpec KemSK) X) (runtime : A)
    (count : Nat) (selected : Fin (count + 1)) (index : Nat) :
    (entryClient (Reader := Reader) setup codec checks ensureInit supplied decision work runtime count selected
      index).IsQueryBoundP (IsValue (D := PqxdhCorrelatedExtractFamily.Message) (R := Output)) 2 := by
  unfold entryClient PqxdhRegistrationJointKemEntryFactor.internalizeV
  rw [← Nat.zero_add 2]
  refine isQueryBoundP_bind (IsQueryBoundP.liftComp_subSpec (fun _ => Iff.rfl) (isQueryBoundP_false _ 0))
    fun start reached => ?_
  rw [StateT.run'_eq, isQueryBoundP_map_iff]
  refine IsQueryBoundP.simulateQ_run_StateT_of_step ?_
    (fun query cache => PqxdhRegistrationJointKemSecondEntry.publicLocalV_value query cache) start.1
  refine postSkel_two setup codec checks decision count selected _ start.2.1 start.2.2.2 start.2.2.1 ?_
  exact sharedStart_once setup codec checks ensureInit supplied decision work runtime count selected index start
    (OracleComp.mem_support_of_mem_support_liftComp _ _ start reached)

/-! ### Stage S2 and theorem T7 with two slots -/

/-- Stage S2 with two slots: G1's split world (H1) and the uniform-root world (H2) are distinguishable with advantage at most the sum of two one-query HMAC-SHA-512 PRF advantages. -/
theorem split_uniform_two (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes)
    (decision : X → Bool) (work : OracleComp (SourceSpec KemSK) X) (runtime : A)
    (count : Nat) (selected : Fin (count + 1)) (index : Nat) :
    (splitGame (sharedStart (Reader := Reader) setup codec checks ensureInit supplied decision work runtime count
        selected index) (sharedClient setup codec checks decision count selected)).boolDistance
      (uniformGame (rootClient (Reader := Reader) setup codec checks ensureInit supplied decision work runtime count
        selected index)) ≤
      ∑ slot ∈ Finset.range 2,
        (hmacPrfRealGame setup.hmac (indexedReduction setup.hmac (rootClient (Reader := Reader) setup codec checks
          ensureInit supplied decision work runtime count selected index) slot)).boolDistance
          (hmacPrfRandomGame (indexedReduction setup.hmac (rootClient (Reader := Reader) setup codec checks ensureInit
            supplied decision work runtime count selected index) slot)) := by
  rw [PqxdhRegistrationJointKemRootExpand.splitGame_expanded]
  exact PqxdhCorrelatedExpandHybrid.expanded_uniform_bound setup.hmac _ _
    (rootClient_two setup codec checks ensureInit supplied decision work runtime count selected index)

/-- Stages S1c and S2 with two slots: the opaque KEM-ideal branch of theorem T6 (H0) and the uniform-root world (H2) are distinguishable with advantage at most `(qAccept + qFinish + qHmac) / 2^256` (route R1) plus the sum of two one-query HMAC-SHA-512 PRF advantages. -/
theorem opaqueBranch_uniform_two (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes)
    (decision : X → Bool) (work : OracleComp (SourceSpec KemSK) X) (runtime : A)
    (count : Nat) (selected : Fin (count + 1)) (index : Nat)
    (budget : PqxdhRegistrationJointRevealCosts.SourceKind → Nat)
    (certified : ∀ source, work.IsQueryBoundP
      (fun query => PqxdhRegistrationJointRevealCosts.sourceKind (KemSK := KemSK) query = source) (budget source)) :
    (opaqueBranch (Reader := Reader) setup codec checks ensureInit supplied decision work runtime count selected index
        false).boolDistance
      (uniformGame (rootClient (Reader := Reader) setup codec checks ensureInit supplied decision work runtime count
        selected index)) ≤
      ((budget (.inl 3) + budget (.inl 5) + budget (.inl 6) : ℕ) : ℝ) / 2 ^ 256 +
        ∑ slot ∈ Finset.range 2,
          (hmacPrfRealGame setup.hmac (indexedReduction setup.hmac (rootClient (Reader := Reader) setup codec checks
            ensureInit supplied decision work runtime count selected index) slot)).boolDistance
            (hmacPrfRandomGame (indexedReduction setup.hmac (rootClient (Reader := Reader) setup codec checks
              ensureInit supplied decision work runtime count selected index) slot)) :=
  (ProbComp.boolDistance_triangle _ _ _).trans (add_le_add
    (PqxdhRegistrationJointKemRomSplit.opaqueBranch_split setup codec checks ensureInit supplied decision work runtime
      count selected index budget certified)
    (split_uniform_two setup codec checks ensureInit supplied decision work runtime count selected index))

/-- Theorem T7 with stage T. The opaque KEM-ideal branch of theorem T6 (H0) and the ideal-key branch (H4) are distinguishable with advantage at most `(qAccept + qFinish + qHmac) / 2^256`, plus the sum of two one-query HMAC-SHA-512 PRF advantages of reductions built from the candidate-free root client, plus four key-schedule advantages of reductions built from entry 0's distinguisher `entryD`. The first term is valid only because the zero-key 192-byte Extract slice is modelled as a random oracle (route R1): it pays for removing the hidden entries' dependence on the KEM candidate and their reachability by direct reads, and R1 also gives the hidden entries at distinct coordinates their mutual independence; without that idealization this step would be the forbidden decorrelation. This is a two-sided transfer of the registration segment, not a secrecy theorem: it has no test query and covers no later record. -/
theorem opaqueBranch_idealKeys_two (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes)
    (decision : X → Bool) (work : OracleComp (SourceSpec KemSK) X) (runtime : A)
    (count : Nat) (selected : Fin (count + 1)) (index : Nat)
    (budget : PqxdhRegistrationJointRevealCosts.SourceKind → Nat)
    (certified : ∀ source, work.IsQueryBoundP
      (fun query => PqxdhRegistrationJointRevealCosts.sourceKind (KemSK := KemSK) query = source) (budget source))
    (correct : SourceFullCorrect setup.source setup.hmac) :
    (opaqueBranch (Reader := Reader) setup codec checks ensureInit supplied decision work runtime count selected index
        false).boolDistance
      (idealKeysBranch (Reader := Reader) setup codec checks ensureInit supplied decision work runtime count selected
        index) ≤
      ((budget (.inl 3) + budget (.inl 5) + budget (.inl 6) : ℕ) : ℝ) / 2 ^ 256 +
        ∑ slot ∈ Finset.range 2,
          (hmacPrfRealGame setup.hmac (indexedReduction setup.hmac (rootClient (Reader := Reader) setup codec checks
            ensureInit supplied decision work runtime count selected index) slot)).boolDistance
            (hmacPrfRandomGame (indexedReduction setup.hmac (rootClient (Reader := Reader) setup codec checks
              ensureInit supplied decision work runtime count selected index) slot)) +
        ((extractRealGame setup.hmac uniform32 (initExtractReduction setup.source setup.hmac
            (entryD (Reader := Reader) setup codec checks ensureInit supplied decision work runtime count selected
              index))).boolDistance
            (extractUniformGame uniform32 (initExtractReduction setup.source setup.hmac
              (entryD (Reader := Reader) setup codec checks ensureInit supplied decision work runtime count selected
                index))) +
          (hmacPrfRealGame setup.hmac (initExpandReduction setup.source
            (entryD (Reader := Reader) setup codec checks ensureInit supplied decision work runtime count selected
              index))).boolDistance
            (hmacPrfRandomGame (initExpandReduction setup.source
              (entryD (Reader := Reader) setup codec checks ensureInit supplied decision work runtime count selected
                index))) +
          (extractRealGame setup.hmac uniform32 (stepExtractReduction setup.hmac
            (entryD (Reader := Reader) setup codec checks ensureInit supplied decision work runtime count selected
              index))).boolDistance
            (extractUniformGame uniform32 (stepExtractReduction setup.hmac
              (entryD (Reader := Reader) setup codec checks ensureInit supplied decision work runtime count selected
                index))) +
          (hmacPrfRealGame setup.hmac (stepExpandReduction
            (entryD (Reader := Reader) setup codec checks ensureInit supplied decision work runtime count selected
              index))).boolDistance
            (hmacPrfRandomGame (stepExpandReduction
              (entryD (Reader := Reader) setup codec checks ensureInit supplied decision work runtime count selected
                index)))) :=
  (ProbComp.boolDistance_triangle _ _ _).trans (add_le_add
    (opaqueBranch_uniform_two setup codec checks ensureInit supplied decision work runtime count selected index budget
      certified)
    (PqxdhRegistrationJointKemIdealKeys.uniform_idealKeys setup codec checks ensureInit supplied decision work runtime
      count selected index correct))

/-! ### Stage S7 with two entries -/

/-- Stage S7 with stage T. The opaque KEM-ideal branch of theorem T6 and the game in which every hidden entry holds 108 uniform bytes are distinguishable with advantage at most `(qAccept + qFinish + qHmac) / 2^256` (route R1, stage S1c), plus the sum of two one-query HMAC-SHA-512 PRF advantages (stage S2), plus, for each of the first two fresh hidden entries, the four key-schedule advantages of G2 on that entry's distinguisher. The first term is valid only because the zero-key 192-byte Extract slice is modelled as a random oracle (R1), as in T7. -/
theorem opaqueBranch_allIdeal_two (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes)
    (decision : X → Bool) (work : OracleComp (SourceSpec KemSK) X) (runtime : A)
    (count : Nat) (selected : Fin (count + 1)) (index : Nat)
    (budget : PqxdhRegistrationJointRevealCosts.SourceKind → Nat)
    (certified : ∀ source, work.IsQueryBoundP
      (fun query => PqxdhRegistrationJointRevealCosts.sourceKind (KemSK := KemSK) query = source) (budget source))
    (correct : SourceFullCorrect setup.source setup.hmac) :
    (opaqueBranch (Reader := Reader) setup codec checks ensureInit supplied decision work runtime count selected index
        false).boolDistance
      (allIdealBranch (Reader := Reader) setup codec checks ensureInit supplied decision work runtime count selected
        index) ≤
      ((budget (.inl 3) + budget (.inl 5) + budget (.inl 6) : ℕ) : ℝ) / 2 ^ 256 +
        ∑ slot ∈ Finset.range 2,
          (hmacPrfRealGame setup.hmac (indexedReduction setup.hmac (rootClient (Reader := Reader) setup codec checks
            ensureInit supplied decision work runtime count selected index) slot)).boolDistance
            (hmacPrfRandomGame (indexedReduction setup.hmac (rootClient (Reader := Reader) setup codec checks
              ensureInit supplied decision work runtime count selected index) slot)) +
        ∑ k ∈ Finset.range 2, keyScheduleBound setup.source setup.hmac
          (entryDk (Reader := Reader) setup codec checks ensureInit supplied decision work runtime count selected index
            k) := by
  have tail : (uniformGame (rootClient (Reader := Reader) setup codec checks ensureInit supplied decision work runtime
      count selected index)).boolDistance
      (allIdealBranch (Reader := Reader) setup codec checks ensureInit supplied decision work runtime count selected
        index) ≤
      ∑ k ∈ Finset.range 2, keyScheduleBound setup.source setup.hmac
        (entryDk (Reader := Reader) setup codec checks ensureInit supplied decision work runtime count selected index
          k) := by
    rw [PqxdhRegistrationJointKemIdealKeys.advantage_left (PqxdhRegistrationJointKemSecondEntry.uniform_hybrid setup
      codec checks ensureInit supplied decision work runtime count selected index),
      ← PqxdhRegistrationJointKemSecondEntry.hybrid_all setup codec checks ensureInit supplied decision work runtime
        count selected index _ (entryClient_two setup codec checks ensureInit supplied decision work runtime count
          selected index)]
    exact PqxdhRegistrationJointKemSecondEntry.hybrid_telescope setup codec checks ensureInit supplied decision work
      runtime count selected index correct _
  exact (ProbComp.boolDistance_triangle _ _ _).trans (add_le_add
    (opaqueBranch_uniform_two setup codec checks ensureInit supplied decision work runtime count selected index budget
      certified) tail)

/-- The slot form at two slots: the first-touch allocator in front of the persistent lazy table on `PqxdhRecordLiftInterface.Slot 2` gives the game with every hidden entry ideal. -/
theorem slotGame_two (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes)
    (decision : X → Bool) (work : OracleComp (SourceSpec KemSK) X) (runtime : A)
    (count : Nat) (selected : Fin (count + 1)) (index : Nat) :
    slotGame (Reader := Reader) setup codec checks ensureInit supplied decision work runtime count selected index 2 =
      allIdealBranch (Reader := Reader) setup codec checks ensureInit supplied decision work runtime count selected
        index :=
  PqxdhRegistrationJointKemSecondEntry.slotGame_all setup codec checks ensureInit supplied decision work runtime count
    selected index 2 (entryClient_two setup codec checks ensureInit supplied decision work runtime count selected index)

/-- Stage S7 with stage T through the first-touch allocator and the persistent lazy table on two slots: the bound of `opaqueBranch_allIdeal_two`. -/
theorem opaqueBranch_slots_two (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes)
    (decision : X → Bool) (work : OracleComp (SourceSpec KemSK) X) (runtime : A)
    (count : Nat) (selected : Fin (count + 1)) (index : Nat)
    (budget : PqxdhRegistrationJointRevealCosts.SourceKind → Nat)
    (certified : ∀ source, work.IsQueryBoundP
      (fun query => PqxdhRegistrationJointRevealCosts.sourceKind (KemSK := KemSK) query = source) (budget source))
    (correct : SourceFullCorrect setup.source setup.hmac) :
    (opaqueBranch (Reader := Reader) setup codec checks ensureInit supplied decision work runtime count selected index
        false).boolDistance
      (slotGame (Reader := Reader) setup codec checks ensureInit supplied decision work runtime count selected index 2) ≤
      ((budget (.inl 3) + budget (.inl 5) + budget (.inl 6) : ℕ) : ℝ) / 2 ^ 256 +
        ∑ slot ∈ Finset.range 2,
          (hmacPrfRealGame setup.hmac (indexedReduction setup.hmac (rootClient (Reader := Reader) setup codec checks
            ensureInit supplied decision work runtime count selected index) slot)).boolDistance
            (hmacPrfRandomGame (indexedReduction setup.hmac (rootClient (Reader := Reader) setup codec checks
              ensureInit supplied decision work runtime count selected index) slot)) +
        ∑ k ∈ Finset.range 2, keyScheduleBound setup.source setup.hmac
          (entryDk (Reader := Reader) setup codec checks ensureInit supplied decision work runtime count selected index
            k) := by
  rw [slotGame_two]
  exact opaqueBranch_allIdeal_two setup codec checks ensureInit supplied decision work runtime count selected index
    budget certified correct

end BeaconcryptCore.Computational.PqxdhRegistrationJointBeaconFinishOnce

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointBeaconFinishOnce.rootClient_two' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointBeaconFinishOnce.rootClient_two

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointBeaconFinishOnce.entryClient_two' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointBeaconFinishOnce.entryClient_two

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointBeaconFinishOnce.split_uniform_two' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointBeaconFinishOnce.split_uniform_two

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointBeaconFinishOnce.opaqueBranch_uniform_two' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointBeaconFinishOnce.opaqueBranch_uniform_two

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointBeaconFinishOnce.opaqueBranch_idealKeys_two' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointBeaconFinishOnce.opaqueBranch_idealKeys_two

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointBeaconFinishOnce.opaqueBranch_allIdeal_two' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointBeaconFinishOnce.opaqueBranch_allIdeal_two

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointBeaconFinishOnce.slotGame_two' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointBeaconFinishOnce.slotGame_two

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointBeaconFinishOnce.opaqueBranch_slots_two' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointBeaconFinishOnce.opaqueBranch_slots_two
