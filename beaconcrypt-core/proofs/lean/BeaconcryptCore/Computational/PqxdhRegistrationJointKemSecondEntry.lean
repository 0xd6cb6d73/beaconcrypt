import BeaconcryptCore.Computational.PqxdhRegistrationJointKemSecondEntryTable
import BeaconcryptCore.Computational.PqxdhRegistrationJointKemIdealKeys

/-!
# Every hidden entry ideal (item 2, stage S7)

This module builds stage S7 of the item 2 plan: from the uniform-root world of stage S2 to the game in which every hidden entry, not only entry 0, holds 108 uniform bytes.

- `allIdealBranch` runs the factored root client `PqxdhRegistrationJointKemEntryFactor.entryClient` with every hidden coordinate answered by 108 uniform bytes, consistently on repeated coordinates (VCVio's lazy uniform table keyed by the 128-byte coordinates). Every other root and every other HMAC/HKDF evaluation is as in the ideal-key branch of stage S4b.
- `slotGame n` is the same game through the first-touch coordinate-to-slot allocator in front of Codex's persistent lazy table `PqxdhRecordLiftLazyTable.impl` on `PqxdhRecordLiftInterface.Slot n` (item 2 plan sections 18 and 20): a new hidden coordinate gets the next slot, equal coordinates share a slot, and the 108 bytes of a slot are read only through the table. `slotGame_all` shows that the two games are equal once `n` is at least the number of hidden reads, which is at most `1 + qFinish` (`entryClient_value`); stage T would make it 2. `entryClient_natural` is the naturality CE-11 needs: the registration core reads hidden-slot outputs only through the slot service. The first touch of a slot is a hidden read, which the skeleton makes only at the selected raw accept's private root on the challenge marker and at a grouped Beacon finish on the challenge marker (`PqxdhRegistrationJointKemRootExpand.resumeImpl_hidden`, `skelImpl_hidden`).
- The hybrid `hybrid k` answers the first `k` fresh hidden coordinates (in first-touch order) with 108 uniform bytes and every later one with the key-schedule output of a fresh uniform root. `hybrid 0` is the uniform-root world, and `hybrid (1 + qFinish)` is `allIdealBranch`. Each hop `k` to `k + 1` is the key-schedule game on the distinguisher `entryDk k` of the `k`-th fresh entry (`hybrid_root`, `hybrid_uniform`, by eager sampling of that entry), bounded by G2 (`PqxdhKeyScheduleFromRoot.fromRoot_bound`). `entryDk 0` is stage S3b's `entryD` (`entryDk_zero`), and `entryDk 1` is the distinguisher of the second entry.
- `opaqueBranch_allIdeal`: the opaque KEM-ideal branch of T6 and `allIdealBranch` are distinguishable with advantage at most the S1c and S2 terms of T7 plus the sum over `k < 1 + qFinish` of the four key-schedule advantages of G2 on `entryDk k` (`keyScheduleBound`).

The step is the plan's T7-all with the indexed lazy-table hybrid. The premises are T5's source budget and `SourceFullCorrect`. No assumption is added, and the decorrelation caveat of T7 (route R1) applies unchanged.
-/

open OracleComp OracleSpec ENNReal

set_option autoImplicit false
set_option maxRecDepth 100000

namespace BeaconcryptCore.Computational.PqxdhRegistrationJointKemSecondEntry

open PqxdhKemIndCca PqxdhInitializerSecrecy PqxdhServerAuthExperiment PqxdhJointIdentity
open PqxdhSecretInputKdf (hmacPrfRealGame hmacPrfRandomGame extractRealGame extractUniformGame RootOutput HmacOracle
  HmacSha512)
open PqxdhJointKdfGame (FixedHkdfSha512NoSaltSource)
open PqxdhFullSecretInputKdf (SourceFullCorrect)
open PqxdhServerAuthKeySchedule (uniform32 initExtractReduction initExpandReduction stepExtractReduction
  stepExpandReduction rootHybrid fromRoot)
open PqxdhCorrelatedExpandHybrid (indexedReduction)
open PqxdhRegistrationJointKemCommands (SourceSpec)
open PqxdhRegistrationJointKemRawOpaque (opaqueBranch)
open PqxdhRegistrationJointKemRootExpand (rootClient)
open PqxdhRegistrationJointKemPostSkeleton (SkelSpec sharedStart postSkel)
open PqxdhRegistrationJointKemEntryFactor (Output EntrySpec entryClient entryD internalizeV publicLocalV)

/-! ### The four key-schedule advantages of G2 -/

/-- The bound of G2 on a distinguisher: two Extract advantages on an independent uniform 32-byte input and two HMAC-SHA-512 PRF advantages of the reductions of `PqxdhServerAuthKeySchedule`. -/
noncomputable def keyScheduleBound (source : FixedHkdfSha512NoSaltSource) (hmac : HmacSha512)
    (distinguisher : PqxdhServerAuthKeySchedule.Distinguisher) : ℝ :=
  (extractRealGame hmac uniform32 (initExtractReduction source hmac distinguisher)).boolDistAdvantage
      (extractUniformGame uniform32 (initExtractReduction source hmac distinguisher)) +
    (hmacPrfRealGame hmac (initExpandReduction source distinguisher)).boolDistAdvantage
      (hmacPrfRandomGame (initExpandReduction source distinguisher)) +
    (extractRealGame hmac uniform32 (stepExtractReduction hmac distinguisher)).boolDistAdvantage
      (extractUniformGame uniform32 (stepExtractReduction hmac distinguisher)) +
    (hmacPrfRealGame hmac (stepExpandReduction distinguisher)).boolDistAdvantage
      (hmacPrfRandomGame (stepExpandReduction distinguisher))

/-- G2 with its bound written as `keyScheduleBound`. -/
theorem keySchedule_hop (source : FixedHkdfSha512NoSaltSource) (hmac : HmacSha512)
    (correct : SourceFullCorrect source hmac) (distinguisher : PqxdhServerAuthKeySchedule.Distinguisher) :
    (rootHybrid source distinguisher).boolDistAdvantage (PqxdhServerAuthKeySchedule.uniformGame distinguisher) ≤
      keyScheduleBound source hmac distinguisher :=
  PqxdhKeyScheduleFromRoot.fromRoot_bound source hmac correct distinguisher

/-- Two games with equal output distributions have equal advantages against any game, on the right. -/
theorem advantage_right {left right right' : ProbComp Bool} (same : 𝒟[right] = 𝒟[right']) :
    left.boolDistAdvantage right = left.boolDistAdvantage right' := by
  unfold ProbComp.boolDistAdvantage
  rw [same]

/-! ### The number of hidden reads of the factored root client -/

section Count

variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response A X : Type}

/-- One step of the root client's local interpretation makes one value request for a hidden read and none otherwise. -/
theorem publicLocalV_value {V : Type} (query : (SkelSpec V).Domain) (cache : HmacOracle.QueryCache) :
    ((publicLocalV V query).run cache).IsQueryBoundP (IsValue (D := PqxdhCorrelatedExtractFamily.Message) (R := V))
      (if PqxdhRegistrationJointKemRootExpand.valueRead? query = true then 1 else 0) := by
  rcases query with coin | (message | point)
  · change ((fun reply => (reply, cache)) <$>
      (liftM ((EntrySpec V).query (.inl coin)) : OracleComp (EntrySpec V) _)).IsQueryBoundP _ 0
    rw [isQueryBoundP_map_iff]
    exact PqxdhRegistrationJointKemRomSplit.query_free _ _ (by simp [IsValue])
  · change ((fun reply => (reply, cache)) <$>
      (liftM ((EntrySpec V).query (.inr message)) : OracleComp (EntrySpec V) _)).IsQueryBoundP _ 1
    rw [isQueryBoundP_map_iff]
    exact PqxdhRegistrationJointKemRomSplit.query_one _ _
  · change (OracleComp.liftComp ((HmacOracle.randomOracle point).run cache) (EntrySpec V)).IsQueryBoundP _ 0
    exact IsQueryBoundP.liftComp_subSpec (fun _ => Iff.rfl) (isQueryBoundP_false _ 0)

/-- The factored root client makes at most `1 + qFinish` hidden reads: at most one at the Server's resumption and at most one per Beacon finish request after the cut. -/
theorem entryClient_value (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes)
    (decision : X → Bool) (work : OracleComp (SourceSpec KemSK) X) (runtime : A)
    (count : Nat) (selected : Fin (count + 1)) (index : Nat)
    (budget : PqxdhRegistrationJointRevealCosts.SourceKind → Nat)
    (certified : ∀ source, work.IsQueryBoundP
      (fun query => PqxdhRegistrationJointRevealCosts.sourceKind (KemSK := KemSK) query = source) (budget source)) :
    (entryClient (Reader := Reader) setup codec checks ensureInit supplied decision work runtime count selected
      index).IsQueryBoundP (IsValue (D := PqxdhCorrelatedExtractFamily.Message) (R := Output)) (1 + budget (.inl 5)) := by
  have inherits := PqxdhRegistrationJointKemRootExpand.sharedStart_inherit (Reader := Reader)
    PqxdhRegistrationJointKemRootExpand.FinishKind setup codec checks ensureInit supplied decision work runtime count
    selected index (budget (.inl 5)) (PqxdhRegistrationJointKemRootExpand.certified_finish work budget certified)
  unfold entryClient internalizeV
  rw [← Nat.zero_add (1 + budget (.inl 5))]
  refine isQueryBoundP_bind (IsQueryBoundP.liftComp_subSpec (fun _ => Iff.rfl) (isQueryBoundP_false _ 0))
    fun start reached => ?_
  rw [StateT.run'_eq, isQueryBoundP_map_iff]
  refine IsQueryBoundP.simulateQ_run_StateT_of_step ?_ (fun query cache => publicLocalV_value query cache) start.1
  refine PqxdhRegistrationJointKemRootExpand.postSkel_hidden setup codec checks decision count selected _ start.2.1
    start.2.2.2 start.2.2.1 _ ?_
  exact inherits start (OracleComp.mem_support_of_mem_support_liftComp _ _ start reached)

end Count

/-! ### The hybrids -/

section Hybrid

variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response A X : Type}

/-- The sampler of the `k`-th hybrid: the first `k` fresh hidden coordinates get 108 uniform bytes, every later one the key-schedule output of a fresh uniform root. -/
noncomputable def sampler (source : FixedHkdfSha512NoSaltSource) (k : ℕ) : ℕ → ProbComp Output :=
  fun j => if j < k then $ᵗ Output else fromRoot source <$> ($ᵗ RootOutput)

/-- The `k`-th hybrid. -/
noncomputable def hybrid (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes)
    (decision : X → Bool) (work : OracleComp (SourceSpec KemSK) X) (runtime : A)
    (count : Nat) (selected : Fin (count + 1)) (index : Nat) (k : ℕ) : ProbComp Bool :=
  (simulateQ (indexedImpl (sampler setup.source k))
    (entryClient (Reader := Reader) setup codec checks ensureInit supplied decision work runtime count selected
      index)).run' ((∅ : (PqxdhCorrelatedExtractFamily.Message →ₒ Output).QueryCache), 0)

/-- The key-schedule distinguisher of the `k`-th fresh hidden entry: the `k`-th hybrid with that entry answered by the given 108 bytes. -/
noncomputable def entryDk (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes)
    (decision : X → Bool) (work : OracleComp (SourceSpec KemSK) X) (runtime : A)
    (count : Nat) (selected : Fin (count + 1)) (index : Nat) (k : ℕ) : PqxdhServerAuthKeySchedule.Distinguisher :=
  fun value => (simulateQ (indexedImpl (pin k value (sampler setup.source k)))
    (entryClient (Reader := Reader) setup codec checks ensureInit supplied decision work runtime count selected
      index)).run' ((∅ : (PqxdhCorrelatedExtractFamily.Message →ₒ Output).QueryCache), 0)

/-- Every hidden entry ideal: the factored root client with every hidden coordinate answered by 108 uniform bytes, consistently on repeated coordinates. -/
noncomputable def allIdealBranch (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes)
    (decision : X → Bool) (work : OracleComp (SourceSpec KemSK) X) (runtime : A)
    (count : Nat) (selected : Fin (count + 1)) (index : Nat) : ProbComp Bool :=
  (simulateQ lazyImpl (entryClient (Reader := Reader) setup codec checks ensureInit supplied decision work runtime
    count selected index)).run' (∅ : (PqxdhCorrelatedExtractFamily.Message →ₒ Output).QueryCache)

/-- The same game through the first-touch slot allocator in front of the persistent lazy table on `n` slots. -/
noncomputable def slotGame (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes)
    (decision : X → Bool) (work : OracleComp (SourceSpec KemSK) X) (runtime : A)
    (count : Nat) (selected : Fin (count + 1)) (index : Nat) (n : ℕ) : ProbComp Bool :=
  (simulateQ (slotImpl (D := PqxdhCorrelatedExtractFamily.Message) (tableService (n := n)))
    (entryClient (Reader := Reader) setup codec checks ensureInit supplied decision work runtime count selected
      index)).run' (emptyAlloc, PqxdhRecordLiftLazyTable.initial)

/-- Eager sampling of the `k`-th fresh entry, for output distributions. -/
theorem run_eager (draw : ℕ → ProbComp Output) (k : ℕ)
    (client : OracleComp (Spec PqxdhCorrelatedExtractFamily.Message Output) Bool)
    (state : IState PqxdhCorrelatedExtractFamily.Message Output) :
    𝒟[(simulateQ (indexedImpl draw) client).run' state] =
      𝒟[do let value ← draw k; (simulateQ (indexedImpl (pin k value draw)) client).run' state] := by
  apply evalDist_eq_of_evalSPMF_eq
  have project := congrArg (fun distribution => Prod.fst <$> distribution) (indexed_eager draw k client state)
  simp only [← evalSPMF_map] at project
  simpa [StateT.run'_eq, map_bind] using project

/-- The `k`-th hybrid is the key-schedule game with a uniform root on the `k`-th entry's distinguisher. -/
theorem hybrid_root (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes)
    (decision : X → Bool) (work : OracleComp (SourceSpec KemSK) X) (runtime : A)
    (count : Nat) (selected : Fin (count + 1)) (index : Nat) (k : ℕ) :
    𝒟[hybrid (Reader := Reader) setup codec checks ensureInit supplied decision work runtime count selected index k] =
      𝒟[rootHybrid setup.source (entryDk (Reader := Reader) setup codec checks ensureInit supplied decision work runtime
        count selected index k)] := by
  rw [hybrid, run_eager _ k]
  simp only [sampler, lt_irrefl, ite_false, bind_map_left]
  rfl

/-- The `k + 1`-st hybrid is the key-schedule game with 108 uniform bytes on the `k`-th entry's distinguisher. -/
theorem hybrid_uniform (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes)
    (decision : X → Bool) (work : OracleComp (SourceSpec KemSK) X) (runtime : A)
    (count : Nat) (selected : Fin (count + 1)) (index : Nat) (k : ℕ) :
    𝒟[hybrid (Reader := Reader) setup codec checks ensureInit supplied decision work runtime count selected index
        (k + 1)] =
      𝒟[PqxdhServerAuthKeySchedule.uniformGame (entryDk (Reader := Reader) setup codec checks ensureInit supplied
        decision work runtime count selected index k)] := by
  rw [hybrid, run_eager _ k]
  have pinned : ∀ value, pin k value (sampler setup.source (k + 1)) = pin k value (sampler setup.source k) :=
    fun value => pin_congr k value _ _ fun j other => by
      simp only [sampler]
      congr 1
      exact propext ⟨fun below => Nat.lt_of_le_of_ne (Nat.le_of_lt_succ below) other, fun below => Nat.lt_succ_of_lt below⟩
  simp only [sampler, Nat.lt_succ_self, ite_true, pinned]
  rfl

/-- One hop: replacing the `k`-th fresh entry's key-schedule output by 108 uniform bytes costs the four key-schedule advantages of G2 on that entry's distinguisher. -/
theorem hybrid_hop (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes)
    (decision : X → Bool) (work : OracleComp (SourceSpec KemSK) X) (runtime : A)
    (count : Nat) (selected : Fin (count + 1)) (index : Nat) (correct : SourceFullCorrect setup.source setup.hmac)
    (k : ℕ) :
    (hybrid (Reader := Reader) setup codec checks ensureInit supplied decision work runtime count selected index
        k).boolDistAdvantage
      (hybrid (Reader := Reader) setup codec checks ensureInit supplied decision work runtime count selected index
        (k + 1)) ≤
      keyScheduleBound setup.source setup.hmac (entryDk (Reader := Reader) setup codec checks ensureInit supplied
        decision work runtime count selected index k) := by
  rw [PqxdhRegistrationJointKemIdealKeys.advantage_left (hybrid_root setup codec checks ensureInit supplied decision
    work runtime count selected index k), advantage_right (hybrid_uniform setup codec checks ensureInit supplied
    decision work runtime count selected index k)]
  exact keySchedule_hop setup.source setup.hmac correct _

/-- The hybrids telescope: from the uniform-root world to the `q`-th hybrid, the advantage is at most the sum of the key-schedule bounds of the first `q` entries. -/
theorem hybrid_telescope (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes)
    (decision : X → Bool) (work : OracleComp (SourceSpec KemSK) X) (runtime : A)
    (count : Nat) (selected : Fin (count + 1)) (index : Nat) (correct : SourceFullCorrect setup.source setup.hmac)
    (q : ℕ) :
    (hybrid (Reader := Reader) setup codec checks ensureInit supplied decision work runtime count selected index
        0).boolDistAdvantage
      (hybrid (Reader := Reader) setup codec checks ensureInit supplied decision work runtime count selected index q) ≤
      ∑ k ∈ Finset.range q, keyScheduleBound setup.source setup.hmac (entryDk (Reader := Reader) setup codec checks
        ensureInit supplied decision work runtime count selected index k) := by
  induction q with
  | zero => simp [ProbComp.boolDistAdvantage_self]
  | succ q ih =>
      rw [Finset.sum_range_succ]
      exact (ProbComp.boolDistAdvantage_triangle _ _ _).trans
        (add_le_add ih (hybrid_hop setup codec checks ensureInit supplied decision work runtime count selected index
          correct q))

/-- The distinguisher of entry 0 is stage S3b's `entryD`. -/
theorem entryDk_zero (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes)
    (decision : X → Bool) (work : OracleComp (SourceSpec KemSK) X) (runtime : A)
    (count : Nat) (selected : Fin (count + 1)) (index : Nat) :
    entryDk (Reader := Reader) setup codec checks ensureInit supplied decision work runtime count selected index 0 =
      entryD (Reader := Reader) setup codec checks ensureInit supplied decision work runtime count selected index := by
  funext value
  have constant : sampler setup.source 0 = fun _ => fromRoot setup.source <$> ($ᵗ RootOutput) := by
    funext j
    simp [sampler]
  rw [entryDk, entryD, firstTable_pinned, constant]

/-- The uniform-root world of stage S2 has the output distribution of the 0-th hybrid. -/
theorem uniform_hybrid (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes)
    (decision : X → Bool) (work : OracleComp (SourceSpec KemSK) X) (runtime : A)
    (count : Nat) (selected : Fin (count + 1)) (index : Nat) :
    𝒟[PqxdhCorrelatedExpandHybrid.uniformGame (rootClient (Reader := Reader) setup codec checks ensureInit supplied
        decision work runtime count selected index)] =
      𝒟[hybrid (Reader := Reader) setup codec checks ensureInit supplied decision work runtime count selected index 0] := by
  rw [PqxdhRegistrationJointKemEntryFactor.uniformGame_entry, hybrid_root, entryDk_zero]

/-- With at least as many fresh-entry samplers as hidden reads, the hybrid is the game with every hidden entry ideal. -/
theorem hybrid_all (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes)
    (decision : X → Bool) (work : OracleComp (SourceSpec KemSK) X) (runtime : A)
    (count : Nat) (selected : Fin (count + 1)) (index : Nat) (q : ℕ)
    (bounded : (entryClient (Reader := Reader) setup codec checks ensureInit supplied decision work runtime count
      selected index).IsQueryBoundP (IsValue (D := PqxdhCorrelatedExtractFamily.Message) (R := Output)) q) :
    hybrid (Reader := Reader) setup codec checks ensureInit supplied decision work runtime count selected index q =
      allIdealBranch (Reader := Reader) setup codec checks ensureInit supplied decision work runtime count selected
        index := by
  have lazy := indexed_lazy (sampler setup.source q) q (fun j below => by simp [sampler, below]) _ q bounded
    ((∅ : (PqxdhCorrelatedExtractFamily.Message →ₒ Output).QueryCache), 0) (by simp)
  rw [hybrid, allIdealBranch, StateT.run'_eq, StateT.run'_eq, ← lazy, Functor.map_map]
  rfl

/-- With at least as many slots as hidden reads, the allocator and the persistent lazy table give the game with every hidden entry ideal. -/
theorem slotGame_all (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes)
    (decision : X → Bool) (work : OracleComp (SourceSpec KemSK) X) (runtime : A)
    (count : Nat) (selected : Fin (count + 1)) (index : Nat) (n : ℕ)
    (bounded : (entryClient (Reader := Reader) setup codec checks ensureInit supplied decision work runtime count
      selected index).IsQueryBoundP (IsValue (D := PqxdhCorrelatedExtractFamily.Message) (R := Output)) n) :
    slotGame (Reader := Reader) setup codec checks ensureInit supplied decision work runtime count selected index n =
      allIdealBranch (Reader := Reader) setup codec checks ensureInit supplied decision work runtime count selected
        index := by
  have lazy := slot_lazy (n := n) _ n bounded (emptyAlloc, PqxdhRecordLiftLazyTable.initial) slotGood_empty
    (by simp [emptyAlloc])
  rw [cacheOf_empty] at lazy
  rw [slotGame, allIdealBranch, StateT.run'_eq, StateT.run'_eq, ← lazy, Functor.map_map]
  rfl

/-- Naturality of the registration core in its slot service (the property CE-11 calls `CoreNatural`): the factored root client reads hidden-slot outputs only through the slot service behind the first-touch allocator, so a projection that carries one slot service to another under an invariant carries the whole run. -/
theorem entryClient_natural {S₁ S₂ : Type} (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes)
    (decision : X → Bool) (work : OracleComp (SourceSpec KemSK) X) (runtime : A)
    (count : Nat) (selected : Fin (count + 1)) (index : Nat) {n : ℕ}
    (service₁ : SlotService S₁ Output n) (service₂ : SlotService S₂ Output n) (inv : S₁ → Prop) (proj : S₁ → S₂)
    (step : ∀ slot state, inv state →
      Prod.map id proj <$> (service₁ slot).run state = (service₂ slot).run (proj state))
    (keeps : ∀ slot state, inv state → ∀ result ∈ support ((service₁ slot).run state), inv result.2)
    (alloc : Alloc PqxdhCorrelatedExtractFamily.Message n) (state : S₁) (holds : inv state) :
    (simulateQ (slotImpl service₁) (entryClient (Reader := Reader) setup codec checks ensureInit supplied decision work
        runtime count selected index)).run' (alloc, state) =
      (simulateQ (slotImpl service₂) (entryClient (Reader := Reader) setup codec checks ensureInit supplied decision work
        runtime count selected index)).run' (alloc, proj state) := by
  rw [StateT.run'_eq, StateT.run'_eq, ← (slot_natural service₁ service₂ inv proj step keeps _ alloc state holds).1,
    Functor.map_map]
  rfl

end Hybrid

/-! ### Stage S7 -/

section Main

variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response A X : Type}

/-- Stage S7 (T7 with every hidden entry ideal). The opaque KEM-ideal branch of theorem T6 and the game in which every hidden entry holds 108 uniform bytes are distinguishable with advantage at most `(qAccept + qFinish + qHmac) / 2^256` (route R1, stage S1c), plus the sum of `1 + qFinish` one-query HMAC-SHA-512 PRF advantages (stage S2), plus, for each of the first `1 + qFinish` fresh hidden entries, the four key-schedule advantages of G2 on that entry's distinguisher. Stage T would replace `1 + qFinish` by 2. The first term is valid only because the zero-key 192-byte Extract slice is modelled as a random oracle (R1), as in T7. -/
theorem opaqueBranch_allIdeal (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes)
    (decision : X → Bool) (work : OracleComp (SourceSpec KemSK) X) (runtime : A)
    (count : Nat) (selected : Fin (count + 1)) (index : Nat)
    (budget : PqxdhRegistrationJointRevealCosts.SourceKind → Nat)
    (certified : ∀ source, work.IsQueryBoundP
      (fun query => PqxdhRegistrationJointRevealCosts.sourceKind (KemSK := KemSK) query = source) (budget source))
    (correct : SourceFullCorrect setup.source setup.hmac) :
    (opaqueBranch (Reader := Reader) setup codec checks ensureInit supplied decision work runtime count selected index
        false).boolDistAdvantage
      (allIdealBranch (Reader := Reader) setup codec checks ensureInit supplied decision work runtime count selected
        index) ≤
      ((budget (.inl 3) + budget (.inl 5) + budget (.inl 6) : ℕ) : ℝ) / 2 ^ 256 +
        ∑ slot ∈ Finset.range (1 + budget (.inl 5)),
          (hmacPrfRealGame setup.hmac (indexedReduction setup.hmac (rootClient (Reader := Reader) setup codec checks
            ensureInit supplied decision work runtime count selected index) slot)).boolDistAdvantage
            (hmacPrfRandomGame (indexedReduction setup.hmac (rootClient (Reader := Reader) setup codec checks
              ensureInit supplied decision work runtime count selected index) slot)) +
        ∑ k ∈ Finset.range (1 + budget (.inl 5)), keyScheduleBound setup.source setup.hmac
          (entryDk (Reader := Reader) setup codec checks ensureInit supplied decision work runtime count selected index
            k) := by
  have tail : (PqxdhCorrelatedExpandHybrid.uniformGame (rootClient (Reader := Reader) setup codec checks ensureInit
      supplied decision work runtime count selected index)).boolDistAdvantage
      (allIdealBranch (Reader := Reader) setup codec checks ensureInit supplied decision work runtime count selected
        index) ≤
      ∑ k ∈ Finset.range (1 + budget (.inl 5)), keyScheduleBound setup.source setup.hmac
        (entryDk (Reader := Reader) setup codec checks ensureInit supplied decision work runtime count selected index
          k) := by
    rw [PqxdhRegistrationJointKemIdealKeys.advantage_left (uniform_hybrid setup codec checks ensureInit supplied
      decision work runtime count selected index), ← hybrid_all setup codec checks ensureInit supplied decision work
      runtime count selected index _ (entryClient_value setup codec checks ensureInit supplied decision work runtime
        count selected index budget certified)]
    exact hybrid_telescope setup codec checks ensureInit supplied decision work runtime count selected index correct _
  exact (ProbComp.boolDistAdvantage_triangle _ _ _).trans (add_le_add
    (PqxdhRegistrationJointKemRootExpand.opaqueBranch_uniform setup codec checks ensureInit supplied decision work
      runtime count selected index budget certified) tail)

/-- Stage S7 through the first-touch allocator and the persistent lazy table on `1 + qFinish` slots: the bound of `opaqueBranch_allIdeal`. -/
theorem opaqueBranch_slots (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes)
    (decision : X → Bool) (work : OracleComp (SourceSpec KemSK) X) (runtime : A)
    (count : Nat) (selected : Fin (count + 1)) (index : Nat)
    (budget : PqxdhRegistrationJointRevealCosts.SourceKind → Nat)
    (certified : ∀ source, work.IsQueryBoundP
      (fun query => PqxdhRegistrationJointRevealCosts.sourceKind (KemSK := KemSK) query = source) (budget source))
    (correct : SourceFullCorrect setup.source setup.hmac) :
    (opaqueBranch (Reader := Reader) setup codec checks ensureInit supplied decision work runtime count selected index
        false).boolDistAdvantage
      (slotGame (Reader := Reader) setup codec checks ensureInit supplied decision work runtime count selected index
        (1 + budget (.inl 5))) ≤
      ((budget (.inl 3) + budget (.inl 5) + budget (.inl 6) : ℕ) : ℝ) / 2 ^ 256 +
        ∑ slot ∈ Finset.range (1 + budget (.inl 5)),
          (hmacPrfRealGame setup.hmac (indexedReduction setup.hmac (rootClient (Reader := Reader) setup codec checks
            ensureInit supplied decision work runtime count selected index) slot)).boolDistAdvantage
            (hmacPrfRandomGame (indexedReduction setup.hmac (rootClient (Reader := Reader) setup codec checks
              ensureInit supplied decision work runtime count selected index) slot)) +
        ∑ k ∈ Finset.range (1 + budget (.inl 5)), keyScheduleBound setup.source setup.hmac
          (entryDk (Reader := Reader) setup codec checks ensureInit supplied decision work runtime count selected index
            k) := by
  rw [slotGame_all setup codec checks ensureInit supplied decision work runtime count selected index _
    (entryClient_value setup codec checks ensureInit supplied decision work runtime count selected index budget
      certified)]
  exact opaqueBranch_allIdeal setup codec checks ensureInit supplied decision work runtime count selected index budget
    certified correct

end Main

end BeaconcryptCore.Computational.PqxdhRegistrationJointKemSecondEntry

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemSecondEntry.keySchedule_hop' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemSecondEntry.keySchedule_hop

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemSecondEntry.advantage_right' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemSecondEntry.advantage_right

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemSecondEntry.publicLocalV_value' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemSecondEntry.publicLocalV_value

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemSecondEntry.entryClient_value' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemSecondEntry.entryClient_value

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemSecondEntry.run_eager' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemSecondEntry.run_eager

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemSecondEntry.hybrid_root' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemSecondEntry.hybrid_root

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemSecondEntry.hybrid_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemSecondEntry.hybrid_uniform

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemSecondEntry.hybrid_hop' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemSecondEntry.hybrid_hop

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemSecondEntry.hybrid_telescope' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemSecondEntry.hybrid_telescope

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemSecondEntry.entryDk_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemSecondEntry.entryDk_zero

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemSecondEntry.uniform_hybrid' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemSecondEntry.uniform_hybrid

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemSecondEntry.hybrid_all' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemSecondEntry.hybrid_all

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemSecondEntry.slotGame_all' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemSecondEntry.slotGame_all

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemSecondEntry.entryClient_natural' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemSecondEntry.entryClient_natural

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemSecondEntry.opaqueBranch_allIdeal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemSecondEntry.opaqueBranch_allIdeal

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemSecondEntry.opaqueBranch_slots' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemSecondEntry.opaqueBranch_slots
