import BeaconcryptCore.Computational.PqxdhRegistrationJointKemRootCostsClient
import BeaconcryptCore.Computational.PqxdhRegistrationJointBeaconFinishOnce

/-!
# The random draws of the key-schedule distinguishers (item 2, stage S8)

The key-schedule terms of theorem T7 (`PqxdhRegistrationJointKemSecondEntry.keyScheduleBound`) are G2 games on the distinguishers `PqxdhRegistrationJointKemEntryFactor.entryD` (entry 0) and `PqxdhRegistrationJointKemSecondEntry.entryDk k` (stage S7). Each runs the factored root client of stage S3b under a table of its hidden entries: `entryD` answers the first fresh hidden coordinate by the given 108 bytes and every later one by the key-schedule output of a fresh uniform 32-byte root; `entryDk k` answers the `k`-th by the given bytes, the earlier ones by 108 uniform bytes and the later ones as `entryD`.

- `firstTable_step` and `indexedTable_step`: a coin of the table costs one draw, a hidden read at most the cost of its sampler (32 for a fresh root, 108 for a fresh ideal entry, nothing on a hit or at the given entry);
- `entryD_total` and `entryDk_total`: with the coin bill `rootBill` of the factored root client (`entryClient_coins`) and stage T's two hidden reads (`PqxdhRegistrationJointBeaconFinishOnce.entryClient_two`), every run of `entryD` draws at most `rootBill + 64` and every run of `entryDk k` at most `rootBill + 216`.

These are resource bounds; they make no security claim.
-/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc

set_option autoImplicit false
set_option maxRecDepth 100000

namespace BeaconcryptCore.Computational.PqxdhRegistrationJointKemRootCosts

open PqxdhKemIndCca PqxdhInitializerSecrecy PqxdhServerAuthExperiment PqxdhJointIdentity
open PqxdhServerAuthSourceCosts (KemCaps KemBound)
open PqxdhRegistrationJointRevealCosts (SourceKind sourceKind)
open PqxdhRegistrationJointKemSecondEntry (IsValue indexedImpl pin sampler entryDk)
open PqxdhJointKdfGame (FixedHkdfSha512NoSaltSource)

/-! ### The hidden-entry tables -/

section Tables

variable {D R : Type} [DecidableEq D]

/-- A total bound in the unit weight is a total query bound. -/
theorem total_of_wBound {ι' α : Type} {spec : OracleSpec.{0, 0} ι'} {work : OracleComp spec α} {n : ℕ}
    (bounded : WBound work (fun _ => 1) n) : work.IsTotalQueryBound n :=
  (isQueryBoundP_true_iff work n).mp (isQueryBoundP_of_wBound (fun _ => True) (fun _ _ => le_rfl) bounded)

/-- The tables' interface: one per coin, `cost` per hidden read. -/
def wTable2 (cost : ℕ) : (PqxdhRegistrationJointKemSecondEntry.Spec D R).Domain → ℕ
  | .inl _ => 1
  | .inr _ => cost

/-- A step of the first-value table costs one draw per coin and at most the sampler's cost per hidden read. -/
theorem firstTable_step (value : R) (sample : ProbComp R) (cost : ℕ) (bounded : sample.IsTotalQueryBound cost)
    (query : (PqxdhRegistrationJointKemSecondEntry.Spec D R).Domain) (state : PqxdhRootFirstEntry.State D R) :
    ((PqxdhRegistrationJointKemEntryFactor.firstTable value sample query).run state).IsTotalQueryBound
      (wTable2 cost query) := by
  rcases query with coin | point
  · change OracleComp.IsTotalQueryBound (((unifSpec.query coin : ProbComp (unifSpec.Range coin)) >>= fun answer =>
      pure (answer, state))) 1
    exact ⟨Nat.zero_lt_succ 0, fun _ => True.intro⟩
  · obtain ⟨cache, first⟩ := state
    change (match cache point with
      | some answer => Pure.pure (answer, (cache, first))
      | none => match first with
        | none => Pure.pure (value, (cache.cacheQuery point value, some point))
        | some first => do
            let answer ← sample
            Pure.pure (answer, (cache.cacheQuery point answer, some first)) : ProbComp _).IsTotalQueryBound cost
    rcases cache point with _ | answer
    · rcases first with _ | first
      · trivial
      · refine (isTotalQueryBound_bind (n₂ := 0) bounded fun answer => ?_).mono (by omega)
        trivial
    · trivial

/-- A step of the indexed table costs one draw per coin and at most `cost` per hidden read when every sampler of the family costs at most `cost`. -/
theorem indexedTable_step (family : ℕ → ProbComp R) (cost : ℕ) (bounded : ∀ j, (family j).IsTotalQueryBound cost)
    (query : (PqxdhRegistrationJointKemSecondEntry.Spec D R).Domain)
    (state : PqxdhRegistrationJointKemSecondEntry.IState D R) :
    ((indexedImpl family query).run state).IsTotalQueryBound (wTable2 cost query) := by
  rcases query with coin | point
  · change OracleComp.IsTotalQueryBound (((unifSpec.query coin : ProbComp (unifSpec.Range coin)) >>= fun answer =>
      pure (answer, state))) 1
    exact ⟨Nat.zero_lt_succ 0, fun _ => True.intro⟩
  · obtain ⟨cache, fresh⟩ := state
    change (match cache point with
      | some answer => Pure.pure (answer, (cache, fresh))
      | none => do
          let answer ← family fresh
          Pure.pure (answer, (cache.cacheQuery point answer, fresh + 1)) : ProbComp _).IsTotalQueryBound cost
    rcases cache point with _ | answer
    · refine (isTotalQueryBound_bind (n₂ := 0) (bounded fresh) fun answer => ?_).mono (by omega)
      trivial
    · trivial

omit [DecidableEq D] in
/-- A client with at most `m` hidden reads, run under a table whose hidden reads cost at most `cost`, draws at most its coins and `cost * m`. -/
theorem table_total {α σ : Type} (handler : QueryImpl (PqxdhRegistrationJointKemSecondEntry.Spec D R) (StateT σ ProbComp))
    (cost : ℕ) (step : ∀ query state, ((handler query).run state).IsTotalQueryBound (wTable2 cost query))
    (client : OracleComp (PqxdhRegistrationJointKemSecondEntry.Spec D R) α) (n m : ℕ)
    (coins : WBound client (wTable2 0) n) (reads : client.IsQueryBoundP (IsValue (D := D) (R := R)) m) (state : σ) :
    ((simulateQ handler client).run' state).IsTotalQueryBound (n + cost * m) := by
  have both := wBound_add coins (wBound_of_isQueryBoundP _ cost reads)
  have weighted : WBound client (wTable2 cost) (n + cost * m) := by
    refine wBound_weight_mono (fun query => ?_) both
    rcases query with _ | _ <;> simp [wTable2, IsValue]
  rw [StateT.run'_eq, IsTotalQueryBound, isQueryBound_map_iff]
  exact total_of_wBound (wBound_run handler (wTable2 cost) (fun _ => 1)
    (fun query current => wBound_of_total (step query current)) weighted state)

end Tables

/-! ### The key-schedule distinguishers -/

section Distinguishers

open PqxdhRegistrationJointKemCommands (SourceSpec)

variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response A X : Type}

/-- A fresh root's key-schedule output costs its 32 bytes. -/
theorem rootSample_total (source : FixedHkdfSha512NoSaltSource) :
    (PqxdhServerAuthKeySchedule.fromRoot source <$> ($ᵗ PqxdhSecretInputKdf.RootOutput)).IsTotalQueryBound 32 := by
  rw [IsTotalQueryBound, isQueryBound_map_iff]
  exact CtxComputationalSecurity.uniformFixedBytes_isTotalQueryBound 32

/-- Stage S8, the distinguisher of entry 0: every run draws at most `rootBill + 64`. -/
theorem entryD_total (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (caps : KemCaps) (bounded : KemBound setup caps) (ensureInit : StateT A ProbComp Bool)
    (qInit : Nat) (initBound : ∀ runtime, (ensureInit.run runtime).IsTotalQueryBound qInit)
    (supplied : Option Pqxdh.Bytes) (decision : X → Bool) (work : OracleComp (SourceSpec KemSK) X)
    (budget : SourceKind → ℕ)
    (certified : ∀ source, work.IsQueryBoundP (fun query => sourceKind (KemSK := KemSK) query = source) (budget source))
    (runtime : A) (count : Nat) (selected : Fin (count + 1)) (index : Nat) (value : PqxdhServerAuthKeySchedule.Output) :
    (PqxdhRegistrationJointKemEntryFactor.entryD (Reader := Reader) setup codec checks ensureInit supplied decision
      work runtime count selected index value).IsTotalQueryBound (rootBill caps qInit supplied count budget + 64) := by
  have coins := entryClient_coins (Reader := Reader) setup codec checks caps bounded ensureInit qInit initBound supplied
    decision work budget certified runtime count selected index
  have weighted : WBound (PqxdhRegistrationJointKemEntryFactor.entryClient (Reader := Reader) setup codec checks
      ensureInit supplied decision work runtime count selected index) (wTable2 0)
      (rootBill caps qInit supplied count budget) :=
    wBound_weight_mono (fun query => by rcases query with _ | _ <;> exact le_rfl) coins
  exact table_total (PqxdhRegistrationJointKemEntryFactor.firstTable value
      (PqxdhServerAuthKeySchedule.fromRoot setup.source <$> ($ᵗ PqxdhSecretInputKdf.RootOutput))) 32
    (firstTable_step value _ 32 (rootSample_total setup.source)) _ _ 2 weighted
    (PqxdhRegistrationJointBeaconFinishOnce.entryClient_two setup codec checks ensureInit supplied decision work
      runtime count selected index) (∅, none)

/-- Every sampler of the `k`-th hybrid with one pinned value costs at most 108. -/
theorem pinned_total (source : FixedHkdfSha512NoSaltSource) (k : ℕ) (value : PqxdhServerAuthKeySchedule.Output)
    (j : ℕ) : (pin k value (sampler source k) j).IsTotalQueryBound 108 := by
  unfold pin sampler
  split
  · trivial
  · split
    · exact PqxdhServerAuthEntryFactor.entry_output_uniform
    · exact (rootSample_total source).mono (by omega)

/-- Stage S8, the distinguishers of stage S7: every run of `entryDk k` draws at most `rootBill + 216`. -/
theorem entryDk_total (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (caps : KemCaps) (bounded : KemBound setup caps) (ensureInit : StateT A ProbComp Bool)
    (qInit : Nat) (initBound : ∀ runtime, (ensureInit.run runtime).IsTotalQueryBound qInit)
    (supplied : Option Pqxdh.Bytes) (decision : X → Bool) (work : OracleComp (SourceSpec KemSK) X)
    (budget : SourceKind → ℕ)
    (certified : ∀ source, work.IsQueryBoundP (fun query => sourceKind (KemSK := KemSK) query = source) (budget source))
    (runtime : A) (count : Nat) (selected : Fin (count + 1)) (index : Nat) (k : ℕ)
    (value : PqxdhServerAuthKeySchedule.Output) :
    (entryDk (Reader := Reader) setup codec checks ensureInit supplied decision work runtime count selected index k
      value).IsTotalQueryBound (rootBill caps qInit supplied count budget + 216) := by
  have coins := entryClient_coins (Reader := Reader) setup codec checks caps bounded ensureInit qInit initBound supplied
    decision work budget certified runtime count selected index
  have weighted : WBound (PqxdhRegistrationJointKemEntryFactor.entryClient (Reader := Reader) setup codec checks
      ensureInit supplied decision work runtime count selected index) (wTable2 0)
      (rootBill caps qInit supplied count budget) :=
    wBound_weight_mono (fun query => by rcases query with _ | _ <;> exact le_rfl) coins
  exact table_total (indexedImpl (pin k value (sampler setup.source k))) 108
    (indexedTable_step _ 108 (pinned_total setup.source k value)) _ _ 2 weighted
    (PqxdhRegistrationJointBeaconFinishOnce.entryClient_two setup codec checks ensureInit supplied decision work
      runtime count selected index) (∅, 0)

end Distinguishers

end BeaconcryptCore.Computational.PqxdhRegistrationJointKemRootCosts

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemRootCosts.total_of_wBound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemRootCosts.total_of_wBound

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemRootCosts.firstTable_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemRootCosts.firstTable_step

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemRootCosts.indexedTable_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemRootCosts.indexedTable_step

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemRootCosts.table_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemRootCosts.table_total

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemRootCosts.rootSample_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemRootCosts.rootSample_total

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemRootCosts.entryD_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemRootCosts.entryD_total

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemRootCosts.pinned_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemRootCosts.pinned_total

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemRootCosts.entryDk_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemRootCosts.entryDk_total
