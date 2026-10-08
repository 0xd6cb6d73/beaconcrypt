import BeaconcryptCore.Computational.PqxdhRegistrationJointKemRomSplitPost

/-!
# The random-oracle split of the KEM-ideal branch (item 2, stage S1c)

This module completes stage S1c of the item 2 plan. Stage S1b (`PqxdhRegistrationJointKemPostSkeleton.opaqueBranch_shared`) states the opaque KEM-ideal branch (H0 of the plan) as G1's shared world: the KEM candidate is G1's secret, the 32-byte suffix of every hidden read, and every other read of the shared zero-key 192-byte Extract table, including the cache keys written before the cut, goes to the same table. The main theorem `opaqueBranch_split` instantiates G1 (`PqxdhExtractRomHiddenSuffix.hidden_suffix_bound`) at coefficient one:

```text
(opaqueBranch … false).boolDistAdvantage (splitGame (sharedStart …) (sharedClient …)) ≤ (qAccept + qFinish + qHmac) / 2^256
```

where `qAccept`, `qFinish` and `qHmac` are the source budgets of raw accepts, Beacon finishes and public HMAC requests (`tableBudget`). G1's split world `splitGame` (H1 of the plan) answers the hidden reads from a separate lazily sampled table keyed by the 128-byte coordinates alone and draws no secret: the candidate is no longer a suffix of any key of the shared Extract-table cache, which now holds only the direct reads. This is the step that the semantic review of increment 1 assigned to S1c (plan section 19).

This step is valid only because the zero-key 192-byte Extract slice is modelled as a random oracle (route R1, owner decision 2, extended to this line). For the real Extract function, outputs at inputs that share one secret 32-byte suffix are not known to be independent; R1 gives the hidden entries at distinct coordinates their mutual independence in both worlds, and the split removes their dependence on the secret and their reachability by direct reads at the cost of the guessing term.

The budget split (the plan's cut-split of `certified`): for every outcome of the prefix, the keys of the table cache at the cut (`keys`, at most `c` by `PqxdhRegistrationJointKemRomSplit.sharedStart_fits`) and the direct reads after the cut (at most one for the Server's resumption, which is the selected raw accept, plus one per table request of the continuation, at most `Q - c - 1`, by `sharedClient_direct`) add up to at most `Q`. No assumption is added: the bound holds for every adversary and every setup, under the source budget `certified` of theorem T5.
-/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement

set_option autoImplicit false
set_option maxRecDepth 100000

namespace BeaconcryptCore.Computational.PqxdhRegistrationJointKemRomSplit

open PqxdhKemIndCca PqxdhInitializerSecrecy PqxdhServerAuthExperiment PqxdhJointIdentity
open PqxdhSecretInputKdf (HmacBlock HmacOracle RootOutput)
open PqxdhRegistrationJointKemPostSkeleton (sharedStart sharedClient cacheOf)
open PqxdhRegistrationJointKemCommands (SourceSpec)
open PqxdhRegistrationJointKemRawOpaque (OpaqueContext opaqueBranch)
open PqxdhExtractRomHiddenSuffix (sharedGame splitGame)

/-! ### The source budget of table requests -/

section Budget

variable {KemSK X : Type}

/-- The source budget of the requests that read the shared table: raw accepts (kind 3), Beacon finishes (kind 5) and public HMAC (kind 6). -/
def tableBudget (budget : PqxdhRegistrationJointRevealCosts.SourceKind → Nat) : Nat :=
  budget (.inl 3) + budget (.inl 5) + budget (.inl 6)

theorem tableKind_source (query : (SourceSpec KemSK).Domain) (table : TableKind query) :
    (PqxdhRegistrationJointRevealCosts.sourceKind query = .inl 3 ∨
      PqxdhRegistrationJointRevealCosts.sourceKind query = .inl 5) ∨
      PqxdhRegistrationJointRevealCosts.sourceKind query = .inl 6 := by
  rcases query with (coin | request) | read
  · exact table.elim
  · cases request <;> first
      | exact table.elim
      | simp [PqxdhRegistrationJointRevealCosts.sourceKind, PqxdhRegistrationSchedule.sourceKind]
  · exact table.elim

/-- The source budget bounds the table requests of the source program. -/
theorem certified_table (work : OracleComp (SourceSpec KemSK) X)
    (budget : PqxdhRegistrationJointRevealCosts.SourceKind → Nat)
    (certified : ∀ source, work.IsQueryBoundP
      (fun query => PqxdhRegistrationJointRevealCosts.sourceKind (KemSK := KemSK) query = source) (budget source)) :
    work.IsQueryBoundP (TableKind (KemSK := KemSK)) (tableBudget budget) :=
  IsQueryBoundP.of_imp tableKind_source
    (isQueryBoundP_or work (isQueryBoundP_or work (certified (.inl 3)) (certified (.inl 5))) (certified (.inl 6)))

end Budget

/-! ### G1 for the KEM-ideal branch -/

section Split

variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response A X : Type}

/-- A finite set of byte strings covering the keys of a table cache with finitely many keys. -/
noncomputable def keys {C : Type} (start : HmacOracle.QueryCache × C) : Finset Pqxdh.Bytes := by
  classical
  exact if finite : (cacheKeys start.1).Finite then finite.toFinset else ∅

theorem keys_cover {C : Type} (start : HmacOracle.QueryCache × C) (finite : (cacheKeys start.1).Finite)
    (point : Pqxdh.Bytes) (present : start.1 point ≠ none) : point ∈ keys start := by
  unfold keys
  rw [dite_eq_left finite, Set.Finite.mem_toFinset]
  exact present

theorem keys_card {C : Type} (start : HmacOracle.QueryCache × C) (finite : (cacheKeys start.1).Finite) (c : ℕ)
    (count : (cacheKeys start.1).encard ≤ c) : (keys start).card ≤ c := by
  unfold keys
  rw [dite_eq_left finite]
  have same := Set.encard_coe_eq_coe_finsetCard finite.toFinset
  rw [Set.Finite.coe_toFinset] at same
  exact_mod_cast (same ▸ count)

/-- The client of an inactive prechallenge context makes no direct read. -/
theorem sharedClient_inactive (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (decision : X → Bool) (count : Nat) (selected : Fin (count + 1))
    (context : (MlKem768PublicKey × KemSK) × OpaqueContext Reader KemSK A X count × MlKem768Ciphertext)
    (inactive : ∀ created others raw value ephemeral consumed native owners next state runtime,
      context.2.1 ≠ .ready created others (some (.pending raw value ephemeral consumed native owners next)) state runtime) :
    (sharedClient setup codec checks decision count selected context).IsQueryBoundP
      PqxdhExtractRomHiddenSuffix.IsDirect 0 := by
  obtain ⟨chosen, context, challenge⟩ := context
  rcases context with state | ⟨created, others, _ | (outcome | ⟨raw, value, ephemeral, consumed, native, owners, next⟩),
    state, runtime⟩
  · trivial
  · trivial
  · trivial
  · exact absurd rfl (inactive created others raw value ephemeral consumed native owners next state runtime)

/-- Stage S1c, the G1 instance: the shared world of stage S1b and G1's split world are distinguishable with advantage at most the source's table budget over `2^256` (coefficient one). -/
theorem shared_split (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes)
    (decision : X → Bool) (work : OracleComp (SourceSpec KemSK) X) (runtime : A)
    (count : Nat) (selected : Fin (count + 1)) (index : Nat)
    (budget : PqxdhRegistrationJointRevealCosts.SourceKind → Nat)
    (certified : ∀ source, work.IsQueryBoundP
      (fun query => PqxdhRegistrationJointRevealCosts.sourceKind (KemSK := KemSK) query = source) (budget source)) :
    (sharedGame (sharedStart (Reader := Reader) setup codec checks ensureInit supplied decision work runtime count
        selected index) (sharedClient setup codec checks decision count selected)).boolDistAdvantage
      (splitGame (sharedStart (Reader := Reader) setup codec checks ensureInit supplied decision work runtime count
        selected index) (sharedClient setup codec checks decision count selected)) ≤
      (tableBudget budget : ℝ) / 2 ^ 256 := by
  have fits := sharedStart_fits (Reader := Reader) setup codec checks ensureInit supplied decision work runtime count
    selected index (tableBudget budget) (certified_table work budget certified)
  have finite : ∀ start ∈ support (sharedStart (Reader := Reader) setup codec checks ensureInit supplied decision work
      runtime count selected index), (cacheKeys start.1).Finite ∧ ∃ c : ℕ, (cacheKeys start.1).encard ≤ c ∧
        c ≤ tableBudget budget ∧ (sharedClient setup codec checks decision count selected start.2).IsQueryBoundP
          PqxdhExtractRomHiddenSuffix.IsDirect (tableBudget budget - c) := by
    intro start reached
    obtain ⟨cache, fit⟩ := fits start reached
    obtain ⟨table, chosen, context, challenge⟩ := start
    dsimp only at cache fit ⊢
    subst cache
    have inactive : ∀ context : OpaqueContext Reader KemSK A X count,
        (∀ created others raw value ephemeral consumed native owners next state runtime,
          context ≠ .ready created others (some (.pending raw value ephemeral consumed native owners next)) state
            runtime) →
        cacheOf context = ∅ →
        (cacheKeys (cacheOf context)).Finite ∧ ∃ c : ℕ, (cacheKeys (cacheOf context)).encard ≤ c ∧
          c ≤ tableBudget budget ∧ (sharedClient setup codec checks decision count selected
            (chosen, context, challenge)).IsQueryBoundP PqxdhExtractRomHiddenSuffix.IsDirect (tableBudget budget - c) := by
      intro context other empty
      rw [empty, cacheKeys_empty]
      exact ⟨Set.finite_empty, 0, by simp, Nat.zero_le _,
        (sharedClient_inactive setup codec checks decision count selected _ other).mono (Nat.zero_le _)⟩
    rcases context with state | ⟨created, others, _ | (outcome | ⟨raw, value, ephemeral, consumed, native, owners,
      next⟩), state, runtime⟩
    · exact inactive _ (fun _ _ _ _ _ _ _ _ _ _ _ same => by cases same) rfl
    · exact inactive _ (fun _ _ _ _ _ _ _ _ _ _ _ same => by cases same) rfl
    · exact inactive _ (fun _ _ _ _ _ _ _ _ _ _ _ same => by cases same) rfl
    obtain ⟨c, keysCount, room, remaining⟩ := fit
    refine ⟨Set.finite_of_encard_le_coe keysCount, c, keysCount, by omega, ?_⟩
    refine (sharedClient_direct setup codec checks decision count selected
      (chosen, .ready created others (some (.pending raw value ephemeral consumed native owners next)) state runtime,
        challenge) (tableBudget budget - c - 1) remaining).mono (by omega)
  refine PqxdhExtractRomHiddenSuffix.hidden_suffix_bound _ _ (tableBudget budget) keys
    (fun start => tableBudget budget - (keys start).card) ?_ ?_ ?_
  · intro start reached point present
    exact keys_cover start (finite start reached).1 point present
  · intro start reached
    obtain ⟨fin, c, keysCount, room, direct⟩ := finite start reached
    exact direct.mono (Nat.sub_le_sub_left (keys_card start fin c keysCount) _)
  · intro start reached
    obtain ⟨fin, c, keysCount, room, _⟩ := finite start reached
    have := keys_card start fin c keysCount
    omega

/-- Stage S1c. The opaque KEM-ideal branch of theorem T6 (H0, equal to H0b by stages S0a and S0b) and G1's split world (H1) on the same prefix and client are distinguishable with advantage at most `(qAccept + qFinish + qHmac) / 2^256`, the source's table budget over `2^256` (coefficient one). In the split world the hidden entries are keyed by their 128-byte coordinates alone, no secret is drawn, and the KEM candidate is no longer the suffix of any key of the shared Extract-table cache. This step is valid only because the zero-key 192-byte Extract slice is modelled as a random oracle (route R1): R1 gives the hidden entries at distinct coordinates their mutual independence in both worlds; without that idealization, treating Extract outputs at inputs that share one secret suffix as independent would be the forbidden decorrelation. -/
theorem opaqueBranch_split (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes)
    (decision : X → Bool) (work : OracleComp (SourceSpec KemSK) X) (runtime : A)
    (count : Nat) (selected : Fin (count + 1)) (index : Nat)
    (budget : PqxdhRegistrationJointRevealCosts.SourceKind → Nat)
    (certified : ∀ source, work.IsQueryBoundP
      (fun query => PqxdhRegistrationJointRevealCosts.sourceKind (KemSK := KemSK) query = source) (budget source)) :
    (opaqueBranch (Reader := Reader) setup codec checks ensureInit supplied decision work runtime count selected index
        false).boolDistAdvantage
      (splitGame (sharedStart (Reader := Reader) setup codec checks ensureInit supplied decision work runtime count
        selected index) (sharedClient setup codec checks decision count selected)) ≤
      ((budget (.inl 3) + budget (.inl 5) + budget (.inl 6) : ℕ) : ℝ) / 2 ^ 256 := by
  rw [PqxdhRegistrationJointKemPostSkeleton.opaqueBranch_shared]
  exact shared_split setup codec checks ensureInit supplied decision work runtime count selected index budget certified

end Split

end BeaconcryptCore.Computational.PqxdhRegistrationJointKemRomSplit

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemRomSplit.tableKind_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemRomSplit.tableKind_source

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemRomSplit.certified_table' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemRomSplit.certified_table

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemRomSplit.keys_cover' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemRomSplit.keys_cover

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemRomSplit.keys_card' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemRomSplit.keys_card

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemRomSplit.sharedClient_inactive' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemRomSplit.sharedClient_inactive

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemRomSplit.shared_split' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemRomSplit.shared_split

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemRomSplit.opaqueBranch_split' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemRomSplit.opaqueBranch_split
