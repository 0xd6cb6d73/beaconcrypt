import BeaconcryptCore.Computational.PqxdhRegistrationJointKemRootExpandCount

/-!
# The root Expand of the KEM-ideal branch (item 2, stage S2)

This module completes stage S2 of the item 2 plan: the hop from G1's split world (H1 of the plan, after stage S1c) to the uniform-root world `PqxdhCorrelatedExpandHybrid.uniformGame rootClient` (H2), for the KEM-ideal branch.

- `splitGame_expanded` (in `PqxdhRegistrationJointKemRootExpandLocal`) states H1 as the cached-root game with real Expand on the root client `rootClient`, which holds the prefix, the CCA evaluation, the native game state and the public table inside it.
- `rootClient_root` (in `PqxdhRegistrationJointKemRootExpandCount`) bounds the root requests of `rootClient` by `1 + qFinish`.
- `rootClient_uniform` applies `PqxdhCorrelatedExpandHybrid.expanded_uniform_bound`: replacing every root (the real Expand of a fresh uniform hidden PRK) by a fresh uniform root, consistently on repeated coordinates, costs at most the sum over `index < 1 + qFinish` of the HMAC-SHA-512 PRF advantages of `PqxdhCorrelatedExpandHybrid.indexedReduction setup.hmac rootClient index`. Each reduction makes one challenge query.

`split_uniform` is the hop H1 to H2, and `opaqueBranch_uniform` composes it with stage S1c (`PqxdhRegistrationJointKemRomSplit.opaqueBranch_split`): the opaque KEM-ideal branch of theorem T6 and the uniform-root world are distinguishable with advantage at most `(qAccept + qFinish + qHmac) / 2^256` plus the PRF sum. The PRF step is standard: after S1c each hidden PRK is a fresh uniform block that only its Expand reads, so Expand is HMAC under a uniform secret key. The reductions use `rootClient`, which has no candidate argument and is defined from the arguments of `splitGame`, which draws no candidate (`splitGame_root`). No assumption is added beyond the source budget `certified` of theorem T5; the PRF advantages are explicit terms of the bound.
-/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement

set_option autoImplicit false
set_option maxRecDepth 100000

namespace BeaconcryptCore.Computational.PqxdhRegistrationJointKemRootExpand

open PqxdhKemIndCca PqxdhInitializerSecrecy PqxdhServerAuthExperiment PqxdhJointIdentity
open PqxdhSecretInputKdf (hmacPrfRealGame hmacPrfRandomGame)
open PqxdhCorrelatedExpandHybrid (uniformGame indexedReduction)
open PqxdhRegistrationJointKemPostSkeleton (sharedStart sharedClient)
open PqxdhRegistrationJointKemCommands (SourceSpec)
open PqxdhRegistrationJointKemRawOpaque (opaqueBranch)
open PqxdhExtractRomHiddenSuffix (splitGame)

variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response A X : Type}

/-- The cached-root game with real Expand on the root client and the uniform-root world are distinguishable with advantage at most the sum of `1 + qFinish` one-query HMAC PRF advantages. -/
theorem rootClient_uniform (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes)
    (decision : X → Bool) (work : OracleComp (SourceSpec KemSK) X) (runtime : A)
    (count : Nat) (selected : Fin (count + 1)) (index : Nat)
    (budget : PqxdhRegistrationJointRevealCosts.SourceKind → Nat)
    (certified : ∀ source, work.IsQueryBoundP
      (fun query => PqxdhRegistrationJointRevealCosts.sourceKind (KemSK := KemSK) query = source) (budget source)) :
    (PqxdhCorrelatedExpand.expandedGame setup.hmac (rootClient (Reader := Reader) setup codec checks ensureInit
        supplied decision work runtime count selected index)).boolDistance
      (uniformGame (rootClient (Reader := Reader) setup codec checks ensureInit supplied decision work runtime count
        selected index)) ≤
      ∑ slot ∈ Finset.range (1 + budget (.inl 5)),
        (hmacPrfRealGame setup.hmac (indexedReduction setup.hmac (rootClient (Reader := Reader) setup codec checks
          ensureInit supplied decision work runtime count selected index) slot)).boolDistance
          (hmacPrfRandomGame (indexedReduction setup.hmac (rootClient (Reader := Reader) setup codec checks ensureInit
            supplied decision work runtime count selected index) slot)) :=
  PqxdhCorrelatedExpandHybrid.expanded_uniform_bound setup.hmac _ _
    (rootClient_root setup codec checks ensureInit supplied decision work runtime count selected index budget certified)

/-- Stage S2. G1's split world of the KEM-ideal branch (H1) and the uniform-root world on the root client (H2) are distinguishable with advantage at most the sum of `1 + qFinish` one-query HMAC PRF advantages. -/
theorem split_uniform (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes)
    (decision : X → Bool) (work : OracleComp (SourceSpec KemSK) X) (runtime : A)
    (count : Nat) (selected : Fin (count + 1)) (index : Nat)
    (budget : PqxdhRegistrationJointRevealCosts.SourceKind → Nat)
    (certified : ∀ source, work.IsQueryBoundP
      (fun query => PqxdhRegistrationJointRevealCosts.sourceKind (KemSK := KemSK) query = source) (budget source)) :
    (splitGame (sharedStart (Reader := Reader) setup codec checks ensureInit supplied decision work runtime count
        selected index) (sharedClient setup codec checks decision count selected)).boolDistance
      (uniformGame (rootClient (Reader := Reader) setup codec checks ensureInit supplied decision work runtime count
        selected index)) ≤
      ∑ slot ∈ Finset.range (1 + budget (.inl 5)),
        (hmacPrfRealGame setup.hmac (indexedReduction setup.hmac (rootClient (Reader := Reader) setup codec checks
          ensureInit supplied decision work runtime count selected index) slot)).boolDistance
          (hmacPrfRandomGame (indexedReduction setup.hmac (rootClient (Reader := Reader) setup codec checks ensureInit
            supplied decision work runtime count selected index) slot)) := by
  rw [splitGame_expanded]
  exact rootClient_uniform setup codec checks ensureInit supplied decision work runtime count selected index budget
    certified

/-- Stages S1c and S2. The opaque KEM-ideal branch of theorem T6 (H0) and the uniform-root world on the root client (H2) are distinguishable with advantage at most `(qAccept + qFinish + qHmac) / 2^256` (route R1, stage S1c) plus the sum of `1 + qFinish` one-query HMAC PRF advantages (stage S2). -/
theorem opaqueBranch_uniform (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
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
        ∑ slot ∈ Finset.range (1 + budget (.inl 5)),
          (hmacPrfRealGame setup.hmac (indexedReduction setup.hmac (rootClient (Reader := Reader) setup codec checks
            ensureInit supplied decision work runtime count selected index) slot)).boolDistance
            (hmacPrfRandomGame (indexedReduction setup.hmac (rootClient (Reader := Reader) setup codec checks
              ensureInit supplied decision work runtime count selected index) slot)) :=
  (ProbComp.boolDistance_triangle _ _ _).trans (add_le_add
    (PqxdhRegistrationJointKemRomSplit.opaqueBranch_split setup codec checks ensureInit supplied decision work runtime
      count selected index budget certified)
    (split_uniform setup codec checks ensureInit supplied decision work runtime count selected index budget certified))

end BeaconcryptCore.Computational.PqxdhRegistrationJointKemRootExpand

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemRootExpand.rootClient_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemRootExpand.rootClient_uniform

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemRootExpand.split_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemRootExpand.split_uniform

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemRootExpand.opaqueBranch_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemRootExpand.opaqueBranch_uniform
