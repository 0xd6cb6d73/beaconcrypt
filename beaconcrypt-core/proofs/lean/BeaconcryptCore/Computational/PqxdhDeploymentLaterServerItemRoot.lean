-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemSplit

/-! LQ-F upstream, unit A2: stage S2 of item 2 over the logged source, without the stage T count (LQ-F upstream design-v2, section 4.4, module `…ItemRoot`). It turns G1's split world of stage S1c over the logged source into an ordinary game of the correlated Extract family on the logged root client `PqxdhDeploymentLaterServerItemTargets.rootClientL` of unit D1, and carries the PRF step of stage S2 at any number of root requests.

- `splitGameL_root`: G1's split world on the logged prefix and client (`sharedStartL`, `sharedClientL`) is the family's random game on the compiled logged root client. This is `PqxdhRegistrationJointKemRootExpand.splitGame_local`, which is generic in the prefix and the skeleton client, at the logged prefix and the logged skeleton's postchallenge phase `postSkelL`. `splitGameL_expanded` rewrites it into the cached-root game with real Expand.
- `rootClientL_root` and `entryClientL_value`: the logged root client makes at most `n` root requests, and the logged factored root client at most `n` value requests, whenever the logged postchallenge phase makes at most `n` hidden reads on every outcome of the logged prefix. The root client's coins and its public table make no root request (`publicLocal_root`, `publicLocalV_value`).
- `splitL_uniform` and `opaqueBranchL_uniform`: at such an `n`, the split world and the uniform-root world are distinguishable with advantage at most the sum of `n` one-query HMAC-SHA-512 PRF advantages of the indexed reductions of `rootClientL` (`PqxdhCorrelatedExpandHybrid.expanded_uniform_bound`), and together with stage S1c over the logged source (`PqxdhDeploymentLaterServerItemSplit.opaqueBranchL_split`) the logged opaque KEM-ideal branch and the uniform-root world are distinguishable with advantage at most `(qAccept + qFinish + qHmac) / 2^256` plus that sum. `PqxdhDeploymentLaterServerItemOnce` supplies `n = 2` (stage T).

The classical stage S2 also bounds the root requests by `1 + qFinish` (`PqxdhRegistrationJointKemRootExpand.rootClient_root`, through the per-request hidden-read counts `skelImpl_hidden`, `groupedClient_group` and `postSkel_hidden`); LQ-F needs only the two-read forms of stage T, and the LQ-F upstream design does not build the `1 + qFinish` forms (its first version, section 3.10), so that count is not restated here. The root client has no candidate argument, and it is defined from the arguments of `splitGame`, which draws no candidate. These are program equalities and the generic PRF step; no assumption is added beyond the logged source budget `certified` of stage S1c. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option maxRecDepth 100000
namespace BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemRoot
open PqxdhKemIndCca PqxdhInitializerSecrecy PqxdhServerAuthExperiment PqxdhJointIdentity
open PqxdhSecretInputKdf (hmacPrfRealGame hmacPrfRandomGame)
open PqxdhCorrelatedExpandHybrid (IsRoot uniformGame indexedReduction)
open PqxdhCorrelatedExtractFamily (randomGame)
open PqxdhExtractRomHiddenSuffix (splitGame)
open PqxdhRegistrationJointKemPostSkeleton (nativeServices)
open PqxdhRegistrationJointKemRootExpand (valueRead? publicLocal_root)
open PqxdhRegistrationJointKemEntryFactor (Output factoredServices)
open PqxdhRegistrationJointKemSecondEntry (IsValue publicLocalV_value)
open PqxdhDeploymentLaterServerOpaque (opaqueBranch)
open PqxdhDeploymentLaterServerItemTargets (sharedStartL sharedClientL postSkelL rootClientL entryClientL)

variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response A X : Type}

/-! ### The internalization -/

/-- Stage S2 over the logged source, the internalization: G1's split world on the logged prefix and client is the correlated family's random game on the compiled logged root client. -/
theorem splitGameL_root (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes) (decision : X → Bool)
    (work : OracleComp (PqxdhDeploymentLaterServerSource.Spec KemSK) X) (runtime : A) (count : Nat)
    (selected : Fin (count + 1)) (index : Nat) :
    splitGame (sharedStartL (Reader := Reader) setup codec checks ensureInit supplied decision work runtime count
        selected index) (sharedClientL setup codec checks decision count selected) =
      randomGame (simulateQ (PqxdhCorrelatedExpand.compile setup.hmac) (rootClientL (Reader := Reader) setup codec
        checks ensureInit supplied decision work runtime count selected index)) :=
  PqxdhRegistrationJointKemRootExpand.splitGame_local setup.hmac _ _

/-- G1's split world on the logged prefix and client is the cached-root game with real Expand on the logged root client. -/
theorem splitGameL_expanded (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes) (decision : X → Bool)
    (work : OracleComp (PqxdhDeploymentLaterServerSource.Spec KemSK) X) (runtime : A) (count : Nat)
    (selected : Fin (count + 1)) (index : Nat) :
    splitGame (sharedStartL (Reader := Reader) setup codec checks ensureInit supplied decision work runtime count
        selected index) (sharedClientL setup codec checks decision count selected) =
      PqxdhCorrelatedExpand.expandedGame setup.hmac (rootClientL (Reader := Reader) setup codec checks ensureInit
        supplied decision work runtime count selected index) := by
  rw [splitGameL_root]
  exact PqxdhCorrelatedExpand.expandedGame_eq setup.hmac _

/-! ### Root requests from hidden reads -/

/-- The logged root client makes at most `n` root requests, repeated requests included, when the logged postchallenge phase with the native services makes at most `n` hidden reads on every outcome of the logged prefix: its coins and its public table make none, and every hidden read becomes one root request. -/
theorem rootClientL_root (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes) (decision : X → Bool)
    (work : OracleComp (PqxdhDeploymentLaterServerSource.Spec KemSK) X) (runtime : A) (count : Nat)
    (selected : Fin (count + 1)) (index : Nat) (n : ℕ)
    (hidden : ∀ start ∈ support (sharedStartL (Reader := Reader) setup codec checks ensureInit supplied decision work
      runtime count selected index),
      (postSkelL setup codec checks decision count selected (nativeServices setup codec checks) start.2.1
        start.2.2.2 start.2.2.1).IsQueryBoundP (fun query => valueRead? query = true) n) :
    (rootClientL (Reader := Reader) setup codec checks ensureInit supplied decision work runtime count selected
      index).IsQueryBoundP IsRoot n := by
  unfold rootClientL PqxdhRegistrationJointKemRootExpand.internalize
  rw [← Nat.zero_add n]
  refine isQueryBoundP_bind (PqxdhCorrelatedExpandQueryBounds.rootCoins_roots _) fun start reached => ?_
  rw [StateT.run'_eq, isQueryBoundP_map_iff]
  refine IsQueryBoundP.simulateQ_run_StateT_of_step ?_ (fun query cache => publicLocal_root query cache) start.1
  exact hidden start (OracleComp.mem_support_of_mem_support_liftComp _ _ start reached)

/-- The logged factored root client makes at most `n` value requests when the logged postchallenge phase with the factored services makes at most `n` hidden reads on every outcome of the logged prefix. -/
theorem entryClientL_value (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes) (decision : X → Bool)
    (work : OracleComp (PqxdhDeploymentLaterServerSource.Spec KemSK) X) (runtime : A) (count : Nat)
    (selected : Fin (count + 1)) (index : Nat) (n : ℕ)
    (hidden : ∀ start ∈ support (sharedStartL (Reader := Reader) setup codec checks ensureInit supplied decision work
      runtime count selected index),
      (postSkelL setup codec checks decision count selected (factoredServices setup codec checks) start.2.1
        start.2.2.2 start.2.2.1).IsQueryBoundP (fun query => valueRead? query = true) n) :
    (entryClientL (Reader := Reader) setup codec checks ensureInit supplied decision work runtime count selected
      index).IsQueryBoundP (IsValue (D := PqxdhCorrelatedExtractFamily.Message) (R := Output)) n := by
  unfold entryClientL PqxdhRegistrationJointKemEntryFactor.internalizeV
  rw [← Nat.zero_add n]
  refine isQueryBoundP_bind (IsQueryBoundP.liftComp_subSpec (fun _ => Iff.rfl) (isQueryBoundP_false _ 0))
    fun start reached => ?_
  rw [StateT.run'_eq, isQueryBoundP_map_iff]
  refine IsQueryBoundP.simulateQ_run_StateT_of_step ?_ (fun query cache => publicLocalV_value query cache) start.1
  exact hidden start (OracleComp.mem_support_of_mem_support_liftComp _ _ start reached)

/-! ### The PRF step -/

/-- Stage S2 over the logged source at `n` root requests: G1's split world on the logged prefix and client and the uniform-root world on the logged root client are distinguishable with advantage at most the sum of `n` one-query HMAC-SHA-512 PRF advantages. -/
theorem splitL_uniform (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes) (decision : X → Bool)
    (work : OracleComp (PqxdhDeploymentLaterServerSource.Spec KemSK) X) (runtime : A) (count : Nat)
    (selected : Fin (count + 1)) (index : Nat) (n : ℕ)
    (roots : (rootClientL (Reader := Reader) setup codec checks ensureInit supplied decision work runtime count
      selected index).IsQueryBoundP IsRoot n) :
    (splitGame (sharedStartL (Reader := Reader) setup codec checks ensureInit supplied decision work runtime count
        selected index) (sharedClientL setup codec checks decision count selected)).boolDistAdvantage
      (uniformGame (rootClientL (Reader := Reader) setup codec checks ensureInit supplied decision work runtime count
        selected index)) ≤
      ∑ slot ∈ Finset.range n,
        (hmacPrfRealGame setup.hmac (indexedReduction setup.hmac (rootClientL (Reader := Reader) setup codec checks
          ensureInit supplied decision work runtime count selected index) slot)).boolDistAdvantage
          (hmacPrfRandomGame (indexedReduction setup.hmac (rootClientL (Reader := Reader) setup codec checks
            ensureInit supplied decision work runtime count selected index) slot)) := by
  rw [splitGameL_expanded]
  exact PqxdhCorrelatedExpandHybrid.expanded_uniform_bound setup.hmac _ _ roots

/-- Stages S1c and S2 over the logged source at `n` root requests: the logged opaque KEM-ideal branch and the uniform-root world on the logged root client are distinguishable with advantage at most `(qAccept + qFinish + qHmac) / 2^256` (route R1, stage S1c over the logged source) plus the sum of `n` one-query HMAC-SHA-512 PRF advantages. -/
theorem opaqueBranchL_uniform (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes) (decision : X → Bool)
    (work : OracleComp (PqxdhDeploymentLaterServerSource.Spec KemSK) X) (runtime : A) (count : Nat)
    (selected : Fin (count + 1)) (index : Nat) (budget : PqxdhRegistrationJointRevealCosts.SourceKind → ℕ)
    (certified : ∀ kind, work.IsQueryBoundP
      (fun query => PqxdhDeploymentLaterServerReserve.laterKind (KemSK := KemSK) query = some kind) (budget kind))
    (n : ℕ)
    (roots : (rootClientL (Reader := Reader) setup codec checks ensureInit supplied decision work runtime count
      selected index).IsQueryBoundP IsRoot n) :
    (opaqueBranch (Reader := Reader) setup codec checks ensureInit supplied decision work runtime count selected index
        false).boolDistAdvantage
      (uniformGame (rootClientL (Reader := Reader) setup codec checks ensureInit supplied decision work runtime count
        selected index)) ≤
      ((budget (.inl 3) + budget (.inl 5) + budget (.inl 6) : ℕ) : ℝ) / 2 ^ 256 +
        ∑ slot ∈ Finset.range n,
          (hmacPrfRealGame setup.hmac (indexedReduction setup.hmac (rootClientL (Reader := Reader) setup codec checks
            ensureInit supplied decision work runtime count selected index) slot)).boolDistAdvantage
            (hmacPrfRandomGame (indexedReduction setup.hmac (rootClientL (Reader := Reader) setup codec checks
              ensureInit supplied decision work runtime count selected index) slot)) :=
  (ProbComp.boolDistAdvantage_triangle _ _ _).trans (add_le_add
    (PqxdhDeploymentLaterServerItemSplit.opaqueBranchL_split setup codec checks ensureInit supplied decision work
      runtime count selected index budget certified)
    (splitL_uniform setup codec checks ensureInit supplied decision work runtime count selected index n roots))

end BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemRoot

-- Axiom guards (generated)

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemRoot.splitGameL_root' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemRoot.splitGameL_root

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemRoot.splitGameL_expanded' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemRoot.splitGameL_expanded

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemRoot.rootClientL_root' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemRoot.rootClientL_root

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemRoot.entryClientL_value' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemRoot.entryClientL_value

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemRoot.splitL_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemRoot.splitL_uniform

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemRoot.opaqueBranchL_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemRoot.opaqueBranchL_uniform
