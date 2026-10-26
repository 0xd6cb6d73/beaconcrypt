import BeaconcryptCore.Computational.PqxdhRegistrationJointKemRomSplit
import BeaconcryptCore.Computational.PqxdhCorrelatedExpandHybrid

/-!
# The root client of the KEM-ideal branch (item 2, stage S2, internalization)

This module begins stage S2 of the item 2 plan. It turns G1's split world of stage S1c (`PqxdhExtractRomHiddenSuffix.splitGame`, H1 of the plan) into an ordinary game of the correlated Extract family (`PqxdhCorrelatedExtractFamily.randomGame`) on a root client (`rootClient`) that holds everything except the hidden table.

- `internalize start post` is a root-valued client (`PqxdhCorrelatedExpand.RootSpec`: coins and root requests at 128-byte coordinates). It runs the prefix `start` on its own coins and then the skeleton client `post`, answering coins and hidden reads by its own requests and every direct read from a lazily sampled public table that it holds itself (`publicLocal`), starting from the table cache at the cut. The root requests are the only requests whose answers it does not compute itself.
- `splitGame_local`: G1's split world with any prefix and any skeleton client compiled by `compileHidden` equals the family's random game on the compiled root client. The hidden reads in the split world are answered by a coordinate-keyed lazily sampled table, which is the family's random table; the public table moves into the client (`split_step`, `split_local_run`).
- `rootClient` is `internalize` at the prefix and skeleton client of the KEM-ideal branch (`sharedStart` and `postSkel` with the native services). It runs the key generation, the prechallenge source, the encapsulation, the actual encapsulator, the post-challenge router, the CCA evaluation and the native game state (with its BLAKE2b table) inside the client. `splitGame_root` is the plan's S2 equality, and `splitGame_expanded` rewrites it with `PqxdhCorrelatedExpand.expandedGame_eq` into the cached-root game with real Expand.

The candidate does not occur in `rootClient`: it is defined from the arguments of `splitGame`, which draws no candidate, and it has no candidate argument. These are program equalities; they charge nothing.
-/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement

set_option autoImplicit false
set_option maxRecDepth 100000

namespace BeaconcryptCore.Computational.PqxdhRegistrationJointKemRootExpand

open PqxdhSecretInputKdf (HmacBlock HmacOracle RootOutput)
open PqxdhCorrelatedExpand (RootSpec rootCoins compile)
open PqxdhCorrelatedExtractFamily (FamilySpec ExtractOracle randomImpl randomGame coins)
open PqxdhExtractRomHiddenSuffix (HiddenSpec TableOracle splitImpl splitGame)
open PqxdhRegistrationJointKemPostSkeleton (SkelSpec ValueOracle compileHidden)

/-! ### The public table inside the root client -/

section Local

/-- The root client's interpretation of the skeleton interface: coins and hidden reads are the root client's own requests; a direct read is answered from a lazily sampled public table in the client's state, with coins drawn by the client. -/
noncomputable def publicLocal :
    QueryImpl (SkelSpec RootOutput) (StateT HmacOracle.QueryCache (OracleComp RootSpec)) :=
  (fun query => StateT.mk fun cache =>
      (fun reply => (reply, cache)) <$> (RootSpec.query (.inl query) : OracleComp RootSpec _) :
      QueryImpl unifSpec (StateT HmacOracle.QueryCache (OracleComp RootSpec))) +
    ((fun message => StateT.mk fun cache =>
        (fun reply => (reply, cache)) <$> (RootSpec.query (.inr message) : OracleComp RootSpec _) :
        QueryImpl (ValueOracle RootOutput) (StateT HmacOracle.QueryCache (OracleComp RootSpec))) +
      (fun point => StateT.mk fun cache => rootCoins ((HmacOracle.randomOracle point).run cache) :
        QueryImpl TableOracle (StateT HmacOracle.QueryCache (OracleComp RootSpec))))

/-- The root client of a prefix and a skeleton client: the prefix runs on the client's coins, and the table cache at the cut becomes the client's own public table. -/
noncomputable def internalize {C : Type} (start : ProbComp (HmacOracle.QueryCache × C))
    (post : C → OracleComp (SkelSpec RootOutput) Bool) : OracleComp RootSpec Bool := do
  let p ← rootCoins start
  (simulateQ publicLocal (post p.2)).run' p.1

/-- Coins of the family leave its random table untouched. -/
theorem random_coins {α : Type} (work : ProbComp α) (cache : ExtractOracle.QueryCache) :
    (simulateQ randomImpl (coins work)).run cache = (fun reply => (reply, cache)) <$> work := by
  simp only [coins, randomImpl, QueryImpl.simulateQ_add_liftComp_left, simulateQ_liftTarget,
    simulateQ_ofLift_eq_self]
  simp only [StateT.run_monadLift, monadLift_eq_self, bind_pure_comp]

/-- One request: the split world's step equals the root client's step under the compiled family's random table, with the public table moved into the client. -/
theorem split_step (hmac : PqxdhSecretInputKdf.HmacSha512) (query : (SkelSpec RootOutput).Domain)
    (cache : HmacOracle.QueryCache) (hidden : ExtractOracle.QueryCache) :
    (simulateQ splitImpl (compileHidden hmac query)).run (cache, hidden) =
      (fun result => (result.1.1, (result.1.2, result.2))) <$>
        (simulateQ randomImpl (simulateQ (compile hmac) ((publicLocal query).run cache))).run hidden := by
  rcases query with coin | (message | point)
  · change (simulateQ splitImpl (liftM (HiddenSpec.query (.inl coin)))).run (cache, hidden) =
      (fun result => (result.1.1, (result.1.2, result.2))) <$>
        (simulateQ randomImpl (simulateQ (compile hmac)
          ((fun reply => (reply, cache)) <$> (liftM (RootSpec.query (.inl coin)) : OracleComp RootSpec _)))).run hidden
    simp only [simulateQ_spec_query, simulateQ_map, StateT.run_map, Functor.map_map]
    rfl
  · change (simulateQ splitImpl (PqxdhSecretInputKdf.expandRoot hmac <$>
        (liftM (HiddenSpec.query (.inr (.inl message))) : OracleComp HiddenSpec _))).run (cache, hidden) =
      (fun result => (result.1.1, (result.1.2, result.2))) <$>
        (simulateQ randomImpl (simulateQ (compile hmac)
          ((fun reply => (reply, cache)) <$> (liftM (RootSpec.query (.inr message)) : OracleComp RootSpec _)))).run
          hidden
    simp only [simulateQ_spec_query, simulateQ_map, StateT.run_map, Functor.map_map]
    change _ = _ <$> (simulateQ randomImpl (PqxdhSecretInputKdf.expandRoot hmac <$>
      (liftM (FamilySpec.query (.inr message)) : OracleComp FamilySpec _))).run hidden
    simp only [simulateQ_spec_query, simulateQ_map, StateT.run_map, Functor.map_map, splitImpl, randomImpl,
      QueryImpl.add_apply_inr, QueryImpl.add_apply_inl, StateT.run_mk]
  · change (simulateQ splitImpl (liftM (HiddenSpec.query (.inr (.inr point))))).run (cache, hidden) =
      (fun result => (result.1.1, (result.1.2, result.2))) <$>
        (simulateQ randomImpl (simulateQ (compile hmac) (rootCoins ((HmacOracle.randomOracle point).run cache)))).run
          hidden
    rw [PqxdhCorrelatedExpand.compile_coins, random_coins, simulateQ_spec_query, Functor.map_map]
    rfl

/-- Every program: the split world equals the root client's interpretation under the compiled family's random table. -/
theorem split_local_run {α : Type} (hmac : PqxdhSecretInputKdf.HmacSha512) (work : OracleComp (SkelSpec RootOutput) α)
    (cache : HmacOracle.QueryCache) (hidden : ExtractOracle.QueryCache) :
    (simulateQ splitImpl (simulateQ (compileHidden hmac) work)).run (cache, hidden) =
      (fun result => (result.1.1, (result.1.2, result.2))) <$>
        (simulateQ randomImpl (simulateQ (compile hmac) ((simulateQ publicLocal work).run cache))).run hidden := by
  induction work using OracleComp.inductionOn generalizing cache hidden with
  | pure value => simp
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, split_step, bind_map_left, map_bind]
      exact bind_congr fun result => ih result.1.1 result.1.2 result.2

/-- G1's split world on a skeleton client compiled by `compileHidden` is the family's random game on the root client that holds the prefix and the public table. -/
theorem splitGame_local (hmac : PqxdhSecretInputKdf.HmacSha512) {C : Type}
    (start : ProbComp (HmacOracle.QueryCache × C)) (post : C → OracleComp (SkelSpec RootOutput) Bool) :
    splitGame start (fun context => simulateQ (compileHidden hmac) (post context)) =
      randomGame (simulateQ (compile hmac) (internalize start post)) := by
  unfold splitGame randomGame internalize
  rw [simulateQ_bind, PqxdhCorrelatedExpand.compile_coins, simulateQ_bind, StateT.run'_eq, StateT.run_bind,
    random_coins, bind_map_left, map_bind]
  refine bind_congr fun p => ?_
  rw [StateT.run'_eq, split_local_run, StateT.run'_eq, simulateQ_map, simulateQ_map, StateT.run_map,
    Functor.map_map, Functor.map_map]

end Local

/-! ### The root client of the KEM-ideal branch -/

section Root

open PqxdhKemIndCca PqxdhInitializerSecrecy PqxdhServerAuthExperiment PqxdhJointIdentity
open PqxdhRegistrationJointKemPostSkeleton (sharedStart sharedClient postSkel nativeServices)
open PqxdhRegistrationJointKemCommands (SourceSpec)

variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response A X : Type}

/-- The root client of stage S2: the prefix of the KEM-ideal branch (key generation, prechallenge source, encapsulation) and the skeleton's post-challenge phase with the native services (actual encapsulator, post-challenge router, CCA evaluation and native game state), with the public table at the cut held inside. It has no candidate argument. -/
noncomputable def rootClient (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes)
    (decision : X → Bool) (work : OracleComp (SourceSpec KemSK) X) (runtime : A)
    (count : Nat) (selected : Fin (count + 1)) (index : Nat) : OracleComp RootSpec Bool :=
  internalize (sharedStart (Reader := Reader) setup codec checks ensureInit supplied decision work runtime count
      selected index)
    (fun context => postSkel setup codec checks decision count selected (nativeServices setup codec checks) context.1
      context.2.2 context.2.1)

/-- Stage S2, the internalization: G1's split world of the KEM-ideal branch is the correlated family's random game on the compiled root client. -/
theorem splitGame_root (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes)
    (decision : X → Bool) (work : OracleComp (SourceSpec KemSK) X) (runtime : A)
    (count : Nat) (selected : Fin (count + 1)) (index : Nat) :
    splitGame (sharedStart (Reader := Reader) setup codec checks ensureInit supplied decision work runtime count
        selected index) (sharedClient setup codec checks decision count selected) =
      randomGame (simulateQ (compile setup.hmac) (rootClient (Reader := Reader) setup codec checks ensureInit supplied
        decision work runtime count selected index)) :=
  splitGame_local setup.hmac _ _

/-- G1's split world of the KEM-ideal branch is the cached-root game with real Expand on the root client. -/
theorem splitGame_expanded (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes)
    (decision : X → Bool) (work : OracleComp (SourceSpec KemSK) X) (runtime : A)
    (count : Nat) (selected : Fin (count + 1)) (index : Nat) :
    splitGame (sharedStart (Reader := Reader) setup codec checks ensureInit supplied decision work runtime count
        selected index) (sharedClient setup codec checks decision count selected) =
      PqxdhCorrelatedExpand.expandedGame setup.hmac (rootClient (Reader := Reader) setup codec checks ensureInit
        supplied decision work runtime count selected index) := by
  rw [splitGame_root]
  exact PqxdhCorrelatedExpand.expandedGame_eq setup.hmac _

end Root

end BeaconcryptCore.Computational.PqxdhRegistrationJointKemRootExpand

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemRootExpand.random_coins' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemRootExpand.random_coins

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemRootExpand.split_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemRootExpand.split_step

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemRootExpand.split_local_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemRootExpand.split_local_run

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemRootExpand.splitGame_local' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemRootExpand.splitGame_local

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemRootExpand.splitGame_root' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemRootExpand.splitGame_root

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemRootExpand.splitGame_expanded' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemRootExpand.splitGame_expanded
