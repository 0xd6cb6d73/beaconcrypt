-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterGame

/-! LQ-F upstream, unit B1: the challenger's draws and the draw swap of item 2's logged prefix. The later second compile lemma (`PqxdhDeploymentIdealLaterGame.IdealCompileServerTarget`) compares item 2's logged two-slot world `PqxdhDeploymentLaterServerItemTargets.laterSlotGame` with the later ideal game `PqxdhDeploymentIdealLaterGame.idealLaterGame`, which draws the challenger's parameters first (`PqxdhDeploymentIdealParams.drawParams`: the selected KEM key pair, the other key pairs and the challenge encapsulation) and then runs pointwise in them. This module writes item 2's side in the same form, as `PqxdhDeploymentIdealParams` does for the classical `slotGame`.

- `preOpaquePoolL` is the logged opaque prephase `PqxdhDeploymentLaterServerOpaque.sourcePreOpaque` with the family of the other KEM key pairs given as an argument; `preOpaque_poolL` moves the family draw before the Server constructor (a failed constructor discards it).
- `startPoolL` is item 2's logged prefix at a draw (the result type of `PqxdhDeploymentLaterServerItemTargets.sharedStartL`), and `draws_swapL` moves the challenge encapsulation before the prephase, which does not read it: `sharedStartL` has the law of `drawParams` followed by `startPoolL`.
- `entryClientAtL` and `laterSlotGameAt` are the logged factored root client and the logged `n`-slot world at a draw; `laterSlotGame_pool`: the logged `n`-slot world has the distribution of `drawParams` followed by `laterSlotGameAt` (at `n = 2`, item 2's logged two-slot world).

Every step is an exchange of independent draws (`LazyOracleDiscard.lawEq_swap`) or the removal of an unused draw (`LazyOracleDiscard.lawEq_drop`). These are equalities in law; they charge nothing and make no security claim. -/

open OracleComp OracleSpec
set_option autoImplicit false

namespace BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterParams
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhKemIndCca (MlKem768PublicKey MlKem768Ciphertext)
open PqxdhInitializerSecrecy (kemAmbientImpl)
open PqxdhLiveKemReservation (Pair)
open LazyOracleDiscard (LawEq)
open PqxdhDeploymentLaterServerOpaque (OpaqueContext opaqueScan sourcePreOpaque)
open PqxdhDeploymentLaterServerItemTargets (sharedStartL cacheOfL postSkelL entryClientL laterSlotGame)
open PqxdhRegistrationJointAcceptCutTag (decideTag)
open PqxdhRegistrationJointKemEntryFactor (Output EntrySpec internalizeV factoredServices)
open PqxdhRegistrationJointKemSecondEntry (slotImpl emptyAlloc)
open PqxdhDeploymentIdealParams (Params drawParams)

variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response A X : Type}
  (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
  (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes) (decision : X → Bool)
  (work : OracleComp (PqxdhDeploymentLaterServerSource.Spec KemSK) X) (runtime : A)

/-! ### The logged prephase at a given pool and the draw swap -/

/-- Item 2's logged stopped-source prephase (`PqxdhDeploymentLaterServerOpaque.sourcePreOpaque`) with the family of the other KEM key pairs given as an argument instead of drawn after the constructor. -/
noncomputable def preOpaquePoolL (count : ℕ) (selected : Fin (count + 1)) (index : ℕ) (chosen : Pair KemSK)
    (others : Fin count → Pair KemSK) : ProbComp (OpaqueContext Reader KemSK A X count) := do
  let born ← (simulateQ (PqxdhRegistrationJointServerBirth.impl setup ensureInit)
    (PqxdhRegistrationJointServerBirth.client setup.serverKeyId supplied)).run
      ((PqxdhDynamicIdentityPool.initialState, PqxdhLiveKemBirth.empty), runtime)
  match born.1 with
  | none => pure (.failed born.2)
  | some created => do
    let result ← (((simulateQ (PqxdhDynamicKemJointRouter.stopped setup.baseImpl setup.joint setup.kem selected.val
      (List.ofFn (selected.insertNth chosen others)))
      (opaqueScan setup codec checks created.server.server.metadata.identityIndex created.publicIdentity
        (decideTag decision) work index [] [] (PqxdhRegistrationJointInitializedAccept.initial created))).run).run
          (born.2.1.1, PqxdhDynamicKemRouter.empty))
    pure (.ready created others result.1 result.2 born.2.2)

/-- Drawing the family of the other KEM key pairs before the Server constructor: item 2's logged prephase has the law of the family draw followed by the logged prephase at the drawn family. A failed constructor discards the family. -/
theorem preOpaque_poolL (count : ℕ) (selected : Fin (count + 1)) (index : ℕ) (chosen : Pair KemSK) :
    LawEq (sourcePreOpaque (Reader := Reader) setup codec checks ensureInit supplied decision work runtime count selected
        index chosen)
      (PqxdhLiveKemSelection.sampleFamily (simulateQ (kemAmbientImpl setup.baseImpl) setup.kem.keygen) count >>=
        fun others => preOpaquePoolL (Reader := Reader) setup codec checks ensureInit supplied decision work runtime
          count selected index chosen others) := by
  refine LawEq.trans ?_ (LazyOracleDiscard.lawEq_swap _ _ _).symm
  unfold sourcePreOpaque
  refine LawEq.bind (LawEq.refl _) fun born => ?_
  rcases born with ⟨_ | created, after⟩
  · exact (LazyOracleDiscard.lawEq_drop _ _).symm
  · exact LawEq.refl _

/-- Item 2's logged prefix at a given draw of the challenger: the logged prephase at the drawn pool, returning the table cache at the cut, the selected key pair, the prechallenge context and the challenge ciphertext (the result type of `sharedStartL`). -/
noncomputable def startPoolL (count : ℕ) (selected : Fin (count + 1)) (index : ℕ) (p : Params KemSK count) :
    ProbComp (PqxdhSecretInputKdf.HmacOracle.QueryCache ×
      (Pair KemSK × OpaqueContext Reader KemSK A X count × MlKem768Ciphertext)) := do
  let context ← preOpaquePoolL (Reader := Reader) setup codec checks ensureInit supplied decision work runtime count
    selected index p.chosen p.others
  pure (cacheOfL context, (p.chosen, context, p.challenge))

/-- The draw swap for the logged prefix: `sharedStartL` has the law of the challenger's draws `drawParams` (selected key pair, family, challenge encapsulation) followed by the logged prephase at the drawn pool. The family moves before the constructor (`preOpaque_poolL`) and the encapsulation before the prephase, which does not read it. -/
theorem draws_swapL (count : ℕ) (selected : Fin (count + 1)) (index : ℕ) :
    LawEq (sharedStartL (Reader := Reader) setup codec checks ensureInit supplied decision work runtime count selected
        index)
      (drawParams setup count >>= startPoolL (Reader := Reader) setup codec checks ensureInit supplied decision work
        runtime count selected index) := by
  unfold sharedStartL drawParams startPoolL
  simp only [bind_assoc, pure_bind]
  refine LawEq.bind (LawEq.refl _) fun chosen => ?_
  refine (LawEq.bind (preOpaque_poolL setup codec checks ensureInit supplied decision work runtime count selected
    index chosen) fun context => LawEq.refl _).trans ?_
  simp only [bind_assoc]
  refine LawEq.bind (LawEq.refl _) fun others => ?_
  exact LazyOracleDiscard.lawEq_swap _ _ _

/-! ### Item 2's logged `n`-slot world, pointwise in the challenger's draws -/

/-- Item 2's logged factored root client (`PqxdhDeploymentLaterServerItemTargets.entryClientL`) at a given draw of the challenger: the logged prefix at the drawn pool, then the logged skeleton's post-challenge phase with the factored services. -/
noncomputable def entryClientAtL (count : ℕ) (selected : Fin (count + 1)) (index : ℕ) (p : Params KemSK count) :
    OracleComp (EntrySpec Output) Bool :=
  internalizeV (startPoolL (Reader := Reader) setup codec checks ensureInit supplied decision work runtime count
      selected index p)
    (fun context => postSkelL setup codec checks decision count selected (factoredServices setup codec checks)
      context.1 context.2.2 context.2.1)

/-- Item 2's logged `n`-slot world (`laterSlotGame`) at a given draw of the challenger. -/
noncomputable def laterSlotGameAt (count : ℕ) (selected : Fin (count + 1)) (index n : ℕ) (p : Params KemSK count) :
    ProbComp Bool :=
  (simulateQ (slotImpl (D := PqxdhCorrelatedExtractFamily.Message) (PqxdhRegistrationJointKemSecondEntry.tableService
      (n := n)))
    (entryClientAtL (Reader := Reader) setup codec checks ensureInit supplied decision work runtime count selected
      index p)).run' (emptyAlloc, PqxdhRecordLiftLazyTable.initial)

/-- The draw swap in item 2's logged `n`-slot world (at `n = 2`, item 2's logged two-slot world): the logged `n`-slot world has the distribution of the challenger's draws followed by the same world at the drawn parameters. -/
theorem laterSlotGame_pool (count : ℕ) (selected : Fin (count + 1)) (index n : ℕ) :
    𝒟[laterSlotGame setup codec checks ensureInit supplied decision work runtime count selected index n] =
      𝒟[drawParams setup count >>= laterSlotGameAt (Reader := Reader) setup codec checks ensureInit supplied decision
        work runtime count selected index n] := by
  unfold laterSlotGame laterSlotGameAt entryClientAtL entryClientL
  simp only [PqxdhDeploymentIdealParams.internalize_run]
  refine (draws_swapL setup codec checks ensureInit supplied decision work runtime count selected index Bool _).trans ?_
  rw [bind_assoc]

end BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterParams

-- Axiom guards (generated)

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterParams.preOpaque_poolL' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterParams.preOpaque_poolL

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterParams.draws_swapL' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterParams.draws_swapL

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterParams.laterSlotGame_pool' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterParams.laterSlotGame_pool
