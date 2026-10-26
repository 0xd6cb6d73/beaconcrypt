-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRegistrationJointKemSecondEntry
import BeaconcryptCore.Computational.PqxdhDeploymentKemTransfer
import BeaconcryptCore.Computational.LazyOracleDiscard

/-!
# The challenger's draws of CE-11b and the draw swap of item 2's prefix

The ideal registration of the common deployment experiment (CE-11b) is pointwise in the challenger's draws, which are made before the run in item 2's order and type (design-v2 section 3.1, route R3): the selected KEM key pair `chosen`, the family `others` of the other `count` KEM key pairs, and the challenge ciphertext of an encapsulation to `chosen`'s public key (`Params`, `drawParams`). A target in item 2's coordinates is a raw-accept ordinal and a KEM creation index (`Target`; `Target.ofCE` reads it from a CE designation `g`, with `PqxdhDeploymentKemTransfer.selectedKem`). The reservation of the stopped selected-first router is the pool `Params.pool`: entry `t.kem` is `chosen` and the other entries are `others` in index order (`pool_kem`, `pool_other`), which is the form `List.ofFn (selected.insertNth chosen others)` in which item 2's prephase builds the router's reservation (`pool_eq` gives the list form; `preOpaquePool`, the prephase at a given family, builds the router from this list, and `preOpaque_pool` relates it to item 2's prephase).

Item 2's ideal world draws the same values in another order: `PqxdhRegistrationJointKemPostSkeleton.sharedStart` draws `chosen`, then runs the prephase `PqxdhRegistrationJointKemRawOpaque.sourcePreOpaque`, which draws the family after the Server constructor (and not at all when the constructor fails), then draws the challenge encapsulation. `preOpaquePool` is the prephase with the family given as an argument; `preOpaque_pool` moves the family draw before the constructor (a failed constructor discards it), and `draws_swap` moves the encapsulation before the prephase, so item 2's prefix has the law of `drawParams` followed by the prephase at the drawn pool (`startPool`). `slotGame_pool` lifts this to item 2's `n`-slot ideal world `PqxdhRegistrationJointKemSecondEntry.slotGame` (at `n = 2`, item 2's two-slot ideal world): it is, in distribution, `drawParams` followed by the same world pointwise in the drawn parameters (`slotGameAt`). Every step is an exchange of independent draws (`LazyOracleDiscard.lawEq_swap`) or the removal of an unused draw (`LazyOracleDiscard.lawEq_drop`). These are equalities in law; they charge nothing and make no security claim.
-/

open OracleComp OracleSpec

set_option autoImplicit false

namespace BeaconcryptCore.Computational.PqxdhDeploymentIdealParams
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhKemIndCca (MlKem768PublicKey MlKem768Ciphertext)
open PqxdhInitializerSecrecy (kemAmbientImpl)
open PqxdhLiveKemReservation (Pair)
open PqxdhDeploymentInterface (Budget)
open LazyOracleDiscard (LawEq)
open PqxdhRegistrationJointKemRawOpaque (OpaqueContext opaqueScan sourcePreOpaque)
open PqxdhRegistrationJointKemCommands (SourceSpec)
open PqxdhRegistrationJointAcceptCutTag (decideTag)
open PqxdhRegistrationJointKemPostSkeleton (sharedStart cacheOf postSkel)
open PqxdhRegistrationJointKemEntryFactor (Output EntrySpec entryClient internalizeV factoredServices)
open PqxdhRegistrationJointKemSecondEntry (slotImpl emptyAlloc slotGame)

/-! ### Targets and the challenger's draws -/

/-- A target in item 2's coordinates: the raw-accept ordinal of the selected Server session and the KEM creation index of the selected owner. -/
structure Target (count : ℕ) where
  accept : ℕ
  kem : Fin (count + 1)

/-- The target of a CE designation `g = (i, k)`: the raw-accept ordinal `i` and the KEM creation index of `k` (`PqxdhDeploymentKemTransfer.selectedKem`). -/
def Target.ofCE (budget : Budget) (g : Fin budget.accept × Fin budget.capacity) : Target budget.create :=
  ⟨g.1.val, PqxdhDeploymentKemTransfer.selectedKem budget g⟩

/-- The target's KEM creation index is the selected KEM of the designation. -/
theorem ofCE_kem (budget : Budget) (g : Fin budget.accept × Fin budget.capacity) :
    (Target.ofCE budget g).kem = PqxdhDeploymentKemTransfer.selectedKem budget g := rfl

/-- The target's raw-accept ordinal is the designation's accept index. -/
theorem ofCE_accept (budget : Budget) (g : Fin budget.accept × Fin budget.capacity) :
    (Target.ofCE budget g).accept = g.1.val := rfl

/-- The challenger's draws, in item 2's order and type: the selected KEM key pair, the other `count` KEM key pairs and the challenge ciphertext. -/
structure Params (KemSK : Type) (count : ℕ) where
  chosen : Pair KemSK
  others : Fin count → Pair KemSK
  challenge : MlKem768Ciphertext

variable {KemSK : Type} {count : ℕ}

/-- The indexed KEM reservation of a target: entry `t.kem` is `chosen`, the other entries are `others` in index order. -/
def Params.family (t : Target count) (p : Params KemSK count) : Fin (count + 1) → Pair KemSK :=
  t.kem.insertNth p.chosen p.others

/-- The KEM reservation of a target as a list: owner `j` holds entry `j`. -/
def Params.pool (t : Target count) (p : Params KemSK count) : List (Pair KemSK) :=
  List.ofFn (p.family t)

/-- The pool has one entry per KEM creation index. -/
theorem pool_length (t : Target count) (p : Params KemSK count) : (p.pool t).length = count + 1 :=
  List.length_ofFn

/-- The selected creation index holds the selected key pair. -/
theorem pool_kem (t : Target count) (p : Params KemSK count) : (p.pool t)[t.kem.val]? = some p.chosen := by
  have bound := t.kem.isLt
  rw [Params.pool, List.getElem?_ofFn]
  simp [Params.family]
  omega

/-- Every other creation index holds the corresponding other key pair, in index order. -/
theorem pool_other (t : Target count) (p : Params KemSK count) (j : Fin count) :
    (p.pool t)[(t.kem.succAbove j).val]? = some (p.others j) := by
  have bound := (t.kem.succAbove j).isLt
  rw [Params.pool, List.getElem?_ofFn]
  simp [Params.family]
  omega

/-- The pool of a target as a list: `List.ofFn (t.kem.insertNth chosen others)`. This lemma only unfolds `Params.pool`. It is the form in which item 2's prephase builds the reservation of the stopped selected-first router: the prephase at a given family, `preOpaquePool`, passes this list to the router by definition, and `preOpaque_pool` shows that the family draw followed by `preOpaquePool` has the law of item 2's prephase `sourcePreOpaque`. -/
theorem pool_eq (t : Target count) (p : Params KemSK count) :
    p.pool t = List.ofFn (t.kem.insertNth p.chosen p.others) := rfl

section Draws
variable {ι : Type} {baseSpec : OracleSpec ι} (setup : Setup baseSpec KemSK)

/-- The challenger's draws (R3): the selected key pair, the family of the other key pairs, and the encapsulation to the selected public key, of which the ciphertext is kept. -/
noncomputable def drawParams (count : ℕ) : ProbComp (Params KemSK count) := do
  let chosen ← simulateQ (kemAmbientImpl setup.baseImpl) setup.kem.keygen
  let others ← PqxdhLiveKemSelection.sampleFamily (simulateQ (kemAmbientImpl setup.baseImpl) setup.kem.keygen) count
  let encapsulated ← simulateQ (kemAmbientImpl setup.baseImpl) (setup.kem.encaps chosen.1)
  pure ⟨chosen, others, encapsulated.1⟩

end Draws

/-! ### The prephase at a given pool and the draw swap -/

section Swap
variable {ι : Type} {baseSpec : OracleSpec ι} {Reader Response A X : Type}
  (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
  (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes) (decision : X → Bool)
  (work : OracleComp (SourceSpec KemSK) X) (runtime : A)

/-- Item 2's stopped-source prephase (`PqxdhRegistrationJointKemRawOpaque.sourcePreOpaque`) with the family of the other KEM key pairs given as an argument instead of drawn after the constructor. -/
noncomputable def preOpaquePool (count : ℕ) (selected : Fin (count + 1)) (index : ℕ) (chosen : Pair KemSK)
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
        (decideTag decision) work index [] (PqxdhRegistrationJointInitializedAccept.initial created))).run).run
          (born.2.1.1, PqxdhDynamicKemRouter.empty))
    pure (.ready created others result.1 result.2 born.2.2)

/-- Drawing the family of the other KEM key pairs before the Server constructor: item 2's prephase has the law of the family draw followed by the prephase at the drawn family. A failed constructor discards the family. -/
theorem preOpaque_pool (count : ℕ) (selected : Fin (count + 1)) (index : ℕ) (chosen : Pair KemSK) :
    LawEq (sourcePreOpaque (Reader := Reader) setup codec checks ensureInit supplied decision work runtime count selected
        index chosen)
      (PqxdhLiveKemSelection.sampleFamily (simulateQ (kemAmbientImpl setup.baseImpl) setup.kem.keygen) count >>=
        fun others => preOpaquePool (Reader := Reader) setup codec checks ensureInit supplied decision work runtime count
          selected index chosen others) := by
  refine LawEq.trans ?_ (LazyOracleDiscard.lawEq_swap _ _ _).symm
  unfold sourcePreOpaque
  refine LawEq.bind (LawEq.refl _) fun born => ?_
  rcases born with ⟨_ | created, after⟩
  · exact (LazyOracleDiscard.lawEq_drop _ _).symm
  · exact LawEq.refl _

/-- Item 2's prefix at a given draw of the challenger: the prephase at the drawn pool, returning the table cache at the cut, the selected key pair, the prechallenge context and the challenge ciphertext (the result type of `PqxdhRegistrationJointKemPostSkeleton.sharedStart`). -/
noncomputable def startPool (count : ℕ) (selected : Fin (count + 1)) (index : ℕ) (p : Params KemSK count) :
    ProbComp (PqxdhSecretInputKdf.HmacOracle.QueryCache ×
      (Pair KemSK × OpaqueContext Reader KemSK A X count × MlKem768Ciphertext)) := do
  let context ← preOpaquePool (Reader := Reader) setup codec checks ensureInit supplied decision work runtime count
    selected index p.chosen p.others
  pure (cacheOf context, (p.chosen, context, p.challenge))

/-- The draw swap (design-v2 section 8.3, step 1; S13): item 2's prefix `sharedStart` has the law of the challenger's draws `drawParams` (selected key pair, family, challenge encapsulation) followed by the prephase at the drawn pool. The family moves before the constructor (`preOpaque_pool`) and the encapsulation before the prephase, which does not read it. -/
theorem draws_swap (count : ℕ) (selected : Fin (count + 1)) (index : ℕ) :
    LawEq (sharedStart (Reader := Reader) setup codec checks ensureInit supplied decision work runtime count selected
        index)
      (drawParams setup count >>= startPool (Reader := Reader) setup codec checks ensureInit supplied decision work
        runtime count selected index) := by
  unfold sharedStart drawParams startPool
  simp only [bind_assoc, pure_bind]
  refine LawEq.bind (LawEq.refl _) fun chosen => ?_
  refine (LawEq.bind (preOpaque_pool setup codec checks ensureInit supplied decision work runtime count selected index
    chosen) fun context => LawEq.refl _).trans ?_
  simp only [bind_assoc]
  refine LawEq.bind (LawEq.refl _) fun others => ?_
  exact LazyOracleDiscard.lawEq_swap _ _ _

end Swap

/-! ### Item 2's `n`-slot ideal world, pointwise in the challenger's draws -/

section Slots
variable {ι : Type} {baseSpec : OracleSpec ι} {Reader Response A X : Type}
  (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
  (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes) (decision : X → Bool)
  (work : OracleComp (SourceSpec KemSK) X) (runtime : A)

/-- Item 2's factored root client (`PqxdhRegistrationJointKemEntryFactor.entryClient`) at a given draw of the challenger: the prefix at the drawn pool, then the skeleton's post-challenge phase with the factored services. -/
noncomputable def entryClientAt (count : ℕ) (selected : Fin (count + 1)) (index : ℕ) (p : Params KemSK count) :
    OracleComp (EntrySpec Output) Bool :=
  internalizeV (startPool (Reader := Reader) setup codec checks ensureInit supplied decision work runtime count selected
      index p)
    (fun context => postSkel setup codec checks decision count selected (factoredServices setup codec checks) context.1
      context.2.2 context.2.1)

/-- Item 2's `n`-slot ideal world (`PqxdhRegistrationJointKemSecondEntry.slotGame`) at a given draw of the challenger. -/
noncomputable def slotGameAt (count : ℕ) (selected : Fin (count + 1)) (index n : ℕ) (p : Params KemSK count) :
    ProbComp Bool :=
  (simulateQ (slotImpl (D := PqxdhCorrelatedExtractFamily.Message) (PqxdhRegistrationJointKemSecondEntry.tableService
      (n := n)))
    (entryClientAt (Reader := Reader) setup codec checks ensureInit supplied decision work runtime count selected index
      p)).run' (emptyAlloc, PqxdhRecordLiftLazyTable.initial)

/-- A lifted probabilistic computation passes through the first-touch allocator with the allocator and service state unchanged. -/
theorem slot_liftComp {S α : Type} {n : ℕ} (service : PqxdhRegistrationJointKemSecondEntry.SlotService S Output n)
    (start : ProbComp α) (state : PqxdhRegistrationJointKemSecondEntry.Alloc PqxdhCorrelatedExtractFamily.Message n × S) :
    (simulateQ (slotImpl service) (OracleComp.liftComp start (EntrySpec Output))).run state =
      (fun value => (value, state)) <$> start := by
  rw [slotImpl, QueryImpl.simulateQ_add_liftComp_left, simulateQ_liftTarget, simulateQ_ofLift_eq_self]
  change (StateT.lift start : StateT _ ProbComp α).run state = _
  rw [StateT.run_lift, map_eq_bind_pure_comp]
  rfl

/-- Item 2's internalized client through the first-touch allocator: its prefix, then the post-challenge phase with the table cache at the cut held inside. -/
theorem internalize_run {C S : Type} {n : ℕ} (service : PqxdhRegistrationJointKemSecondEntry.SlotService S Output n)
    (start : ProbComp (PqxdhSecretInputKdf.HmacOracle.QueryCache × C))
    (post : C → OracleComp (PqxdhRegistrationJointKemPostSkeleton.SkelSpec Output) Bool)
    (state : PqxdhRegistrationJointKemSecondEntry.Alloc PqxdhCorrelatedExtractFamily.Message n × S) :
    (simulateQ (slotImpl service) (internalizeV start post)).run' state =
      start >>= fun q => (simulateQ (slotImpl service)
        ((simulateQ (PqxdhRegistrationJointKemEntryFactor.publicLocalV Output) (post q.2)).run' q.1)).run' state := by
  rw [internalizeV, simulateQ_bind, StateT.run'_eq, StateT.run_bind, slot_liftComp, bind_map_left, map_bind]
  rfl

/-- The draw swap in item 2's `n`-slot ideal world (at `n = 2`, item 2's two-slot ideal world): the `n`-slot world has the distribution of the challenger's draws followed by the same world at the drawn parameters. -/
theorem slotGame_pool (count : ℕ) (selected : Fin (count + 1)) (index n : ℕ) :
    𝒟[slotGame setup codec checks ensureInit supplied decision work runtime count selected index n] =
      𝒟[drawParams setup count >>= slotGameAt (Reader := Reader) setup codec checks ensureInit supplied decision work
        runtime count selected index n] := by
  unfold slotGame slotGameAt entryClientAt entryClient
  simp only [internalize_run]
  refine (draws_swap setup codec checks ensureInit supplied decision work runtime count selected index Bool _).trans ?_
  rw [bind_assoc]

end Slots

end BeaconcryptCore.Computational.PqxdhDeploymentIdealParams

-- Axiom guards (generated)

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealParams.ofCE_kem' does not depend on any axioms
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealParams.ofCE_kem

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealParams.ofCE_accept' does not depend on any axioms
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealParams.ofCE_accept

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealParams.pool_length' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealParams.pool_length

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealParams.pool_kem' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealParams.pool_kem

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealParams.pool_other' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealParams.pool_other

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealParams.pool_eq' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealParams.pool_eq

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealParams.preOpaque_pool' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealParams.preOpaque_pool

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealParams.draws_swap' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealParams.draws_swap

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealParams.slot_liftComp' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealParams.slot_liftComp

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealParams.internalize_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealParams.internalize_run

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealParams.slotGame_pool' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealParams.slotGame_pool
