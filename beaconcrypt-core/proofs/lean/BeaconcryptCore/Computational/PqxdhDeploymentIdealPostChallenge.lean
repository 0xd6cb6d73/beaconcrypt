-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhDeploymentIdealPostFinish

/-!
# Owner k's challenge finish through item 2's layers (CE-11b, unit U6, fourth part)

After an active selected accept, the middle source handler answers a finish of the selected owner k in the `initSent` phase by the ideal registration's challenge finish (`PqxdhDeploymentIdealSteps.finishStep`, `finishChallenge`): the native grouped owner `groupedOwnerCE` under `ownerImplCE` with the factored hidden services, past the first-touch allocator and item 2's lazy table. Item 2's upper layers answer it by the grouped owner (`PqxdhRegistrationJointKemPostSkeleton.groupedOwner`) at the encoded owner, and item 2's service layers answer the skeleton's requests. This module proves `PqxdhDeploymentIdealPostHidden.StepAtC` for that finish, and with `PqxdhDeploymentIdealPostFinish.step_finish` for every finish after an active selected accept.

- Relabelling: the opaque preparation and collection (`PqxdhBeaconPhase2Shared.prepare`, `collect`) are natural in the owner's identity, KEM key and identity-conversion types for one owner (`RelabelCalls`, `collect_relabel`, `prepare_relabel`); item 2's encoded owner (identity index, public key with KEM index) and the native owner (identity seed, key pair) are related through it.
- The preparation through item 2's layers: the post-challenge router answers the decapsulation of the challenge ciphertext at the selected index from its placeholder candidate without a CCA query (`reservation_selected`, `post_target`), and item 2's marked preparation returns the challenge marker (`stack_target`); every other preparation request is item 2's marked preparation with known handles under the actual services, which changes only transcripts that item 2's view erases (`prepItem`, `prepKnown_erase`, `stack_prepQuery`, `stack_prepProgram`). Item 2's answers relabel the native answers with the challenge handle (`prep_calls`), which keep the CE-native state (`slot_prep`).
- The grouped request: a known decapsulation result is item 2's native grouped answer on both sides (`slot_known` with `PqxdhDeploymentIdealPostFinish.stack_known`); the challenge marker is `PqxdhDeploymentIdealSteps.groupCE_challenge` carried through item 2's table layers to the allocator (`tableLayer_flat`, `stack_challenge`, `groupCE_keep`, `stack_challengeC`).
- `owner_challenge`: owner k's grouped owner through item 2's layers is the CE-native grouped owner past the allocator, projected.
- The allocator keeps a good state and every value it represents (`slot_keep`, `slot_keepProgram`), so the hidden read leaves item 2's view of the mark unchanged.
- The middle side and the step: `rejoin_set`, `afterChallenge`, `finishStep_challenge`, `finishChallenge_found`, `sourceMid_challenge`, and `step_challenge`, with hypotheses that the finish is owner k's challenge finish, item 2's ownership invariant, the addressed owner's KEM index the selected one, a prefix KEM pool, a good allocator state and a stored value at the mark's coordinates. `finish_other` derives the premise of `step_finish` about the addressed owner from the finish not being owner k's challenge finish, the active flag and the owner's KEM index being its position; `step_finishActive` combines both steps for every finish after an active selected accept.

These are program equalities and support facts of the allocator. They charge nothing and make no security claim.
-/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc

set_option autoImplicit false

namespace BeaconcryptCore.Computational.PqxdhDeploymentIdealPostChallenge
open PqxdhBeaconPhase2Shared (Secrets Inputs Prepared Query Spec collect prepare afterInputs admitted)
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhKemIndCca (MlKem768PublicKey MlKem768Ciphertext MlKemSharedSecret)
open PqxdhRefinement (absBytes)

/-! ### Relabelling the owner's identity, key and conversion types -/

section Relabel
variable {I₁ I₂ K₁ K₂ X₁ X₂ D Response S : Type}

/-- Two interpretations of the opaque preparation interface at different identity, KEM key and identity-conversion types that agree on one owner: the owner's identity converts to `x₁` and `x₂`, its keys decapsulate alike, the converted identities compute the same DH outputs, and every other request is answered alike. -/
structure RelabelCalls {m : Type → Type} [Monad m] (source : QueryImpl (Spec I₁ D K₁ X₁ Response S) m)
    (target : QueryImpl (Spec I₂ D K₂ X₂ Response S) m) (identity₁ : I₁) (identity₂ : I₂) (kem₁ : K₁) (kem₂ : K₂)
    (x₁ : X₁) (x₂ : X₂) : Prop where
  decode : ∀ raw, target (.decode raw) = source (.decode raw)
  ciphertext : ∀ response, target (.ciphertext response) = source (.ciphertext response)
  ephemeral : ∀ response, target (.ephemeral response) = source (.ephemeral response)
  serverIdentity : ∀ response, target (.serverIdentity response) = source (.serverIdentity response)
  publicConversion : ∀ value, target (.publicConversion value) = source (.publicConversion value)
  privateSource : source (.privateConversion identity₁) = pure (some x₁)
  privateTarget : target (.privateConversion identity₂) = pure (some x₂)
  decapsulate : ∀ ciphertext, target (.decapsulate ciphertext kem₂) = source (.decapsulate ciphertext kem₁)
  dhPair : ∀ pair publicValue, target (.dhPair pair publicValue) = source (.dhPair pair publicValue)
  dhIdentity : ∀ publicValue, target (.dhIdentity x₂ publicValue) = source (.dhIdentity x₁ publicValue)
  assignedId : ∀ response, target (.assignedId response) = source (.assignedId response)
  eraseShared : ∀ secrets, target (.eraseShared secrets) = source (.eraseShared secrets)

/-- The collection is natural in the owner's identity, key and conversion types. -/
theorem collect_relabel {m : Type → Type} [Monad m] [LawfulMonad m]
    (source : QueryImpl (Spec I₁ D K₁ X₁ Response S) m) (target : QueryImpl (Spec I₂ D K₂ X₂ Response S) m)
    (identity₁ : I₁) (identity₂ : I₂) (kem₁ : K₁) (kem₂ : K₂) (x₁ : X₁) (x₂ : X₂)
    (calls : RelabelCalls source target identity₁ identity₂ kem₁ kem₂ x₁ x₂) (prekey oneTime : D)
    (raw : PqxdhBeaconPhase2Preparation.Bytes) :
    simulateQ target (collect identity₂ prekey oneTime kem₂ raw) =
      simulateQ source (collect identity₁ prekey oneTime kem₁ raw) := by
  simp only [collect, OptionT.run_bind, OptionT.run_mk,
    OptionT.run_pure, OptionT.run_monadLift, Option.elimM, bind_map_left,
    simulateQ_bind, simulateQ_spec_query]
  simp only [calls.decode]
  congr 1
  funext response
  cases response <;> simp only [Option.elim_none, Option.elim_some, simulateQ_pure]
  repeat' (
    simp only [simulateQ_bind, simulateQ_spec_query, simulateQ_pure, pure_bind, calls.ciphertext, calls.ephemeral,
      calls.serverIdentity, calls.publicConversion, calls.privateSource, calls.privateTarget, calls.decapsulate, calls.dhPair, calls.dhIdentity, calls.assignedId,
      Option.elim_none, Option.elim_some]
    first | rfl | (congr 1; funext reply; cases reply))
  all_goals simp only [Option.elim, simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
    id_map, simulateQ_pure, calls.assignedId]

/-- The opaque preparation is natural in the owner's identity, key and conversion types. -/
theorem prepare_relabel {m : Type → Type} [Monad m] [LawfulMonad m]
    (source : QueryImpl (Spec I₁ D K₁ X₁ Response S) m) (target : QueryImpl (Spec I₂ D K₂ X₂ Response S) m)
    (identity₁ : I₁) (identity₂ : I₂) (kem₁ : K₁) (kem₂ : K₂) (x₁ : X₁) (x₂ : X₂)
    (calls : RelabelCalls source target identity₁ identity₂ kem₁ kem₂ x₁ x₂)
    (control : beaconcrypt_core.pqxdh.BeaconInitSent) (prekey oneTime : D) (raw : PqxdhBeaconPhase2Preparation.Bytes) :
    simulateQ target (prepare control identity₂ prekey oneTime kem₂ raw) =
      simulateQ source (prepare control identity₁ prekey oneTime kem₁ raw) := by
  simp only [prepare, simulateQ_bind, collect_relabel source target identity₁ identity₂ kem₁ kem₂ x₁ x₂ calls]
  refine bind_congr fun inputs => ?_
  rcases inputs with _ | inputs
  · simp only [simulateQ_pure]
  · simp only [afterInputs, simulateQ_bind, simulateQ_spec_query, simulateQ_pure, calls.eraseShared]

end Relabel

/-! ### The preparation of owner k's challenge finish through item 2's layers -/

section Prep
open PqxdhRegistrationJointKemPostSkeleton (OwnerSpec PreSpec SkelState)
open PqxdhRegistrationJointKemEntryFactor (Output)
open PqxdhDeploymentIdealPostSim (ServiceState SlotState)
open PqxdhDeploymentIdealPostHidden (lowerEC eraseServiceC eraseTables)
open PqxdhDeploymentIdealPostFinish (stackRun stackRun_pure stackRun_bind preparationKnown targetPrep)
open PqxdhDeploymentIdealParams (Target Params)
open PqxdhPhase2DecapsulationRouting (Shared)
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}
  (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks) {count : ℕ}
  (t : Target count) (p : Params KemSK count) (created : PqxdhLiveServerConstruction.Created Unit)

/-- The post-challenge router's reservation at the selected creation index holds the selected public key without its secret. -/
theorem reservation_selected :
    PqxdhDynamicKemRouter.selectedReservation t.kem p.chosen.1 p.others t.kem.val = some (p.chosen.1, none) := by
  rw [← PqxdhDynamicKemRouter.selected_reservation, ← PqxdhDeploymentIdealParams.pool_eq]
  simp [PqxdhDynamicKemRouter.redact, PqxdhDeploymentIdealParams.pool_kem t p]

/-- The post-challenge router answers the decapsulation of the challenge ciphertext at the created selected index from its placeholder candidate, without a CCA query. -/
theorem post_target (state : PqxdhDynamicKemJointSource.State KemSK) (made : t.kem.val < state.2.created) :
    ((PqxdhDeploymentIdealPostRequests.postRouter setup t.kem p.chosen p.others p.challenge
        (.inr (.inr (.decapsulate t.kem.val p.challenge)))).run).run state =
      pure (some (some PqxdhRegistrationJointBeaconOpaqueFinishRouter.placeholder),
        (state.1, PqxdhDynamicKemRouter.record (.decapsulate t.kem.val p.challenge)
          (some PqxdhRegistrationJointBeaconOpaqueFinishRouter.placeholder) state.2)) := by
  simp [PqxdhDeploymentIdealPostRequests.postRouter, PqxdhDynamicKemJointRouter.post,
    PqxdhDynamicKemJointRouter.combine, PqxdhDynamicKemRouter.post, PqxdhDynamicKemRouter.router,
    PqxdhDynamicKemRouter.postDecapsulation, PqxdhDynamicKemRouter.lookup, made, reservation_selected t p,
    StateT.run, OptionT.run_mk]
  rfl

/-- The selected challenge decapsulation of the preparation through item 2's layers: the post-challenge router answers from its placeholder candidate without a CCA query, and item 2's marked preparation returns the challenge marker; the skeleton state and item 2's view of the router state are kept. -/
theorem stack_target (ciphertext : PqxdhBeaconPhase2Preparation.Ciphertext) (pk : MlKem768PublicKey)
    (same : PqxdhPhase2InputBytes.ciphertext ciphertext = p.challenge)
    (joint : PqxdhDynamicIdentityPool.SourceState) (pool : PqxdhLiveKemBirth.Pool KemSK) (made : t.kem.val < pool.keys.length)
    (tables : PqxdhSecretInputKdf.HmacOracle.QueryCache × SlotState) (skel : SkelState KemSK Output) :
    stackRun setup codec checks t p created
        ((OwnerSpec Response).query (.inl (.decapsulate ciphertext (pk, t.kem.val))) : OracleComp (OwnerSpec Response) _)
        skel (eraseServiceC ((joint, PqxdhDeploymentIdealPoolSource.routerOf pool), tables)) =
      pure (some (some Shared.challenge, skel), eraseServiceC ((joint, PqxdhDeploymentIdealPoolSource.routerOf pool), tables)) := by
  unfold stackRun
  rw [simulateQ_spec_query]
  change ((simulateQ (lowerEC setup t p) ((simulateQ (PqxdhRegistrationJointKemPostSkeleton.skelImpl setup codec checks
    created.server.server.metadata.identityIndex created.publicIdentity
      (PqxdhRegistrationJointKemEntryFactor.factoredServices setup codec checks))
    (simulateQ (PqxdhRegistrationJointKemPostSkeleton.groupedPoolLift (Response := Response))
      (PqxdhRegistrationJointBeaconOpaqueFinish.markedPreparation setup codec t.kem.val p.challenge
        (.decapsulate ciphertext (pk, t.kem.val))))).run skel)).run).run _ = _
  rw [PqxdhDeploymentIdealPostFinish.skel_groupedPool, simulateQ_map, OptionT.run_map, StateT.run_map]
  have run := PqxdhRegistrationJointKemObserverFree.run_eraseOption eraseServiceC
    PqxdhDeploymentIdealPostHidden.eraseServiceC_idem _
    (PqxdhDeploymentIdealPostHidden.serviceLayer_neverReadC setup t.kem p.chosen p.others p.challenge)
    (simulateQ PqxdhDeploymentIdealPostRequests.poolUp (PqxdhRegistrationJointBeaconOpaqueFinish.markedPreparation setup
      codec t.kem.val p.challenge (.decapsulate ciphertext (pk, t.kem.val))))
    ((joint, PqxdhDeploymentIdealPoolSource.routerOf pool), tables)
  rw [← run, PqxdhDeploymentIdealPostRequests.service_poolProgram]
  simp only [PqxdhRegistrationJointBeaconOpaqueFinish.markedPreparation]
  rw [same, simulateQ_map, simulateQ_spec_query, OptionT.run_map, StateT.run_map]
  rw [post_target setup t p (joint, PqxdhDeploymentIdealPoolSource.routerOf pool) made]
  simp only [PqxdhDynamicKemPost.evaluate]
  rfl

/-- Item 2's answers to the preparation requests of owner k's finish, from the private pools: the selected challenge decapsulation answers the challenge marker, every other request is answered as item 2's marked preparation with known handles under the actual services. -/
noncomputable def prepItem (joint : PqxdhDynamicIdentityPool.SourceState) (pool : PqxdhLiveKemBirth.Pool KemSK) :
    QueryImpl (PreSpec Response) ProbComp
  | .decapsulate ciphertext key =>
      if key.2 = t.kem.val ∧ PqxdhPhase2InputBytes.ciphertext ciphertext = p.challenge then pure (some Shared.challenge)
      else Prod.fst <$> (simulateQ (PqxdhLiveKemBirth.impl setup.baseImpl setup.joint setup.kem)
        (preparationKnown setup codec (.decapsulate ciphertext key))).run (joint, pool)
  | query => Prod.fst <$> (simulateQ (PqxdhLiveKemBirth.impl setup.baseImpl setup.joint setup.kem)
      (preparationKnown setup codec query)).run (joint, pool)

set_option backward.isDefEq.respectTransparency false in
/-- A preparation request with known handles under the actual services changes the private pools only in their transcripts, which item 2's view erases. -/
theorem prepKnown_erase (query : (PreSpec Response).Domain) (joint : PqxdhDynamicIdentityPool.SourceState)
    (pool : PqxdhLiveKemBirth.Pool KemSK) :
    (fun result => (result.1, PqxdhRegistrationJointKemObserverFree.eraseJoint
        (result.2.1, PqxdhDeploymentIdealPoolSource.routerOf result.2.2))) <$>
        (simulateQ (PqxdhLiveKemBirth.impl setup.baseImpl setup.joint setup.kem) (preparationKnown setup codec query)).run
          (joint, pool) =
      (fun result => (result.1, PqxdhRegistrationJointKemObserverFree.eraseJoint
        (joint, PqxdhDeploymentIdealPoolSource.routerOf pool))) <$>
        (simulateQ (PqxdhLiveKemBirth.impl setup.baseImpl setup.joint setup.kem) (preparationKnown setup codec query)).run
          (joint, pool) := by
  cases query
  case decapsulate ciphertext key =>
    simp only [preparationKnown, simulateQ_map, simulateQ_spec_query, StateT.run_map, Functor.map_map]
    change _ <$> ((fun result => (result.1, (joint, result.2))) <$>
      (PqxdhLiveKemBirth.poolImpl setup.baseImpl setup.kem
        (.decapsulate key.2 (PqxdhPhase2InputBytes.ciphertext ciphertext))).run pool) =
      _ <$> ((fun result => (result.1, (joint, result.2))) <$>
      (PqxdhLiveKemBirth.poolImpl setup.baseImpl setup.kem
        (.decapsulate key.2 (PqxdhPhase2InputBytes.ciphertext ciphertext))).run pool)
    simp only [PqxdhLiveKemBirth.poolImpl, StateT.run, Functor.map_map]
    split <;> simp only [pure_bind, map_pure, map_bind] <;> rfl
  case dhIdentity index point =>
    simp only [preparationKnown, simulateQ_map, simulateQ_spec_query, StateT.run_map, Functor.map_map]
    change _ <$> ((fun result => (result.1, (result.2, pool))) <$>
      (PqxdhDynamicIdentityPool.lazyImpl setup.joint
        (.inr (.service index (.staticDh (PqxdhPhase2GapDhSource.peer point))))).run joint) =
      _ <$> ((fun result => (result.1, (result.2, pool))) <$>
      (PqxdhDynamicIdentityPool.lazyImpl setup.joint
        (.inr (.service index (.staticDh (PqxdhPhase2GapDhSource.peer point))))).run joint)
    simp only [PqxdhDynamicIdentityPool.lazyImpl, PqxdhDynamicIdentityPool.poolImpl, StateT.run, map_pure]
    rfl
  all_goals rfl

/-- A preparation request of owner k's finish through item 2's layers, from the erased router state of a prefix pool in which the selected key is created: item 2's answer `prepItem`, with the skeleton state and item 2's view of the service state kept. -/
theorem stack_prepQuery (query : (PreSpec Response).Domain) (joint : PqxdhDynamicIdentityPool.SourceState)
    (pool : PqxdhLiveKemBirth.Pool KemSK) (prefixed : PqxdhDeploymentIdealPoolSource.PoolPrefix (p.pool t) pool)
    (made : t.kem.val < pool.keys.length) (tables : PqxdhSecretInputKdf.HmacOracle.QueryCache × SlotState)
    (skel : SkelState KemSK Output) :
    stackRun setup codec checks t p created ((OwnerSpec Response).query (.inl query) : OracleComp (OwnerSpec Response) _)
        skel (eraseServiceC ((joint, PqxdhDeploymentIdealPoolSource.routerOf pool), tables)) =
      (fun answer => (some (answer, skel), eraseServiceC ((joint, PqxdhDeploymentIdealPoolSource.routerOf pool), tables))) <$>
        prepItem setup codec t p joint pool query := by
  by_cases target : targetPrep t.kem.val p.challenge query
  · rcases query with _ | _ | _ | _ | _ | _ | ⟨ciphertext, ⟨pk, index⟩⟩ | _ | _ | _ | _
    all_goals try exact target.elim
    obtain ⟨selected, same⟩ := target
    simp only at selected
    subst selected
    rw [stack_target setup codec checks t p created ciphertext pk same joint pool made tables skel]
    simp only [prepItem, same, and_self, ↓reduceIte, map_pure]
  · have free : OracleComp.IsQueryBoundP ((PreSpec Response).query query : OracleComp (PreSpec Response) _)
        (targetPrep t.kem.val p.challenge) 0 := by
      rw [isQueryBoundP_query_iff]
      exact fun hit => absurd hit target
    have stack := PqxdhDeploymentIdealPostFinish.stack_prep setup codec checks t p created _ free joint pool prefixed
      tables skel
    rw [simulateQ_spec_query, simulateQ_spec_query] at stack
    rw [stack]
    have answer : prepItem setup codec t p joint pool query = Prod.fst <$>
        (simulateQ (PqxdhLiveKemBirth.impl setup.baseImpl setup.joint setup.kem)
          (preparationKnown setup codec query)).run (joint, pool) := by
      rcases query with _ | _ | _ | _ | _ | _ | ⟨ciphertext, key⟩ | _ | _ | _ | _
      all_goals try rfl
      simp only [targetPrep] at target
      simp only [prepItem, target, ↓reduceIte]
    rw [answer, Functor.map_map]
    have erased := congrArg (fun work => (fun result => (some (result.1, skel), (result.2,
      PqxdhDeploymentIdealPostHidden.eraseTables tables))) <$> work) (prepKnown_erase setup codec query joint pool)
    simp only [Functor.map_map] at erased
    exact erased

/-- The preparation of owner k's finish through item 2's layers is item 2's answers `prepItem`, with the skeleton state and item 2's view of the service state kept. -/
theorem stack_prepProgram {β : Type} (work : OracleComp (PreSpec Response) β) (joint : PqxdhDynamicIdentityPool.SourceState)
    (pool : PqxdhLiveKemBirth.Pool KemSK) (prefixed : PqxdhDeploymentIdealPoolSource.PoolPrefix (p.pool t) pool)
    (made : t.kem.val < pool.keys.length) (tables : PqxdhSecretInputKdf.HmacOracle.QueryCache × SlotState)
    (skel : SkelState KemSK Output) :
    stackRun setup codec checks t p created
        (simulateQ (fun query => ((OwnerSpec Response).query (.inl query) : OracleComp (OwnerSpec Response) _)) work) skel
        (eraseServiceC ((joint, PqxdhDeploymentIdealPoolSource.routerOf pool), tables)) =
      (fun answer => (some (answer, skel), eraseServiceC ((joint, PqxdhDeploymentIdealPoolSource.routerOf pool), tables))) <$>
        simulateQ (prepItem setup codec t p joint pool) work := by
  induction work using OracleComp.inductionOn with
  | pure value => simp only [simulateQ_pure, stackRun_pure, map_pure]
  | query_bind query next ih =>
      rw [simulateQ_bind, simulateQ_spec_query, stackRun_bind,
        stack_prepQuery setup codec checks t p created query joint pool prefixed made tables skel, bind_map_left,
        simulateQ_bind, simulateQ_spec_query, map_bind]
      refine bind_congr fun answer => ?_
      exact ih answer

end Prep

/-! ### The grouped request of owner k's challenge finish -/

section Group
open PqxdhRegistrationJointKemPostSkeleton (OwnerSpec SkelSpec SkelState Pending clean)
open PqxdhRegistrationJointKemEntryFactor (Output factoredHidden factoredServices publicLocalV)
open PqxdhDeploymentIdealPostSim (ServiceState SlotState tableLayer)
open PqxdhDeploymentIdealPostHidden (lowerEC eraseServiceC eraseTables)
open PqxdhDeploymentIdealPostFinish (stackRun)
open PqxdhDeploymentIdealSteps (groupCE liftS)
open PqxdhDeploymentIdealSlots (Coord SlotSpec)
open PqxdhDeploymentIdealParams (Target Params)
open PqxdhPhase2DecapsulationRouting (Shared)
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}
  (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks) {count : ℕ}
  (t : Target count) (p : Params KemSK count) (created : PqxdhLiveServerConstruction.Created Unit)

/-- Item 2's table layers are its public-table layer followed by the CE allocator in front of the lazy table, up to reassociation. -/
theorem tableLayer_flat {α : Type} (work : OracleComp (SkelSpec Output) α) (cache : PqxdhSecretInputKdf.HmacOracle.QueryCache)
    (slots : SlotState) :
    (simulateQ tableLayer work).run (cache, slots) =
      (fun z : (α × PqxdhSecretInputKdf.HmacOracle.QueryCache) × SlotState => (z.1.1, (z.1.2, z.2))) <$>
        (simulateQ (PqxdhRegistrationJointKemSecondEntry.slotImpl PqxdhDeploymentSeedSplit.tableService)
          ((simulateQ (publicLocalV Output) work).run cache)).run slots := by
  have nested := OracleComp.simulateQ_mapStateTBase_run_eq_map_flattenStateT
    (PqxdhRegistrationJointKemSecondEntry.slotImpl (D := PqxdhCorrelatedExtractFamily.Message)
      (PqxdhRegistrationJointKemSecondEntry.tableService (n := 2)))
    (publicLocalV Output) work cache slots
  have back := congrArg (fun run => (fun z : (α × PqxdhSecretInputKdf.HmacOracle.QueryCache) × SlotState =>
    (z.1.1, (z.1.2, z.2))) <$> run) nested
  simp only [Functor.map_map] at back
  rw [show (cache, slots) = ((cache, slots).1, (cache, slots).2) from rfl]
  change _ = _ <$> (simulateQ (PqxdhRegistrationJointKemSecondEntry.slotImpl (D := PqxdhCorrelatedExtractFamily.Message)
      (PqxdhRegistrationJointKemSecondEntry.tableService (n := 2))) ((simulateQ (publicLocalV Output) work).run cache)).run
        slots
  rw [back]
  exact (id_map _).symm

/-- A known grouped request of owner k's challenge finish on the CE side: item 2's native grouped answer, lifted past the allocator, with the recorded coordinates kept. -/
theorem slot_known (hidden : Output → PqxdhRegistrationJointKemPostSkeleton.Hidden Response) (pending : Pending Response)
    (secret : MlKemSharedSecret) (marker : pending.root.shared = .known secret)
    (native : PqxdhServerAuthNative.NativeState KemSK) (recorded : Option Coord) (slots : SlotState) :
    (simulateQ (PqxdhRegistrationJointKemSecondEntry.slotImpl PqxdhDeploymentSeedSplit.tableService)
        ((groupCE setup codec hidden pending).run (native, recorded))).run slots =
      (fun r => ((r.1, (r.2, recorded)), slots)) <$>
        (PqxdhRegistrationJointKemPostSkeleton.groupNativeN setup codec (List.Vector.replicate 32 0) pending).run native := by
  rw [PqxdhDeploymentIdealSteps.groupCE_known setup codec hidden pending secret marker native recorded, simulateQ_map,
    StateT.run_map, PqxdhDeploymentIdealCut.slotImpl_lift, Functor.map_map]

/-- A grouped request with the challenge marker through item 2's layers, from a state that projects the CE-native state, is the CE-native answer `groupCE` with the factored hidden services past the allocator: the reply, the CE game state without ghosts, item 2's marks, item 2's view of the router state and the table cache are kept as on the CE side, and the allocator and table state are the CE's. -/
theorem stack_challenge (pending : Pending Response) (marker : pending.root.shared = .challenge)
    (joint : PqxdhDynamicKemJointSource.State KemSK) (native : PqxdhServerAuthNative.NativeState KemSK)
    (marks : PqxdhRegistrationJointKemPostSkeleton.Marks Output) (recorded : Option Coord) (slots : SlotState) :
    stackRun setup codec checks t p created ((OwnerSpec Response).query (.inr pending) : OracleComp (OwnerSpec Response) _)
        (clean native.2, marks) (eraseServiceC (joint, (native.1.cache, slots))) =
      (fun r => (some (r.1.1, (clean r.1.2.1.2, marks)), eraseServiceC (joint, (native.1.cache, r.2)))) <$>
        (simulateQ (PqxdhRegistrationJointKemSecondEntry.slotImpl PqxdhDeploymentSeedSplit.tableService)
          ((groupCE setup codec (factoredHidden setup codec checks) pending).run (native, recorded))).run slots := by
  unfold stackRun
  rw [simulateQ_spec_query, show PqxdhRegistrationJointKemPostSkeleton.groupedCompiler setup codec t.kem.val p.challenge
      (.inr pending) = (PqxdhRegistrationJointKemPostSkeleton.GSpec KemSK Response).query (.inr pending) from rfl,
    simulateQ_spec_query,
    show (PqxdhRegistrationJointKemPostSkeleton.skelImpl setup codec checks created.server.server.metadata.identityIndex
      created.publicIdentity (factoredServices setup codec checks) (.inr pending)).run (clean native.2, marks) =
      simulateQ (PqxdhRegistrationJointKemPostSkeleton.fwd (T := PqxdhRegistrationJointKemPostSkeleton.TSpec Output)
        (PqxdhRegistrationJointKemPostSkeleton.coinLift (KemSK := KemSK)))
        ((PqxdhRegistrationJointKemPostSkeleton.groupStep setup codec (factoredServices setup codec checks) pending).run
          (clean native.2, marks)) from rfl,
    PqxdhDeploymentIdealPostHidden.lowerEC_native, tableLayer_flat]
  have key := congrArg (fun work => (simulateQ (PqxdhRegistrationJointKemSecondEntry.slotImpl
      PqxdhDeploymentSeedSplit.tableService) work).run slots)
    (PqxdhDeploymentIdealSteps.groupCE_challenge setup codec checks pending marker native recorded marks native.1.cache)
  simp only [simulateQ_map, StateT.run_map] at key
  have mapped := congrArg (fun work => (fun w : (Option PqxdhBeaconPhase2Publication.Staged ×
      PqxdhJointDhExtractFamily.State × PqxdhServerAuthExperiment.GameState KemSK × Option Coord ×
        PqxdhRegistrationJointKemPostSkeleton.Marks Output × PqxdhSecretInputKdf.HmacOracle.QueryCache) × SlotState =>
      (some (w.1.1, (w.1.2.2.1, w.1.2.2.2.2.1)), (PqxdhRegistrationJointKemObserverFree.eraseJoint joint,
        eraseTables (w.1.2.2.2.2.2, w.2)))) <$> work) key
  simp only [Functor.map_map] at mapped
  simp only [Functor.map_map]
  exact mapped.symm

/-- The CE-native grouped request with the challenge marker keeps the first component (the Extract family state) of the native state. -/
theorem groupCE_keep (hidden : Output → PqxdhRegistrationJointKemPostSkeleton.Hidden Response) (pending : Pending Response)
    (marker : pending.root.shared = .challenge) (native : PqxdhServerAuthNative.NativeState KemSK) (recorded : Option Coord) :
    (groupCE setup codec hidden pending).run (native, recorded) =
      (fun r => (r.1, ((native.1, r.2.1.2), r.2.2))) <$> (groupCE setup codec hidden pending).run (native, recorded) := by
  simp only [groupCE, StateT.run, marker]
  split_ifs
  · simp only [PqxdhServerAuthNative.nativeCtx, StateT.run, map_bind, map_pure]
    refine bind_congr fun value => ?_
    simp only [liftS, OracleComp.liftComp_map, bind_map_left]
  · simp only [map_pure]

/-- `stack_challenge` with the CE result's Extract family state in item 2's table cache. -/
theorem stack_challengeC (pending : Pending Response) (marker : pending.root.shared = .challenge)
    (joint : PqxdhDynamicKemJointSource.State KemSK) (native : PqxdhServerAuthNative.NativeState KemSK)
    (marks : PqxdhRegistrationJointKemPostSkeleton.Marks Output) (recorded : Option Coord) (slots : SlotState) :
    stackRun setup codec checks t p created ((OwnerSpec Response).query (.inr pending) : OracleComp (OwnerSpec Response) _)
        (clean native.2, marks) (eraseServiceC (joint, (native.1.cache, slots))) =
      (fun r => (some (r.1.1, (clean r.1.2.1.2, marks)), eraseServiceC (joint, (r.1.2.1.1.cache, r.2)))) <$>
        (simulateQ (PqxdhRegistrationJointKemSecondEntry.slotImpl PqxdhDeploymentSeedSplit.tableService)
          ((groupCE setup codec (factoredHidden setup codec checks) pending).run (native, recorded))).run slots := by
  rw [stack_challenge setup codec checks t p created pending marker joint native marks recorded slots]
  conv_rhs => rw [groupCE_keep setup codec (factoredHidden setup codec checks) pending marker native recorded]
  rw [simulateQ_map, StateT.run_map, Functor.map_map]

end Group

/-! ### Item 2's preparation answers against the native ones -/

section Calls
open PqxdhRegistrationJointKemPostSkeleton (PreSpec)
open PqxdhDeploymentIdealSteps (PreSpecCE OwnerSpecCE preparationCE ownerImplCE liftS)
open PqxdhDeploymentIdealSlots (Coord)
open PqxdhDeploymentIdealPostFinish (preparationKnown)
open PqxdhDeploymentIdealParams (Target Params)
open PqxdhPhase2DecapsulationRouting (Shared)
open PqxdhRegistrationJointKemEntryFactor (Output)
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}
  (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) {count : ℕ}
  (t : Target count) (p : Params KemSK count)

set_option backward.isDefEq.respectTransparency false in
/-- Item 2's answers to owner k's preparation requests relabel the native answers with the challenge handle (`PqxdhDeploymentIdealSteps.preparationCE`): the owner's identity index holds its seed and the selected KEM index holds its key pair. -/
theorem prep_calls (joint : PqxdhDynamicIdentityPool.SourceState) (pool : PqxdhLiveKemBirth.Pool KemSK)
    (identityIndex : ℕ) (seed : PqxdhJointIdentity.IdentitySeed) (keys : MlKem768PublicKey × KemSK)
    (identityOwned : joint.seeds[identityIndex]? = some seed) (kemOwned : pool.keys[t.kem.val]? = some keys) :
    RelabelCalls (preparationCE (Response := Response) setup codec p.challenge) (prepItem setup codec t p joint pool) seed
      (PqxdhRegistrationJointBundle.identityMap setup identityIndex seed) keys
      (PqxdhRegistrationJointBundle.keyMap t.kem.val keys) seed identityIndex where
  decode _ := by simp [prepItem, preparationKnown, preparationCE]
  ciphertext _ := by simp [prepItem, preparationKnown, preparationCE]
  ephemeral _ := by simp [prepItem, preparationKnown, preparationCE]
  serverIdentity _ := by simp [prepItem, preparationKnown, preparationCE]
  publicConversion _ := by simp [prepItem, preparationKnown, preparationCE]
  privateSource := rfl
  privateTarget := by simp [prepItem, preparationKnown, PqxdhRegistrationJointBundle.identityMap]
  decapsulate ciphertext := by
    by_cases same : PqxdhPhase2InputBytes.ciphertext ciphertext = p.challenge
    · simp [prepItem, PqxdhRegistrationJointBundle.keyMap, same, preparationCE]
    · simp only [prepItem, PqxdhRegistrationJointBundle.keyMap, same, and_false, ↓reduceIte, preparationCE,
        preparationKnown, simulateQ_map, simulateQ_spec_query, StateT.run_map]
      change Prod.fst <$> (_ <$> ((fun result => (result.1, (joint, result.2))) <$>
        (PqxdhLiveKemBirth.poolImpl setup.baseImpl setup.kem
          (.decapsulate t.kem.val (PqxdhPhase2InputBytes.ciphertext ciphertext))).run pool)) = _
      simp only [PqxdhLiveKemBirth.poolImpl, StateT.run, kemOwned, Functor.map_map, bind_pure_comp]
  dhPair _ _ := by simp [prepItem, preparationKnown, preparationCE]
  dhIdentity point := by
    simp only [prepItem, preparationKnown, preparationCE, simulateQ_map, simulateQ_spec_query, StateT.run_map]
    change Prod.fst <$> (_ <$> ((fun result => (result.1, (result.2, pool))) <$>
      (PqxdhDynamicIdentityPool.lazyImpl setup.joint
        (.inr (.service identityIndex (.staticDh (PqxdhPhase2GapDhSource.peer point))))).run joint)) = _
    simp only [PqxdhDynamicIdentityPool.lazyImpl, PqxdhDynamicIdentityPool.poolImpl, StateT.run, identityOwned,
      Option.map_some, PqxdhJointIdentity.primitiveReply, map_pure, Option.join]
    rfl
  assignedId _ := by simp [prepItem, preparationKnown, preparationCE]
  eraseShared _ := by simp [prepItem, preparationKnown, preparationCE]

/-- The native preparation of owner k's challenge finish on the CE side keeps the CE-native state and the slot state: it is the native preparation callbacks with the challenge handle. -/
theorem slot_prep {β : Type} (hidden : Output → PqxdhRegistrationJointKemPostSkeleton.Hidden Response)
    (work : OracleComp (PreSpecCE KemSK Response) β) (state : PqxdhServerAuthNative.NativeState KemSK × Option Coord)
    (slots : PqxdhDeploymentIdealPostSim.SlotState) :
    (simulateQ (PqxdhRegistrationJointKemSecondEntry.slotImpl PqxdhDeploymentSeedSplit.tableService)
        ((simulateQ (ownerImplCE setup codec hidden p.challenge)
          (simulateQ (fun query => ((OwnerSpecCE KemSK Response).query (.inl query) :
            OracleComp (OwnerSpecCE KemSK Response) _)) work)).run state)).run slots =
      (fun value => ((value, state), slots)) <$> simulateQ (preparationCE setup codec p.challenge) work := by
  induction work using OracleComp.inductionOn with
  | pure value => simp
  | query_bind query next ih =>
      rw [simulateQ_bind, simulateQ_spec_query, simulateQ_bind, simulateQ_spec_query, StateT.run_bind,
        show (ownerImplCE setup codec hidden p.challenge (.inl query)).run state =
          (fun reply => (reply, state)) <$> liftS (preparationCE setup codec p.challenge query) from rfl,
        bind_map_left, simulateQ_bind, StateT.run_bind, PqxdhDeploymentIdealCut.slotImpl_lift, bind_map_left,
        simulateQ_bind, simulateQ_spec_query, map_bind]
      refine bind_congr fun reply => ?_
      exact ih reply

end Calls

/-! ### Owner k's challenge finish through item 2's layers -/

section Owner
open PqxdhRegistrationJointKemPostSkeleton (OwnerSpec PreSpec SkelState Pending clean groupedOwner)
open PqxdhRegistrationJointKemEntryFactor (Output factoredHidden)
open PqxdhDeploymentIdealPostSim (SlotState)
open PqxdhDeploymentIdealPostHidden (eraseServiceC)
open PqxdhDeploymentIdealPostFinish (stackRun stackRun_pure stackRun_bind)
open PqxdhDeploymentIdealSteps (OwnerSpecCE groupedOwnerCE preparationCE ownerImplCE)
open PqxdhDeploymentIdealSlots (Coord)
open PqxdhDeploymentIdealParams (Target Params)
open PqxdhPhase2DecapsulationRouting (Shared)
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}
  (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks) {count : ℕ}
  (t : Target count) (p : Params KemSK count) (created : PqxdhLiveServerConstruction.Created Unit)

/-- Owner k's grouped finish through item 2's layers, at the encoded owner with the selected KEM index, from a state that projects the private pools and the CE-native state, is the CE-native grouped owner `groupedOwnerCE` under `ownerImplCE` with the factored hidden services past the allocator, from no recorded coordinates, projected: the returned owner encoded, the skeleton's game state the CE one without ghosts, item 2's marks and item 2's view of the router state kept, and the table cache, the allocator and the table the CE's. It needs the owner's identity index to hold its seed, the selected KEM index to hold the owner's KEM key pair while it waits for Phase 2, and a prefix KEM pool. -/
theorem owner_challenge (raw : Pqxdh.Bytes) (identityIndex : ℕ) (owner : PqxdhRegistrationSchedule.Owner KemSK)
    (joint : PqxdhDynamicIdentityPool.SourceState) (pool : PqxdhLiveKemBirth.Pool KemSK)
    (identityOwned : joint.seeds[identityIndex]? = some owner.beacon.identity)
    (kemOwned : ∀ control prekey oneTime keys, owner.beacon.phase = .initSent control prekey oneTime keys →
      pool.keys[t.kem.val]? = some keys)
    (prefixed : PqxdhDeploymentIdealPoolSource.PoolPrefix (p.pool t) pool)
    (native : PqxdhServerAuthNative.NativeState KemSK) (marks : PqxdhRegistrationJointKemPostSkeleton.Marks Output)
    (slots : SlotState) :
    stackRun setup codec checks t p created
        (groupedOwner raw (PqxdhRegistrationJointBundle.encode setup identityIndex t.kem.val owner))
        (clean native.2, marks) (eraseServiceC ((joint, PqxdhDeploymentIdealPoolSource.routerOf pool), (native.1.cache, slots))) =
      (fun r => (some ((r.1.1.1, PqxdhRegistrationJointBundle.encode setup identityIndex t.kem.val r.1.1.2),
          (clean r.1.2.1.2, marks)),
          eraseServiceC ((joint, PqxdhDeploymentIdealPoolSource.routerOf pool), (r.1.2.1.1.cache, r.2)))) <$>
        (simulateQ (PqxdhRegistrationJointKemSecondEntry.slotImpl PqxdhDeploymentSeedSplit.tableService)
          ((simulateQ (ownerImplCE setup codec (factoredHidden setup codec checks) p.challenge)
            (groupedOwnerCE raw owner)).run (native, none))).run slots := by
  have mappedPhase : (PqxdhRegistrationJointBundle.encode setup identityIndex t.kem.val owner).beacon.phase =
      PqxdhBeaconPhase1Publication.mapPhase (PqxdhRegistrationJointBundle.keyMap t.kem.val) owner.beacon.phase := rfl
  unfold groupedOwner groupedOwnerCE
  rw [mappedPhase]
  rcases phase : owner.beacon.phase with _ | _ | ⟨control, prekey, oneTime, keys⟩ | _ | _
  all_goals simp only [PqxdhBeaconPhase1Publication.mapPhase]
  case fresh | freshWithCoins | established | aborted =>
    rw [stackRun_pure]
    simp only [simulateQ_pure, StateT.run_pure, map_pure]
  case initSent =>
    have kemAt := kemOwned control prekey oneTime keys phase
    have made : t.kem.val < pool.keys.length := (List.getElem?_eq_some_iff.mp kemAt).1
    rw [stackRun_bind, show (PqxdhRegistrationJointBundle.encode setup identityIndex t.kem.val owner).beacon.identity =
        PqxdhRegistrationJointBundle.identityMap setup identityIndex owner.beacon.identity from rfl,
      stack_prepProgram setup codec checks t p created _ joint pool prefixed made (native.1.cache, slots)
        (clean native.2, marks),
      prepare_relabel (preparationCE setup codec p.challenge) (prepItem setup codec t p joint pool) owner.beacon.identity
        (PqxdhRegistrationJointBundle.identityMap setup identityIndex owner.beacon.identity) keys
        (PqxdhRegistrationJointBundle.keyMap t.kem.val keys) owner.beacon.identity identityIndex
        (prep_calls setup codec t p joint pool identityIndex owner.beacon.identity keys identityOwned kemAt) control prekey
        oneTime raw,
      bind_map_left, simulateQ_bind, StateT.run_bind, simulateQ_bind, StateT.run_bind,
      slot_prep setup codec p (factoredHidden setup codec checks) _ (native, none) slots, bind_map_left, map_bind]
    refine bind_congr fun prepared => ?_
    rcases prepared with _ | pending
    · simp only [Option.elim_some, stackRun_pure, simulateQ_pure, StateT.run_pure, map_pure,
        PqxdhRegistrationJointFinish.finish_map]
    · simp only [Option.elim_some]
      rw [stackRun_bind, simulateQ_bind, simulateQ_spec_query, StateT.run_bind, simulateQ_bind, StateT.run_bind,
        show ownerImplCE setup codec (factoredHidden setup codec checks) p.challenge (.inr pending) =
          PqxdhDeploymentIdealSteps.groupCE setup codec (factoredHidden setup codec checks) pending from rfl]
      cases shared : pending.root.shared with
      | known secret =>
          rw [PqxdhDeploymentIdealPostFinish.stack_known setup codec checks t p created (List.Vector.replicate 32 0) pending
              secret shared joint pool native marks slots,
            slot_known setup codec _ pending secret shared native none slots, bind_map_left, bind_map_left, map_bind]
          refine bind_congr fun result => ?_
          simp only [Option.elim_some, stackRun_pure, simulateQ_pure, StateT.run_pure, map_pure,
            PqxdhRegistrationJointFinish.finish_map]
          rfl
      | challenge =>
          rw [stack_challengeC setup codec checks t p created pending shared
              (joint, PqxdhDeploymentIdealPoolSource.routerOf pool) native marks none slots, bind_map_left, map_bind]
          refine bind_congr fun result => ?_
          simp only [Option.elim_some, stackRun_pure, simulateQ_pure, StateT.run_pure, map_pure,
            PqxdhRegistrationJointFinish.finish_map]

end Owner

/-! ### The allocator keeps the values it represents -/

section Slots
open PqxdhRegistrationJointKemSecondEntry (Alloc SlotGood cacheOf slotImpl)
open PqxdhDeploymentIdealSlots (Coord)
open PqxdhRecordLiftInterface (Slot)

/-- One request of the allocator with the slot table, from a good state, keeps the state good and every value it represents. -/
theorem slot_keep (query : (PqxdhRegistrationJointKemSecondEntry.Spec Coord PqxdhServerAuthKeySchedule.Output).Domain)
    (state : PqxdhDeploymentIdealPostSim.SlotState) (good : SlotGood state) :
    ∀ result ∈ support ((slotImpl PqxdhDeploymentSeedSplit.tableService query).run state),
      SlotGood result.2 ∧ ∀ point value, cacheOf state point = some value → cacheOf result.2 point = some value := by
  obtain ⟨below, unique, free⟩ := good
  rcases query with coin | point
  · intro result member
    rw [PqxdhRegistrationJointKemSecondEntry.slot_coin, support_map] at member
    obtain ⟨_, -, rfl⟩ := member
    exact ⟨⟨below, unique, free⟩, fun _ _ held => held⟩
  · rcases found : state.1.1 point with _ | slot
    · by_cases room : state.1.2 < 2
      · intro result member
        have empty : state.2.1 ⟨state.1.2, room⟩ = none := free _ le_rfl
        rw [PqxdhRegistrationJointKemSecondEntry.slot_none _ _ _ found room] at member
        change result ∈ support ((fun result => (result.1, ((Function.update state.1.1 point (some ⟨state.1.2, room⟩),
          state.1.2 + 1), result.2))) <$> (PqxdhRecordLiftLazyTable.impl (spec := PqxdhDeploymentSeedSplit.OutputSpec 2)
            ⟨state.1.2, room⟩).run state.2) at member
        rw [PqxdhRecordLiftLazyTable.run_miss _ _ empty, Functor.map_map, support_map] at member
        obtain ⟨answer, -, rfl⟩ := member
        refine ⟨⟨fun other otherSlot otherFound => ?_, fun first second sharedSlot firstFound secondFound => ?_,
          fun freeSlot after => ?_⟩, fun other value held => ?_⟩
        · by_cases same : other = point
          · subst same
            simp only [Function.update_self, Option.some.injEq] at otherFound
            subst otherFound
            exact Nat.lt_succ_self _
          · simp only [Function.update_of_ne same] at otherFound
            exact Nat.lt_succ_of_lt (below other otherSlot otherFound)
        · by_cases firstSame : first = point
          · by_cases secondSame : second = point
            · rw [firstSame, secondSame]
            · subst firstSame
              simp only [Function.update_self, Option.some.injEq] at firstFound
              simp only [Function.update_of_ne secondSame] at secondFound
              have := below second sharedSlot secondFound
              rw [← firstFound] at this
              exact absurd this (Nat.lt_irrefl _)
          · by_cases secondSame : second = point
            · subst secondSame
              simp only [Function.update_self, Option.some.injEq] at secondFound
              simp only [Function.update_of_ne firstSame] at firstFound
              have := below first sharedSlot firstFound
              rw [← secondFound] at this
              exact absurd this (Nat.lt_irrefl _)
            · simp only [Function.update_of_ne firstSame] at firstFound
              simp only [Function.update_of_ne secondSame] at secondFound
              exact unique first second sharedSlot firstFound secondFound
        · have distinct : freeSlot ≠ ⟨state.1.2, room⟩ := by
            intro equal
            rw [equal] at after
            exact Nat.not_succ_le_self _ after
          simp only [QueryCache.cacheQuery_of_ne _ _ distinct]
          exact free freeSlot (Nat.le_of_succ_le after)
        · have apart : other ≠ point := by
            intro same
            subst same
            simp [cacheOf, found] at held
          rcases otherFound : state.1.1 other with _ | otherSlot
          · simp [cacheOf, otherFound] at held
          · have distinct : otherSlot ≠ ⟨state.1.2, room⟩ := by
              intro equal
              have := below other otherSlot otherFound
              rw [equal] at this
              exact Nat.lt_irrefl _ this
            simp only [cacheOf, QueryCache.ofFn_apply, otherFound, Option.bind_some] at held
            simp only [cacheOf, QueryCache.ofFn_apply, Function.update_of_ne apart, otherFound, Option.bind_some,
              QueryCache.cacheQuery_of_ne _ _ distinct, held]
      · intro result member
        simp only [slotImpl, QueryImpl.add_apply_inr, StateT.run_mk, found, room, _root_.dite_false, support_map] at member
        obtain ⟨_, -, rfl⟩ := member
        exact ⟨⟨below, unique, free⟩, fun _ _ held => held⟩
    · intro result member
      rw [PqxdhRegistrationJointKemSecondEntry.slot_some _ _ _ _ found] at member
      change result ∈ support ((fun result => (result.1, (state.1, result.2))) <$>
        (PqxdhRecordLiftLazyTable.impl (spec := PqxdhDeploymentSeedSplit.OutputSpec 2) slot).run state.2) at member
      rcases stored : state.2.1 slot with _ | answer
      · rw [PqxdhRecordLiftLazyTable.run_miss _ _ stored, Functor.map_map, support_map] at member
        obtain ⟨answer, -, rfl⟩ := member
        refine ⟨⟨below, unique, fun freeSlot after => ?_⟩, fun other value held => ?_⟩
        · have distinct : freeSlot ≠ slot := by
            intro equal
            rw [equal] at after
            exact Nat.lt_irrefl _ (Nat.lt_of_lt_of_le (below point slot found) after)
          simp only [QueryCache.cacheQuery_of_ne _ _ distinct]
          exact free freeSlot after
        · rcases otherFound : state.1.1 other with _ | otherSlot
          · simp [cacheOf, otherFound] at held
          · have distinct : otherSlot ≠ slot := by
              intro equal
              rw [equal] at otherFound
              simp [cacheOf, otherFound, stored] at held
            simp only [cacheOf, QueryCache.ofFn_apply, otherFound, Option.bind_some] at held
            simp only [cacheOf, QueryCache.ofFn_apply, otherFound, Option.bind_some, QueryCache.cacheQuery_of_ne _ _ distinct, held]
      · rw [PqxdhRecordLiftLazyTable.run_hit _ _ _ stored, map_pure, support_pure, Set.mem_singleton_iff] at member
        subst member
        exact ⟨⟨below, unique, free⟩, fun _ _ held => held⟩

/-- A client of the allocator with the slot table, from a good state, keeps the state good and every value it represents. -/
theorem slot_keepProgram {α : Type}
    (client : OracleComp (PqxdhRegistrationJointKemSecondEntry.Spec Coord PqxdhServerAuthKeySchedule.Output) α)
    (state : PqxdhDeploymentIdealPostSim.SlotState) (good : SlotGood state) :
    ∀ result ∈ support ((simulateQ (slotImpl PqxdhDeploymentSeedSplit.tableService) client).run state),
      SlotGood result.2 ∧ ∀ point value, cacheOf state point = some value → cacheOf result.2 point = some value := by
  induction client using OracleComp.inductionOn generalizing state with
  | pure value =>
      intro result member
      simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at member
      subst member
      exact ⟨good, fun _ _ held => held⟩
  | query_bind query next ih =>
      intro result member
      rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at member
      obtain ⟨middle, first, rest⟩ := member
      obtain ⟨goodMiddle, keepMiddle⟩ := slot_keep query state good middle first
      obtain ⟨goodResult, keepResult⟩ := ih middle.1 middle.2 goodMiddle result rest
      exact ⟨goodResult, fun point value held => keepResult point value (keepMiddle point value held)⟩

end Slots

/-! ### The middle side of owner k's challenge finish -/

section Middle
open PqxdhRegistrationJointKemEntryFactor (Output factoredHidden)
open PqxdhDeploymentIdealPostSource (Mid sourceMid)
open PqxdhDeploymentIdealSteps (groupedOwnerCE ownerImplCE establishedAt initSentAt)
open PqxdhDeploymentIdealSlots (Coord)
open PqxdhDeploymentIdealParams (Target Params)
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}
  (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
  (checks : Checks) {count : ℕ} (t : Target count) (p : Params KemSK count)
  (created : PqxdhLiveServerConstruction.Created Unit)

/-- Rejoining an annotated source state with a new shared native state and its owners with one owner replaced replaces that owner in its entry and keeps its indices. -/
theorem rejoin_set (old : PqxdhRegistrationJointSchedule.State KemSK) (shared : PqxdhServerAuthNative.NativeState KemSK)
    (address : ℕ) (entry : PqxdhRegistrationJointOwnership.Entry KemSK) (found : old.owners[address]? = some entry)
    (owner : PqxdhRegistrationSchedule.Owner KemSK) :
    PqxdhDeploymentIdealPostSource.rejoin old
        ⟨shared, (old.owners.map PqxdhRegistrationJointOwnership.Entry.owner).set address owner⟩ =
      { old with shared := shared, owners := old.owners.set address { entry with owner := owner } } := by
  simp only [PqxdhDeploymentIdealPostSource.rejoin]
  congr 1
  apply List.ext_getElem?
  intro index
  rw [List.getElem?_mapIdx, List.getElem?_set, List.getElem?_set, List.getElem?_map]
  by_cases same : address = index
  · subst same
    obtain ⟨bound, equal⟩ := List.getElem?_eq_some_iff.mp found
    simp [bound, equal]
  · simp only [same, ↓reduceIte]
    rcases old.owners[index]? <;> rfl

/-- The middle state after owner k's challenge finish: the new shared native state, the addressed owner's entry with the returned owner, the allocator and the table after the hidden read, and the Beacon install ghost recording the read's coordinates when the owner becomes established. -/
def afterChallenge (m : Mid KemSK) (address : ℕ) (entry : PqxdhRegistrationJointOwnership.Entry KemSK)
    (result : ((Option Pqxdh.Bytes × PqxdhRegistrationSchedule.Owner KemSK) ×
      (PqxdhServerAuthNative.NativeState KemSK × Option Coord)) × PqxdhDeploymentIdealPostSim.SlotState) : Mid KemSK where
  joint := { m.joint with shared := result.1.2.1, owners := m.joint.owners.set address { entry with owner := result.1.1.2 } }
  backend := (result.2.2, (result.2.1, { m.backend.2.2 with
    beacon := if establishedAt ((m.joint.owners.map PqxdhRegistrationJointOwnership.Entry.owner).set address result.1.1.2)
        address then result.1.2.2.or m.backend.2.2.beacon else m.backend.2.2.beacon }))
  seeds := m.seeds

/-- The ideal registration's finish of owner k after an active selected accept, unfolded: the LQ-F snapshot, `finishChallenge` from no recorded coordinates, and the Beacon install ghost. -/
theorem finishStep_challenge (hidden : Output → PqxdhRegistrationJointKemPostSkeleton.Hidden Response) (address : ℕ)
    (raw : Pqxdh.Bytes) (y : PqxdhDeploymentBackend.XState KemSK PqxdhDeploymentIdealSteps.IdealCore 2)
    (condition : y.backend.active = true ∧ address = t.kem.val ∧ initSentAt y.base.native.owners address = true) :
    (PqxdhDeploymentIdealSteps.finishStep setup codec route checks t p hidden created address raw).run y =
      (PqxdhDeploymentIdealSteps.finishChallenge setup codec hidden p.challenge address raw).run (y.base.native, none) >>=
        fun r => pure (r.1, { y with
          base := { y.base with native := r.2.1 }
          snap := PqxdhDeploymentLater.snapshotAt y.snap y.base.native.owners (some address)
          backend := { y.backend with
            beacon := if establishedAt r.2.1.owners address then r.2.2.or y.backend.beacon else y.backend.beacon } }) := by
  change (if y.backend.active = true ∧ address = t.kem.val ∧ initSentAt y.base.native.owners address = true then _
    else _) = _
  rw [ite_eq_left_of_eq_true _ _ (eq_true condition)]

/-- `finishChallenge` at a present owner: the grouped native owner under `ownerImplCE`, with the owner reinstalled. -/
theorem finishChallenge_found (hidden : Output → PqxdhRegistrationJointKemPostSkeleton.Hidden Response)
    (challenge : MlKem768Ciphertext) (address : ℕ) (raw : Pqxdh.Bytes) (state : PqxdhRegistrationSchedule.State KemSK)
    (owner : PqxdhRegistrationSchedule.Owner KemSK) (found : state.owners[address]? = some owner) (recorded : Option Coord) :
    (PqxdhDeploymentIdealSteps.finishChallenge setup codec hidden challenge address raw).run (state, recorded) =
      (fun result => (result.1.1, (({ shared := result.2.1, owners := state.owners.set address result.1.2 } :
          PqxdhRegistrationSchedule.State KemSK), result.2.2))) <$>
        (simulateQ (ownerImplCE setup codec hidden challenge) (groupedOwnerCE raw owner)).run (state.shared, recorded) := by
  change (match state.owners[address]? with
    | none => _
    | some owner => _) = _
  rw [found]
  simp only [bind_pure_comp]

/-- On owner k's challenge finish, the middle source handler is the ideal registration's challenge finish: the CE-native grouped owner under `ownerImplCE` with the factored hidden services from the annotated shared state and no recorded coordinates, past the allocator and item 2's lazy table from the middle's. -/
theorem sourceMid_challenge (address : ℕ) (raw : Pqxdh.Bytes) (m : Mid KemSK)
    (hidden : PqxdhDeploymentIdealPostSource.finishHiddenAt t m address = true)
    (entry : PqxdhRegistrationJointOwnership.Entry KemSK) (found : m.joint.owners[address]? = some entry) :
    (sourceMid setup codec route checks t p created (.inl (.inr (.finish address raw)))).run m =
      (fun result => (result.1.1.1, afterChallenge m address entry result)) <$>
        (simulateQ (PqxdhRegistrationJointKemSecondEntry.slotImpl PqxdhDeploymentSeedSplit.tableService)
          ((simulateQ (ownerImplCE setup codec (factoredHidden setup codec checks) p.challenge)
            (groupedOwnerCE raw entry.owner)).run (m.joint.shared, none))).run (m.backend.2.1, m.backend.1) := by
  change (if PqxdhDeploymentIdealPostSource.finishHiddenAt t m address then _ else _) = _
  rw [ite_eq_left_of_eq_true _ _ (eq_true hidden), PqxdhDeploymentIdealPostHidden.idealMid_run]
  change _ <$> (simulateQ (PqxdhRegistrationJointKemSecondEntry.slotImpl PqxdhDeploymentSeedSplit.tableService)
    ((PqxdhDeploymentIdealSteps.finishStep setup codec route checks t p (factoredHidden setup codec checks) created address
      raw).run (PqxdhDeploymentIdealSlots.detach (PqxdhDeploymentIdealPostSource.toX m)))).run _ = _
  have condition : m.backend.2.2.active = true ∧ address = t.kem.val ∧
      initSentAt (PqxdhRegistrationJointSchedule.source m.joint).owners address = true := by
    simpa [PqxdhDeploymentIdealPostSource.finishHiddenAt] using hidden
  have sourceFound : (PqxdhRegistrationJointSchedule.source m.joint).owners[address]? = some entry.owner := by
    simp [PqxdhRegistrationJointSchedule.source, List.getElem?_map, found]
  rw [finishStep_challenge setup codec route checks t p created _ address raw _ condition, simulateQ_bind,
    StateT.run_bind, finishChallenge_found setup codec _ p.challenge address raw
      (PqxdhDeploymentIdealSlots.detach (PqxdhDeploymentIdealPostSource.toX m)).base.native entry.owner sourceFound none,
    simulateQ_map, StateT.run_map, bind_map_left]
  simp only [simulateQ_pure, StateT.run_pure, bind_pure_comp, Functor.map_map]
  refine congrArg (fun f => f <$> _) (funext fun result => ?_)
  simp only [PqxdhDeploymentIdealPostSource.fromX, PqxdhDeploymentIdealSlots.attach, afterChallenge]
  rw [show (PqxdhDeploymentIdealSlots.detach (PqxdhDeploymentIdealPostSource.toX m)).base.native.owners =
    m.joint.owners.map PqxdhRegistrationJointOwnership.Entry.owner from rfl, rejoin_set _ _ address entry found]
  rfl

end Middle

/-! ### The step -/

section Step
open PqxdhRegistrationJointKemPostSkeleton (SkelState clean)
open PqxdhRegistrationJointKemEntryFactor (Output factoredHidden factoredServices)
open PqxdhDeploymentIdealPostSource (Mid sourceMid)
open PqxdhDeploymentIdealPostSteps (encodeMid skelMarks)
open PqxdhDeploymentIdealPostHidden (StepAtC encodeMidC eraseServiceC)
open PqxdhDeploymentIdealPostFinish (stackRun)
open PqxdhDeploymentIdealParams (Target Params)
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}
  (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
  (checks : Checks) {count : ℕ} (t : Target count) (p : Params KemSK count)
  (created : PqxdhLiveServerConstruction.Created Unit)

/-- Owner k's challenge finish: item 2's grouped finish of owner k through item 2's layers is the ideal registration's challenge finish on the middle state, at item 2's view without table counters. It needs item 2's ownership invariant, the addressed owner's KEM index to be the selected one, a prefix KEM pool, a good allocator state, and a stored value at the mark's coordinates (so that the hidden read leaves item 2's view of the mark unchanged). -/
theorem step_challenge (address : ℕ) (raw : Pqxdh.Bytes) (m : Mid KemSK)
    (hidden : PqxdhDeploymentIdealPostSource.finishHiddenAt t m address = true)
    (owned : PqxdhRegistrationJointSchedule.Invariant m.joint)
    (keyed : ∀ entry, m.joint.owners[address]? = some entry → entry.kemIndex = t.kem.val)
    (prefixed : PqxdhDeploymentIdealPoolSource.PoolPrefix (p.pool t) m.joint.pool.2)
    (good : PqxdhRegistrationJointKemSecondEntry.SlotGood (m.backend.2.1, m.backend.1))
    (stored : ∀ mark, m.backend.2.2.marks = some mark →
      (PqxdhRegistrationJointKemSecondEntry.cacheOf (m.backend.2.1, m.backend.1) mark.2).isSome) :
    StepAtC setup codec route checks t p created (.inl (.inr (.finish address raw))) m := by
  have condition : m.backend.2.2.active = true ∧ address = t.kem.val ∧
      PqxdhDeploymentIdealSteps.initSentAt (PqxdhRegistrationJointSchedule.source m.joint).owners address = true := by
    simpa [PqxdhDeploymentIdealPostSource.finishHiddenAt] using hidden
  rcases found : m.joint.owners[address]? with _ | entry
  · have absent : (PqxdhRegistrationJointSchedule.source m.joint).owners[address]? = none := by
      simp [PqxdhRegistrationJointSchedule.source, List.getElem?_map, found]
    have := condition.2.2
    simp [PqxdhDeploymentIdealSteps.initSentAt, absent] at this
  have kemAt := keyed entry found
  have entryOwned := owned entry (List.mem_of_getElem? found)
  have identityOwned : m.joint.pool.1.seeds[entry.identityIndex]? = some entry.owner.beacon.identity := entryOwned.1
  have kemOwned : ∀ control prekey oneTime keys, entry.owner.beacon.phase = .initSent control prekey oneTime keys →
      m.joint.pool.2.keys[t.kem.val]? = some keys := by
    intro control prekey oneTime keys phase
    rw [← kemAt]
    exact entryOwned.2 keys (by simp only [PqxdhRegistrationJointOwnership.activeKey, phase])
  unfold StepAtC
  rw [show (encodeMidC setup m).1 = (encodeMid setup m).1 from rfl,
    PqxdhDeploymentIdealPostSteps.upperE_run setup codec checks t p created _ _
      (PqxdhDeploymentIdealPostSteps.encodeMid_clean setup m),
    sourceMid_challenge setup codec route checks t p created address raw m hidden entry found]
  have present : (encodeMid setup m).1.1[address]? = some (PqxdhRegistrationJointGeneratedFinish.encodeEntry setup entry) := by
    simp [encodeMid, PqxdhRegistrationJointGeneratedFinish.encodeState, List.getElem?_map, found]
  have encoded : (PqxdhRegistrationJointGeneratedFinish.encodeEntry setup entry).2.2 =
      PqxdhRegistrationJointBundle.encode setup entry.identityIndex t.kem.val entry.owner := by
    simp [PqxdhRegistrationJointGeneratedFinish.encodeEntry, kemAt]
  have start : (encodeMidC setup m).2 = eraseServiceC ((m.joint.pool.1,
      PqxdhDeploymentIdealPoolSource.routerOf m.joint.pool.2), (m.joint.shared.1.cache, (m.backend.2.1, m.backend.1))) := by
    simp only [encodeMidC, encodeMid, eraseServiceC, Prod.map, PqxdhRegistrationJointKemObserverFree.eraseJoint_idem]
  have stack := owner_challenge setup codec checks t p created raw entry.identityIndex entry.owner m.joint.pool.1
    m.joint.pool.2 identityOwned kemOwned prefixed m.joint.shared (skelMarks m) (m.backend.2.1, m.backend.1)
  rw [← start, ← encoded] at stack
  unfold stackRun at stack
  rw [PqxdhDeploymentIdealPostFinish.upperLayer_finish setup codec checks t p created address raw _ _ present,
    Functor.map_map, simulateQ_map, OptionT.run_map, StateT.run_map]
  erw [stack]
  simp only [Functor.map_map]
  rw [map_eq_bind_pure_comp, map_eq_bind_pure_comp]
  refine bind_congr_of_forall_mem_support _ fun result member => ?_
  obtain ⟨-, keep⟩ := slot_keepProgram _ _ good result member
  have marks : skelMarks (afterChallenge m address entry result) = skelMarks m := by
    unfold skelMarks
    rcases mark : m.backend.2.2.marks with _ | mark'
    · simp only [afterChallenge, mark, Option.bind_none]
    · obtain ⟨value, held⟩ := Option.isSome_iff_exists.mp (stored mark' mark)
      simp only [afterChallenge, mark, Option.bind_some]
      rw [keep _ _ held, held]
  have owners : (PqxdhRegistrationJointGeneratedFinish.encodeState setup (afterChallenge m address entry result).joint).owners =
      (encodeMid setup m).1.1.set address (entry.identityIndex, entry.kemIndex,
        PqxdhRegistrationJointBundle.encode setup entry.identityIndex t.kem.val result.1.1.2) := by
    simp [afterChallenge, PqxdhRegistrationJointGeneratedFinish.encodeState, encodeMid, List.map_set,
      PqxdhRegistrationJointGeneratedFinish.encodeEntry, kemAt]
  simp only [Function.comp_apply, Option.map_some]
  rw [show (encodeMidC setup (afterChallenge m address entry result)).1 =
      ((PqxdhRegistrationJointGeneratedFinish.encodeState setup (afterChallenge m address entry result).joint).owners,
        (clean result.1.2.1.2, skelMarks (afterChallenge m address entry result))) from rfl, owners, marks]
  simp only [encodeMidC, encodeMid, eraseServiceC, Prod.map, PqxdhRegistrationJointKemObserverFree.eraseJoint_idem, id_eq]
  rfl

/-- After an active selected accept, `step_finish`'s premise on the addressed owner follows from the finish not being owner k's challenge finish, when the owner's KEM index is its position: an owner at the selected KEM index in the `initSent` phase would be owner k waiting for its challenge finish. -/
theorem finish_other (address : ℕ) (m : Mid KemSK)
    (real : PqxdhDeploymentIdealPostSource.finishHiddenAt t m address = false) (active : m.backend.2.2.active = true)
    (positioned : ∀ entry, m.joint.owners[address]? = some entry → entry.kemIndex = address) :
    ∀ entry, m.joint.owners[address]? = some entry → entry.kemIndex = t.kem.val →
      ∀ control prekey oneTime kem, entry.owner.beacon.phase ≠ .initSent control prekey oneTime kem := by
  intro entry found selected control prekey oneTime kem phase
  have atSelected : address = t.kem.val := (positioned entry found).symm.trans selected
  have sourceFound : (PqxdhRegistrationJointSchedule.source m.joint).owners[address]? = some entry.owner := by
    simp [PqxdhRegistrationJointSchedule.source, List.getElem?_map, found]
  have waiting : PqxdhDeploymentIdealSteps.initSentAt (PqxdhRegistrationJointSchedule.source m.joint).owners address =
      true := by
    simp [PqxdhDeploymentIdealSteps.initSentAt, sourceFound, phase]
  simp only [PqxdhDeploymentIdealPostSource.finishHiddenAt, decide_eq_false_iff_not] at real
  exact real ⟨active, atSelected, waiting⟩

/-- Every Beacon finish after an active selected accept: owner k's challenge finish by `step_challenge`, every other finish by item 2's real finish step `PqxdhDeploymentIdealPostFinish.step_finish`, at item 2's view without table counters. It needs item 2's ownership invariant, the addressed owner's KEM index to be its position, a prefix KEM pool, a good allocator state and a stored value at the mark's coordinates. -/
theorem step_finishActive (address : ℕ) (raw : Pqxdh.Bytes) (m : Mid KemSK) (active : m.backend.2.2.active = true)
    (owned : PqxdhRegistrationJointSchedule.Invariant m.joint)
    (positioned : ∀ entry, m.joint.owners[address]? = some entry → entry.kemIndex = address)
    (prefixed : PqxdhDeploymentIdealPoolSource.PoolPrefix (p.pool t) m.joint.pool.2)
    (good : PqxdhRegistrationJointKemSecondEntry.SlotGood (m.backend.2.1, m.backend.1))
    (stored : ∀ mark, m.backend.2.2.marks = some mark →
      (PqxdhRegistrationJointKemSecondEntry.cacheOf (m.backend.2.1, m.backend.1) mark.2).isSome) :
    StepAtC setup codec route checks t p created (.inl (.inr (.finish address raw))) m := by
  cases hidden : PqxdhDeploymentIdealPostSource.finishHiddenAt t m address
  · exact PqxdhDeploymentIdealPostFinish.step_finish setup codec route checks t p created address raw m hidden owned
      prefixed (finish_other t address m hidden active positioned)
  · have condition : m.backend.2.2.active = true ∧ address = t.kem.val ∧
        PqxdhDeploymentIdealSteps.initSentAt (PqxdhRegistrationJointSchedule.source m.joint).owners address = true := by
      simpa [PqxdhDeploymentIdealPostSource.finishHiddenAt] using hidden
    have atSelected : address = t.kem.val := condition.2.1
    exact step_challenge setup codec route checks t p created address raw m hidden owned
      (fun entry found => (positioned entry found).trans atSelected) prefixed good stored

end Step

end BeaconcryptCore.Computational.PqxdhDeploymentIdealPostChallenge

-- Axiom guards (generated)

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPostChallenge.collect_relabel' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPostChallenge.collect_relabel

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPostChallenge.prepare_relabel' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPostChallenge.prepare_relabel

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPostChallenge.reservation_selected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPostChallenge.reservation_selected

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPostChallenge.post_target' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPostChallenge.post_target

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPostChallenge.stack_target' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPostChallenge.stack_target

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPostChallenge.prepKnown_erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPostChallenge.prepKnown_erase

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPostChallenge.stack_prepQuery' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPostChallenge.stack_prepQuery

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPostChallenge.stack_prepProgram' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPostChallenge.stack_prepProgram

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPostChallenge.tableLayer_flat' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPostChallenge.tableLayer_flat

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPostChallenge.slot_known' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPostChallenge.slot_known

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPostChallenge.stack_challenge' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPostChallenge.stack_challenge

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPostChallenge.groupCE_keep' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPostChallenge.groupCE_keep

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPostChallenge.stack_challengeC' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPostChallenge.stack_challengeC

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPostChallenge.prep_calls' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPostChallenge.prep_calls

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPostChallenge.slot_prep' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPostChallenge.slot_prep

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPostChallenge.owner_challenge' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPostChallenge.owner_challenge

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPostChallenge.slot_keep' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPostChallenge.slot_keep

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPostChallenge.slot_keepProgram' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPostChallenge.slot_keepProgram

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPostChallenge.rejoin_set' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPostChallenge.rejoin_set

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPostChallenge.finishStep_challenge' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPostChallenge.finishStep_challenge

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPostChallenge.finishChallenge_found' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPostChallenge.finishChallenge_found

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPostChallenge.sourceMid_challenge' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPostChallenge.sourceMid_challenge

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPostChallenge.step_challenge' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPostChallenge.step_challenge

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPostChallenge.finish_other' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPostChallenge.finish_other

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPostChallenge.step_finishActive' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPostChallenge.step_finishActive
