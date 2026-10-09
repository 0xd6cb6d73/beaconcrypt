-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhDeploymentIdealPostMark

/-!
# Item 2's post-challenge stack as two layers (CE-11b, unit U6, second part)

The active branch of the second compile lemma (`PqxdhDeploymentIdealActive.ActiveBranch`) compares the CE side with item 2's post-challenge phase (`PqxdhDeploymentIdealBranch.itemPost`), a stack of seven interpreters: the grouped client on the encoded owners, the skeleton's native layer, the actual encapsulator, the post-challenge router (which may stop), the challenger's CCA evaluation, item 2's public-table layer and the first-touch allocator in front of the two-slot table. This module regroups the stack into two layers and gives the simulation lemma that the post-challenge simulation (CE-11b design-v2 section 8.4) uses.

- Generic: `optionLower` runs an optional stateful layer followed by a stateful interpreter of its requests as one optional stateful layer on the product state (`optionLower_run`); it keeps the property of never reading some observers of the optional layer's state (`optionLower_neverRead`), as do a stateless layer in front (`compose_neverRead`) and the forwarding of table oracles (`fwdOption_neverRead`), stated with item 2's `PqxdhRegistrationJointKemObserverFree.NeverReadOption`.
- Generic: `sim_option` is a functional simulation through an upper stateful layer and a lower optional stateful layer: if every allowed request of a middle handler, projected to the two layers' states, is answered by the two layers without stopping while an invariant holds and a room is left for the costly requests, then every program with only allowed requests and at most the room's number of costly requests runs through the two layers without stopping, as the projection of its middle run. With the source creates as the costly class and the router's remaining reservation as the room, this is the no-stop argument of the post-challenge router together with the simulation.
- Item 2's stack: `upperLayer` is the grouped client followed by the skeleton's native layer (`skelResume_upper`: the skeleton's resumed client is the Server's private resumption followed by the tagged client through `upperLayer`); `serviceLayer` is the actual encapsulator, the post-challenge router, the CCA evaluation and the table layers (`tableLayer`) as one optional stateful layer. `itemPost_active`: on a pending prechallenge context whose verified PQ key is the selected one, `itemPost` is the skeleton's decision of the resumed client run through `serviceLayer`. The service layers never read the router transcripts (`serviceLayer_neverRead`, from item 2's `post_neverRead`), so `itemPost_erased` runs it with the transcripts erased after every step (`eraseService`).

These are program equalities and generic simulation lemmas. They charge nothing and make no security claim.
-/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc

set_option autoImplicit false

namespace BeaconcryptCore.Computational.PqxdhDeploymentIdealPostSim

/-! ### A stateful interpreter below an optional stateful layer -/

section Lower
variable {ι₁ ι₂ : Type} {spec₁ : OracleSpec ι₁} {spec₂ : OracleSpec ι₂} {J K : Type}

/-- An optional stateful layer followed by a stateful interpreter of its requests, as one optional stateful layer on the product state. -/
def optionLower (layer : QueryImpl spec₁ (OptionT (StateT J (OracleComp spec₂))))
    (lower : QueryImpl spec₂ (StateT K ProbComp)) : QueryImpl spec₁ (OptionT (StateT (J × K) ProbComp)) :=
  fun query => OptionT.mk (StateT.mk fun state =>
    (fun result => (result.1.1, (result.1.2, result.2))) <$>
      (simulateQ lower (((layer query).run).run state.1)).run state.2)

/-- Running a program through an optional stateful layer and then a stateful interpreter of its requests is running it through `optionLower`, up to reassociation; a stopped run keeps the interpreter's state. -/
theorem optionLower_run (layer : QueryImpl spec₁ (OptionT (StateT J (OracleComp spec₂))))
    (lower : QueryImpl spec₂ (StateT K ProbComp)) {α : Type} (work : OracleComp spec₁ α) (j : J) (k : K) :
    (simulateQ lower (((simulateQ layer work).run).run j)).run k =
      (fun result => ((result.1, result.2.1), result.2.2)) <$>
        ((simulateQ (optionLower layer lower) work).run).run (j, k) := by
  induction work using OracleComp.inductionOn generalizing j k with
  | pure value => simp
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, OptionT.run_bind, Option.elimM, StateT.run_bind, map_bind]
      simp only [optionLower, OptionT.run_mk, StateT.run_mk, bind_map_left]
      refine bind_congr fun result => ?_
      rcases result with ⟨⟨_ | value, after⟩, lowered⟩
      · simp
      · simpa using ih value after lowered

/-- `optionLower` never reads observers of the optional layer's state that the layer never reads. -/
theorem optionLower_neverRead (layer : QueryImpl spec₁ (OptionT (StateT J (OracleComp spec₂))))
    (lower : QueryImpl spec₂ (StateT K ProbComp)) (erase : J → J)
    (never : PqxdhRegistrationJointKemObserverFree.NeverReadOption erase layer) :
    PqxdhRegistrationJointKemObserverFree.NeverReadOption (Prod.map erase id) (optionLower layer lower) := by
  intro query state
  have lowered := congrArg (fun work => (simulateQ lower work).run state.2) (never query state.1)
  simp only [simulateQ_map, StateT.run_map] at lowered
  simp only [optionLower, OptionT.run_mk, StateT.run_mk, Functor.map_map, Prod.map_fst, Prod.map_snd, id_eq]
  have mapped := congrArg (fun work => (fun result : (Option (spec₁.Range query) × J) × K =>
    (result.1.1, (result.1.2, result.2))) <$> work) lowered
  simp only [Functor.map_map] at mapped
  exact mapped

end Lower

/-! ### Erasure through stateless and forwarding layers -/

section Erase
variable {ιA ιB ιT : Type} {A : OracleSpec ιA} {B : OracleSpec ιB} {T : OracleSpec ιT} {J : Type}

/-- An optional stateful layer that never reads some observers keeps that property after a stateless layer in front of it. -/
theorem compose_neverRead {ιC : Type} {C : OracleSpec ιC}
    (layer : QueryImpl A (OptionT (StateT J (OracleComp B)))) (front : QueryImpl C (OracleComp A)) (erase : J → J)
    (idem : ∀ state, erase (erase state) = erase state)
    (never : PqxdhRegistrationJointKemObserverFree.NeverReadOption erase layer) :
    PqxdhRegistrationJointKemObserverFree.NeverReadOption erase (layer ∘ₛ front) := by
  intro query state
  simp only [QueryImpl.apply_compose]
  rw [PqxdhRegistrationJointKemObserverFree.run_eraseOption erase idem layer never,
    PqxdhRegistrationJointKemObserverFree.run_eraseOption erase idem layer never, idem]

/-- Forwarding the table oracles keeps the property of never reading some observers. -/
theorem fwdOption_neverRead (layer : QueryImpl A (OptionT (StateT J (OracleComp B)))) (erase : J → J)
    (idem : ∀ state, erase (erase state) = erase state)
    (never : PqxdhRegistrationJointKemObserverFree.NeverReadOption erase layer) :
    PqxdhRegistrationJointKemObserverFree.NeverReadOption erase
      (PqxdhRegistrationJointKemPostSkeleton.fwdOption (T := T) layer) := by
  intro query state
  rcases query with query | query
  · rw [PqxdhRegistrationJointKemPostSkeleton.fwdOption_inl, PqxdhRegistrationJointKemPostSkeleton.fwdOption_inl]
    have lifted := congrArg (fun work => OracleComp.liftComp work (B + T)) (never query state)
    simp only [OracleComp.liftComp_map] at lifted
    exact lifted
  · rw [PqxdhRegistrationJointKemPostSkeleton.fwdOption_inr, PqxdhRegistrationJointKemPostSkeleton.fwdOption_inr]
    simp only [Functor.map_map]
    refine congrArg (fun f => f <$> _) (funext fun reply => ?_)
    simp only [Prod.map, id_eq, idem]

end Erase

/-! ### Budgeted simulation through an optional stateful layer -/

section Budget
variable {ι ι' : Type} {spec : OracleSpec ι} {spec' : OracleSpec ι'} {A B S : Type}

/-- A functional simulation through two layers, the lower one optional: if every allowed request of a middle handler, projected by `project`, is answered by the upper layer followed by the optional lower layer without stopping, as long as an invariant holds and the request fits a room (one unit for every request in a class `costly`), and every such middle step keeps the invariant and uses at most one unit of room on a costly request, then every program with only allowed requests and at most the room's number of costly requests runs through the two layers without stopping, as the projection of its middle run. -/
theorem sim_option (upper : QueryImpl spec (StateT A (OracleComp spec')))
    (lower : QueryImpl spec' (OptionT (StateT B ProbComp))) (middle : QueryImpl spec (StateT S ProbComp))
    (project : S → A × B) (inv : S → Prop) (allowed costly : ι → Prop) [DecidablePred allowed]
    [DecidablePred costly] (room : S → ℕ)
    (step : ∀ query state, inv state → allowed query → (costly query → 0 < room state) →
      ((simulateQ lower ((upper query).run (project state).1)).run).run (project state).2 =
        (fun result => (some (result.1, (project result.2).1), (project result.2).2)) <$> (middle query).run state)
    (keep : ∀ query state, inv state → allowed query → (costly query → 0 < room state) →
      ∀ result ∈ support ((middle query).run state), inv result.2 ∧
        room state ≤ room result.2 + (if costly query then 1 else 0))
    {α : Type} (work : OracleComp spec α) (onlyAllowed : work.IsQueryBoundP (fun query => ¬ allowed query) 0)
    (budget : ℕ) (bounded : work.IsQueryBoundP costly budget)
    (state : S) (fits : budget ≤ room state) (holds : inv state) :
    ((simulateQ lower ((simulateQ upper work).run (project state).1)).run).run (project state).2 =
      (fun result => (some (result.1, (project result.2).1), (project result.2).2)) <$>
        (simulateQ middle work).run state := by
  induction work using OracleComp.inductionOn generalizing budget state with
  | pure value => simp
  | query_bind query next ih =>
      rw [isQueryBoundP_query_bind_iff] at bounded onlyAllowed
      obtain ⟨allowedCost, rest⟩ := bounded
      obtain ⟨first, restOnly⟩ := onlyAllowed
      have isAllowed : allowed query := by
        rcases first with free | impossible
        · exact not_not.mp free
        · omega
      have available : costly query → 0 < room state := by
        intro isCostly
        rcases allowedCost with free | positive
        · exact absurd isCostly free
        · omega
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, OptionT.run_bind, Option.elimM,
        map_bind]
      rw [step query state holds isAllowed available, bind_map_left]
      refine bind_congr_of_forall_mem_support _ fun result member => ?_
      obtain ⟨kept, used⟩ := keep query state holds isAllowed available result member
      simp only [Option.elim]
      have nextOnly := restOnly result.1
      simp only [isAllowed, not_true_eq_false, ↓reduceIte] at nextOnly
      refine ih result.1 nextOnly _ (rest result.1) result.2 ?_ kept
      split_ifs at used ⊢ with isCostly
      · omega
      · omega

end Budget

/-! ### Item 2's post-challenge phase through one optional service layer -/

section Item2
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhKemIndCca (MlKem768PublicKey MlKem768Ciphertext)
open PqxdhRegistrationJointKemPostSkeleton (Enc TSpec SkelSpec fwd fwdOption evalLayer skelDecide skelResume)
open PqxdhRegistrationJointKemEntryFactor (Output publicLocalV factoredServices)
open PqxdhDeploymentIdealParams (Target Params)
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}

/-- The slot state of item 2's two-slot ideal world: the first-touch allocator and the persistent lazy table. -/
abbrev SlotState :=
  PqxdhRegistrationJointKemSecondEntry.Alloc PqxdhCorrelatedExtractFamily.Message 2 × PqxdhDeploymentIdealSteps.TableState

/-- The state of the service layers of item 2's post-challenge phase: the joint identity and KEM router state, item 2's public table cache and the slot state. -/
abbrev ServiceState (KemSK : Type) :=
  PqxdhDynamicKemJointSource.State KemSK × (PqxdhSecretInputKdf.HmacOracle.QueryCache × SlotState)

/-- The table layers of item 2's post-challenge phase as one stateful interpreter: item 2's public-table layer (direct reads) in front of the first-touch allocator and the two-slot table (hidden reads). -/
noncomputable def tableLayer :
    QueryImpl (SkelSpec Output) (StateT (PqxdhSecretInputKdf.HmacOracle.QueryCache × SlotState) ProbComp) :=
  ((PqxdhRegistrationJointKemSecondEntry.slotImpl (D := PqxdhCorrelatedExtractFamily.Message)
    (PqxdhRegistrationJointKemSecondEntry.tableService (n := 2))).mapStateTBase (publicLocalV Output)).flattenStateT

/-- The service layers below item 2's skeleton in its post-challenge phase as one optional stateful interpreter of the skeleton's exposed encapsulation interface with the table oracles: the actual encapsulator, the post-challenge router holding the placeholder candidate, the challenger's CCA evaluation and the table layers. -/
noncomputable def serviceLayer (setup : Setup baseSpec KemSK) {count : ℕ} (selected : Fin (count + 1))
    (chosen : MlKem768PublicKey × KemSK) (others : Fin count → MlKem768PublicKey × KemSK)
    (challenge : MlKem768Ciphertext) :
    QueryImpl (Enc KemSK + TSpec Output) (OptionT (StateT (ServiceState KemSK) ProbComp)) :=
  optionLower
    (fwdOption (T := TSpec Output) (PqxdhDynamicKemJointRouter.post setup.joint setup.kem selected.val
      (PqxdhDynamicKemRouter.selectedReservation selected chosen.1 others) challenge
        PqxdhRegistrationJointBeaconOpaqueFinishRouter.placeholder) ∘ₛ
      fwd (T := TSpec Output) (PqxdhRegistrationJointKemEncapsulation.actual setup))
    (tableLayer ∘ₛ fwd (T := TSpec Output) (evalLayer setup chosen.2 challenge))

/-- Item 2's post-challenge phase (`PqxdhDeploymentIdealBranch.itemPost`) on a pending prechallenge context whose verified PQ key is the selected one is the skeleton's resumed client run through the one optional service layer `serviceLayer`, from the erased router state of the context, the context's table cache and the empty slot state, followed by the skeleton's decision. -/
theorem itemPost_active {A Y : Type} {count : ℕ} (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (t : Target count) (p : Params KemSK count)
    (decision : Y × PqxdhDeploymentCompile.Local → Bool) (created : PqxdhRegistrationJointServerBirth.ClientCreated Unit)
    (others : Fin count → MlKem768PublicKey × KemSK) (raw : Pqxdh.Bytes)
    (value : PqxdhServerRootPreparation.Verified Reader) (matched : value.keys.pqKey = p.chosen.1)
    (ephemeral : PqxdhServerRootPreparation.Ephemeral PqxdhJointGapDh.ScalarBytes) (consumed : List Pqxdh.Bytes)
    (native : PqxdhServerAuthNative.NativeState KemSK)
    (owners : List PqxdhRegistrationJointGeneratedFinish.EncodedEntry)
    (next : Option ℕ → OracleComp (PqxdhRegistrationJointKemCommands.SourceSpec KemSK) (Y × PqxdhDeploymentCompile.Local))
    (state : PqxdhDynamicKemJointSource.State KemSK) (after : A) :
    PqxdhDeploymentIdealBranch.itemPost setup codec checks t p decision
        (.ready created others (some (.pending raw value ephemeral consumed native owners next)) state after) =
      skelDecide <$> ((simulateQ (serviceLayer setup t.kem p.chosen others p.challenge)
        (skelResume setup codec checks created.server.server.metadata.identityIndex created.publicIdentity
          (PqxdhRegistrationJointAcceptCutTag.decideTag decision) raw value ephemeral consumed native.2 owners next
          t.kem.val p.challenge (factoredServices setup codec checks))).run).run
        (PqxdhRegistrationJointKemObserverFree.eraseJoint state,
          (native.1.cache, (PqxdhRegistrationJointKemSecondEntry.emptyAlloc, PqxdhRecordLiftLazyTable.initial))) := by
  have table : ∀ {β : Type} (work : OracleComp (SkelSpec Output) β) (cache : PqxdhSecretInputKdf.HmacOracle.QueryCache)
      (slots : SlotState),
      (simulateQ (PqxdhRegistrationJointKemSecondEntry.slotImpl (D := PqxdhCorrelatedExtractFamily.Message)
        (PqxdhRegistrationJointKemSecondEntry.tableService (n := 2))) ((simulateQ (publicLocalV Output) work).run'
          cache)).run' slots = (simulateQ tableLayer work).run' (cache, slots) := by
    intro β work cache slots
    simp only [StateT.run'_eq, simulateQ_map, StateT.run_map,
      OracleComp.simulateQ_mapStateTBase_run_eq_map_flattenStateT]
    simp only [Functor.map_map]
    rfl
  unfold PqxdhDeploymentIdealBranch.itemPost
  simp only [PqxdhRegistrationJointKemPostSkeleton.postSkel, matched, ↓reduceIte,
    PqxdhRegistrationJointKemPostSkeleton.cacheOf]
  rw [table, simulateQ_map, StateT.run'_eq, StateT.run_map, ← QueryImpl.simulateQ_compose,
    ← QueryImpl.simulateQ_compose (fwdOption (T := TSpec Output) _), optionLower_run]
  simp only [Functor.map_map]
  rfl

/-- The upper layers of item 2's post-challenge phase as one stateful interpreter of the source command interface: the grouped client on the encoded owners, then the skeleton's native layer on the skeleton state. -/
noncomputable def upperLayer {V : Type} (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (identityIndex : ℕ) (publicIdentity : PqxdhJointIdentity.PublicIdentity) (selected : ℕ)
    (challenge : MlKem768Ciphertext) (services : PqxdhRegistrationJointKemPostSkeleton.Services V Response) :
    QueryImpl (PqxdhRegistrationJointKemCommands.SourceSpec KemSK)
      (StateT (List PqxdhRegistrationJointGeneratedFinish.EncodedEntry ×
        PqxdhRegistrationJointKemPostSkeleton.SkelState KemSK V) (OracleComp (Enc KemSK + TSpec V))) :=
  ((PqxdhRegistrationJointKemPostSkeleton.skelImpl setup codec checks identityIndex publicIdentity services).mapStateTBase
    (PqxdhRegistrationJointKemPostSkeleton.groupedClient setup codec selected challenge)).flattenStateT

/-- The skeleton's resumed client: the Server's private resumption on the native layer, then the tagged client through `upperLayer` from the encoded owners and the skeleton state after the resumption. -/
theorem skelResume_upper {X R V : Type} (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (identityIndex : ℕ) (publicIdentity : PqxdhJointIdentity.PublicIdentity)
    (observe : X × PqxdhRegistrationJointAcceptCutTag.Tag → R) (raw : Pqxdh.Bytes)
    (value : PqxdhServerRootPreparation.Verified Reader)
    (ephemeral : PqxdhServerRootPreparation.Ephemeral PqxdhJointGapDh.ScalarBytes) (consumed : List Pqxdh.Bytes)
    (game : PqxdhServerAuthExperiment.GameState KemSK) (owners : List PqxdhRegistrationJointGeneratedFinish.EncodedEntry)
    (next : Option ℕ → OracleComp (PqxdhRegistrationJointKemCommands.SourceSpec KemSK) X) (selected : ℕ)
    (challenge : MlKem768Ciphertext) (services : PqxdhRegistrationJointKemPostSkeleton.Services V Response) :
    skelResume setup codec checks identityIndex publicIdentity observe raw value ephemeral consumed game owners next
        selected challenge services =
      (simulateQ (PqxdhRegistrationJointKemPostSkeleton.resumeImpl setup.hmac game.sessions services)
          (PqxdhRegistrationJointKemOpaqueResume.resume setup codec checks identityIndex publicIdentity raw value ephemeral
            (PqxdhAcceptedRegistration.ciphertextArray challenge) .challenge game consumed)).run (game, none) >>=
        fun answer => (fun result => ((result.1, result.2.1), result.2.2)) <$>
          (simulateQ (upperLayer setup codec checks identityIndex publicIdentity selected challenge services)
            (PqxdhRegistrationJointAcceptKemCut.tagged observe raw next answer.1)).run (owners, answer.2) := by
  unfold skelResume upperLayer
  refine bind_congr fun answer => ?_
  rw [OracleComp.simulateQ_mapStateTBase_run_eq_map_flattenStateT]

/-- Erase the transcripts of the joint router state in a service state. -/
def eraseService (state : ServiceState KemSK) : ServiceState KemSK :=
  Prod.map PqxdhRegistrationJointKemObserverFree.eraseJoint id state

/-- The service layers never read the router transcripts. -/
theorem serviceLayer_neverRead (setup : Setup baseSpec KemSK) {count : ℕ} (selected : Fin (count + 1))
    (chosen : MlKem768PublicKey × KemSK) (others : Fin count → MlKem768PublicKey × KemSK)
    (challenge : MlKem768Ciphertext) :
    PqxdhRegistrationJointKemObserverFree.NeverReadOption eraseService
      (serviceLayer setup selected chosen others challenge) :=
  optionLower_neverRead _ _ PqxdhRegistrationJointKemObserverFree.eraseJoint
    (compose_neverRead _ _ _ PqxdhRegistrationJointKemObserverFree.eraseJoint_idem
      (fwdOption_neverRead _ _ PqxdhRegistrationJointKemObserverFree.eraseJoint_idem
        (PqxdhRegistrationJointKemObserverFree.post_neverRead _ _ _ _ _ _)))

/-- Item 2's post-challenge phase on a pending prechallenge context whose verified PQ key is the selected one, with the router transcripts erased after every step (`eraseService`): the skeleton's decision reads no transcript. -/
theorem itemPost_erased {A Y : Type} {count : ℕ} (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (t : Target count) (p : Params KemSK count)
    (decision : Y × PqxdhDeploymentCompile.Local → Bool) (created : PqxdhRegistrationJointServerBirth.ClientCreated Unit)
    (others : Fin count → MlKem768PublicKey × KemSK) (raw : Pqxdh.Bytes)
    (value : PqxdhServerRootPreparation.Verified Reader) (matched : value.keys.pqKey = p.chosen.1)
    (ephemeral : PqxdhServerRootPreparation.Ephemeral PqxdhJointGapDh.ScalarBytes) (consumed : List Pqxdh.Bytes)
    (native : PqxdhServerAuthNative.NativeState KemSK)
    (owners : List PqxdhRegistrationJointGeneratedFinish.EncodedEntry)
    (next : Option ℕ → OracleComp (PqxdhRegistrationJointKemCommands.SourceSpec KemSK) (Y × PqxdhDeploymentCompile.Local))
    (state : PqxdhDynamicKemJointSource.State KemSK) (after : A) :
    PqxdhDeploymentIdealBranch.itemPost setup codec checks t p decision
        (.ready created others (some (.pending raw value ephemeral consumed native owners next)) state after) =
      skelDecide <$> ((simulateQ (PqxdhRegistrationJointKemObserverFree.eraseOptionImpl eraseService
          (serviceLayer setup t.kem p.chosen others p.challenge))
        (skelResume setup codec checks created.server.server.metadata.identityIndex created.publicIdentity
          (PqxdhRegistrationJointAcceptCutTag.decideTag decision) raw value ephemeral consumed native.2 owners next
          t.kem.val p.challenge (factoredServices setup codec checks))).run).run
        (PqxdhRegistrationJointKemObserverFree.eraseJoint state,
          (native.1.cache, (PqxdhRegistrationJointKemSecondEntry.emptyAlloc, PqxdhRecordLiftLazyTable.initial))) := by
  rw [itemPost_active setup codec checks t p decision created others raw value matched ephemeral consumed native owners
    next state after]
  have erased := PqxdhRegistrationJointKemObserverFree.run_eraseOption eraseService
    (fun state => by simp only [eraseService, Prod.map, PqxdhRegistrationJointKemObserverFree.eraseJoint_idem, id_eq])
    (serviceLayer setup t.kem p.chosen others p.challenge) (serviceLayer_neverRead setup t.kem p.chosen others p.challenge)
    (skelResume setup codec checks created.server.server.metadata.identityIndex created.publicIdentity
      (PqxdhRegistrationJointAcceptCutTag.decideTag decision) raw value ephemeral consumed native.2 owners next
      t.kem.val p.challenge (factoredServices setup codec checks))
    (PqxdhRegistrationJointKemObserverFree.eraseJoint state,
      (native.1.cache, (PqxdhRegistrationJointKemSecondEntry.emptyAlloc, PqxdhRecordLiftLazyTable.initial)))
  have same : eraseService (PqxdhRegistrationJointKemObserverFree.eraseJoint state,
      (native.1.cache, (PqxdhRegistrationJointKemSecondEntry.emptyAlloc, PqxdhRecordLiftLazyTable.initial))) =
      (PqxdhRegistrationJointKemObserverFree.eraseJoint state,
        (native.1.cache, (PqxdhRegistrationJointKemSecondEntry.emptyAlloc, PqxdhRecordLiftLazyTable.initial))) := rfl
  rw [same] at erased
  rw [← erased, Functor.map_map]
  rfl

end Item2

end BeaconcryptCore.Computational.PqxdhDeploymentIdealPostSim

-- Axiom guards (generated)

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPostSim.optionLower_run' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPostSim.optionLower_run

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPostSim.optionLower_neverRead' depends on axioms: [propext,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPostSim.optionLower_neverRead

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPostSim.compose_neverRead' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPostSim.compose_neverRead

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPostSim.fwdOption_neverRead' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPostSim.fwdOption_neverRead

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPostSim.sim_option' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPostSim.sim_option

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPostSim.itemPost_active' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPostSim.itemPost_active

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPostSim.skelResume_upper' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPostSim.skelResume_upper

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPostSim.serviceLayer_neverRead' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPostSim.serviceLayer_neverRead

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPostSim.itemPost_erased' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPostSim.itemPost_erased
