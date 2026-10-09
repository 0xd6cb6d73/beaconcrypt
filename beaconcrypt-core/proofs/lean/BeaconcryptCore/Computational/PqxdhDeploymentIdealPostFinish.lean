-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhDeploymentIdealPostHidden

/-!
# The real Beacon finish through item 2's layers (CE-11b, unit U6, third part)

The middle source handler answers a finish that is not owner k's challenge finish by the annotated source finish (`PqxdhRegistrationJointSchedule.finish`, `sourceMid_finish`). Item 2's upper layers answer it by the grouped owner (`PqxdhRegistrationJointKemPostSkeleton.groupedOwner`) through the grouped compiler and the skeleton, and item 2's service layers answer the skeleton's requests. This module proves `PqxdhDeploymentIdealPostHidden.StepAtC` for such a finish.

- Naturality: the opaque preparation and collection (`PqxdhBeaconPhase2Shared.prepare`, `collect`) commute with relabelling the handle type (`MapCalls`, `collect_map`, `admitted_map`, `prepare_map`), and decapsulate only with the owner's own key (`collect_free`, `prepare_free`).
- Grouping: `groupH` interprets the grouped owner's interface by an interpretation of the opaque owner's interface, and `owner_grouped` equates the opaque owner with the grouped owner under it.
- Known handles: item 2's marked preparation answers with known handles away from the selected challenge decapsulation (`preparationKnown`, `prepSecret`, `targetPrep`, `markedPrep_known`, `markedPrep_bounds`, `known_calls`); `handlesKnown` and `known_fullCalls` give the full callback conditions of item 2's `PqxdhBeaconPhase2Shared.owner_realization` for the source's native finish callbacks; `tail_known` is the grouped tail with known handles; `middle_finish` is the annotated source finish at a present owner as the grouped owner under `groupH handlesKnown`, from item 2's ownership invariant.
- The stack: `stackRun` (with `stackRun_pure`, `stackRun_bind`), `skel_groupedPool`, `lowerEC_run`, `stack_prep` (a preparation without the selected challenge decapsulation, from a prefix pool), `splitT_ctx`, `splitT_group_known`, `stack_known` and `owner_stack`: a grouped owner that is not waiting for Phase 2 with the selected KEM key, through item 2's layers, is the grouped owner under `groupH handlesKnown` on the source state, projected to item 2's view.
- The step: `upperLayer_finish`, `upperLayer_finish_none` and `step_finish`, with hypotheses that the finish is not owner k's challenge finish, item 2's ownership invariant, a prefix KEM pool, and that an owner at the selected KEM index is not waiting for Phase 2.

These are program equalities. They charge nothing and make no security claim.
-/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc

set_option autoImplicit false

namespace BeaconcryptCore.Computational.PqxdhDeploymentIdealPostFinish
open PqxdhBeaconPhase2Shared (Secrets Inputs Prepared Query Spec collect prepare afterInputs admitted)
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhKemIndCca (MlKem768PublicKey MlKem768Ciphertext MlKemSharedSecret)
open PqxdhRefinement (absBytes)

/-! ### Naturality of the opaque preparation in the handle type -/

section Natural
variable {I D K X Response S₁ S₂ : Type}

/-- Relabel the handle of root coordinates. -/
def mapSecrets (f : S₁ → S₂) (secrets : Secrets S₁) : Secrets S₂ :=
  ⟨secrets.dh1, secrets.dh2, secrets.dh3, secrets.dh4, f secrets.shared⟩

/-- Relabel the handle of collected inputs. -/
def mapInputs (f : S₁ → S₂) (inputs : Inputs Response S₁) : Inputs Response S₂ :=
  ⟨inputs.response, inputs.ciphertext, inputs.ephemeral, inputs.serverIdentity, inputs.assigned,
    mapSecrets f inputs.secrets⟩

/-- Relabel the handle of a prepared finish. -/
def mapPrepared (f : S₁ → S₂) (pending : Prepared Response S₁) : Prepared Response S₂ :=
  ⟨pending.response, pending.ciphertext, pending.ephemeral, pending.metadata, mapSecrets f pending.root⟩

/-- Two interpretations of the opaque preparation interface that differ only by a relabelling of the decapsulation handle. -/
structure MapCalls {m : Type → Type} [Monad m] (f : S₁ → S₂) (source : QueryImpl (Spec I D K X Response S₁) m)
    (target : QueryImpl (Spec I D K X Response S₂) m) : Prop where
  decode : ∀ raw, target (.decode raw) = source (.decode raw)
  ciphertext : ∀ response, target (.ciphertext response) = source (.ciphertext response)
  ephemeral : ∀ response, target (.ephemeral response) = source (.ephemeral response)
  serverIdentity : ∀ response, target (.serverIdentity response) = source (.serverIdentity response)
  publicConversion : ∀ value, target (.publicConversion value) = source (.publicConversion value)
  privateConversion : ∀ identity, target (.privateConversion identity) = source (.privateConversion identity)
  decapsulate : ∀ ciphertext kem, target (.decapsulate ciphertext kem) = Option.map f <$> source (.decapsulate ciphertext kem)
  dhPair : ∀ pair publicValue, target (.dhPair pair publicValue) = source (.dhPair pair publicValue)
  dhIdentity : ∀ identity publicValue, target (.dhIdentity identity publicValue) = source (.dhIdentity identity publicValue)
  assignedId : ∀ response, target (.assignedId response) = source (.assignedId response)
  eraseShared : ∀ secrets, target (.eraseShared (mapSecrets f secrets)) = source (.eraseShared secrets)

/-- The collection is natural in the handle type. -/
theorem collect_map {m : Type → Type} [Monad m] [LawfulMonad m] (f : S₁ → S₂)
    (source : QueryImpl (Spec I D K X Response S₁) m) (target : QueryImpl (Spec I D K X Response S₂) m)
    (calls : MapCalls f source target) (identity : I) (prekey oneTime : D) (kem : K) (raw : PqxdhBeaconPhase2Preparation.Bytes) :
    simulateQ target (collect identity prekey oneTime kem raw) =
      Option.map (mapInputs f) <$> simulateQ source (collect identity prekey oneTime kem raw) := by
  simp only [collect, OptionT.run_bind, OptionT.run_mk,
    OptionT.run_pure, OptionT.run_monadLift, Option.elimM, bind_map_left,
    simulateQ_bind, simulateQ_spec_query]
  simp only [calls.decode, map_bind]
  congr 1
  funext response
  cases response <;> simp only [Option.elim_none, Option.elim_some, simulateQ_pure, map_pure, Option.map_none]
  repeat' (
    simp only [simulateQ_bind, simulateQ_spec_query, simulateQ_pure, map_bind, map_pure,
      bind_map_left, calls.ciphertext, calls.ephemeral, calls.serverIdentity, calls.publicConversion,
      calls.privateConversion, calls.decapsulate, calls.dhPair, calls.dhIdentity, calls.assignedId,
      Option.elim_none, Option.elim_some, Option.map_none, Option.map_some]
    first | rfl | (congr 1; funext reply; cases reply))
  all_goals simp only [Option.elim, simulateQ_pure, map_pure, Option.map]

/-- Admission does not read the decapsulation handle. -/
theorem admitted_map (f : S₁ → S₂) (control : beaconcrypt_core.pqxdh.BeaconInitSent) (inputs : Inputs Response S₁) :
    admitted control (mapInputs f inputs) = admitted control inputs := by
  simp only [admitted, mapInputs, mapSecrets, PqxdhBeaconPhase2Shared.nonzero]
  congr

/-- The opaque preparation is natural in the handle type. -/
theorem prepare_map {m : Type → Type} [Monad m] [LawfulMonad m] (f : S₁ → S₂)
    (source : QueryImpl (Spec I D K X Response S₁) m) (target : QueryImpl (Spec I D K X Response S₂) m)
    (calls : MapCalls f source target) (control : beaconcrypt_core.pqxdh.BeaconInitSent) (identity : I)
    (prekey oneTime : D) (kem : K) (raw : PqxdhBeaconPhase2Preparation.Bytes) :
    simulateQ target (prepare control identity prekey oneTime kem raw) =
      Option.map (mapPrepared f) <$> simulateQ source (prepare control identity prekey oneTime kem raw) := by
  simp only [prepare, simulateQ_bind, collect_map f source target calls, bind_map_left, map_bind]
  refine bind_congr fun inputs => ?_
  rcases inputs with _ | inputs
  · simp only [Option.map_none, simulateQ_pure, map_pure]
  · simp only [Option.map_some, afterInputs, simulateQ_bind, simulateQ_spec_query, simulateQ_pure, map_bind, map_pure,
      admitted_map]
    rw [show (mapInputs f inputs).secrets = mapSecrets f inputs.secrets from rfl, calls.eraseShared]
    refine bind_congr fun _ => ?_
    rcases admitted control inputs with _ | metadata
    · rfl
    · rfl

/-- The collection decapsulates only with the owner's KEM key: a predicate that holds only on decapsulations with another key is never queried. -/
theorem collect_free {Shared : Type} (bad : Query I D K X Response Shared → Prop) [DecidablePred bad]
    (identity : I) (prekey oneTime : D) (kem : K) (raw : PqxdhBeaconPhase2Preparation.Bytes)
    (shaped : ∀ query, bad query → ∃ ciphertext key, query = .decapsulate ciphertext key ∧ key ≠ kem) :
    (collect (Response := Response) (X := X) identity prekey oneTime kem raw).IsQueryBoundP bad 0 := by
  have fine : ∀ query, (∀ ciphertext key, query = .decapsulate ciphertext key → key = kem) → ¬ bad query := by
    intro query shape hit
    obtain ⟨ciphertext, key, equal, other⟩ := shaped query hit
    exact other (shape ciphertext key equal)
  simp only [collect, OptionT.run_bind, OptionT.run_mk, OptionT.run_pure, OptionT.run_monadLift, Option.elimM,
    bind_map_left]
  repeat' (first
    | (rw [isQueryBoundP_query_bind_iff]; refine ⟨Or.inl (fine _ ?_), fun _ => ?_⟩)
    | (intro ciphertext key equal; cases equal; rfl)
    | (intro ciphertext key equal; cases equal)
    | (rename_i answer; cases answer <;> simp only [Option.elim_none, Option.elim_some]))
  all_goals simp only [isQueryBoundP_pure]

/-- The opaque preparation decapsulates only with the owner's KEM key. -/
theorem prepare_free {Shared : Type} (bad : Query I D K X Response Shared → Prop) [DecidablePred bad]
    (control : beaconcrypt_core.pqxdh.BeaconInitSent) (identity : I) (prekey oneTime : D) (kem : K)
    (raw : PqxdhBeaconPhase2Preparation.Bytes)
    (shaped : ∀ query, bad query → ∃ ciphertext key, query = .decapsulate ciphertext key ∧ key ≠ kem) :
    (prepare (Response := Response) (X := X) control identity prekey oneTime kem raw).IsQueryBoundP bad 0 := by
  unfold prepare
  rw [show (0 : ℕ) = 0 + 0 from rfl]
  refine isQueryBoundP_bind (collect_free (Response := Response) (X := X) bad identity prekey oneTime kem raw shaped)
    fun inputs _ => ?_
  rcases inputs with _ | inputs
  · simp only [isQueryBoundP_pure]
  · simp only [afterInputs]
    rw [isQueryBoundP_query_bind_iff]
    refine ⟨Or.inl fun hit => ?_, fun _ => by simp only [isQueryBoundP_pure]⟩
    obtain ⟨ciphertext, key, equal, -⟩ := shaped _ hit
    cases equal

end Natural

/-! ### The grouped owner from the opaque owner -/

section Group
open PqxdhRegistrationJointKemPostSkeleton (OwnerSpec Pending groupedOwner)
open PqxdhRegistrationJointBundle (Identity Key)
open PqxdhPhase2DecapsulationRouting (Shared)
variable {Response : Type} {m : Type → Type} [Monad m] [LawfulMonad m]

/-- An interpretation of the opaque owner's interface as one of the grouped owner's: preparation requests unchanged, a grouped request by the private root and the continuation after it. -/
noncomputable def groupH (handles : QueryImpl (PqxdhBeaconPhase2Shared.FullSpec Identity PqxdhJointGapDh.ScalarBytes Key ℕ
    Response Shared) m) (decode : RawCtxReceive.FrameDecoder) : QueryImpl (OwnerSpec Response) m
  | .inl query => handles (.inl query)
  | .inr pending => simulateQ (fun query => handles (.inr query)) (PqxdhBeaconPhase2Shared.tail decode pending)

/-- The opaque owner and the grouped owner have the same interpretation. -/
theorem owner_grouped (handles : QueryImpl (PqxdhBeaconPhase2Shared.FullSpec Identity PqxdhJointGapDh.ScalarBytes Key ℕ
    Response Shared) m) (decode : RawCtxReceive.FrameDecoder) (raw : Pqxdh.Bytes)
    (state : PqxdhRegistrationJointBundle.Owner) :
    simulateQ handles (PqxdhBeaconPhase2Shared.owner decode raw state) =
      simulateQ (groupH handles decode) (groupedOwner raw state) := by
  unfold PqxdhBeaconPhase2Shared.owner groupedOwner
  rcases phase : state.beacon.phase with _ | _ | ⟨control, prekey, oneTime, kem⟩ | _ | _
  all_goals try simp only [simulateQ_pure]
  simp only [simulateQ_bind]
  rw [← QueryImpl.simulateQ_compose, ← QueryImpl.simulateQ_compose]
  have pre : handles ∘ₛ PqxdhBeaconPhase2Shared.preLift = groupH handles decode ∘ₛ
      (fun query => ((OwnerSpec Response).query (.inl query) : OracleComp (OwnerSpec Response) _)) := by
    funext query
    simp only [QueryImpl.apply_compose, PqxdhBeaconPhase2Shared.preLift, simulateQ_spec_query]
    rfl
  rw [pre]
  refine bind_congr fun prepared => ?_
  rcases prepared with _ | pending
  · simp only [simulateQ_pure]
  · simp only [simulateQ_bind, simulateQ_pure, simulateQ_spec_query]
    rw [← QueryImpl.simulateQ_compose]
    have tail : handles ∘ₛ PqxdhBeaconPhase2Shared.tailLift = fun query => handles (.inr query) := by
      funext query
      simp only [QueryImpl.apply_compose, PqxdhBeaconPhase2Shared.tailLift, simulateQ_spec_query]
    rw [tail]
    rfl

end Group

/-! ### The preparation of a finish through the private services -/

section Preparation
open PqxdhRegistrationJointKemPostSkeleton (PreSpec)
open PqxdhRegistrationJointBundle (Identity Key)
open PqxdhPhase2DecapsulationRouting (Shared)
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}
  (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)

/-- Item 2's marked preparation (`PqxdhRegistrationJointBeaconOpaqueFinish.markedPreparation`) with every decapsulation answered by a known handle. -/
noncomputable def preparationKnown : QueryImpl (PreSpec Response) (OracleComp (PqxdhLiveKemBirth.Spec KemSK))
  | .decode raw => pure (codec.read2 raw)
  | .ciphertext response => pure (codec.ciphertext response)
  | .ephemeral response => pure (codec.ephemeral response)
  | .serverIdentity response => pure (codec.serverIdentity response)
  | .publicConversion server => pure ((setup.source.crypto.xpkConv (absBytes server)).bind
      PqxdhServerAuthExperiment.toWord32)
  | .privateConversion identity => pure (some identity.1)
  | .decapsulate ciphertext key =>
      Option.map Shared.known <$>
        (PqxdhLiveKemBirth.Spec KemSK).query (.inr (.inr (.decapsulate key.2 (PqxdhPhase2InputBytes.ciphertext ciphertext))))
  | .dhPair scalar point => pure ((PqxdhJointGapDh.sourceScalarDh setup.source.crypto scalar
      (PqxdhPhase2GapDhSource.peer point)).map PqxdhRootTableInitialization.rootArray)
  | .dhIdentity index point =>
      (fun reply => Option.map PqxdhRootTableInitialization.rootArray reply.join) <$>
        (PqxdhLiveKemBirth.Spec KemSK).query (.inl (.inr (.service index (.staticDh (PqxdhPhase2GapDhSource.peer point)))))
  | .assignedId response => pure (codec.assignedId response)
  | .eraseShared _ => pure ()

/-- The same preparation with the decapsulation result itself as the handle. -/
noncomputable def prepSecret :
    QueryImpl (Spec Identity PqxdhJointGapDh.ScalarBytes Key ℕ Response MlKemSharedSecret)
      (OracleComp (PqxdhLiveKemBirth.Spec KemSK))
  | .decode raw => pure (codec.read2 raw)
  | .ciphertext response => pure (codec.ciphertext response)
  | .ephemeral response => pure (codec.ephemeral response)
  | .serverIdentity response => pure (codec.serverIdentity response)
  | .publicConversion server => pure ((setup.source.crypto.xpkConv (absBytes server)).bind
      PqxdhServerAuthExperiment.toWord32)
  | .privateConversion identity => pure (some identity.1)
  | .decapsulate ciphertext key =>
      (PqxdhLiveKemBirth.Spec KemSK).query (.inr (.inr (.decapsulate key.2 (PqxdhPhase2InputBytes.ciphertext ciphertext))))
  | .dhPair scalar point => pure ((PqxdhJointGapDh.sourceScalarDh setup.source.crypto scalar
      (PqxdhPhase2GapDhSource.peer point)).map PqxdhRootTableInitialization.rootArray)
  | .dhIdentity index point =>
      (fun reply => Option.map PqxdhRootTableInitialization.rootArray reply.join) <$>
        (PqxdhLiveKemBirth.Spec KemSK).query (.inl (.inr (.service index (.staticDh (PqxdhPhase2GapDhSource.peer point)))))
  | .assignedId response => pure (codec.assignedId response)
  | .eraseShared _ => pure ()

/-- The decapsulation of the selected challenge ciphertext among the preparation requests. -/
def targetPrep (selected : ℕ) (challenge : MlKem768Ciphertext) : (PreSpec Response).Domain → Prop
  | .decapsulate ciphertext key => key.2 = selected ∧ PqxdhPhase2InputBytes.ciphertext ciphertext = challenge
  | _ => False

/-- Deciding the selected challenge decapsulation. -/
instance (selected : ℕ) (challenge : MlKem768Ciphertext) : DecidablePred (targetPrep (Response := Response) selected challenge)
  | .decapsulate ciphertext key =>
      inferInstanceAs (Decidable (key.2 = selected ∧ PqxdhPhase2InputBytes.ciphertext ciphertext = challenge))
  | .decode _ | .ciphertext _ | .ephemeral _ | .serverIdentity _ | .publicConversion _ | .privateConversion _
  | .dhPair _ _ | .dhIdentity _ _ | .assignedId _ | .eraseShared _ => inferInstanceAs (Decidable False)

/-- Away from the selected challenge decapsulation, item 2's marked preparation answers with known handles. -/
theorem markedPrep_known (selected : ℕ) (challenge : MlKem768Ciphertext) (query : (PreSpec Response).Domain)
    (other : ¬ targetPrep selected challenge query) :
    PqxdhRegistrationJointBeaconOpaqueFinish.markedPreparation setup codec selected challenge query =
      preparationKnown (KemSK := KemSK) setup codec query := by
  cases query with
  | decapsulate ciphertext key =>
      simp only [PqxdhRegistrationJointBeaconOpaqueFinish.markedPreparation, preparationKnown]
      simp only [targetPrep] at other
      simp only [other, decide_false]
      rfl
  | _ => rfl

/-- Item 2's marked preparation never creates a KEM key, never reveals one, and decapsulates the selected challenge ciphertext exactly on the selected challenge decapsulation request. -/
theorem markedPrep_bounds (selected : ℕ) (challenge : MlKem768Ciphertext) (query : (PreSpec Response).Domain) :
    (PqxdhRegistrationJointBeaconOpaqueFinish.markedPreparation (KemSK := KemSK) setup codec selected challenge
        query).IsQueryBoundP
          (fun request => PqxdhRegistrationJointServiceCosts.poolClass (KemSK := KemSK) request = .kemCreate) 0 ∧
      (PqxdhRegistrationJointBeaconOpaqueFinish.markedPreparation (KemSK := KemSK) setup codec selected challenge
        query).IsQueryBoundP
          (fun request => PqxdhRegistrationJointServiceCosts.poolClass (KemSK := KemSK) request = .other) 0 ∧
      (PqxdhRegistrationJointBeaconOpaqueFinish.markedPreparation (KemSK := KemSK) setup codec selected challenge
        query).IsQueryBoundP
          (fun request => PqxdhDeploymentIdealPostRequests.challengeDecaps (KemSK := KemSK) selected challenge request = true)
          (if targetPrep (Response := Response) selected challenge query then 1 else 0) := by
  refine ⟨?_, ?_, ?_⟩ <;> cases query
  all_goals simp only [PqxdhRegistrationJointBeaconOpaqueFinish.markedPreparation, isQueryBoundP_map_iff]
  all_goals first
    | trivial
    | (rw [isQueryBoundP_query_iff]; intro hit; simp [PqxdhRegistrationJointServiceCosts.poolClass] at hit)
    | (rw [isQueryBoundP_query_iff]; simp [PqxdhDeploymentIdealPostRequests.challengeDecaps, targetPrep]; done)
    | (rw [isQueryBoundP_query_iff]; simp only [PqxdhDeploymentIdealPostRequests.challengeDecaps, targetPrep,
        decide_eq_true_eq]; intro hit; simp [hit])

/-- The known-handle preparation is the secret-handle preparation with the handle relabelled by `known`. -/
theorem known_calls :
    MapCalls (I := Identity) (D := PqxdhJointGapDh.ScalarBytes) (K := Key) (X := ℕ) (Response := Response) Shared.known
      (fun query => simulateQ (PqxdhLiveKemBirth.impl setup.baseImpl setup.joint setup.kem) (prepSecret setup codec query))
      (fun query => simulateQ (PqxdhLiveKemBirth.impl setup.baseImpl setup.joint setup.kem)
        (preparationKnown setup codec query)) where
  decode _ := rfl
  ciphertext _ := rfl
  ephemeral _ := rfl
  serverIdentity _ := rfl
  publicConversion _ := rfl
  privateConversion _ := rfl
  decapsulate _ _ := simulateQ_map _ _ _
  dhPair _ _ := rfl
  dhIdentity _ _ := rfl
  assignedId _ := rfl
  eraseShared _ := rfl

end Preparation

/-! ### The source's finish with known handles -/

section Known
open PqxdhRegistrationJointBundle (Identity Key)
open PqxdhPhase2DecapsulationRouting (Shared)
open PqxdhRegistrationJointFinish (onPool onNative)
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}
  (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (candidate : MlKemSharedSecret)

/-- A pool step followed by a pure map. -/
theorem onPool_map {α β : Type} (f : α → β) (work : OracleComp (PqxdhLiveKemBirth.Spec KemSK) α) :
    onPool (simulateQ (PqxdhLiveKemBirth.impl setup.baseImpl setup.joint setup.kem) (f <$> work)) =
      f <$> onPool (simulateQ (PqxdhLiveKemBirth.impl setup.baseImpl setup.joint setup.kem) work) := by
  apply StateT.ext
  intro state
  rw [StateT.run_map]
  change (fun result : β × PqxdhLiveKemBirth.State KemSK => (result.1, (result.2, state.2))) <$>
      (simulateQ (PqxdhLiveKemBirth.impl setup.baseImpl setup.joint setup.kem) (f <$> work)).run state.1 =
    _ <$> ((fun result : α × PqxdhLiveKemBirth.State KemSK => (result.1, (result.2, state.2))) <$>
      (simulateQ (PqxdhLiveKemBirth.impl setup.baseImpl setup.joint setup.kem) work).run state.1)
  rw [simulateQ_map, StateT.run_map, Functor.map_map, Functor.map_map]

/-- The opaque owner's callbacks on the source's private pools and native state, with every decapsulation answered by a known handle and the private root derived from the handle's interpretation at `candidate` (`PqxdhRegistrationJointBeaconOpaqueFinish.markedRoot`). -/
noncomputable def handlesKnown :
    QueryImpl (PqxdhBeaconPhase2Shared.FullSpec Identity PqxdhJointGapDh.ScalarBytes Key ℕ Response Shared)
      (StateT (PqxdhRegistrationJointFinish.State KemSK) ProbComp)
  | .inl query => onPool (simulateQ (PqxdhLiveKemBirth.impl setup.baseImpl setup.joint setup.kem)
      (preparationKnown setup codec query))
  | .inr (.inl query) => PqxdhRegistrationJointFinish.callbacks setup codec (.inr (.inl query))
  | .inr (.inr (.root secrets)) => onNative (PqxdhRegistrationJointBeaconOpaqueFinish.markedRoot setup.hmac candidate secrets)
  | .inr (.inr (.initial request)) => PqxdhRegistrationJointFinish.callbacks setup codec (.inr (.inr (.initial request)))
  | .inr (.inr (.application response)) =>
      PqxdhRegistrationJointFinish.callbacks setup codec (.inr (.inr (.application response)))

/-- The source's callbacks realize the known-handle callbacks (item 2's `PqxdhBeaconPhase2Shared.FullCalls`), with the handle interpretation at `candidate`. -/
theorem known_fullCalls :
    PqxdhBeaconPhase2Shared.FullCalls (PqxdhRegistrationJointBeaconOpaqueFinish.interpret candidate)
      (PqxdhRegistrationJointFinish.callbacks setup codec) (handlesKnown (Response := Response) setup codec candidate) where
  preparation := {
    decode := fun _ => rfl
    ciphertext := fun _ => rfl
    ephemeral := fun _ => rfl
    serverIdentity := fun _ => rfl
    publicConversion := fun _ => rfl
    privateConversion := fun _ => rfl
    decapsulate := fun ciphertext key => by
      have left := onPool_map setup (Option.map PqxdhRootTableInitialization.rootArray)
        ((PqxdhLiveKemBirth.Spec KemSK).query (.inr (.inr (.decapsulate key.2
          (PqxdhPhase2InputBytes.ciphertext ciphertext)))) : OracleComp (PqxdhLiveKemBirth.Spec KemSK) _)
      have right := onPool_map setup (Option.map Shared.known)
        ((PqxdhLiveKemBirth.Spec KemSK).query (.inr (.inr (.decapsulate key.2
          (PqxdhPhase2InputBytes.ciphertext ciphertext)))) : OracleComp (PqxdhLiveKemBirth.Spec KemSK) _)
      refine left.trans (Eq.trans ?_ (congrArg (fun work =>
        Option.map (PqxdhRegistrationJointBeaconOpaqueFinish.interpret candidate) <$> work) right).symm)
      rw [Functor.map_map]
      congr 1
      funext result
      rcases result with _ | secret <;> rfl
    dhPair := fun _ _ => rfl
    dhIdentity := fun _ _ => rfl
    assignedId := fun _ => rfl
    eraseShared := fun _ => rfl }
  tail := {
    root := fun secrets input built => by
      change onNative _ = onNative (PqxdhRegistrationJointBeaconOpaqueFinish.markedRoot setup.hmac candidate secrets)
      simp only [PqxdhRegistrationJointBeaconOpaqueFinish.markedRoot, built]
      rfl
    initial := fun _ => rfl
    application := fun _ => rfl
    raw := fun _ => rfl }

/-- Lifting a pure computation on the shared commitment cache to the native state is pure. -/
theorem nativeCtx_pure {α : Type} (value : α) :
    PqxdhServerAuthNative.nativeCtx (KemSK := KemSK)
      (pure value : StateT (RawCtxSharedPrimitive.SharedState Unit) ProbComp α) = pure value := by
  rfl

/-- Lifting to the native state distributes over binds. -/
theorem nativeCtx_bind {α β : Type} (work : StateT (RawCtxSharedPrimitive.SharedState Unit) ProbComp α)
    (next : α → StateT (RawCtxSharedPrimitive.SharedState Unit) ProbComp β) :
    PqxdhServerAuthNative.nativeCtx (KemSK := KemSK) (work >>= next) =
      PqxdhServerAuthNative.nativeCtx work >>= fun value => PqxdhServerAuthNative.nativeCtx (next value) := by
  apply StateT.ext
  intro state
  show (fun result => (result.1, (state.1, { state.2 with ctx := result.2.2 }))) <$>
      (work >>= next).run ((), state.2.ctx) =
    ((fun result => (result.1, (state.1, { state.2 with ctx := result.2.2 }))) <$> work.run ((), state.2.ctx)) >>=
      fun middle => (fun result => (result.1, (middle.2.1, { middle.2.2 with ctx := result.2.2 }))) <$>
        (next middle.1).run ((), middle.2.2.ctx)
  rw [StateT.run_bind, map_bind, bind_map_left]

/-- Interpreting a program by computations on the shared commitment cache, each lifted to the native state, is lifting the interpreted program. -/
theorem simulate_nativeCtx {ι' α : Type} {spec : OracleSpec ι'}
    (handler : QueryImpl spec (StateT (RawCtxSharedPrimitive.SharedState Unit) ProbComp)) (work : OracleComp spec α) :
    simulateQ (fun query => PqxdhServerAuthNative.nativeCtx (KemSK := KemSK) (handler query)) work =
      PqxdhServerAuthNative.nativeCtx (simulateQ handler work) := by
  induction work using OracleComp.inductionOn with
  | pure value => simp only [simulateQ_pure, nativeCtx_pure]
  | query_bind query next ih => simp only [simulateQ_bind, simulateQ_spec_query, nativeCtx_bind, ih]

/-- The known-handle tail callbacks as native programs: the private root by `markedRoot`, everything else by the source's native tail. -/
noncomputable def tailKnown :
    QueryImpl (PqxdhBeaconPhase2Shared.TailSpec Response Shared) (PqxdhServerAuthNative.NativeGame KemSK)
  | .inl query => PqxdhServerAuthNative.sourceBeaconTail setup codec (.inl query)
  | .inr (.root secrets) => PqxdhRegistrationJointBeaconOpaqueFinish.markedRoot setup.hmac candidate secrets
  | .inr (.initial request) => PqxdhServerAuthNative.sourceBeaconTail setup codec (.inr (.initial request))
  | .inr (.application response) => PqxdhServerAuthNative.sourceBeaconTail setup codec (.inr (.application response))

/-- The known-handle tail of a grouped finish request is item 2's native grouped answer, on the native state. -/
theorem tail_known (pending : PqxdhRegistrationJointKemPostSkeleton.Pending Response)
    (state : PqxdhRegistrationJointFinish.State KemSK) :
    (simulateQ (fun query => handlesKnown setup codec candidate (.inr query))
        (PqxdhBeaconPhase2Shared.tail codec.frameRead pending)).run state =
      (fun result => (result.1, (state.1, result.2))) <$>
        (PqxdhRegistrationJointKemPostSkeleton.groupNativeN setup codec candidate pending).run state.2 := by
  have lifted : (fun query => handlesKnown setup codec candidate (.inr query) :
      QueryImpl (PqxdhBeaconPhase2Shared.TailSpec Response Shared) _) =
      fun query => onNative (tailKnown setup codec candidate query) := by
    funext query
    rcases query with query | (secrets | request | response) <;> rfl
  rw [lifted, PqxdhRegistrationJointFinish.native_program]
  congr 1
  unfold PqxdhBeaconPhase2Shared.tail PqxdhRegistrationJointKemPostSkeleton.groupNativeN
  simp only [simulateQ_bind, simulateQ_spec_query]
  rw [StateT.run_bind, StateT.run_bind]
  refine bind_congr fun result => ?_
  rcases result with ⟨_ | root, after⟩
  · rfl
  · change (simulateQ (tailKnown setup codec candidate)
      (PqxdhBeaconPhase2Shared.afterRoot codec.frameRead pending root)).run after = _
    rw [PqxdhRegistrationJointKemPostSkeleton.afterRoot_congr (tailKnown setup codec candidate)
      (fun query => PqxdhServerAuthNative.nativeCtx
        (PqxdhRegistrationJointKemPostSkeleton.tailNative setup codec query)) (fun _ => rfl) (fun _ => rfl)
      (fun _ => rfl), simulate_nativeCtx]

/-- Item 2's annotated source finish of a present owner, encoded: the grouped owner on the encoded owner under the known-handle callbacks, from the source's private pools and native state (through item 2's `PqxdhRegistrationJointServiceSchedule.finish_source`, `PqxdhRegistrationJointFinishCompiler.program_interpreted`, `PqxdhBeaconPhase2Shared.owner_realization` and `owner_grouped`). -/
theorem middle_finish (checks : Checks) (seed : PqxdhJointIdentity.IdentitySeed) (address : ℕ) (raw : Pqxdh.Bytes)
    (state : PqxdhRegistrationJointSchedule.State KemSK) (owned : PqxdhRegistrationJointSchedule.Invariant state)
    (entry : PqxdhRegistrationJointOwnership.Entry KemSK) (found : state.owners[address]? = some entry) :
    (fun result => (result.1, PqxdhRegistrationJointGeneratedFinish.encodeState setup result.2)) <$>
        (PqxdhRegistrationJointSchedule.finish setup codec address raw).run state =
      (fun result => (result.1.1, (⟨result.2.1, result.2.2, (state.owners.map
          (PqxdhRegistrationJointGeneratedFinish.encodeEntry setup)).set address
            ((PqxdhRegistrationJointGeneratedFinish.encodeEntry setup entry).1,
              (PqxdhRegistrationJointGeneratedFinish.encodeEntry setup entry).2.1, result.1.2)⟩ :
            PqxdhRegistrationJointGeneratedFinish.EncodedState KemSK))) <$>
        (simulateQ (groupH (handlesKnown setup codec candidate) codec.frameRead)
          (PqxdhRegistrationJointKemPostSkeleton.groupedOwner raw
            (PqxdhRegistrationJointGeneratedFinish.encodeEntry setup entry).2.2)).run (state.pool, state.shared) := by
  rw [← PqxdhRegistrationJointServiceSchedule.finish_source setup codec checks seed address raw state owned,
    ← owner_grouped, ← PqxdhBeaconPhase2Shared.owner_realization _ _ _ (known_fullCalls setup codec candidate)]
  have encoded : (PqxdhRegistrationJointGeneratedFinish.encodeState setup state).owners[address]? =
      some (PqxdhRegistrationJointGeneratedFinish.encodeEntry setup entry) := by
    simp [PqxdhRegistrationJointGeneratedFinish.encodeState, List.getElem?_map, found]
  simp only [PqxdhRegistrationJointServiceSchedule.execute, StateT.run, PqxdhRegistrationJointServiceSchedule.finish,
    encoded, simulateQ_map, PqxdhRegistrationJointServiceSchedule.finish_program,
    PqxdhRegistrationJointFinishCompiler.program_interpreted]
  change (fun result => _) <$> StateT.run ((fun result => _) <$> _) _ = (fun result => _) <$> StateT.run _ _
  rw [StateT.run_map, Functor.map_map]
  rfl

end Known

/-! ### Owner programs through item 2's layers -/

section Stack
open PqxdhRegistrationJointKemPostSkeleton (OwnerSpec PreSpec SkelState Enc TSpec fwd coinLift groupedCompiler
  groupedPoolLift skelImpl)
open PqxdhRegistrationJointKemEntryFactor (Output factoredServices)
open PqxdhDeploymentIdealPostSim (ServiceState SlotState serviceLayer)
open PqxdhDeploymentIdealPostHidden (lowerEC eraseServiceC eraseTables)
open PqxdhDeploymentIdealParams (Target Params)
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}
  (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks) {count : ℕ}
  (t : Target count) (p : Params KemSK count) (created : PqxdhLiveServerConstruction.Created Unit)

/-- A grouped owner program through item 2's layers: the grouped owner's callbacks, the skeleton's native layer, and the service layers with both observers erased. -/
noncomputable def stackRun {α : Type} (work : OracleComp (OwnerSpec Response) α) (skel : SkelState KemSK Output)
    (svc : ServiceState KemSK) : ProbComp (Option (α × SkelState KemSK Output) × ServiceState KemSK) :=
  ((simulateQ (lowerEC setup t p) ((simulateQ (skelImpl setup codec checks created.server.server.metadata.identityIndex
    created.publicIdentity (factoredServices setup codec checks))
      (simulateQ (groupedCompiler setup codec t.kem.val p.challenge) work)).run skel)).run).run svc

/-- A pure owner program through item 2's layers is pure and keeps both states. -/
theorem stackRun_pure {α : Type} (value : α) (skel : SkelState KemSK Output) (svc : ServiceState KemSK) :
    stackRun setup codec checks t p created (pure value : OracleComp (OwnerSpec Response) α) skel svc =
      pure (some (value, skel), svc) := by
  simp [stackRun]

/-- Item 2's layers distribute over binds of owner programs; a failure stops the continuation. -/
theorem stackRun_bind {α β : Type} (work : OracleComp (OwnerSpec Response) α)
    (next : α → OracleComp (OwnerSpec Response) β) (skel : SkelState KemSK Output) (svc : ServiceState KemSK) :
    stackRun setup codec checks t p created (work >>= next) skel svc =
      stackRun setup codec checks t p created work skel svc >>= fun result =>
        result.1.elim (pure (none, result.2)) fun value =>
          stackRun setup codec checks t p created (next value.1) value.2 result.2 := by
  simp only [stackRun, simulateQ_bind, StateT.run_bind, OptionT.run_bind, Option.elimM]
  refine bind_congr fun result => ?_
  rcases result with ⟨_ | value, after⟩ <;> rfl

/-- A private-service program sent through the grouped owner's pool lift and the skeleton reaches the exposed encapsulation interface unchanged. -/
theorem skel_groupedPool {α : Type} (client : OracleComp (PqxdhLiveKemBirth.Spec KemSK) α) (state : SkelState KemSK Output) :
    (simulateQ (skelImpl setup codec checks created.server.server.metadata.identityIndex created.publicIdentity
        (factoredServices setup codec checks))
      (simulateQ (groupedPoolLift (Response := Response)) client)).run state =
      (fun value => (value, state)) <$> simulateQ PqxdhDeploymentIdealPostRequests.poolUp client := by
  induction client using OracleComp.inductionOn with
  | pure value => simp
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, map_bind]
      have head : StateT.run (simulateQ (skelImpl setup codec checks created.server.server.metadata.identityIndex
          created.publicIdentity (factoredServices setup codec checks))
          (groupedPoolLift (Response := Response) query)) state =
          (fun reply => (reply, state)) <$> PqxdhDeploymentIdealPostRequests.poolUp query := by
        rw [show simulateQ (skelImpl setup codec checks created.server.server.metadata.identityIndex
            created.publicIdentity (factoredServices setup codec checks))
            (groupedPoolLift (Response := Response) query) =
            skelImpl setup codec checks created.server.server.metadata.identityIndex created.publicIdentity
              (factoredServices setup codec checks) (.inl (.inl (.inl query))) from simulateQ_spec_query _ _]
        rfl
      rw [head, bind_map_left]
      exact bind_congr fun reply => ih reply

/-- Item 2's service layers with both observers erased are the projection of the layers with the router transcripts erased. -/
theorem lowerEC_run {α : Type} (work : OracleComp (Enc KemSK + TSpec Output) α) (state : ServiceState KemSK) :
    ((simulateQ (lowerEC setup t p) work).run).run (eraseServiceC state) =
      Prod.map id eraseServiceC <$>
        ((simulateQ (PqxdhDeploymentIdealPostSteps.lowerE setup t p) work).run).run
          (PqxdhDeploymentIdealPostSim.eraseService state) := by
  have counted := PqxdhRegistrationJointKemObserverFree.run_eraseOption eraseServiceC
    PqxdhDeploymentIdealPostHidden.eraseServiceC_idem _
    (PqxdhDeploymentIdealPostHidden.serviceLayer_neverReadC setup t.kem p.chosen p.others p.challenge) work state
  have erased := PqxdhRegistrationJointKemObserverFree.run_eraseOption PqxdhDeploymentIdealPostSim.eraseService
    (fun state => by simp only [PqxdhDeploymentIdealPostSim.eraseService, Prod.map,
      PqxdhRegistrationJointKemObserverFree.eraseJoint_idem, id_eq])
    _ (PqxdhDeploymentIdealPostSim.serviceLayer_neverRead setup t.kem p.chosen p.others p.challenge) work state
  rw [← counted]
  change _ = Prod.map id eraseServiceC <$> ((simulateQ (PqxdhRegistrationJointKemObserverFree.eraseOptionImpl
    PqxdhDeploymentIdealPostSim.eraseService (serviceLayer setup t.kem p.chosen p.others p.challenge)) work).run).run
      (PqxdhDeploymentIdealPostSim.eraseService state)
  rw [← erased, Functor.map_map]
  refine congrArg (fun f => f <$> _) (funext fun result => ?_)
  simp only [Prod.map, id_eq, PqxdhDeploymentIdealPostHidden.eraseServiceC_eraseService]

/-- The preparation part of a grouped owner, with no decapsulation of the selected challenge ciphertext, through item 2's layers from the erased router state of a prefix pool: item 2's marked preparation under the actual services, which answers with known handles; the skeleton state is kept, the router state is that of the final pool, the table state keeps its contents. -/
theorem stack_prep {β : Type} (work : OracleComp (PreSpec Response) β)
    (free : work.IsQueryBoundP (targetPrep t.kem.val p.challenge) 0)
    (joint : PqxdhDynamicIdentityPool.SourceState) (pool : PqxdhLiveKemBirth.Pool KemSK)
    (prefixed : PqxdhDeploymentIdealPoolSource.PoolPrefix (p.pool t) pool)
    (tables : PqxdhSecretInputKdf.HmacOracle.QueryCache × SlotState) (skel : SkelState KemSK Output) :
    stackRun setup codec checks t p created
        (simulateQ (fun query => ((OwnerSpec Response).query (.inl query) : OracleComp (OwnerSpec Response) _)) work) skel
        (eraseServiceC ((joint, PqxdhDeploymentIdealPoolSource.routerOf pool), tables)) =
      (fun result => (some (result.1, skel), (PqxdhRegistrationJointKemObserverFree.eraseJoint
          (result.2.1, PqxdhDeploymentIdealPoolSource.routerOf result.2.2), eraseTables tables))) <$>
        (simulateQ (fun query => simulateQ (PqxdhLiveKemBirth.impl setup.baseImpl setup.joint setup.kem)
          (preparationKnown setup codec query)) work).run (joint, pool) := by
  have compiled : simulateQ (groupedCompiler setup codec t.kem.val p.challenge)
      (simulateQ (fun query => ((OwnerSpec Response).query (.inl query) : OracleComp (OwnerSpec Response) _)) work) =
      simulateQ (groupedPoolLift (Response := Response))
        (simulateQ (PqxdhRegistrationJointBeaconOpaqueFinish.markedPreparation setup codec t.kem.val p.challenge)
          work) := by
    rw [← QueryImpl.simulateQ_compose, ← QueryImpl.simulateQ_compose]
    congr 1
    funext query
    simp only [QueryImpl.apply_compose, simulateQ_spec_query]
    rfl
  have bounds := fun query => markedPrep_bounds (KemSK := KemSK) (Response := Response) setup codec t.kem.val
    p.challenge query
  have noCreate : (simulateQ (PqxdhRegistrationJointBeaconOpaqueFinish.markedPreparation setup codec t.kem.val
      p.challenge) work).IsQueryBoundP (PqxdhLiveKemReservation.IsCreate (KemSK := KemSK)) 0 := by
    refine (isQueryBoundP_congr_pred (fun query => ?_)).mpr
      (PqxdhRegistrationJointBeaconOpaqueFinishRouter.simulateQ_free _ _ (fun query => (bounds query).1) work)
    rw [PqxdhDeploymentIdealPoolSource.isCreate_class]
  have noReveal := PqxdhRegistrationJointBeaconOpaqueFinishRouter.simulateQ_free _ _ (fun query => (bounds query).2.1)
    work
  have fresh := PqxdhRegistrationJointBeaconOpaqueFinishRouter.simulateQ_transfer _ _ _ (fun query => (bounds query).2.2)
    work free
  unfold stackRun
  rw [compiled, skel_groupedPool, simulateQ_map, OptionT.run_map, StateT.run_map, lowerEC_run,
    show PqxdhDeploymentIdealPostSim.eraseService ((joint, PqxdhDeploymentIdealPoolSource.routerOf pool), tables) =
      (PqxdhRegistrationJointKemObserverFree.eraseJoint (joint, PqxdhDeploymentIdealPoolSource.routerOf pool), tables)
      from rfl,
    PqxdhDeploymentIdealPostRequests.lowerE_pool setup t p _ 0 noCreate noReveal fresh joint pool prefixed
      (by simpa using PqxdhDeploymentIdealPostRequests.prefix_length _ _ prefixed),
    PqxdhDeploymentIdealPoolSource.reserved_noCreate setup (p.pool t) _ noCreate, ← QueryImpl.simulateQ_compose,
    PqxdhRegistrationJointBeaconOpaqueFinishRouter.simulateQ_agree _
      (fun query => simulateQ (PqxdhLiveKemBirth.impl setup.baseImpl setup.joint setup.kem)
        (preparationKnown setup codec query)) _ (fun query other => by
          simp only [QueryImpl.apply_compose, markedPrep_known setup codec t.kem.val p.challenge query other]) work free]
  simp only [Functor.map_map]
  rfl

/-- A computation on the shared commitment cache splits into the skeleton's game-state step on the same computation. -/
theorem splitT_ctx {α : Type} (work : StateT (RawCtxSharedPrimitive.SharedState Unit) ProbComp α) :
    PqxdhDeploymentIdealPostServer.SplitT (KemSK := KemSK) (PqxdhServerAuthNative.nativeCtx work)
      (PqxdhRegistrationJointKemPostSkeleton.gameStep (PqxdhRegistrationJointKemPostSkeleton.ctxGame work)) := by
  intro native marks slots
  rw [PqxdhRegistrationJointKemPostSkeleton.gameStep_run, simulateQ_map, StateT.run_map,
    PqxdhDeploymentIdealPostItem.tableLayer_lift]
  simp only [PqxdhRegistrationJointKemPostSkeleton.ctxGame, PqxdhServerAuthNative.nativeCtx, StateT.run,
    Functor.map_map]
  rfl

/-- The grouped finish with a known decapsulation result splits: the skeleton reads the root input directly from the table, the native answer derives the root from the same table entry, and both run the native continuation after the root. -/
theorem splitT_group_known (candidate : MlKemSharedSecret) (pending : PqxdhRegistrationJointKemPostSkeleton.Pending Response)
    (secret : MlKemSharedSecret) (known : pending.root.shared = .known secret) :
    PqxdhDeploymentIdealPostServer.SplitT (KemSK := KemSK)
      (PqxdhRegistrationJointKemPostSkeleton.groupNativeN setup codec candidate pending)
      (PqxdhRegistrationJointKemPostSkeleton.groupStep setup codec (factoredServices setup codec checks) pending) := by
  intro native marks slots
  obtain ⟨response, ciphertext, ephemeral, metadata, ⟨dh1, dh2, dh3, dh4, shared⟩⟩ := pending
  simp only at known
  subst known
  by_cases nonzero : Pqxdh.dhNonZero (absBytes dh1, absBytes dh2, absBytes dh3, absBytes dh4)
  · obtain ⟨input, built, -⟩ := (PqxdhRefinement.build_root_key_input_abs
      (PqxdhBeaconPhase2Shared.concreteSecrets (PqxdhRegistrationJointBeaconOpaqueFinish.interpret candidate)
        ⟨dh1, dh2, dh3, dh4, .known secret⟩)).1 nonzero
    have bytes := PqxdhPhase2InputBytes.root_input _ input built
    have sside : PqxdhRegistrationJointKemPostSkeleton.groupNativeN (KemSK := KemSK) setup codec candidate
        ⟨response, ciphertext, ephemeral, metadata, ⟨dh1, dh2, dh3, dh4, .known secret⟩⟩ =
        PqxdhServerAuthNative.sourceRoot setup.hmac input >>= fun root => match root with
          | none => pure none
          | some root => PqxdhServerAuthNative.nativeCtx (simulateQ (PqxdhRegistrationJointKemPostSkeleton.tailNative
              setup codec) (PqxdhBeaconPhase2Shared.afterRoot codec.frameRead
                ⟨response, ciphertext, ephemeral, metadata, ⟨dh1, dh2, dh3, dh4, .known secret⟩⟩ root)) := by
      simp only [PqxdhRegistrationJointKemPostSkeleton.groupNativeN, PqxdhRegistrationJointBeaconOpaqueFinish.markedRoot,
        built]
      rfl
    have tside : PqxdhRegistrationJointKemPostSkeleton.groupStep (KemSK := KemSK) setup codec
        (factoredServices setup codec checks)
        ⟨response, ciphertext, ephemeral, metadata, ⟨dh1, dh2, dh3, dh4, .known secret⟩⟩ =
        PqxdhRegistrationJointKemPostSkeleton.tableRead (PqxdhHiddenRoot.hiddenRootIKM
          (PqxdhPhase2InputBytes.coordinates dh1 dh2 dh3 dh4) secret) >>=
          fun block => PqxdhRegistrationJointKemPostSkeleton.gameStep (PqxdhRegistrationJointKemPostSkeleton.ctxGame
            (simulateQ (PqxdhRegistrationJointKemPostSkeleton.tailNative setup codec)
              (PqxdhBeaconPhase2Shared.afterRoot codec.frameRead
                ⟨response, ciphertext, ephemeral, metadata, ⟨dh1, dh2, dh3, dh4, .known secret⟩⟩
                (PqxdhRootTableInitialization.rootArray (PqxdhSecretInputKdf.expandRoot setup.hmac block))))) := by
      simp only [PqxdhRegistrationJointKemPostSkeleton.groupStep, nonzero, ite_true]
    have same : absBytes input.bytes = PqxdhHiddenRoot.hiddenRootIKM
        (PqxdhPhase2InputBytes.coordinates dh1 dh2 dh3 dh4) secret := by
      rw [bytes]
      simp only [PqxdhBeaconPhase2Shared.concreteSecrets, PqxdhRegistrationJointBeaconOpaqueFinish.interpret,
        PqxdhPhase2DecapsulationRouting.materialize, PqxdhPhase2InputBytes.word_rootArray]
    rw [sside, tside, StateT.run_bind, simulateQ_bind, StateT.run_bind, PqxdhDeploymentIdealPostServer.tableRead_run,
      bind_map_left, StateT.run_bind, PqxdhRegistrationJointKemPostSkeleton.sourceRoot_run, bind_map_left, map_bind]
    rw [same]
    refine bind_congr fun result => ?_
    exact splitT_ctx _ (({ native.1 with cache := result.2 } : PqxdhJointDhExtractFamily.State), native.2) marks slots
  · have rejected := (PqxdhRefinement.build_root_key_input_abs
      (PqxdhBeaconPhase2Shared.concreteSecrets (PqxdhRegistrationJointBeaconOpaqueFinish.interpret candidate)
        ⟨dh1, dh2, dh3, dh4, .known secret⟩)).2 nonzero
    have sside : PqxdhRegistrationJointKemPostSkeleton.groupNativeN (KemSK := KemSK) setup codec candidate
        ⟨response, ciphertext, ephemeral, metadata, ⟨dh1, dh2, dh3, dh4, .known secret⟩⟩ = pure none := by
      simp only [PqxdhRegistrationJointKemPostSkeleton.groupNativeN, PqxdhRegistrationJointBeaconOpaqueFinish.markedRoot,
        rejected, pure_bind]
    have tside : PqxdhRegistrationJointKemPostSkeleton.groupStep (KemSK := KemSK) setup codec
        (factoredServices setup codec checks)
        ⟨response, ciphertext, ephemeral, metadata, ⟨dh1, dh2, dh3, dh4, .known secret⟩⟩ = pure none := by
      simp only [PqxdhRegistrationJointKemPostSkeleton.groupStep, nonzero, ite_false]
    rw [sside, tside]
    exact PqxdhDeploymentIdealPostServer.splitT_pure none native marks slots

/-- A grouped finish request with a known decapsulation result through item 2's layers is item 2's native grouped answer (`PqxdhRegistrationJointKemPostSkeleton.groupNativeN`, at any candidate) on the native state, with the router state kept and the table counters erased. -/
theorem stack_known (candidate : MlKemSharedSecret) (pending : PqxdhRegistrationJointKemPostSkeleton.Pending Response)
    (secret : MlKemSharedSecret) (known : pending.root.shared = .known secret)
    (joint : PqxdhDynamicIdentityPool.SourceState) (pool : PqxdhLiveKemBirth.Pool KemSK)
    (native : PqxdhServerAuthNative.NativeState KemSK) (marks : PqxdhRegistrationJointKemPostSkeleton.Marks Output)
    (slots : SlotState) :
    stackRun setup codec checks t p created
        ((OwnerSpec Response).query (.inr pending) : OracleComp (OwnerSpec Response) _)
        (PqxdhRegistrationJointKemPostSkeleton.clean native.2, marks)
        (eraseServiceC ((joint, PqxdhDeploymentIdealPoolSource.routerOf pool), (native.1.cache, slots))) =
      (fun result => (some (result.1, (PqxdhRegistrationJointKemPostSkeleton.clean result.2.2, marks)),
          (PqxdhRegistrationJointKemObserverFree.eraseJoint (joint, PqxdhDeploymentIdealPoolSource.routerOf pool),
            eraseTables (result.2.1.cache, slots)))) <$>
        (PqxdhRegistrationJointKemPostSkeleton.groupNativeN setup codec candidate pending).run native := by
  unfold stackRun
  rw [simulateQ_spec_query, show groupedCompiler setup codec t.kem.val p.challenge (.inr pending) =
      (PqxdhRegistrationJointKemPostSkeleton.GSpec KemSK Response).query (.inr pending) from rfl, simulateQ_spec_query,
    show (skelImpl setup codec checks created.server.server.metadata.identityIndex created.publicIdentity
      (factoredServices setup codec checks) (.inr pending)).run (PqxdhRegistrationJointKemPostSkeleton.clean native.2, marks) =
      simulateQ (fwd (T := TSpec Output) (coinLift (KemSK := KemSK)))
        ((PqxdhRegistrationJointKemPostSkeleton.groupStep setup codec (factoredServices setup codec checks) pending).run
          (PqxdhRegistrationJointKemPostSkeleton.clean native.2, marks)) from rfl,
    lowerEC_run,
    show PqxdhDeploymentIdealPostSim.eraseService ((joint, PqxdhDeploymentIdealPoolSource.routerOf pool),
      (native.1.cache, slots)) = (PqxdhRegistrationJointKemObserverFree.eraseJoint
        (joint, PqxdhDeploymentIdealPoolSource.routerOf pool), (native.1.cache, slots)) from rfl,
    PqxdhDeploymentIdealPostSteps.lowerE_native setup t p _ _ (by
      simp only [PqxdhDeploymentIdealPostSim.eraseService, Prod.map, PqxdhRegistrationJointKemObserverFree.eraseJoint_idem,
        id_eq]),
    splitT_group_known setup codec checks candidate pending secret known native marks slots]
  simp only [Functor.map_map]
  refine congrArg (fun f => f <$> _) (funext fun result => ?_)
  simp only [Prod.map, id_eq, eraseServiceC, PqxdhRegistrationJointKemObserverFree.eraseJoint_idem]

/-- A grouped Beacon owner whose KEM key is not the selected one, through item 2's layers from a state that projects the source's private pools and native state, is the owner under the known-handle callbacks on the source's state, projected. -/
theorem owner_stack (candidate : MlKemSharedSecret) (raw : Pqxdh.Bytes) (owner : PqxdhRegistrationJointBundle.Owner)
    (fresh : ∀ control prekey oneTime kem, owner.beacon.phase = .initSent control prekey oneTime kem → kem.2 ≠ t.kem.val)
    (joint : PqxdhDynamicIdentityPool.SourceState) (pool : PqxdhLiveKemBirth.Pool KemSK)
    (prefixed : PqxdhDeploymentIdealPoolSource.PoolPrefix (p.pool t) pool)
    (native : PqxdhServerAuthNative.NativeState KemSK) (marks : PqxdhRegistrationJointKemPostSkeleton.Marks Output)
    (slots : SlotState) :
    stackRun setup codec checks t p created (PqxdhRegistrationJointKemPostSkeleton.groupedOwner raw owner)
        (PqxdhRegistrationJointKemPostSkeleton.clean native.2, marks)
        (eraseServiceC ((joint, PqxdhDeploymentIdealPoolSource.routerOf pool), (native.1.cache, slots))) =
      (fun result => (some (result.1, (PqxdhRegistrationJointKemPostSkeleton.clean result.2.2.2, marks)),
          eraseServiceC ((result.2.1.1, PqxdhDeploymentIdealPoolSource.routerOf result.2.1.2),
            (result.2.2.1.cache, slots)))) <$>
        (simulateQ (groupH (handlesKnown setup codec candidate) codec.frameRead)
          (PqxdhRegistrationJointKemPostSkeleton.groupedOwner raw owner)).run ((joint, pool), native) := by
  unfold PqxdhRegistrationJointKemPostSkeleton.groupedOwner
  rcases phase : owner.beacon.phase with _ | _ | ⟨control, prekey, oneTime, kem⟩ | _ | _
  all_goals dsimp only
  case fresh | freshWithCoins | established | aborted =>
    rw [stackRun_pure]
    simp only [simulateQ_pure, StateT.run_pure, map_pure]
  case initSent =>
    have notSelected := fresh control prekey oneTime kem phase
    have free : (prepare control owner.beacon.identity prekey oneTime kem raw :
        OracleComp (PreSpec Response) _).IsQueryBoundP (targetPrep t.kem.val p.challenge) 0 :=
      prepare_free _ control _ _ _ kem raw fun query hit => by
        cases query with
        | decapsulate ciphertext key => exact ⟨ciphertext, key, rfl, fun same => notSelected (same ▸ hit.1)⟩
        | _ => exact hit.elim
    rw [stackRun_bind, stack_prep setup codec checks t p created _ free joint pool prefixed (native.1.cache, slots)]
    rw [simulateQ_bind, StateT.run_bind, ← QueryImpl.simulateQ_compose]
    have inl : (groupH (handlesKnown setup codec candidate) codec.frameRead ∘ₛ
        (fun query => ((OwnerSpec Response).query (.inl query) : OracleComp (OwnerSpec Response) _))) =
        fun query => PqxdhRegistrationJointFinish.onPool (simulateQ (PqxdhLiveKemBirth.impl setup.baseImpl setup.joint
          setup.kem) (preparationKnown setup codec query)) := by
      funext query
      simp only [QueryImpl.apply_compose, simulateQ_spec_query]
      rfl
    rw [inl, PqxdhRegistrationJointFinish.pool_program,
      prepare_map PqxdhPhase2DecapsulationRouting.Shared.known _ _ (known_calls setup codec) control owner.beacon.identity prekey oneTime kem raw,
      StateT.run_map]
    simp only [Functor.map_map, bind_map_left, map_bind]
    refine bind_congr fun result => ?_
    rcases result with ⟨_ | prepared, after⟩
    · simp only [Option.map_none, Option.elim_some]
      rw [stackRun_pure]
      simp only [simulateQ_pure, StateT.run_pure, map_pure]
      rfl
    · simp only [Option.map_some, Option.elim_some]
      rw [show (PqxdhRegistrationJointKemObserverFree.eraseJoint (after.1, PqxdhDeploymentIdealPoolSource.routerOf after.2),
          eraseTables (native.1.cache, slots)) =
          eraseServiceC ((after.1, PqxdhDeploymentIdealPoolSource.routerOf after.2), (native.1.cache, slots)) from rfl,
        stackRun_bind, stack_known setup codec checks t p created candidate _ prepared.root.shared rfl after.1 after.2
          native marks slots, simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
      change _ = _ <$> ((simulateQ (fun query => handlesKnown setup codec candidate (.inr query))
        (PqxdhBeaconPhase2Shared.tail codec.frameRead
          (mapPrepared PqxdhPhase2DecapsulationRouting.Shared.known prepared))).run (after, native) >>= _)
      rw [tail_known]
      simp only [bind_map_left, map_bind]
      refine bind_congr fun result => ?_
      simp only [Option.elim_some]
      rw [stackRun_pure]
      simp only [simulateQ_pure, StateT.run_pure, map_pure]
      rfl

end Stack

/-! ### The real finish -/

section Finish
open PqxdhRegistrationJointKemPostSkeleton (SkelState clean)
open PqxdhRegistrationJointKemEntryFactor (Output factoredServices)
open PqxdhDeploymentIdealPostSim (upperLayer)
open PqxdhDeploymentIdealPostSource (Mid sourceMid)
open PqxdhDeploymentIdealPostSteps (encodeMid)
open PqxdhDeploymentIdealPostHidden (StepAtC encodeMidC eraseServiceC)
open PqxdhDeploymentIdealParams (Target Params)
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}
  (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
  (checks : Checks) {count : ℕ} (t : Target count) (p : Params KemSK count)
  (created : PqxdhLiveServerConstruction.Created Unit)

/-- On a finish that is not owner k's challenge finish, the middle source handler is the annotated source finish. -/
theorem sourceMid_finish (owner : ℕ) (raw : Pqxdh.Bytes) (m : Mid KemSK)
    (real : PqxdhDeploymentIdealPostSource.finishHiddenAt t m owner = false) :
    (sourceMid setup codec route checks t p created (.inl (.inr (.finish owner raw)))).run m =
      (fun result => (result.1, { m with joint := result.2 })) <$>
        (PqxdhRegistrationJointSchedule.finish setup codec owner raw).run m.joint := by
  change (if PqxdhDeploymentIdealPostSource.finishHiddenAt t m owner then _ else _) = _
  simp only [real, Bool.false_eq_true, ↓reduceIte]
  rfl

/-- The upper layers on a finish at a present address: the grouped owner through the skeleton, then the owner reinstalled. -/
theorem upperLayer_finish (owner : ℕ) (raw : Pqxdh.Bytes) (entry : PqxdhRegistrationJointGeneratedFinish.EncodedEntry)
    (state : List PqxdhRegistrationJointGeneratedFinish.EncodedEntry × SkelState KemSK Output)
    (found : state.1[owner]? = some entry) :
    (upperLayer setup codec checks created.server.server.metadata.identityIndex created.publicIdentity t.kem.val
        p.challenge (factoredServices setup codec checks) (.inl (.inr (.finish owner raw)))).run state =
      (fun result => (result.1.1, (state.1.set owner (entry.1, entry.2.1, result.1.2), result.2))) <$>
        (simulateQ (PqxdhRegistrationJointKemPostSkeleton.skelImpl setup codec checks
          created.server.server.metadata.identityIndex created.publicIdentity (factoredServices setup codec checks))
          (simulateQ (PqxdhRegistrationJointKemPostSkeleton.groupedCompiler setup codec t.kem.val p.challenge)
            (PqxdhRegistrationJointKemPostSkeleton.groupedOwner raw entry.2.2))).run state.2 := by
  rcases state with ⟨owners, skel⟩
  simp only [upperLayer, QueryImpl.flattenStateT, QueryImpl.mapStateTBase, StateT.run_mk,
    PqxdhRegistrationJointKemPostSkeleton.groupedClient]
  change (fun x => (x.1.1, x.1.2, x.2)) <$> StateT.run (simulateQ _
    (PqxdhRegistrationJointKemPostSkeleton.groupedFinish setup codec t.kem.val p.challenge owner raw owners)) skel = _
  simp only [PqxdhRegistrationJointKemPostSkeleton.groupedFinish, found, simulateQ_map, StateT.run_map,
    Functor.map_map]

/-- The upper layers on a finish at an absent address: nothing happens. -/
theorem upperLayer_finish_none (owner : ℕ) (raw : Pqxdh.Bytes)
    (state : List PqxdhRegistrationJointGeneratedFinish.EncodedEntry × SkelState KemSK Output)
    (missing : state.1[owner]? = none) :
    (upperLayer setup codec checks created.server.server.metadata.identityIndex created.publicIdentity t.kem.val
        p.challenge (factoredServices setup codec checks) (.inl (.inr (.finish owner raw)))).run state =
      pure (none, state) := by
  rcases state with ⟨owners, skel⟩
  simp only [upperLayer, QueryImpl.flattenStateT, QueryImpl.mapStateTBase, StateT.run_mk,
    PqxdhRegistrationJointKemPostSkeleton.groupedClient]
  change (fun x => (x.1.1, x.1.2, x.2)) <$> StateT.run (simulateQ _
    (PqxdhRegistrationJointKemPostSkeleton.groupedFinish setup codec t.kem.val p.challenge owner raw owners)) skel = _
  simp only [PqxdhRegistrationJointKemPostSkeleton.groupedFinish, missing]
  simp

/-- A finish that is not owner k's challenge finish, of an owner whose KEM index is not the selected one or which is not waiting for Phase 2: item 2's grouped finish through item 2's layers is the annotated source finish on the middle state. It needs item 2's ownership invariant and a prefix KEM pool. -/
theorem step_finish (owner : ℕ) (raw : Pqxdh.Bytes) (m : Mid KemSK)
    (real : PqxdhDeploymentIdealPostSource.finishHiddenAt t m owner = false)
    (owned : PqxdhRegistrationJointSchedule.Invariant m.joint)
    (prefixed : PqxdhDeploymentIdealPoolSource.PoolPrefix (p.pool t) m.joint.pool.2)
    (other : ∀ entry, m.joint.owners[owner]? = some entry → entry.kemIndex = t.kem.val →
      ∀ control prekey oneTime kem, entry.owner.beacon.phase ≠ .initSent control prekey oneTime kem) :
    StepAtC setup codec route checks t p created (.inl (.inr (.finish owner raw))) m := by
  unfold StepAtC
  rw [show (encodeMidC setup m).1 = (encodeMid setup m).1 from rfl,
    PqxdhDeploymentIdealPostSteps.upperE_run setup codec checks t p created _ _
      (PqxdhDeploymentIdealPostSteps.encodeMid_clean setup m),
    sourceMid_finish setup codec route checks t p created owner raw m real]
  rcases found : m.joint.owners[owner]? with _ | entry
  · have missing : (encodeMid setup m).1.1[owner]? = none := by
      simp [encodeMid, PqxdhRegistrationJointGeneratedFinish.encodeState, List.getElem?_map, found]
    rw [upperLayer_finish_none setup codec checks t p created owner raw _ missing, map_pure, simulateQ_pure]
    simp only [PqxdhRegistrationJointSchedule.finish, found, StateT.run]
    simp only [OptionT.run_pure, map_pure]
    rfl
  · have present : (encodeMid setup m).1.1[owner]? = some (PqxdhRegistrationJointGeneratedFinish.encodeEntry setup entry) := by
      simp [encodeMid, PqxdhRegistrationJointGeneratedFinish.encodeState, List.getElem?_map, found]
    have fresh : ∀ control prekey oneTime kem,
        (PqxdhRegistrationJointGeneratedFinish.encodeEntry setup entry).2.2.beacon.phase =
          .initSent control prekey oneTime kem → kem.2 ≠ t.kem.val := by
      intro control prekey oneTime kem phase selected
      rcases original : entry.owner.beacon.phase with _ | _ | ⟨control', prekey', oneTime', kem'⟩ | _ | _
      all_goals simp [PqxdhRegistrationJointGeneratedFinish.encodeEntry, PqxdhRegistrationJointBundle.encode,
        PqxdhBeaconPhase1Publication.mapState, PqxdhBeaconPhase1Publication.mapPhase, original] at phase
      obtain ⟨_, _, _, keyed⟩ := phase
      subst keyed
      exact other entry found selected control' prekey' oneTime' kem' original
    have start : (encodeMidC setup m).2 = eraseServiceC ((m.joint.pool.1,
        PqxdhDeploymentIdealPoolSource.routerOf m.joint.pool.2), (m.joint.shared.1.cache, (m.backend.2.1, m.backend.1))) := by
      simp only [encodeMidC, encodeMid, eraseServiceC, Prod.map, PqxdhRegistrationJointKemObserverFree.eraseJoint_idem]
    have stack := owner_stack setup codec checks t p created (List.Vector.replicate 32 0) raw _ fresh m.joint.pool.1
      m.joint.pool.2 prefixed m.joint.shared (PqxdhDeploymentIdealPostSteps.skelMarks m) (m.backend.2.1, m.backend.1)
    rw [← start] at stack
    unfold stackRun at stack
    have middle := middle_finish setup codec (List.Vector.replicate 32 0) checks created.seed owner raw m.joint owned
      entry found
    rw [upperLayer_finish setup codec checks t p created owner raw _ _ present, Functor.map_map, simulateQ_map,
      OptionT.run_map, StateT.run_map]
    erw [stack]
    refine Eq.trans ?_ (?_ : (fun result : _ × PqxdhRegistrationJointGeneratedFinish.EncodedState KemSK =>
        (some (result.1, (result.2.owners, (clean result.2.shared.2, PqxdhDeploymentIdealPostSteps.skelMarks m))),
          eraseServiceC ((result.2.pool.1, PqxdhDeploymentIdealPoolSource.routerOf result.2.pool.2),
            (result.2.shared.1.cache, (m.backend.2.1, m.backend.1))))) <$>
        ((fun result => (result.1, PqxdhRegistrationJointGeneratedFinish.encodeState setup result.2)) <$>
          (PqxdhRegistrationJointSchedule.finish setup codec owner raw).run m.joint) = _)
    · rw [middle, Functor.map_map, Functor.map_map]
      refine congrArg (fun f => f <$> _) (funext fun result => ?_)
      rfl
    · simp only [Functor.map_map]
      rfl

end Finish

end BeaconcryptCore.Computational.PqxdhDeploymentIdealPostFinish

-- Axiom guards (generated)

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPostFinish.collect_map' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPostFinish.collect_map

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPostFinish.admitted_map' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPostFinish.admitted_map

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPostFinish.prepare_map' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPostFinish.prepare_map

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPostFinish.collect_free' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPostFinish.collect_free

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPostFinish.prepare_free' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPostFinish.prepare_free

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPostFinish.owner_grouped' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPostFinish.owner_grouped

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPostFinish.markedPrep_known' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPostFinish.markedPrep_known

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPostFinish.markedPrep_bounds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPostFinish.markedPrep_bounds

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPostFinish.known_calls' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPostFinish.known_calls

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPostFinish.onPool_map' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPostFinish.onPool_map

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPostFinish.known_fullCalls' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPostFinish.known_fullCalls

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPostFinish.nativeCtx_pure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPostFinish.nativeCtx_pure

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPostFinish.nativeCtx_bind' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPostFinish.nativeCtx_bind

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPostFinish.simulate_nativeCtx' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPostFinish.simulate_nativeCtx

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPostFinish.tail_known' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPostFinish.tail_known

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPostFinish.middle_finish' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPostFinish.middle_finish

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPostFinish.stackRun_pure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPostFinish.stackRun_pure

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPostFinish.stackRun_bind' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPostFinish.stackRun_bind

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPostFinish.skel_groupedPool' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPostFinish.skel_groupedPool

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPostFinish.lowerEC_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPostFinish.lowerEC_run

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPostFinish.stack_prep' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPostFinish.stack_prep

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPostFinish.splitT_ctx' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPostFinish.splitT_ctx

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPostFinish.splitT_group_known' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPostFinish.splitT_group_known

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPostFinish.stack_known' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPostFinish.stack_known

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPostFinish.owner_stack' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPostFinish.owner_stack

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPostFinish.sourceMid_finish' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPostFinish.sourceMid_finish

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPostFinish.upperLayer_finish' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPostFinish.upperLayer_finish

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPostFinish.upperLayer_finish_none' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPostFinish.upperLayer_finish_none

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPostFinish.step_finish' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPostFinish.step_finish
