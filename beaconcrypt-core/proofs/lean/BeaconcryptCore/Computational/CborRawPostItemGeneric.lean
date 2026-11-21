-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhDeploymentIdealPostItemRun

/-! The existing slot skeleton and native middle handoff are independent of the compiled result type. These additive wrappers retain the complete raw-CBOR compiler memory rather than restricting a continuation to the legacy compiler's local state. All service layers, accept execution and table invariants are the existing concrete interpreters. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.CborRawPostItemGeneric
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhKemIndCca (MlKem768PublicKey MlKem768Ciphertext MlKemSharedSecret)
open PqxdhDeploymentIdealParams (Target Params)
open PqxdhRegistrationJointKemRawOpaque (OpaqueContext)
open PqxdhRegistrationJointKemPostSkeleton (Enc TSpec SkelSpec SkelState fwd fwdOption evalLayer skelDecide skelResume clean)
open PqxdhRegistrationJointKemEntryFactor (Output publicLocalV factoredServices)
open PqxdhDeploymentIdealPostSim (SlotState ServiceState tableLayer serviceLayer eraseService optionLower_run serviceLayer_neverRead)
open PqxdhDeploymentIdealPostItem (cleanUpper cleanSkel upperLayer_neverRead)
open PqxdhDeploymentIdealPostSource (Mid sourceMid)
open PqxdhDeploymentIdealPostHidden (lowerEC eraseServiceC encodeMidC)
open PqxdhDeploymentIdealPostAccept (marksOf Stored)
open PqxdhDeploymentIdealPostItemRun (afterSelected bind_clean acceptAfter_keeps itemInv_after)
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}

noncomputable def itemPost (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    {count : Nat} (t : Target count) (p : Params KemSK count) {A R : Type}
    (decision : R → Bool) (context : OpaqueContext Reader KemSK A R count) : ProbComp Bool :=
  (simulateQ (PqxdhRegistrationJointKemSecondEntry.slotImpl (D := PqxdhCorrelatedExtractFamily.Message)
      (PqxdhRegistrationJointKemSecondEntry.tableService (n := 2)))
    ((simulateQ (publicLocalV Output) (PqxdhRegistrationJointKemPostSkeleton.postSkel setup codec checks decision count
      t.kem (factoredServices setup codec checks) p.chosen p.challenge context)).run'
        (PqxdhRegistrationJointKemPostSkeleton.cacheOf context))).run'
    (PqxdhRegistrationJointKemSecondEntry.emptyAlloc, PqxdhRecordLiftLazyTable.initial)

theorem itemPost_active {A R : Type} {count : ℕ} (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (t : Target count) (p : Params KemSK count)
    (decision : R → Bool) (created : PqxdhRegistrationJointServerBirth.ClientCreated Unit)
    (others : Fin count → MlKem768PublicKey × KemSK) (raw : Pqxdh.Bytes)
    (value : PqxdhServerRootPreparation.Verified Reader) (matched : value.keys.pqKey = p.chosen.1)
    (ephemeral : PqxdhServerRootPreparation.Ephemeral PqxdhJointGapDh.ScalarBytes) (consumed : List Pqxdh.Bytes)
    (native : PqxdhServerAuthNative.NativeState KemSK)
    (owners : (List PqxdhRegistrationJointGeneratedFinish.EncodedEntry × (ℕ → Option PqxdhEd25519EufCma.Phase1Candidate)))
    (next : Option ℕ → OracleComp (PqxdhRegistrationJointKemCommands.SourceSpec KemSK) (R))
    (state : PqxdhDynamicKemJointSource.State KemSK) (after : A) :
    itemPost setup codec checks t p decision
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
  unfold itemPost
  simp only [PqxdhRegistrationJointKemPostSkeleton.postSkel, matched, ↓reduceIte,
    PqxdhRegistrationJointKemPostSkeleton.cacheOf]
  rw [table, simulateQ_map, StateT.run'_eq, StateT.run_map, ← QueryImpl.simulateQ_compose,
    ← QueryImpl.simulateQ_compose (fwdOption (T := TSpec Output) _), optionLower_run]
  simp only [Functor.map_map]
  rfl


theorem itemPost_erased {A R : Type} {count : ℕ} (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (t : Target count) (p : Params KemSK count)
    (decision : R → Bool) (created : PqxdhRegistrationJointServerBirth.ClientCreated Unit)
    (others : Fin count → MlKem768PublicKey × KemSK) (raw : Pqxdh.Bytes)
    (value : PqxdhServerRootPreparation.Verified Reader) (matched : value.keys.pqKey = p.chosen.1)
    (ephemeral : PqxdhServerRootPreparation.Ephemeral PqxdhJointGapDh.ScalarBytes) (consumed : List Pqxdh.Bytes)
    (native : PqxdhServerAuthNative.NativeState KemSK)
    (owners : (List PqxdhRegistrationJointGeneratedFinish.EncodedEntry × (ℕ → Option PqxdhEd25519EufCma.Phase1Candidate)))
    (next : Option ℕ → OracleComp (PqxdhRegistrationJointKemCommands.SourceSpec KemSK) (R))
    (state : PqxdhDynamicKemJointSource.State KemSK) (after : A) :
    itemPost setup codec checks t p decision
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


theorem itemPost_clean {A R : Type} {count : ℕ} (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (t : Target count) (p : Params KemSK count)
    (decision : R → Bool) (created : PqxdhRegistrationJointServerBirth.ClientCreated Unit)
    (others : Fin count → MlKem768PublicKey × KemSK) (raw : Pqxdh.Bytes)
    (value : PqxdhServerRootPreparation.Verified Reader) (matched : value.keys.pqKey = p.chosen.1)
    (ephemeral : PqxdhServerRootPreparation.Ephemeral PqxdhJointGapDh.ScalarBytes) (consumed : List Pqxdh.Bytes)
    (native : PqxdhServerAuthNative.NativeState KemSK)
    (owners : (List PqxdhRegistrationJointGeneratedFinish.EncodedEntry × (ℕ → Option PqxdhEd25519EufCma.Phase1Candidate)))
    (next : Option ℕ → OracleComp (PqxdhRegistrationJointKemCommands.SourceSpec KemSK) (R))
    (state : PqxdhDynamicKemJointSource.State KemSK) (after : A) :
    itemPost setup codec checks t p decision
        (.ready created others (some (.pending raw value ephemeral consumed native owners next)) state after) =
      PqxdhRegistrationJointKemPostSkeleton.skelDecide <$>
        ((simulateQ (PqxdhRegistrationJointKemObserverFree.eraseOptionImpl PqxdhDeploymentIdealPostSim.eraseService
          (serviceLayer setup t.kem p.chosen others p.challenge))
          ((simulateQ (PqxdhRegistrationJointKemPostSkeleton.resumeImpl setup.hmac native.2.sessions
              (factoredServices setup codec checks))
            (PqxdhRegistrationJointKemOpaqueResume.resume setup codec checks created.server.server.metadata.identityIndex
              created.publicIdentity raw value ephemeral (PqxdhAcceptedRegistration.ciphertextArray p.challenge)
              .challenge native.2 consumed)).run (native.2, none) >>= fun answer =>
            (fun result => ((result.1, result.2.1), result.2.2)) <$>
              (simulateQ (PqxdhRegistrationJointKemObserverFree.eraseImpl cleanUpper
                (PqxdhDeploymentIdealPostSim.upperLayer setup codec checks created.server.server.metadata.identityIndex
                  created.publicIdentity t.kem.val p.challenge (factoredServices setup codec checks)))
                (PqxdhRegistrationJointAcceptKemCut.tagged (PqxdhRegistrationJointAcceptCutTag.decideTag decision) raw
                  next answer.1)).run (owners, cleanSkel answer.2))).run).run
          (PqxdhRegistrationJointKemObserverFree.eraseJoint state,
            (native.1.cache, (PqxdhRegistrationJointKemSecondEntry.emptyAlloc, PqxdhRecordLiftLazyTable.initial))) := by
  rw [itemPost_erased setup codec checks t p decision created others raw value matched
    ephemeral consumed native owners next state after, PqxdhDeploymentIdealPostSim.skelResume_upper]
  have inner : ∀ answer : Option ℕ × SkelState KemSK Output,
      (fun result => ((result.1, result.2.1), result.2.2)) <$>
        (simulateQ (PqxdhRegistrationJointKemObserverFree.eraseImpl cleanUpper
          (PqxdhDeploymentIdealPostSim.upperLayer setup codec checks created.server.server.metadata.identityIndex
            created.publicIdentity t.kem.val p.challenge (factoredServices setup codec checks)))
          (PqxdhRegistrationJointAcceptKemCut.tagged (PqxdhRegistrationJointAcceptCutTag.decideTag decision) raw
            next answer.1)).run (owners, cleanSkel answer.2) =
      (fun result : (Bool × (List PqxdhRegistrationJointGeneratedFinish.EncodedEntry × (ℕ → Option PqxdhEd25519EufCma.Phase1Candidate))) × SkelState KemSK Output =>
          (result.1, cleanSkel result.2)) <$>
        ((fun result => ((result.1, result.2.1), result.2.2)) <$>
          (simulateQ (PqxdhDeploymentIdealPostSim.upperLayer setup codec checks created.server.server.metadata.identityIndex
            created.publicIdentity t.kem.val p.challenge (factoredServices setup codec checks))
            (PqxdhRegistrationJointAcceptKemCut.tagged (PqxdhRegistrationJointAcceptCutTag.decideTag decision) raw
              next answer.1)).run (owners, answer.2)) := by
    intro answer
    have erased := PqxdhRegistrationJointKemObserverFree.run_erase cleanUpper (fun _ => rfl)
      (PqxdhDeploymentIdealPostSim.upperLayer setup codec checks created.server.server.metadata.identityIndex
        created.publicIdentity t.kem.val p.challenge (factoredServices setup codec checks))
      (upperLayer_neverRead setup codec checks _ _ _ _ _)
      (PqxdhRegistrationJointAcceptKemCut.tagged (PqxdhRegistrationJointAcceptCutTag.decideTag decision) raw next
        answer.1) (owners, answer.2)
    change _ = _ <$> (_ <$> _)
    rw [show (owners, cleanSkel answer.2) = cleanUpper (owners, answer.2) from rfl, ← erased]
    simp only [Functor.map_map]
    rfl
  simp only [inner, simulateQ_bind, OptionT.run_bind, Option.elimM, StateT.run_bind, map_bind]
  refine bind_congr fun reached => ?_
  rcases reached with ⟨_ | answer, after⟩
  · rfl
  · simp only [Option.elim, simulateQ_map, OptionT.run_map, StateT.run_map, Functor.map_map]
    refine congrArg (fun f => f <$> _) (funext fun reached => ?_)
    rcases reached with ⟨_ | result, after⟩ <;> rfl


section Middle
variable (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (checks : Checks) {count : Nat}
    (t : Target count) (p : Params KemSK count)

theorem itemPost_middle {A R : Type} (decision : R → Bool)
    (created : PqxdhLiveServerConstruction.Created Unit)
    (identity : created.publicIdentity = setup.joint.publicKeys created.seed) (raw : Pqxdh.Bytes)
    (value : PqxdhServerRootPreparation.Verified Reader) (matched : value.keys.pqKey = p.chosen.1)
    (ephemeral : PqxdhServerRootPreparation.Ephemeral PqxdhJointGapDh.ScalarBytes) (consumed : List Pqxdh.Bytes)
    (logged : Option PqxdhJointGapDh.ScalarBytes) (joint : PqxdhRegistrationJointSchedule.State KemSK)
    (owned : PqxdhDeploymentIdealPoolSource.PoolOwned created.seed created.server.server.metadata.identityIndex joint)
    (prefixed : PqxdhDeploymentIdealPoolSource.PoolPrefix (p.pool t) joint.pool.2)
    (indexed : PqxdhDeploymentIdealCut.PoolIndexed joint)
    (next : Option ℕ → OracleComp (PqxdhRegistrationJointKemCommands.SourceSpec KemSK) (R))
    (onlyAllowed : ∀ answer, (next answer).IsQueryBoundP
      (fun query => ¬ PqxdhDeploymentIdealPostInvariant.Allowed (KemSK := KemSK) query) 0)
    (budget : ℕ) (bounded : ∀ answer, (next answer).IsQueryBoundP
      (PqxdhDeploymentIdealPostInvariant.Costly (KemSK := KemSK)) budget)
    (fits : budget ≤ (p.pool t).length - joint.pool.2.keys.length) (after : A) :
    itemPost setup codec checks t p decision
        (.ready (PqxdhRegistrationJointServerBirth.encode created) p.others
          (some (.pending raw value ephemeral consumed joint.shared
            ((PqxdhRegistrationJointGeneratedFinish.encodeState setup joint).owners, joint.inits) next))
          (joint.pool.1, PqxdhDeploymentIdealPoolSource.routerOf joint.pool.2) after) =
      (simulateQ (PqxdhRegistrationJointKemSecondEntry.slotImpl PqxdhDeploymentSeedSplit.tableService)
          ((PqxdhDeploymentIdealActive.acceptAfter setup codec checks created.seed p.challenge value ephemeral consumed
            logged).run joint.shared)).run
          (PqxdhRegistrationJointKemSecondEntry.emptyAlloc, PqxdhRecordLiftLazyTable.initial) >>= fun w =>
        (fun result => result.1) <$> (simulateQ (sourceMid setup codec route checks t p created)
          (PqxdhRegistrationJointAcceptKemCut.tagged (PqxdhRegistrationJointAcceptCutTag.decideTag decision) raw next
            w.1.1.1.1)).run (afterSelected t joint w) := by
  rw [itemPost_clean setup codec checks t p decision _ p.others raw value matched ephemeral
    consumed joint.shared _ next _ after]
  have counts : (PqxdhRegistrationJointKemObserverFree.eraseJoint (joint.pool.1,
      PqxdhDeploymentIdealPoolSource.routerOf joint.pool.2), (joint.shared.1.cache,
        (PqxdhRegistrationJointKemSecondEntry.emptyAlloc, PqxdhRecordLiftLazyTable.initial))) =
      PqxdhDeploymentIdealPostSim.eraseService ((joint.pool.1, PqxdhDeploymentIdealPoolSource.routerOf joint.pool.2),
        (joint.shared.1.cache, ((PqxdhRegistrationJointKemSecondEntry.emptyAlloc : PqxdhRegistrationJointKemSecondEntry.Alloc
          PqxdhCorrelatedExtractFamily.Message 2), (PqxdhRecordLiftLazyTable.initial : PqxdhDeploymentIdealSteps.TableState)))) :=
    rfl
  rw [counts]
  have toC : ∀ work : OracleComp (PqxdhRegistrationJointKemPostSkeleton.Enc KemSK +
      PqxdhRegistrationJointKemPostSkeleton.TSpec Output) ((Bool × (List PqxdhRegistrationJointGeneratedFinish.EncodedEntry ×
        (ℕ → Option PqxdhEd25519EufCma.Phase1Candidate))) × PqxdhRegistrationJointKemPostSkeleton.SkelState KemSK Output),
      PqxdhRegistrationJointKemPostSkeleton.skelDecide <$> ((simulateQ (PqxdhDeploymentIdealPostSteps.lowerE setup t p)
        work).run).run (PqxdhDeploymentIdealPostSim.eraseService ((joint.pool.1,
          PqxdhDeploymentIdealPoolSource.routerOf joint.pool.2), (joint.shared.1.cache,
            ((PqxdhRegistrationJointKemSecondEntry.emptyAlloc : PqxdhRegistrationJointKemSecondEntry.Alloc
              PqxdhCorrelatedExtractFamily.Message 2), (PqxdhRecordLiftLazyTable.initial : PqxdhDeploymentIdealSteps.TableState))))) =
      PqxdhRegistrationJointKemPostSkeleton.skelDecide <$> ((simulateQ (lowerEC setup t p) work).run).run
        (eraseServiceC ((joint.pool.1, PqxdhDeploymentIdealPoolSource.routerOf joint.pool.2), (joint.shared.1.cache,
          ((PqxdhRegistrationJointKemSecondEntry.emptyAlloc : PqxdhRegistrationJointKemSecondEntry.Alloc
            PqxdhCorrelatedExtractFamily.Message 2), (PqxdhRecordLiftLazyTable.initial : PqxdhDeploymentIdealSteps.TableState))))) := by
    intro work
    rw [PqxdhDeploymentIdealPostFinish.lowerEC_run, Functor.map_map]
    rfl
  rw [toC]
  refine Eq.trans (congrArg (fun work => PqxdhRegistrationJointKemPostSkeleton.skelDecide <$>
    ((simulateQ (lowerEC setup t p) work).run).run (eraseServiceC ((joint.pool.1,
      PqxdhDeploymentIdealPoolSource.routerOf joint.pool.2), (joint.shared.1.cache,
        ((PqxdhRegistrationJointKemSecondEntry.emptyAlloc : PqxdhRegistrationJointKemSecondEntry.Alloc
          PqxdhCorrelatedExtractFamily.Message 2), (PqxdhRecordLiftLazyTable.initial : PqxdhDeploymentIdealSteps.TableState))))))
    (bind_clean _ _ (PqxdhDeploymentIdealPostAccept.resume_clean setup codec checks (factoredServices setup codec checks)
      (PqxdhRegistrationJointServerBirth.encode created).server.server.metadata.identityIndex
      (PqxdhRegistrationJointServerBirth.encode created).publicIdentity raw value ephemeral
      (PqxdhAcceptedRegistration.ciphertextArray p.challenge) joint.shared.2 consumed none)
      (fun answer skel => (fun result => ((result.1, result.2.1), result.2.2)) <$>
        (simulateQ (PqxdhDeploymentIdealPostSteps.upperE setup codec checks t p created)
          (PqxdhRegistrationJointAcceptKemCut.tagged (PqxdhRegistrationJointAcceptCutTag.decideTag decision) raw next
            answer)).run (((PqxdhRegistrationJointGeneratedFinish.encodeState setup joint).owners, joint.inits),
              skel)))) ?_
  rw [show (PqxdhRegistrationJointServerBirth.encode created).publicIdentity = setup.joint.publicKeys created.seed
      from identity, simulateQ_bind, OptionT.run_bind, Option.elimM, StateT.run_bind,
    PqxdhDeploymentIdealPostAccept.resume_accept setup codec checks t p created.seed
      (PqxdhRegistrationJointServerBirth.encode created).server.server.metadata.identityIndex raw value ephemeral consumed
      logged joint.shared joint.pool.1 joint.pool.2 prefixed owned.1.2 _
      PqxdhRegistrationJointKemSecondEntry.slotGood_empty (by decide),
    bind_map_left, map_bind]
  refine bind_congr_of_forall_mem_support _ fun w member => ?_
  have produced : w.1 ∈ support ((PqxdhDeploymentIdealActive.acceptAfter setup codec checks created.seed p.challenge value
      ephemeral consumed logged).run joint.shared) := by
    apply OracleComp.support_simulateQ_run'_subset
      (PqxdhRegistrationJointKemSecondEntry.slotImpl PqxdhDeploymentSeedSplit.tableService) _
      (PqxdhRegistrationJointKemSecondEntry.emptyAlloc, PqxdhRecordLiftLazyTable.initial)
    rw [StateT.run'_eq, support_map]
    exact ⟨w, member, rfl⟩
  have active := (PqxdhDeploymentIdealPostMark.acceptAfter_mark setup codec checks created.seed p.challenge value ephemeral
    consumed logged joint.shared w.1 produced).1
  obtain ⟨good, stored⟩ := acceptAfter_keeps setup codec checks p created.seed value ephemeral consumed logged joint.shared
    _ PqxdhRegistrationJointKemSecondEntry.slotGood_empty (by decide) w member
  have holds := itemInv_after t p created joint owned prefixed indexed w active good stored
  have encodeAfter : encodeMidC setup (afterSelected t joint w) =
      ((((PqxdhRegistrationJointGeneratedFinish.encodeState setup joint).owners, joint.inits),
          (clean w.1.2.2, marksOf w.1.1.2.2 w.2)),
        eraseServiceC ((joint.pool.1, PqxdhDeploymentIdealPoolSource.routerOf joint.pool.2), (w.1.2.1.cache, w.2))) := by
    simp only [encodeMidC, PqxdhDeploymentIdealPostSteps.encodeMid, eraseServiceC, Prod.map,
      PqxdhRegistrationJointKemObserverFree.eraseJoint_idem]
    rfl
  have sim := PqxdhDeploymentIdealPostInvariant.item_sim setup codec route checks t p created identity
    (PqxdhRegistrationJointAcceptKemCut.tagged (PqxdhRegistrationJointAcceptCutTag.decideTag decision) raw next w.1.1.1.1)
    (by unfold PqxdhRegistrationJointAcceptKemCut.tagged; exact (OracleComp.isQueryBoundP_map_iff _ _ _).mpr (onlyAllowed _)) budget
    (by unfold PqxdhRegistrationJointAcceptKemCut.tagged; exact (OracleComp.isQueryBoundP_map_iff _ _ _).mpr (bounded _))
    (afterSelected t joint w) fits holds
  rw [encodeAfter] at sim
  simp only [Option.elim_some, simulateQ_map, OptionT.run_map, StateT.run_map]
  rw [show cleanSkel (clean w.1.2.2, marksOf w.1.1.2.2 w.2) = (clean w.1.2.2, marksOf w.1.1.2.2 w.2) from rfl, sim,
    Functor.map_map, Functor.map_map]
  rfl

end Middle

end BeaconcryptCore.Computational.CborRawPostItemGeneric

/-- info: 'BeaconcryptCore.Computational.CborRawPostItemGeneric.itemPost_active' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawPostItemGeneric.itemPost_active

/-- info: 'BeaconcryptCore.Computational.CborRawPostItemGeneric.itemPost_erased' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawPostItemGeneric.itemPost_erased

/-- info: 'BeaconcryptCore.Computational.CborRawPostItemGeneric.itemPost_clean' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawPostItemGeneric.itemPost_clean

/-- info: 'BeaconcryptCore.Computational.CborRawPostItemGeneric.itemPost_middle' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawPostItemGeneric.itemPost_middle
