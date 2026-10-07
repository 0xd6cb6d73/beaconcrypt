-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRegistrationJointKemRawCertified

/-! LQ-F spike: the raw-ordinal ML-KEM hop for an arbitrary scanned source program. `KemRawChallenge.preRaw`, `KemRawGame.adversary`, `branch` and `sourceReal` and the proof-carrying `KemRawCertified.adversary` fix the scanned program to the KEM scan of `AcceptKemCut.exposeAt` at occurrence zero, but their proofs (`preRaw_source`, `branchRaw_source`, `branchRaw_real_error`, `advantageRaw_error`, `prefix_erase`, `branch_erase`, `advantage`) never look inside that program: they use only the generic router equality `PqxdhDynamicKemJointRouter.pre_program`, the generic postphase equality `KemResume.post_source` and the ordinary one-key IND-CCA branch lemmas. This module states the same games and the same bound for every family `scanned : ClientCreated Unit → OracleComp (PqxdhLiveKemBirth.Spec KemSK) (KemCut.Cut KemSK (Outcome KemSK Bool))` of scanned programs over the actual initialized Server, and shows that the existing raw-ordinal definitions are the instance `scanned := KemRawChallenge.rawScan setup codec checks decision work index` (`preRaw_eq`, `sourcePreRaw_eq`, `sourceReal_eq`, `branch_eq`, `adversary_eq`, all by `rfl`). A later-quantum source whose exposure of the selected encapsulation is another program over the same interface (for example a source that also logs the Server's ephemeral scalars) therefore receives the KEM hop, with one ordinary one-key ML-KEM IND-CCA advantage and one ordinary ML-KEM correctness error, without a new proof. The query bills of the constructed adversary (`KemRawBills.adversary_bound`) are not generic: they depend on the caps of the scanned program and must be re-proved for every new exposure. No assumption, contract or premise is added; `FunctionalDecapsulation` is the one inherited contract, used exactly where `KemRawGame` uses it. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhDeploymentLaterServerKemHop
open PqxdhKemIndCca PqxdhPrivateKemSource PqxdhJointIdentity PqxdhInitializerSecrecy
open PqxdhRegistrationJointKemCommands (SourceSpec Outcome)
open PqxdhRegistrationJointKemChallenge (Context)
open PqxdhRegistrationJointKemResume (post sourcePost)
open PqxdhRegistrationJointServerBirth (ClientCreated)
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response A X : Type}

/-- A family of scanned source programs over the actual initialized Server: for each constructed Server, a program over the joint identity, coin and KEM pool interface whose result is a KEM cut of a Boolean source outcome. -/
abbrev Scanned (KemSK : Type) :=
  ClientCreated Unit → OracleComp (PqxdhLiveKemBirth.Spec KemSK)
    (PqxdhRegistrationJointKemCut.Cut KemSK (Outcome KemSK Bool))

/-- The executable prephase for an arbitrary scanned program: actual initialization, all local reservations and the scanned program under the selected-first prechallenge router. Every constructor branch is handled exactly as in `KemChallenge.pre` and `KemRawChallenge.preRaw`. -/
noncomputable def pre (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes) (scanned : Scanned KemSK)
    (runtime : A) (count : Nat) (selected : Fin (count + 1)) (target : MlKem768PublicKey) :
    OracleComp (MlKemCCAOracleSpec baseSpec) (Context KemSK A Bool count) := do
  let born ← ccaCoins ((simulateQ (PqxdhRegistrationJointServerBirth.impl setup ensureInit)
    (PqxdhRegistrationJointServerBirth.client setup.serverKeyId supplied)).run
      ((PqxdhDynamicIdentityPool.initialState, PqxdhLiveKemBirth.empty), runtime))
  match born.1 with
  | none => pure (.failed born.2)
  | some created => do
    let others ← ccaCoins (PqxdhLiveKemSelection.sampleFamily
      (simulateQ (PqxdhInitializerSecrecy.kemAmbientImpl setup.baseImpl) setup.kem.keygen) count)
    let result ← (((simulateQ (PqxdhDynamicKemJointRouter.pre setup.joint setup.kem selected.val
      (PqxdhDynamicKemRouter.selectedReservation selected target others))
      (scanned created)).run).run
        (born.2.1.1, PqxdhDynamicKemRouter.empty))
    pure (.ready created others result.1 result.2 born.2.2)

/-- The stopped-source interpretation of the same initializer and scanned program. Only this source interpreter receives the chosen key pair. -/
noncomputable def sourcePre (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes) (scanned : Scanned KemSK)
    (runtime : A) (count : Nat) (selected : Fin (count + 1)) (chosen : MlKem768PublicKey × KemSK) :
    ProbComp (Context KemSK A Bool count) := do
  let born ← (simulateQ (PqxdhRegistrationJointServerBirth.impl setup ensureInit)
    (PqxdhRegistrationJointServerBirth.client setup.serverKeyId supplied)).run
      ((PqxdhDynamicIdentityPool.initialState, PqxdhLiveKemBirth.empty), runtime)
  match born.1 with
  | none => pure (.failed born.2)
  | some created => do
    let others ← PqxdhLiveKemSelection.sampleFamily
      (simulateQ (PqxdhInitializerSecrecy.kemAmbientImpl setup.baseImpl) setup.kem.keygen) count
    let result ← (((simulateQ (PqxdhDynamicKemJointRouter.stopped setup.baseImpl setup.joint setup.kem selected.val
      (List.ofFn (selected.insertNth chosen others)))
      (scanned created)).run).run
        (born.2.1.1, PqxdhDynamicKemRouter.empty))
    pure (.ready created others result.1 result.2 born.2.2)

/-- The executable prephase under the ordinary prechallenge interpretation equals the stopped-source prephase, for every scanned program. The proof is that of `KemRawChallenge.preRaw_source`, which does not depend on the scanned program. -/
theorem pre_source (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes) (scanned : Scanned KemSK)
    (runtime : A) (count : Nat) (selected : Fin (count + 1)) (chosen : MlKem768PublicKey × KemSK) :
    evalKem setup.baseImpl setup.kem chosen.2
      (pre setup ensureInit supplied scanned runtime count selected chosen.1) =
      sourcePre setup ensureInit supplied scanned runtime count selected chosen := by
  simp only [pre, sourcePre, evalKem, simulateQ_bind]
  rw [show simulateQ (PqxdhInitializerSecrecy.kemAmbientImpl setup.baseImpl)
    (simulateQ (PqxdhStatefulPhase1EufCma.localKemPreChallengeImpl setup.kem chosen.2)
      (ccaCoins ((simulateQ (PqxdhRegistrationJointServerBirth.impl setup ensureInit)
        (PqxdhRegistrationJointServerBirth.client setup.serverKeyId supplied)).run
          ((PqxdhDynamicIdentityPool.initialState, PqxdhLiveKemBirth.empty), runtime)))) = _ from
    evalKem_coins setup.baseImpl setup.kem chosen.2 _]
  apply bind_congr
  rintro ⟨(_ | created), after⟩
  · rfl
  · simp only [simulateQ_bind]
    rw [show simulateQ (PqxdhInitializerSecrecy.kemAmbientImpl setup.baseImpl)
      (simulateQ (PqxdhStatefulPhase1EufCma.localKemPreChallengeImpl setup.kem chosen.2)
        (ccaCoins (PqxdhLiveKemSelection.sampleFamily
          (simulateQ (PqxdhInitializerSecrecy.kemAmbientImpl setup.baseImpl) setup.kem.keygen) count))) = _ from
      evalKem_coins setup.baseImpl setup.kem chosen.2 _]
    apply bind_congr
    intro others
    have same := PqxdhDynamicKemJointRouter.pre_program setup.baseImpl setup.joint setup.kem selected.val
      (List.ofFn (selected.insertNth chosen others)) chosen.1 chosen.2
      (by simpa only [List.nil_append, List.length_nil, Nat.zero_add, Prod.mk.eta] using
        PqxdhLiveKemSelection.selected_index [] selected chosen others)
      (scanned created)
      (after.1.1, PqxdhDynamicKemRouter.empty)
    rw [PqxdhDynamicKemRouter.selected_reservation] at same
    simpa only [evalKem, simulateQ_pure, bind_pure_comp] using congrArg
      (fun work => (fun result => Context.ready created others result.1 result.2 after.2) <$> work) same

/-- The ordinary one-key adversary for a scanned program: it receives only the public challenge key and a candidate reply, runs the prephase and resumes the saved callback. -/
noncomputable def adversary (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes) (scanned : Scanned KemSK)
    (runtime : A) (count : Nat) (selected : Fin (count + 1)) : OneKeyAdversary setup.kem where
  Context := Context KemSK A Bool count
  preChallenge := pre setup ensureInit supplied scanned runtime count selected
  postChallenge transcript candidate :=
    PqxdhRegistrationJointKemGame.decision <$> post setup count selected transcript candidate

/-- The explicit fixed branch for a scanned program: the challenger's key pair, the stopped-source prephase, the challenger's encapsulation and the branch-independent uniform draw. -/
noncomputable def branch (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes) (scanned : Scanned KemSK)
    (runtime : A) (count : Nat) (selected : Fin (count + 1)) (real : Bool) : ProbComp Bool := do
  let chosen ← simulateQ (kemAmbientImpl setup.baseImpl) setup.kem.keygen
  let context ← sourcePre setup ensureInit supplied scanned runtime count selected chosen
  let encapsulated ← simulateQ (kemAmbientImpl setup.baseImpl) (setup.kem.encaps chosen.1)
  let uniform ← $ᵗ MlKemSharedSecret
  PqxdhRegistrationJointKemGame.decision <$> PqxdhDynamicKemPost.evaluate setup.baseImpl setup.kem chosen.2
    encapsulated.1 (post setup count selected ⟨chosen.1, encapsulated.1, context⟩
      (if real then encapsulated.2 else uniform))

/-- The real game for a scanned program: the literal source callback resumed through the stopped source interpreter, with the harmless challenger ghost draw. -/
noncomputable def sourceReal (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes) (scanned : Scanned KemSK)
    (runtime : A) (count : Nat) (selected : Fin (count + 1)) : ProbComp Bool := do
  let chosen ← simulateQ (kemAmbientImpl setup.baseImpl) setup.kem.keygen
  let context ← sourcePre setup ensureInit supplied scanned runtime count selected chosen
  let encapsulated ← simulateQ (kemAmbientImpl setup.baseImpl) (setup.kem.encaps chosen.1)
  let _ ← $ᵗ MlKemSharedSecret
  PqxdhRegistrationJointKemGame.decision <$> sourcePost setup count selected chosen
    ⟨chosen.1, encapsulated.1, context⟩ encapsulated.2

set_option backward.isDefEq.respectTransparency false in
/-- The fixed branch of the constructed ordinary adversary equals the explicit branch, for every scanned program. -/
theorem branch_source (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes) (scanned : Scanned KemSK)
    (runtime : A) (count : Nat) (selected : Fin (count + 1)) (real : Bool) :
    simulateQ (kemAmbientImpl setup.baseImpl)
      (oneKeyBranchMain setup.kem (runtimeOfImpl (kemAmbientImpl setup.baseImpl))
        (adversary setup ensureInit supplied scanned runtime count selected) real) =
      branch setup ensureInit supplied scanned runtime count selected real := by
  simp only [oneKeyBranchMain, oneKeyPrefix, oneKeyFinish, adversary, branch,
    simulateQ_bind, bind_assoc, pure_bind, runtimeOfImpl_liftProbComp,
    simulateQ_kemAmbient_liftProbComp, simulateQ_map]
  apply bind_congr
  intro chosen
  have same := pre_source setup ensureInit supplied scanned runtime count selected chosen
  change simulateQ (kemAmbientImpl setup.baseImpl)
    (simulateQ (setup.kem.IND_CCA_preChallengeImpl chosen.2)
      (pre setup ensureInit supplied scanned runtime count selected chosen.1)) = _ at same
  rw [same]
  rfl

/-- The real branch and the real stopped-source game differ by at most the ordinary ML-KEM correctness error, for every scanned program. The proof is that of `KemRawGame.branchRaw_real_error`. -/
theorem real_error (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes) (scanned : Scanned KemSK)
    (runtime : A) (count : Nat) (selected : Fin (count + 1)) :
    tvDist (branch setup ensureInit supplied scanned runtime count selected true)
      (sourceReal setup ensureInit supplied scanned runtime count selected) ≤
      PqxdhRegistrationJointKemRawGame.correctnessError setup := by
  have point : ∀ (chosen : MlKem768PublicKey × KemSK) (context : Context KemSK A Bool count)
      (pair : MlKem768Ciphertext × MlKemSharedSecret),
      tvDist (do
          let uniform ← $ᵗ MlKemSharedSecret
          PqxdhRegistrationJointKemGame.decision <$> PqxdhDynamicKemPost.evaluate setup.baseImpl setup.kem chosen.2
            pair.1 (post setup count selected ⟨chosen.1, pair.1, context⟩ (if true then pair.2 else uniform)))
        (do
          let _ ← $ᵗ MlKemSharedSecret
          PqxdhRegistrationJointKemGame.decision <$> sourcePost setup count selected chosen
            ⟨chosen.1, pair.1, context⟩ pair.2) ≤
      (𝒟[simulateQ (kemAmbientImpl setup.baseImpl) (do
          let recovered ← setup.kem.decaps chosen.2 pair.1
          pure (decide (recovered ≠ some pair.2)))] {true}).toReal := by
    intro chosen context pair
    by_cases good : functional.result chosen.2 pair.1 = some pair.2
    · have agreement : setup.kem.decaps chosen.2 pair.1 = pure (some pair.2) :=
        (functional.exact chosen.2 pair.1).trans (congrArg pure good)
      have same := PqxdhRegistrationJointKemResume.post_source setup count selected chosen context pair.1 pair.2
        agreement
      simp only [↓reduceIte, same, tvDist_self]
      exact ENNReal.toReal_nonneg
    · have bad : (𝒟[simulateQ (kemAmbientImpl setup.baseImpl) (do
          let recovered ← setup.kem.decaps chosen.2 pair.1
          pure (decide (recovered ≠ some pair.2)))] {true}).toReal = 1 := by
        rw [evalDist_apply_singleton]
        simp [functional.exact, good]
      rw [bad]
      exact tvDist_le_one _ _
  unfold branch sourceReal
  refine le_trans (PqxdhHiddenRoot.tvDist_bind_left_le_probEvent_bind _ _ _
    (fun pair => simulateQ (kemAmbientImpl setup.baseImpl)
      (PqxdhKemCorrectnessStopped.keyError setup.kem pair.1 pair.2))
    (fun result => result = true) ?_) (le_of_eq ?_)
  · intro chosen
    refine le_trans (PqxdhHiddenRoot.tvDist_bind_left_le_probEvent_bind _ _ _
      (fun _ => simulateQ (kemAmbientImpl setup.baseImpl)
        (PqxdhKemCorrectnessStopped.keyError setup.kem chosen.1 chosen.2))
      (fun result => result = true) ?_) (le_of_eq ?_)
    · intro context
      refine le_trans (PqxdhHiddenRoot.tvDist_bind_left_le_probEvent_bind _ _ _
        (fun pair => simulateQ (kemAmbientImpl setup.baseImpl) (do
          let recovered ← setup.kem.decaps chosen.2 pair.1
          pure (decide (recovered ≠ some pair.2))))
        (fun result => result = true) ?_) (le_of_eq ?_)
      · intro pair
        rw [probEvent_eq_eq_probOutput, ← evalDist_apply_singleton]
        exact point chosen context pair
      · simp only [PqxdhKemCorrectnessStopped.keyError, simulateQ_bind]
    · simp only [probEvent_bind_const, probFailure_eq_zero, tsub_zero, one_mul]
  · rw [PqxdhRegistrationJointKemRawGame.correctnessError, evalDist_apply_singleton, ← probEvent_eq_eq_probOutput,
      PqxdhKemCorrectnessStopped.error_keygen, simulateQ_bind]

/-- The real game and its candidate replacement are within one ordinary one-key ML-KEM IND-CCA advantage plus one ordinary ML-KEM correctness error, both with coefficient one, for every scanned program. -/
theorem advantage_error (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes) (scanned : Scanned KemSK)
    (runtime : A) (count : Nat) (selected : Fin (count + 1)) :
    (sourceReal setup ensureInit supplied scanned runtime count selected).boolDistAdvantage
      (branch setup ensureInit supplied scanned runtime count selected false) ≤
      setup.kem.IND_CCA_Advantage (runtimeOfImpl (kemAmbientImpl setup.baseImpl))
        (adversary setup ensureInit supplied scanned runtime count selected).toINDCCA +
        PqxdhRegistrationJointKemRawGame.correctnessError setup := by
  have exactHop := oneKey_indCCAAdvantage_eq_branchDist setup.kem
    (runtimeOfImpl (kemAmbientImpl setup.baseImpl))
    (adversary setup ensureInit supplied scanned runtime count selected)
    (runtimeOfImpl_evalDist_pure (kemAmbientImpl setup.baseImpl))
    (runtimeOfImpl_evalDist_bind (kemAmbientImpl setup.baseImpl))
    (runtimeOfImpl_evalDist_liftProbComp setup.baseImpl)
    (runtimeOfImpl_noFail_bool (kemAmbientImpl setup.baseImpl))
  have hop : (branch setup ensureInit supplied scanned runtime count selected true).boolDistAdvantage
      (branch setup ensureInit supplied scanned runtime count selected false) =
      setup.kem.IND_CCA_Advantage (runtimeOfImpl (kemAmbientImpl setup.baseImpl))
        (adversary setup ensureInit supplied scanned runtime count selected).toINDCCA := by
    simpa only [oneKeyBranch, runtimeOfImpl_evalDist, branch_source, ProbComp.boolDistAdvantage,
      SPMF.boolDistAdvantage, MeasureTheory.Measure.boolDist, probOutput_def, evalDist_apply_singleton] using
      exactHop.symm
  have close : (sourceReal setup ensureInit supplied scanned runtime count selected).boolDistAdvantage
      (branch setup ensureInit supplied scanned runtime count selected true) ≤
      PqxdhRegistrationJointKemRawGame.correctnessError setup := by
    rw [ProbComp.boolDistAdvantage_comm]
    refine le_trans ?_ (real_error setup functional ensureInit supplied scanned runtime count selected)
    rw [ProbComp.boolDistAdvantage]
    simpa only [evalDist_apply_singleton] using abs_probOutput_toReal_sub_le_tvDist _ _
  have triangle := ProbComp.boolDistAdvantage_triangle
    (sourceReal setup ensureInit supplied scanned runtime count selected)
    (branch setup ensureInit supplied scanned runtime count selected true)
    (branch setup ensureInit supplied scanned runtime count selected false)
  rw [hop] at triangle
  linarith

/-- A saved context of the prephase of a scanned program, with an erased proof that it was produced by that executable prephase at the recorded public key. -/
abbrev Saved (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes) (scanned : Scanned KemSK)
    (runtime : A) (count : Nat) (selected : Fin (count + 1)) :=
  (target : MlKem768PublicKey) × {context : Context KemSK A Bool count //
    context ∈ support (pre setup ensureInit supplied scanned runtime count selected target)}

/-- The prephase with an erased support certificate of its own context. -/
noncomputable def annotatedPre (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes) (scanned : Scanned KemSK)
    (runtime : A) (count : Nat) (selected : Fin (count + 1)) (target : MlKem768PublicKey) :
    OracleComp (MlKemCCAOracleSpec baseSpec) (Saved setup ensureInit supplied scanned runtime count selected) :=
  (fun result => ⟨target, result⟩) <$> RawCtxSupportedSample.certify
    (pre setup ensureInit supplied scanned runtime count selected target)
    (fun context => context ∈ support (pre setup ensureInit supplied scanned runtime count selected target))
    (fun _ reached => reached)

/-- Proof erasure restores exactly the executable prephase. -/
theorem prefix_erase (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes) (scanned : Scanned KemSK)
    (runtime : A) (count : Nat) (selected : Fin (count + 1)) (target : MlKem768PublicKey) :
    (fun result => result.2.val) <$> annotatedPre setup ensureInit supplied scanned runtime count selected target =
      pre setup ensureInit supplied scanned runtime count selected target := by
  simpa only [annotatedPre, Functor.map_map] using RawCtxSupportedSample.erase
    (pre setup ensureInit supplied scanned runtime count selected target) _ _

/-- The proof-carrying adversary for a scanned program; its postphase ignores the certificate. -/
noncomputable def certified (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes) (scanned : Scanned KemSK)
    (runtime : A) (count : Nat) (selected : Fin (count + 1)) : OneKeyAdversary setup.kem where
  Context := Saved setup ensureInit supplied scanned runtime count selected
  preChallenge := annotatedPre setup ensureInit supplied scanned runtime count selected
  postChallenge transcript candidate := PqxdhRegistrationJointKemGame.decision <$>
    post setup count selected ⟨transcript.publicKey, transcript.ciphertext, transcript.context.2.val⟩ candidate

set_option backward.isDefEq.respectTransparency false in
/-- The proof-carrying adversary has exactly the fixed-branch program of the plain one. -/
theorem branch_erase (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes) (scanned : Scanned KemSK)
    (runtime : A) (count : Nat) (selected : Fin (count + 1)) (real : Bool) :
    oneKeyBranchMain setup.kem (runtimeOfImpl (kemAmbientImpl setup.baseImpl))
      (certified setup ensureInit supplied scanned runtime count selected) real =
    oneKeyBranchMain setup.kem (runtimeOfImpl (kemAmbientImpl setup.baseImpl))
      (adversary setup ensureInit supplied scanned runtime count selected) real := by
  simp only [oneKeyBranchMain, oneKeyPrefix, oneKeyFinish, certified, adversary, bind_assoc, pure_bind]
  apply bind_congr
  intro chosen
  have same := congrArg (simulateQ (setup.kem.IND_CCA_preChallengeImpl chosen.2))
    (prefix_erase setup ensureInit supplied scanned runtime count selected chosen.1)
  simp only [simulateQ_map] at same
  rw [← same, bind_map_left]

/-- The KEM hop for every scanned program, with the proof-carrying adversary: one ordinary one-key ML-KEM IND-CCA advantage plus one ordinary ML-KEM correctness error, both with coefficient one. -/
theorem certified_advantage (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes) (scanned : Scanned KemSK)
    (runtime : A) (count : Nat) (selected : Fin (count + 1)) :
    (sourceReal setup ensureInit supplied scanned runtime count selected).boolDistAdvantage
      (branch setup ensureInit supplied scanned runtime count selected false) ≤
      setup.kem.IND_CCA_Advantage (runtimeOfImpl (kemAmbientImpl setup.baseImpl))
        (certified setup ensureInit supplied scanned runtime count selected).toINDCCA +
        PqxdhRegistrationJointKemRawGame.correctnessError setup := by
  have proofCarrying := oneKey_indCCAAdvantage_eq_branchDist setup.kem
    (runtimeOfImpl (kemAmbientImpl setup.baseImpl))
    (certified setup ensureInit supplied scanned runtime count selected)
    (runtimeOfImpl_evalDist_pure (kemAmbientImpl setup.baseImpl))
    (runtimeOfImpl_evalDist_bind (kemAmbientImpl setup.baseImpl))
    (runtimeOfImpl_evalDist_liftProbComp setup.baseImpl)
    (runtimeOfImpl_noFail_bool (kemAmbientImpl setup.baseImpl))
  have plain := oneKey_indCCAAdvantage_eq_branchDist setup.kem
    (runtimeOfImpl (kemAmbientImpl setup.baseImpl))
    (adversary setup ensureInit supplied scanned runtime count selected)
    (runtimeOfImpl_evalDist_pure (kemAmbientImpl setup.baseImpl))
    (runtimeOfImpl_evalDist_bind (kemAmbientImpl setup.baseImpl))
    (runtimeOfImpl_evalDist_liftProbComp setup.baseImpl)
    (runtimeOfImpl_noFail_bool (kemAmbientImpl setup.baseImpl))
  have same : setup.kem.IND_CCA_Advantage (runtimeOfImpl (kemAmbientImpl setup.baseImpl))
      (certified setup ensureInit supplied scanned runtime count selected).toINDCCA =
      setup.kem.IND_CCA_Advantage (runtimeOfImpl (kemAmbientImpl setup.baseImpl))
        (adversary setup ensureInit supplied scanned runtime count selected).toINDCCA := by
    rw [proofCarrying, plain]
    simp only [oneKeyBranch, branch_erase]
  rw [same]
  exact advantage_error setup functional ensureInit supplied scanned runtime count selected

/-- One-sided form of the KEM hop for every scanned program and the proof-carrying adversary. -/
theorem real_le_ideal (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes) (scanned : Scanned KemSK)
    (runtime : A) (count : Nat) (selected : Fin (count + 1)) :
    𝒟[sourceReal setup ensureInit supplied scanned runtime count selected] {true} ≤
      𝒟[branch setup ensureInit supplied scanned runtime count selected false] {true} +
        ENNReal.ofReal (setup.kem.IND_CCA_Advantage (runtimeOfImpl (kemAmbientImpl setup.baseImpl))
          (certified setup ensureInit supplied scanned runtime count selected).toINDCCA +
          PqxdhRegistrationJointKemRawGame.correctnessError setup) :=
  (ProbComp.evalDist_apply_true_le_add_ofReal_boolDistAdvantage _ _).trans (add_le_add le_rfl
    (ENNReal.ofReal_le_ofReal (certified_advantage setup functional ensureInit supplied scanned runtime count
      selected)))

/-- The existing raw-ordinal prephase is the instance at the KEM scan of `AcceptKemCut.exposeAt`. -/
theorem preRaw_eq (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (checks : PqxdhServerAuthExperiment.Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes)
    (decision : X → Bool) (work : OracleComp (SourceSpec KemSK) X) (runtime : A)
    (count : Nat) (selected : Fin (count + 1)) (index : Nat) :
    PqxdhRegistrationJointKemRawChallenge.preRaw setup codec checks ensureInit supplied decision work runtime count
      selected index =
      pre setup ensureInit supplied (PqxdhRegistrationJointKemRawChallenge.rawScan setup codec checks decision work index)
        runtime count selected := rfl

/-- The existing stopped-source raw-ordinal prephase is the same instance. -/
theorem sourcePreRaw_eq (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (checks : PqxdhServerAuthExperiment.Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes)
    (decision : X → Bool) (work : OracleComp (SourceSpec KemSK) X) (runtime : A)
    (count : Nat) (selected : Fin (count + 1)) (index : Nat) :
    PqxdhRegistrationJointKemRawChallenge.sourcePreRaw setup codec checks ensureInit supplied decision work runtime
      count selected index =
      sourcePre setup ensureInit supplied (PqxdhRegistrationJointKemRawChallenge.rawScan setup codec checks decision work
        index) runtime count selected := rfl

/-- The existing raw-ordinal real game is the same instance. -/
theorem sourceReal_eq (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (checks : PqxdhServerAuthExperiment.Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes)
    (decision : X → Bool) (work : OracleComp (SourceSpec KemSK) X) (runtime : A)
    (count : Nat) (selected : Fin (count + 1)) (index : Nat) :
    PqxdhRegistrationJointKemRawGame.sourceReal setup codec checks ensureInit supplied decision work runtime count
      selected index =
      sourceReal setup ensureInit supplied (PqxdhRegistrationJointKemRawChallenge.rawScan setup codec checks decision
        work index) runtime count selected := rfl

/-- The existing raw-ordinal branches are the same instance. -/
theorem branch_eq (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (checks : PqxdhServerAuthExperiment.Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes)
    (decision : X → Bool) (work : OracleComp (SourceSpec KemSK) X) (runtime : A)
    (count : Nat) (selected : Fin (count + 1)) (index : Nat) (real : Bool) :
    PqxdhRegistrationJointKemRawGame.branch setup codec checks ensureInit supplied decision work runtime count
      selected index real =
      branch setup ensureInit supplied (PqxdhRegistrationJointKemRawChallenge.rawScan setup codec checks decision work
        index) runtime count selected real := rfl

/-- The existing proof-carrying raw-ordinal adversary is the same instance, so its IND-CCA advantage and its bills are those of the generic adversary at the KEM scan of `exposeAt`. -/
theorem adversary_eq (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (checks : PqxdhServerAuthExperiment.Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes)
    (decision : X → Bool) (work : OracleComp (SourceSpec KemSK) X) (runtime : A)
    (count : Nat) (selected : Fin (count + 1)) (index : Nat) :
    PqxdhRegistrationJointKemRawCertified.adversary setup codec checks ensureInit supplied decision work runtime count
      selected index =
      certified setup ensureInit supplied (PqxdhRegistrationJointKemRawChallenge.rawScan setup codec checks decision work
        index) runtime count selected := rfl

end BeaconcryptCore.Computational.PqxdhDeploymentLaterServerKemHop

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerKemHop.pre_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerKemHop.pre_source

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerKemHop.branch_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerKemHop.branch_source

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerKemHop.real_error' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerKemHop.real_error

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerKemHop.advantage_error' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerKemHop.advantage_error

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerKemHop.prefix_erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerKemHop.prefix_erase

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerKemHop.branch_erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerKemHop.branch_erase

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerKemHop.certified_advantage' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerKemHop.certified_advantage

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerKemHop.real_le_ideal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerKemHop.real_le_ideal

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerKemHop.preRaw_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerKemHop.preRaw_eq

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerKemHop.sourcePreRaw_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerKemHop.sourcePreRaw_eq

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerKemHop.sourceReal_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerKemHop.sourceReal_eq

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerKemHop.branch_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerKemHop.branch_eq

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerKemHop.adversary_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerKemHop.adversary_eq
