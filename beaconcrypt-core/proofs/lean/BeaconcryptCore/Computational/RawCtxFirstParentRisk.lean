import BeaconcryptCore.Computational.RawCtxFirstParentPrefix
import BeaconcryptCore.Computational.RawCtxSelectiveFamilyLogBounds
import BeaconcryptCore.Computational.RawCtxStatefulScanRisk
import BeaconcryptCore.Computational.PqxdhHiddenRoot
import BeaconcryptCore.Computational.RawCtxForwardParentSampler

/-!
The first-hit predecessor scan charges cache reuse against its actual chronological input log. Before a selected stop, every matching call is a fresh full76 draw. Its next32 coordinate can hit at most the previously logged addresses plus the current input. Unmatched calls and non-KDF work preserve absence of the current cursor address. The initial absence and source cache-domain invariant are explicit; no cached output is resampled or assumed independent.
-/
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.refined ratchet.concrete
open OracleComp OracleSpec ENNReal
set_option autoImplicit false
set_option maxRecDepth 10000
namespace BeaconcryptCore.Computational.RawCtxFirstParentRisk
open PqxdhJointKdf PqxdhJointKdfGame PqxdhSecretInputKdf PqxdhFullSecretInputKdf
open RawCtxSelectiveChainGame RawCtxPendingSelectiveFamily RawCtxSelectiveFamilyLog
open RawCtxSelectiveFamilyLogBounds
variable {A Result : Type} {S B : Nat}

def inputAddress (root : RootOutput) : JointKdfAddress := FixedHkdfDomain.ratchet.address root.toList

private theorem input_injective : Function.Injective inputAddress := by
  intro left right same
  exact Subtype.ext (congrArg JointKdfAddress.input same)

private theorem uniform_address (address : JointKdfAddress) :
    Pr{let root ← ($ᵗ RootOutput)}[inputAddress root = address] ≤
      (Fintype.card RootOutput : ℝ≥0∞)⁻¹ := by
  classical
  by_cases present : ∃ root, inputAddress root = address
  · obtain ⟨root, rfl⟩ := present
    simp only [input_injective.eq_iff]
    exact le_of_eq (SampleableType.prEvent_uniformSample_eq_singleton root)
  · rw [prEvent_eq_zero_of_forall_not _ _ fun root same => present ⟨root, same⟩]
    exact bot_le

/-- A uniform next32 input hits a fixed chronological address list with probability at most its length divided by the full 256-bit coordinate space. -/
theorem uniform_inputs (past : List JointKdfAddress) :
    Pr{let root ← ($ᵗ RootOutput)}[inputAddress root ∈ past] ≤
      (past.length : ℝ≥0∞) * (2 ^ 256 : ℝ≥0∞)⁻¹ := by
  have card : Fintype.card RootOutput = 2 ^ 256 := PqxdhHiddenRoot.hiddenRootCoordinate_card
  induction past with
  | nil => simp
  | cons address past ih =>
    simp only [List.mem_cons]
    refine (prEvent_or_le _ _ _).trans ?_
    have head := uniform_address address
    simp only [card, Nat.cast_pow, Nat.cast_ofNat] at head
    have total := add_le_add head ih
    simpa only [List.length_cons, Nat.cast_add, Nat.cast_one, add_mul, one_mul, add_comm] using total

/-- The actual full76 draw has the same next-input guessing bound, retaining all other coordinates in its distribution. -/
theorem full_inputs (past : List JointKdfAddress) :
    Pr{let output ← ($ᵗ FullOutput)}[inputAddress (PqxdhOrderedChainHybrids.nextChain output) ∈ past] ≤
      (past.length : ℝ≥0∞) * (2 ^ 256 : ℝ≥0∞)⁻¹ := by
  have same := (PqxdhOrderedChainHybrids.fullOutput_observed (fun _ root => pure root)).prEvent_eq
    (fun root => inputAddress root ∈ past)
  rw [bind_pure_comp _ ($ᵗ FullOutput), prEvent_map] at same
  simp only [bind_pure] at same
  rw [same]
  exact prEvent_bind_le_of_forall_le _ _ _ fun _ => uniform_inputs past

set_option linter.deprecated false in theorem _root_.BeaconcryptCore.Computational.RawCtxFirstParentRisk.full_inputs_vcvioLegacy :
    ∀ (past : List BeaconcryptCore.Computational.PqxdhJointKdf.JointKdfAddress), (probEvent ($ᵗ BeaconcryptCore.Computational.PqxdhFullSecretInputKdf.FullOutput) fun (output : BeaconcryptCore.Computational.PqxdhFullSecretInputKdf.FullOutput) => BeaconcryptCore.Computational.RawCtxFirstParentRisk.inputAddress (BeaconcryptCore.Computational.PqxdhOrderedChainHybrids.nextChain output) ∈ past) ≤ ↑past.length * (2 ^ 256)⁻¹ :=
  by simpa only [BeaconcryptCore.VCVioLegacy.probEvent_eq_prEvent] using @BeaconcryptCore.Computational.RawCtxFirstParentRisk.full_inputs

def Clean (state : LoggedState A) : Prop := state.1.2.1 (cursorAddress state.1.2.2) = none

def Valid (depth k : Nat) (state : LoggedState A) : Prop :=
  Covered state ∧ state.1.2.2.depth ≤ depth ∧ state.2.length ≤ k

/-- The actual source callback preserves cache provenance, predecessor depth and the exact chronological length bill. -/
theorem valid_step (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (depth stage k : Nat) (query : (Spec S B).Domain) (state : LoggedState A)
    (valid : Valid depth k state) (unchosen : RawCtxFirstParentPrefix.selected depth query state = false)
    (result : (Spec S B).Range query × LoggedState A)
    (supported : result ∈ support ((RawCtxSelectiveFamilyLog.handler source writer stage query).run state)) :
    Valid depth (k + if privateQuery query then 1 else 0) result.2 := by
  refine ⟨step_covered source writer stage query state valid.1 result supported, ?_⟩
  simp only [RawCtxSelectiveFamilyLog.handler, StateT.run, bind_pure_comp, support_map, Set.mem_image] at supported
  obtain ⟨reply, actual, rfl⟩ := supported
  constructor
  · exact RawCtxPendingParentPrefix.step_preserve source writer stage depth query state.1 valid.2.1
      (RawCtxFirstParentPrefix.unchosen depth query state unchosen).1 reply actual
  · change (inputs query state.2).length ≤ _
    rw [inputs_length]
    exact Nat.add_le_add_right valid.2.2 _

private theorem private_risk (source : FixedHkdfSha512NoSaltSource) (stage : Nat)
    (request : JointKdfAddress) (store : Store) (past : List JointKdfAddress)
    (covered : ∀ address output, store.1 address = some output → address ∈ past)
    (clean : store.1 (cursorAddress store.2) = none)
    (active : matched store.2 request = true → store.2.depth < stage) :
    Pr{let result ← privateStep source stage request store}[result.2.1 (cursorAddress result.2.2) ≠ none] ≤
      ((past.length + 1 : Nat) : ℝ≥0∞) * (2 ^ 256 : ℝ≥0∞)⁻¹ := by
  cases matching : matched store.2 request with
  | false =>
    have zero : Pr{let result ← privateStep source stage request store}[result.2.1 (cursorAddress result.2.2) ≠ none] = 0 := by
      apply prEvent_eq_zero_of_forall_mem_support
      intro result supported bad
      have exactState := private_state source stage request store result supported
      rw [exactState] at bad
      have different : cursorAddress store.2 ≠ request := by
        exact Ne.symm (by simpa only [matched, decide_eq_false_iff_not] using matching)
      have unchanged : advance store.2 request result.1 = store.2 := by simp [advance, matching]
      change (store.1.cacheQuery request result.1) (cursorAddress (advance store.2 request result.1)) ≠ none at bad
      rw [unchanged, QueryCache.cacheQuery_of_ne (spec := JointKdfRO) store.1 result.1 different, clean] at bad
      exact bad rfl
    rw [zero]
    exact bot_le
  | true =>
    have same : request = cursorAddress store.2 := by simpa only [matched, decide_eq_true_eq] using matching
    have missing : store.1 request = none := same ▸ clean
    rw [private_selected source stage request store missing matching (active matching), prEvent_map]
    have inclusion : ∀ output : FullOutput,
        (store.1.cacheQuery request output) (cursorAddress (advance store.2 request output)) ≠ none →
        inputAddress (PqxdhOrderedChainHybrids.nextChain output) ∈ past ++ [request] := by
      intro output bad
      by_contra absent
      have different : inputAddress (PqxdhOrderedChainHybrids.nextChain output) ≠ request := by
        intro same
        exact absent (by simp [same])
      have missingNext : store.1 (inputAddress (PqxdhOrderedChainHybrids.nextChain output)) = none := by
        cases found : store.1 (inputAddress (PqxdhOrderedChainHybrids.nextChain output)) with
        | none => rfl
        | some value => exact False.elim (absent (List.mem_append_left _ (covered _ value found)))
      have unchanged : cursorAddress (advance store.2 request output) =
          inputAddress (PqxdhOrderedChainHybrids.nextChain output) := by
        simp only [advance, matching, ite_true]
        rfl
      rw [unchanged, QueryCache.cacheQuery_of_ne (spec := JointKdfRO) store.1 output different, missingNext] at bad
      exact bad rfl
    exact (prEvent_mono _ _ _ inclusion).trans (by simpa only [List.length_append, List.length_singleton] using full_inputs (past ++ [request]))

set_option backward.isDefEq.respectTransparency false in
/-- The actual complete callback has zero risk when it performs no private KDF call; otherwise its fresh-coordinate collision risk is bounded by the retained chronological list plus this input. -/
theorem callback_risk (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (depth k : Nat) (query : (Spec S B).Domain) (state : LoggedState A)
    (valid : Valid depth k state) (clean : Clean state)
    (unchosen : RawCtxFirstParentPrefix.selected depth query state = false) :
    Pr{let result ← (RawCtxSelectiveFamilyLog.handler source writer (depth + 1) query).run state}[¬Clean result.2] ≤
      if privateQuery query then ((k + 1 : Nat) : ℝ≥0∞) * (2 ^ 256 : ℝ≥0∞)⁻¹ else 0 := by
  cases found : RawCtxSelectedFamilyContext.queryAddress query with
  | none =>
    simp only [privateQuery, found, ne_eq, not_true_eq_false, ite_false]
    apply le_of_eq
    apply prEvent_eq_zero_of_forall_mem_support
    intro result supported bad
    simp only [RawCtxSelectiveFamilyLog.handler, StateT.run, bind_pure_comp, support_map, Set.mem_image] at supported
    obtain ⟨reply, actual, rfl⟩ := supported
    have unchanged := RawCtxPendingNonKdfStore.callback_store source writer (depth + 1) query found state.1 reply actual
    apply bad
    change reply.2.2.1 (cursorAddress reply.2.2.2) = none
    rw [unchanged]
    exact clean
  | some address =>
    simp only [privateQuery, found]
    have active : matched state.1.2.2 address = true → state.1.2.2.depth < depth + 1 := by
      intro matching
      exact Nat.lt_succ_of_le valid.2.1
    have localRisk := private_risk source (depth + 1) address state.1.2 state.2 valid.1 clean active
    have cost : ((state.2.length + 1 : Nat) : ℝ≥0∞) * (2 ^ 256 : ℝ≥0∞)⁻¹ ≤
        ((k + 1 : Nat) : ℝ≥0∞) * (2 ^ 256 : ℝ≥0∞)⁻¹ := by
      apply mul_le_mul_left
      exact_mod_cast Nat.add_le_add_right valid.2.2 1
    apply (le_trans · cost)
    have logged : Pr{let result ← (RawCtxSelectiveFamilyLog.handler source writer (depth + 1) query).run state}[¬Clean result.2] =
        Pr{let result ← (RawCtxPendingSelectiveFamily.handler source writer (depth + 1) query).run state.1}[
          result.2.2.1 (cursorAddress result.2.2.2) ≠ none] := by
      rw [show (RawCtxSelectiveFamilyLog.handler source writer (depth + 1) query).run state =
          (fun result => (result.1, (result.2, RawCtxSelectiveFamilyLog.inputs query state.2))) <$>
            (RawCtxPendingSelectiveFamily.handler source writer (depth + 1) query).run state.1 from by
        simp only [RawCtxSelectiveFamilyLog.handler, StateT.run, bind_pure_comp], prEvent_map]
      exact prEvent_congr _ _ _ fun _ => Iff.rfl
    rw [logged]
    rcases query with ((request | opening) | ((request | sealing) | request)) | request
    all_goals simp only [RawCtxSelectedFamilyContext.queryAddress, RawCtxSelectedFamilyContext.primitiveAddress] at found
    all_goals try cases found
    all_goals first | rw [RawCtxPendingParentCallbacks.receive_step] | rw [RawCtxPendingParentCallbacks.send_step]
    all_goals rw [prEvent_map]
    all_goals exact localRisk

set_option linter.deprecated false in set_option linter.unusedVariables false in theorem _root_.BeaconcryptCore.Computational.RawCtxFirstParentRisk.callback_risk_vcvioLegacy :
    ∀ {A : Type} {S B : Nat} (source : BeaconcryptCore.Computational.PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : BeaconcryptCore.Computational.RawCtxMixedShared.Writer) (depth k : Nat) (query : @OracleSpec.Domain.{0, 0} (Sum.{0, 0} (Sum.{0, 0} (Sum.{0, 0} (BeaconcryptCore.Computational.RawCtxChainReceive.Kdf beaconcrypt_core.ratchet.RatchetChain beaconcrypt_core.ratchet.RatchetChain beaconcrypt_core.ratchet.RatchetMaterial BeaconcryptCore.Computational.RawCtxWholeOwner.OpenContext) (BeaconcryptCore.Computational.RawCtxInterpretedOpening.Opening beaconcrypt_core.ratchet.RatchetChain beaconcrypt_core.ratchet.RatchetChain beaconcrypt_core.ratchet.RatchetMaterial BeaconcryptCore.Computational.RawCtxWholeOwner.OpenContext)) (Sum.{0, 0} (Sum.{0, 0} (BeaconcryptCore.Computational.RawCtxChainSend.Kdf beaconcrypt_core.ratchet.RatchetChain beaconcrypt_core.ratchet.RatchetChain beaconcrypt_core.ratchet.RatchetMaterial BeaconcryptCore.Computational.RawCtxSourceSend.SealContext) (BeaconcryptCore.Computational.RawCtxChainSend.Seal beaconcrypt_core.ratchet.RatchetChain beaconcrypt_core.ratchet.RatchetChain beaconcrypt_core.ratchet.RatchetMaterial BeaconcryptCore.Computational.RawCtxSourceSend.SealContext)) (Sum.{0, 0} Nat (Sum.{0, 0} Pqxdh.Bytes BeaconcryptCore.Computational.PqxdhJointKdfGame.JointKdfViewQuery)))) (BeaconcryptCore.Computational.RawCtxGenericFamilyRead.ReadInput (BeaconcryptCore.Computational.RawCtxPendingFamilyLiveQueries.Kernel beaconcrypt_core.ratchet.RatchetChain) S B)) (BeaconcryptCore.Computational.RawCtxPendingSelectiveFamily.Spec S B)) (state : BeaconcryptCore.Computational.RawCtxSelectiveFamilyLog.LoggedState A) (valid : @BeaconcryptCore.Computational.RawCtxFirstParentRisk.Valid A depth k state) (clean : @BeaconcryptCore.Computational.RawCtxFirstParentRisk.Clean A state) (unchosen : @Eq.{1} Bool (@BeaconcryptCore.Computational.RawCtxFirstParentPrefix.selected A S B depth query state) Bool.false), @LE.le.{0} ENNReal ENNReal.instLE (@probEvent.{0, 0} ProbComp (Prod.{0, 0} (@OracleSpec.Range.{0, 0} (Sum.{0, 0} (Sum.{0, 0} (Sum.{0, 0} (BeaconcryptCore.Computational.RawCtxChainReceive.Kdf beaconcrypt_core.ratchet.RatchetChain beaconcrypt_core.ratchet.RatchetChain beaconcrypt_core.ratchet.RatchetMaterial BeaconcryptCore.Computational.RawCtxWholeOwner.OpenContext) (BeaconcryptCore.Computational.RawCtxInterpretedOpening.Opening beaconcrypt_core.ratchet.RatchetChain beaconcrypt_core.ratchet.RatchetChain beaconcrypt_core.ratchet.RatchetMaterial BeaconcryptCore.Computational.RawCtxWholeOwner.OpenContext)) (Sum.{0, 0} (Sum.{0, 0} (BeaconcryptCore.Computational.RawCtxChainSend.Kdf beaconcrypt_core.ratchet.RatchetChain beaconcrypt_core.ratchet.RatchetChain beaconcrypt_core.ratchet.RatchetMaterial BeaconcryptCore.Computational.RawCtxSourceSend.SealContext) (BeaconcryptCore.Computational.RawCtxChainSend.Seal beaconcrypt_core.ratchet.RatchetChain beaconcrypt_core.ratchet.RatchetChain beaconcrypt_core.ratchet.RatchetMaterial BeaconcryptCore.Computational.RawCtxSourceSend.SealContext)) (Sum.{0, 0} Nat (Sum.{0, 0} Pqxdh.Bytes BeaconcryptCore.Computational.PqxdhJointKdfGame.JointKdfViewQuery)))) (BeaconcryptCore.Computational.RawCtxGenericFamilyRead.ReadInput (BeaconcryptCore.Computational.RawCtxPendingFamilyLiveQueries.Kernel beaconcrypt_core.ratchet.RatchetChain) S B)) (BeaconcryptCore.Computational.RawCtxPendingSelectiveFamily.Spec S B) query) (BeaconcryptCore.Computational.RawCtxSelectiveFamilyLog.LoggedState A)) (@instMonadLiftTOfMonadLift.{0, 0, 0, 0} ProbComp PMF.{0} SPMF.{0} SPMF.instMonadLiftPMF.{0} (@PFunctor.FreeM.instMonadLiftTPMF.{0, 0} (@OracleSpec.toPFunctor.{0, 0} Nat unifSpec) (@OracleSpec.IsUniformSpec.toIsProbabilitySpec.{0, 0} Nat unifSpec OracleSpec.instIsUniformSpecNatUnifSpec))) (@StateT.run.{0, 0} (BeaconcryptCore.Computational.RawCtxSelectiveFamilyLog.LoggedState A) ProbComp (@OracleSpec.Range.{0, 0} (Sum.{0, 0} (Sum.{0, 0} (Sum.{0, 0} (BeaconcryptCore.Computational.RawCtxChainReceive.Kdf beaconcrypt_core.ratchet.RatchetChain beaconcrypt_core.ratchet.RatchetChain beaconcrypt_core.ratchet.RatchetMaterial BeaconcryptCore.Computational.RawCtxWholeOwner.OpenContext) (BeaconcryptCore.Computational.RawCtxInterpretedOpening.Opening beaconcrypt_core.ratchet.RatchetChain beaconcrypt_core.ratchet.RatchetChain beaconcrypt_core.ratchet.RatchetMaterial BeaconcryptCore.Computational.RawCtxWholeOwner.OpenContext)) (Sum.{0, 0} (Sum.{0, 0} (BeaconcryptCore.Computational.RawCtxChainSend.Kdf beaconcrypt_core.ratchet.RatchetChain beaconcrypt_core.ratchet.RatchetChain beaconcrypt_core.ratchet.RatchetMaterial BeaconcryptCore.Computational.RawCtxSourceSend.SealContext) (BeaconcryptCore.Computational.RawCtxChainSend.Seal beaconcrypt_core.ratchet.RatchetChain beaconcrypt_core.ratchet.RatchetChain beaconcrypt_core.ratchet.RatchetMaterial BeaconcryptCore.Computational.RawCtxSourceSend.SealContext)) (Sum.{0, 0} Nat (Sum.{0, 0} Pqxdh.Bytes BeaconcryptCore.Computational.PqxdhJointKdfGame.JointKdfViewQuery)))) (BeaconcryptCore.Computational.RawCtxGenericFamilyRead.ReadInput (BeaconcryptCore.Computational.RawCtxPendingFamilyLiveQueries.Kernel beaconcrypt_core.ratchet.RatchetChain) S B)) (BeaconcryptCore.Computational.RawCtxPendingSelectiveFamily.Spec S B) query) (@BeaconcryptCore.Computational.RawCtxSelectiveFamilyLog.handler A S B source writer (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) depth (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) query) state) fun (result : Prod.{0, 0} (@OracleSpec.Range.{0, 0} (Sum.{0, 0} (Sum.{0, 0} (Sum.{0, 0} (BeaconcryptCore.Computational.RawCtxChainReceive.Kdf beaconcrypt_core.ratchet.RatchetChain beaconcrypt_core.ratchet.RatchetChain beaconcrypt_core.ratchet.RatchetMaterial BeaconcryptCore.Computational.RawCtxWholeOwner.OpenContext) (BeaconcryptCore.Computational.RawCtxInterpretedOpening.Opening beaconcrypt_core.ratchet.RatchetChain beaconcrypt_core.ratchet.RatchetChain beaconcrypt_core.ratchet.RatchetMaterial BeaconcryptCore.Computational.RawCtxWholeOwner.OpenContext)) (Sum.{0, 0} (Sum.{0, 0} (BeaconcryptCore.Computational.RawCtxChainSend.Kdf beaconcrypt_core.ratchet.RatchetChain beaconcrypt_core.ratchet.RatchetChain beaconcrypt_core.ratchet.RatchetMaterial BeaconcryptCore.Computational.RawCtxSourceSend.SealContext) (BeaconcryptCore.Computational.RawCtxChainSend.Seal beaconcrypt_core.ratchet.RatchetChain beaconcrypt_core.ratchet.RatchetChain beaconcrypt_core.ratchet.RatchetMaterial BeaconcryptCore.Computational.RawCtxSourceSend.SealContext)) (Sum.{0, 0} Nat (Sum.{0, 0} Pqxdh.Bytes BeaconcryptCore.Computational.PqxdhJointKdfGame.JointKdfViewQuery)))) (BeaconcryptCore.Computational.RawCtxGenericFamilyRead.ReadInput (BeaconcryptCore.Computational.RawCtxPendingFamilyLiveQueries.Kernel beaconcrypt_core.ratchet.RatchetChain) S B)) (BeaconcryptCore.Computational.RawCtxPendingSelectiveFamily.Spec S B) query) (BeaconcryptCore.Computational.RawCtxSelectiveFamilyLog.LoggedState A)) => Not (@BeaconcryptCore.Computational.RawCtxFirstParentRisk.Clean A (@Prod.snd.{0, 0} (@OracleSpec.Range.{0, 0} (Sum.{0, 0} (Sum.{0, 0} (Sum.{0, 0} (BeaconcryptCore.Computational.RawCtxChainReceive.Kdf beaconcrypt_core.ratchet.RatchetChain beaconcrypt_core.ratchet.RatchetChain beaconcrypt_core.ratchet.RatchetMaterial BeaconcryptCore.Computational.RawCtxWholeOwner.OpenContext) (BeaconcryptCore.Computational.RawCtxInterpretedOpening.Opening beaconcrypt_core.ratchet.RatchetChain beaconcrypt_core.ratchet.RatchetChain beaconcrypt_core.ratchet.RatchetMaterial BeaconcryptCore.Computational.RawCtxWholeOwner.OpenContext)) (Sum.{0, 0} (Sum.{0, 0} (BeaconcryptCore.Computational.RawCtxChainSend.Kdf beaconcrypt_core.ratchet.RatchetChain beaconcrypt_core.ratchet.RatchetChain beaconcrypt_core.ratchet.RatchetMaterial BeaconcryptCore.Computational.RawCtxSourceSend.SealContext) (BeaconcryptCore.Computational.RawCtxChainSend.Seal beaconcrypt_core.ratchet.RatchetChain beaconcrypt_core.ratchet.RatchetChain beaconcrypt_core.ratchet.RatchetMaterial BeaconcryptCore.Computational.RawCtxSourceSend.SealContext)) (Sum.{0, 0} Nat (Sum.{0, 0} Pqxdh.Bytes BeaconcryptCore.Computational.PqxdhJointKdfGame.JointKdfViewQuery)))) (BeaconcryptCore.Computational.RawCtxGenericFamilyRead.ReadInput (BeaconcryptCore.Computational.RawCtxPendingFamilyLiveQueries.Kernel beaconcrypt_core.ratchet.RatchetChain) S B)) (BeaconcryptCore.Computational.RawCtxPendingSelectiveFamily.Spec S B) query) (BeaconcryptCore.Computational.RawCtxSelectiveFamilyLog.LoggedState A) result))) (@ite.{1} ENNReal (@BeaconcryptCore.Computational.RawCtxSelectiveFamilyLogBounds.privateQuery S B query) (@BeaconcryptCore.Computational.RawCtxSelectiveFamilyLogBounds.instDecidablePredDomainSumKdfRatchetChainRatchetMaterialOpenContextOpeningKdfSealContextSealNatBytesJointKdfViewQueryReadInputKernelSpecPrivateQuery S B query) (@HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal (@instHMul.{0} ENNReal (@Distrib.toMul.{0} ENNReal (@instDistribOfSemiring.{0} ENNReal (@CommSemiring.toSemiring.{0} ENNReal ENNReal.instCommSemiring)))) (@Nat.cast.{0} ENNReal (@AddMonoidWithOne.toNatCast.{0} ENNReal (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.instAddCommMonoidWithOne)) (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) k (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) (@Inv.inv.{0} ENNReal ENNReal.instInv (@HPow.hPow.{0, 0, 0} ENNReal Nat ENNReal (@instHPow.{0, 0} ENNReal Nat (@NPow.toPow.{0} ENNReal (@Monoid.toNPow.{0} ENNReal (@Semiring.toMonoid.{0} ENNReal (@CommSemiring.toSemiring.{0} ENNReal ENNReal.instCommSemiring))))) (@OfNat.ofNat.{0} ENNReal (nat_lit 2) (@instOfNatAtLeastTwo.{0} ENNReal (nat_lit 2) (@AddMonoidWithOne.toNatCast.{0} ENNReal (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.instAddCommMonoidWithOne)) (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))) (@OfNat.ofNat.{0} Nat (nat_lit 256) (instOfNatNat (nat_lit 256)))))) (@OfNat.ofNat.{0} ENNReal (nat_lit 0) (@Zero.toOfNat0.{0} ENNReal ENNReal.instZero))) :=
  by simpa only [BeaconcryptCore.VCVioLegacy.probEvent_eq_prEvent] using @BeaconcryptCore.Computational.RawCtxFirstParentRisk.callback_risk

/-- The actual first-hit/predecessor scan accumulates only its bounded original private calls; every failure risk is indexed by the retained chronological input count. -/
theorem scan_risk (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (depth k calls : Nat) (client : OracleComp (Spec S B) Result)
    (bounded : client.IsQueryBoundP privateQuery calls) (state : LoggedState A)
    (valid : Valid depth k state) (clean : Clean state) :
    Pr{let result ← (RawCtxStatefulPendingPrefix.scan
      (RawCtxFirstParentPrefix.selected depth) (RawCtxSelectiveFamilyLog.handler source writer (depth + 1)) client state)}[¬Clean result.2] ≤
      ∑ j ∈ Finset.range calls, ((k + j + 1 : Nat) : ℝ≥0∞) * (2 ^ 256 : ℝ≥0∞)⁻¹ := by
  exact RawCtxStatefulScanRisk.scan_risk _ _ privateQuery Clean (Valid depth)
    (fun count => ((count + 1 : Nat) : ℝ≥0∞) * (2 ^ 256 : ℝ≥0∞)⁻¹)
    (fun count query before unchosen valid _ result supported =>
      valid_step source writer depth (depth + 1) count query before valid unchosen result supported)
    (fun count query before unchosen valid clean =>
      callback_risk source writer depth count query before valid clean unchosen)
    client calls k bounded state valid clean

/-- The original finite LIVE family supplies S+51R directly; no probability-to-query transport is used. -/
theorem source_risk {M P I D K : Type}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (depth k : Nat)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp (RawCtxProtocolReveals.SourceSpec S B) Result)
    (budget : RawCtxRevealBudgets.Budget) (bounded : RawCtxRevealBudgets.Bounded client budget)
    (state : RawCtxProtocolReveals.State M P I D K S B) (initial : LoggedState A)
    (valid : Valid depth k initial) (clean : Clean initial) :
    Pr{let result ← RawCtxFirstParentPrefix.scan source writer depth (depth + 1) sender route decode client state initial}[¬Clean result.2] ≤
      ∑ j ∈ Finset.range (budget.1 .send + 51 * budget.1 .raw),
        ((k + j + 1 : Nat) : ℝ≥0∞) * (2 ^ 256 : ℝ≥0∞)⁻¹ :=
  scan_risk source writer depth k _ (program sender route decode client state)
    (RawCtxSelectiveFamilyLogBounds.source_private sender route decode client budget bounded state) initial valid clean

/-- The executable forward sampler carries the same exact source state, so its current-input collision event has this derived source bound. -/
theorem carried_risk {M P I D K : Type}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (depth k : Nat)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp (RawCtxProtocolReveals.SourceSpec S B) Result)
    (budget : RawCtxRevealBudgets.Budget) (bounded : RawCtxRevealBudgets.Bounded client budget)
    (state : RawCtxProtocolReveals.State M P I D K S B) (initial : LoggedState A)
    (valid : Valid depth k initial) (clean : Clean initial) :
    Pr{let result ← RawCtxForwardParentSampler.first source writer depth (depth + 1) sender route decode client state initial}[¬Clean (RawCtxLoggedParentSampler.pack sender route decode result).2] ≤
      ∑ j ∈ Finset.range (budget.1 .send + 51 * budget.1 .raw),
        ((k + j + 1 : Nat) : ℝ≥0∞) * (2 ^ 256 : ℝ≥0∞)⁻¹ := by
  have original := source_risk source writer depth k sender route decode client budget bounded state initial valid clean
  rw [← RawCtxForwardParentSampler.first_pack source writer depth (depth + 1) sender route decode client state initial,
    prEvent_map] at original
  exact original

def Cached {M P I D K : Type} : RawCtxLoggedParentSampler.Cut M P I D K A Result S B → Prop
  | .pending context state => state.1.2.1 (RawCtxSelectedFamilyContext.address context) ≠ none
  | _ => False

/-- The actual earliest matched cache-hit branch of the executable source sampler is charged by the derived chronological birthday sum, without discarding its full continuation. -/
theorem cached_risk {M P I D K : Type}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (depth k : Nat)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp (RawCtxProtocolReveals.SourceSpec S B) Result)
    (budget : RawCtxRevealBudgets.Budget) (bounded : RawCtxRevealBudgets.Bounded client budget)
    (state : RawCtxProtocolReveals.State M P I D K S B) (initial : LoggedState A)
    (valid : Valid depth k initial) (clean : Clean initial) :
    Pr{let x ← RawCtxForwardParentSampler.first source writer depth (depth + 1) sender route decode client state initial}[Cached x] ≤
      ∑ j ∈ Finset.range (budget.1 .send + 51 * budget.1 .raw),
        ((k + j + 1 : Nat) : ℝ≥0∞) * (2 ^ 256 : ℝ≥0∞)⁻¹ := by
  refine (prEvent_mono_of_support _ _ (fun result => ¬Clean (RawCtxLoggedParentSampler.pack sender route decode result).2) ?_).trans
    (carried_risk source writer depth k sender route decode client budget bounded state initial valid clean)
  intro result supported bad
  cases result with
  | complete value reached => exact False.elim bad
  | other saved => exact False.elim bad
  | pending context reached =>
    have origin := RawCtxForwardParentSampler.first_origin source writer depth (depth + 1) sender route decode
      client state initial reached valid.1 context supported
    have same : RawCtxSelectedFamilyContext.address context = cursorAddress reached.1.2.2 := by
      simpa only [matched, decide_eq_true_eq] using origin.2.1
    change reached.1.2.1 (cursorAddress reached.1.2.2) ≠ none
    rw [← same]
    exact bad

/-- An actual empty private cache starts clean regardless of the retained initial chain coordinate and prior input list. -/
theorem empty_clean (state : RawCtxSharedPrimitive.SharedState A) (cursor : Cursor) (past : List JointKdfAddress) :
    Clean ((state, ((fun _ => none), cursor)), past) := rfl

end BeaconcryptCore.Computational.RawCtxFirstParentRisk

/-- info: 'BeaconcryptCore.Computational.RawCtxFirstParentRisk.uniform_inputs' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxFirstParentRisk.uniform_inputs

/-- info: 'BeaconcryptCore.Computational.RawCtxFirstParentRisk.full_inputs' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxFirstParentRisk.full_inputs

/-- info: 'BeaconcryptCore.Computational.RawCtxFirstParentRisk.valid_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxFirstParentRisk.valid_step

/-- info: 'BeaconcryptCore.Computational.RawCtxFirstParentRisk.callback_risk' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxFirstParentRisk.callback_risk

/-- info: 'BeaconcryptCore.Computational.RawCtxFirstParentRisk.scan_risk' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxFirstParentRisk.scan_risk

/-- info: 'BeaconcryptCore.Computational.RawCtxFirstParentRisk.source_risk' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxFirstParentRisk.source_risk

/-- info: 'BeaconcryptCore.Computational.RawCtxFirstParentRisk.carried_risk' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxFirstParentRisk.carried_risk

/-- info: 'BeaconcryptCore.Computational.RawCtxFirstParentRisk.cached_risk' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxFirstParentRisk.cached_risk

/-- info: 'BeaconcryptCore.Computational.RawCtxFirstParentRisk.empty_clean' does not depend on any axioms -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxFirstParentRisk.empty_clean
