import BeaconcryptCore.Computational.PqxdhInitialNativeCarried
import BeaconcryptCore.Computational.RawCtxFirstParentRisk

/-!
The complete source predecessor sampler charges actual cached hits through its original chronological private-input log. External preparation, initialization, application, selector and publication callbacks preserve that separate private table and cursor. The earlier fresh-coordinate calculation therefore lifts to the same full source execution without resampling a hit or assuming that a selected request misses.
-/
open OracleComp OracleSpec CoreModels Aeneas ENNReal
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhInitialNativeRisk
open PqxdhJointKdf PqxdhJointKdfGame PqxdhInitialNativeLog PqxdhInitialNativePrefix PqxdhInitialBeaconAmbient
variable {ι I D K X Response Shared A N C Result : Type} {extra : OracleSpec ι} {S B : Nat}

def counted : (Spec extra RatchetChain I D K X Response Shared S B).Domain → Prop
  | .inl query => RawCtxSelectiveFamilyLogBounds.privateQuery query
  | .inr _ => False

instance : DecidablePred (counted (extra := extra) (I := I) (D := D) (K := K) (X := X) (Response := Response) (Shared := Shared) (S := S) (B := B)) :=
  fun query => match query with
    | .inl request => inferInstanceAs (Decidable (RawCtxSelectiveFamilyLogBounds.privateQuery request))
    | .inr _ => isFalse id

def Clean (state : State A N C) : Prop := RawCtxFirstParentRisk.Clean state.1

def Valid (depth k : Nat) (state : State A N C) : Prop := RawCtxFirstParentRisk.Valid depth k state.1

set_option backward.isDefEq.respectTransparency false in
/-- Each actual unselected callback preserves private-cache provenance, predecessor depth and the chronological counted-input bound. -/
theorem valid_step (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (depth stage k : Nat)
    (external : QueryImpl (External extra RatchetChain I D K X Response Shared) (Ambient A N C))
    (query : (Spec extra RatchetChain I D K X Response Shared S B).Domain) (state : State A N C)
    (valid : Valid depth k state) (unchosen : selected (extra := extra) depth query state = false)
    (result : (Spec extra RatchetChain I D K X Response Shared S B).Range query × State A N C)
    (supported : result ∈ support ((handler source writer stage external query).run state)) :
    Valid depth (k + if counted (extra := extra) query then 1 else 0) result.2 := by
  cases query with
  | inl query =>
      rw [live_handler] at supported
      simp only [support_map, Set.mem_image] at supported
      obtain ⟨reply, actual, rfl⟩ := supported
      exact RawCtxFirstParentRisk.valid_step source writer depth stage k query state.1 valid unchosen reply actual
  | inr query =>
      rw [external_handler] at supported
      simp only [support_map, Set.mem_image] at supported
      obtain ⟨reply, actual, rfl⟩ := supported
      simpa only [counted, ite_false, Nat.add_zero, Valid, RawCtxFirstParentRisk.Valid, RawCtxSelectiveFamilyLog.Covered] using valid

set_option backward.isDefEq.respectTransparency false in
/-- Every external callback has zero cache-collision risk; each actual private step has only the existing full76 next-coordinate risk from its chronological inputs. -/
theorem callback_risk (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (depth k : Nat)
    (external : QueryImpl (External extra RatchetChain I D K X Response Shared) (Ambient A N C))
    (query : (Spec extra RatchetChain I D K X Response Shared S B).Domain) (state : State A N C)
    (valid : Valid depth k state) (clean : Clean state)
    (unchosen : selected (extra := extra) depth query state = false) :
    Pr{let result ← (handler source writer (depth + 1) external query).run state}[¬Clean result.2] ≤
      if counted (extra := extra) query then ((k + 1 : Nat) : ℝ≥0∞) * (2 ^ 256 : ℝ≥0∞)⁻¹ else 0 := by
  cases query with
  | inl query =>
      rw [live_handler, prEvent_map]
      exact RawCtxFirstParentRisk.callback_risk source writer depth k query state.1 valid clean unchosen
  | inr query =>
      rw [external_handler, prEvent_map]
      simp only [Clean, RawCtxFirstParentRisk.Clean] at clean ⊢
      simp [counted, clean, -evalDist_apply_singleton, -evalDist_apply_setOf, -evalDist_apply_univ]

/-- The full-interface first-hit scan accumulates only its actual counted source calls, with collision terms indexed by the retained chronological input bound. -/
theorem scan_risk (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (depth k calls : Nat)
    (external : QueryImpl (External extra RatchetChain I D K X Response Shared) (Ambient A N C))
    (client : OracleComp (Spec extra RatchetChain I D K X Response Shared S B) Result)
    (bounded : client.IsQueryBoundP (counted (extra := extra)) calls) (state : State A N C)
    (valid : Valid depth k state) (clean : Clean state) :
    Pr{let result ← (RawCtxStatefulPendingPrefix.scan (selected (extra := extra) depth)
      (handler source writer (depth + 1) external) client state)}[¬Clean result.2] ≤
      ∑ j ∈ Finset.range calls, ((k + j + 1 : Nat) : ℝ≥0∞) * (2 ^ 256 : ℝ≥0∞)⁻¹ :=
  RawCtxStatefulScanRisk.scan_risk _ _ counted Clean (Valid depth)
    (fun count => ((count + 1 : Nat) : ℝ≥0∞) * (2 ^ 256 : ℝ≥0∞)⁻¹)
    (fun count query before unchosen valid _ result supported =>
      valid_step source writer depth (depth + 1) count external query before valid unchosen result supported)
    (fun count query before unchosen valid clean =>
      callback_risk source writer depth count external query before valid clean unchosen)
    client calls k bounded state valid clean

section Source
open PqxdhInitialNativeCarried
variable {M P Origin : Type}
variable (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
  (mark : PqxdhBeaconPhase2Shared.Secrets Shared → Origin)
  (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
  (execution : Execution extra M P I D K Result Origin S B)

/-- The complete original consumed-registration builder and adaptive post client supply the concrete source callback cap used in the chronological collision sum. -/
theorem source_risk (depth k qPost : Nat)
    (external : QueryImpl (External extra RatchetChain I D K X Response Shared) (Ambient A N C))
    (bounded : ∀ reply, (execution.outside reply).IsTotalQueryBound qPost)
    (state : State A N C) (valid : Valid depth k state) (clean : Clean state) :
    Pr{let result ← (RawCtxStatefulPendingPrefix.scan (selected (extra := extra) depth)
      (handler source writer (depth + 1) external) (original source mark sender route decode execution) state)}[¬Clean result.2] ≤
      ∑ j ∈ Finset.range (7 + qPost * 67), ((k + j + 1 : Nat) : ℝ≥0∞) * (2 ^ 256 : ℝ≥0∞)⁻¹ :=
  scan_risk source writer depth k (7 + qPost * 67) external (original source mark sender route decode execution)
    (PqxdhInitialOriginPost.sequence_total source execution.initial mark execution.origin sender route decode
      execution.index execution.metadata execution.ready execution.outside qPost bounded
      (execution.before, execution.trace)).isQueryBoundP state valid clean

/-- The executable descriptor-carrying sampler pays the same source-derived collision sum while retaining its complete original state and continuation. -/
theorem carried_risk (depth k qPost : Nat)
    (external : QueryImpl (External extra RatchetChain I D K X Response Shared) (Ambient A N C))
    (bounded : ∀ reply, (execution.outside reply).IsTotalQueryBound qPost)
    (state : State A N C) (valid : Valid depth k state) (clean : Clean state) :
    Pr{let result ← carried source writer mark sender route decode execution depth (depth + 1) external state}[¬Clean (RawCtxForwardScan.pack
      (PqxdhInitialOriginContext.frame (X := X) (Response := Response) mark sender route decode) result).2] ≤
      ∑ j ∈ Finset.range (7 + qPost * 67), ((k + j + 1 : Nat) : ℝ≥0∞) * (2 ^ 256 : ℝ≥0∞)⁻¹ := by
  have bound := source_risk source writer mark sender route decode execution depth k qPost external bounded state valid clean
  rw [← carried_pack source writer mark sender route decode execution depth (depth + 1) external state, prEvent_map] at bound
  exact bound

set_option linter.deprecated false in set_option linter.unusedVariables false in theorem _root_.BeaconcryptCore.Computational.PqxdhInitialNativeRisk.carried_risk_vcvioLegacy :
    ∀ {ι I D K X Response Shared A N C Result : Type} {extra : OracleSpec.{0, 0} ι} {S B : Nat} {M P Origin : Type} (source : BeaconcryptCore.Computational.PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : BeaconcryptCore.Computational.RawCtxMixedShared.Writer) (mark : BeaconcryptCore.Computational.PqxdhBeaconPhase2Shared.Secrets Shared → Origin) (sender : M → Aeneas.Std.U64) (route : BeaconcryptCore.Computational.RawCtxServerRouting.SenderDecoder) (decode : BeaconcryptCore.Computational.RawCtxReceive.FrameDecoder) (execution : @BeaconcryptCore.Computational.PqxdhInitialNativeCarried.Execution ι extra M P I D K Result Origin S B) (depth k qPost : Nat) (external : @QueryImpl.{0, 0, 0} (Sum.{0, 0} (BeaconcryptCore.Computational.PqxdhBeaconPhase2Shared.Query I D K X Response Shared) (Sum.{0, 0} Response (Sum.{0, 0} (BeaconcryptCore.Computational.PqxdhBeaconPhase2Shared.Secrets Shared) (Sum.{0, 0} ι BeaconcryptCore.Computational.PqxdhServerRegistrationPublication.AuxQuery)))) (@BeaconcryptCore.Computational.PqxdhInitialNativeLog.External ι extra beaconcrypt_core.ratchet.RatchetChain I D K X Response Shared) (BeaconcryptCore.Computational.PqxdhInitialBeaconAmbient.Ambient A N C)) (bounded : ∀ (reply : BeaconcryptCore.Computational.PqxdhInitialBuilderContext.BuildResult), @OracleComp.IsTotalQueryBound.{0} (Sum.{0, 0} (Sum.{0, 0} (Sum.{0, 0} (Sum.{0, 0} (@Sigma.{0, 0} (Fin S) fun (i : Fin S) => @OracleSpec.Domain.{0, 0} (Sum.{0, 0} (Prod.{0, 0} Pqxdh.Bytes Aeneas.Std.U64) Pqxdh.Bytes) BeaconcryptCore.Computational.RawCtxServerMixed.SourceSpec) (Sum.{0, 0} (@Sigma.{0, 0} (Fin B) fun (i : Fin B) => @OracleSpec.Domain.{0, 0} (Sum.{0, 0} Pqxdh.Bytes Pqxdh.Bytes) BeaconcryptCore.Computational.RawCtxMixedOwner.SourceSpec) (Sum.{0, 0} Nat (Sum.{0, 0} Pqxdh.Bytes BeaconcryptCore.Computational.PqxdhJointKdfGame.JointKdfViewQuery)))) (BeaconcryptCore.Computational.RawCtxProtocolReveals.Request S B)) ι) (BeaconcryptCore.Computational.PqxdhPhase2LiveFinish.Request B)) (@BeaconcryptCore.Computational.PqxdhInitialPostContext.PostSpec ι extra S B) Result (@BeaconcryptCore.Computational.PqxdhInitialNativeCarried.Execution.outside ι extra M P I D K Result Origin S B execution reply) qPost) (state : BeaconcryptCore.Computational.PqxdhInitialNativeLog.State A N C) (valid : @BeaconcryptCore.Computational.PqxdhInitialNativeRisk.Valid A N C depth k state) (clean : @BeaconcryptCore.Computational.PqxdhInitialNativeRisk.Clean A N C state), @LE.le.{0} ENNReal ENNReal.instLE (@probEvent.{0, 0} ProbComp (@BeaconcryptCore.Computational.PqxdhInitialNativeCarried.Carried ι extra M P I D K Result Origin A N C S B) (@instMonadLiftTOfMonadLift.{0, 0, 0, 0} ProbComp PMF.{0} SPMF.{0} SPMF.instMonadLiftPMF.{0} (@PFunctor.FreeM.instMonadLiftTPMF.{0, 0} (@OracleSpec.toPFunctor.{0, 0} Nat unifSpec) (@OracleSpec.IsUniformSpec.toIsProbabilitySpec.{0, 0} Nat unifSpec OracleSpec.instIsUniformSpecNatUnifSpec))) (@BeaconcryptCore.Computational.PqxdhInitialNativeCarried.carried ι M P I D K X Response Shared Result Origin A N C extra S B source writer mark sender route decode execution depth (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) depth (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) external state) fun (result : @BeaconcryptCore.Computational.PqxdhInitialNativeCarried.Carried ι extra M P I D K Result Origin A N C S B) => Not (@BeaconcryptCore.Computational.PqxdhInitialNativeRisk.Clean A N C (@Prod.snd.{0, 0} (@BeaconcryptCore.Computational.RawCtxPendingMixedPrefix.Stopped.{0} (Sum.{0, 0} (Sum.{0, 0} (Sum.{0, 0} (Sum.{0, 0} (BeaconcryptCore.Computational.RawCtxChainReceive.Kdf beaconcrypt_core.ratchet.RatchetChain beaconcrypt_core.ratchet.RatchetChain beaconcrypt_core.ratchet.RatchetMaterial BeaconcryptCore.Computational.RawCtxWholeOwner.OpenContext) (BeaconcryptCore.Computational.RawCtxInterpretedOpening.Opening beaconcrypt_core.ratchet.RatchetChain beaconcrypt_core.ratchet.RatchetChain beaconcrypt_core.ratchet.RatchetMaterial BeaconcryptCore.Computational.RawCtxWholeOwner.OpenContext)) (Sum.{0, 0} (Sum.{0, 0} (BeaconcryptCore.Computational.RawCtxChainSend.Kdf beaconcrypt_core.ratchet.RatchetChain beaconcrypt_core.ratchet.RatchetChain beaconcrypt_core.ratchet.RatchetMaterial BeaconcryptCore.Computational.RawCtxSourceSend.SealContext) (BeaconcryptCore.Computational.RawCtxChainSend.Seal beaconcrypt_core.ratchet.RatchetChain beaconcrypt_core.ratchet.RatchetChain beaconcrypt_core.ratchet.RatchetMaterial BeaconcryptCore.Computational.RawCtxSourceSend.SealContext)) (Sum.{0, 0} Nat (Sum.{0, 0} Pqxdh.Bytes BeaconcryptCore.Computational.PqxdhJointKdfGame.JointKdfViewQuery)))) (BeaconcryptCore.Computational.RawCtxGenericFamilyRead.ReadInput (BeaconcryptCore.Computational.RawCtxPendingFamilyLiveQueries.Kernel beaconcrypt_core.ratchet.RatchetChain) S B)) (Sum.{0, 0} (BeaconcryptCore.Computational.PqxdhBeaconPhase2Shared.Query I D K X Response Shared) (Sum.{0, 0} Response (Sum.{0, 0} (BeaconcryptCore.Computational.PqxdhBeaconPhase2Shared.Secrets Shared) (Sum.{0, 0} ι BeaconcryptCore.Computational.PqxdhServerRegistrationPublication.AuxQuery))))) (@BeaconcryptCore.Computational.PqxdhInitialPostContext.Base ι extra beaconcrypt_core.ratchet.RatchetChain I D K X Response Shared S B) (Prod.{0, 0} Result (Prod.{0, 0} (BeaconcryptCore.Computational.PqxdhInitialPostContext.NativeFront M P I D K S B) (BeaconcryptCore.Computational.PqxdhInitialOriginPost.Trace Origin S B)))) (BeaconcryptCore.Computational.PqxdhInitialNativeLog.State A N C) (@BeaconcryptCore.Computational.RawCtxForwardScan.pack.{0} (@BeaconcryptCore.Computational.PqxdhInitialOriginContext.Context ι extra M P I D K Result Origin S B) (Sum.{0, 0} (Sum.{0, 0} (Sum.{0, 0} (Sum.{0, 0} (BeaconcryptCore.Computational.RawCtxChainReceive.Kdf beaconcrypt_core.ratchet.RatchetChain beaconcrypt_core.ratchet.RatchetChain beaconcrypt_core.ratchet.RatchetMaterial BeaconcryptCore.Computational.RawCtxWholeOwner.OpenContext) (BeaconcryptCore.Computational.RawCtxInterpretedOpening.Opening beaconcrypt_core.ratchet.RatchetChain beaconcrypt_core.ratchet.RatchetChain beaconcrypt_core.ratchet.RatchetMaterial BeaconcryptCore.Computational.RawCtxWholeOwner.OpenContext)) (Sum.{0, 0} (Sum.{0, 0} (BeaconcryptCore.Computational.RawCtxChainSend.Kdf beaconcrypt_core.ratchet.RatchetChain beaconcrypt_core.ratchet.RatchetChain beaconcrypt_core.ratchet.RatchetMaterial BeaconcryptCore.Computational.RawCtxSourceSend.SealContext) (BeaconcryptCore.Computational.RawCtxChainSend.Seal beaconcrypt_core.ratchet.RatchetChain beaconcrypt_core.ratchet.RatchetChain beaconcrypt_core.ratchet.RatchetMaterial BeaconcryptCore.Computational.RawCtxSourceSend.SealContext)) (Sum.{0, 0} Nat (Sum.{0, 0} Pqxdh.Bytes BeaconcryptCore.Computational.PqxdhJointKdfGame.JointKdfViewQuery)))) (BeaconcryptCore.Computational.RawCtxGenericFamilyRead.ReadInput (BeaconcryptCore.Computational.RawCtxPendingFamilyLiveQueries.Kernel beaconcrypt_core.ratchet.RatchetChain) S B)) (Sum.{0, 0} (BeaconcryptCore.Computational.PqxdhBeaconPhase2Shared.Query I D K X Response Shared) (Sum.{0, 0} Response (Sum.{0, 0} (BeaconcryptCore.Computational.PqxdhBeaconPhase2Shared.Secrets Shared) (Sum.{0, 0} ι BeaconcryptCore.Computational.PqxdhServerRegistrationPublication.AuxQuery))))) (Prod.{0, 0} Result (Prod.{0, 0} (BeaconcryptCore.Computational.PqxdhInitialPostContext.NativeFront M P I D K S B) (BeaconcryptCore.Computational.PqxdhInitialOriginPost.Trace Origin S B))) (BeaconcryptCore.Computational.PqxdhInitialNativeLog.State A N C) (@BeaconcryptCore.Computational.PqxdhInitialPostContext.Base ι extra beaconcrypt_core.ratchet.RatchetChain I D K X Response Shared S B) (@BeaconcryptCore.Computational.PqxdhInitialOriginContext.frame ι M P I D K X Response Shared Result Origin extra S B mark sender route decode) result)))) (∑ j ∈ Finset.range (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7))) (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) qPost (@OfNat.ofNat.{0} Nat (nat_lit 67) (instOfNatNat (nat_lit 67))))), @HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal (@instHMul.{0} ENNReal (@Distrib.toMul.{0} ENNReal (@instDistribOfSemiring.{0} ENNReal (@CommSemiring.toSemiring.{0} ENNReal ENNReal.instCommSemiring)))) (@Nat.cast.{0} ENNReal (@AddMonoidWithOne.toNatCast.{0} ENNReal (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.instAddCommMonoidWithOne)) (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) k j) (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) (@Inv.inv.{0} ENNReal ENNReal.instInv (@HPow.hPow.{0, 0, 0} ENNReal Nat ENNReal (@instHPow.{0, 0} ENNReal Nat (@NPow.toPow.{0} ENNReal (@Monoid.toNPow.{0} ENNReal (@Semiring.toMonoid.{0} ENNReal (@CommSemiring.toSemiring.{0} ENNReal ENNReal.instCommSemiring))))) (@OfNat.ofNat.{0} ENNReal (nat_lit 2) (@instOfNatAtLeastTwo.{0} ENNReal (nat_lit 2) (@AddMonoidWithOne.toNatCast.{0} ENNReal (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.instAddCommMonoidWithOne)) (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))) (@OfNat.ofNat.{0} Nat (nat_lit 256) (instOfNatNat (nat_lit 256)))))) :=
  by simpa only [BeaconcryptCore.VCVioLegacy.probEvent_eq_prEvent] using @BeaconcryptCore.Computational.PqxdhInitialNativeRisk.carried_risk

def Cached : Carried extra M P I D K Result Origin A N C S B → Prop
  | .complete _ _ => False
  | .pending context state => state.1.1.2.1 (PqxdhInitialBuilderContext.address context.original) ≠ none

/-- The earliest actual cached predecessor is charged by the full source collision sum; no hit is discarded, resampled or granted a freshness premise. -/
theorem cached_risk (depth k qPost : Nat)
    (external : QueryImpl (External extra RatchetChain I D K X Response Shared) (Ambient A N C))
    (bounded : ∀ reply, (execution.outside reply).IsTotalQueryBound qPost)
    (state : State A N C) (valid : Valid depth k state) (clean : Clean state) :
    Pr{let x ← carried source writer mark sender route decode execution depth (depth + 1) external state}[Cached x] ≤
      ∑ j ∈ Finset.range (7 + qPost * 67), ((k + j + 1 : Nat) : ℝ≥0∞) * (2 ^ 256 : ℝ≥0∞)⁻¹ := by
  refine (prEvent_mono_of_support _ Cached (fun result => ¬Clean (RawCtxForwardScan.pack
      (PqxdhInitialOriginContext.frame (X := X) (Response := Response) mark sender route decode) result).2) ?_).trans
    (carried_risk source writer mark sender route decode execution depth k qPost external bounded state valid clean)
  intro result supported bad
  cases result with
  | complete value reached => exact False.elim bad
  | pending context reached =>
      have cases := carried_cases source writer mark sender route decode execution depth (depth + 1) external state reached valid.1 context supported
      have same : PqxdhInitialBuilderContext.address context.original = RawCtxSelectiveChainGame.cursorAddress reached.1.1.2.2 := by
        simpa only [RawCtxSelectiveChainGame.matched, decide_eq_true_eq] using cases.1
      change reached.1.1.2.1 (RawCtxSelectiveChainGame.cursorAddress reached.1.1.2.2) ≠ none
      rw [← same]
      exact bad

end Source

/-- The actual empty selective store starts clean independently of the retained initial chain and other private state. -/
theorem empty_clean (primitive : RawCtxSharedPrimitive.SharedState A) (cursor : RawCtxSelectiveChainGame.Cursor)
    (past : List JointKdfAddress) (privateState : N) (cache : C) :
    Clean (((primitive, ((fun _ => none), cursor)), past), (privateState, cache)) := rfl

end BeaconcryptCore.Computational.PqxdhInitialNativeRisk

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialNativeRisk.valid_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialNativeRisk.valid_step
/-- info: 'BeaconcryptCore.Computational.PqxdhInitialNativeRisk.callback_risk' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialNativeRisk.callback_risk
/-- info: 'BeaconcryptCore.Computational.PqxdhInitialNativeRisk.scan_risk' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialNativeRisk.scan_risk
/-- info: 'BeaconcryptCore.Computational.PqxdhInitialNativeRisk.source_risk' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialNativeRisk.source_risk
/-- info: 'BeaconcryptCore.Computational.PqxdhInitialNativeRisk.carried_risk' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialNativeRisk.carried_risk
/-- info: 'BeaconcryptCore.Computational.PqxdhInitialNativeRisk.cached_risk' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialNativeRisk.cached_risk
/-- info: 'BeaconcryptCore.Computational.PqxdhInitialNativeRisk.empty_clean' does not depend on any axioms -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialNativeRisk.empty_clean
