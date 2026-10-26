-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRecordFactsOriginSelectedGuess
import BeaconcryptCore.Computational.PqxdhRecordFactsOriginCandidateFlag

/-! The actual selected replay flag after an unconditioned failed writer. -/
open OracleComp OracleSpec ENNReal MeasureTheory ProbabilityTheory
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhRecordFactsOriginFailedFlag
open CtxRomAuth AdaptiveCtxReceive
open PqxdhRecordLiftWorldCompiler (Label)
open PqxdhRecordLiftIdeal (CtxPrivate KeyMode)
open PqxdhRecordLiftProtocol (ServiceSpec)
open PqxdhServerAuthExperiment (Setup Codec)
open PqxdhRecordFactsOriginSelectedSeal (hiddenResult)
open PqxdhRecordFactsOriginRawGuess (serviceCandidate)
open PqxdhRecordFactsOriginCandidateTrace (traced)
open PqxdhRecordFactsOriginMuteAdaptive (marked muted)
open PqxdhRecordFactsOriginSelectedGuess (Counted)
local instance (α : Type) : MeasurableSpace α := ⊤
local instance (α : Type) : DiscreteMeasurableSpace α := ⟨fun _ => trivial⟩
variable {n : Nat} {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response X : Type}
local instance : MeasurableSpace (CtxDigest × Option ((X × List CtxDigest) × CtxPrivate n)) := ⊤
local instance : DiscreteMeasurableSpace (CtxDigest × Option ((X × List CtxDigest) × CtxPrivate n)) := ⟨fun _ => trivial⟩

/-- Follow the exact original failed-writer branch and record every selected replay match in its complete adaptive continuation. -/
noncomputable def sampled (modes : Label n → KeyMode)
    (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (pending : PqxdhRecordLiftProtocol.Sealing n) (input : CtxSealInput)
    (body tag : Pqxdh.Bytes) (width : tag.length = 16) (state : CtxPrivate n)
    (client : OracleComp (ServiceSpec n) X) : ProbComp Bool := do
  let digest ← $ᵗ CtxDigest
  if (hiddenResult codec.frameWrite pending input body tag width digest state).1.isNone then
    let result ← (simulateQ (marked pending.material (RawCtxUniversalDecoder.decoder codec.frameRead)
      (muted pending.material modes replace setup codec)) client).run
        ((hiddenResult codec.frameWrite pending input body tag width digest state).2, false)
    pure result.2.2
  else pure false

/-- Literal selected hidden poststate satisfies the fixed-digest premise used by adaptive flag-to-candidate coverage. -/
theorem hidden_fixed (writer : RawCtxMixedShared.Writer)
    (pending : PqxdhRecordLiftProtocol.Sealing n) (input : CtxSealInput)
    (body tag : Pqxdh.Bytes) (width : tag.length = 16) (digest : CtxDigest) (state : CtxPrivate n)
    (empty : (state.keys pending.material).1.successfulSeals = []) :
    ∀ entry ∈ ((hiddenResult writer pending input body tag width digest state).2.keys pending.material).1.successfulSeals,
      entry.record.commit = digest := by
  rw [PqxdhRecordFactsOriginSelectedGuess.hidden_dictionary writer pending input body tag width digest state empty]
  simp only [List.mem_singleton, forall_eq]


/-- Actual selected replay matches after the literal failed writer are covered by the complete public candidate trace, without resampling or conditioning the digest. -/
theorem sampled_le_trace (modes : Label n → KeyMode)
    (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (pending : PqxdhRecordLiftProtocol.Sealing n) (input : CtxSealInput)
    (body tag : Pqxdh.Bytes) (width : tag.length = 16) (state : CtxPrivate n)
    (empty : (state.keys pending.material).1.successfulSeals = [])
    (client : OracleComp (ServiceSpec n) X)
    (noSeal : client.IsQueryBoundP (PqxdhRecordFactsOriginMuteServices.IsTargetSealing pending.material) 0) :
    𝒟[sampled modes setup codec replace pending input body tag width state client] {flag | flag = true} ≤
    𝒟[PqxdhRecordFactsOriginFailedGuess.experiment modes setup codec replace pending input body tag width state
      (traced (serviceCandidate codec.frameRead) client [])]
      {result | ∃ value, result.2 = some value ∧ result.1 ∈ value.1.2} := by
  simp only [sampled, PqxdhRecordFactsOriginFailedGuess.experiment]
  rw [← prEvent_eq_evalDist_of_discrete, ← prEvent_eq_evalDist_of_discrete]
  simp only [OracleComp.prEvent_bind_eq_tsum]
  refine ENNReal.tsum_le_tsum fun digest => mul_le_mul_right ?_ _
  split_ifs
  · rw [PqxdhRecordFactsOriginFailedGuess.continuation, bind_map_left, bind_pure_comp (β := Bool),
      bind_pure_comp (β := CtxDigest × Option _), prEvent_map, prEvent_map]
    simp only [Option.some.injEq, exists_eq_left', Prod.map, id_eq]
    have flag := PqxdhRecordFactsOriginCandidateFlag.flag_probability pending.material modes codec.frameRead
      setup.source.crypto (PqxdhRecordFactsPrivateCacheWorld.baseInterpreter setup codec) codec.frameWrite replace
      client noSeal (hiddenResult codec.frameWrite pending input body tag width digest state).2 digest
      (hidden_fixed codec.frameWrite pending input body tag width digest state empty)
    rw [← @prEvent_eq_evalDist_of_discrete _ _ _ _ _ _ PqxdhRecordFactsOriginCandidateFlag.instMeasurableSpaceProdCtxPrivateBool
        PqxdhRecordFactsOriginCandidateFlag.instDiscreteMeasurableSpaceProdCtxPrivateBool,
      ← @prEvent_eq_evalDist_of_discrete _ _ _ _ _ _ PqxdhRecordFactsOriginCandidateFlag.instMeasurableSpaceProdCtxPrivate
        PqxdhRecordFactsOriginCandidateFlag.instDiscreteMeasurableSpaceProdCtxPrivate] at flag
    exact flag
  · simp only [prEvent_pure, Bool.false_eq_true, ite_false, zero_le]


-- Composing these exact measure bounds normalizes the concrete 64-byte draw.
set_option maxRecDepth 1024 in
/-- The literal selected failed-writer replay flag costs at most two uniform point masses per original raw receive allowance. -/
theorem sampled_bound (modes : Label n → KeyMode)
    (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (pending : PqxdhRecordLiftProtocol.Sealing n) (input : CtxSealInput)
    (body tag : Pqxdh.Bytes) (width : tag.length = 16) (state : CtxPrivate n)
    (empty : (state.keys pending.material).1.successfulSeals = [])
    (client : OracleComp (ServiceSpec n) X)
    (noSeal : client.IsQueryBoundP (PqxdhRecordFactsOriginMuteServices.IsTargetSealing pending.material) 0)
    (cap : Nat) (bound : client.IsQueryBoundP Counted cap) :
    𝒟[sampled modes setup codec replace pending input body tag width state client] {flag | flag = true} ≤
      2 * cap * ((2 ^ 512 : Nat) : ℝ≥0∞)⁻¹ :=
  (sampled_le_trace modes setup codec replace pending input body tag width state empty client noSeal).trans
    (PqxdhRecordFactsOriginSelectedGuess.failed_trace_bound modes setup codec replace pending input body tag width
      state client noSeal cap bound)


/-- The same original selected failed-writer experiment with every actual erased-source reply returned to its adaptive continuation. -/
noncomputable def sampledErased (modes : Label n → KeyMode)
    (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (pending : PqxdhRecordLiftProtocol.Sealing n) (input : CtxSealInput)
    (body tag : Pqxdh.Bytes) (width : tag.length = 16) (state : CtxPrivate n)
    (client : OracleComp (ServiceSpec n) X) : ProbComp Bool := do
  let digest ← $ᵗ CtxDigest
  if (hiddenResult codec.frameWrite pending input body tag width digest state).1.isNone then
    let result ← (simulateQ (marked pending.material (RawCtxUniversalDecoder.decoder codec.frameRead)
      (PqxdhRecordFactsPrivateCacheWorld.erased modes replace setup codec)) client).run
        ((hiddenResult codec.frameWrite pending input body tag width digest state).2, false)
    pure result.2.2
  else pure false

/-- The exact adaptive comparison transports the selected match probability without adding any second bad-event term. -/
theorem sampled_probability (modes : Label n → KeyMode)
    (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (pending : PqxdhRecordLiftProtocol.Sealing n) (input : CtxSealInput)
    (body tag : Pqxdh.Bytes) (width : tag.length = 16) (state : CtxPrivate n)
    (client : OracleComp (ServiceSpec n) X) :
    𝒟[sampledErased modes setup codec replace pending input body tag width state client] {flag | flag = true} =
      𝒟[sampled modes setup codec replace pending input body tag width state client] {flag | flag = true} := by
  simp only [sampledErased, sampled]
  rw [← prEvent_eq_evalDist_of_discrete, ← prEvent_eq_evalDist_of_discrete]
  simp only [OracleComp.prEvent_bind_eq_tsum]
  apply tsum_congr
  intro digest
  refine congrArg (HMul.hMul _) ?_
  split_ifs
  · rw [bind_pure_comp (β := Bool), bind_pure_comp (β := Bool), prEvent_map, prEvent_map]
    have bad := (PqxdhRecordFactsOriginMuteAdaptive.source_bad_probability pending.material modes replace setup codec
      client (hiddenResult codec.frameWrite pending input body tag width digest state).2).symm
    rw [← @prEvent_eq_evalDist_of_discrete _ _ _ _ _ _ PqxdhRecordFactsOriginMuteAdaptive.instMeasurableSpaceProdCtxPrivateBool
        PqxdhRecordFactsOriginMuteAdaptive.instDiscreteMeasurableSpaceProdCtxPrivateBool,
      ← @prEvent_eq_evalDist_of_discrete _ _ _ _ _ _ PqxdhRecordFactsOriginMuteAdaptive.instMeasurableSpaceProdCtxPrivateBool
        PqxdhRecordFactsOriginMuteAdaptive.instDiscreteMeasurableSpaceProdCtxPrivateBool] at bad
    exact bad
  · rfl


/-- The actual adaptive erased-source replay flag after the failed selected writer has the same coefficient-two raw-query bound. -/
theorem sampled_erased_bound (modes : Label n → KeyMode)
    (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (pending : PqxdhRecordLiftProtocol.Sealing n) (input : CtxSealInput)
    (body tag : Pqxdh.Bytes) (width : tag.length = 16) (state : CtxPrivate n)
    (empty : (state.keys pending.material).1.successfulSeals = [])
    (client : OracleComp (ServiceSpec n) X)
    (noSeal : client.IsQueryBoundP (PqxdhRecordFactsOriginMuteServices.IsTargetSealing pending.material) 0)
    (cap : Nat) (bound : client.IsQueryBoundP Counted cap) :
    𝒟[sampledErased modes setup codec replace pending input body tag width state client] {flag | flag = true} ≤
      2 * cap * ((2 ^ 512 : Nat) : ℝ≥0∞)⁻¹ := by
  rw [sampled_probability]
  exact sampled_bound modes setup codec replace pending input body tag width state empty client noSeal cap bound

end BeaconcryptCore.Computational.PqxdhRecordFactsOriginFailedFlag

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginFailedFlag.hidden_fixed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginFailedFlag.hidden_fixed
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginFailedFlag.sampled_le_trace' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginFailedFlag.sampled_le_trace
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginFailedFlag.sampled_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginFailedFlag.sampled_bound
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginFailedFlag.sampled_probability' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginFailedFlag.sampled_probability
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginFailedFlag.sampled_erased_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginFailedFlag.sampled_erased_bound
