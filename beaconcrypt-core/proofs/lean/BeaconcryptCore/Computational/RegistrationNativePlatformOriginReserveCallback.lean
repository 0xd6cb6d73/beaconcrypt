-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformOriginReserveTailGuess
import BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryExperiment
import BeaconcryptCore.Computational.PqxdhRecordFactsOriginFailedCallback
/-! The actual selected seal and post-send source reserve retain the original replay-match probability. Body/tag sampling, codec refusal, charged reserve errors and all platform poststates are preserved under the existing explicitly normalized uniform instrumentation. -/
open OracleComp OracleSpec CoreModels Aeneas ENNReal MeasureTheory ProbabilityTheory
open Aeneas.Std hiding namespace core alloc
open beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformOriginReserveCallback
open CtxRomAuth
open PqxdhRecordLiftIdeal (CtxPrivate KeyMode)
open PqxdhRecordLiftWorldCompiler (Label)
open PqxdhRecordLiftProtocol (ServiceSpec)
open PqxdhServerAuthExperiment (Setup Codec)
open PqxdhRecordFactsOriginSelectedSeal (hiddenResult)
open PqxdhRecordFactsOriginMuteServices (IsTargetSealing)
open PqxdhRecordFactsOriginMuteAdaptive (marked muted)
open RegistrationNativePlatformOriginReserveSourceGuess (tail fixed)
variable {n : Nat} {I KemSK Reader Response X Platform Failure : Type} {base : OracleSpec I}
local instance (T : Type) : MeasurableSpace T := ⊤
local instance (T : Type) : DiscreteMeasurableSpace T := ⟨fun _ => trivial⟩
local instance : MeasurableSpace (((Option (X × Platform)) × CtxPrivate n) × Bool) := ⊤
local instance : DiscreteMeasurableSpace (((Option (X × Platform)) × CtxPrivate n) × Bool) := ⟨fun _ => trivial⟩
local instance : MeasurableSpace (CtxDigest × (((Option (X × Platform)) × List CtxDigest) × CtxPrivate n)) := ⊤
local instance : DiscreteMeasurableSpace (CtxDigest × (((Option (X × Platform)) × List CtxDigest) × CtxPrivate n)) := ⟨fun _ => trivial⟩
variable (reserve : Nat → StateT Platform ProbComp (core.result.Result Unit Failure))
    (future : Platform → OracleComp (ServiceSpec n) X) (before : Platform)
    (tag : PqxdhDeploymentInterface.FrameTag)
    (modes : Label n → KeyMode) (setup : Setup base KemSK) (codec : Codec Reader Response)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (pending : PqxdhRecordLiftProtocol.Sealing n) (input : CtxSealInput)
    (body bytesTag : Pqxdh.Bytes) (width : bytesTag.length=16) (state : CtxPrivate n)

noncomputable def sampled (erased : Bool) : ProbComp Bool := do
  let digest ← $ᵗ CtxDigest
  let service := if erased then PqxdhRecordFactsPrivateCacheWorld.erased modes replace setup codec
    else muted pending.material modes replace setup codec
  let result ← (simulateQ (marked pending.material (RawCtxUniversalDecoder.decoder codec.frameRead) service)
    (tail reserve future before tag (hiddenResult codec.frameWrite pending input body bytesTag width digest state).1)).run
    ((hiddenResult codec.frameWrite pending input body bytesTag width digest state).2,false)
  pure result.2.2

/-- The original source and its muted comparison have the identical match probability through the actual charged reserve tail; no additional bad event is paid. -/
theorem sampled_probability :
    𝒟[sampled reserve future before tag modes setup codec replace pending input body bytesTag width state true] {flag | flag=true} =
      𝒟[sampled reserve future before tag modes setup codec replace pending input body bytesTag width state false] {flag | flag=true} := by
  unfold sampled
  simp only [Bool.false_eq_true,ite_true,ite_false]
  rw [←prEvent_eq_evalDist_of_discrete,←prEvent_eq_evalDist_of_discrete]
  conv_lhs => rw [OracleComp.prEvent_bind_eq_tsum]
  conv_rhs => rw [OracleComp.prEvent_bind_eq_tsum]
  apply tsum_congr
  intro digest
  refine congrArg (HMul.hMul _) ?_
  rw [bind_pure_comp (β := Bool),bind_pure_comp (β := Bool),prEvent_map,prEvent_map]
  have bad := (PqxdhRecordFactsOriginMuteAdaptive.source_bad_probability pending.material modes replace setup codec
    (tail reserve future before tag (hiddenResult codec.frameWrite pending input body bytesTag width digest state).1)
    (hiddenResult codec.frameWrite pending input body bytesTag width digest state).2).symm
  rw [← @prEvent_eq_evalDist_of_discrete _ _ _ _ _ _ PqxdhRecordFactsOriginMuteAdaptive.instMeasurableSpaceProdCtxPrivateBool
      PqxdhRecordFactsOriginMuteAdaptive.instDiscreteMeasurableSpaceProdCtxPrivateBool,
    ← @prEvent_eq_evalDist_of_discrete _ _ _ _ _ _ PqxdhRecordFactsOriginMuteAdaptive.instMeasurableSpaceProdCtxPrivateBool
      PqxdhRecordFactsOriginMuteAdaptive.instDiscreteMeasurableSpaceProdCtxPrivateBool] at bad
  exact bad

private theorem tail_eq_fixed (reply : Option RawCtxSourceSend.Encrypted) (amount : Nat)
    (sized : ∀value,reply=some value → value.ciphertext.length=amount) :
    tail reserve future before tag reply=fixed reserve future before tag amount reply.isNone := by
  unfold tail fixed
  apply bind_congr
  intro _
  cases reply with
  | none => simp only [RegistrationNativePlatformOrdinaryGate.gate,StateT.run_pure,simulateQ_pure,pure_bind,Option.isNone_none,ite_true]
  | some value =>
    simp only [RegistrationNativePlatformOrdinaryGate.gate,StateT.run_bind,simulateQ_bind,
      Option.isNone_some,Bool.false_eq_true,ite_false,sized value rfl,bind_assoc]
    apply bind_congr
    intro allocated
    cases allocated.1 <;> simp only [StateT.run_pure,simulateQ_pure,pure_bind,Option.isNone_none,Option.isNone_some,Bool.false_eq_true,ite_false,ite_true]

/-- Every replay match in that same original tail is covered by an actual public raw candidate in its same complete source continuation. -/
theorem sampled_le_trace (amount : Nat)
    (sized : ∀digest value,(hiddenResult codec.frameWrite pending input body bytesTag width digest state).1=some value → value.ciphertext.length=amount)
    (empty : (state.keys pending.material).1.successfulSeals=[])
    (noSeal : ∀absent,(fixed reserve future before tag amount absent).IsQueryBoundP (IsTargetSealing pending.material) 0) :
    𝒟[sampled reserve future before tag modes setup codec replace pending input body bytesTag width state false] {flag | flag=true} ≤
      𝒟[RegistrationNativePlatformOriginReserveTailGuess.experiment reserve future before tag modes setup codec replace pending input body bytesTag width state]
        {result | result.1 ∈ result.2.1.2} := by
  unfold sampled RegistrationNativePlatformOriginReserveTailGuess.experiment
  simp only [Bool.false_eq_true,ite_false]
  rw [←prEvent_eq_evalDist_of_discrete,←prEvent_eq_evalDist_of_discrete]
  conv_lhs => rw [OracleComp.prEvent_bind_eq_tsum]
  conv_rhs => rw [OracleComp.prEvent_bind_eq_tsum]
  refine ENNReal.tsum_le_tsum fun digest => mul_le_mul_right ?_ _
  rw [bind_pure_comp (β := Bool),bind_pure_comp (β := CtxDigest × _),prEvent_map,prEvent_map]
  have flag := PqxdhRecordFactsOriginCandidateFlag.flag_probability pending.material modes codec.frameRead
    setup.source.crypto (PqxdhRecordFactsPrivateCacheWorld.baseInterpreter setup codec) codec.frameWrite replace
    (tail reserve future before tag (hiddenResult codec.frameWrite pending input body bytesTag width digest state).1)
    (by rw [tail_eq_fixed reserve future before tag _ amount (sized digest)];exact noSeal _)
    (hiddenResult codec.frameWrite pending input body bytesTag width digest state).2 digest
    (PqxdhRecordFactsOriginFailedFlag.hidden_fixed codec.frameWrite pending input body bytesTag width digest state empty)
  rw [← @prEvent_eq_evalDist_of_discrete _ _ _ _ _ _ PqxdhRecordFactsOriginCandidateFlag.instMeasurableSpaceProdCtxPrivateBool
      PqxdhRecordFactsOriginCandidateFlag.instDiscreteMeasurableSpaceProdCtxPrivateBool,
    ← @prEvent_eq_evalDist_of_discrete _ _ _ _ _ _ PqxdhRecordFactsOriginCandidateFlag.instMeasurableSpaceProdCtxPrivate
      PqxdhRecordFactsOriginCandidateFlag.instDiscreteMeasurableSpaceProdCtxPrivate] at flag
  rw [prEvent_map]
  simpa only [Prod.map,id_eq] using flag

/-- The selected source match probability includes both encoder absence and real reserve refusal, with exact platform state, the named uniform-instrumentation projection and the same coefficient-two raw allowance. -/
theorem sampled_bound (amount : Nat)
    (sized : ∀digest value,(hiddenResult codec.frameWrite pending input body bytesTag width digest state).1=some value → value.ciphertext.length=amount)
    (empty : (state.keys pending.material).1.successfulSeals=[])
    (noSeal : ∀absent,(fixed reserve future before tag amount absent).IsQueryBoundP (IsTargetSealing pending.material) 0)
    (cap : Nat) (bounded : ∀absent,(fixed reserve future before tag amount absent).IsQueryBoundP
      (fun query => PqxdhRecordLiftCtxProtocolBounds.categoryCost .raw query=1) cap) :
    𝒟[sampled reserve future before tag modes setup codec replace pending input body bytesTag width state true] {flag | flag=true} ≤
      2*cap*((2^512 : Nat) : ℝ≥0∞)⁻¹ := by
  rw [sampled_probability]
  exact (sampled_le_trace reserve future before tag modes setup codec replace pending input body bytesTag width state amount sized empty noSeal).trans
    (RegistrationNativePlatformOriginReserveTailGuess.trace_bound reserve future before tag modes setup codec replace pending input body bytesTag width state amount sized noSeal cap bounded)
noncomputable def callback : ProbComp Bool := do
  let reply ← (PqxdhRecordFactsPrivateCacheWorld.erased modes replace setup codec (.sealing pending)).run state
  let result ← (simulateQ (marked pending.material (RawCtxUniversalDecoder.decoder codec.frameRead)
    (PqxdhRecordFactsPrivateCacheWorld.erased modes replace setup codec))
    (tail reserve future before tag reply.1)).run (reply.2,false)
  pure result.2.2

/-- The literal selected source callback averages its actual ordered body/tag/digest draws and every admission failure before charging the same coefficient-two raw allowance. -/
theorem callback_bound (ideal : modes pending.material≠.real)
    (fresh : PqxdhRecordFactsPrivateCacheSource.FreshPoint state (.sealing pending))
    (empty : (state.keys pending.material).1.successfulSeals=[])
    (amount : Pqxdh.Bytes → Nat)
    (sized : ∀input body bytesTag (width : bytesTag.length=16) digest value,
      (hiddenResult codec.frameWrite pending input body bytesTag width digest state).1=some value → value.ciphertext.length=amount body)
    (noSeal : ∀body absent,(fixed reserve future before tag (amount body) absent).IsQueryBoundP (IsTargetSealing pending.material) 0)
    (cap : Nat) (bounded : ∀body absent,(fixed reserve future before tag (amount body) absent).IsQueryBoundP
      (fun query => PqxdhRecordLiftCtxProtocolBounds.categoryCost .raw query=1) cap) :
    𝒟[callback reserve future before tag modes setup codec replace pending state] {flag | flag=true} ≤
      2*cap*((2^512 : Nat) : ℝ≥0∞)⁻¹ := by
  simp only [callback,PqxdhRecordFactsOriginSelectedSeal.source_sampler modes replace setup codec pending state ideal fresh,
    PqxdhRecordFactsOriginSelectedSeal.hiddenSampler]
  split
  · split
    · simp only [bind_assoc,pure_bind]
      rw [←prEvent_eq_evalDist_of_discrete]
      refine prEvent_bind_le_of_forall_le_of_support _ _ _ fun body _ =>
        prEvent_bind_le_of_forall_le_of_support _ _ _ fun bytesTag _ => ?_
      rw [prEvent_eq_evalDist_of_discrete]
      simpa only [sampled,ite_true] using sampled_bound reserve future before tag modes setup codec replace pending _
        body.toList bytesTag.toList bytesTag.toList_length state (amount body.toList)
        (sized _ _ _ _) empty (noSeal body.toList) cap (bounded body.toList)
    · simpa only [sampled,ite_true,bind_assoc,pure_bind] using sampled_bound reserve future before tag modes setup codec replace pending _
        _ _ (setup.source.crypto.aeadSeal_tag_length _ _ _ _) state (amount _)
        (sized _ _ _ _) empty (noSeal _) cap (bounded _)
  · simp only [pure_bind,bind_pure_comp]
    rw [←prEvent_eq_evalDist_of_discrete,prEvent_map]
    have no : (tail reserve future before tag none).IsQueryBoundP (IsTargetSealing pending.material) 0 := by
      rw [tail_eq_fixed reserve future before tag none (amount []) (by intro value impossible;cases impossible)]
      exact noSeal [] true
    have zero := PqxdhRecordFactsOriginEmpty.erased_probability pending.material modes setup codec replace
      (tail reserve future before tag none) no state empty
    rw [← @prEvent_eq_evalDist_of_discrete _ _ _ _ _ _
      PqxdhRecordFactsOriginEmpty.instMeasurableSpaceProdCtxPrivateBool
      PqxdhRecordFactsOriginEmpty.instDiscreteMeasurableSpaceProdCtxPrivateBool] at zero
    exact (le_of_eq zero).trans zero_le

private theorem canonical_size (selected : PqxdhRecordLiftProtocol.Sealing n) (plain : CtxSealInput)
    (body tag : Pqxdh.Bytes) (width : tag.length=16) (digest : CtxDigest) (state : CtxPrivate n)
    (value : RawCtxSourceSend.Encrypted)
    (encoded : (hiddenResult CborRawCanonicalBuild.canonicalWriter selected plain body tag width digest state).1=some value) :
    value.ciphertext.length=RegistrationNativePlatformOriginReserveWidth.amount selected body := by
  let frame : RawCtxReceive.DecodedFrame := ⟨selected.sequence,selected.context.senderId,(⟨body,tag,width,digest⟩ : CtxRomRecord).encode⟩
  have payload : frame.payload.length=body.length+80 := by
    simp only [frame,CtxRomRecord.encode,CtxRomRecord.toRecordCipher,Pqxdh.RecordCipher.encode,
      List.length_append,width,ctxDigest_toList_length]
  change (CborRawCanonicalBuild.canonicalWriter frame).map
    (fun ciphertext => (⟨ciphertext,selected.context.targetId,selected.sequence⟩ : RawCtxSourceSend.Encrypted))=some value at encoded
  rw [Option.map_eq_some_iff] at encoded
  obtain ⟨bytes,written,rfl⟩ := encoded
  unfold CborRawCanonicalBuild.canonicalWriter at written
  split at written
  · rename_i admitted
    have same := Option.some.inj written
    subst bytes
    have representable : frame.payload.length<2^64 := by
      unfold CborSizing.frameLen CborSizing.byteStringLen CborSizing.maxMessageSize at admitted
      omega
    have size := CborTransport.render_length frame representable
    simpa only [RegistrationNativePlatformOriginReserveWidth.amount,payload,frame] using size
  · cases written

/-- At the exact concrete source frame codec, successful serialization supplies the only length fact internally. Public writer/reserve failures and their actual states remain in the same selected callback. -/
theorem concrete_bound
    (ideal : modes pending.material≠.real)
    (fresh : PqxdhRecordFactsPrivateCacheSource.FreshPoint state (.sealing pending))
    (empty : (state.keys pending.material).1.successfulSeals=[])
    (noSeal : ∀body absent,(fixed reserve future before tag (RegistrationNativePlatformOriginReserveWidth.amount pending body) absent).IsQueryBoundP (IsTargetSealing pending.material) 0)
    (cap : Nat) (bounded : ∀body absent,(fixed reserve future before tag (RegistrationNativePlatformOriginReserveWidth.amount pending body) absent).IsQueryBoundP
      (fun query => PqxdhRecordLiftCtxProtocolBounds.categoryCost .raw query=1) cap) :
    𝒟[callback reserve future before tag modes setup
      (RegistrationNativeWire.ledgerCodec (RegistrationNativePlatformOrdinaryExperiment.canonicalWire RegistrationNativePlatformConcreteSource.wire))
      replace pending state] {flag | flag=true} ≤ 2*cap*((2^512 : Nat) : ℝ≥0∞)⁻¹ := by
  exact callback_bound reserve future before tag modes setup _ replace pending state ideal fresh empty
    (RegistrationNativePlatformOriginReserveWidth.amount pending)
    (fun plain body tag width digest value => canonical_size pending plain body tag width digest state value) noSeal cap bounded

end BeaconcryptCore.Computational.RegistrationNativePlatformOriginReserveCallback

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOriginReserveCallback.sampled_probability' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOriginReserveCallback.sampled_probability

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOriginReserveCallback.sampled_le_trace' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOriginReserveCallback.sampled_le_trace

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOriginReserveCallback.sampled_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOriginReserveCallback.sampled_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOriginReserveCallback.callback_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOriginReserveCallback.callback_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOriginReserveCallback.concrete_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOriginReserveCallback.concrete_bound
