-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformOriginSourceSendSyntax
import BeaconcryptCore.Computational.RegistrationNativePlatformOriginGivenReserveBound
import BeaconcryptCore.Computational.RegistrationNativePlatformOriginCallbackProbability
import BeaconcryptCore.Computational.RegistrationNativePlatformOriginReplyJointObservation
open OracleComp OracleSpec CoreModels Aeneas ENNReal MeasureTheory ProbabilityTheory
open Aeneas.Std hiding namespace core alloc
open beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1800000
namespace BeaconcryptCore.Computational.RegistrationNativePlatformOriginSourceFormBound
open PqxdhRecordLiftProtocol (ServiceSpec)
open PqxdhRecordLiftIdeal (CtxPrivate KeyMode)
open PqxdhRecordLiftWorldCompiler (Label)
open PqxdhServerAuthExperiment (Setup Codec)
open PqxdhRecordFactsOriginOrdinalPath (Prefix)
open RegistrationNativePlatformOriginSourceSendSyntax (Form Reply)
open RegistrationNativePlatformOriginReserveContinuationBound (continued)
variable {n : Nat} {I KemSK Platform Failure Reader Response A X : Type} {base : OracleSpec I}
local instance (T : Type) : MeasurableSpace T := ⊤
local instance (T : Type) : DiscreteMeasurableSpace T := ⟨fun _=>trivial⟩
noncomputable local instance (p : Prop) : Decidable p:=Classical.propDecidable p
abbrev Joint (n : Nat) (A X : Type) := (A × CtxPrivate n) × (X × CtxPrivate n)
local instance : MeasurableSpace (Joint n A X) := ⊤
local instance : DiscreteMeasurableSpace (Joint n A X) := ⟨fun _=>trivial⟩

local instance : MeasurableSpace (Joint n A X × Bool) := ⊤
local instance : DiscreteMeasurableSpace (Joint n A X × Bool) := ⟨fun _=>trivial⟩
local instance : MeasurableSpace ((X × CtxPrivate n) × Bool) := ⊤
local instance : DiscreteMeasurableSpace ((X × CtxPrivate n) × Bool) := ⟨fun _=>trivial⟩

noncomputable def run (service : QueryImpl (ServiceSpec n) (StateT (CtxPrivate n) ProbComp))
    (body : OracleComp (ServiceSpec n) A) (future : A → OracleComp (ServiceSpec n) X) (before : CtxPrivate n) :
    ProbComp (Joint n A X) := do
  let current←(simulateQ service body).run before
  let final←(simulateQ service (future current.1)).run current.2
  pure (current,final)

def Acquired (before after : CtxPrivate n) (label : Label n) : Prop :=
  ∃entry,entry∉(before.keys label).1.successfulSeals ∧entry∈(after.keys label).1.successfulSeals

def Bad (read : A → Reply) (accepts : Label n → X × CtxPrivate n → Prop)
    (before : CtxPrivate n) (result : Joint n A X) : Prop :=
  read result.1.1=none ∧∃label,Acquired before result.1.2 label ∧accepts label result.2

/-- The full callback coin prefix keeps every private seal coordinate at its actual reached state. -/
theorem coin_keys (modes : Label n → KeyMode) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (setup : Setup base KemSK) (codec : Codec Reader Response) (amount : Nat)
    (before : CtxPrivate n) (result : Fin (amount+1) × CtxPrivate n)
    (supported : result∈support ((simulateQ (PqxdhRecordFactsPrivateCacheWorld.erased modes replace setup codec)
      (RegistrationNativePlatformOriginGateSource.coins amount)).run before)) : result.2.keys=before.keys := by
  apply RegistrationNativePlatformOriginErasedFields.program modes replace setup codec _ _ before result supported
  simp only [RegistrationNativePlatformOriginGateSource.coins,allQueriesSatisfy_query_bind_iff]
  exact ⟨by trivial,fun _=>(allQueriesSatisfy_query_iff _ _).mpr (by trivial)⟩

/-- A supported original callback coin prefix reaches its same continuation without adding a seal cut. -/
theorem coin_prefix (service : QueryImpl (ServiceSpec n) (StateT (CtxPrivate n) ProbComp))
    (initial : OracleComp (ServiceSpec n) X) (start : CtxPrivate n) (past0 : List (Label n))
    (amount : Nat) (next : Fin (amount+1) → OracleComp (ServiceSpec n) X)
    (before : CtxPrivate n) (past : List (Label n)) (cuts : List (PqxdhRecordFactsOriginOrdinalCut.Cut n X))
    (beforePrefix : Prefix service initial start past0 (RegistrationNativePlatformOriginGateSource.coins amount >>=next) before past cuts)
    (result : Fin (amount+1) × CtxPrivate n)
    (supported : result∈support ((simulateQ service (RegistrationNativePlatformOriginGateSource.coins amount)).run before)) :
    Prefix service initial start past0 (next result.1) result.2 past cuts := by
  simp only [RegistrationNativePlatformOriginGateSource.coins,bind_assoc] at beforePrefix
  simp only [RegistrationNativePlatformOriginGateSource.coins,simulateQ_bind,simulateQ_spec_query,StateT.run_bind,
    mem_support_bind_iff] at supported
  obtain ⟨charged,called,continued⟩ :=supported
  have first:=Prefix.step beforePrefix called
  have second:=Prefix.step first continued
  simpa only [PqxdhRecordLiftWorldProvenance.sealingCoordinates,PqxdhRecordFactsOriginOrdinalPath.cutAt,
    List.append_nil] using second

/-- A no-seal sending callback contributes zero to the newly-acquired, publicly refused callback event. -/
theorem quiet_bound (modes : Label n → KeyMode) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (setup : Setup base KemSK) (codec : Codec Reader Response) (read : A → Reply)
    (accepts : Label n → X × CtxPrivate n → Prop) (body : OracleComp (ServiceSpec n) A)
    (quiet : body.AllQueriesSatisfy RegistrationNativePlatformOriginErasedFields.BaseOnly)
    (future : A → OracleComp (ServiceSpec n) X) (before : CtxPrivate n) :
    𝒟[run (PqxdhRecordFactsPrivateCacheWorld.erased modes replace setup codec) body future before]
      {result|Bad read accepts before result} =0 := by
  apply le_antisymm ?_ bot_le
  calc
    _ ≤ 𝒟[run (PqxdhRecordFactsPrivateCacheWorld.erased modes replace setup codec) body future before] (∅) := by
      apply measure_mono_ae
      apply OracleComp.ae_evalDist_of_forall_mem_support
      intro result supported bad
      simp only [run,mem_support_bind_iff,mem_support_pure_iff] at supported
      obtain ⟨current,called,final,_continued,rfl⟩ :=supported
      obtain ⟨_refused,label,acquired,_accepted⟩ :=bad
      obtain ⟨entry,absent,present⟩ :=acquired
      have kept:=RegistrationNativePlatformOriginErasedFields.program modes replace setup codec body quiet before current called
      exact False.elim (absent (kept ▸ present))
    _=0:=measure_empty
/-- The original experiment coin prefix is averaged before any reply-dependent send branch; it adds no attempted-send or label factor. -/
theorem coin_bound (modes : Label n → KeyMode) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (setup : Setup base KemSK) (codec : Codec Reader Response) (read : A → Reply)
    (accepts : Label n → X × CtxPrivate n → Prop) (amount : Nat)
    (next : Fin (amount+1) → OracleComp (ServiceSpec n) A) (future : A → OracleComp (ServiceSpec n) X)
    (before : CtxPrivate n) (cap : ℝ≥0∞)
    (later : ∀result∈support ((simulateQ (PqxdhRecordFactsPrivateCacheWorld.erased modes replace setup codec)
        (RegistrationNativePlatformOriginGateSource.coins amount)).run before),
      𝒟[run (PqxdhRecordFactsPrivateCacheWorld.erased modes replace setup codec) (next result.1) future result.2]
        {output|Bad read accepts result.2 output}≤cap) :
    𝒟[run (PqxdhRecordFactsPrivateCacheWorld.erased modes replace setup codec)
        (RegistrationNativePlatformOriginGateSource.coins amount >>=next) future before]
      {result|Bad read accepts before result}≤cap := by
  have equal : run (PqxdhRecordFactsPrivateCacheWorld.erased modes replace setup codec)
      (RegistrationNativePlatformOriginGateSource.coins amount >>=next) future before=
      (do let result←(simulateQ (PqxdhRecordFactsPrivateCacheWorld.erased modes replace setup codec)
            (RegistrationNativePlatformOriginGateSource.coins amount)).run before
          run (PqxdhRecordFactsPrivateCacheWorld.erased modes replace setup codec) (next result.1) future result.2) := by
    simp only [run,simulateQ_bind,StateT.run_bind,bind_assoc]
  rw [equal]
  let : MeasurableSpace (unifSpec.Range amount × CtxPrivate n) := ⊤
  let : DiscreteMeasurableSpace (unifSpec.Range amount × CtxPrivate n) := ⟨fun _=>trivial⟩
  apply PqxdhRecordFactsOriginAverage.bind_le
  intro result supported
  have kept:=coin_keys modes replace setup codec amount before result supported
  convert later result supported using 1
  congr 1
  ext output
  simp only [Bad,Acquired,kept]

private theorem coins_base {Y : Type} (work : ProbComp Y) :
    (simulateQ (RegistrationNativePlatformOriginGateSource.coins (n := n)) work).AllQueriesSatisfy
      RegistrationNativePlatformOriginErasedFields.BaseOnly := by
  induction work using OracleComp.inductionOn with
  | pure value=>trivial
  | query_bind query next ih=>
    simp only [simulateQ_bind,simulateQ_spec_query,RegistrationNativePlatformOriginGateSource.coins,bind_assoc,
      allQueriesSatisfy_query_bind_iff]
    exact ⟨by trivial,fun _=>⟨by trivial,fun reply=>ih reply⟩⟩

private theorem prefix_base (reserve : Nat → StateT Platform ProbComp (core.result.Result Unit Failure))
    (beforeP : Platform) (tag : PqxdhDeploymentInterface.FrameTag) (reply : Reply) :
    (RegistrationNativePlatformOriginResumedCallback.prefixWork (n := n) reserve beforeP tag reply).AllQueriesSatisfy
      RegistrationNativePlatformOriginErasedFields.BaseOnly := by
  rw [RegistrationNativePlatformOriginResumedCallback.prefixWork,allQueriesSatisfy_query_bind_iff]
  exact ⟨by trivial,fun _=>coins_base _⟩

private theorem run_current (service : QueryImpl (ServiceSpec n) (StateT (CtxPrivate n) ProbComp))
    (body : OracleComp (ServiceSpec n) A) (future : A → OracleComp (ServiceSpec n) X) (before : CtxPrivate n)
    (result : Joint n A X) (supported : result∈support (run service body future before)) :
    result.1∈support ((simulateQ service body).run before) := by
  simp only [run,mem_support_bind_iff,mem_support_pure_iff] at supported
  obtain ⟨current,called,final,_continued,rfl⟩ :=supported
  exact called

/-- The marker implication is an operational same-prefix receipt, separate from every probability estimate. -/
def Flags (service : QueryImpl (ServiceSpec n) (StateT (CtxPrivate n) ProbComp))
    (decode : AdaptiveCtxReceive.RawDecoder) (accepts : Label n → X × CtxPrivate n → Prop)
    (journal : OracleComp (ServiceSpec n) X) (start : CtxPrivate n) : Prop :=
  ∀cut :PqxdhRecordFactsOriginOrdinalCut.Cut n X,∀earlier,
    Prefix service journal start []
      (((ServiceSpec n).query (.sealing cut.pending) :OracleComp (ServiceSpec n) _) >>=cut.next) cut.state cut.past earlier →
    ∀sealed∈support ((service (.sealing cut.pending)).run cut.state),
    ∀final∈support ((simulateQ (PqxdhRecordFactsOriginMuteAdaptive.marked cut.pending.material decode service)
      (cut.next sealed.1)).run (sealed.2,false)),
    accepts cut.pending.material (final.1,final.2.1) →final.2.2=true

/-- A literal hidden-send branch has the original coefficient-two bound for its SAME acquired-history, actual refused reply, and actual accepted future. -/
theorem hidden_bound {E Value : Type} (route : RawCtxServerRouting.SenderDecoder)
    (modes : Label n → KeyMode) (ideal : ∀label,modes label≠.real)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : Setup base KemSK)
    (actualWork : OracleComp (PqxdhRecordLiftInterface.WorldSpec n) (RegistrationNativeEntropyRun.Outcome E Value))
    (journal : OracleComp (ServiceSpec n) X)
    (project : X → PqxdhRecordLiftIdeal.Client n (RegistrationNativeRecordPackage.Extra E) Value)
    (projected : project <$>journal=RegistrationNativeRecordOriginProgram.program
      (RegistrationNativeWire.ledgerCodec (RegistrationNativePlatformOrdinaryExperiment.canonicalWire RegistrationNativePlatformConcreteSource.wire)) route actualWork)
    (rawCap : Nat) (bounded : (RegistrationNativeRecordOriginProgram.program
      (RegistrationNativeWire.ledgerCodec (RegistrationNativePlatformOrdinaryExperiment.canonicalWire RegistrationNativePlatformConcreteSource.wire)) route actualWork).IsQueryBoundP
      (fun query=>PqxdhRecordLiftCtxProtocolBounds.categoryCost .raw query=1) rawCap)
    (reserve : Nat → StateT Platform ProbComp (core.result.Result Unit Failure)) (read : A → Reply)
    (accepts : Label n → X × CtxPrivate n → Prop)
    (pending : PqxdhRecordLiftProtocol.Sealing n) (tag : PqxdhDeploymentInterface.FrameTag)
    (beforeP : Platform) (after : Reply → Platform → A) (same : ∀output state,read (after output state)=output)
    (future : A → OracleComp (ServiceSpec n) X) (before : CtxPrivate n)
    (past : List (Label n)) (cuts : List (PqxdhRecordFactsOriginOrdinalCut.Cut n X))
    (beforePrefix : Prefix (PqxdhRecordFactsPrivateCacheWorld.erased modes replace setup
        (RegistrationNativeWire.ledgerCodec (RegistrationNativePlatformOrdinaryExperiment.canonicalWire RegistrationNativePlatformConcreteSource.wire)))
      journal (PqxdhRecordFactsCounter.zeroCtx CtxPrivate.initial) []
      ((do let _←((ServiceSpec n).query (.lookup pending.material) :OracleComp (ServiceSpec n) _)
           let sealed←((ServiceSpec n).query (.sealing pending) :OracleComp (ServiceSpec n) _)
           continued reserve (fun output state=>pure (after output state)) beforeP tag sealed) >>=future) before past cuts)
    (flags : Flags (PqxdhRecordFactsPrivateCacheWorld.erased modes replace setup
        (RegistrationNativeWire.ledgerCodec (RegistrationNativePlatformOrdinaryExperiment.canonicalWire RegistrationNativePlatformConcreteSource.wire)))
      (RawCtxUniversalDecoder.decoder (RegistrationNativeWire.ledgerCodec
        (RegistrationNativePlatformOrdinaryExperiment.canonicalWire RegistrationNativePlatformConcreteSource.wire)).frameRead)
      accepts journal (PqxdhRecordFactsCounter.zeroCtx CtxPrivate.initial)) :
    𝒟[run (PqxdhRecordFactsPrivateCacheWorld.erased modes replace setup
        (RegistrationNativeWire.ledgerCodec (RegistrationNativePlatformOrdinaryExperiment.canonicalWire RegistrationNativePlatformConcreteSource.wire)))
      (do let _←((ServiceSpec n).query (.lookup pending.material) :OracleComp (ServiceSpec n) _)
          let sealed←((ServiceSpec n).query (.sealing pending) :OracleComp (ServiceSpec n) _)
          continued reserve (fun output state=>pure (after output state)) beforeP tag sealed) future before]
      {result|Bad read accepts before result}≤2*rawCap*((2^512:Nat):ℝ≥0∞)⁻¹ := by
  let codec:=RegistrationNativeWire.ledgerCodec
    (RegistrationNativePlatformOrdinaryExperiment.canonicalWire RegistrationNativePlatformConcreteSource.wire)
  let service:=PqxdhRecordFactsPrivateCacheWorld.erased modes replace setup codec
  let decode:=RawCtxUniversalDecoder.decoder codec.frameRead
  let afterFuture:=fun output state=>future (after output state)
  let body:=do
    let _←((ServiceSpec n).query (.lookup pending.material) :OracleComp (ServiceSpec n) _)
    let sealed←((ServiceSpec n).query (.sealing pending) :OracleComp (ServiceSpec n) _)
    continued reserve (fun output state=>pure (after output state)) beforeP tag sealed
  have bind_continued (sealed : Reply) :
      (continued (n := n) reserve (fun output state=>pure (after output state)) beforeP tag sealed >>=future)=
        continued reserve afterFuture beforeP tag sealed := by
    simp only [continued,bind_assoc,pure_bind,afterFuture]
  have prefixForm : body >>=future=
      (do let _←((ServiceSpec n).query (.lookup pending.material) :OracleComp (ServiceSpec n) _)
          let sealed←((ServiceSpec n).query (.sealing pending) :OracleComp (ServiceSpec n) _)
          continued reserve afterFuture beforeP tag sealed) := by
    simp only [body,bind_assoc,bind_continued]
  change Prefix service journal (PqxdhRecordFactsCounter.zeroCtx CtxPrivate.initial) [] (body >>=future) before past cuts at beforePrefix
  rw [prefixForm] at beforePrefix
  change 𝒟[run service body future before] {result|Bad read accepts before result}≤_
  have form : run service body future before=
      (do let looked←(service (.lookup pending.material)).run before
          run service (((ServiceSpec n).query (.sealing pending) :OracleComp (ServiceSpec n) _) >>=
            continued reserve (fun output state=>pure (after output state)) beforeP tag) future looked.2) := by
    simp only [run,body,simulateQ_bind,simulateQ_spec_query,StateT.run_bind,bind_assoc]
  rw [form]
  let : MeasurableSpace (Unit × CtxPrivate n):=⊤
  let : DiscreteMeasurableSpace (Unit × CtxPrivate n):=⟨fun _=>trivial⟩
  apply PqxdhRecordFactsOriginAverage.bind_le
  intro looked lookupCalled
  have sealPrefix:=Prefix.step beforePrefix lookupCalled
  simp only [PqxdhRecordLiftWorldProvenance.sealingCoordinates,PqxdhRecordFactsOriginOrdinalPath.cutAt,List.append_nil] at sealPrefix
  let cut :PqxdhRecordFactsOriginOrdinalCut.Cut n X:=⟨pending,continued reserve afterFuture beforeP tag,looked.2,past⟩
  have localBound:=RegistrationNativePlatformOriginGivenReserveBound.reached route modes replace setup actualWork journal project projected
    rawCap bounded cut (ideal pending.material) (PqxdhRecordFactsOriginOrdinalPath.prefix_reach service sealPrefix)
    reserve afterFuture beforeP tag rfl
  let observed:=RegistrationNativePlatformOriginReplyJointObservation.joint reserve after future beforeP tag pending.material decode service looked.2 pending
  have erased : Prod.fst <$>observed=run service
      (((ServiceSpec n).query (.sealing pending) :OracleComp (ServiceSpec n) _) >>=
        continued reserve (fun output state=>pure (after output state)) beforeP tag) future looked.2 :=
    RegistrationNativePlatformOriginReplyJointObservation.erase reserve after future beforeP tag pending.material decode service looked.2 pending
  have sameProbability : 𝒟[Prod.fst <$>observed] {result|Bad read accepts before result}=
      𝒟[observed] {result|Bad read accepts before result.1} := by
    rw [←prEvent_eq_evalDist_of_discrete,←prEvent_eq_evalDist_of_discrete,prEvent_map]
  rw [←erased,sameProbability]
  calc
    _≤𝒟[observed] {result|result.2=true} := by
      apply measure_mono_ae
      apply OracleComp.ae_evalDist_of_forall_mem_support
      intro result supported bad
      change result.2=true
      obtain ⟨sealed,gated,finished,sealCalled,gateCalled,finishedCalled,equal⟩ :=
        RegistrationNativePlatformOriginReplyJointObservation.cases_source reserve after future beforeP tag pending.material decode service looked.2 pending result supported
      have currentCalled : result.1.1∈support ((simulateQ service body).run before) := by
        have lifted : result.1∈support (Prod.fst <$>observed):=by rw [support_map];exact ⟨result,supported,rfl⟩
        rw [erased] at lifted
        have current:=run_current service _ future looked.2 result.1 lifted
        simp only [body,simulateQ_bind,simulateQ_spec_query,StateT.run_bind,mem_support_bind_iff]
        exact ⟨looked,lookupCalled,by simpa only [simulateQ_bind,simulateQ_spec_query,StateT.run_bind,mem_support_bind_iff] using current⟩
      obtain ⟨refused,label,acquired,accepted⟩ :=bad
      obtain ⟨entry,absent,present⟩ :=acquired
      have lookupKept:=RegistrationNativePlatformOriginErasedFields.base_call modes replace setup codec
        (.lookup pending.material) (by trivial) before looked lookupCalled
      have gateKept:=RegistrationNativePlatformOriginErasedFields.program modes replace setup codec _
        (prefix_base reserve beforeP tag sealed.1) sealed.2 gated gateCalled
      have material : pending.material=label := by
        by_contra different
        have other:=RegistrationNativePlatformOriginErasedFields.sealing_other modes replace setup codec pending looked.2 sealed sealCalled label (Ne.symm different)
        have fresh : entry∉(looked.2.keys label).1.successfulSeals:=by rw [lookupKept];exact absent
        have inserted : entry∈(sealed.2.keys label).1.successfulSeals:=by rw [←gateKept];simpa only [equal] using present
        exact fresh ((congrArg (fun state=>state.1.successfulSeals) other) ▸inserted)
      have markedCalled : finished∈support ((simulateQ (PqxdhRecordFactsOriginMuteAdaptive.marked pending.material decode service)
          (continued reserve afterFuture beforeP tag sealed.1)).run (sealed.2,false)) := by
        rw [RegistrationNativePlatformOriginReplyJointObservation.continued_form reserve beforeP tag pending.material decode service]
        rw [mem_support_bind_iff]
        exact ⟨gated,gateCalled,finishedCalled⟩
      have acceptedPending : accepts pending.material (finished.1,finished.2.1) := by
        rw [material]
        simpa only [equal] using accepted
      have raised:=flags cut cuts sealPrefix sealed sealCalled finished markedCalled acceptedPending
      have absentOutput : gated.1.1=none :=by simpa only [equal,same] using refused
      simpa only [equal,absentOutput,Option.isNone_none,Bool.true_and] using raised
    _≤2*rawCap*((2^512:Nat):ℝ≥0∞)⁻¹ := by
      have projection:=RegistrationNativePlatformOriginReplyJointObservation.project reserve after future beforeP tag pending.material decode service looked.2 pending
      have probability : 𝒟[observed] {result|result.2=true}=
          𝒟[RegistrationNativePlatformOriginResumedCallback.sealingObservation reserve afterFuture beforeP tag pending.material decode service looked.2 pending]
            {result|result.2=true} := by
        rw [←projection]
        rw [←prEvent_eq_evalDist_of_discrete,←prEvent_eq_evalDist_of_discrete,prEvent_map]
      exact probability.trans_le localBound

/-- The actual source normal form averages its original coins and contributes the coefficient-two bound once for its single possible hidden send; neither coordinate nor failure histories are conditioned away. -/
theorem bound {E Value : Type} (route : RawCtxServerRouting.SenderDecoder)
    (modes : Label n → KeyMode) (ideal : ∀label,modes label≠.real)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : Setup base KemSK)
    (actualWork : OracleComp (PqxdhRecordLiftInterface.WorldSpec n) (RegistrationNativeEntropyRun.Outcome E Value))
    (journal : OracleComp (ServiceSpec n) X)
    (project : X → PqxdhRecordLiftIdeal.Client n (RegistrationNativeRecordPackage.Extra E) Value)
    (projected : project <$>journal=RegistrationNativeRecordOriginProgram.program
      (RegistrationNativeWire.ledgerCodec (RegistrationNativePlatformOrdinaryExperiment.canonicalWire RegistrationNativePlatformConcreteSource.wire)) route actualWork)
    (rawCap : Nat) (bounded : (RegistrationNativeRecordOriginProgram.program
      (RegistrationNativeWire.ledgerCodec (RegistrationNativePlatformOrdinaryExperiment.canonicalWire RegistrationNativePlatformConcreteSource.wire)) route actualWork).IsQueryBoundP
      (fun query=>PqxdhRecordLiftCtxProtocolBounds.categoryCost .raw query=1) rawCap)
    (reserve : Nat → StateT Platform ProbComp (core.result.Result Unit Failure)) (read : A → Reply)
    (accepts : Label n → X × CtxPrivate n → Prop)
    (body : OracleComp (ServiceSpec n) A) (sourceForm : Form reserve read body)
    (future : A → OracleComp (ServiceSpec n) X) (before : CtxPrivate n)
    (past : List (Label n)) (cuts : List (PqxdhRecordFactsOriginOrdinalCut.Cut n X))
    (beforePrefix : Prefix (PqxdhRecordFactsPrivateCacheWorld.erased modes replace setup
        (RegistrationNativeWire.ledgerCodec (RegistrationNativePlatformOrdinaryExperiment.canonicalWire RegistrationNativePlatformConcreteSource.wire)))
      journal (PqxdhRecordFactsCounter.zeroCtx CtxPrivate.initial) []
      (body >>=future) before past cuts)
    (flags : Flags (PqxdhRecordFactsPrivateCacheWorld.erased modes replace setup
        (RegistrationNativeWire.ledgerCodec (RegistrationNativePlatformOrdinaryExperiment.canonicalWire RegistrationNativePlatformConcreteSource.wire)))
      (RawCtxUniversalDecoder.decoder (RegistrationNativeWire.ledgerCodec
        (RegistrationNativePlatformOrdinaryExperiment.canonicalWire RegistrationNativePlatformConcreteSource.wire)).frameRead)
      accepts journal (PqxdhRecordFactsCounter.zeroCtx CtxPrivate.initial)) :
    𝒟[run (PqxdhRecordFactsPrivateCacheWorld.erased modes replace setup
        (RegistrationNativeWire.ledgerCodec (RegistrationNativePlatformOrdinaryExperiment.canonicalWire RegistrationNativePlatformConcreteSource.wire)))
      body future before]
      {result|Bad read accepts before result}≤2*rawCap*((2^512:Nat):ℝ≥0∞)⁻¹ := by
  induction sourceForm generalizing before past cuts with
  | quiet body quiet=>
    rw [quiet_bound modes replace setup _ read accepts body quiet future before]
    exact bot_le
  | hidden pending tag beforeP after same=>
    exact hidden_bound route modes ideal replace setup actualWork journal project projected rawCap bounded reserve read accepts
      pending tag beforeP after same future before past cuts beforePrefix flags
  | coin amount next _later ih=>
    apply coin_bound modes replace setup _ read accepts amount next future before (2*rawCap*((2^512:Nat):ℝ≥0∞)⁻¹)
    intro result supported
    apply ih result.1 result.2 past cuts
    rw [bind_assoc] at beforePrefix
    exact coin_prefix _ journal (PqxdhRecordFactsCounter.zeroCtx CtxPrivate.initial) [] amount
      (fun reply=>next reply >>=future) before past cuts beforePrefix result supported

end BeaconcryptCore.Computational.RegistrationNativePlatformOriginSourceFormBound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOriginSourceFormBound.coin_keys' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOriginSourceFormBound.coin_keys

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOriginSourceFormBound.coin_prefix' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOriginSourceFormBound.coin_prefix

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOriginSourceFormBound.quiet_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOriginSourceFormBound.quiet_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOriginSourceFormBound.coin_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOriginSourceFormBound.coin_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOriginSourceFormBound.hidden_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOriginSourceFormBound.hidden_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOriginSourceFormBound.bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOriginSourceFormBound.bound
