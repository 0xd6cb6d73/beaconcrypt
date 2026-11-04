-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformOriginReachedReserveBound
/-! Actual post-seal refusal instrumentation erases exactly to the original source continuation. Its replay-match event has the same probability as the stopped callback under the named uniform-instrumentation/private-cache service observation. -/
open OracleComp OracleSpec CoreModels Aeneas ENNReal MeasureTheory ProbabilityTheory
open Aeneas.Std hiding namespace core alloc
open beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
namespace BeaconcryptCore.Computational.RegistrationNativePlatformOriginResumedCallback
open CtxRomAuth
open PqxdhRecordLiftIdeal (CtxPrivate KeyMode)
open PqxdhRecordLiftWorldCompiler (Label)
open PqxdhRecordLiftProtocol (Service ServiceSpec)
open PqxdhRecordFactsOriginMuteAdaptive (marked)
open PqxdhRecordFactsOriginMuteUntilBad (serviceBad)
open PqxdhServerAuthExperiment (Setup Codec)
open RegistrationNativePlatformOriginReserveContinuationBound (continued)
open RegistrationNativePlatformOriginReserveSourceGuess (tail)
variable {n : Nat} {I KemSK Reader Response X Platform Failure : Type} {base : OracleSpec I}
local instance (T : Type) : MeasurableSpace T := ⊤
local instance (T : Type) : DiscreteMeasurableSpace T := ⟨fun _ => trivial⟩

private theorem quiet_program {A : Type} (target : Label n) (decode : AdaptiveCtxReceive.RawDecoder)
    (service : QueryImpl (ServiceSpec n) (StateT (CtxPrivate n) ProbComp))
    (work : OracleComp (ServiceSpec n) A)
    (quiet : work.AllQueriesSatisfy (fun query => ∀state,serviceBad target decode query state=false))
    (before : CtxPrivate n) (flag : Bool) :
    (simulateQ (marked target decode service) work).run (before,flag)=
      (fun result => (result.1,(result.2,flag))) <$> (simulateQ service work).run before := by
  induction work using OracleComp.inductionOn generalizing before with
  | pure value => simp only [simulateQ_pure,StateT.run_pure,map_pure]
  | query_bind query next ih =>
    rw [allQueriesSatisfy_query_bind_iff] at quiet
    simp only [simulateQ_bind,simulateQ_spec_query]
    change ((marked target decode service query >>= fun reply => simulateQ (marked target decode service) (next reply)).run (before,flag)) =
      (fun result => (result.1,(result.2,flag))) <$> ((service query >>= fun reply => simulateQ service (next reply)).run before)
    simp only [StateT.run_bind]
    change ((do let result ← (service query).run before; pure (result.1,(result.2,flag || serviceBad target decode query before))) >>= _) = _
    simp only [bind_assoc,pure_bind,map_bind]
    apply bind_congr
    intro result
    simpa only [pure_bind,quiet.1 before,Bool.or_false] using ih result.1 (quiet.2 result.1) result.2

private theorem coins_quiet {A : Type} (target : Label n) (decode : AdaptiveCtxReceive.RawDecoder) (work : ProbComp A) :
    (simulateQ RegistrationNativePlatformOriginGateSource.coins work).AllQueriesSatisfy
      (fun query => ∀state,serviceBad target decode query state=false) := by
  induction work using OracleComp.inductionOn with
  | pure value => trivial
  | query_bind query next ih =>
    simp only [simulateQ_bind,simulateQ_spec_query,RegistrationNativePlatformOriginGateSource.coins,bind_assoc,
      allQueriesSatisfy_query_bind_iff]
    exact ⟨fun _ => rfl,fun _ => ⟨fun _ => rfl,fun reply => ih reply⟩⟩

noncomputable def prefixWork
    (reserve : Nat → StateT Platform ProbComp (core.result.Result Unit Failure))
    (before : Platform) (tag : PqxdhDeploymentInterface.FrameTag) (reply : Option RawCtxSourceSend.Encrypted) :
    OracleComp (ServiceSpec n) (Option RawCtxSourceSend.Encrypted × Platform) := do
  let _ ← ((ServiceSpec n).query (.publish tag) : OracleComp (ServiceSpec n) _)
  simulateQ RegistrationNativePlatformOriginGateSource.coins
    ((RegistrationNativePlatformOrdinaryGate.gate reserve (fun value => value.ciphertext.length) reply).run before)

private theorem prefix_quiet
    (target : Label n) (decode : AdaptiveCtxReceive.RawDecoder)
    (reserve : Nat → StateT Platform ProbComp (core.result.Result Unit Failure))
    (before : Platform) (tag : PqxdhDeploymentInterface.FrameTag) (reply : Option RawCtxSourceSend.Encrypted) :
    (prefixWork reserve before tag reply).AllQueriesSatisfy
      (fun query => ∀state,serviceBad target decode query state=false) := by
  simp only [prefixWork,allQueriesSatisfy_query_bind_iff]
  exact ⟨fun _ => rfl,fun _ => coins_quiet target decode _⟩

variable (reserve : Nat → StateT Platform ProbComp (core.result.Result Unit Failure))
    (after : Option RawCtxSourceSend.Encrypted → Platform → OracleComp (ServiceSpec n) X)
    (before : Platform) (tag : PqxdhDeploymentInterface.FrameTag)
    (target : Label n) (decode : AdaptiveCtxReceive.RawDecoder)
    (service : QueryImpl (ServiceSpec n) (StateT (CtxPrivate n) ProbComp))
    (reply : Option RawCtxSourceSend.Encrypted) (state : CtxPrivate n)

private theorem continued_form :
    (simulateQ (marked target decode service) (continued reserve after before tag reply)).run (state,false) =
      (do let gated ← (simulateQ service (prefixWork reserve before tag reply)).run state
          (simulateQ (marked target decode service) (after gated.1.1 gated.1.2)).run (gated.2,false)) := by
  have ast : continued reserve after before tag reply =
      (prefixWork reserve before tag reply >>= fun gated => after gated.1 gated.2) := by
    simp only [continued,prefixWork,bind_assoc]
  rw [ast,simulateQ_bind,StateT.run_bind,
    quiet_program target decode service _ (prefix_quiet target decode reserve before tag reply) state false]
  simp only [bind_map_left]

noncomputable def observation : ProbComp ((X × CtxPrivate n) × Bool) :=
  (fun result => ((result.1.2,result.2.1),result.1.1 && result.2.2)) <$>
    (simulateQ (marked target decode service)
      (continued reserve (fun output reached => (fun value => (output.isNone,value)) <$> after output reached) before tag reply)).run (state,false)

/-- The guarded publication observation erases to the literal original continuation and full private state. -/
theorem erase :
    Prod.fst <$> observation reserve after before tag target decode service reply state =
      (simulateQ service (continued reserve after before tag reply)).run state := by
  unfold observation
  simp only [Functor.map_map]
  have erased := PqxdhRecordFactsOriginMuteAdaptive.complete_erase target decode service
    (continued reserve (fun output reached => (fun value => (output.isNone,value)) <$> after output reached) before tag reply) (state,false)
  have projected := congrArg (Functor.map (Prod.map Prod.snd id)) erased
  simp only [Functor.map_map,Prod.map,id_eq] at projected
  rw [projected]
  unfold continued
  simp only [simulateQ_bind,simulateQ_spec_query,simulateQ_map,StateT.run_bind,StateT.run_map,map_bind,Functor.map_map,Prod.map,id_eq]
  apply bind_congr
  intro first
  apply bind_congr
  intro gated
  exact id_map _

local instance : MeasurableSpace ((X × CtxPrivate n) × Bool) := ⊤
local instance : DiscreteMeasurableSpace ((X × CtxPrivate n) × Bool) := ⟨fun _ => trivial⟩
local instance : MeasurableSpace ((Option (X × Platform)) × (CtxPrivate n × Bool)) := ⊤
local instance : DiscreteMeasurableSpace ((Option (X × Platform)) × (CtxPrivate n × Bool)) := ⟨fun _ => trivial⟩

/-- A replay match guarded by actual public refusal is exactly the stopped-tail match event. -/
theorem probability :
    𝒟[observation reserve after before tag target decode service reply state] {result | result.2=true} =
      𝒟[(simulateQ (marked target decode service) (tail reserve (after none) before tag reply)).run (state,false)]
        {result | result.2.2=true} := by
  unfold observation
  rw [←prEvent_eq_evalDist_of_discrete,←prEvent_eq_evalDist_of_discrete,prEvent_map,
    continued_form reserve _ before tag target decode service reply state]
  have ast : tail reserve (after none) before tag reply =
      (prefixWork reserve before tag reply >>= fun gated =>
        if gated.1.isNone then (fun value => some (value,gated.2)) <$> after none gated.2 else pure none) := by
    simp only [tail,prefixWork,bind_assoc]
  rw [ast,simulateQ_bind,StateT.run_bind,
    quiet_program target decode service _ (prefix_quiet target decode reserve before tag reply) state false]
  simp only [bind_map_left]
  conv_lhs => rw [OracleComp.prEvent_bind_eq_tsum]
  conv_rhs => rw [OracleComp.prEvent_bind_eq_tsum]
  apply tsum_congr
  rintro ⟨⟨output,reached⟩,secret⟩
  apply congrArg (HMul.hMul _)
  cases output with
  | none =>
    simp only [Option.isNone_none,ite_true,simulateQ_map,StateT.run_map,prEvent_map,Bool.true_and]
  | some encrypted =>
    simp only [Option.isNone_some,Bool.false_eq_true,ite_false,simulateQ_map,StateT.run_map,prEvent_map,
      Bool.false_and,simulateQ_pure,StateT.run_pure,prEvent_pure]
    rw [prEvent_false]

noncomputable def sealingObservation (pending : PqxdhRecordLiftProtocol.Sealing n) : ProbComp ((X × CtxPrivate n) × Bool) := do
  let sealed ← (service (.sealing pending)).run state
  observation reserve after before tag target decode service sealed.1 sealed.2

/-- Erasing the exact publication-refusal and match flag preserves the original resumed source callback. -/
theorem sealing_erase (pending : PqxdhRecordLiftProtocol.Sealing n) :
    Prod.fst <$> sealingObservation reserve after before tag target decode service state pending =
      (simulateQ service
        (((ServiceSpec n).query (.sealing pending) : OracleComp (ServiceSpec n) _) >>= continued reserve after before tag)).run state := by
  simp only [sealingObservation,map_bind,simulateQ_bind,simulateQ_spec_query,StateT.run_bind]
  apply bind_congr
  intro sealed
  exact erase reserve after before tag target decode service sealed.1 sealed.2

/-- The same actual seal, reserve and reached state have exactly the stopped match probability, without an additional bad event. -/
theorem sealing_probability
    (modes : Label n → KeyMode) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (setup : Setup base KemSK) (codec : Codec Reader Response) (pending : PqxdhRecordLiftProtocol.Sealing n) :
    𝒟[sealingObservation reserve after before tag pending.material (RawCtxUniversalDecoder.decoder codec.frameRead)
      (PqxdhRecordFactsPrivateCacheWorld.erased modes replace setup codec) state pending] {result | result.2=true} =
    𝒟[RegistrationNativePlatformOriginReserveCallback.callback reserve (after none) before tag modes setup codec replace pending state]
      {flag | flag=true} := by
  unfold sealingObservation RegistrationNativePlatformOriginReserveCallback.callback
  rw [←prEvent_eq_evalDist_of_discrete,←prEvent_eq_evalDist_of_discrete]
  conv_lhs => rw [OracleComp.prEvent_bind_eq_tsum]
  conv_rhs => rw [OracleComp.prEvent_bind_eq_tsum]
  apply tsum_congr
  intro sealed
  apply congrArg (HMul.hMul _)
  rw [bind_pure_comp (β := Bool),prEvent_map]
  have same := probability reserve after before tag pending.material (RawCtxUniversalDecoder.decoder codec.frameRead)
    (PqxdhRecordFactsPrivateCacheWorld.erased modes replace setup codec) sealed.1 sealed.2
  rw [←prEvent_eq_evalDist_of_discrete,←prEvent_eq_evalDist_of_discrete] at same
  exact same

section Reached
variable {E Value : Type}
local notation "concreteCodec" => RegistrationNativeWire.ledgerCodec
  (RegistrationNativePlatformOrdinaryExperiment.canonicalWire RegistrationNativePlatformConcreteSource.wire)
/-- The same actual reached source node has an erasing guarded continuation bounded by the derived reserve charge. -/
theorem reached (modes : Label n → KeyMode) (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : Setup base KemSK)
    (route : RawCtxServerRouting.SenderDecoder)
    (work : OracleComp (PqxdhRecordLiftInterface.WorldSpec n) (RegistrationNativeEntropyRun.Outcome E Value))
    (rawCap : Nat)
    (raws : (RegistrationNativeRecordOriginProgram.program concreteCodec route work).IsQueryBoundP
      (fun query => PqxdhRecordLiftCtxProtocolBounds.categoryCost .raw query=1) rawCap)
    (source : RegistrationNativePlatformOriginSourceTails.HasTails Platform Failure
      (RegistrationNativeRecordOriginProgram.program concreteCodec route work))
    (cut : PqxdhRecordFactsOriginOrdinalCut.Cut n (PqxdhRecordLiftIdeal.Client n (RegistrationNativeRecordPackage.Extra E) Value))
    (ideal : modes cut.pending.material≠.real)
    (called : PqxdhRecordFactsPrivateCacheSource.Reach
      (PqxdhRecordFactsPrivateCacheWorld.erased modes replace setup concreteCodec)
      (RegistrationNativeRecordOriginProgram.program concreteCodec route work)
      (PqxdhRecordFactsCounter.zeroCtx CtxPrivate.initial) []
      (((ServiceSpec n).query (.sealing cut.pending) : OracleComp (ServiceSpec n) _) >>= cut.next) cut.state cut.past) :
    ∃ (reserve : Nat → StateT Platform ProbComp (core.result.Result Unit Failure))
      (after : Option RawCtxSourceSend.Encrypted → Platform → OracleComp (ServiceSpec n)
        (PqxdhRecordLiftIdeal.Client n (RegistrationNativeRecordPackage.Extra E) Value))
      (before : Platform) (tag : PqxdhDeploymentInterface.FrameTag),cut.next=continued reserve after before tag ∧
      𝒟[sealingObservation reserve after before tag cut.pending.material (RawCtxUniversalDecoder.decoder (concreteCodec).frameRead)
        (PqxdhRecordFactsPrivateCacheWorld.erased modes replace setup concreteCodec) cut.state cut.pending]
        {result | result.2=true} ≤ 2*rawCap*((2^512 : Nat) : ℝ≥0∞)⁻¹ := by
  obtain ⟨reserve,after,before,tag,same,bounded⟩ :=
    RegistrationNativePlatformOriginReachedReserveBound.reached modes replace setup route work rawCap raws source cut ideal called
  refine ⟨reserve,after,before,tag,same,?_⟩
  rw [sealing_probability]
  exact bounded
end Reached
end BeaconcryptCore.Computational.RegistrationNativePlatformOriginResumedCallback

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOriginResumedCallback.erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOriginResumedCallback.erase

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOriginResumedCallback.probability' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOriginResumedCallback.probability

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOriginResumedCallback.sealing_erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOriginResumedCallback.sealing_erase

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOriginResumedCallback.sealing_probability' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOriginResumedCallback.sealing_probability

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOriginResumedCallback.reached' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOriginResumedCallback.reached
