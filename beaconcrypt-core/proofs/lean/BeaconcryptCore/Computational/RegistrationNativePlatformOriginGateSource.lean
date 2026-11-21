-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformGatedRecordPost
import BeaconcryptCore.Computational.PqxdhRecordFactsOriginAmbient
import BeaconcryptCore.Computational.CborRawRecordOriginProjection
/-! The actual public reserve runs as independent coins after the private seal. Its original platform poststate remains literal, while every private seal dictionary and attempted-publication log is retained. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformOriginGateSource
open PqxdhRecordLiftInterface (WorldSpec coinLift)
open PqxdhRecordLiftProtocol (Control ServiceSpec)
open PqxdhRecordLiftIdeal (CtxPrivate KeyMode ctxInterpreter)
open PqxdhRecordLiftWorldCompiler (Label)
open PqxdhServerAuthExperiment (Setup Codec)
open PqxdhRecordFactsOriginAmbient (Kept)
variable {n : Nat} {I KemSK Reader Response Platform Failure A : Type} {base : OracleSpec I}

def coins : QueryImpl unifSpec (OracleComp (ServiceSpec n)) := fun query => do
  let _ ← ((ServiceSpec n).query (.charge .coin) : OracleComp (ServiceSpec n) _)
  (ServiceSpec n).query (.coin query)

private theorem protocol_coins (work : ProbComp A) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (control : Control n) :
    (simulateQ (PqxdhRecordLiftProtocol.handler codec.frameRead route) (simulateQ coinLift work)).run control =
      (fun value => (value,control)) <$> simulateQ coins work := by
  induction work using OracleComp.inductionOn with
  | pure value => simp only [simulateQ_pure,StateT.run_pure,map_pure]
  | query_bind query continuation ih =>
    simp only [simulateQ_bind,coinLift,simulateQ_spec_query,StateT.run_bind,map_bind,coins]
    rw [show (PqxdhRecordLiftProtocol.handler (n := n) codec.frameRead route (.inr (.inl (.inl query)))).run control =
      (fun reply => (reply,control)) <$> coins query by
        simp only [PqxdhRecordLiftProtocol.handler,PqxdhRecordLiftProtocol.effects,StateT.run_bind,StateT.run_lift,
          bind_map_left,bind_pure_comp,coins,map_bind]
        rfl]
    simp only [bind_map_left,ih]
    rfl

/-- The actual cursor and Protocol close any public probabilistic action into coins alone, keeping both original control states literal. -/
theorem closed_program (work : ProbComp A) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (shell : CborRecordWorldClient.Shell) (control : Control n) :
    ((simulateQ (PqxdhRecordLiftProtocol.handler codec.frameRead route)
      ((simulateQ CborRecordWorldClient.handler (simulateQ coinLift work)).run shell)).run control) =
      (fun value => ((value,shell),control)) <$> simulateQ coins work := by
  rw [CborRawRecordOriginProjection.coin_shell,simulateQ_map,StateT.run_map,protocol_coins]
  simp only [Functor.map_map]

/-- A public action retains its exact platform result and complete private state under any physical service interpretation; only the public shell/control pair is framed. -/
theorem closed_source {Secret : Type}
    (service : QueryImpl (ServiceSpec n) (StateT Secret ProbComp)) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (work : StateT Platform ProbComp A) (before : RegistrationNativePlatformGatedRecordFlat.State n Platform Secret) :
    (RegistrationNativePlatformGatedRecordFlat.fold service codec route (RegistrationNativePlatformGatedRecordInterface.closed work)).run before =
      (fun result => (result.1.1,(((result.1.2,before.1.1.2),before.1.2),result.2))) <$>
        (simulateQ service (simulateQ coins (work.run before.1.1.1))).run before.2 := by
  unfold RegistrationNativePlatformGatedRecordFlat.fold
  change RegistrationNativePlatformGatedRecordFlat.join <$>
    (simulateQ service ((simulateQ (PqxdhRecordLiftProtocol.handler codec.frameRead route)
      ((simulateQ CborRecordWorldClient.handler (simulateQ coinLift (work.run before.1.1.1))).run before.1.1.2)).run before.1.2)).run before.2 = _
  rw [closed_program]
  simp only [simulateQ_map,StateT.run_map,Functor.map_map,RegistrationNativePlatformGatedRecordFlat.join]

private theorem coin_kept (modes : Label n → KeyMode) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (setup : Setup base KemSK) (codec : Codec Reader Response) (query : unifSpec.Domain)
    (before : CtxPrivate n) (result : unifSpec.Range query × CtxPrivate n)
    (supported : result ∈ support ((simulateQ (ctxInterpreter modes replace setup codec) (coins query)).run before)) :
    Kept before result.2 := by
  simp only [coins,simulateQ_bind,simulateQ_spec_query,StateT.run_bind,mem_support_bind_iff] at supported
  obtain ⟨charged,chargeCalled,called⟩ := supported
  exact Kept.trans before charged.2 result.2
    (PqxdhRecordFactsOriginAmbient.environmental_kept modes replace setup codec (.charge .coin) trivial before charged chargeCalled)
    (PqxdhRecordFactsOriginAmbient.environmental_kept modes replace setup codec (.coin query) trivial charged.2 result called)

private theorem coins_kept (modes : Label n → KeyMode) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (setup : Setup base KemSK) (codec : Codec Reader Response) (work : ProbComp A)
    (before : CtxPrivate n) (result : A × CtxPrivate n)
    (supported : result ∈ support ((simulateQ (ctxInterpreter modes replace setup codec) (simulateQ coins work)).run before)) :
    Kept before result.2 := by
  induction work using OracleComp.inductionOn generalizing before result with
  | pure value =>
    simp only [simulateQ_pure,StateT.run_pure,mem_support_pure_iff] at supported
    cases supported
    exact Kept.refl before
  | query_bind query continuation ih =>
    simp only [simulateQ_bind,simulateQ_spec_query,StateT.run_bind,mem_support_bind_iff] at supported
    obtain ⟨middle,called,continued⟩ := supported
    exact Kept.trans before middle.2 result.2
      (coin_kept modes replace setup codec query before middle called)
      (ih middle.1 middle.2 result continued)

/-- Executing the genuine post-send public reserve preserves the complete private seal dictionary and logs, without discarding its platform effects. -/
theorem closed_kept (modes : Label n → KeyMode) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (setup : Setup base KemSK) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (work : StateT Platform ProbComp A) (before : RegistrationNativePlatformGatedRecordFlat.State n Platform (CtxPrivate n))
    (result : A × RegistrationNativePlatformGatedRecordFlat.State n Platform (CtxPrivate n))
    (supported : result ∈ support ((RegistrationNativePlatformGatedRecordFlat.fold (ctxInterpreter modes replace setup codec) codec route
      (RegistrationNativePlatformGatedRecordInterface.closed work)).run before)) :
    Kept before.2 result.2.2 := by
  unfold RegistrationNativePlatformGatedRecordFlat.fold at supported
  change result ∈ support (RegistrationNativePlatformGatedRecordFlat.join <$>
    (simulateQ (ctxInterpreter modes replace setup codec)
      ((simulateQ (PqxdhRecordLiftProtocol.handler codec.frameRead route)
        ((simulateQ CborRecordWorldClient.handler (simulateQ coinLift (work.run before.1.1.1))).run before.1.1.2)).run before.1.2)).run before.2) at supported
  rw [closed_program] at supported
  simp only [simulateQ_map,StateT.run_map,Functor.map_map,support_map] at supported
  obtain ⟨inner,called,rfl⟩ := supported
  exact coins_kept modes replace setup codec (work.run before.1.1.1) before.2 inner called

/-- An absent actual public reply is either an already absent encoder result or an actual failed reserve at exactly the ciphertext's public encoded length. -/
theorem gate_refused (reserve : Nat → StateT Platform ProbComp (core.result.Result Unit Failure))
    (reply : Option RawCtxSourceSend.Encrypted) (before after : Platform)
    (supported : (none,after) ∈ support ((RegistrationNativePlatformOrdinaryGate.gate reserve (fun value => value.ciphertext.length) reply).run before)) :
    (reply=none ∧ after=before) ∨ ∃ value error,reply=some value ∧
      (.Err error,after) ∈ support ((reserve value.ciphertext.length).run before) := by
  cases reply with
  | none =>
    simp only [RegistrationNativePlatformOrdinaryGate.gate,StateT.run_pure,mem_support_pure_iff,Prod.mk.injEq] at supported
    exact Or.inl ⟨rfl,supported.2⟩
  | some value =>
    simp only [RegistrationNativePlatformOrdinaryGate.gate,StateT.run_bind,mem_support_bind_iff] at supported
    obtain ⟨⟨allocated,final⟩,called,returned⟩ := supported
    cases allocated with
    | Ok returnedUnit => simp only [StateT.run_pure,mem_support_pure_iff,Prod.mk.injEq,reduceCtorEq,false_and] at returned
    | Err error =>
      simp only [StateT.run_pure,mem_support_pure_iff,Prod.mk.injEq,true_and] at returned
      subst final
      exact Or.inr ⟨value,error,rfl,called⟩
end BeaconcryptCore.Computational.RegistrationNativePlatformOriginGateSource
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOriginGateSource.closed_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOriginGateSource.closed_program
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOriginGateSource.closed_kept' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOriginGateSource.closed_kept
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOriginGateSource.gate_refused' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOriginGateSource.gate_refused

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOriginGateSource.closed_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOriginGateSource.closed_source
