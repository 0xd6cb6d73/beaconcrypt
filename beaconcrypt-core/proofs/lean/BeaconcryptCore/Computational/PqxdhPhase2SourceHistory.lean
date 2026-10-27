import BeaconcryptCore.Computational.PqxdhPhase2GeneratedDriver

/-! The actual prechallenge scheduler appends at most one reveal-history entry per original request. Identity, primitive and native finish computations retain the same prior history. This bound concerns the complete supported evaluated execution, including failed requests. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.PqxdhPhase2SourceHistory
open PqxdhPhase2SourceScheduler PqxdhPhase2SourceAux PqxdhPrivateKemSource PqxdhKemIndCca
open PqxdhInitializerSecrecy PqxdhStatefulPhase1EufCma
open PqxdhEd25519EufCma PqxdhJointIdentity PqxdhPhase1AcceptanceOracle
variable {ι M P I D K X Response A KemSK : Type} {baseSpec : OracleSpec ι} {S B : Nat}
variable (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
  (primitives : Primitives) (count : Nat) (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
  (writer : RawCtxMixedShared.Writer) (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder)
  (decode : RawCtxReceive.FrameDecoder) (localImpl : QueryImpl (LocalSpec I D K X Response) (StateT A ProbComp))
  (baseImpl : QueryImpl baseSpec ProbComp) (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (secret : KemSK)
local notation "handler" => ordinary attachedVerify primitives count source writer sender route decode localImpl
local notation "evaluate" => evalKem baseImpl kem secret

/-- Every actual scheduler callback preserves the prior observations and adds at most one reveal entry. -/
theorem step (query : (Spec baseSpec S B).Domain) (state : State M P I D K (A × BareState count) S B)
    (result : (Spec baseSpec S B).Range query × State M P I D K (A × BareState count) S B)
    (present : result ∈ support (evaluate ((handler query).run state))) :
    ∃ suffix, result.2.roles.2.observations = state.roles.2.observations ++ suffix ∧ suffix.length ≤ 1 := by
  rcases query with ((query | query) | query)
  · change result ∈ support (evaluate (ccaCoins _)) at present
    rw [evalKem_coins] at present
    exact (PqxdhPhase2LiveFinish.old_step_history source writer sender route decode query state result present).2.2.2
  · simp only [ordinary, StateT.run_mk, bind_pure_comp, evalKem, simulateQ_map, support_map] at present
    obtain ⟨reply, _, rfl⟩ := present
    exact ⟨[], by simp [identityState]⟩
  · cases query with
    | finish index raw =>
      simp only [ordinary, PqxdhPhase2LiveFinish.finishImpl, StateT.run, StateT.mk,
        bind_pure_comp, evalKem, simulateQ_map, support_map] at present
      obtain ⟨reply, _, rfl⟩ := present
      exact ⟨[], by simp [PqxdhPhase2LiveFinish.install, RawCtxProtocolReveals.tick]⟩

/-- The whole adaptive prechallenge schedule appends at most its original request allowance, without dropping rejected, identity or finish branches. -/
theorem schedule {Result : Type} (client : OracleComp (Spec baseSpec S B) Result)
    (budget : Nat) (bounded : client.IsTotalQueryBound budget)
    (state : State M P I D K (A × BareState count) S B)
    (result : Result × State M P I D K (A × BareState count) S B)
    (present : result ∈ support (evaluate ((simulateQ handler client).run state))) :
    ∃ suffix, result.2.roles.2.observations = state.roles.2.observations ++ suffix ∧ suffix.length ≤ budget := by
  induction client using OracleComp.inductionOn generalizing budget state result with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, evalKem, simulateQ_pure, mem_support_pure_iff] at present
      subst result
      exact ⟨[], by simp⟩
  | query_bind query next ih =>
      rw [isTotalQueryBound_query_bind_iff] at bounded
      rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, evalKem_bind, mem_support_bind_iff] at present
      obtain ⟨reply, supported, continued⟩ := present
      obtain ⟨firstLog, prefixEq, prefixLength⟩ :=
        step attachedVerify primitives count source writer sender route decode localImpl baseImpl kem secret query state reply supported
      obtain ⟨tailLog, tailEq, tailLength⟩ :=
        ih reply.1 (budget - 1) (bounded.2 reply.1) reply.2 result continued
      refine ⟨firstLog ++ tailLog, ?_, ?_⟩
      · rw [tailEq, prefixEq, List.append_assoc]
      · simp only [List.length_append]
        omega

/-- Publishing the generated Phase1 object embeds the old history without adding or deleting any observation. -/
theorem start_length {setup : StatefulPhase1Setup baseSpec}
    (env : PqxdhPhase2GeneratedDriver.Environment setup M P I K X Response A S B)
    (index : Nat) (publicIdentity : PublicIdentity) (generated : Generated setup Unit)
    (bundle : Phase1Candidate)
    (result : Option Pqxdh.Bytes × PqxdhGeneratedBeaconState.State setup M P I K A S (B + 1))
    (present : result ∈ support (PqxdhGeneratedBeaconState.start setup env.phase1Writer index publicIdentity generated env.binding bundle env.initial)) :
    result.2.roles.2.observations.length = env.initial.roles.2.observations.length := by
  simp only [PqxdhGeneratedBeaconState.start, support_map] at present
  obtain ⟨reply, _, rfl⟩ := present
  simp [PqxdhGeneratedBeaconState.reinstall, PqxdhGeneratedBeaconState.extend, PqxdhGeneratedBeaconState.embedHistory]

/-- The actual generated driver pays its complete original source request allowance for all prior reveal observations after publication. -/
theorem driver_length {setup : StatefulPhase1Setup baseSpec}
    (env : PqxdhPhase2GeneratedDriver.Environment setup M P I K X Response A S B)
    (program : PqxdhPhase2GeneratedDriver.Program baseSpec setup.Context S (B + 1))
    (budget : Nat) (bounded : ∀ reply, (program.main reply).IsTotalQueryBound budget)
    (index : Nat) (publicIdentity : PublicIdentity) (generated : Generated setup Unit)
    (transcript : Phase1PublicTranscript setup.Context) (identities : BareState count)
    (result : Phase1Candidate × program.Selection × PqxdhGeneratedBeaconState.State setup M P I K (A × BareState count) S (B + 1))
    (present : result ∈ support (evaluate (PqxdhPhase2GeneratedDriver.ordinaryRun env program attachedVerify primitives count
      index publicIdentity generated transcript identities))) :
    result.2.2.roles.2.observations.length ≤ env.initial.roles.2.observations.length + budget := by
  simp only [PqxdhPhase2GeneratedDriver.ordinaryRun, evalKem_bind, evalKem_coins,
    mem_support_bind_iff] at present
  obtain ⟨started, startedSupport, selected, selectedSupport, finished⟩ := present
  have finalEq := eq_of_mem_support_pure _ finished
  subst result
  obtain ⟨suffix, equality, cap⟩ := schedule attachedVerify primitives count env.source env.recordWriter env.senderId env.route env.decode
    env.localImpl baseImpl kem secret _ budget (bounded _) (PqxdhPhase2OldSource.packState started.2 identities) selected selectedSupport
  have startEq := start_length env index publicIdentity generated (PqxdhGeneratedBeaconSelector.bundle transcript) started startedSupport
  simp only [equality, List.length_append, PqxdhPhase2OldSource.packState]
  omega

end BeaconcryptCore.Computational.PqxdhPhase2SourceHistory
/-- info: 'BeaconcryptCore.Computational.PqxdhPhase2SourceHistory.step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase2SourceHistory.step

/-- info: 'BeaconcryptCore.Computational.PqxdhPhase2SourceHistory.schedule' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase2SourceHistory.schedule

/-- info: 'BeaconcryptCore.Computational.PqxdhPhase2SourceHistory.start_length' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase2SourceHistory.start_length

/-- info: 'BeaconcryptCore.Computational.PqxdhPhase2SourceHistory.driver_length' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase2SourceHistory.driver_length
