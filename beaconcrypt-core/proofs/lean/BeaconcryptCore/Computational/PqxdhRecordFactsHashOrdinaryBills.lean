-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRecordFactsHashPrivateBills
import BeaconcryptCore.Computational.PqxdhDeploymentCompileBudget

/-! Ordinary digest-query bills of the complete concrete source compiler. -/
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhRecordFactsHashOrdinaryBills
open PqxdhRecordLiftIdeal (CtxPrivate KeyMode)
open PqxdhRecordLiftWorldCompiler (Label)
open PqxdhRecordFactsPrivateCacheSourceDraw (Spec)
open PqxdhServerAuthExperiment (Setup Codec)
variable {n : Nat} {ι KemSK Reader Response : Type} {baseSpec : OracleSpec ι}

/-- Exactly ordinary full-byte hash addresses; private label/suffix addresses and coins are separate categories. -/
def ordinaryQuery : (Spec n).Domain → Bool
  | .inl (.inr _) => true
  | _ => false

/-- The logged native compiler makes at most one explicit hash request per original native hash call. -/
theorem logged_total {X : Type} (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (client : OracleComp RawCtxMixedOwner.NativeSpec X) (cap : Nat)
    (bounded : client.IsQueryBoundP (fun query => RawCtxMixedOwner.callKind query = .hash) cap)
    (state : PqxdhRecordLiftWorld.Counts × PqxdhRecordLiftLoggedAdapters.Frames) :
    (PqxdhRecordFactsHashNative.loggedProgram setup codec client state).IsTotalQueryBound cap := by
  rw [PqxdhRecordFactsHashNative.loggedProgram, IsTotalQueryBound, isQueryBound_map_iff,
    ← IsTotalQueryBound, ← isQueryBoundP_true_iff]
  have logged := PqxdhDeploymentCompileBudget.logged_bound _ client cap state.2 bounded
  apply logged.simulateQ_run_StateT_of_step
  intro query counts
  rw [isQueryBoundP_true_iff]
  have step := PqxdhRecordFactsHashNative.counted_queries setup codec query counts
  rcases query with request | input | input | bytes | frame
  all_goals simpa only [RawCtxMixedOwner.callKind, PqxdhRecordFactsHashNative.hashCost,
    reduceCtorEq, ite_true, ite_false] using step

/-- Shared forwarding preserves the logged native program's total explicit query cap. -/
theorem native_total {X : Type} (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (client : OracleComp RawCtxMixedOwner.NativeSpec X) (cap : Nat)
    (bounded : client.IsQueryBoundP (fun query => RawCtxMixedOwner.callKind query = .hash) cap)
    (state : CtxPrivate n) :
    (PqxdhRecordFactsHashShared.nativeProgram setup codec client state).IsTotalQueryBound cap := by
  rw [PqxdhRecordFactsHashShared.nativeProgram, IsTotalQueryBound, isQueryBound_map_iff]
  exact (logged_total setup codec client cap bounded (state.base.primitive.1, state.base.pending)).simulateQ_run_of_step
    PqxdhRecordFactsHashShared.compile_queries state

/-- All actual caller-known native work obeys its original hash cap in the ordinary combined-oracle category. -/
theorem native_ordinary {X : Type} (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (client : OracleComp RawCtxMixedOwner.NativeSpec X) (cap : Nat)
    (bounded : client.IsQueryBoundP (fun query => RawCtxMixedOwner.callKind query = .hash) cap)
    (state : CtxPrivate n) :
    (PqxdhRecordFactsHashShared.nativeProgram setup codec client state).IsQueryBoundP
      (fun query => ordinaryQuery query) cap := by
  apply IsQueryBoundP.of_imp (p' := fun _ => True) (fun _ _ => True.intro)
  rw [isQueryBoundP_true_iff]
  exact native_total setup codec client cap bounded state

/-- The entire finite-coin sampler contributes zero ordinary digest queries; its coins are retained and separately charged. -/
theorem coins_ordinary {X : Type} (work : ProbComp X) :
    (OracleComp.liftComp work (Spec n)).IsQueryBoundP (fun query => ordinaryQuery query) 0 := by
  induction work using OracleComp.inductionOn with
  | pure value => trivial
  | query_bind coin next ih =>
      rw [OracleComp.liftComp_bind, OracleComp.liftComp_query]
      change ((liftM ((Spec n).query (.inr coin)) : OracleComp (Spec n) _) >>= _).IsQueryBoundP _ 0
      rw [isQueryBoundP_query_bind_iff]
      exact ⟨Or.inl (by simp [ordinaryQuery]), ih⟩

/-- Every actual hidden sealing branch uses only its private address and finite coins, including width rejection and writer failure. -/
theorem sealing_ordinary (modes : Label n → KeyMode) (crypto : Pqxdh.Crypto)
    (writer : RawCtxMixedShared.Writer) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (pending : PqxdhRecordLiftProtocol.Sealing n) (state : CtxPrivate n) :
    (PqxdhRecordFactsPrivateCacheSourceDraw.compileHiddenSeal modes crypto writer replace pending state).IsQueryBoundP
      (fun query => ordinaryQuery query) 0 := by
  classical
  have addressed := PqxdhRecordFactsPrivateCacheSourceDraw.hiddenSeal_addressed modes crypto writer replace pending state
  have zero := (isQueryBoundP_zero_iff _ _).mpr addressed
  apply IsQueryBoundP.of_imp (p' := fun query => ¬ PqxdhRecordFactsPrivateCacheSourceDraw.Addressed pending.material query) _ zero
  intro query ordinary
  rcases query with (address | bytes) | coin
  · simp [ordinaryQuery] at ordinary
  · simp [PqxdhRecordFactsPrivateCacheSourceDraw.Addressed]
  · simp [ordinaryQuery] at ordinary

/-- Every concrete service's ordinary digest requests fit its existing source hash-category bill, retaining caller-known source callbacks. -/
theorem query_ordinary (modes : Label n → KeyMode) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (query : PqxdhRecordLiftProtocol.Service n) (state : CtxPrivate n) :
    ((PqxdhRecordFactsHashSource.compiler modes replace setup codec query).run state).IsQueryBoundP
      (fun query => ordinaryQuery query) (PqxdhRecordLiftCtxProtocolBounds.categoryCost .hash query) := by
  cases query with
  | allocate slot =>
      change (PqxdhRecordFactsHashBase.allocate slot state).IsQueryBoundP _ 0
      rw [PqxdhRecordFactsHashBase.allocate, isQueryBoundP_map_iff]
      exact coins_ordinary _
  | coin coin =>
      simp [PqxdhRecordFactsHashSource.compiler, PqxdhRecordFactsHashBase.coin, StateT.run,
        PqxdhRecordLiftCtxProtocolBounds.categoryCost, IsQueryBoundP, ordinaryQuery]
  | hash bytes =>
      simp [PqxdhRecordFactsHashSource.compiler, PqxdhRecordFactsHashShared.compile, StateT.run,
        PqxdhRecordLiftCtxProtocolBounds.categoryCost, IsQueryBoundP, ordinaryQuery]
  | charge kind => trivial
  | lookup coordinate => exact coins_ordinary (PqxdhRecordFactsHashLocal.lookupWork coordinate state)
  | opening pending => trivial
  | sealing pending =>
      exact (sealing_ordinary modes setup.source.crypto codec.frameWrite replace pending state).mono (by simp)
  | knownSend kernel context =>
      exact native_ordinary setup codec _ 1
        (PqxdhRecordLiftCtxProtocolBounds.known_send_hash kernel context) state
  | knownReceive kernel target context =>
      exact native_ordinary setup codec _ 1
        (PqxdhRecordLiftCtxProtocolBounds.known_receive_hash kernel target context) state
  | publish tag => trivial

/-- The actual adaptive compiler preserves the original weighted source hash bill with coefficient one. -/
theorem program_ordinary {X : Type} (modes : Label n → KeyMode) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (client : OracleComp (PqxdhRecordLiftProtocol.ServiceSpec n) X) (cap : Nat)
    (bounded : PqxdhRecordLiftCtxProgramBounds.Weighted (PqxdhRecordLiftCtxProtocolBounds.categoryCost .hash) client cap)
    (state : CtxPrivate n) :
    ((simulateQ (PqxdhRecordFactsHashSource.compiler modes replace setup codec) client).run state).IsQueryBoundP
      (fun query => ordinaryQuery query) cap :=
  PqxdhRecordLiftCtxBills.run_bound _ (fun query => ordinaryQuery query)
    (PqxdhRecordLiftCtxProtocolBounds.categoryCost .hash) (query_ordinary modes replace setup codec)
    client cap bounded state

open PqxdhRecordLiftInterface (Environment Frame EffectKind)
open PqxdhDeploymentInterface (FreshBounds Mode ModeSpec Budget)

/-- The complete initialized source compiler stays within the already defined shared hash total, including environment and caller-known hash work. -/
theorem source_ordinary {E X : Type} (modes : Label n → KeyMode) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (env : Environment n E)
    (startup : Nat) (allowance : Fin 14 → EffectKind → Nat) (framed : Frame env startup allowance)
    (serverKid : Aeneas.Std.U64) (bounds : FreshBounds) (mode : Mode)
    (budget : Budget) (adversary : OracleComp (ModeSpec mode) X) (respects : budget.Respects adversary)
    (decisionCost : Nat) :
    ((simulateQ (PqxdhRecordFactsHashSource.compiler modes replace setup codec)
      (PqxdhRecordLiftProtocol.program env setup.source.crypto codec route serverKid bounds mode adversary)).run
        (PqxdhRecordFactsCounter.zeroCtx CtxPrivate.initial)).IsQueryBoundP
      (fun query => ordinaryQuery query)
      (PqxdhRecordLiftIdeal.sharedHashTotal ⟨budget, startup, allowance, bounds, n, decisionCost⟩) := by
  rw [← PqxdhRecordLiftCtxBills.hash_bill]
  exact program_ordinary modes replace setup codec _ _
    (PqxdhRecordLiftCtxBills.program_categories .hash env startup allowance framed setup.source.crypto codec
      route serverKid bounds mode budget adversary respects decisionCost) _

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsHashOrdinaryBills.logged_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms logged_total
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsHashOrdinaryBills.native_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms native_total
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsHashOrdinaryBills.native_ordinary' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms native_ordinary
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsHashOrdinaryBills.coins_ordinary' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms coins_ordinary
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsHashOrdinaryBills.sealing_ordinary' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms sealing_ordinary
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsHashOrdinaryBills.query_ordinary' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms query_ordinary
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsHashOrdinaryBills.program_ordinary' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms program_ordinary
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsHashOrdinaryBills.source_ordinary' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms source_ordinary

end BeaconcryptCore.Computational.PqxdhRecordFactsHashOrdinaryBills
