-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.CborRawIdealProvenanceStep

/-! A full-ledger invariant rule for the actual guarded World and arbitrary registration state. Its registration obligation is a one-command support fact over the original shared World effects. The proof retains the original test/fresh oracle programs and their analysis ledger even when their send is refused. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.CborRawIdealProvenanceRun
open PqxdhServerAuthExperiment (Setup Codec)
open PqxdhRecordLiftInterface (Environment EnvQuery)
open PqxdhDeploymentInterface (Entry Spec)
open PqxdhRecordLiftOrigins (Origins)
open PqxdhDeploymentEnvironmentJoin (fixedView)
open PqxdhDeploymentIdealOrigins (IsFixed QuietEntry aEffects coinOrSend_fixed)
open CborRawIdealProvenanceStep (worldStep)
variable {ι KemSK Reader Response E : Type} {baseSpec : OracleSpec ι} {n : Nat}
variable (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)

noncomputable def ledgerStep (env : Environment n E) (crypto : Pqxdh.Crypto) (serverKid : Std.U64)
    (bounds : PqxdhDeploymentInterface.FreshBounds) :
    QueryImpl PqxdhDeploymentInterface.FullSpec
      (StateT (PqxdhDeploymentSecrecy.Ledger × (E × PqxdhRecordLiftOrigins.State n)) ProbComp) :=
  ((worldStep setup codec route env).mapStateTBase
    (PqxdhDeploymentSecrecy.ledgerImpl crypto codec serverKid bounds)).flattenStateT

theorem ledgerStep_run (env : Environment n E) (crypto : Pqxdh.Crypto) (serverKid : Std.U64)
    (bounds : PqxdhDeploymentInterface.FreshBounds) (query : PqxdhDeploymentInterface.FullSpec.Domain)
    (ledger : PqxdhDeploymentSecrecy.Ledger) (state : E × PqxdhRecordLiftOrigins.State n) :
    (ledgerStep setup codec route env crypto serverKid bounds query).run (ledger, state) =
      (fun result => (result.1.1, (result.1.2, result.2))) <$>
        (simulateQ (worldStep setup codec route env)
          ((PqxdhDeploymentSecrecy.ledgerImpl crypto codec serverKid bounds query).run ledger)).run state := rfl

/-- An arbitrary program of the unchanged ledger's coins and sends preserves registration state, origins and fixed World view, and still returns an outcome of that original program. -/
theorem fixed_run {Result : Type} (env : Environment n E) (work : OracleComp Spec Result)
    (onlyFixed : work.IsQueryBoundP (fun query => PqxdhDeploymentSecrecy.coinOrSend query = false) 0)
    (e : E) (w : PqxdhRecordLiftWorld.State n) (o : Origins n) :
    ∀ result ∈ support ((simulateQ (worldStep setup codec route env) work).run (e, (w, o))),
      result.2.1 = e ∧ result.2.2.2 = o ∧ fixedView result.2.2.1 = fixedView w ∧ result.1 ∈ support work := by
  induction work using OracleComp.inductionOn generalizing w with
  | pure value =>
      intro result member
      simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at member
      subst member
      exact ⟨rfl, rfl, rfl, by simp⟩
  | query_bind query next ih =>
      intro result member
      rw [isQueryBoundP_query_bind_iff] at onlyFixed
      have sent : PqxdhDeploymentSecrecy.coinOrSend query = true := by
        rcases onlyFixed.1 with notFixed | impossible
        · simpa using notFixed
        · exact absurd impossible (Nat.lt_irrefl 0)
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, id_map,
        StateT.run_bind, mem_support_bind_iff] at member
      obtain ⟨step, stepMember, rest⟩ := member
      obtain ⟨same, sameO, view⟩ := CborRawIdealProvenanceStep.fixed setup codec route env query
        (coinOrSend_fixed query sent) (e, (w, o)) step stepMember
      dsimp only at same sameO view
      change result ∈ support ((simulateQ (worldStep setup codec route env) (next step.1)).run
        (step.2.1, (step.2.2.1, step.2.2.2))) at rest
      rw [same, sameO] at rest
      have nextFixed := onlyFixed.2 step.1
      simp only [sent, Bool.true_eq_false, ite_false] at nextFixed
      obtain ⟨sameE, nextO, nextView, nextMember⟩ := ih step.1 nextFixed step.2.2.1 result rest
      exact ⟨sameE, nextO, nextView.trans view,
        (mem_support_bind_iff _ _ _).mpr ⟨step.1, mem_support_query query step.1, nextMember⟩⟩

/-- A relation preserved by every actual fixed query is preserved by the ledger's original coin/send program. -/
theorem fixed_relation {Result : Type} (env : Environment n E)
    (R : E → PqxdhRecordLiftOrigins.State n → Prop)
    (rFixed : ∀ query e state, IsFixed query → R e state →
      ∀ result ∈ support ((worldStep setup codec route env query).run (e, state)), R result.2.1 result.2.2)
    (work : OracleComp Spec Result)
    (onlyFixed : work.IsQueryBoundP (fun query => PqxdhDeploymentSecrecy.coinOrSend query = false) 0)
    (e : E) (state : PqxdhRecordLiftOrigins.State n) (holds : R e state) :
    ∀ result ∈ support ((simulateQ (worldStep setup codec route env) work).run (e, state)),
      R result.2.1 result.2.2 := by
  induction work using OracleComp.inductionOn generalizing e state with
  | pure value =>
      intro result reached
      simpa only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] using
        reached ▸ holds
  | query_bind query next ih =>
      intro result reached
      rw [isQueryBoundP_query_bind_iff] at onlyFixed
      have sent : PqxdhDeploymentSecrecy.coinOrSend query = true := by
        rcases onlyFixed.1 with notFixed | impossible
        · simpa using notFixed
        · exact absurd impossible (Nat.lt_irrefl 0)
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at reached
      obtain ⟨step, stepMember, rest⟩ := reached
      have nextFixed := onlyFixed.2 step.1
      simp only [sent, Bool.true_eq_false, ite_false] at nextFixed
      exact ih step.1 nextFixed step.2.1 step.2.2
        (rFixed query e state (coinOrSend_fixed query sent) holds step stepMember) result rest

/-- Full-ledger preservation follows from fixed-view stability, quiet entries and the actual one-registration-step rule. No full-game relation is assumed. -/
theorem ledgerStep_keeps (env : Environment n E)
    (R : List Entry → E → PqxdhRecordLiftWorld.State n → Origins n → Prop)
    (rFixed : ∀ query transcript e w o, IsFixed query → R transcript e w o →
      ∀ result ∈ support ((worldStep setup codec route env query).run (e, (w, o))),
        R transcript result.2.1 result.2.2.1 result.2.2.2)
    (rQuiet : ∀ transcript e w o (entry : Entry), QuietEntry entry → R transcript e w o → R (transcript ++ [entry]) e w o)
    (rStep : ∀ (query : EnvQuery) transcript e w o, R transcript e w o →
      ∀ result ∈ support ((simulateQ (aEffects setup codec route) ((env.step query).run e)).run (w, o)),
        R (transcript ++ [⟨.inl (.inr query.val), result.1.1⟩]) result.1.2 result.2.1 result.2.2)
    (crypto : Pqxdh.Crypto) (serverKid : Std.U64) (bounds : PqxdhDeploymentInterface.FreshBounds)
    (query : PqxdhDeploymentInterface.FullSpec.Domain)
    (state : PqxdhDeploymentSecrecy.Ledger × (E × PqxdhRecordLiftOrigins.State n))
    (holds : R state.1.transcript state.2.1 state.2.2.1 state.2.2.2) :
    ∀ result ∈ support ((ledgerStep setup codec route env crypto serverKid bounds query).run state),
      R result.2.1.transcript result.2.2.1 result.2.2.2.1 result.2.2.2.2 := by
  rcases state with ⟨ledger, e, w, o⟩
  intro result member
  rw [ledgerStep_run, support_map] at member
  obtain ⟨inner, innerMember, rfl⟩ := member
  rcases query with request | secrecy
  · rw [PqxdhDeploymentSecrecy.ledgerImpl_forward, simulateQ_map, simulateQ_spec_query, StateT.run_map,
      support_map] at innerMember
    obtain ⟨answer, answerMember, rfl⟩ := innerMember
    have fixedCase : IsFixed request → R (ledger.record (.inl request) answer.1).transcript answer.2.1 answer.2.2.1
        answer.2.2.2 := by
      intro isFixed
      refine rQuiet _ _ _ _ _ (fun command reply equal => ?_)
        (rFixed request ledger.transcript e w o isFixed holds answer answerMember)
      have queries := congrArg Entry.query equal
      simp only [Sum.inl.injEq] at queries
      subst queries
      rcases command with ⟨command, allowed⟩
      cases command <;> first | exact absurd allowed id | exact isFixed
    have commandCase : ∀ command : EnvQuery, request = .inr command.val →
        R (ledger.record (.inl request) answer.1).transcript answer.2.1 answer.2.2.1 answer.2.2.2 := by
      intro command same
      subst same
      rw [CborRawIdealProvenanceStep.worldStep_reg setup codec route env command e (w, o), support_map] at answerMember
      obtain ⟨stepped, steppedMember, rfl⟩ := answerMember
      exact rStep command ledger.transcript e w o holds stepped steppedMember
    rcases request with coin | command
    · exact fixedCase trivial
    · cases command with
      | create pin keyId => exact commandCase ⟨.create pin keyId, trivial⟩ rfl
      | bundle owner => exact commandCase ⟨.bundle owner, trivial⟩ rfl
      | accept raw => exact commandCase ⟨.accept raw, trivial⟩ rfl
      | build session payload => exact commandCase ⟨.build session payload, trivial⟩ rfl
      | finish owner raw => exact commandCase ⟨.finish owner raw, trivial⟩ rfl
      | hmac key message => exact commandCase ⟨.hmac key message, trivial⟩ rfl
      | hash _ => exact fixedCase trivial
      | serverSend _ _ => exact fixedCase trivial
      | serverRaw _ => exact fixedCase trivial
      | beaconSend _ _ => exact fixedCase trivial
      | beaconRaw _ _ => exact fixedCase trivial
  · obtain ⟨same, sameO, view, produced⟩ := fixed_run setup codec route env _
      (PqxdhDeploymentSecrecy.secrecy_frame crypto codec serverKid bounds secrecy ledger) e w o inner innerMember
    have preserved := fixed_relation setup codec route env
      (fun e state => R ledger.transcript e state.1 state.2)
      (fun query e state isFixed h => rFixed query ledger.transcript e state.1 state.2 isFixed h) _
      (PqxdhDeploymentSecrecy.secrecy_frame crypto codec serverKid bounds secrecy ledger) e (w, o) holds inner innerMember
    dsimp only
    rw [PqxdhDeploymentEligibility.ledger_secrecy crypto codec serverKid bounds secrecy ledger inner.1 produced]
    refine rQuiet _ _ _ _ _ (fun command reply equal => ?_) preserved
    have queries := congrArg Entry.query equal
    simp at queries

/-- Every outcome of an arbitrary adaptive full CE client preserves the relation proved by the registration step and the quiet/fixed-view rules. -/
theorem run_keeps {Result : Type} (env : Environment n E)
    (R : List Entry → E → PqxdhRecordLiftWorld.State n → Origins n → Prop)
    (rFixed : ∀ query transcript e w o, IsFixed query → R transcript e w o →
      ∀ result ∈ support ((worldStep setup codec route env query).run (e, (w, o))),
        R transcript result.2.1 result.2.2.1 result.2.2.2)
    (rQuiet : ∀ transcript e w o (entry : Entry), QuietEntry entry → R transcript e w o → R (transcript ++ [entry]) e w o)
    (rStep : ∀ (query : EnvQuery) transcript e w o, R transcript e w o →
      ∀ result ∈ support ((simulateQ (aEffects setup codec route) ((env.step query).run e)).run (w, o)),
        R (transcript ++ [⟨.inl (.inr query.val), result.1.1⟩]) result.1.2 result.2.1 result.2.2)
    (crypto : Pqxdh.Crypto) (serverKid : Std.U64) (bounds : PqxdhDeploymentInterface.FreshBounds)
    (adversary : OracleComp PqxdhDeploymentInterface.FullSpec Result) (ledger : PqxdhDeploymentSecrecy.Ledger)
    (e : E) (w : PqxdhRecordLiftWorld.State n) (o : Origins n) (holds : R ledger.transcript e w o) :
    ∀ result ∈ support ((simulateQ (CborRawIdealProvenanceGuard.handler setup codec route)
        ((simulateQ (PqxdhRecordLiftInterface.native env)
          ((simulateQ (PqxdhDeploymentSecrecy.ledgerImpl crypto codec serverKid bounds) adversary).run ledger)).run
            e)).run (w, o)),
      R result.1.1.2.transcript result.1.2 result.2.1 result.2.2 := by
  intro result member
  rw [OracleComp.simulateQ_mapStateTBase_run_eq_map_flattenStateT, support_map] at member
  obtain ⟨flat, flatMember, rfl⟩ := member
  change flat ∈ support ((simulateQ (worldStep setup codec route env)
    ((simulateQ (PqxdhDeploymentSecrecy.ledgerImpl crypto codec serverKid bounds) adversary).run ledger)).run
      (e, (w, o))) at flatMember
  rw [OracleComp.simulateQ_mapStateTBase_run_eq_map_flattenStateT, support_map] at flatMember
  obtain ⟨inner, innerMember, rfl⟩ := flatMember
  exact PqxdhDeploymentEnvironmentJoin.keeps_simulateQ (ledgerStep setup codec route env crypto serverKid bounds)
    (fun state => R state.1.transcript state.2.1 state.2.2.1 state.2.2.2)
    (fun query state h => ledgerStep_keeps setup codec route env R rFixed rQuiet rStep
      crypto serverKid bounds query state h) adversary (ledger, (e, (w, o))) holds inner innerMember

end BeaconcryptCore.Computational.CborRawIdealProvenanceRun

/-- info: 'BeaconcryptCore.Computational.CborRawIdealProvenanceRun.ledgerStep_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawIdealProvenanceRun.ledgerStep_run

/-- info: 'BeaconcryptCore.Computational.CborRawIdealProvenanceRun.fixed_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawIdealProvenanceRun.fixed_run

/-- info: 'BeaconcryptCore.Computational.CborRawIdealProvenanceRun.fixed_relation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawIdealProvenanceRun.fixed_relation

/-- info: 'BeaconcryptCore.Computational.CborRawIdealProvenanceRun.ledgerStep_keeps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawIdealProvenanceRun.ledgerStep_keeps

/-- info: 'BeaconcryptCore.Computational.CborRawIdealProvenanceRun.run_keeps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawIdealProvenanceRun.run_keeps
