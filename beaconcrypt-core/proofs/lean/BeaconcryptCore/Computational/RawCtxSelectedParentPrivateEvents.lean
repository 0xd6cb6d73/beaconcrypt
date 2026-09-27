import BeaconcryptCore.Computational.RawCtxSelectedParentPrivate
import BeaconcryptCore.Computational.AdaptiveCtxPrefixValidation

/-!
Private alias routing retains the same actual public HKDF service while hidden live reads are masked only for an unconditioned event that excludes their recorded disclosure. No disclosure probability is added. The remaining comparison cost is the original target-free masked execution's complete candidate event, in either direction. The source composition must derive the actual freshness implication and the candidate budget.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RawCtxSelectedParentPrivateEvents
open RawCtxSelectedChain RawCtxSelectedParentEntry RawCtxSelectedParentTable
open RawCtxSelectedLiveRead RawCtxSelectedLiveTrace RawCtxSelectedLiveCompiler
open PqxdhJointKdf PqxdhJointKdfGame PqxdhSecretInputKdf PqxdhFullSecretInputKdf

/-- Private alias substitution changes no permitted optional read or callback effect. -/
theorem alternate_safe {Auxiliary : Type}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (entry : Entry) (output : FullOutput) (target : RootOutput)
    (view : RawCtxSelectedParentLive.View) (query : Spec.Domain)
    (safe : RawCtxSelectedParentReadMask.direct query = false) :
    RawCtxSelectedParentPrivate.alternate (Auxiliary := Auxiliary) source writer prior entry output
        (nativeReader (RawCtxFreshChainCut.concreteChain target)) view query =
      RawCtxSelectedParentPrivate.alternate source writer prior entry output labelRead view query := by
  cases query with
  | inl query =>
      rcases query with (receive | opening) | ((send | sealing) | (coin | (hash | view)))
      all_goals rfl
  | inr query =>
      simp only [RawCtxSelectedParentPrivate.alternate, RawCtxSelectedParentLive.handler, nativeReader,
        before_exposure query.1 (RawCtxFreshChainCut.concreteChain target) query.2 safe]

/-- Routing equal-byte private aliases preserves every non-exposing callback in both reader interpretations. -/
theorem query_safe {Auxiliary : Type}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (entry : Entry) (output : FullOutput) (target : RootOutput)
    (view : RawCtxSelectedParentLive.View) (query : Spec.Domain)
    (safe : RawCtxSelectedParentReadMask.direct query = false) :
    RawCtxSelectedParentPrivate.handler (Auxiliary := Auxiliary) source writer prior entry output
        (nativeReader (RawCtxFreshChainCut.concreteChain target)) view target query =
      RawCtxSelectedParentPrivate.handler source writer prior entry output labelRead view target query := by
  unfold RawCtxSelectedParentPrivate.handler RawCtxSelectedAliasCoupling.routed
  split
  · exact alternate_safe source writer prior entry output target view query safe
  · exact RawCtxSelectedParentReadMask.query_safe source writer prior entry output target view query safe

/-- The full original event excluding the recorded hidden read has equal unconditioned probability under the actual and masked readers, even with private aliases. -/
theorem event_good {Auxiliary Result : Type}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (entry : Entry) (output : FullOutput) (target : RootOutput)
    (view : RawCtxSelectedParentLive.View) (client : OracleComp Spec Result)
    (state : RawCtxSelectedParentLive.State Auxiliary)
    (event : Result × RawCtxSelectedParentLive.State Auxiliary → Prop) :
    Pr[fun result => event result ∧ result.2.2 = false |
      (simulateQ (RawCtxSelectedParentPrivate.observed source writer prior entry output
        (nativeReader (RawCtxFreshChainCut.concreteChain target)) view target) client).run state] =
      Pr[fun result => event result ∧ result.2.2 = false |
        (simulateQ (RawCtxSelectedParentPrivate.observed source writer prior entry output labelRead view target) client).run state] := by
  exact RawCtxFlaggedQueryAgreement.event_good _ _ inputs RawCtxSelectedParentReadMask.direct
    (query_safe source writer prior entry output target view) client state event

noncomputable def decision {Auxiliary Result : Type}
    (event : Result × RawCtxSelectedParentLive.State Auxiliary → Prop)
    (result : Result × RawCtxSelectedParentLive.State Auxiliary) : Bool := by
  classical
  exact decide (event result ∧ result.2.2 = false)

/-- The Boolean experiment tests the original event and the actual final disclosure flag together, without conditioning. -/
theorem decision_probability {Auxiliary Result : Type}
    (event : Result × RawCtxSelectedParentLive.State Auxiliary → Prop)
    (run : ProbComp (Result × RawCtxSelectedParentLive.State Auxiliary)) :
    Pr[= true | decision event <$> run] = Pr[fun result => event result ∧ result.2.2 = false | run] := by
  simp only [← probEvent_eq_eq_probOutput, probEvent_map, Function.comp_def, decision, decide_eq_true_eq]

/-- The original private-table experiment and target-free masked observer differ only by the complete masked candidate event; excluded disclosures have no additive charge. -/
theorem local_bound {Auxiliary Result : Type}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (entry : Entry) (output : FullOutput) (target : RootOutput)
    (view : RawCtxSelectedParentLive.View) (client : OracleComp Spec Result)
    (state : RawCtxSelectedParentLive.State Auxiliary)
    (event : Result × RawCtxSelectedParentLive.State Auxiliary → Prop) :
    (decision event <$> (simulateQ (RawCtxSelectedParentPrivate.observed source writer prior entry output
      (nativeReader (RawCtxFreshChainCut.concreteChain target)) view target) client).run state).boolDistAdvantage
      (decision event <$> (simulateQ (RawCtxSelectedParentReadMask.observed source writer prior entry output
        labelRead view) client).run state) ≤
      Pr[fun result => target ∈ result.2.1.2 |
        (simulateQ (RawCtxSelectedParentReadMask.observed source writer prior entry output labelRead view) client).run state].toReal := by
  have agreement := event_good source writer prior entry output target view client state event
  rw [ProbComp.boolDistAdvantage]
  simp only [evalDist_apply_singleton]
  rw [decision_probability, decision_probability, agreement]
  have variation := (abs_probOutput_toReal_sub_le_tvDist
    (decision event <$> (simulateQ (RawCtxSelectedParentPrivate.observed source writer prior entry output labelRead view target) client).run state)
    (decision event <$> (simulateQ (RawCtxSelectedParentReadMask.observed source writer prior entry output labelRead view) client).run state)).trans
      (tvDist_map_le (decision event) _ _)
  rw [decision_probability, decision_probability, tvDist_comm] at variation
  exact variation.trans (RawCtxSelectedParentPrivate.distance source writer prior entry output
    labelRead view target client state)

end BeaconcryptCore.Computational.RawCtxSelectedParentPrivateEvents
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedParentPrivateEvents.alternate_safe' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedParentPrivateEvents.alternate_safe

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedParentPrivateEvents.query_safe' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedParentPrivateEvents.query_safe

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedParentPrivateEvents.event_good' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedParentPrivateEvents.event_good

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedParentPrivateEvents.decision_probability' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedParentPrivateEvents.decision_probability

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedParentPrivateEvents.local_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedParentPrivateEvents.local_bound
