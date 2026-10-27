-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality

/-! The actual forwarded ordinary random interpreter retains all histories while interpreting the source's explicit uniform/hash prelude. -/
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhLaterChallengeRandomBackend
open AdaptiveCtxSharedHash PqxdhFirstRecordConfidentiality
variable (decode : AdaptiveCtxReceive.RawDecoder) (crypto : Pqxdh.Crypto)

/-- Interpret the existing source forwarding interface with the complete ordinary random CTX interpreter. -/
noncomputable def handler : QueryImpl HashSpec (StateT RandomState ProbComp) :=
  confRandomImpl decode crypto ∘ₛ RawCtxSourceSharedRom.forward

/-- An actual source coin is sampled uniformly and keeps every component state and history unchanged. -/
theorem coin (n : Nat) (state : RandomState) :
    (handler decode crypto (.inl n)).run state =
      (fun reply => (reply, state)) <$> (unifSpec.query n : ProbComp (Fin (n + 1))) := by
  change (confRandomImpl decode crypto (.inl (.inl (.inl n)))).run state = _
  rcases state with ⟨reduction, publicHistory, receiver, history, primitive⟩
  rw [confRandomImpl_run, reduction_selected]
  simp only [simulateQ_map, simulateQ_spec_query, StateT.run_map, Functor.map_map]
  rw [lower2_run, guard_forward]
  simp only [simulateQ_map, simulateQ_spec_query, StateT.run_map, Functor.map_map]
  rw [lower3_run]
  have wrapped : (AdaptiveCtxReceive.reductionImpl decode (.inl (.inl n))).run receiver =
      (fun a => (a, receiver)) <$> (AdaptiveRawNonceAead.AdaptiveSpec.query (.inl (.inl n)) :
        OracleComp AdaptiveRawNonceAead.AdaptiveSpec (Fin (n + 1))) := by
    simp only [AdaptiveCtxReceive.reductionImpl, StateT.run, bind_pure_comp]
  rw [wrapped, simulateQ_map, simulateQ_spec_query, StateT.run_map]
  rw [lower4_coin]
  simp only [Functor.map_map]
  rfl

/-- Every complete source coin program retains the entire actual random interpreter state, including all pre-existing histories. -/
theorem coins {Result : Type} (work : ProbComp Result) (state : RandomState) :
    (simulateQ (handler decode crypto) (simulateQ RawCtxSelectiveSharedRom.coins work)).run state =
      (fun result => (result, state)) <$> work := by
  induction work using OracleComp.inductionOn with
  | pure value => rfl
  | query_bind query next ih =>
    change (do
      let result ← (handler decode crypto (.inl query)).run state
      (simulateQ (handler decode crypto) (simulateQ RawCtxSelectiveSharedRom.coins (next result.1))).run result.2) = _
    rw [coin, bind_map_left]
    simpa only [map_bind] using (bind_congr fun answer => ih answer)

/-- The backend is the literal original forwarding followed by the ordinary random interpretation, for every complete adaptive source prelude and full starting state. -/
theorem forwarded {Result : Type} (work : OracleComp HashSpec Result) (state : RandomState) :
    (simulateQ (handler decode crypto) work).run state =
      (simulateQ (confRandomImpl decode crypto) (simulateQ RawCtxSourceSharedRom.forward work)).run state := by
  simp only [handler, QueryImpl.simulateQ_compose]

end BeaconcryptCore.Computational.PqxdhLaterChallengeRandomBackend

/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeRandomBackend.coin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeRandomBackend.coin

/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeRandomBackend.coins' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeRandomBackend.coins

/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeRandomBackend.forwarded' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeRandomBackend.forwarded
