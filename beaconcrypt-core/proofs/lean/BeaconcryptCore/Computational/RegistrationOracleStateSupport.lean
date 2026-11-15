-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.VCVioForwardOracleComp

/-! The unchanged generic state-support preservation lemma is shared by source journals and the flattened record world. Its statement and proof term are retained under their original qualified name; no protocol effect or security assumption is introduced here. -/
open OracleComp OracleSpec
set_option autoImplicit false
set_option warningAsError true
namespace BeaconcryptCore.Computational.PqxdhRecordLiftFlat
variable {κ κ' : Type} {spec : OracleSpec κ} {spec' : OracleSpec κ'}

/-- A state predicate that every query keeps is kept by every simulated program. -/
theorem support_keep_oracle {σ α : Type} (impl : QueryImpl spec (StateT σ (OracleComp spec'))) (B : σ → Prop)
    (keep : ∀ q s, B s → ∀ p ∈ support ((impl q).run s), B p.2) (oa : OracleComp spec α) (s : σ) (hs : B s) :
    ∀ p ∈ support ((simulateQ impl oa).run s), B p.2 := by
  induction oa using OracleComp.inductionOn generalizing s with
  | pure a =>
      intro p hp
      simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hp
      subst hp
      exact hs
  | query_bind q k ih =>
      intro p hp
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, id_map,
        StateT.run_bind] at hp
      obtain ⟨mid, hmid, hp⟩ := (MonadAttach.mem_support_bind).mp hp
      exact ih mid.1 mid.2 (keep q s hs mid hmid) p hp


end BeaconcryptCore.Computational.PqxdhRecordLiftFlat

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftFlat.support_keep_oracle' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftFlat.support_keep_oracle
