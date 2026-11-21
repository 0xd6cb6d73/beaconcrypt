-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeMldsaEufTapeReduction

/-! Primitive generation/signing costs are explicit narrow source receipts. The eager ordinary-EUF reduction pays for every reserved ordinary generation, every reached nonselected source signature, each public random query and each selected external signing request, including failures. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeMldsaEufTapeCosts
open Classical
open RegistrationNativeMldsa (Source Credential)
open RegistrationNativeMldsaOpaque (handleSource)
open RegistrationNativeMldsaEufTape (Pool Token handler evaluate)
open RegistrationNativeMldsaChosen (IsUniform IsSigning)
variable {Value : Type} (source : Source)

def IsCoin : (RegistrationNativeMldsaProgram.Spec (handleSource source)).Domain → Prop
  | .inl _ => True
  | _ => False

def IsSign : (RegistrationNativeMldsaProgram.Spec (handleSource source)).Domain → Prop
  | .inr (.sign _ _) => True
  | _ => False

private theorem ordinary_coins (work : ProbComp Value) (count : Nat) (bounded : work.IsTotalQueryBound count) :
    (RegistrationNativeMldsaChosen.lift work).IsQueryBoundP IsUniform count := by
  classical
  have transferred := IsQueryBoundP.simulateQ_of_step_le_total
    (impl := RegistrationNativeMldsaChosen.coins) bounded (fun query => by
      change OracleComp.IsQueryBoundP ((RegistrationNativeMldsaEuf.Spec.query (.inl query)) : OracleComp RegistrationNativeMldsaEuf.Spec _) IsUniform 1
      simp only [isQueryBoundP_query_iff, IsUniform]
      trivial)
  simpa only [RegistrationNativeMldsaChosen.lift, Nat.mul_one] using transferred

private theorem ordinary_signs (work : ProbComp Value) :
    (RegistrationNativeMldsaChosen.lift work).IsQueryBoundP IsSigning 0 := by
  classical
  induction work using OracleComp.inductionOn with
  | pure value => trivial
  | query_bind query next ih =>
      simp only [RegistrationNativeMldsaChosen.lift, simulateQ_bind, simulateQ_spec_query]
      change OracleComp.IsQueryBoundP ((RegistrationNativeMldsaEuf.Spec.query (.inl query) : OracleComp RegistrationNativeMldsaEuf.Spec _) >>=
        fun reply => RegistrationNativeMldsaChosen.lift (next reply)) IsSigning 0
      rw [isQueryBoundP_query_bind_iff]
      constructor
      · exact Or.inl (fun impossible => impossible.elim)
      · intro reply
        simpa only [IsSigning, ite_false] using ih reply

private theorem owned (qSign : Nat)
    (bounded : ∀ key request, (source.sign key request).IsTotalQueryBound qSign)
    (key : Credential source) (request : registration.MldsaSigningRequest) :
    (RegistrationNativeMldsa.owned source key request).IsTotalQueryBound qSign := by
  classical
  unfold RegistrationNativeMldsa.owned
  split
  · exact bounded key.secret request
  · trivial

/-- One eager routed source slot has its literal private-randomness allowance. Generation uses its already reserved entry. -/
theorem query_coins (qSign : Nat)
    (bounded : ∀ key request, (source.sign key request).IsTotalQueryBound qSign)
    (publicKey : RegistrationNativeMldsaEuf.PublicKey) (tape : List (Option (Token source)))
    (query : (RegistrationNativeMldsaProgram.Spec (handleSource source)).Domain) (before : Pool source) :
    ((handler source publicKey tape query).run before).IsQueryBoundP IsUniform
      ((if IsCoin source query then 1 else 0) + qSign * (if IsSign source query then 1 else 0)) := by
  classical
  cases query with
  | inl coin =>
      change OracleComp.IsQueryBoundP ((fun reply => (reply, before)) <$> (RegistrationNativeMldsaEuf.Spec.query (.inl coin) : OracleComp RegistrationNativeMldsaEuf.Spec _)) IsUniform _
      simp only [isQueryBoundP_map_iff, isQueryBoundP_query_iff, IsUniform, IsCoin, IsSign, ite_true, ite_false, Nat.mul_zero, Nat.add_zero]
      trivial
  | inr query => cases query with
    | generate => trivial
    | sign handle request =>
        simp only [IsCoin, IsSign, ite_false, ite_true, Nat.mul_one, Nat.zero_add,
          handler, StateT.run]
        cases found : before.keys[handle.secret]? with
        | none => trivial
        | some key =>
            simp only
            split
            · cases key with
              | some ordinary =>
                  exact (isQueryBoundP_map_iff _ _ _).mpr
                    (ordinary_coins (RegistrationNativeMldsa.owned source ordinary request) qSign (owned source qSign bounded ordinary request))
              | none =>
                  simp only [isQueryBoundP_map_iff, isQueryBoundP_query_iff, IsUniform]
                  exact fun impossible => impossible.elim
            · trivial

/-- Every source signing slot issues at most one ordinary challenger request, including an optional failed reply. -/
theorem query_signs (publicKey : RegistrationNativeMldsaEuf.PublicKey) (tape : List (Option (Token source)))
    (query : (RegistrationNativeMldsaProgram.Spec (handleSource source)).Domain) (before : Pool source) :
    ((handler source publicKey tape query).run before).IsQueryBoundP IsSigning (if IsSign source query then 1 else 0) := by
  classical
  cases query with
  | inl coin =>
      change OracleComp.IsQueryBoundP ((fun reply => (reply, before)) <$> (RegistrationNativeMldsaEuf.Spec.query (.inl coin) : OracleComp RegistrationNativeMldsaEuf.Spec _)) IsSigning _
      simp only [isQueryBoundP_map_iff, isQueryBoundP_query_iff, IsSigning, IsSign, ite_false]
      trivial
  | inr query => cases query with
    | generate => trivial
    | sign handle request =>
        simp only [IsSign, ite_true, handler, StateT.run]
        cases found : before.keys[handle.secret]? with
        | none => trivial
        | some key =>
            simp only
            split
            · cases key with
              | some ordinary =>
                  exact ((isQueryBoundP_map_iff _ _ _).mpr (ordinary_signs (RegistrationNativeMldsa.owned source ordinary request))).mono (Nat.zero_le _)
              | none =>
                  simp only [isQueryBoundP_map_iff, isQueryBoundP_query_iff, IsSigning]
                  trivial
            · trivial

/-- All actual ordinary challenger queries are charged to the complete adaptive source signing-slot bound. -/
theorem program_signs (publicKey : RegistrationNativeMldsaEuf.PublicKey) (tape : List (Option (Token source)))
    (work : OracleComp (RegistrationNativeMldsaProgram.Spec (handleSource source)) Value) (count : Nat)
    (bounded : work.IsQueryBoundP (IsSign source) count) (before : Pool source) :
    (evaluate source publicKey tape work before).IsQueryBoundP IsSigning count := by
  classical
  exact bounded.simulateQ_run_StateT_of_step (query_signs source publicKey tape) before

/-- Complete eager execution pays only its source random queries and the declared primitive cost at each signing slot. -/
theorem program_coins (qSign : Nat)
    (primitive : ∀ key request, (source.sign key request).IsTotalQueryBound qSign)
    (publicKey : RegistrationNativeMldsaEuf.PublicKey) (tape : List (Option (Token source)))
    (work : OracleComp (RegistrationNativeMldsaProgram.Spec (handleSource source)) Value)
    (qCoins qSigns : Nat) (coins : work.IsQueryBoundP (IsCoin source) qCoins)
    (signs : work.IsQueryBoundP (IsSign source) qSigns) (before : Pool source) :
    (evaluate source publicKey tape work before).IsQueryBoundP IsUniform (qCoins + qSign * qSigns) := by
  classical
  induction work using OracleComp.inductionOn generalizing qCoins qSigns before with
  | pure value => trivial
  | query_bind query next ih =>
      rw [isQueryBoundP_query_bind_iff] at coins signs
      change ((handler source publicKey tape query).run before >>= fun result =>
        evaluate source publicKey tape (next result.1) result.2).IsQueryBoundP IsUniform _
      have rest := isQueryBoundP_bind (query_coins source qSign primitive publicKey tape query before)
        (fun result _ => ih result.1 _ _ (coins.2 result.1) (signs.2 result.1) result.2)
      apply rest.mono
      have coinPositive : IsCoin source query → 0 < qCoins := fun h => coins.1.resolve_left (not_not.mpr h)
      have signPositive : IsSign source query → 0 < qSigns := fun h => signs.1.resolve_left (not_not.mpr h)
      have shrink : IsSign source query → qSign * (qSigns - 1) + qSign = qSign * qSigns := by
        intro active
        simpa only [Nat.mul_add, Nat.mul_one] using congrArg (fun count => qSign * count)
          (Nat.sub_add_cancel (Nat.succ_le_iff.mpr (signPositive active)))
      by_cases hc : IsCoin source query <;> by_cases hs : IsSign source query <;>
        simp only [hc, hs, ite_true, ite_false, Nat.mul_zero, Nat.mul_one, true_implies, false_implies] at coinPositive signPositive shrink ⊢ <;> omega

/-- Every reserved ordinary optional key pays its declared primitive generation cost, even when unused after stopping or when generation fails. -/
theorem reservation (qGenerate : Nat) (primitive : source.generate.IsTotalQueryBound qGenerate) (count : Nat) :
    (RegistrationNativeMldsaEager.family source count).IsTotalQueryBound (qGenerate * count) := by
  induction count with
  | zero => trivial
  | succ count ih =>
      simp only [RegistrationNativeMldsaEager.family]
      have rest : (do
          let generated ← RegistrationNativeMldsa.generate source
          let other ← RegistrationNativeMldsaEager.family source count
          pure (Fin.cons generated other : Fin (count + 1) → Option (Credential source))).IsTotalQueryBound (qGenerate + qGenerate * count) := by
        apply isTotalQueryBound_bind (RegistrationNativeMldsa.generation_bound source qGenerate primitive)
        intro generated
        simpa only [bind_pure_comp, IsTotalQueryBound, isQueryBound_map_iff] using ih
      simpa only [Nat.mul_succ, Nat.add_comm] using rest

/-- The constructed ordinary EUF adversary's complete external signing budget is the actual source signing-slot budget. -/
theorem reduction_signs {count : Nat} (target : Fin (count + 1))
    (work : RegistrationNativeMldsaEuf.PublicKey → OracleComp (RegistrationNativeMldsaProgram.Spec (handleSource source))
      (Option RegistrationNativeMldsaEuf.Forgery))
    (publicKey : RegistrationNativeMldsaEuf.PublicKey) (qSigns : Nat)
    (bounded : (work publicKey).IsQueryBoundP (IsSign source) qSigns) :
    (RegistrationNativeMldsaEufTapeReduction.adversary source target work publicKey).IsQueryBoundP IsSigning qSigns := by
  suffices same : (RegistrationNativeMldsaEufTapeReduction.adversary source target work publicKey).IsQueryBoundP IsSigning (0 + qSigns) by
    simpa only [Nat.zero_add] using same
  unfold RegistrationNativeMldsaEufTapeReduction.adversary
  refine isQueryBoundP_bind (ordinary_signs (RegistrationNativeMldsaEager.family source count)) ?_
  intro others _possible
  simpa only [bind_pure_comp, isQueryBoundP_map_iff] using
    program_signs source publicKey (RegistrationNativeMldsaEufTape.selectedTape source target others) (work publicKey) qSigns bounded {}

/-- The ordinary reduction's total random-query bill includes all other reserved key generations, actual source public randomness, and every allowed ordinary signing primitive. -/
theorem reduction_coins (qGenerate qSign : Nat) (generation : source.generate.IsTotalQueryBound qGenerate)
    (signing : ∀ key request, (source.sign key request).IsTotalQueryBound qSign)
    {count : Nat} (target : Fin (count + 1))
    (work : RegistrationNativeMldsaEuf.PublicKey → OracleComp (RegistrationNativeMldsaProgram.Spec (handleSource source))
      (Option RegistrationNativeMldsaEuf.Forgery))
    (publicKey : RegistrationNativeMldsaEuf.PublicKey) (qCoins qSigns : Nat)
    (coins : (work publicKey).IsQueryBoundP (IsCoin source) qCoins)
    (signs : (work publicKey).IsQueryBoundP (IsSign source) qSigns) :
    (RegistrationNativeMldsaEufTapeReduction.adversary source target work publicKey).IsQueryBoundP IsUniform
      (qGenerate * count + (qCoins + qSign * qSigns)) := by
  unfold RegistrationNativeMldsaEufTapeReduction.adversary
  refine isQueryBoundP_bind
    (ordinary_coins (RegistrationNativeMldsaEager.family source count) (qGenerate * count) (reservation source qGenerate generation count)) ?_
  intro others _possible
  simpa only [bind_pure_comp, isQueryBoundP_map_iff] using
    program_coins source qSign signing publicKey (RegistrationNativeMldsaEufTape.selectedTape source target others)
      (work publicKey) qCoins qSigns coins signs {}
end BeaconcryptCore.Computational.RegistrationNativeMldsaEufTapeCosts

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaEufTapeCosts.query_coins' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaEufTapeCosts.query_coins

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaEufTapeCosts.query_signs' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaEufTapeCosts.query_signs

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaEufTapeCosts.program_signs' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaEufTapeCosts.program_signs

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaEufTapeCosts.program_coins' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaEufTapeCosts.program_coins

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaEufTapeCosts.reservation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaEufTapeCosts.reservation

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaEufTapeCosts.reduction_signs' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaEufTapeCosts.reduction_signs

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaEufTapeCosts.reduction_coins' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaEufTapeCosts.reduction_coins
