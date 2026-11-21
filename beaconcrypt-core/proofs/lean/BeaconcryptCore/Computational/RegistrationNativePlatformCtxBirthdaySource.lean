-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformCtxBirthdayCompiler
/-! Forgetting only the statistical digest history preserves the complete actual physical backend execution, including count-bearing replies and the full cache/query journal. -/
open OracleComp OracleSpec CoreModels
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformCtxBirthdaySource
open PqxdhRecordFactsCollision (DrawSpec History interpreter)
open RegistrationNativePlatformCtxBirthdayCompiler (plain compiler)
variable {A : Type}

/-- The statistical history has no influence on an actual digest or public coin reply. -/
theorem query_forget (query : (DrawSpec CtxRomAuth.CtxDigest).Domain) (before : History CtxRomAuth.CtxDigest) :
    Prod.fst <$> (interpreter query).run before = plain query := by
  cases query with
  | inl target => simp only [interpreter, StateT.run, bind_pure_comp, Functor.map_map, plain]; exact id_map _
  | inr coin => simp only [interpreter, StateT.run, bind_pure_comp, Functor.map_map, plain]; exact id_map _

/-- Every adaptive statistical draw program has its exact uninstrumented full-result distribution. -/
theorem draw_forget (work : OracleComp (DrawSpec CtxRomAuth.CtxDigest) A) (before : History CtxRomAuth.CtxDigest) :
    Prod.fst <$> (simulateQ interpreter work).run before = simulateQ plain work := by
  induction work using OracleComp.inductionOn generalizing before with
  | pure value => simp only [simulateQ_pure, StateT.run_pure, map_pure]
  | query_bind query next ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, map_bind]
    calc
      (do let result ← (interpreter query).run before
          Prod.fst <$> (simulateQ interpreter (next result.1)).run result.2) =
          (Prod.fst <$> (interpreter query).run before) >>= fun reply => simulateQ plain (next reply) := by
        simp only [bind_map_left]
        exact bind_congr (fun result => ih result.1 result.2)
      _ = _ := by rw [query_forget]

/-- Erasure recovers the literal physical hash execution, retaining every actual cache, input-journal, uniform-count and returned-value coordinate. -/
theorem complete (work : OracleComp RegistrationNativePlatformCtxBackend.Spec A)
    (before : RegistrationNativePlatformCtxBackend.State) (history : History CtxRomAuth.CtxDigest) :
    Prod.fst <$> (simulateQ interpreter ((simulateQ compiler work).run before)).run history =
      (simulateQ RegistrationNativePlatformCtxBackend.implementation work).run before :=
  (draw_forget _ history).trans (RegistrationNativePlatformCtxBirthdayCompiler.complete work before)
end BeaconcryptCore.Computational.RegistrationNativePlatformCtxBirthdaySource

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformCtxBirthdaySource.query_forget' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformCtxBirthdaySource.query_forget

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformCtxBirthdaySource.draw_forget' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformCtxBirthdaySource.draw_forget

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformCtxBirthdaySource.complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformCtxBirthdaySource.complete
