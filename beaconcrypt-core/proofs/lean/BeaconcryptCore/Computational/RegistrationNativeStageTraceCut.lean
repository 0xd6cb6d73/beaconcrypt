-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeStageTrace
/-! A chronological source path splits at the literal selected callback, retaining the actual leading and trailing states. -/
open OracleComp OracleSpec
set_option autoImplicit false
set_option warningAsError true
namespace BeaconcryptCore.Computational.RegistrationNativeStageTraceCut
open RegistrationNativeStageTrace (Call Path Executed)
variable {Q S : Type} {spec : OracleSpec Q}

/-- The selected callback has exactly its original leading path, execution and full suffix. -/
theorem split (implementation : QueryImpl spec (StateT S ProbComp)) {before after : S}
    (leading trailing : List (Call spec S)) (call : Call spec S)
    (path : Path implementation before (leading++call::trailing) after) :
    Path implementation before leading call.before ∧ Executed implementation call ∧ Path implementation call.after trailing after := by
  induction leading generalizing before with
  | nil =>
      cases path with
      | cons step called rest last following => exact ⟨.nil _,called,following⟩
  | cons step leading ih =>
      cases path with
      | cons head called rest last following =>
          obtain ⟨beforePath,executed,afterPath⟩ := ih following
          exact ⟨.cons step called _ _ beforePath,executed,afterPath⟩

end BeaconcryptCore.Computational.RegistrationNativeStageTraceCut

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeStageTraceCut.split' does not depend on any axioms -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeStageTraceCut.split
