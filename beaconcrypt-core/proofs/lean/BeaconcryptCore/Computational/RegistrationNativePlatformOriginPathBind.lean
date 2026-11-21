-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRecordFactsOriginOrdinalFinalPrefix
/-! Exact source paths split and compose at their actual monadic boundaries with the same private state, seal chronology and enclosing continuations. -/
open OracleComp OracleSpec
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1800000
namespace BeaconcryptCore.Computational.RegistrationNativePlatformOriginPathBind
open PqxdhRecordLiftIdeal (CtxPrivate)
open PqxdhRecordLiftWorldCompiler (Label)
open PqxdhRecordLiftProtocol (ServiceSpec)
open PqxdhRecordFactsOriginOrdinalCut (Cut)
open PqxdhRecordFactsOriginOrdinalPath (Path Prefix cutAt)
open PqxdhRecordFactsOriginOrdinalTrace (Result)
variable {n : Nat} {A B : Type}

def bindCut (next : A → OracleComp (ServiceSpec n) B) (cut : Cut n A) : Cut n B :=
  ⟨cut.pending,(fun reply=>cut.next reply >>= next),cut.state,cut.past⟩

private theorem cutAt_bind (query : (ServiceSpec n).Domain)
    (first : (ServiceSpec n).Range query → OracleComp (ServiceSpec n) A)
    (next : A → OracleComp (ServiceSpec n) B) (state : CtxPrivate n) (past : List (Label n)) :
    cutAt query (fun reply=>first reply >>=next) state past=(cutAt query first state past).map (bindCut next) := by
  cases query <;> rfl

/-- A literal source path splits at its actual bind boundary, preserving every cut's complete future and the same private state/history. -/
theorem split (service : QueryImpl (ServiceSpec n) (StateT (CtxPrivate n) ProbComp))
    (first : OracleComp (ServiceSpec n) A) (next : A → OracleComp (ServiceSpec n) B)
    (before : CtxPrivate n) (past : List (Label n)) (result : Result n B)
    (path : Path service (first >>=next) before past result) :
    ∃ (value : A) (middle : CtxPrivate n) (history : List (Label n)) (earlier : List (Cut n A)) (later : List (Cut n B)),
      Prefix service first before past (pure value) middle history earlier ∧
      Path service (next value) middle history (later,result.2) ∧
      result.1=earlier.map (bindCut next)++later := by
  induction first using OracleComp.inductionOn generalizing before past result with
  | pure value =>
    refine ⟨value,before,past,[],result.1,.initial,?_,rfl⟩
    simpa only [pure_bind] using path
  | query_bind query continuation ih =>
    rw [bind_assoc] at path
    obtain ⟨reply,answered,child,tail,rfl⟩ := PqxdhRecordFactsOriginOrdinalPath.path_query service query
      (fun answer=>continuation answer >>=next) before past result path
    obtain ⟨value,middle,history,earlier,later,prefixPath,following,cutSplit⟩ := ih _ _ _ _ tail
    refine ⟨value,middle,history,cutAt query continuation before past++earlier,later,?_,following,?_⟩
    · exact PqxdhRecordFactsOriginOrdinalPath.prefix_trans service (.step .initial answered) prefixPath
    · rw [cutSplit,List.map_append,←cutAt_bind,List.append_assoc]

/-- A real source prefix embeds in its unchanged enclosing continuation, with every cut updated to that exact continuation. -/
theorem prefix_bind (service : QueryImpl (ServiceSpec n) (StateT (CtxPrivate n) ProbComp))
    (next : A → OracleComp (ServiceSpec n) B)
    {first remaining : OracleComp (ServiceSpec n) A} {before middle : CtxPrivate n}
    {past history : List (Label n)} {cuts : List (Cut n A)}
    (prefixPath : Prefix service first before past remaining middle history cuts) :
    Prefix service (first >>=next) before past (remaining >>=next) middle history (cuts.map (bindCut next)) := by
  induction prefixPath with
  | initial => exact .initial
  | @step query continuation state past cuts reply previous called ih =>
    rw [bind_assoc] at ih
    have advanced := Prefix.step ih called
    simpa only [List.map_append,←cutAt_bind] using advanced

/-- Joining a completed real prefix to its actual suffix preserves one same-result source path and its complete cut order. -/
theorem compose (service : QueryImpl (ServiceSpec n) (StateT (CtxPrivate n) ProbComp))
    (next : A → OracleComp (ServiceSpec n) B)
    {first : OracleComp (ServiceSpec n) A} {value : A} {before middle : CtxPrivate n}
    {past history : List (Label n)} {cuts : List (Cut n A)} {result : Result n B}
    (prefixPath : Prefix service first before past (pure value) middle history cuts)
    (following : Path service (next value) middle history result) :
    Path service (first >>=next) before past (cuts.map (bindCut next)++result.1,result.2) := by
  have prefixLift := prefix_bind service next prefixPath
  simp only [pure_bind] at prefixLift
  exact PqxdhRecordFactsOriginOrdinalPath.prefix_path service prefixLift following
end BeaconcryptCore.Computational.RegistrationNativePlatformOriginPathBind

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOriginPathBind.split' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOriginPathBind.split

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOriginPathBind.prefix_bind' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOriginPathBind.prefix_bind

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOriginPathBind.compose' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOriginPathBind.compose
