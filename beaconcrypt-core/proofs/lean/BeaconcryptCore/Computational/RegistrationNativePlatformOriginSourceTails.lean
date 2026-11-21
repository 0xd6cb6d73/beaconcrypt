-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformOriginReserveContinuationBound
import BeaconcryptCore.Computational.PqxdhRecordFactsPrivateCacheSource
/-! Actual post-seal publication/reserve syntax is stable under adaptive composition and exact source prefixes. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
namespace BeaconcryptCore.Computational.RegistrationNativePlatformOriginSourceTails
open PqxdhRecordLiftProtocol (Service ServiceSpec)
open RegistrationNativePlatformOriginReserveContinuationBound (continued)
variable {n : Nat} {Platform Failure A B : Type}
def Sealing (query : Service n) : Prop := ∃pending,query=.sealing pending
noncomputable def Head (Platform Failure : Type) (query : Service n)
    (next : (ServiceSpec n).Range query → OracleComp (ServiceSpec n) A) : Prop :=
  match query with
  | .sealing _ => ∃ (reserve : Nat → StateT Platform ProbComp (core.result.Result Unit Failure))
      (after : Option RawCtxSourceSend.Encrypted → Platform → OracleComp (ServiceSpec n) A)
      (before : Platform) (tag : PqxdhDeploymentInterface.FrameTag),next=continued reserve after before tag
  | _ => True
noncomputable def HasTails (Platform Failure : Type) (work : OracleComp (ServiceSpec n) A) : Prop :=
  OracleComp.recOn work (fun _ => True) (fun query next recurse => Head Platform Failure query next ∧ ∀reply,recurse reply)
private theorem query_tails (query : Service n) (next : (ServiceSpec n).Range query → OracleComp (ServiceSpec n) A) :
    HasTails Platform Failure (((ServiceSpec n).query query : OracleComp (ServiceSpec n) _) >>= next) =
      (Head Platform Failure query next ∧ ∀reply,HasTails Platform Failure (next reply)) := rfl
private theorem continued_bind (reserve : Nat → StateT Platform ProbComp (core.result.Result Unit Failure))
    (after : Option RawCtxSourceSend.Encrypted → Platform → OracleComp (ServiceSpec n) A)
    (before : Platform) (tag : PqxdhDeploymentInterface.FrameTag) (reply : Option RawCtxSourceSend.Encrypted)
    (next : A → OracleComp (ServiceSpec n) B) :
    (continued reserve after before tag reply >>= next)=continued reserve (fun output state => after output state >>= next) before tag reply := by
  simp only [continued,bind_assoc]
/-- Adaptive source composition preserves each actual charged tail. -/
theorem bind (work : OracleComp (ServiceSpec n) A) (next : A → OracleComp (ServiceSpec n) B)
    (first : HasTails Platform Failure work) (later : ∀value,HasTails Platform Failure (next value)) :
    HasTails Platform Failure (work >>= next) := by
  induction work using OracleComp.inductionOn with
  | pure value => simpa only [pure_bind] using later value
  | query_bind query continuation ih =>
      rw [query_tails] at first
      rw [bind_assoc,query_tails]
      refine ⟨?_,fun reply => ih reply (first.2 reply)⟩
      cases query
      case sealing pending =>
        obtain ⟨reserve,after,before,tag,same⟩ := first.1
        refine ⟨reserve,(fun output state => after output state >>= next),before,tag,?_⟩
        funext reply
        rw [same]
        exact continued_bind reserve after before tag reply next
      all_goals trivial
/-- Pure reassociation of a source result retains every actual post-seal tail. -/
theorem map (f : A → B) (work : OracleComp (ServiceSpec n) A) (source : HasTails Platform Failure work) :
    HasTails Platform Failure (f <$> work) := by
  simpa only [bind_pure_comp] using bind work (fun value => pure (f value)) source (fun _ => by trivial)
/-- A non-sealing service request retains every original reply continuation. -/
theorem nonsealing (query : Service n) (next : (ServiceSpec n).Range query → OracleComp (ServiceSpec n) A)
    (quiet : ¬Sealing query) (later : ∀reply,HasTails Platform Failure (next reply)) :
    HasTails Platform Failure (((ServiceSpec n).query query : OracleComp (ServiceSpec n) _) >>= next) := by
  rw [query_tails]
  refine ⟨?_,later⟩
  cases query
  case sealing pending => exact False.elim (quiet ⟨pending,rfl⟩)
  all_goals trivial
/-- No-sealing syntax needs no tail exception for any other service effects. -/
theorem zero (work : OracleComp (ServiceSpec n) A) (quiet : work.AllQueriesSatisfy (fun query => ¬Sealing query)) :
    HasTails Platform Failure work := by
  induction work using OracleComp.inductionOn with
  | pure value => trivial
  | query_bind query next ih =>
      rw [allQueriesSatisfy_query_bind_iff] at quiet
      rw [query_tails]
      refine ⟨?_,fun reply => ih reply (quiet.2 reply)⟩
      cases query
      case sealing pending => exact False.elim (quiet.1 ⟨pending,rfl⟩)
      all_goals trivial
private theorem coins_quiet {V : Type} (work : ProbComp V) :
    (simulateQ (RegistrationNativePlatformOriginGateSource.coins (n := n)) work).AllQueriesSatisfy (fun query => ¬Sealing query) := by
  induction work using OracleComp.inductionOn with
  | pure value => trivial
  | query_bind query next ih =>
      simp only [simulateQ_bind,simulateQ_spec_query,RegistrationNativePlatformOriginGateSource.coins,bind_assoc,
        allQueriesSatisfy_query_bind_iff]
      refine ⟨?_,fun _ => ⟨?_,fun reply => ih reply⟩⟩
      · rintro ⟨pending,impossible⟩;cases impossible
      · rintro ⟨pending,impossible⟩;cases impossible
private theorem continued_tails (reserve : Nat → StateT Platform ProbComp (core.result.Result Unit Failure))
    (after : Option RawCtxSourceSend.Encrypted → Platform → OracleComp (ServiceSpec n) A)
    (before : Platform) (tag : PqxdhDeploymentInterface.FrameTag) (reply : Option RawCtxSourceSend.Encrypted)
    (later : ∀output state,HasTails Platform Failure (after output state)) :
    HasTails Platform Failure (continued reserve after before tag reply) := by
  unfold continued
  apply bind _ _ (zero _ ?_)
  · intro _
    exact bind _ _ (zero _ (coins_quiet _)) (fun gated => later gated.1 gated.2)
  · rw [allQueriesSatisfy_query_iff]
    rintro ⟨pending,impossible⟩
    cases impossible
/-- The literal hidden-seal source node has its actual reserve continuation, preserving every public reply and reached platform state. -/
theorem sealing_node (pending : PqxdhRecordLiftProtocol.Sealing n)
    (reserve : Nat → StateT Platform ProbComp (core.result.Result Unit Failure))
    (after : Option RawCtxSourceSend.Encrypted → Platform → OracleComp (ServiceSpec n) A)
    (before : Platform) (tag : PqxdhDeploymentInterface.FrameTag)
    (later : ∀output state,HasTails Platform Failure (after output state)) :
    HasTails Platform Failure (((ServiceSpec n).query (.sealing pending) : OracleComp (ServiceSpec n) _) >>= continued reserve after before tag) := by
  rw [query_tails]
  exact ⟨⟨reserve,after,before,tag,rfl⟩,fun reply => continued_tails reserve after before tag reply later⟩
/-- Every literal reached source prefix retains the original syntactic tail property. -/
theorem reach (service : QueryImpl (ServiceSpec n) (StateT (PqxdhRecordLiftIdeal.CtxPrivate n) ProbComp))
    {initial work : OracleComp (ServiceSpec n) A} {before state : PqxdhRecordLiftIdeal.CtxPrivate n}
    {past firstPast : List (PqxdhRecordLiftWorldCompiler.Label n)} (source : HasTails Platform Failure initial)
    (reached : PqxdhRecordFactsPrivateCacheSource.Reach service initial before firstPast work state past) :
    HasTails Platform Failure work := by
  induction reached with
  | initial => exact source
  | step prior called ih => rw [query_tails] at ih;exact ih.2 _
/-- The reached seal's future is its original publication/reserve followed by the same callback. -/
theorem sealing_tail (service : QueryImpl (ServiceSpec n) (StateT (PqxdhRecordLiftIdeal.CtxPrivate n) ProbComp))
    {initial : OracleComp (ServiceSpec n) A} {before state : PqxdhRecordLiftIdeal.CtxPrivate n}
    {past firstPast : List (PqxdhRecordLiftWorldCompiler.Label n)} (source : HasTails Platform Failure initial)
    (pending : PqxdhRecordLiftProtocol.Sealing n) (next : Option RawCtxSourceSend.Encrypted → OracleComp (ServiceSpec n) A)
    (reached : PqxdhRecordFactsPrivateCacheSource.Reach service initial before firstPast
      (((ServiceSpec n).query (.sealing pending) : OracleComp (ServiceSpec n) _) >>= next) state past) : Head Platform Failure (.sealing pending) next := by
  have shape := reach service source reached
  rw [query_tails] at shape
  exact shape.1
end BeaconcryptCore.Computational.RegistrationNativePlatformOriginSourceTails

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOriginSourceTails.bind' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOriginSourceTails.bind

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOriginSourceTails.zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOriginSourceTails.zero

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOriginSourceTails.reach' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOriginSourceTails.reach

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOriginSourceTails.sealing_tail' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOriginSourceTails.sealing_tail

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOriginSourceTails.sealing_node' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOriginSourceTails.sealing_node

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOriginSourceTails.map' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOriginSourceTails.map

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOriginSourceTails.nonsealing' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOriginSourceTails.nonsealing
