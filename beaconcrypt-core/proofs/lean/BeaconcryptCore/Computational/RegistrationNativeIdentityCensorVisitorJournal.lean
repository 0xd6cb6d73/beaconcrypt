-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorCanonicalSource
import BeaconcryptCore.Computational.RegistrationNativeIdentityUnissuedProjection
/-! A complete original chronological execution has exactly the same public before-accept observation as its absorbing visitor. Every original later callback remains in the full execution; only its unused output is integrated out by genuine losslessness. -/
open OracleComp OracleSpec CoreModels
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityCensorVisitorJournal
open RegistrationNativeRawAdapter (TypedSpec)
open RegistrationNativeStageTrace (Call)
open RegistrationNativeIdentityCensorPacketClient (Found)
variable {S A : Type}
abbrev Packet := beaconcrypt_core.registration.InitPacket

def fold (target : S → Option Pqxdh.Bytes)
    (published : (query : TypedSpec.Domain) → TypedSpec.Range query → S → Bool) (accept : Nat) :
    Nat → List (Call TypedSpec S) → Option Found
  | _cursor,[] => none
  | cursor,call::rest =>
      match RegistrationNativeIdentityCensorAdaptivePostselection.attempt accept call.query cursor with
      | some packet => (target call.before).map (fun message => (message,packet))
      | none => if published call.query call.reply call.after then none else
          fold target published accept (cursor+if RegistrationNativeIdentityCensorPublicClient.IsAccept call.query then 1 else 0) rest

noncomputable def visit (implementation : QueryImpl TypedSpec (StateT S ProbComp))
    (target : S → Option Pqxdh.Bytes)
    (published : (query : TypedSpec.Domain) → TypedSpec.Range query → S → Bool)
    (accept : Nat) (work : OracleComp TypedSpec A) : S → Nat → ProbComp (Option Found) :=
  work.recOn (fun _ _before _cursor => pure none)
    (fun query _next continued before cursor =>
      match RegistrationNativeIdentityCensorAdaptivePostselection.attempt accept query cursor with
      | some packet => pure ((target before).map (fun message => (message,packet)))
      | none => do
          let result ← (implementation query).run before
          if published query result.1 result.2 then pure none else
            continued result.1 result.2 (cursor+if RegistrationNativeIdentityCensorPublicClient.IsAccept query then 1 else 0))

noncomputable def full (implementation : QueryImpl TypedSpec (StateT S ProbComp)) (work : OracleComp TypedSpec A)
    (before : S) := (simulateQ (RegistrationNativeStageTrace.handler implementation) work).run (before,[])

private theorem prepend (implementation : QueryImpl TypedSpec (StateT S ProbComp)) (work : OracleComp TypedSpec A)
    (before : S) (leading : List (Call TypedSpec S)) :
    (fun result => (result.1,(result.2.1,leading++result.2.2))) <$> full implementation work before =
      (simulateQ (RegistrationNativeStageTrace.handler implementation) work).run (before,leading) := by
  have law := OracleComp.map_run_simulateQ_eq_of_query_map_eq
    (RegistrationNativeStageTrace.handler implementation) (RegistrationNativeStageTrace.handler implementation)
    (fun current => (current.1,leading++current.2)) (fun query current => by
      simp only [RegistrationNativeStageTrace.handler,StateT.run,Functor.map_map,Prod.map_def,id_eq,List.append_assoc]) work (before,[])
  simpa only [full,List.append_nil,Prod.map_def,id_eq] using law

private theorem full_step (implementation : QueryImpl TypedSpec (StateT S ProbComp)) (query : TypedSpec.Domain)
    (next : TypedSpec.Range query → OracleComp TypedSpec A) (before : S) :
    full implementation (TypedSpec.query query >>= next) before = (do
      let reached ← (implementation query).run before
      let result ← full implementation (next reached.1) reached.2
      pure (result.1,(result.2.1,(⟨query,before,reached.1,reached.2⟩ : Call TypedSpec S)::result.2.2))) := by
  unfold full
  rw [simulateQ_bind,simulateQ_spec_query,StateT.run_bind]
  simp only [RegistrationNativeStageTrace.handler,StateT.run,bind_map_left,List.nil_append]
  apply bind_congr
  intro reached
  have law := (prepend implementation (next reached.1) reached.2 [⟨query,before,reached.1,reached.2⟩]).symm
  simpa only [full,StateT.run,map_eq_bind_pure_comp,Function.comp_def,List.singleton_append] using law

private theorem visit_step (implementation : QueryImpl TypedSpec (StateT S ProbComp))
    (target : S → Option Pqxdh.Bytes) (published : (query : TypedSpec.Domain) → TypedSpec.Range query → S → Bool)
    (accept : Nat) (query : TypedSpec.Domain) (next : TypedSpec.Range query → OracleComp TypedSpec A) (before : S) (cursor : Nat) :
    visit implementation target published accept (TypedSpec.query query >>= next) before cursor =
      (match RegistrationNativeIdentityCensorAdaptivePostselection.attempt accept query cursor with
      | some packet => pure ((target before).map (fun message => (message,packet)))
      | none => do
          let reached ← (implementation query).run before
          if published query reached.1 reached.2 then pure none else
            visit implementation target published accept (next reached.1) reached.2
              (cursor+if RegistrationNativeIdentityCensorPublicClient.IsAccept query then 1 else 0)) := rfl

/-- The complete original journal and literal public visitor have equal distributions; ignored original suffixes are integrated out, never replaced by a support implication. -/
theorem source (implementation : QueryImpl TypedSpec (StateT S ProbComp))
    (target : S → Option Pqxdh.Bytes) (published : (query : TypedSpec.Domain) → TypedSpec.Range query → S → Bool)
    (accept : Nat) (work : OracleComp TypedSpec A) (before : S) (cursor : Nat) :
    (fun result => fold target published accept cursor result.2.2) <$> full implementation work before =ᵈ
      visit implementation target published accept work before cursor := by
  induction work using OracleComp.inductionOn generalizing before cursor with
  | pure value => simp only [full,simulateQ_pure,StateT.run_pure,map_pure,fold,visit];rfl
  | query_bind query next ih =>
      rw [full_step,visit_step]
      simp only [map_bind,bind_pure_comp,Functor.map_map]
      cases chosen : RegistrationNativeIdentityCensorAdaptivePostselection.attempt accept query cursor with
      | some packet =>
          simp only [chosen,fold]
          exact (EvalDistEq.bind_right ((implementation query).run before) (fun reached =>
            EvalDistEq.map_const (full implementation (next reached.1) reached.2) ((target before).map (fun message => (message,packet))))).trans
              (EvalDistEq.bind_const ((implementation query).run before) (pure ((target before).map (fun message => (message,packet)))))
      | none =>
          simp only [chosen,fold]
          apply EvalDistEq.bind_right
          intro reached
          cases stopped : published query reached.1 reached.2 with
          | true => simpa only [stopped,ite_true] using EvalDistEq.map_const (full implementation (next reached.1) reached.2) (none : Option Found)
          | false => simpa only [stopped,Bool.false_eq_true,ite_false] using ih reached.1 reached.2 (cursor+if RegistrationNativeIdentityCensorPublicClient.IsAccept query then 1 else 0)

end BeaconcryptCore.Computational.RegistrationNativeIdentityCensorVisitorJournal

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorVisitorJournal.source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorVisitorJournal.source
