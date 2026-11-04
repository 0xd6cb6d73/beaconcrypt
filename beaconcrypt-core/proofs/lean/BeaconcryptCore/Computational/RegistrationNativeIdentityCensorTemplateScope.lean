-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorOperational
open OracleComp OracleSpec
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityCensorTemplateScope
open RegistrationNativeIdentityCensorOperational (Spec Old Source embed promote implementation)
open RegistrationNativeIdentityCensorCompiler (Mode)
open PqxdhEd25519EufCma (Ed25519Signature)
variable {A : Type}

def Allowed : Spec.Domain → Prop
  | .inl (.inr hash) => hash.input.isSome = true
  | .inr (.template _ _ leading _) => leading.length = 4140
  | _ => True


private theorem prepare (selected handle : Nat) (message : Pqxdh.Bytes) (mode : Mode) :
    ((promote (RegistrationNativeIdentityCensorCompiler.prepare selected handle message)).run mode).AllQueriesSatisfy Allowed := by
  unfold promote RegistrationNativeIdentityCensorCompiler.prepare
  dsimp only [StateT.run]
  split
  · split
    · simp only [simulateQ_bind,RegistrationNativeIdentityCensorCompiler.select,simulateQ_spec_query,embed]
      apply allQueriesSatisfy_bind
      · exact (allQueriesSatisfy_query_iff _ _).mpr trivial
      · intro chosen
        cases chosen with
        | false =>
          simp only [Bool.false_eq_true,ite_false,simulateQ_pure]
          exact allQueriesSatisfy_pure _ _
        | true =>
          simp only [ite_true,simulateQ_bind,RegistrationNativeIdentityCensorCompiler.inspect,simulateQ_spec_query,embed]
          apply allQueriesSatisfy_bind
          · exact (allQueriesSatisfy_query_iff _ _).mpr trivial
          · intro inspected
            exact allQueriesSatisfy_pure _ _
    · simp only [pure_bind]
      exact allQueriesSatisfy_pure _ _
  · simp only [simulateQ_pure]
    exact allQueriesSatisfy_pure _ _


private theorem lift_safe (work : OracleComp Spec A) (safe : work.AllQueriesSatisfy Allowed) (mode : Mode) :
    ((StateT.lift work : StateT Mode (OracleComp Spec) A).run mode).AllQueriesSatisfy Allowed := by
  change (do let reply ← work; pure (reply,mode)).AllQueriesSatisfy Allowed
  exact allQueriesSatisfy_bind safe (fun _ => allQueriesSatisfy_pure _ _)

private theorem protocol (query : PqxdhJointPhase1Reports.ProtocolSpec.Domain) (mode : Mode) :
    ((promote (StateT.lift (RegistrationNativeIdentityCensorCompiler.protocol query))).run mode).AllQueriesSatisfy Allowed := by
  change (simulateQ embed (do let reply ← RegistrationNativeIdentityCensorCompiler.protocol query; pure (reply,mode))).AllQueriesSatisfy Allowed
  rw [simulateQ_bind]
  apply allQueriesSatisfy_bind
  · simp only [RegistrationNativeIdentityCensorCompiler.protocol,simulateQ_spec_query,embed]
    exact (allQueriesSatisfy_query_iff _ _).mpr trivial
  · intro reply
    exact allQueriesSatisfy_pure _ _

private theorem signing (selected handle : Nat) (message : Pqxdh.Bytes) (mode : Mode) :
    ((RegistrationNativeIdentityCensorOperational.signing selected handle message).run mode).AllQueriesSatisfy Allowed := by
  rw [RegistrationNativeIdentityCensorOperational.signing,StateT.run_bind]
  apply allQueriesSatisfy_bind (prepare selected handle message mode)
  intro prepared
  simp only [StateT.run_bind,StateT.run_get,pure_bind]
  split
  · apply lift_safe
    exact (allQueriesSatisfy_query_iff _ _).mpr trivial
  · apply lift_safe
    simp only [embed]
    exact (allQueriesSatisfy_query_iff _ _).mpr trivial


private theorem hash (selected : Nat) (placeholder : Ed25519Signature) (bytes : Pqxdh.Bytes) (mode : Mode) :
    ((implementation selected placeholder (.inr bytes)).run mode).AllQueriesSatisfy Allowed := by
  change (match (RegistrationNativeIdentityCensorCompiler.hashInput mode bytes).input with
    | some _ => simulateQ embed ((RegistrationNativeIdentityCensorCompiler.implementation selected placeholder (.inr bytes)).run mode)
    | none => do
      let reply ← (Spec.query (.inr (.template selected mode.target
        (RegistrationNativeIdentityCensorOperational.parts bytes).1 (RegistrationNativeIdentityCensorOperational.parts bytes).2)) : OracleComp Spec (CtxRomAuth.CtxDigest × Nat))
      pure (reply,mode)).AllQueriesSatisfy Allowed
  cases described : (RegistrationNativeIdentityCensorCompiler.hashInput mode bytes).input with
  | none =>
    apply allQueriesSatisfy_bind
    · apply (allQueriesSatisfy_query_iff _ _).mpr
      have width := ((RegistrationNativeIdentityCensorCompiler.hash_token_iff mode bytes).mp described).2
      simp only [Allowed,RegistrationNativeIdentityCensorOperational.parts,List.length_take]
      omega
    · intro reply
      exact allQueriesSatisfy_pure _ _
  | some input =>
    change (simulateQ embed ((RegistrationNativeIdentityCensorCompiler.implementation selected placeholder (.inr bytes)).run mode)).AllQueriesSatisfy Allowed
    unfold RegistrationNativeIdentityCensorCompiler.implementation
    dsimp only [StateT.run]
    rw [simulateQ_bind]
    apply allQueriesSatisfy_bind
    · rw [simulateQ_spec_query]
      simp only [embed]
      apply (allQueriesSatisfy_query_iff _ _).mpr
      change (RegistrationNativeIdentityCensorCompiler.hashInput mode bytes).input.isSome = true
      rw [described]
      rfl
    · intro answer
      exact allQueriesSatisfy_pure _ _

/-- Every marker emitted by the actual operational lowering is either a known public hash or an exact-width hidden template; malformed hidden frames are never emitted. -/
theorem query (selected : Nat) (placeholder : Ed25519Signature) (request : Source.Domain) (mode : Mode) :
    ((implementation selected placeholder request).run mode).AllQueriesSatisfy Allowed := by
  rcases request with ((coin | request) | report) | bytes
  · exact protocol _ mode
  · cases request with
    | create | reveal handle => exact protocol _ mode
    | service handle request => cases request with
      | staticDh peer => exact protocol _ mode
      | sign message => exact signing selected handle message mode
  · exact protocol _ mode
  · exact hash selected placeholder bytes mode

/-- The same executable syntax restriction is preserved through every adaptive source program and its actual mode updates. -/
theorem program (selected : Nat) (placeholder : Ed25519Signature) (work : OracleComp Source A) (mode : Mode) :
    ((simulateQ (implementation selected placeholder) work).run mode).AllQueriesSatisfy Allowed := by
  induction work using OracleComp.inductionOn generalizing mode with
  | pure value => exact allQueriesSatisfy_pure _ _
  | query_bind request next ih =>
    rw [simulateQ_bind,simulateQ_spec_query,StateT.run_bind]
    exact allQueriesSatisfy_bind (query selected placeholder request mode) (fun result => ih result.1 result.2)

end BeaconcryptCore.Computational.RegistrationNativeIdentityCensorTemplateScope

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorTemplateScope.query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorTemplateScope.query

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorTemplateScope.program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorTemplateScope.program
