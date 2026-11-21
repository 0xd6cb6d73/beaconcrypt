-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorForwardScope

/-! Literal postselection lowering emits no new prefix scan and annotates every public/template hash with its same retained target. All source replies and full Mode state remain unchanged. -/
open OracleComp OracleSpec
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityCensorTargetAnnotations
open RegistrationNativeIdentityCensorOperational (Spec Source promote embed implementation)
open RegistrationNativeIdentityCensorCompiler (Mode)
open PqxdhEd25519EufCma (Ed25519Signature)
variable {A : Type}

def ProtocolAllowed (_selected : Nat) (_target : Pqxdh.Bytes) (_request : PqxdhJointPhase1Reports.ProtocolSpec.Domain) : Prop := True

/-- Every postselection hash is annotated by the same public target and no prefix scan is repeated. -/
def Allowed (_selected : Nat) (target : Pqxdh.Bytes) : Spec.Domain → Prop
  | .inl (.inl (.inr _)) => False
  | .inl (.inr described) => described.message = some target
  | .inr (.template _ message _ _) => message = some target
  | _ => True

private theorem bind_safe {B : Type} (work : OracleComp Spec A) (next : A → OracleComp Spec B)
    (selected : Nat) (target : Pqxdh.Bytes) (safe : work.AllQueriesSatisfy (Allowed selected target))
    (continued : ∀ result ∈ support work, (next result).AllQueriesSatisfy (Allowed selected target)) :
    (work >>= next).AllQueriesSatisfy (Allowed selected target) := by
  induction work using OracleComp.inductionOn with
  | pure value =>
    exact continued value (by simp only [mem_support_pure_iff])
  | query_bind request rest ih =>
    obtain ⟨first, later⟩ := (allQueriesSatisfy_query_bind_iff _ _ _).mp safe
    rw [bind_assoc, allQueriesSatisfy_query_bind_iff]
    refine ⟨first, fun answer => ih answer (later answer) ?_⟩
    intro result reached
    apply continued result
    rw [mem_support_bind_iff]
    exact ⟨answer, by simp only [support_query, Set.mem_univ], reached⟩

private theorem lifted (selected : Nat) (target : Pqxdh.Bytes) (query : Spec.Domain)
    (safe : Allowed selected target query) (mode : Mode) (held : mode.target = some target) :
    ((StateT.lift (Spec.query query) : StateT Mode (OracleComp Spec) _).run mode).AllQueriesSatisfy (Allowed selected target) ∧
      ∀ result ∈ support ((StateT.lift (Spec.query query) : StateT Mode (OracleComp Spec) _).run mode), result.2.target = some target := by
  constructor
  · exact allQueriesSatisfy_bind ((allQueriesSatisfy_query_iff _ _).mpr safe) (fun _ => allQueriesSatisfy_pure _ _)
  · intro result reached
    change result ∈ support (do let answer ← (Spec.query query : OracleComp Spec _); pure (answer, mode)) at reached
    rw [bind_pure_comp, support_map] at reached
    obtain ⟨answer, _possible, rfl⟩ := reached
    exact held

private theorem signing (selected handle : Nat) (message target : Pqxdh.Bytes) (mode : Mode)
    (held : mode.target = some target) :
    ((RegistrationNativeIdentityCensorOperational.signing selected handle message).run mode).AllQueriesSatisfy (Allowed selected target) ∧
      ∀ result ∈ support ((RegistrationNativeIdentityCensorOperational.signing selected handle message).run mode), result.2.target = some target := by
  have prepared := RegistrationNativeIdentityCensorCompiler.prepare_selected selected handle message target mode held
  have promoted : ((promote (RegistrationNativeIdentityCensorCompiler.prepare selected handle message)).run mode) =
      pure ((), if handle = selected ∧ RegistrationNativeIdentitySigningRole.oneTime message then
        {mode with active := mode.target == some message} else mode) := by
    change simulateQ embed ((RegistrationNativeIdentityCensorCompiler.prepare selected handle message).run mode) = _
    rw [prepared, simulateQ_pure]
  simp only [RegistrationNativeIdentityCensorOperational.signing, StateT.run_bind, promoted, pure_bind,
    StateT.run_get]
  split_ifs with eligible suppressed suppressed
  · exact lifted selected target (.inr (.omitted handle message)) trivial _ held
  · exact lifted selected target (.inl (.inl (.inl (.inl (.inl (.inr (.service handle (.sign message)))))))) trivial _ held
  · exact lifted selected target (.inr (.omitted handle message)) trivial _ held
  · exact lifted selected target (.inl (.inl (.inl (.inl (.inl (.inr (.service handle (.sign message)))))))) trivial _ held

private theorem protocol (selected : Nat) (target : Pqxdh.Bytes)
    (request : PqxdhJointPhase1Reports.ProtocolSpec.Domain) (safe : ProtocolAllowed selected target request)
    (mode : Mode) (held : mode.target = some target) :
    ((promote (StateT.lift (RegistrationNativeIdentityCensorCompiler.protocol request))).run mode).AllQueriesSatisfy (Allowed selected target) ∧
      ∀ result ∈ support ((promote (StateT.lift (RegistrationNativeIdentityCensorCompiler.protocol request))).run mode), result.2.target = some target := by
  have literal : (promote (StateT.lift (RegistrationNativeIdentityCensorCompiler.protocol request))).run mode =
      (StateT.lift (Spec.query (.inl (.inl (.inl (.inl request))))) : StateT Mode (OracleComp Spec) _).run mode := by
    change simulateQ embed (do let answer ← RegistrationNativeIdentityCensorCompiler.protocol request; pure (answer, mode)) = _
    simp only [simulateQ_bind, RegistrationNativeIdentityCensorCompiler.protocol, simulateQ_spec_query, embed, simulateQ_pure]
    rfl
  rw [literal]
  exact lifted selected target (.inl (.inl (.inl (.inl request)))) safe mode held

private theorem hash (selected : Nat) (placeholder : Ed25519Signature) (target bytes : Pqxdh.Bytes)
    (mode : Mode) (held : mode.target = some target) :
    ((implementation selected placeholder (.inr bytes)).run mode).AllQueriesSatisfy (Allowed selected target) ∧
      ∀ result ∈ support ((implementation selected placeholder (.inr bytes)).run mode), result.2.target = some target := by
  have run : (implementation selected placeholder (.inr bytes)).run mode =
      (match (RegistrationNativeIdentityCensorCompiler.hashInput mode bytes).input with
    | some _ => (promote (RegistrationNativeIdentityCensorCompiler.implementation selected placeholder (.inr bytes))).run mode
    | none => do
      let answer ← (Spec.query (.inr (.template selected mode.target (RegistrationNativeIdentityCensorOperational.parts bytes).1
        (RegistrationNativeIdentityCensorOperational.parts bytes).2)) : OracleComp Spec _)
      pure (answer, mode)) := rfl
  rw [run]
  cases described : (RegistrationNativeIdentityCensorCompiler.hashInput mode bytes).input with
  | none =>
    dsimp only
    exact lifted selected target (.inr (.template selected mode.target (RegistrationNativeIdentityCensorOperational.parts bytes).1
      (RegistrationNativeIdentityCensorOperational.parts bytes).2)) held mode held
  | some input =>
    dsimp only
    have literal : (promote (RegistrationNativeIdentityCensorCompiler.implementation selected placeholder (.inr bytes))).run mode =
        (StateT.lift (Spec.query (.inl (.inr (RegistrationNativeIdentityCensorCompiler.hashInput mode bytes)))) :
          StateT Mode (OracleComp Spec) _).run {mode with knownInputs := mode.knownInputs ++ [input]} := by
      change simulateQ embed (do
        let answer ← (RegistrationNativeIdentityCensorCompiler.Spec.query (.inr (RegistrationNativeIdentityCensorCompiler.hashInput mode bytes)) : OracleComp RegistrationNativeIdentityCensorCompiler.Spec _)
        pure (answer, {mode with knownInputs := match (RegistrationNativeIdentityCensorCompiler.hashInput mode bytes).input with
          | none => mode.knownInputs | some input => mode.knownInputs ++ [input]})) = _
      simp only [simulateQ_bind, simulateQ_spec_query, embed, simulateQ_pure, described]
      rfl
    rw [literal]
    exact lifted selected target (.inl (.inr (RegistrationNativeIdentityCensorCompiler.hashInput mode bytes))) held {mode with knownInputs := mode.knownInputs ++ [input]} held

/-- Every literal lowered query has the same public target on each hash and emits no prefix scan after selection, for every reply. -/
theorem query (selected : Nat) (placeholder : Ed25519Signature) (target : Pqxdh.Bytes)
    (request : Source.Domain) (mode : Mode) (held : mode.target = some target) :
    ((implementation selected placeholder request).run mode).AllQueriesSatisfy (Allowed selected target) ∧
      ∀ result ∈ support ((implementation selected placeholder request).run mode), result.2.target = some target := by
  rcases request with ((coin | request) | report) | bytes
  · exact protocol selected target (.inl (.inl coin)) trivial mode held
  · cases request with
    | create => exact protocol selected target (.inl (.inr .create)) trivial mode held
    | reveal handle => exact protocol selected target (.inl (.inr (.reveal handle))) trivial mode held
    | service handle request => cases request with
      | staticDh peer => exact protocol selected target (.inl (.inr (.service handle (.staticDh peer)))) trivial mode held
      | sign message => exact signing selected handle message target mode held
  · exact protocol selected target (.inr report) trivial mode held
  · exact hash selected placeholder target bytes mode held

/-- Every actual adaptive postselection source continuation retains exact target annotations and emits no prefix scan. -/
theorem program (selected : Nat) (placeholder : Ed25519Signature) (target : Pqxdh.Bytes)
    (work : OracleComp Source A) (mode : Mode) (held : mode.target = some target) :
    ((simulateQ (implementation selected placeholder) work).run mode).AllQueriesSatisfy (Allowed selected target) ∧
      ∀ result ∈ support ((simulateQ (implementation selected placeholder) work).run mode), result.2.target = some target := by
  induction work using OracleComp.inductionOn generalizing mode with
  | pure value =>
    simp only [simulateQ_pure, StateT.run_pure]
    refine ⟨allQueriesSatisfy_pure _ _, ?_⟩
    intro result reached
    simp only [mem_support_pure_iff] at reached
    cases reached
    exact held
  | query_bind request next ih =>
    rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
    have first := query selected placeholder target request mode held
    constructor
    · apply bind_safe _ _ selected target first.1
      intro result reached
      exact (ih result.1 result.2 (first.2 result reached)).1
    · intro result reached
      rw [mem_support_bind_iff] at reached
      obtain ⟨middle, called, continued⟩ := reached
      exact (ih middle.1 middle.2 (first.2 middle called)).2 result continued

end BeaconcryptCore.Computational.RegistrationNativeIdentityCensorTargetAnnotations

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorTargetAnnotations.query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorTargetAnnotations.query

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorTargetAnnotations.program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorTargetAnnotations.program
