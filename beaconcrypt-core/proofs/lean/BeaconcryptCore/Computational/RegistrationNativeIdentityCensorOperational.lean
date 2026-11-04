-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorCompiler

/-! Every suppressed attempt is represented by a public handle/message marker. The executable EUF interpreter answers that marker with its known placeholder and performs no challenger call; a separate private source interpreter can retain the actual canonical attempt at that same chronological position. Internal hash markers retain only the public framing outside the selected64-byte signature window. Erasing these markers recovers the checked executable censor exactly. No complete original-source realization is assumed or claimed here. -/
open OracleComp OracleSpec
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityCensorOperational
open RegistrationNativeIdentityCensorCompiler (Mode HashInput)
open PqxdhEd25519EufCma (Ed25519Signature)
variable {Value : Type}
abbrev Old := RegistrationNativeIdentityCensorCompiler.Spec
abbrev Source := RegistrationNativePlatformIdentityCtxCompiler.Spec

inductive Marker where
  | omitted (handle : Nat) (message : Pqxdh.Bytes)
  | template (handle : Nat) (message : Option Pqxdh.Bytes) (leading trailing : Pqxdh.Bytes)

def Reply : Marker → Type
  | .omitted _ _ => Option Ed25519Signature
  | .template _ _ _ _ => CtxRomAuth.CtxDigest × Nat

abbrev MarkerSpec : OracleSpec Marker := Reply
abbrev Spec := Old + MarkerSpec

def embed : QueryImpl Old (OracleComp Spec) := fun query => Spec.query (.inl query)

def promote (work : StateT Mode (OracleComp Old) Value) : StateT Mode (OracleComp Spec) Value :=
  fun before => simulateQ embed (work.run before)

/-- The E-side marker interpreter receives neither a selected seed nor canonical signature. -/
def erase (placeholder : Ed25519Signature) : QueryImpl Spec (OracleComp Old)
  | .inl query => Old.query query
  | .inr (.omitted _ _) => pure (some placeholder)
  | .inr (.template _ message _ _) => Old.query (.inr ⟨message, none⟩)

def signing (selected : Nat) (handle : Nat) (message : Pqxdh.Bytes) :
    StateT Mode (OracleComp Spec) (Option Ed25519Signature) := do
  promote (RegistrationNativeIdentityCensorCompiler.prepare selected handle message)
  let before ← get
  if handle = selected ∧ before.target = some message then StateT.lift (Spec.query (.inr (.omitted handle message)))
  else StateT.lift (embed (.inl (.inl (.inl (.inl (.inr (.service handle (.sign message))))))))

/-- The original source transcript's selected one-time signature occupies bytes4140 through4203. -/
def parts (bytes : Pqxdh.Bytes) : Pqxdh.Bytes × Pqxdh.Bytes := (bytes.take 4140, bytes.drop 4204)

def implementation (selected : Nat) (placeholder : Ed25519Signature) : QueryImpl Source (StateT Mode (OracleComp Spec))
  | .inl (.inl (.inr (.service handle (.sign message)))) => signing selected handle message
  | .inr bytes => fun before =>
      match (RegistrationNativeIdentityCensorCompiler.hashInput before bytes).input with
      | some _ => (promote (RegistrationNativeIdentityCensorCompiler.implementation selected placeholder (.inr bytes))).run before
      | none => do
          let reply ← Spec.query (.inr (.template selected before.target (parts bytes).1 (parts bytes).2))
          pure (reply, before)
  | query => promote (RegistrationNativeIdentityCensorCompiler.implementation selected placeholder query)

private theorem round_trip (placeholder : Ed25519Signature) (work : OracleComp Old Value) :
    simulateQ (erase placeholder) (simulateQ embed work) = work := by
  induction work using OracleComp.inductionOn with
  | pure value => rfl
  | query_bind query next ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, embed, erase]
    exact congrArg (fun continued => (Old.query query : OracleComp Old _) >>= continued) (funext ih)

private theorem promote_erase (placeholder : Ed25519Signature) (work : StateT Mode (OracleComp Old) Value) (before : Mode) :
    simulateQ (erase placeholder) ((promote work).run before) = work.run before :=
  round_trip placeholder _

private theorem hash_run (selected : Nat) (placeholder : Ed25519Signature) (bytes : Pqxdh.Bytes) (before : Mode) :
    (implementation selected placeholder (.inr bytes)).run before =
      (match (RegistrationNativeIdentityCensorCompiler.hashInput before bytes).input with
      | some _ => (promote (RegistrationNativeIdentityCensorCompiler.implementation selected placeholder (.inr bytes))).run before
      | none => do
          let reply ← (Spec.query (.inr (.template selected before.target (parts bytes).1 (parts bytes).2)) : OracleComp Spec _)
          pure (reply, before)) := rfl

private theorem lift_run {S A : Type} {m : Type → Type} [Monad m] (work : m A) (before : S) :
    (StateT.lift work : StateT S m A).run before = (do let value ← work; pure (value, before)) := rfl

private theorem signing_erase (selected : Nat) (placeholder : Ed25519Signature) (handle : Nat) (message : Pqxdh.Bytes) (before : Mode) :
    simulateQ (erase placeholder) ((signing selected handle message).run before) =
      (RegistrationNativeIdentityCensorCompiler.signing selected placeholder handle message).run before := by
  simp only [signing, RegistrationNativeIdentityCensorCompiler.signing, StateT.run_bind, simulateQ_bind, promote_erase]
  apply bind_congr
  intro result
  simp only [StateT.run_get, pure_bind, simulateQ_pure]
  split_ifs
  · simp only [lift_run, simulateQ_bind, simulateQ_spec_query, erase, pure_bind, simulateQ_pure, StateT.run_pure]
  · simp only [lift_run, simulateQ_bind, simulateQ_spec_query, embed, erase,
      RegistrationNativeIdentityCensorCompiler.protocol, simulateQ_pure]

/-- Public operational markers preserve the entire checked E query, reply and local Mode state after their zero-challenger-call interpretation. -/
theorem query (selected : Nat) (placeholder : Ed25519Signature) (request : Source.Domain) (before : Mode) :
    simulateQ (erase placeholder) ((implementation selected placeholder request).run before) =
      (RegistrationNativeIdentityCensorCompiler.implementation selected placeholder request).run before := by
  cases request with
  | inl query => cases query with
    | inr report => exact round_trip placeholder _
    | inl query => cases query with
      | inl coin => exact round_trip placeholder _
      | inr query => cases query with
        | create | reveal handle => exact round_trip placeholder _
        | service handle request => cases request with
          | staticDh peer => exact round_trip placeholder _
          | sign message => exact signing_erase selected placeholder handle message before
  | inr bytes =>
    cases routed : (RegistrationNativeIdentityCensorCompiler.hashInput before bytes).input with
    | some input =>
      rw [hash_run, routed]
      exact promote_erase placeholder _ _
    | none =>
      rw [hash_run, routed]
      have descriptor : RegistrationNativeIdentityCensorCompiler.hashInput before bytes = ⟨before.target, none⟩ := by
        cases described : RegistrationNativeIdentityCensorCompiler.hashInput before bytes with
        | mk message input =>
          have same : message = before.target := congrArg HashInput.message described.symm
          cases same
          simp only [described] at routed
          cases routed
          rfl
      simp only [simulateQ_bind, simulateQ_spec_query, erase, simulateQ_pure]
      change (do
        let reply ← (Old.query (.inr ⟨before.target, none⟩) : OracleComp Old _)
        pure (reply, before)) = (do
        let reply ← (Old.query (.inr (RegistrationNativeIdentityCensorCompiler.hashInput before bytes)) : OracleComp Old _)
        pure (reply, {before with knownInputs := match (RegistrationNativeIdentityCensorCompiler.hashInput before bytes).input with
          | none => before.knownInputs
          | some input => before.knownInputs ++ [input]}))
      rw [descriptor]

/-- Every adaptive source continuation has exactly the same executable censor after erasure; every repeated omission remains present as an operational marker before erasure. -/
theorem program (selected : Nat) (placeholder : Ed25519Signature) (work : OracleComp Source Value) (before : Mode) :
    simulateQ (erase placeholder) ((simulateQ (implementation selected placeholder) work).run before) =
      (simulateQ (RegistrationNativeIdentityCensorCompiler.implementation selected placeholder) work).run before := by
  induction work using OracleComp.inductionOn generalizing before with
  | pure value => rfl
  | query_bind request next ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
    rw [query selected placeholder request before]
    exact bind_congr (fun result => ih result.1 result.2)

end BeaconcryptCore.Computational.RegistrationNativeIdentityCensorOperational
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorOperational.query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorOperational.query
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorOperational.program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorOperational.program
