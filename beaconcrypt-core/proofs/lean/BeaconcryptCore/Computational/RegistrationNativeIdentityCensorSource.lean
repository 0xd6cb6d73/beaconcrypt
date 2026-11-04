-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorOperational
import BeaconcryptCore.Computational.RegistrationNativeIdentityPublicHashTemplate
import BeaconcryptCore.Computational.RegistrationNativeIdentityHistoryReserved

/-! The private operational interpretation retains the original generated-key table and every canonical suppressed signing attempt. Public template framing and the actually returned private signature reconstruct the reached physical CTX address. This private state is not captured by the executable EUF adversary; its marker erasure uses only a known placeholder. The whole real/censored callback coupling remains a separate proof. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityCensorSource
open RegistrationNativeIdentityCensorOperational (Spec Marker)
open PqxdhEd25519EufCma (Ed25519Signature)
open PqxdhDynamicIdentityPool (SourceState)

structure State where
  pool : SourceState
  hash : RegistrationNativePlatformCtxBackend.State
  target : Option Pqxdh.Bytes := none
  canonical : Option Ed25519Signature := none
  framing : Option (Pqxdh.Bytes × Pqxdh.Bytes) := none

def zeroSignature : Ed25519Signature := ⟨List.replicate 64 0, by simp⟩

def address (before : State) (leading trailing : Pqxdh.Bytes) : Pqxdh.Bytes :=
  leading ++ (before.canonical.getD zeroSignature).toList ++ trailing

noncomputable def physical (input : Pqxdh.Bytes) : StateT State ProbComp (CtxRomAuth.CtxDigest × Nat) := fun before =>
  (fun result => (result.1, {before with hash := result.2})) <$>
    (RegistrationNativePlatformCtxBackend.physical input).run before.hash

def protocol (joint : PqxdhJointIdentity.Primitives) (query : PqxdhJointPhase1Reports.ProtocolSpec.Domain) :
    StateT State ProbComp (PqxdhJointPhase1Reports.ProtocolSpec.Range query) := fun before =>
  (fun result => (result.1, {before with pool := result.2})) <$>
    (RegistrationNativeIdentityMainSource.implementation joint query).run before.pool

def select (selected : Nat) (message : Pqxdh.Bytes) : StateT State ProbComp Bool := fun before =>
  if before.target = none ∧ message ∉ PqxdhJointIdentity.signedMessages
      (RegistrationNativeIdentityHistory.history selected before.pool.transcript) then
    pure (true, {before with target := some message, canonical := none, framing := none})
  else pure (false, before)

def omitted (joint : PqxdhJointIdentity.Primitives) (selected handle : Nat) (message : Pqxdh.Bytes) :
    StateT State ProbComp (Option Ed25519Signature) := fun before =>
  (fun result => (result.1, {before with
    pool := result.2
    canonical := if handle = selected ∧ before.target = some message then result.1 else before.canonical})) <$>
      (RegistrationNativeIdentityMainSource.implementation joint (.inl (.inr (.service handle (.sign message))))).run before.pool

noncomputable def template (leading trailing : Pqxdh.Bytes) :
    StateT State ProbComp (CtxRomAuth.CtxDigest × Nat) := fun before =>
  (fun result => (result.1, {result.2 with framing := some (leading, trailing)})) <$>
    (physical (address before leading trailing)).run before

noncomputable def implementation (joint : PqxdhJointIdentity.Primitives) (selected : Nat) :
    QueryImpl Spec (StateT State ProbComp)
  | .inl (.inl (.inl (.inl query))) => protocol joint query
  | .inl (.inl (.inl (.inr message))) => select selected message
  | .inl (.inl (.inr _)) => pure ()
  | .inl (.inr described) => fun before =>
      physical (match described.input with
        | some input => input
        | none => match before.framing with
          | some (leading, trailing) => address before leading trailing
          | none => []) before
  | .inr (.omitted handle message) => omitted joint selected handle message
  | .inr (.template _ _ leading trailing) => template leading trailing

/-- This is a private joint source realization, not the executable EUF interpreter. It keeps canonical source observations but returns only the known placeholder on a suppressed call. -/
noncomputable def censored (joint : PqxdhJointIdentity.Primitives) (selected : Nat) (placeholder : Ed25519Signature) :
    QueryImpl Spec (StateT State ProbComp)
  | .inr (.omitted handle message) => do
      let _ ← omitted joint selected handle message
      pure (some placeholder)
  | query => implementation joint selected query

/-- A reached genuine row supplies its actual canonical signature and appends the literal original source service observation. Every suppressed retry is recorded at its current position. -/
theorem omitted_source (joint : PqxdhJointIdentity.Primitives) (selected : Nat) (message : Pqxdh.Bytes)
    (before : State) (seed : PqxdhJointIdentity.IdentitySeed)
    (found : before.pool.seeds[selected]? = some seed) (target : before.target = some message) :
    (omitted joint selected selected message).run before = pure (some (joint.sign seed message),
      {before with
        pool := PqxdhDynamicIdentityPool.record (.inr (.service selected (.sign message))) (some (joint.sign seed message)) before.pool
        canonical := some (joint.sign seed message)}) := by
  simp only [omitted, RegistrationNativeIdentityMainSource.implementation, PqxdhDynamicIdentityPool.lazyImpl,
    PqxdhDynamicIdentityPool.poolImpl, StateT.run, found, Option.map_some, PqxdhJointIdentity.primitiveReply,
    target, and_self, ite_true, map_pure]

/-- A template marker performs the literal physical query with its actual per-call draw charge, full cache and chronological input journal. -/
theorem template_source (leading trailing : Pqxdh.Bytes) (signature : Ed25519Signature)
    (before : State) (stored : before.canonical = some signature) :
    (template leading trailing).run before =
      (fun result => (result.1, {before with hash := result.2, framing := some (leading, trailing)})) <$>
        (RegistrationNativePlatformCtxBackend.physical (leading ++ signature.toList ++ trailing)).run before.hash := by
  simp only [template, physical, StateT.run, address, stored, Option.getD_some, Functor.map_map]

/-- The original source fingerprint/hash continuation derives this exact private physical address from its actual retained one-time attachment. -/
theorem actual_template (pending : registration.BeaconFingerprint) (digest : Std.Array U8 64#usize)
    (signature : Ed25519Signature) (message : Pqxdh.Bytes)
    (attached : PqxdhRefinement.absBytes pending.state.one_time_key = signature.toList ++ message)
    (before : State) (stored : before.canonical = some signature) :
    ∃ next request, pending.resume (.Some digest) = .ok (.HashRequested next) ∧ next.request = .ok request ∧
      address before (RegistrationNativeIdentityCensorOperational.parts (BeaconcryptCore.Refinement.RegistrationInputs.hashBytes request)).1
        (RegistrationNativeIdentityCensorOperational.parts (BeaconcryptCore.Refinement.RegistrationInputs.hashBytes request)).2 =
          BeaconcryptCore.Refinement.RegistrationInputs.hashBytes request := by
  obtain ⟨next, request, resumed, requested, _framing, literal⟩ :=
    RegistrationNativeIdentityPublicHashTemplate.source pending digest signature message attached
  refine ⟨next, request, resumed, requested, ?_⟩
  simpa only [address, stored, Option.getD_some, RegistrationNativeIdentityCensorOperational.parts,
    RegistrationNativeIdentityPublicHashTemplate.parts] using literal.symm

/-- Source and private-censored calls retain the very same canonical service receipt and pool state; only the reply delivered into the frontend continuation changes. -/
theorem censored_omitted (joint : PqxdhJointIdentity.Primitives) (selected : Nat) (placeholder : Ed25519Signature)
    (message : Pqxdh.Bytes) (before : State) (seed : PqxdhJointIdentity.IdentitySeed)
    (found : before.pool.seeds[selected]? = some seed) (target : before.target = some message) :
    (censored joint selected placeholder (.inr (.omitted selected message))).run before = pure (some placeholder,
      {before with
        pool := PqxdhDynamicIdentityPool.record (.inr (.service selected (.sign message))) (some (joint.sign seed message)) before.pool
        canonical := some (joint.sign seed message)}) := by
  simp only [censored, StateT.run_bind, omitted_source joint selected message before seed found target,
    pure_bind, StateT.run_pure]

end BeaconcryptCore.Computational.RegistrationNativeIdentityCensorSource
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorSource.omitted_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorSource.omitted_source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorSource.template_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorSource.template_source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorSource.actual_template' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorSource.actual_template
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorSource.censored_omitted' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorSource.censored_omitted
