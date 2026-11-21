-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateSelectorMessage
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorTargetSyncMain
/-! The only newly selected target in a source body is that body's original one-time signing operand. Every optional source reply, writer failure and persistent private state is retained. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityCensorTargetOperand
open RegistrationNativeIdentityCensorCompiler (Mode)
open PqxdhEd25519EufCma (Ed25519Signature)
open RegistrationNativePlatformIdentityCtxBundleMessageScope (UsesSourceMessage)
variable {A : Type}

def Fixed (fixed : Pqxdh.Bytes) (before : Mode) : Prop :=
  ∀ message, before.target = some message → message = fixed

private theorem simulated_support {I J : Type} {spec : OracleSpec I} {target : OracleSpec J}
    (impl : QueryImpl spec (OracleComp target)) (work : OracleComp spec A) (value : A)
    (reached : value ∈ support (simulateQ impl work)) : value ∈ support work := by
  induction work using OracleComp.inductionOn with
  | pure returned =>
      rw [simulateQ_pure] at reached
      obtain rfl := eq_of_mem_support_pure _ reached
      simp only [support_pure, Set.mem_singleton_iff]
  | query_bind query next ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, mem_support_bind_iff] at reached
    obtain ⟨reply, _queried, continued⟩ := reached
    rw [mem_support_bind_iff]
    exact ⟨reply, mem_support_query query reply, ih reply continued⟩

private theorem lift_state {B : Type} (work : OracleComp RegistrationNativeIdentityCensorOperational.Spec B)
    (mode : Mode) (result : B × Mode)
    (reached : result ∈ support ((StateT.lift work : StateT Mode (OracleComp RegistrationNativeIdentityCensorOperational.Spec) B).run mode)) :
    result.2 = mode := by
  change result ∈ support (do let reply ← work; pure (reply, mode)) at reached
  rw [mem_support_bind_iff] at reached
  obtain ⟨reply, _queried, returned⟩ := reached
  obtain rfl := eq_of_mem_support_pure _ returned
  rfl

private theorem constant_state {I : Type} {spec : OracleSpec I} {B : Type} (work : OracleComp spec B)
    (mode : Mode) (result : B × Mode)
    (reached : result ∈ support (do let reply ← work; pure (reply, mode))) : result.2 = mode := by
  rw [mem_support_bind_iff] at reached
  obtain ⟨reply, _queried, returned⟩ := reached
  obtain rfl := eq_of_mem_support_pure _ returned
  rfl


private theorem prepare (fixed : Pqxdh.Bytes) (selected handle : Nat) (message : Pqxdh.Bytes) (before : Mode)
    (allowed : RegistrationNativeIdentitySigningRole.oneTime message=true → message=fixed) (prior : Fixed fixed before)
    (result : Unit × Mode)
    (reached : result ∈ support ((RegistrationNativeIdentityCensorCompiler.prepare selected handle message).run before)) :
    Fixed fixed result.2 := by
  by_cases eligible : handle = selected ∧ RegistrationNativeIdentitySigningRole.oneTime message
  · simp only [RegistrationNativeIdentityCensorCompiler.prepare, StateT.run, eligible, and_self, ite_true] at reached
    split at reached
    · rw [mem_support_bind_iff] at reached
      obtain ⟨chosen, _selected, rest⟩ := reached
      cases chosen
      · simp only [Bool.false_eq_true, ite_false, mem_support_pure_iff] at rest
        cases rest
        exact prior
      · simp only [ite_true] at rest
        rw [mem_support_bind_iff] at rest
        obtain ⟨_answer, _inspected, returned⟩ := rest
        obtain rfl := eq_of_mem_support_pure _ returned
        intro target same
        have equal : message = target := Option.some.inj same
        exact equal.symm.trans (allowed eligible.2)
    · simp only [Bool.false_eq_true, ite_false, pure_bind, mem_support_pure_iff] at reached
      cases reached
      exact prior
  · simp only [RegistrationNativeIdentityCensorCompiler.prepare, StateT.run, eligible, ite_false, mem_support_pure_iff] at reached
    cases reached
    exact prior

private theorem signing_fixed (fixed : Pqxdh.Bytes) (selected handle : Nat) (message : Pqxdh.Bytes) (before : Mode)
    (allowed : RegistrationNativeIdentitySigningRole.oneTime message=true → message=fixed)
    (prior : Fixed fixed before) (result : Option Ed25519Signature × Mode)
    (reached : result ∈ support ((RegistrationNativeIdentityCensorOperational.signing selected handle message).run before)) :
    Fixed fixed result.2 := by
  rw [RegistrationNativeIdentityCensorOperational.signing, StateT.run_bind, mem_support_bind_iff] at reached
  obtain ⟨prepared, queried, rest⟩ := reached
  have original := simulated_support _ _ _ queried
  have tagged := prepare fixed selected handle message before allowed prior prepared original
  simp only [StateT.run_bind, StateT.run_get, pure_bind] at rest
  split at rest
  all_goals rw [lift_state _ _ _ rest]
  all_goals exact tagged
/-- Every literal operational source leaf selects only its same role-one-time source operand. -/
theorem query (fixed : Pqxdh.Bytes) (selected : Nat) (placeholder : PqxdhEd25519EufCma.Ed25519Signature)
    (request : RegistrationNativePlatformIdentityCtxCompiler.Spec.Domain) (mode : Mode)
    (allowed : UsesSourceMessage fixed request) (prior : Fixed fixed mode)
    (result : RegistrationNativePlatformIdentityCtxCompiler.Spec.Range request × Mode)
    (reached : result ∈ support ((RegistrationNativeIdentityCensorOperational.implementation selected placeholder request).run mode)) :
    Fixed fixed result.2 := by
  rcases request with ((coin | request) | report) | bytes
  · have original := simulated_support _ _ _ reached
    rw [constant_state _ _ _ original]
    exact prior
  · cases request with
    | create | reveal handle =>
      have original := simulated_support _ _ _ reached
      rw [constant_state _ _ _ original]
      exact prior
    | service handle request => cases request with
      | staticDh peer =>
        have original := simulated_support _ _ _ reached
        rw [constant_state _ _ _ original]
        exact prior
      | sign message => exact signing_fixed fixed selected handle message mode allowed prior result reached
  · have original := simulated_support _ _ _ reached
    rw [constant_state _ _ _ original]
    exact prior
  · change result ∈ support (match (RegistrationNativeIdentityCensorCompiler.hashInput mode bytes).input with
      | some _ => simulateQ RegistrationNativeIdentityCensorOperational.embed
          ((RegistrationNativeIdentityCensorCompiler.implementation selected placeholder (.inr bytes)).run mode)
      | none => do
          let reply ← (RegistrationNativeIdentityCensorOperational.Spec.query
            (.inr (.template selected mode.target (RegistrationNativeIdentityCensorOperational.parts bytes).1
              (RegistrationNativeIdentityCensorOperational.parts bytes).2)) : OracleComp RegistrationNativeIdentityCensorOperational.Spec _)
          pure (reply, mode)) at reached
    split at reached
    · have original := simulated_support _ _ _ reached
      change result ∈ support (do
        let reply ← (RegistrationNativeIdentityCensorCompiler.Spec.query
          (.inr (RegistrationNativeIdentityCensorCompiler.hashInput mode bytes)) : OracleComp RegistrationNativeIdentityCensorCompiler.Spec _)
        pure (reply, {mode with knownInputs := match (RegistrationNativeIdentityCensorCompiler.hashInput mode bytes).input with
          | none => mode.knownInputs
          | some input => mode.knownInputs ++ [input]})) at original
      have same := constant_state _ _ result original
      rw [same]
      exact prior
    · rw [constant_state _ _ _ reached]
      exact prior


/-- Every adaptive original source body retains its actual fixed one-time operand through all later optional replies. -/
theorem program (fixed : Pqxdh.Bytes) (selected : Nat) (placeholder : PqxdhEd25519EufCma.Ed25519Signature)
    (work : OracleComp RegistrationNativePlatformIdentityCtxCompiler.Spec A)
    (allowed : work.AllQueriesSatisfy (UsesSourceMessage fixed))
    (mode : Mode) (prior : Fixed fixed mode) (result : A × Mode)
    (reached : result ∈ support ((simulateQ (RegistrationNativeIdentityCensorOperational.implementation selected placeholder) work).run mode)) :
    Fixed fixed result.2 := by
  induction work using OracleComp.inductionOn generalizing mode result with
  | pure value =>
    simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at reached
    cases reached
    exact prior
  | query_bind request next ih =>
    rw [allQueriesSatisfy_query_bind_iff] at allowed
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at reached
    obtain ⟨middle, called, continued⟩ := reached
    exact ih middle.1 (allowed.2 middle.1) middle.2 (query fixed selected placeholder request mode allowed.1 prior middle called) result continued


/-- The actual canonical or private-censored source interpretation retains the same fixed target operand. -/
theorem lower_program (joint : PqxdhJointIdentity.Primitives) (fixed : Pqxdh.Bytes) (selected : Nat)
    (placeholder : Ed25519Signature) (masked : Bool)
    (work : OracleComp RegistrationNativePlatformIdentityCtxCompiler.Spec A)
    (allowed : work.AllQueriesSatisfy (UsesSourceMessage fixed))
    (mode : Mode) (before : RegistrationNativeIdentityCensorSource.State) (prior : Fixed fixed mode)
    (result : (A × Mode) × RegistrationNativeIdentityCensorSource.State)
    (reached : result ∈ support ((simulateQ (if masked then RegistrationNativeIdentityCensorSource.censored joint selected placeholder
      else RegistrationNativeIdentityCensorSource.implementation joint selected)
      ((simulateQ (RegistrationNativeIdentityCensorOperational.implementation selected placeholder) work).run mode)).run before)) :
    Fixed fixed result.1.2 := by
  have operational : result.1 ∈ support
      ((simulateQ (RegistrationNativeIdentityCensorOperational.implementation selected placeholder) work).run mode) := by
    apply OracleComp.support_simulateQ_run'_subset
      (if masked then RegistrationNativeIdentityCensorSource.censored joint selected placeholder
        else RegistrationNativeIdentityCensorSource.implementation joint selected) _ before
    rw [StateT.run'_eq,support_map]
    exact ⟨result,reached,rfl⟩
  exact program fixed selected placeholder work allowed mode prior result.1 operational

open RegistrationNativeIdentityCensorEdOutgoingSource (Full interpret)
variable {n : Nat} {KemSK Platform : Type} {mlSource : RegistrationNativeMldsa.Source}
/-- The complete Main/platform body preserves its source-fixed target without replacing its current private interpreter. -/
theorem main (joint : PqxdhJointIdentity.Primitives) (fixed : Pqxdh.Bytes) (selected : Nat)
    (placeholder : Ed25519Signature) (masked : Bool)
    (work : RegistrationNativePlatformIdentityCtxMain.M n KemSK Platform mlSource A)
    (before : Full (n := n) (KemSK := KemSK) (Platform := Platform) (mlSource := mlSource))
    (allowed : (work.run before.1.1).AllQueriesSatisfy (UsesSourceMessage fixed))
    (prior : Fixed fixed before.1.2)
    (result : A × Full (n := n) (KemSK := KemSK) (Platform := Platform) (mlSource := mlSource))
    (supported : result ∈ support ((interpret joint selected placeholder masked work).run before)) :
    Fixed fixed result.2.1.2 := by
  simp only [interpret,StateT.run,mem_support_bind_iff] at supported
  obtain ⟨returned,called,completed⟩ := supported
  obtain rfl := eq_of_mem_support_pure _ completed
  exact lower_program joint fixed selected placeholder masked (work.run before.1.1) allowed before.1.2 before.2 prior returned called

/-- Starting without a target, any actual selected result is exactly the source body's original operand in both synchronized targets. -/
theorem main_target (joint : PqxdhJointIdentity.Primitives) (fixed : Pqxdh.Bytes) (selected : Nat)
    (placeholder : Ed25519Signature) (masked : Bool)
    (work : RegistrationNativePlatformIdentityCtxMain.M n KemSK Platform mlSource A)
    (before : Full (n := n) (KemSK := KemSK) (Platform := Platform) (mlSource := mlSource))
    (allowed : (work.run before.1.1).AllQueriesSatisfy (UsesSourceMessage fixed))
    (empty : before.1.2.target=none) (synced : before.1.2.target=before.2.target)
    (result : A × Full (n := n) (KemSK := KemSK) (Platform := Platform) (mlSource := mlSource))
    (supported : result ∈ support ((interpret joint selected placeholder masked work).run before))
    (message : Pqxdh.Bytes) (chosen : result.2.2.target=some message) :
    message=fixed ∧ result.2.1.2.target=some fixed ∧ result.2.2.target=some fixed := by
  have held := main joint fixed selected placeholder masked work before allowed
    (fun message present => by rw [empty] at present; cases present) result supported
  have together := RegistrationNativeIdentityCensorTargetSyncMain.main joint selected placeholder masked work before synced result supported
  have equal := held message (together.trans chosen)
  exact ⟨equal,by rw [←equal]; exact together.trans chosen,by rw [←equal]; exact chosen⟩

open PqxdhServerAuthExperiment (Setup Checks)
variable {I E : Type} {base : OracleSpec I}
/-- The actual captured bundle's selected message equals the one-time field of its literal started tuple, including all failed writer and optional-signature paths. -/
theorem bundled (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (index : Nat) (owner : RegistrationNativeIdentityFrontend.Owner mlSource) (scalar : PqxdhJointGapDh.ScalarBytes)
    (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (started : beaconcrypt_core.pqxdh.BeaconStart)
    (built : beaconcrypt_core.pqxdh.beacon_start (beaconcrypt_core.pqxdh.BeaconFresh.mk owner.pin.binding) (RegistrationNativeIdentityFrontend.inputs owner)
      (beaconcrypt_core.pqxdh.BeaconCoins.mk (PqxdhRootTableInitialization.rootArray (setup.dh.publicKey scalar))) = .ok started)
    (tagged : RegistrationNativeIdentitySigningRole.Tagged started)
    (selected : Nat) (placeholder : Ed25519Signature) (masked : Bool)
    (before : Full (n := n) (KemSK := KemSK) (Platform := Platform) (mlSource := mlSource))
    (empty : before.1.2.target=none) (synced : before.1.2.target=before.2.target)
    (result : RustM (Option (alloc.vec.Vec U8)) × Full (n := n) (KemSK := KemSK) (Platform := Platform) (mlSource := mlSource))
    (supported : result ∈ support ((interpret setup.joint selected placeholder masked
      (RegistrationNativePlatformIdentityCtxMain.beacon setup checks representation created
        (RegistrationNativePlatformIdentityBundle.bundled setup index owner scalar writer))).run before))
    (message : Pqxdh.Bytes) (chosen : result.2.2.target=some message) :
    message=PqxdhRefinement.absBytes started.message.one_time_key ∧
      result.2.1.2.target=some (PqxdhRefinement.absBytes started.message.one_time_key) ∧
      result.2.2.target=some (PqxdhRefinement.absBytes started.message.one_time_key) := by
  exact main_target setup.joint _ selected placeholder masked _ before
    (RegistrationNativePlatformIdentityCtxBundleMessageScope.bundled setup checks representation created index owner scalar writer
      started built tagged before.1.1) empty synced result supported message chosen

end BeaconcryptCore.Computational.RegistrationNativeIdentityCensorTargetOperand

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorTargetOperand.query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorTargetOperand.query

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorTargetOperand.program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorTargetOperand.program

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorTargetOperand.lower_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorTargetOperand.lower_program

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorTargetOperand.main' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorTargetOperand.main

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorTargetOperand.main_target' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorTargetOperand.main_target

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorTargetOperand.bundled' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorTargetOperand.bundled
