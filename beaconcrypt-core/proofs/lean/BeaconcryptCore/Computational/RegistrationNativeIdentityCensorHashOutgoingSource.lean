-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorEdOutgoingSource
import BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxHashOutgoing

/-! The actual native hash callback has one explicit hash capability and the exact counter update. Its operational transformation contains no suppressed-sign marker. Real and private-censored interpretation therefore coincide for public hashes; actual paired internal templates couple the complete native/private/P state through their identical public framing. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityCensorHashOutgoingSource
open PqxdhServerAuthExperiment (Setup Checks)
open PqxdhEd25519EufCma (Ed25519Signature)
open RegistrationNativeIdentityCensorCompiler (Mode)
open RegistrationNativeIdentityCensorEdOutgoingSource (Full interpret)
open RegistrationNativeIdentityCensorOperational (Spec parts)
variable {n : Nat} {I KemSK Platform Value : Type} {base : OracleSpec I} {mlSource : RegistrationNativeMldsa.Source}

private def Allowed : Spec.Domain → Prop
  | .inr (.omitted _ _) => False
  | _ => True

private theorem leaves (joint : PqxdhJointIdentity.Primitives) (selected : Nat) (placeholder : Ed25519Signature)
    (query : Spec.Domain) (allowed : Allowed query) :
    RegistrationNativeIdentityCensorSource.implementation joint selected query =
      RegistrationNativeIdentityCensorSource.censored joint selected placeholder query := by
  cases query with
  | inl query => rfl
  | inr query => cases query with
    | omitted handle message => exact False.elim allowed
    | template handle message leading trailing => rfl

private theorem same_program (joint : PqxdhJointIdentity.Primitives) (selected : Nat) (placeholder : Ed25519Signature)
    (work : OracleComp Spec Value) (allowed : work.AllQueriesSatisfy Allowed) (before : RegistrationNativeIdentityCensorSource.State) :
    (simulateQ (RegistrationNativeIdentityCensorSource.implementation joint selected) work).run before =
      (simulateQ (RegistrationNativeIdentityCensorSource.censored joint selected placeholder) work).run before := by
  induction work using OracleComp.inductionOn generalizing before with
  | pure value => rfl
  | query_bind query next ih =>
    rw [allQueriesSatisfy_query_bind_iff] at allowed
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
    rw [leaves joint selected placeholder query allowed.1]
    exact bind_congr (fun result => ih result.1 (allowed.2 result.1) result.2)

private theorem embedded_safe {A : Type} (work : OracleComp RegistrationNativeIdentityCensorOperational.Old A) :
    (simulateQ RegistrationNativeIdentityCensorOperational.embed work).AllQueriesSatisfy Allowed := by
  induction work using OracleComp.inductionOn with
  | pure value => trivial
  | query_bind query next ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, RegistrationNativeIdentityCensorOperational.embed]
    exact (allQueriesSatisfy_query_bind_iff _ _ _).mpr ⟨trivial, ih⟩

private theorem hash_run (selected : Nat) (placeholder : Ed25519Signature) (bytes : Pqxdh.Bytes) (before : Mode) :
    (RegistrationNativeIdentityCensorOperational.implementation selected placeholder (.inr bytes)).run before =
      (match (RegistrationNativeIdentityCensorCompiler.hashInput before bytes).input with
      | some _ => (RegistrationNativeIdentityCensorOperational.promote
          (RegistrationNativeIdentityCensorCompiler.implementation selected placeholder (.inr bytes))).run before
      | none => do
          let reply ← (Spec.query (.inr (.template selected before.target (parts bytes).1 (parts bytes).2)) : OracleComp Spec (CtxRomAuth.CtxDigest × Nat))
          pure (reply, before)) := rfl

private theorem hash_safe (selected : Nat) (placeholder : Ed25519Signature) (bytes : Pqxdh.Bytes) (before : Mode) :
    ((RegistrationNativeIdentityCensorOperational.implementation selected placeholder (.inr bytes)).run before).AllQueriesSatisfy Allowed := by
  rw [hash_run]
  cases (RegistrationNativeIdentityCensorCompiler.hashInput before bytes).input with
  | some input => exact embedded_safe _
  | none => exact (allQueriesSatisfy_query_bind_iff _ _ _).mpr ⟨trivial, fun _ => trivial⟩

private theorem mapped_safe {A B : Type} (work : OracleComp Spec A) (change : A → B)
    (allowed : work.AllQueriesSatisfy Allowed) : (change <$> work).AllQueriesSatisfy Allowed := by
  rw [map_eq_bind_pure_comp]
  exact allQueriesSatisfy_bind allowed (fun _ => trivial)

private theorem interpret_run (joint : PqxdhJointIdentity.Primitives) (selected : Nat) (placeholder : Ed25519Signature)
    (censored : Bool) (work : RegistrationNativePlatformIdentityCtxMain.M n KemSK Platform mlSource Value)
    (before : Full (n := n) (KemSK := KemSK) (Platform := Platform) (mlSource := mlSource)) :
    (interpret joint selected placeholder censored work).run before = (do
      let result ← (simulateQ (if censored then RegistrationNativeIdentityCensorSource.censored joint selected placeholder
          else RegistrationNativeIdentityCensorSource.implementation joint selected)
        ((simulateQ (RegistrationNativeIdentityCensorOperational.implementation selected placeholder) (work.run before.1.1)).run before.1.2)).run before.2
      pure (result.1.1.1, ((result.1.1.2, result.1.2), result.2))) := rfl

private theorem transformed (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created Unit)
    (selected : Nat) (placeholder : Ed25519Signature) (request : registration.HashRequest)
    (before : Full (n := n) (KemSK := KemSK) (Platform := Platform) (mlSource := mlSource)) :
    (simulateQ (RegistrationNativeIdentityCensorOperational.implementation selected placeholder)
      ((RegistrationNativePlatformIdentityCtxMain.beacon setup checks representation created
        (RegistrationNativePlatformIdentityProgram.native
          (RegistrationNativeIdentityFrontend.hash (n := n) (KemSK := KemSK) (Auxiliary := RegistrationServerRoleBackend.State) (source := mlSource) request))).run before.1.1)).run before.1.2 =
      (fun result => ((result.1.1, RegistrationNativePlatformIdentityCtxHashOutgoing.updated result.1.2 before.1.1), result.2)) <$>
        (RegistrationNativeIdentityCensorOperational.implementation selected placeholder
          (.inr (BeaconcryptCore.Refinement.RegistrationInputs.hashBytes request))).run before.1.2 := by
  rw [RegistrationNativePlatformIdentityCtxHashOutgoing.outgoing]
  simp only [bind_pure_comp, simulateQ_map, simulateQ_spec_query, StateT.run_map]

section Actual
variable (setup : Setup base KemSK) (checks : Checks)
variable (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created Unit)
variable (selected : Nat) (placeholder : Ed25519Signature)
local notation "action" request => RegistrationNativePlatformIdentityCtxMain.beacon setup checks representation created
  (RegistrationNativePlatformIdentityProgram.native
    (RegistrationNativeIdentityFrontend.hash (n := n) (KemSK := KemSK) (Auxiliary := RegistrationServerRoleBackend.State) (source := mlSource) request))

/-- The complete actual current hash action uses no suppressed-sign operation, so public hashes have identical real/private-censored semantics on every source state. -/
theorem hash_same (request : registration.HashRequest)
    (before : Full (n := n) (KemSK := KemSK) (Platform := Platform) (mlSource := mlSource)) :
    (interpret setup.joint selected placeholder false (action request)).run before =
      (interpret setup.joint selected placeholder true (action request)).run before := by
  rw [interpret_run, interpret_run, transformed setup checks representation created selected placeholder request before]
  simp only [Bool.false_eq_true, ite_false, ite_true]
  rw [same_program setup.joint selected placeholder _
    (mapped_safe _ _ (hash_safe selected placeholder _ before.1.2)) before.2]

/-- Paired actual internal requests expose the same public template and retain exactly the same full native/private/P reply and poststate. -/
theorem hidden (left right : registration.HashRequest)
    (before : Full (n := n) (KemSK := KemSK) (Platform := Platform) (mlSource := mlSource))
    (active : before.1.2.active = true)
    (routeLeft : RegistrationNativeIdentityHashRoute.route (BeaconcryptCore.Refinement.RegistrationInputs.hashBytes left) = none)
    (routeRight : RegistrationNativeIdentityHashRoute.route (BeaconcryptCore.Refinement.RegistrationInputs.hashBytes right) = none)
    (framing : parts (BeaconcryptCore.Refinement.RegistrationInputs.hashBytes left) = parts (BeaconcryptCore.Refinement.RegistrationInputs.hashBytes right)) :
    (interpret setup.joint selected placeholder false (action left)).run before =
      (interpret setup.joint selected placeholder true (action right)).run before := by
  rw [hash_same setup checks representation created selected placeholder left before]
  rw [interpret_run, interpret_run, transformed setup checks representation created selected placeholder left before,
    transformed setup checks representation created selected placeholder right before, hash_run, hash_run]
  simp only [RegistrationNativeIdentityCensorCompiler.hashInput, active, ite_true, routeLeft, routeRight]
  rw [framing]
  rfl
end Actual
end BeaconcryptCore.Computational.RegistrationNativeIdentityCensorHashOutgoingSource

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorHashOutgoingSource.hash_same' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorHashOutgoingSource.hash_same

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorHashOutgoingSource.hidden' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorHashOutgoingSource.hidden
