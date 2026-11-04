-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorHashOutgoingSource
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorMldsaOutgoingSource
/-! Actual public and hidden-template hash callbacks may update their physical cache, template framing and known-input journal. Their complete private key/service pool, selected target/canonical signature and every remaining Mode control field stay exact. This is derived from literal source physical/template leaves and the actual native counter-bearing hash action. -/
open OracleComp OracleSpec CoreModels Aeneas beaconcrypt_core
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityCensorHashFrame
open PqxdhServerAuthExperiment (Setup Checks)
open PqxdhEd25519EufCma (Ed25519Signature)
open RegistrationNativeIdentityCensorCompiler (Mode HashInput)
open RegistrationNativeIdentityCensorEdOutgoingSource (Full interpret)
open RegistrationNativeIdentityCensorOperational (Spec parts)
variable {n : Nat} {I KemSK Platform A : Type} {base : OracleSpec I} {mlSource : RegistrationNativeMldsa.Source}
abbrev Private := RegistrationNativeIdentityCensorSource.State

def privateView (before : Private) := (before.pool, before.target, before.canonical)
def stable (mode : Mode) (before : Private) := ({mode with knownInputs := []}, privateView before)
private theorem map_apply {S X Y : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (change : X → Y) (work : StateT S m X) (before : S) :
    (change <$> work) before = Prod.map change id <$> work before := StateT.run_map change work before

private theorem physical_frame (input : Pqxdh.Bytes) (before : Private)
    (result : (CtxRomAuth.CtxDigest × Nat) × Private)
    (supported : result ∈ support ((RegistrationNativeIdentityCensorSource.physical input).run before)) :
    privateView result.2 = privateView before := by
  simp only [RegistrationNativeIdentityCensorSource.physical, StateT.run, support_map] at supported
  obtain ⟨inner, _possible, rfl⟩ := supported
  rfl
private theorem template_frame (leading trailing : Pqxdh.Bytes) (before : Private)
    (result : (CtxRomAuth.CtxDigest × Nat) × Private)
    (supported : result ∈ support ((RegistrationNativeIdentityCensorSource.template leading trailing).run before)) :
    privateView result.2 = privateView before := by
  simp only [RegistrationNativeIdentityCensorSource.template, StateT.run, support_map] at supported
  obtain ⟨inner, possible, rfl⟩ := supported
  exact physical_frame _ before inner possible

private def HashOnly : Spec.Domain → Prop
  | .inl (.inr _) => True
  | .inr (.template _ _ _ _) => True
  | _ => False

private theorem hash_leaf (joint : PqxdhJointIdentity.Primitives) (selected : Nat) (placeholder : Ed25519Signature)
    (censored : Bool) (query : Spec.Domain) (allowed : HashOnly query) (before : Private)
    (result : Spec.Range query × Private)
    (supported : result ∈ support (((if censored then RegistrationNativeIdentityCensorSource.censored joint selected placeholder
      else RegistrationNativeIdentityCensorSource.implementation joint selected) query).run before)) :
    privateView result.2 = privateView before := by
  rcases query with (query | described) | marker
  · exact False.elim allowed
  · cases censored <;> exact physical_frame _ before result supported
  · cases marker with
    | omitted handle message => exact False.elim allowed
    | template handle target leading trailing =>
      cases censored <;> exact template_frame leading trailing before result supported

private theorem hash_run (selected : Nat) (placeholder : Ed25519Signature) (bytes : Pqxdh.Bytes) (mode : Mode) :
    (RegistrationNativeIdentityCensorOperational.implementation selected placeholder (.inr bytes)).run mode =
      (match (RegistrationNativeIdentityCensorCompiler.hashInput mode bytes).input with
      | some _ => (RegistrationNativeIdentityCensorOperational.promote
          (RegistrationNativeIdentityCensorCompiler.implementation selected placeholder (.inr bytes))).run mode
      | none => do
          let reply ← (Spec.query (.inr (.template selected mode.target (parts bytes).1 (parts bytes).2)) : OracleComp Spec (CtxRomAuth.CtxDigest × Nat))
          pure (reply, mode)) := rfl
private theorem compiler_hash (selected : Nat) (placeholder : Ed25519Signature) (bytes : Pqxdh.Bytes) (mode : Mode) :
    (RegistrationNativeIdentityCensorCompiler.implementation selected placeholder (.inr bytes)).run mode = (do
      let reply ← (RegistrationNativeIdentityCensorCompiler.Spec.query (.inr (RegistrationNativeIdentityCensorCompiler.hashInput mode bytes)) :
        OracleComp RegistrationNativeIdentityCensorCompiler.Spec (CtxRomAuth.CtxDigest × Nat))
      pure (reply, {mode with knownInputs := match (RegistrationNativeIdentityCensorCompiler.hashInput mode bytes).input with
        | none => mode.knownInputs
        | some input => mode.knownInputs ++ [input]})) := rfl

private theorem operational_hash (selected : Nat) (placeholder : Ed25519Signature) (bytes : Pqxdh.Bytes) (mode : Mode) :
    (RegistrationNativeIdentityCensorOperational.implementation selected placeholder (.inr bytes)).run mode =
      (match (RegistrationNativeIdentityCensorCompiler.hashInput mode bytes).input with
      | some input => (fun reply => (reply, {mode with knownInputs := mode.knownInputs ++ [input]})) <$>
          (Spec.query (.inl (.inr (RegistrationNativeIdentityCensorCompiler.hashInput mode bytes))) : OracleComp Spec (CtxRomAuth.CtxDigest × Nat))
      | none => (fun reply => (reply, mode)) <$>
          (Spec.query (.inr (.template selected mode.target (parts bytes).1 (parts bytes).2)) : OracleComp Spec (CtxRomAuth.CtxDigest × Nat))) := by
  rw [hash_run]
  cases routed : (RegistrationNativeIdentityCensorCompiler.hashInput mode bytes).input with
  | some input =>
    change simulateQ RegistrationNativeIdentityCensorOperational.embed
      ((RegistrationNativeIdentityCensorCompiler.implementation selected placeholder (.inr bytes)).run mode) = _
    rw [compiler_hash]
    simp only [bind_pure_comp, simulateQ_map, simulateQ_spec_query, RegistrationNativeIdentityCensorOperational.embed, routed]
    rfl
  | none => rw [bind_pure_comp]; rfl

private theorem leaf_frame (joint : PqxdhJointIdentity.Primitives) (selected : Nat) (placeholder : Ed25519Signature)
    (censored : Bool) (bytes : Pqxdh.Bytes) (mode : Mode) (before : Private)
    (result : ((CtxRomAuth.CtxDigest × Nat) × Mode) × Private)
    (supported : result ∈ support ((simulateQ (if censored then RegistrationNativeIdentityCensorSource.censored joint selected placeholder
      else RegistrationNativeIdentityCensorSource.implementation joint selected)
      ((RegistrationNativeIdentityCensorOperational.implementation selected placeholder (.inr bytes)).run mode)).run before)) :
    stable result.1.2 result.2 = stable mode before := by
  rw [operational_hash] at supported
  cases routed : (RegistrationNativeIdentityCensorCompiler.hashInput mode bytes).input with
  | some input =>
    simp only [routed, simulateQ_map, StateT.run_map, simulateQ_spec_query, support_map] at supported
    obtain ⟨inner, possible, rfl⟩ := supported
    have unchanged := hash_leaf joint selected placeholder censored
      (.inl (.inr (RegistrationNativeIdentityCensorCompiler.hashInput mode bytes))) trivial before inner possible
    exact congrArg (fun value => ({mode with knownInputs := []}, value)) unchanged
  | none =>
    simp only [routed, simulateQ_map, StateT.run_map, simulateQ_spec_query, support_map] at supported
    obtain ⟨inner, possible, rfl⟩ := supported
    have unchanged := hash_leaf joint selected placeholder censored
      (.inr (.template selected mode.target (parts bytes).1 (parts bytes).2)) trivial before inner possible
    exact congrArg (fun value => ({mode with knownInputs := []}, value)) unchanged

private theorem interpret_run (joint : PqxdhJointIdentity.Primitives) (selected : Nat) (placeholder : Ed25519Signature)
    (censored : Bool) (work : RegistrationNativePlatformIdentityCtxMain.M n KemSK Platform mlSource A)
    (before : Full (n := n) (KemSK := KemSK) (Platform := Platform) (mlSource := mlSource)) :
    (interpret joint selected placeholder censored work).run before = (do
      let result ← (simulateQ (if censored then RegistrationNativeIdentityCensorSource.censored joint selected placeholder
        else RegistrationNativeIdentityCensorSource.implementation joint selected)
        ((simulateQ (RegistrationNativeIdentityCensorOperational.implementation selected placeholder) (work.run before.1.1)).run before.1.2)).run before.2
      pure (result.1.1.1, ((result.1.1.2, result.1.2), result.2))) := rfl

/-- Actual public or hidden-template hashing preserves Mode control, the entire private key/service pool and selected target/canonical signature, while the real hash/framing and known-input journal may advance. -/
theorem outgoing (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created Unit)
    (selected : Nat) (placeholder : Ed25519Signature) (request : registration.HashRequest) (censored : Bool)
    (before : Full (n := n) (KemSK := KemSK) (Platform := Platform) (mlSource := mlSource))
    (result : CtxRomAuth.CtxDigest × Full (n := n) (KemSK := KemSK) (Platform := Platform) (mlSource := mlSource))
    (supported : result ∈ support ((interpret setup.joint selected placeholder censored
      (RegistrationNativePlatformIdentityCtxMain.beacon setup checks representation created
        (RegistrationNativePlatformIdentityProgram.native
          (RegistrationNativeIdentityFrontend.hash (n := n) (KemSK := KemSK) (Auxiliary := RegistrationServerRoleBackend.State) (source := mlSource) request)))).run before)) :
    stable result.2.1.2 result.2.2 = stable before.1.2 before.2 := by
  rw [interpret_run, RegistrationNativePlatformIdentityCtxHashOutgoing.outgoing] at supported
  simp only [bind_pure_comp, simulateQ_map, simulateQ_spec_query, StateT.run_map,
    Functor.map_map, support_map] at supported
  obtain ⟨inner, possible, rfl⟩ := supported
  exact leaf_frame setup.joint selected placeholder censored _ before.1.2 before.2 inner possible
end BeaconcryptCore.Computational.RegistrationNativeIdentityCensorHashFrame

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorHashFrame.outgoing' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorHashFrame.outgoing
