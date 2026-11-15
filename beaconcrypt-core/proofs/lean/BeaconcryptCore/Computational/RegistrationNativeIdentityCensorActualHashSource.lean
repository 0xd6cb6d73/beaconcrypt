-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorHashOutgoingSource
import BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxMain

/-! Real operational hashing erases to the literal ordinary native hash source. Public inputs need no hidden-template assumption. On the selected internal input, its actual source framing and retained canonical reply identify the same physical address, including warm cache hits and exact draw charges. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityCensorActualHashSource
open PqxdhServerAuthExperiment (Setup Checks)
open PqxdhEd25519EufCma (Ed25519Signature)
open RegistrationNativeIdentityCensorEdOutgoingSource (Full interpret)
open RegistrationNativeIdentityCensorCompiler (Mode)
open RegistrationNativeIdentityCensorOperational (parts)
variable {n : Nat} {I KemSK Platform A : Type} {base : OracleSpec I} {mlSource : RegistrationNativeMldsa.Source}

def project (before : Full (n := n) (KemSK := KemSK) (Platform := Platform) (mlSource := mlSource)) :
    RegistrationNativePlatformIdentityCtxMain.Full n KemSK Platform mlSource :=
  (before.1.1, (before.2.pool, before.2.hash))

private theorem original_run (joint : PqxdhJointIdentity.Primitives)
    (work : RegistrationNativePlatformIdentityCtxMain.M n KemSK Platform mlSource A)
    (before : RegistrationNativePlatformIdentityCtxMain.Full n KemSK Platform mlSource) :
    (RegistrationNativePlatformIdentityCtxMain.interpret joint work).run before =
      (fun result => (result.1.1, (result.1.2, result.2))) <$>
        (simulateQ (RegistrationNativePlatformIdentityCtxSource.implementation joint) (work.run before.1)).run before.2 := rfl

private theorem interpret_run (joint : PqxdhJointIdentity.Primitives) (selected : Nat) (placeholder : Ed25519Signature)
    (work : RegistrationNativePlatformIdentityCtxMain.M n KemSK Platform mlSource A)
    (before : Full (n := n) (KemSK := KemSK) (Platform := Platform) (mlSource := mlSource)) :
    (interpret joint selected placeholder false work).run before = (do
      let result ← (simulateQ (RegistrationNativeIdentityCensorSource.implementation joint selected)
        ((simulateQ (RegistrationNativeIdentityCensorOperational.implementation selected placeholder) (work.run before.1.1)).run before.1.2)).run before.2
      pure (result.1.1.1, ((result.1.1.2, result.1.2), result.2))) := rfl

private theorem hash_run (selected : Nat) (placeholder : Ed25519Signature) (bytes : Pqxdh.Bytes) (before : Mode) :
    (RegistrationNativeIdentityCensorOperational.implementation selected placeholder (.inr bytes)).run before =
      (match (RegistrationNativeIdentityCensorCompiler.hashInput before bytes).input with
      | some _ => (RegistrationNativeIdentityCensorOperational.promote
          (RegistrationNativeIdentityCensorCompiler.implementation selected placeholder (.inr bytes))).run before
      | none => do
          let reply ← (RegistrationNativeIdentityCensorOperational.Spec.query (.inr (.template selected before.target
            (parts bytes).1 (parts bytes).2)) : OracleComp RegistrationNativeIdentityCensorOperational.Spec (CtxRomAuth.CtxDigest × Nat))
          pure (reply, before)) := rfl

private theorem promote_run (work : StateT Mode (OracleComp RegistrationNativeIdentityCensorCompiler.Spec) A) (before : Mode) :
    (RegistrationNativeIdentityCensorOperational.promote work).run before =
      simulateQ RegistrationNativeIdentityCensorOperational.embed (work.run before) := rfl

private theorem compiler_hash (selected : Nat) (placeholder : Ed25519Signature) (input : Pqxdh.Bytes) (before : Mode) :
    (RegistrationNativeIdentityCensorCompiler.implementation selected placeholder (.inr input)).run before = (do
      let described := RegistrationNativeIdentityCensorCompiler.hashInput before input
      let answer ← (RegistrationNativeIdentityCensorCompiler.Spec.query (.inr described) : OracleComp RegistrationNativeIdentityCensorCompiler.Spec (CtxRomAuth.CtxDigest × Nat))
      pure (answer, {before with knownInputs := match described.input with
        | none => before.knownInputs | some bytes => before.knownInputs ++ [bytes]})) := rfl

section Actual
variable (setup : Setup base KemSK) (checks : Checks)
variable (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
variable (selected : Nat) (placeholder : Ed25519Signature) (request : registration.HashRequest)
local notation "bytes" => BeaconcryptCore.Refinement.RegistrationInputs.hashBytes request
local notation "action" => RegistrationNativePlatformIdentityCtxMain.beacon setup checks representation created
  (RegistrationNativePlatformIdentityProgram.native
    (RegistrationNativeIdentityFrontend.hash (n := n) (KemSK := KemSK) (Auxiliary := RegistrationServerRoleBackend.State) (source := mlSource) request))

private theorem transformed (before : Full (n := n) (KemSK := KemSK) (Platform := Platform) (mlSource := mlSource)) :
    (interpret setup.joint selected placeholder false action).run before = (do
      let result ← (simulateQ (RegistrationNativeIdentityCensorSource.implementation setup.joint selected)
        ((RegistrationNativeIdentityCensorOperational.implementation selected placeholder (.inr bytes)).run before.1.2)).run before.2
      pure (result.1.1.1, ((RegistrationNativePlatformIdentityCtxHashOutgoing.updated result.1.1.2 before.1.1, result.1.2), result.2))) := by
  rw [interpret_run, RegistrationNativePlatformIdentityCtxHashOutgoing.outgoing]
  simp only [bind_pure_comp, simulateQ_map, simulateQ_spec_query, StateT.run_map, Functor.map_map]

private theorem original (before : Full (n := n) (KemSK := KemSK) (Platform := Platform) (mlSource := mlSource)) :
    (RegistrationNativePlatformIdentityCtxMain.interpret setup.joint action).run (project before) =
      (fun result => (result.1.1, (RegistrationNativePlatformIdentityCtxHashOutgoing.updated result.1.2 before.1.1,
        (before.2.pool, result.2)))) <$> (RegistrationNativePlatformCtxBackend.physical bytes).run before.2.hash := by
  rw [original_run, RegistrationNativePlatformIdentityCtxHashOutgoing.outgoing]
  simp only [bind_pure_comp, simulateQ_map, simulateQ_spec_query, StateT.run_map, project]
  simp only [RegistrationNativePlatformIdentityCtxSource.implementation, StateT.run, Functor.map_map]

/-- Every inactive actual native hash erases to its literal original full source state, preserving all warm-cache draws and P. -/
theorem inactive (before : Full (n := n) (KemSK := KemSK) (Platform := Platform) (mlSource := mlSource))
    (inactive : before.1.2.active = false) :
    Prod.map id project <$> (interpret setup.joint selected placeholder false action).run before =
      (RegistrationNativePlatformIdentityCtxMain.interpret setup.joint action).run (project before) := by
  rw [transformed, original, hash_run]
  simp only [RegistrationNativeIdentityCensorCompiler.hashInput, inactive, Bool.false_eq_true, ite_false]
  rw [promote_run, compiler_hash]
  simp only [RegistrationNativeIdentityCensorCompiler.hashInput, inactive, Bool.false_eq_true, ite_false,
    RegistrationNativeIdentityCensorOperational.embed, bind_pure_comp, simulateQ_map, simulateQ_spec_query, StateT.run_map]
  simp only [RegistrationNativeIdentityCensorSource.implementation, RegistrationNativeIdentityCensorSource.physical,
    StateT.run, Functor.map_map, project, Prod.map_def, id_eq, inactive, Bool.false_eq_true, ite_false]

/-- The reached canonical memo and literal current input framing derive the same physical source query for a selected hidden hash; no source/game equality is a premise. -/
theorem hidden (before : Full (n := n) (KemSK := KemSK) (Platform := Platform) (mlSource := mlSource))
    (signature : Ed25519Signature) (stored : before.2.canonical = some signature)
    (active : before.1.2.active = true) (route : RegistrationNativeIdentityHashRoute.route bytes = none)
    (literal : bytes = (parts bytes).1 ++ signature.toList ++ (parts bytes).2) :
    Prod.map id project <$> (interpret setup.joint selected placeholder false action).run before =
      (RegistrationNativePlatformIdentityCtxMain.interpret setup.joint action).run (project before) := by
  rw [transformed, original, hash_run]
  simp only [RegistrationNativeIdentityCensorCompiler.hashInput, active, ite_true, route,
    simulateQ_bind, simulateQ_spec_query, RegistrationNativeIdentityCensorSource.implementation,
    StateT.run_bind, simulateQ_pure, StateT.run_pure]
  rw [RegistrationNativeIdentityCensorSource.template_source _ _ signature before.2 stored, ← literal]
  simp only [bind_pure_comp, Functor.map_map, project, Prod.map_def, id_eq]
end Actual
end BeaconcryptCore.Computational.RegistrationNativeIdentityCensorActualHashSource

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorActualHashSource.inactive' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorActualHashSource.inactive

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorActualHashSource.hidden' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorActualHashSource.hidden
