-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorOutgoingView

/-! The exact private operational interpretation distributes over the literal Main dictionary. This closes the previously derived NoKem source fold without changing current replies, native/P counters or private physical state. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityCensorSourceFold
open PqxdhServerAuthExperiment (Setup Checks)
open PqxdhEd25519EufCma (Ed25519Signature)
open RegistrationNativeIdentityCensorEdOutgoingSource (Full interpret)
variable {n : Nat} {I KemSK Platform A B Q : Type} {base : OracleSpec I} {spec : OracleSpec Q}
variable {mlSource : RegistrationNativeMldsa.Source}

private theorem interpret_run (joint : PqxdhJointIdentity.Primitives) (selected : Nat) (placeholder : Ed25519Signature)
    (censored : Bool) (work : RegistrationNativePlatformIdentityCtxMain.M n KemSK Platform mlSource A)
    (before : Full (n := n) (KemSK := KemSK) (Platform := Platform) (mlSource := mlSource)) :
    (interpret joint selected placeholder censored work).run before = (do
      let result ← (simulateQ (if censored then RegistrationNativeIdentityCensorSource.censored joint selected placeholder
          else RegistrationNativeIdentityCensorSource.implementation joint selected)
        ((simulateQ (RegistrationNativeIdentityCensorOperational.implementation selected placeholder) (work.run before.1.1)).run before.1.2)).run before.2
      pure (result.1.1.1, ((result.1.1.2, result.1.2), result.2))) := rfl

/-- Pure Core control returns retain the entire source/native/P state. -/
theorem pure_source (joint : PqxdhJointIdentity.Primitives) (selected : Nat) (placeholder : Ed25519Signature)
    (censored : Bool) (value : A) :
    interpret (n := n) (KemSK := KemSK) (Platform := Platform) (mlSource := mlSource) joint selected placeholder censored (pure value) = pure value := by
  funext before
  change (interpret joint selected placeholder censored (pure value)).run before = (pure value : StateT _ ProbComp A).run before
  simp only [interpret_run, simulateQ_pure, StateT.run_pure, pure_bind]

/-- Every actual source continuation receives the complete state reached by its immediate predecessor. -/
theorem bind_source (joint : PqxdhJointIdentity.Primitives) (selected : Nat) (placeholder : Ed25519Signature)
    (censored : Bool) (work : RegistrationNativePlatformIdentityCtxMain.M n KemSK Platform mlSource A)
    (next : A → RegistrationNativePlatformIdentityCtxMain.M n KemSK Platform mlSource B) :
    interpret joint selected placeholder censored (work >>= next) =
      (do let value ← interpret joint selected placeholder censored work
          interpret joint selected placeholder censored (next value)) := by
  funext before
  change (interpret joint selected placeholder censored (work >>= next)).run before =
    ((interpret joint selected placeholder censored work >>= fun value => interpret joint selected placeholder censored (next value)) : StateT _ ProbComp B).run before
  simp only [interpret_run, StateT.run_bind, simulateQ_bind, bind_assoc, pure_bind]

/-- Adaptive free source trees retain the same native/private/P joint distribution under dictionary interpretation. -/
theorem program (joint : PqxdhJointIdentity.Primitives) (selected : Nat) (placeholder : Ed25519Signature)
    (censored : Bool) (handler : QueryImpl spec (RegistrationNativePlatformIdentityCtxMain.M n KemSK Platform mlSource))
    (work : OracleComp spec A) :
    interpret joint selected placeholder censored (simulateQ handler work) =
      simulateQ (fun query => interpret joint selected placeholder censored (handler query)) work := by
  induction work using OracleComp.inductionOn with
  | pure value => simp only [simulateQ_pure]; exact pure_source joint selected placeholder censored value
  | query_bind query next ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, bind_source, ih]

/-- The original mutable Init writer and actual outgoing Ed/hash/ML dictionary close through both source interpreters query by query, with no whole-callback equation supplied. -/
theorem publication {E : Type} (joint : PqxdhJointIdentity.Primitives) (selected : Nat) (placeholder : Ed25519Signature)
    (censored : Bool) (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (index : Nat) (owner : RegistrationNativeIdentityFrontend.Owner mlSource)
    (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (work : OracleComp (RegistrationNativePlatformWriter.Spec E) A) :
    interpret joint selected placeholder censored
      (RegistrationNativePlatformIdentityCtxMain.beacon setup checks representation created
        (simulateQ (RegistrationNativePlatformIdentityPublication.callback (n := n) (Auxiliary := RegistrationServerRoleBackend.State)
          setup index owner writer) work)) =
      simulateQ (fun query => interpret joint selected placeholder censored
        (RegistrationNativePlatformIdentityCtxMain.beacon setup checks representation created
          (RegistrationNativePlatformIdentityPublication.callback (n := n) (Auxiliary := RegistrationServerRoleBackend.State)
            setup index owner writer query))) work := by
  rw [RegistrationNativePlatformIdentityCtxOutgoingFold.publication setup checks representation created index owner writer work,
    program]

end BeaconcryptCore.Computational.RegistrationNativeIdentityCensorSourceFold

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorSourceFold.pure_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorSourceFold.pure_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorSourceFold.bind_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorSourceFold.bind_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorSourceFold.program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorSourceFold.program

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorSourceFold.publication' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorSourceFold.publication
