-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformMaterializedFrontend
import BeaconcryptCore.Computational.RegistrationNativeG2Trace
/-! The same original G2 observer commutes with the exact material-reply/kernel translations on every callback. Applying it to the actual corrected free-source equation retains the full chronology jointly with every return, raw ledger and platform poststate. -/
open OracleComp OracleSpec CoreModels Aeneas beaconcrypt_core
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformG3MaterializedTrace
open RegistrationNativePublicFrontend (Spec)
open RegistrationNativeG3MaterializedLocal (translate)
open RegistrationNativeG2Trace (State handler begin finish)
variable {n : Nat} {KemSK A : Type}
private theorem map_apply {S X Y : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (observe : X → Y) (work : StateT S m X) (before : S) :
    (observe <$> work) before = Prod.map observe id <$> work before := StateT.run_map _ _ _

/-- The exact original chronological observer ignores only the material reply representation and installed kernel representation changed by translation. -/
theorem query_source (full : Bool) (seeds : RegistrationNativeG3AuditedWorld.Seeds n)
    (query : (Spec n KemSK).Domain) (before : State) :
    (simulateQ handler (translate full seeds query)).run before =
      simulateQ (translate full seeds) ((handler query).run before) := by
  rcases query with (message | (message | (publication | environment)) | kem) | record
  · simp only [translate, simulateQ_spec_query, handler, StateT.run, simulateQ_map, begin, finish]
  · cases full <;> simp only [translate, Bool.false_eq_true, ite_false, ite_true, simulateQ_map,
      simulateQ_spec_query, handler, StateT.run, Functor.map_map, begin, finish]
    all_goals rfl
  · simp only [translate, simulateQ_spec_query, handler, StateT.run, simulateQ_map, begin, finish]
  · cases environment with
    | inl coin =>
      simp only [translate, simulateQ_spec_query, handler, StateT.run, simulateQ_map, begin, finish]
      | inr capability =>
      cases capability <;> try (solve | simp only [translate, simulateQ_spec_query, handler, StateT.run, simulateQ_map, begin, finish])
      case installServer keyId binding kernel =>
        cases kernel <;> cases full <;> simp only [translate, Bool.false_eq_true, ite_false, ite_true,
          simulateQ_spec_query, handler, StateT.run, simulateQ_map, begin, finish]; rfl
      case installBeacon owner shell kernel =>
        cases kernel <;> cases full <;> simp only [translate, Bool.false_eq_true, ite_false, ite_true,
          simulateQ_spec_query, handler, StateT.run, simulateQ_map, begin, finish]; rfl
  · rcases kem with (other | key) | (pool | key)
    all_goals simp only [translate, simulateQ_spec_query, handler, StateT.run, simulateQ_map, begin, finish]
  · simp only [translate, simulateQ_spec_query, handler, StateT.run, simulateQ_map, begin, finish]

/-- Both exact translations commute with the same retained chronological interpreter through arbitrary adaptive continuations. -/
theorem program_source (full : Bool) (seeds : RegistrationNativeG3AuditedWorld.Seeds n)
    (work : OracleComp (Spec n KemSK) A) (before : State) :
    (simulateQ handler (simulateQ (translate full seeds) work)).run before =
      simulateQ (translate full seeds) ((simulateQ handler work).run before) := by
  induction work using OracleComp.inductionOn generalizing before with
  | pure value => rfl
  | query_bind query next ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
    rw [query_source]
    apply bind_congr
    rintro ⟨reply, after⟩
    exact ih reply after

open PqxdhServerAuthExperiment (Setup Checks)
variable {I Platform E : Type} {base : OracleSpec I}
variable [primitive : BeaconcryptCore.Refinement.AdapterSealPrimitive.Operations]
    (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire) (source : RegistrationNativeMldsa.Source)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (selectedOwner selectedAccept : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
    (reserveFrame : Nat → StateT Platform ProbComp (core.result.Result Unit E)) (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (BeaconcryptCore.Refinement.AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))

/-- The literal corrected whole public source materialization retains every original G2 event jointly with its full raw ledger, return state and P. -/
theorem run_source (seeds : RegistrationNativeG3AuditedWorld.Seeds n)
    (serverKeyId : U64) (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) A) (before : RegistrationNativePlatformPublicFrontend.State source Platform) :
    simulateQ (translate true seeds) (RegistrationNativeG2Trace.program (simulateQ RegistrationNativePlatformPublicCoinEmbedding.embed
      (RegistrationNativePlatformPublicFrontend.run (n := n) setup checks wire source sign selectedOwner selectedAccept publicPrekey view failure allocation
        reserveRegistration reservePeer reserveFrame erased helper writer serverKeyId bounds mode work before))) =
      simulateQ (translate false seeds) (RegistrationNativeG2Trace.program (simulateQ RegistrationNativePlatformPublicCoinEmbedding.embed
        (RegistrationNativePlatformPublicFrontend.run (n := n) setup checks wire source sign selectedOwner selectedAccept publicPrekey view failure allocation
          reserveRegistration reservePeer reserveFrame erased helper writer serverKeyId bounds mode work before))) := by
  have actual := congrArg (fun tree => (simulateQ RegistrationNativeG2Trace.handler tree).run RegistrationNativeG2Trace.initial)
    (RegistrationNativePlatformMaterializedFrontend.run_source setup checks wire source sign selectedOwner selectedAccept publicPrekey view failure allocation
      reserveRegistration reservePeer reserveFrame erased helper writer seeds serverKeyId bounds mode work before)
  rw [program_source, program_source] at actual
  exact actual

end BeaconcryptCore.Computational.RegistrationNativePlatformG3MaterializedTrace

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformG3MaterializedTrace.query_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformG3MaterializedTrace.query_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformG3MaterializedTrace.program_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformG3MaterializedTrace.program_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformG3MaterializedTrace.run_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformG3MaterializedTrace.run_source
