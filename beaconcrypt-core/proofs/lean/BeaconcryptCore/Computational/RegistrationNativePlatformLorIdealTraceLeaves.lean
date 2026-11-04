-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformLorCtxLeaves
import BeaconcryptCore.Computational.RegistrationNativeSecretWordCheckedTrace
/-! Source-free chronological trace naturality evaluates only opaque words and descriptors. Actual material choices and each installation result remain literal; the dictionary law retains the complete symbolic/native private state and arbitrary persistent World service. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealTraceLeaves
open PqxdhServerAuthExperiment (Setup)
open PqxdhKemIndCca
open RegistrationNativePlatformLorCtxLeaves (World Symbolic frame nativeQuery nativeReply)
variable {n : Nat} {I KemSK Value : Type} {base : OracleSpec I}
local notation "WordTrace" => RegistrationNativeSecretWordFrontendTrace.State
local notation "NativeTrace" => RegistrationNativeG2Trace.State
local notation "state(" candidate ")" => RegistrationNativeSecretWordCheckedTrace.state candidate

/-- Each literal source query starts the same evaluated preparation, demand or role attempt. -/
theorem begin_source (candidate : MlKemSharedSecret) (query : (RegistrationNativeSecretWordInterface.Spec n KemSK).Domain)
    (before : WordTrace) :
    state(candidate) (RegistrationNativeSecretWordFrontendTrace.begin query before) =
      RegistrationNativeG2Trace.begin (nativeQuery candidate query) (state(candidate) before) := by
  rcases query with (message | (message | common) | routed) | record
  · simp only [RegistrationNativeSecretWordFrontendTrace.begin,RegistrationNativeG2Trace.begin,nativeQuery,
      RegistrationNativeSecretWordCheckedTrace.state,List.map_append,List.map_cons,List.map_nil,
      RegistrationNativeSecretWordCheckedTrace.event,Option.map_none]
  · simp only [RegistrationNativeSecretWordFrontendTrace.begin,RegistrationNativeG2Trace.begin,nativeQuery,
      RegistrationNativeSecretWordCheckedTrace.state,List.map_append,List.map_cons,List.map_nil,
      RegistrationNativeSecretWordCheckedTrace.event,Option.map_some]
  · rcases common with publication | effect
    · rfl
    · rcases effect with coin | capability
      · rfl
      · cases capability <;> first
        | rfl
        | exact RegistrationNativeSecretWordCheckedTrace.attempt_state candidate _ before
  · rcases routed with (other | key) | (pool | key)
    all_goals rfl
  · rfl

/-- Every reply, including refused material and failed installation, completes the same evaluated trace. -/
theorem finish_source (candidate : MlKemSharedSecret) (query : (RegistrationNativeSecretWordInterface.Spec n KemSK).Domain)
    (reply : (RegistrationNativeSecretWordInterface.Spec n KemSK).Range query) (before : WordTrace) :
    state(candidate) (RegistrationNativeSecretWordFrontendTrace.finish query reply before) =
      RegistrationNativeG2Trace.finish (nativeQuery candidate query) (nativeReply candidate query reply) (state(candidate) before) := by
  rcases query with (message | (message | common) | routed) | record
  · rfl
  · rfl
  · rcases common with publication | effect
    · rfl
    · rcases effect with coin | capability
      · rfl
      · cases capability <;> first
        | rfl
        | exact RegistrationNativeSecretWordCheckedTrace.installed_state candidate _ reply before
  · rcases routed with (other | key) | (pool | key)
    · rfl
    · simp only [RegistrationNativeSecretWordFrontendTrace.finish,RegistrationNativeG2Trace.finish,nativeQuery,nativeReply,
        RegistrationNativeSecretWordKemProvider.evalReply,RegistrationNativeSecretWordCheckedTrace.state,
        List.map_append,List.map_cons,List.map_nil,RegistrationNativeSecretWordCheckedTrace.event,Prod.map_def,id_eq]
    · cases pool <;> rfl
    · simp only [RegistrationNativeSecretWordFrontendTrace.finish,RegistrationNativeG2Trace.finish,nativeQuery,nativeReply,
        RegistrationNativeSecretWordKemProvider.evalReply,RegistrationNativeSecretWordCheckedTrace.state,
        List.map_append,List.map_cons,List.map_nil,RegistrationNativeSecretWordCheckedTrace.event,Prod.map_def,id_eq]
  · rfl

variable (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes) (candidate : MlKemSharedSecret)
    (unused : QueryImpl RegistrationNativeSecretWordService.Combined (World n))
    (selected : Nat) (pairs : List (MlKem768PublicKey × KemSK)) (publicKey : MlKem768PublicKey) (challenge : MlKem768Ciphertext)
local notation "symbolic" => RegistrationNativePlatformLorCtxLeaves.lower setup wire sign seed scalar candidate unused
  (RegistrationNativeSecretWordKemEarly.early setup.baseImpl setup.kem selected pairs publicKey challenge)
local notation "native" => RegistrationNativeSelectiveHiddenInterpreter.handler setup wire sign seed scalar candidate
  (RegistrationNativeSecretWordKemEarly.actual setup.baseImpl setup.kem selected pairs publicKey challenge candidate)

noncomputable def symbolicTrace : QueryImpl (RegistrationNativeSecretWordInterface.Spec n KemSK)
    (StateT (WordTrace × Symbolic n KemSK) (World n)) :=
  (QueryImpl.mapStateTBase symbolic RegistrationNativeSecretWordFrontendTrace.handler).flattenStateT
noncomputable def nativeTrace : QueryImpl (RegistrationNativePublicFrontend.Spec n KemSK)
    (StateT (NativeTrace × RegistrationNativeSelectiveHiddenInterpreter.State n KemSK RegistrationNativeKemSwitchSource.Phase) (World n)) :=
  (QueryImpl.mapStateTBase native RegistrationNativeG2Trace.handler).flattenStateT

def project : WordTrace × Symbolic n KemSK → NativeTrace × RegistrationNativeSelectiveHiddenInterpreter.State n KemSK RegistrationNativeKemSwitchSource.Phase :=
  Prod.map (state(candidate)) (frame candidate)

private theorem map_apply {S A B : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (f : A → B) (work : StateT S m A) (before : S) :
    (f <$> work) before = Prod.map f id <$> work before := StateT.run_map _ _ _

/-- The actual closed source dictionaries retain the same chronological query result and full private poststate. -/
theorem query_source (query : (RegistrationNativeSecretWordInterface.Spec n KemSK).Domain)
    (before : WordTrace × Symbolic n KemSK) :
    Prod.map (nativeReply candidate query) (project candidate) <$>
      (symbolicTrace setup wire sign seed scalar candidate unused selected pairs publicKey challenge query).run before =
      (nativeTrace setup wire sign seed scalar candidate selected pairs publicKey challenge (nativeQuery candidate query)).run (project candidate before) := by
  rw [symbolicTrace,nativeTrace,QueryImpl.flattenStateT_mapStateTBase_apply_run,QueryImpl.flattenStateT_mapStateTBase_apply_run]
  simp only [RegistrationNativeSecretWordFrontendTrace.handler,RegistrationNativeG2Trace.handler,StateT.run,
    simulateQ_map,simulateQ_spec_query,map_apply,Functor.map_map,project,Prod.map_def,id_eq]
  have related := RegistrationNativePlatformLorCtxLeaves.query_source setup wire sign seed scalar candidate unused selected pairs publicKey challenge query before.2
  have lifted := congrArg (Functor.map (fun result => (result.1,
    (RegistrationNativeG2Trace.finish (nativeQuery candidate query) result.1
      (RegistrationNativeG2Trace.begin (nativeQuery candidate query) (state(candidate) before.1)),result.2)))) related
  simpa only [Functor.map_map,Prod.map_def,id_eq,finish_source,begin_source,StateT.run] using lifted

/-- Closing the same trace query under any persistent physical World preserves its full poststate. -/
theorem physical_query {Physical : Type}
    (physical : QueryImpl (PqxdhRecordLiftInterface.WorldSpec n) (StateT Physical ProbComp))
    (query : (RegistrationNativeSecretWordInterface.Spec n KemSK).Domain)
    (before : WordTrace × Symbolic n KemSK) (physicalBefore : Physical) :
    Prod.map (Prod.map (nativeReply candidate query) (project candidate)) id <$>
      (simulateQ physical ((symbolicTrace setup wire sign seed scalar candidate unused selected pairs publicKey challenge query).run before)).run physicalBefore =
      (simulateQ physical ((nativeTrace setup wire sign seed scalar candidate selected pairs publicKey challenge (nativeQuery candidate query)).run
        (project candidate before))).run physicalBefore := by
  have related := query_source setup wire sign seed scalar candidate unused selected pairs publicKey challenge query before
  have closed := congrArg (fun work => (simulateQ physical work).run physicalBefore) related
  simpa only [simulateQ_map,StateT.run_map,Prod.map_def,id_eq] using closed

end BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealTraceLeaves

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealTraceLeaves.begin_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealTraceLeaves.begin_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealTraceLeaves.finish_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealTraceLeaves.finish_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealTraceLeaves.query_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealTraceLeaves.query_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealTraceLeaves.physical_query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealTraceLeaves.physical_query
