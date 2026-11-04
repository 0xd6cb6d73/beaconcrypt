-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicFrontend
import BeaconcryptCore.Computational.RegistrationNativePublicSourcePersistence
import BeaconcryptCore.Computational.RegistrationNativePublicSourceSupport
/-! The corrected adaptive public frontend is interpreted beside one private World, generated-key pool and earlier-root memo. External uniform requests remain separate from counted native effects. Only the source leaf interpreter and private data layout are reused; none of the earlier callback or complete-profile equations is assumed. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicSourceExecution
open PqxdhServerAuthExperiment (Setup)
open RegistrationNativeRelatedRoot (RootSpec)
open RegistrationNativePublicSourceState (Live MemoCorrect)
open RegistrationNativePublicSourceEffects (close)
variable {n : Nat} {ι KemSK Platform Value : Type} {base : OracleSpec ι} {source : RegistrationNativeMldsa.Source}

abbrev State (n : Nat) (KemSK Platform : Type) (source : RegistrationNativeMldsa.Source) :=
  RegistrationNativePlatformPublicFrontend.State source Platform × RegistrationNativePublicInterpreter.State n KemSK

noncomputable def handler (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply) :
    QueryImpl (RegistrationNativePlatformPublicFrontend.Spec n KemSK) (RegistrationNativePublicInterpreter.M n KemSK)
  | .inl query => RegistrationNativePublicInterpreter.handler setup wire route sign query
  | .inr query => StateT.lift (RootSpec.query (.inl query))

noncomputable def execute (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (work : RegistrationNativePlatformPublicFrontend.M n KemSK Platform source Value) :
    StateT (State n KemSK Platform source) ProbComp Value := fun before =>
  (fun result => (result.1.1, (result.1.2, result.2))) <$>
    (close setup seed scalar (simulateQ (handler setup wire route sign) (work.run before.1))).run before.2

/-- Restoring the selected material is a private interpretation; the persistent platform coordinate remains literal. -/
noncomputable def restore (setup : Setup base KemSK) (seed : PqxdhJointIdentity.IdentitySeed)
    (scalar : PqxdhJointGapDh.ScalarBytes) (before : State n KemSK Platform source) :
    RegistrationNativeExperiment.State n KemSK source × Platform :=
  (RegistrationNativePublicSourceState.restore (RegistrationNativePublicSourceState.roots setup seed scalar)
    scalar before.1.1 before.2, before.1.2)

private theorem query_stable (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (query : (RegistrationNativePlatformPublicFrontend.Spec n KemSK).Domain)
    (before : RegistrationNativePublicInterpreter.State n KemSK)
    (result : (RegistrationNativePlatformPublicFrontend.Spec n KemSK).Range query × RegistrationNativePublicInterpreter.State n KemSK)
    (correct : MemoCorrect setup seed scalar before.roots)
    (supported : result ∈ support ((close setup seed scalar (handler setup wire route sign query)).run before)) :
    MemoCorrect setup seed scalar result.2.roots ∧
      ∀ message root, before.roots message = some root → result.2.roots message = some root := by
  cases query with
  | inl query =>
      exact RegistrationNativePublicSourcePersistence.query_stable setup wire route sign seed scalar query
        before result correct supported
  | inr query =>
      change result ∈ support ((fun reply => (reply, before)) <$> (unifSpec.query query : ProbComp _)) at supported
      rw [support_map] at supported
      obtain ⟨reply, _reached, equal⟩ := supported
      cases equal
      exact ⟨correct, fun _ _ stored => stored⟩

private theorem program_stable (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (work : OracleComp (RegistrationNativePlatformPublicFrontend.Spec n KemSK) Value)
    (before : RegistrationNativePublicInterpreter.State n KemSK) (result : Value × RegistrationNativePublicInterpreter.State n KemSK)
    (correct : MemoCorrect setup seed scalar before.roots)
    (supported : result ∈ support ((close setup seed scalar (simulateQ (handler setup wire route sign) work)).run before)) :
    MemoCorrect setup seed scalar result.2.roots ∧
      ∀ message root, before.roots message = some root → result.2.roots message = some root := by
  induction work using OracleComp.inductionOn generalizing before result with
  | pure value =>
      change result ∈ support (pure (value, before)) at supported
      rw [mem_support_pure_iff] at supported
      cases supported
      exact ⟨correct, fun _ _ stored => stored⟩
  | query_bind query continuation ih =>
      have split : (close setup seed scalar (simulateQ (handler setup wire route sign)
          (((RegistrationNativePlatformPublicFrontend.Spec n KemSK).query query :
            OracleComp (RegistrationNativePlatformPublicFrontend.Spec n KemSK) _) >>= continuation))).run before = (do
          let step ← (close setup seed scalar (handler setup wire route sign query)).run before
          (close setup seed scalar (simulateQ (handler setup wire route sign) (continuation step.1))).run step.2) := by
        simp only [close, simulateQ_bind, simulateQ_spec_query, StateT.run,
          StateT.monad_bind_def, StateT.bind, simulateQ_bind]
      rw [split, mem_support_bind_iff] at supported
      obtain ⟨step, called, continued⟩ := supported
      have first := query_stable setup wire route sign seed scalar query before step correct called
      have rest := ih step.1 step.2 result first.1 continued
      exact ⟨rest.1, fun message root stored => rest.2 message root (first.2 message root stored)⟩

/-- Entire corrected adaptive frontend programs preserve every actual earlier private root, including all external allocator outcomes. -/
theorem roots (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (work : RegistrationNativePlatformPublicFrontend.M n KemSK Platform source Value)
    (before : State n KemSK Platform source) (result : Value × State n KemSK Platform source)
    (correct : MemoCorrect setup seed scalar before.2.roots)
    (supported : result ∈ support ((execute setup wire route sign seed scalar work).run before)) :
    MemoCorrect setup seed scalar result.2.2.roots ∧
      ∀ message root, before.2.roots message = some root → result.2.2.roots message = some root := by
  change result ∈ support ((fun output => (output.1.1, (output.1.2, output.2))) <$>
    (close setup seed scalar (simulateQ (handler setup wire route sign) (work.run before.1))).run before.2) at supported
  rw [support_map] at supported
  obtain ⟨inner, reached, rfl⟩ := supported
  exact program_stable setup wire route sign seed scalar (work.run before.1) before.2 inner correct reached


/-- Private source interpretation sequences the new public callbacks on the same World, memo and external state. -/
theorem execute_bind {Result : Type} (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (first : RegistrationNativePlatformPublicFrontend.M n KemSK Platform source Value)
    (continuation : Value → RegistrationNativePlatformPublicFrontend.M n KemSK Platform source Result)
    (before : State n KemSK Platform source) :
    (execute setup wire route sign seed scalar (first >>= continuation)).run before = (do
      let reached ← (execute setup wire route sign seed scalar first).run before
      (execute setup wire route sign seed scalar (continuation reached.1)).run reached.2) := by
  simp only [execute, simulateQ_bind, close, StateT.run,
    StateT.monad_bind_def, StateT.bind, simulateQ_bind, map_bind, bind_map_left]

/-- Source execution preserves every output-only structural property of the actual corrected open frontend. -/
theorem observed_support (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (work : RegistrationNativePlatformPublicFrontend.M n KemSK Platform source Value)
    (before : State n KemSK Platform source) (result : Value × State n KemSK Platform source)
    (supported : result ∈ support ((execute setup wire route sign seed scalar work).run before)) :
    (result.1, result.2.1) ∈ support (work.run before.1) := by
  change result ∈ support ((fun output => (output.1.1, (output.1.2, output.2))) <$>
    (close setup seed scalar (simulateQ (handler setup wire route sign) (work.run before.1))).run before.2) at supported
  rw [support_map] at supported
  obtain ⟨inner, reached, equal⟩ := supported
  have interpreted := RegistrationNativePublicSourceSupport.simulate_support
    (RegistrationNativeSourceRoot.handler setup.source setup.hmac setup.joint setup.dh seed scalar)
    ((simulateQ (handler setup wire route sign) (work.run before.1)).run before.2) inner reached
  have observed : inner.1 ∈ support (work.run before.1) := by
    apply support_simulateQ_run'_subset (handler setup wire route sign) (work.run before.1) before.2
    rw [StateT.run'_eq, support_map]
    exact ⟨inner, interpreted, rfl⟩
  have same : inner.1 = (result.1, result.2.1) := congrArg (fun output => (output.1, output.2.1)) equal
  rw [← same]
  exact observed

/-- Any corrected callback that only removes earlier Server tokens preserves the internal live-root invariant. -/
theorem live_of_subset (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (work : RegistrationNativePlatformPublicFrontend.M n KemSK Platform source Value)
    (before : State n KemSK Platform source) (result : Value × State n KemSK Platform source)
    (subset : ∀ output ∈ support (work.run before.1), ∀ ready,
      some ready ∈ output.2.1.server.sessions → some ready ∈ before.1.1.server.sessions)
    (live : Live before.1.1 before.2) (correct : MemoCorrect setup seed scalar before.2.roots)
    (supported : result ∈ support ((execute setup wire route sign seed scalar work).run before)) :
    Live result.2.1.1 result.2.2 ∧ MemoCorrect setup seed scalar result.2.2.roots := by
  have stable := roots setup wire route sign seed scalar work before result correct supported
  refine ⟨?_, stable.1⟩
  intro ready member
  have permitted := observed_support setup wire route sign seed scalar work before result supported
  obtain ⟨root, stored⟩ := live ready (subset (result.1, result.2.1) permitted ready member)
  exact ⟨root, stable.2 ready.reference root stored⟩

end BeaconcryptCore.Computational.RegistrationNativePlatformPublicSourceExecution

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicSourceExecution.roots' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicSourceExecution.roots

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicSourceExecution.execute_bind' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicSourceExecution.execute_bind

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicSourceExecution.observed_support' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicSourceExecution.observed_support

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicSourceExecution.live_of_subset' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicSourceExecution.live_of_subset
