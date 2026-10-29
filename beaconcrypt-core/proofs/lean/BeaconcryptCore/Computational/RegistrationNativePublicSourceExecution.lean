-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePublicSourceSupport
import BeaconcryptCore.Computational.RegistrationNativePublicSourceLive

/-! One actual source execution layer for the complete mixed public frontend. Structural session invariants and prepared-root receipts are transported through the real private source interpreter, retaining the frontend, World and opaque pool as separate explicit coordinates. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePublicSourceExecution
open PqxdhServerAuthExperiment (Setup)
open RegistrationNativePublicSourceServer (State)
open RegistrationNativePublicSourceState (Live MemoCorrect)
variable {n : Nat} {ι KemSK Value : Type} {base : OracleSpec ι} {source : RegistrationNativeMldsa.Source}

noncomputable def execute (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (work : RegistrationNativePublicFrontend.M n KemSK source Value) : StateT (State n KemSK source) ProbComp Value := fun before =>
  (fun result => (result.1.1, (result.1.2, result.2))) <$>
    (RegistrationNativePublicSourceEffects.close setup seed scalar
      (simulateQ (RegistrationNativePublicInterpreter.handler setup wire route sign) (work.run before.1))).run before.2

private theorem execute_run (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (work : RegistrationNativePublicFrontend.M n KemSK source Value) (before : State n KemSK source) :
    (execute setup wire route sign seed scalar work).run before =
      (fun result => (result.1.1, (result.1.2, result.2))) <$>
        (RegistrationNativePublicSourceEffects.close setup seed scalar
          (simulateQ (RegistrationNativePublicInterpreter.handler setup wire route sign) (work.run before.1))).run before.2 := rfl

private theorem close_bind {X Y : Type} (setup : Setup base KemSK)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (first : RegistrationNativePublicInterpreter.M n KemSK X)
    (next : X → RegistrationNativePublicInterpreter.M n KemSK Y)
    (before : RegistrationNativePublicInterpreter.State n KemSK) :
    (RegistrationNativePublicSourceEffects.close setup seed scalar (first >>= next)).run before = (do
      let reached ← (RegistrationNativePublicSourceEffects.close setup seed scalar first).run before
      (RegistrationNativePublicSourceEffects.close setup seed scalar (next reached.1)).run reached.2) := by
  change simulateQ (RegistrationNativeSourceRoot.handler setup.source setup.hmac setup.joint setup.dh seed scalar)
    ((first >>= next).run before) = _
  rw [StateT.run_bind, simulateQ_bind]
  rfl

/-- Actual source interpretation commutes with adaptive frontend sequencing on the same World, pool and memo state. -/
theorem execute_bind {Result : Type} (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (first : RegistrationNativePublicFrontend.M n KemSK source Value)
    (next : Value → RegistrationNativePublicFrontend.M n KemSK source Result)
    (before : State n KemSK source) :
    (execute setup wire route sign seed scalar (first >>= next)).run before = (do
      let reached ← (execute setup wire route sign seed scalar first).run before
      (execute setup wire route sign seed scalar (next reached.1)).run reached.2) := by
  rw [execute_run, StateT.run_bind, simulateQ_bind, close_bind]
  simp only [map_bind, execute_run, bind_map_left]

/-- Every actual source outcome retains an output permitted by the original open frontend, including its complete public poststate. -/
theorem observed_support (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (work : RegistrationNativePublicFrontend.M n KemSK source Value)
    (before : State n KemSK source) (result : Value × State n KemSK source)
    (supported : result ∈ support ((execute setup wire route sign seed scalar work).run before)) :
    (result.1, result.2.1) ∈ support (work.run before.1) := by
  rw [execute_run, support_map] at supported
  obtain ⟨inner, reached, equal⟩ := supported
  have observed := RegistrationNativePublicSourceSupport.frontend_support setup wire route sign seed scalar
    (work.run before.1) before.2 inner reached
  have same : inner.1 = (result.1, result.2.1) := congrArg (fun output => (output.1, output.2.1)) equal
  rw [← same]
  exact observed

/-- Any actual source frontend operation preserves functional memo correctness and every earlier successful root preparation. -/
theorem roots (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (work : RegistrationNativePublicFrontend.M n KemSK source Value)
    (before : State n KemSK source) (result : Value × State n KemSK source)
    (correct : MemoCorrect setup seed scalar before.2.roots)
    (supported : result ∈ support ((execute setup wire route sign seed scalar work).run before)) :
    MemoCorrect setup seed scalar result.2.2.roots ∧
      ∀ message root, before.2.roots message = some root → result.2.2.roots message = some root := by
  change result ∈ support ((fun output => (output.1.1, (output.1.2, output.2))) <$>
    (RegistrationNativePublicSourceEffects.close setup seed scalar
      (simulateQ (RegistrationNativePublicInterpreter.handler setup wire route sign) (work.run before.1))).run before.2) at supported
  rw [support_map] at supported
  obtain ⟨inner, reached, rfl⟩ := supported
  exact RegistrationNativePublicSourcePersistence.program_stable setup wire route sign seed scalar
    (work.run before.1) before.2 inner correct reached

/-- A source operation that only removes existing session capabilities preserves the actual internal live-root invariant. -/
theorem live_of_subset (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (work : RegistrationNativePublicFrontend.M n KemSK source Value)
    (before : State n KemSK source) (result : Value × State n KemSK source)
    (subset : ∀ output ∈ support (work.run before.1), ∀ ready,
      some ready ∈ output.2.server.sessions → some ready ∈ before.1.server.sessions)
    (live : Live before.1 before.2) (correct : MemoCorrect setup seed scalar before.2.roots)
    (supported : result ∈ support ((execute setup wire route sign seed scalar work).run before)) :
    Live result.2.1 result.2.2 ∧ MemoCorrect setup seed scalar result.2.2.roots := by
  have stable := roots setup wire route sign seed scalar work before result correct supported
  refine ⟨?_, stable.1⟩
  intro ready member
  change result ∈ support ((fun output => (output.1.1, (output.1.2, output.2))) <$>
    (RegistrationNativePublicSourceEffects.close setup seed scalar
      (simulateQ (RegistrationNativePublicInterpreter.handler setup wire route sign) (work.run before.1))).run before.2) at supported
  rw [support_map] at supported
  obtain ⟨inner, reached, equal⟩ := supported
  have observed := RegistrationNativePublicSourceSupport.frontend_support setup wire route sign seed scalar
    (work.run before.1) before.2 inner reached
  have sameFrontend : inner.1.2 = result.2.1 := congrArg (fun output => output.2.1) equal
  obtain ⟨root, stored⟩ := live ready (subset inner.1 observed ready (sameFrontend ▸ member))
  exact ⟨root, stable.2 ready.reference root stored⟩

/-- Actual owner construction, outgoing publication and finish preserve all Server live-root receipts through their original World effects. -/
theorem beacon_live (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (work : RegistrationNativePublicOwners.M n KemSK RegistrationServerRoleBackend.State source Value)
    (before : State n KemSK source) (result : Value × State n KemSK source)
    (live : Live before.1 before.2) (correct : MemoCorrect setup seed scalar before.2.roots)
    (supported : result ∈ support ((execute setup wire route sign seed scalar
      (RegistrationNativePublicFrontend.beacon work)).run before)) :
    Live result.2.1 result.2.2 ∧ MemoCorrect setup seed scalar result.2.2.roots := by
  apply live_of_subset setup wire route sign seed scalar _ before result _ live correct supported
  intro output reached ready member
  simp only [RegistrationNativePublicFrontend.beacon, StateT.run, support_map] at reached
  obtain ⟨inner, _possible, rfl⟩ := reached
  exact member

/-- Direct public hash, uniform and ongoing record callbacks keep the Server capability roster intact while preserving their real private World effects. -/
theorem lifted_live (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (work : OracleComp (RegistrationNativePublicFrontend.Spec n KemSK) Value)
    (before : State n KemSK source) (result : Value × State n KemSK source)
    (live : Live before.1 before.2) (correct : MemoCorrect setup seed scalar before.2.roots)
    (supported : result ∈ support ((execute setup wire route sign seed scalar (StateT.lift work)).run before)) :
    Live result.2.1 result.2.2 ∧ MemoCorrect setup seed scalar result.2.2.roots := by
  apply live_of_subset setup wire route sign seed scalar _ before result _ live correct supported
  intro output reached ready member
  simp only [StateT.run_lift, bind_pure_comp, support_map] at reached
  obtain ⟨inner, _possible, rfl⟩ := reached
  exact member

end BeaconcryptCore.Computational.RegistrationNativePublicSourceExecution
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePublicSourceExecution.roots' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePublicSourceExecution.roots
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePublicSourceExecution.live_of_subset' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePublicSourceExecution.live_of_subset
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePublicSourceExecution.beacon_live' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePublicSourceExecution.beacon_live
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePublicSourceExecution.lifted_live' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePublicSourceExecution.lifted_live

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePublicSourceExecution.execute_bind' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePublicSourceExecution.execute_bind
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePublicSourceExecution.observed_support' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePublicSourceExecution.observed_support
