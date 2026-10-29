-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeProviderPersistence

/-! Actual provider-source sequencing and live-root persistence retain the full public frontend, current World, live KEM pool and provider state. The original open AST supplies capability-subset facts; the source interpreter supplies actual memo correctness and preservation. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeProviderExecution
open PqxdhServerAuthExperiment (Setup)
open RegistrationNativeProviderInterpreter (Provider)
open RegistrationNativeProviderSource (FrontState execute close)
open RegistrationNativePublicSourceState (Live MemoCorrect)
variable {n : Nat} {ι KemSK ProviderState Value : Type} {base : OracleSpec ι}
variable {source : RegistrationNativeMldsa.Source}

private theorem execute_run (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (provider : Provider KemSK ProviderState) (work : RegistrationNativePublicFrontend.M n KemSK source Value)
    (before : FrontState n KemSK ProviderState source) :
    (execute setup wire route sign seed scalar provider work).run before =
      (fun result => (result.1.1, (result.1.2, result.2))) <$>
        (close setup seed scalar
          (simulateQ (RegistrationNativeProviderInterpreter.handler setup wire route sign provider) (work.run before.1))).run before.2 := rfl

private theorem close_bind {X Y : Type} (setup : Setup base KemSK)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (first : RegistrationNativeProviderInterpreter.M n KemSK ProviderState X)
    (next : X → RegistrationNativeProviderInterpreter.M n KemSK ProviderState Y)
    (before : RegistrationNativeProviderInterpreter.State n KemSK ProviderState) :
    (close setup seed scalar (first >>= next)).run before = (do
      let reached ← (close setup seed scalar first).run before
      (close setup seed scalar (next reached.1)).run reached.2) := by
  change simulateQ (RegistrationNativeSourceRoot.handler setup.source setup.hmac setup.joint setup.dh seed scalar)
    ((first >>= next).run before) = _
  rw [StateT.run_bind, simulateQ_bind]
  rfl

theorem execute_bind {Result : Type} (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (provider : Provider KemSK ProviderState)
    (first : RegistrationNativePublicFrontend.M n KemSK source Value)
    (next : Value → RegistrationNativePublicFrontend.M n KemSK source Result)
    (before : FrontState n KemSK ProviderState source) :
    (execute setup wire route sign seed scalar provider (first >>= next)).run before = (do
      let reached ← (execute setup wire route sign seed scalar provider first).run before
      (execute setup wire route sign seed scalar provider (next reached.1)).run reached.2) := by
  rw [execute_run, StateT.run_bind, simulateQ_bind, close_bind]
  simp only [map_bind, execute_run, bind_map_left]

/-- All earlier prepared source roots persist through any actual frontend operation and provider interleaving. -/
theorem roots (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (provider : Provider KemSK ProviderState) (work : RegistrationNativePublicFrontend.M n KemSK source Value)
    (before : FrontState n KemSK ProviderState source) (result : Value × FrontState n KemSK ProviderState source)
    (correct : MemoCorrect setup seed scalar before.2.1.roots)
    (supported : result ∈ support ((execute setup wire route sign seed scalar provider work).run before)) :
    MemoCorrect setup seed scalar result.2.2.1.roots ∧
      ∀ message root, before.2.1.roots message = some root → result.2.2.1.roots message = some root := by
  change result ∈ support ((fun output => (output.1.1, (output.1.2, output.2))) <$>
    (close setup seed scalar
      (simulateQ (RegistrationNativeProviderInterpreter.handler setup wire route sign provider) (work.run before.1))).run before.2) at supported
  rw [support_map] at supported
  obtain ⟨inner, reached, rfl⟩ := supported
  exact RegistrationNativeProviderPersistence.program_stable setup wire route sign seed scalar provider
    (work.run before.1) before.2 inner correct reached

theorem live_of_subset (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (provider : Provider KemSK ProviderState) (work : RegistrationNativePublicFrontend.M n KemSK source Value)
    (before : FrontState n KemSK ProviderState source) (result : Value × FrontState n KemSK ProviderState source)
    (subset : ∀ output ∈ support (work.run before.1), ∀ ready,
      some ready ∈ output.2.server.sessions → some ready ∈ before.1.server.sessions)
    (live : Live before.1 before.2.1) (correct : MemoCorrect setup seed scalar before.2.1.roots)
    (supported : result ∈ support ((execute setup wire route sign seed scalar provider work).run before)) :
    Live result.2.1 result.2.2.1 ∧ MemoCorrect setup seed scalar result.2.2.1.roots := by
  have stable := roots setup wire route sign seed scalar provider work before result correct supported
  have observed := RegistrationNativeProviderSource.observed_support setup wire route sign seed scalar provider work before result supported
  refine ⟨?_, stable.1⟩
  intro ready member
  obtain ⟨root, stored⟩ := live ready (subset (result.1, result.2.1) observed ready member)
  exact ⟨root, stable.2 ready.reference root stored⟩

/-- Owner creation, publication and finish keep every Server session while preserving actual private source receipts. -/
theorem beacon_live (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (provider : Provider KemSK ProviderState)
    (work : RegistrationNativePublicOwners.M n KemSK RegistrationServerRoleBackend.State source Value)
    (before : FrontState n KemSK ProviderState source) (result : Value × FrontState n KemSK ProviderState source)
    (live : Live before.1 before.2.1) (correct : MemoCorrect setup seed scalar before.2.1.roots)
    (supported : result ∈ support ((execute setup wire route sign seed scalar provider
      (RegistrationNativePublicFrontend.beacon work)).run before)) :
    Live result.2.1 result.2.2.1 ∧ MemoCorrect setup seed scalar result.2.2.1.roots := by
  apply live_of_subset setup wire route sign seed scalar provider _ before result _ live correct supported
  intro output reached ready member
  simp only [RegistrationNativePublicFrontend.beacon, StateT.run, support_map] at reached
  obtain ⟨inner, _possible, rfl⟩ := reached
  exact member

theorem lifted_live (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (provider : Provider KemSK ProviderState) (work : OracleComp (RegistrationNativePublicFrontend.Spec n KemSK) Value)
    (before : FrontState n KemSK ProviderState source) (result : Value × FrontState n KemSK ProviderState source)
    (live : Live before.1 before.2.1) (correct : MemoCorrect setup seed scalar before.2.1.roots)
    (supported : result ∈ support ((execute setup wire route sign seed scalar provider (StateT.lift work)).run before)) :
    Live result.2.1 result.2.2.1 ∧ MemoCorrect setup seed scalar result.2.2.1.roots := by
  apply live_of_subset setup wire route sign seed scalar provider _ before result _ live correct supported
  intro output reached ready member
  simp only [StateT.run_lift, bind_pure_comp, support_map] at reached
  obtain ⟨inner, _possible, rfl⟩ := reached
  exact member

end BeaconcryptCore.Computational.RegistrationNativeProviderExecution

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeProviderExecution.execute_bind' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeProviderExecution.execute_bind
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeProviderExecution.roots' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeProviderExecution.roots
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeProviderExecution.live_of_subset' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeProviderExecution.live_of_subset
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeProviderExecution.beacon_live' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeProviderExecution.beacon_live
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeProviderExecution.lifted_live' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeProviderExecution.lifted_live
