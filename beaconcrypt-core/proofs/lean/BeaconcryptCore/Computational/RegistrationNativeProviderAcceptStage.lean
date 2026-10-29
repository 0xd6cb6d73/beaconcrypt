-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeProviderAcceptMemo
import BeaconcryptCore.Computational.RegistrationNativeProviderAcceptSdk
import BeaconcryptCore.Computational.RegistrationServerProviderReferenceStage

/-! The actual source prepare callback records the private returned root before clearing it from the public capability. Resetting only that private memo gives the generic native agreement stage on the same current environment, World, cache, pool and provider phase. No real-KEM specialization is used. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeProviderAcceptStage
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeProviderInterpreter (Provider)
open RegistrationNativeProviderSource (localImpl)
open RegistrationNativeProviderAcceptRun (Auxiliary State close)
variable {n : Nat} {ι KemSK ProviderState : Type} {base : OracleSpec ι}

def resetAux (memo : RegistrationNativeReferenceInterpreter.State) (before : Auxiliary n KemSK ProviderState) : Auxiliary n KemSK ProviderState :=
  (before.1, RegistrationNativeProviderAcceptMemo.reset memo before.2)

def reset (memo : RegistrationNativeReferenceInterpreter.State) (before : State n KemSK ProviderState) : State n KemSK ProviderState :=
  (before.1, resetAux memo before.2)

theorem prepare_project (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (provider : Provider KemSK ProviderState) (selected : Bool)
    (binding : session.RegistrationBinding)
    (input : PqxdhServerRootPreparation.Inputs registration.InitPacket Unit PqxdhJointIdentity.PeerEncoding)
    (memo : RegistrationNativeReferenceInterpreter.State) (before : RegistrationNativeProviderInterpreter.State n KemSK ProviderState) :
    Prod.map id (RegistrationNativeProviderAcceptMemo.reset memo) <$>
      (simulateQ (localImpl setup wire route sign seed scalar provider selected)
        (simulateQ RegistrationBeaconReferenceCompiler.prepare (RegistrationServerReferenceRoot.client binding input))).run before =
      (fun reply => (reply, RegistrationNativeProviderAcceptMemo.reset memo before)) <$>
        simulateQ (RegistrationServerReferenceSourceClient.prepare setup.source setup.joint setup.dh seed scalar)
          (RegistrationServerReferenceRoot.client binding input) := by
  classical
  by_cases admitted : PqxdhServerRelatedRootInput.localNonzero input
  · have actual := RegistrationNativeProviderLocal.prepare_run setup wire route sign seed scalar provider selected
      (RegistrationNativeRelatedFamily.Message.ofLegacy (PqxdhServerRelatedRootInput.message input)) before
    simp only [RegistrationServerReferenceRoot.client, admitted, not_true_eq_false, ite_false,
      simulateQ_bind, simulateQ_spec_query, RegistrationBeaconReferenceCompiler.prepare, StateT.run_bind,
      pure_bind, simulateQ_pure, StateT.run_pure, map_pure,
      RegistrationServerReferenceSourceClient.prepare]
    rw [actual]
    cases root : RegistrationNativeSourceRoot.value setup.source setup.joint setup.dh seed scalar
      (RegistrationNativeRelatedFamily.Message.ofLegacy (PqxdhServerRelatedRootInput.message input)) <;>
      simp only [Option.map_none, Option.map_some, pure_bind, RegistrationNativeProviderAcceptMemo.reset]
    all_goals rfl
  · simp only [RegistrationServerReferenceRoot.client, admitted, not_false_eq_true, ite_true,
      simulateQ_pure, StateT.run_pure, map_pure]
    rfl

/-- The concrete prepare's private memo update is retained in execution and erased only from this explicit stage observation. -/
theorem agreement_project (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (provider : Provider KemSK ProviderState) (selected : Bool)
    (packet : registration.InitPacket) (authenticated : registration.AuthenticatedInit)
    (memo : RegistrationNativeReferenceInterpreter.State) (before : State n KemSK ProviderState) :
    Prod.map id (reset memo) <$>
      (close (localImpl setup wire route sign seed scalar provider selected)
        (RegistrationServerOpenReferenceCompiler.agreement setup checks packet authenticated)).run before =
      (fun result => (result.1, (before.1, resetAux memo result.2))) <$>
        (RegistrationServerProviderReferenceStage.plainStage setup checks wire route sign seed scalar provider selected packet authenticated).run before.2 := by
  rw [RegistrationNativeProviderAcceptRun.agreement_run]
  simp only [RegistrationServerProviderReferenceStage.plainStage, StateT.run_bind, map_bind]
  apply bind_congr
  rintro ⟨input, current⟩
  cases input with
  | none => simp only [map_pure]; rfl
  | some input =>
      have prepared := congrArg (fun distribution => (fun result => (result.1, (before.1, (current.1, result.2)))) <$> distribution)
        (prepare_project setup wire route sign seed scalar provider selected authenticated.binding input memo current.2)
      simpa only [Functor.map_map, Prod.map_def, id_eq, reset, resetAux, StateT.run_lift, bind_pure_comp] using prepared

end BeaconcryptCore.Computational.RegistrationNativeProviderAcceptStage

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeProviderAcceptStage.prepare_project' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeProviderAcceptStage.prepare_project
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeProviderAcceptStage.agreement_project' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeProviderAcceptStage.agreement_project
