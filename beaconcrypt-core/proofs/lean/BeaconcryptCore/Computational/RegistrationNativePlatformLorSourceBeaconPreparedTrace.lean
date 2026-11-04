-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformLorSourcePreparedTraceCore
import BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerFinishScalar
/-! The actual optional-scalar Beacon preparation records its own returned reference in the same trace. The source echo law is individual per-prepare support; no fixed pin, marked atom, boxed interpreter or whole preparation premise is used. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceBeaconPreparedTrace
open PqxdhServerAuthExperiment (Setup)
open RegistrationNativeSecretWordMessage (Message BeaconReady)
open RegistrationNativeSecretWord (Key)
open RegistrationNativeSecretWordInterface (Spec LocalSpec)
open RegistrationNativePlatformLorSourcePreparedTraceCore (Prepared)
open RegistrationNativePlatformRecordPartnerFinishScalar (scalarLocal)
variable {n : Nat} {I KemSK Private : Type} {base : OracleSpec I}
variable (setup : Setup base KemSK)
    (implementation : QueryImpl (Spec n KemSK) (StateT Private ProbComp))
    (input : Message → Option Key)
    (echo : ∀message before result,result∈support ((implementation (.inl (.inl message))).run before) →
      result.1=(input message).map (fun _=>message))
local notation "actual" => RegistrationNativePlatformLorStatefulSupport.trace implementation
include echo

private theorem actual_echo (message reference : Message)
    (before after : RegistrationNativeSecretWordFrontendTrace.State × Private)
    (supported : (some reference,after)∈support ((actual (.inl (.inl message))).run before)) : reference=message := by
  have ordinary := RegistrationNativePlatformLorSourceKemTrace.query_support implementation (.inl (.inl message)) before (some reference,after) supported
  have expected := echo message before.2 (some reference,after.2) ordinary
  cases formed : input message with
  | none=>simp only [formed,Option.map_none] at expected;cases expected
  | some key=>
    simp only [formed,Option.map_some] at expected
    exact Option.some.inj expected

/-- The returned opaque reference has its actual same-name preparation tag under both scalar paths. -/
theorem query (scalar : Option PqxdhJointGapDh.ScalarBytes) (message reference : Message)
    (before after : RegistrationNativeSecretWordFrontendTrace.State × Private)
    (supported : (some reference,after)∈support (((scalarLocal setup actual scalar) (.inl message)).run before)) :
    Prepared reference after.1 := by
  cases scalar with
  | none=>
    have called : (some reference,after)∈support ((actual (.inl (.inl message))).run before) := by
      simpa only [scalarLocal,QueryImpl.compose,RegistrationNativeSecretWordInterface.liftLocal,simulateQ_spec_query] using supported
    have same := actual_echo implementation input echo message reference before after called
    rw [same]
    exact RegistrationNativePlatformLorSourcePreparedTraceCore.prepare_recorded implementation message before (some reference,after) called
  | some scalar=>
    simp only [scalarLocal,QueryImpl.compose,RegistrationNativeSecretWordOwners.ordinary] at supported
    cases formed : RegistrationNativeSecretWordLocalMessage.materialize setup.joint setup.dh scalar message with
    | none=>simp only [formed,simulateQ_pure,StateT.run_pure,mem_support_pure_iff] at supported;cases supported
    | some translated=>
      have called : (some reference,after)∈support ((actual (.inl (.inl translated))).run before) := by
        simpa only [formed,simulateQ_spec_query,QueryImpl.compose,RegistrationNativeSecretWordInterface.liftLocal] using supported
      have same := actual_echo implementation input echo translated reference before after called
      rw [same]
      exact RegistrationNativePlatformLorSourcePreparedTraceCore.prepare_recorded implementation translated before (some reference,after) called

/-- The successful actual Beacon root client records the very reference retained in its Ready result. -/
theorem root (scalar : Option PqxdhJointGapDh.ScalarBytes) (authenticated : registration.AuthenticatedResponse)
    (pending : RegistrationNativeSecretWordBeaconPrepare.Prepared registration.AuthenticatedResponse)
    (before : RegistrationNativeSecretWordFrontendTrace.State × Private)
    (result : RustM (Option BeaconReady) × (RegistrationNativeSecretWordFrontendTrace.State × Private))
    (supported : result∈support ((simulateQ (scalarLocal setup actual scalar)
      (simulateQ RegistrationNativeSecretWordInterface.prepare (RegistrationNativeSecretWordBeaconRoot.client authenticated pending))).run before))
    (ready : BeaconReady) (success : result.1=.ok (some ready)) : Prepared ready.reference result.2.1 := by
  simp only [RegistrationNativeSecretWordBeaconRoot.client,bind_pure_comp,simulateQ_map,simulateQ_spec_query,
    RegistrationNativeSecretWordInterface.prepare,StateT.run_map,support_map] at supported
  obtain ⟨⟨reply,after⟩,called,equal⟩ := supported
  cases equal
  cases reply with
  | none=>cases success
  | some reference=>
    simp only [Option.map_some,RustM.ok.injEq,Option.some.injEq] at success
    cases success
    exact query setup implementation input echo scalar (RegistrationNativeSecretWordBeaconRoot.message pending) reference before after called


variable {Auxiliary : Type} {source : RegistrationNativeMldsa.Source}
/-- Every successful actual Beacon agreement has its own preparation in the same reached trace, after the complete opaque collector. -/
theorem agreement (scalar : Option PqxdhJointGapDh.ScalarBytes)
    (owner : RegistrationBeaconReferenceCompiler.SelectedOwner source) (oneTime : PqxdhJointGapDh.ScalarBytes)
    (authenticated : registration.AuthenticatedResponse) (env : RegistrationWorldAgreementCompiler.EnvState Auxiliary)
    (before : RegistrationNativeSecretWordFrontendTrace.State × Private)
    (result : (RustM (Option BeaconReady) × RegistrationWorldAgreementCompiler.EnvState Auxiliary) ×
      (RegistrationNativeSecretWordFrontendTrace.State × Private))
    (supported : result∈support ((simulateQ (scalarLocal setup actual scalar)
      ((RegistrationNativeSecretWordBeaconCompiler.agreement (n := n) setup owner oneTime authenticated).run env)).run before))
    (ready : BeaconReady) (success : result.1.1=.ok (some ready)) : Prepared ready.reference result.2.1 := by
  simp only [RegistrationNativeSecretWordBeaconCompiler.agreement,StateT.run_bind,simulateQ_bind,StateT.run_bind,mem_support_bind_iff] at supported
  obtain ⟨collected,_collected,continued⟩ := supported
  cases found : collected.1.1 with
  | none=>
    simp only [found,StateT.run_pure,simulateQ_pure,StateT.run_pure,mem_support_pure_iff] at continued
    cases continued
    cases success
  | some pending=>
    simp only [found,StateT.run_lift,bind_pure_comp,simulateQ_map,StateT.run_map,support_map] at continued
    obtain ⟨finished,called,equal⟩ := continued
    cases equal
    exact root setup implementation input echo scalar authenticated pending collected.2 finished called ready success

/-- The complete literal authentication/collection prefix records its successful Ready before the material continuation can begin. -/
theorem preparation (scalar : Option PqxdhJointGapDh.ScalarBytes) (packet : Option registration.ResponsePacket)
    (owner : RegistrationBeaconReferenceCompiler.SelectedOwner source) (env : RegistrationWorldAgreementCompiler.EnvState Auxiliary)
    (before : RegistrationNativeSecretWordFrontendTrace.State × Private)
    (result : ((RustM (Option BeaconReady) × RegistrationBeaconReferenceCompiler.SelectedOwner source) ×
      RegistrationWorldAgreementCompiler.EnvState Auxiliary) × (RegistrationNativeSecretWordFrontendTrace.State × Private))
    (supported : result∈support ((simulateQ (scalarLocal setup actual scalar)
      (((RegistrationNativeSecretWordBeaconCompiler.finishPreparation (n := n) setup source packet).run owner).run env)).run before))
    (ready : BeaconReady) (success : result.1.1.1=.ok (some ready)) : Prepared ready.reference result.2.1 := by
  simp only [RegistrationNativeSecretWordBeaconCompiler.finishPreparation,StateT.run_bind,StateT.run_get,pure_bind] at supported
  cases phase : owner.phase with
  | fresh | freshWithCoins _ | established _ | aborted _=>
    simp only [phase,StateT.run_pure,simulateQ_pure,mem_support_pure_iff] at supported
    cases supported
    cases success
  | initSent pending oneTime=>
    simp only [phase] at supported
    cases moved : pending.aborted_state with
    | fail error | div=>
      simp only [moved,StateT.run_pure,simulateQ_pure,mem_support_pure_iff] at supported
      cases supported
      cases success
    | ok aborted=>
      simp only [moved,StateT.run_set,pure_bind,StateT.run_lift,bind_pure_comp,
        simulateQ_bind,StateT.run_bind,bind_map_left,mem_support_bind_iff] at supported
      obtain ⟨accepted,_called,continued⟩ := supported
      cases acceptedOutcome : accepted.1 with
      | fail error | div=>
        simp only [acceptedOutcome,StateT.run_pure,simulateQ_pure,StateT.run_pure,mem_support_pure_iff] at continued
        cases continued
        cases success
      | ok response=>cases response with
        | Err previous=>
          simp only [acceptedOutcome,StateT.run_pure,simulateQ_pure,StateT.run_pure,mem_support_pure_iff] at continued
          cases continued
          cases success
        | Ok authenticated=>
          simp only [acceptedOutcome,StateT.run_lift,bind_pure_comp,simulateQ_map,StateT.run_map,support_map] at continued
          obtain ⟨finished,called,equal⟩ := continued
          cases equal
          exact agreement setup implementation input echo scalar owner oneTime authenticated env accepted.2 finished called ready success

end BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceBeaconPreparedTrace
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceBeaconPreparedTrace.query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceBeaconPreparedTrace.query
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceBeaconPreparedTrace.root' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceBeaconPreparedTrace.root

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceBeaconPreparedTrace.agreement' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceBeaconPreparedTrace.agreement

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceBeaconPreparedTrace.preparation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceBeaconPreparedTrace.preparation
