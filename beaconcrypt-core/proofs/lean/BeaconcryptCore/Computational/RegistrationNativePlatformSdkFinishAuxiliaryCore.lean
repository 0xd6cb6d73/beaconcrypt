-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeFinishLifetime
import BeaconcryptCore.Computational.RegistrationNativeLocalEnvironmentFrame
open CoreModels Aeneas OracleComp OracleSpec beaconcrypt_core
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformSdkFinishAuxiliaryCore
open RegistrationNativeBeaconFrontend (Trusted Owner)
open RegistrationWorldAgreementCompiler (EnvState)
open RegistrationNativeBeaconPhaseCommutation (Lower)
open RegistrationNativeLocalEnvironmentFrame (Allowed)
variable {n : Nat} {I KemSK Auxiliary A B J : Type} {base : OracleSpec I} {spec : OracleSpec J}
variable {source : RegistrationNativeMldsa.Source}

def Holds (work : Lower n KemSK Auxiliary A) : Prop :=
  (∀before result,result∈support (work.run before) → result.2.auxiliary=before.auxiliary) ∧
  ∀before,AllQueriesSatisfy (work.run before) (Allowed (n:=n) (KemSK:=KemSK))

private theorem pure_holds (value : A) : Holds (pure value :Lower n KemSK Auxiliary A) :=by
  constructor
  · intro before result reached
    simp only [StateT.run_pure,support_pure,Set.mem_singleton_iff] at reached
    cases reached
    rfl
  · intro before
    exact allQueriesSatisfy_pure _ _

private theorem bind_holds (work :Lower n KemSK Auxiliary A) (next :A → Lower n KemSK Auxiliary B)
    (first :Holds work) (later :∀value,Holds (next value)) :Holds (work >>=next) :=by
  constructor
  · intro before result reached
    simp only [StateT.run_bind,mem_support_bind_iff] at reached
    obtain ⟨middle,called,continued⟩:=reached
    exact ((later middle.1).1 middle.2 result continued).trans (first.1 before middle called)
  · intro before
    rw [StateT.run_bind]
    exact allQueriesSatisfy_bind (first.2 before) (fun result=>(later result.1).2 result.2)

private theorem map_holds (observe :A → B) (work :Lower n KemSK Auxiliary A) (first :Holds work) :Holds (observe <$>work) :=by
  simpa only [map_eq_pure_bind] using bind_holds work (fun value=>pure (observe value)) first (fun _=>pure_holds _)

private theorem simulate_holds (handler :QueryImpl spec (Lower n KemSK Auxiliary))
    (leaves :∀query,Holds (handler query)) (work :OracleComp spec A) :Holds (simulateQ handler work) :=by
  induction work using OracleComp.inductionOn with
  | pure value=>exact pure_holds value
  | query_bind query next ih=>
    simpa only [simulateQ_bind,simulateQ_spec_query] using bind_holds (handler query) _ (leaves query) ih

private theorem oracle_simulate (handler :QueryImpl spec (OracleComp (Trusted n KemSK)))
    (leaves :∀query,AllQueriesSatisfy (handler query) (Allowed (n:=n) (KemSK:=KemSK)))
    (work :OracleComp spec A) :AllQueriesSatisfy (simulateQ handler work) (Allowed (n:=n) (KemSK:=KemSK)) :=by
  induction work using OracleComp.inductionOn with
  | pure value=>exact allQueriesSatisfy_pure _ _
  | query_bind query next ih=>
    simpa only [simulateQ_bind,simulateQ_spec_query] using allQueriesSatisfy_bind (leaves query) ih

private theorem map_allowed (observe : A → B) (work : OracleComp (Trusted n KemSK) A)
    (held : AllQueriesSatisfy work (Allowed (n:=n) (KemSK:=KemSK))) :
    AllQueriesSatisfy (observe <$>work) (Allowed (n:=n) (KemSK:=KemSK)) :=by
  simpa only [map_eq_pure_bind] using allQueriesSatisfy_bind held (fun value=>allQueriesSatisfy_pure (observe value) Allowed)

private theorem lift_holds (work : OracleComp (Trusted n KemSK) A)
    (held : AllQueriesSatisfy work (Allowed (n:=n) (KemSK:=KemSK))) :
    Holds (StateT.lift work : Lower n KemSK Auxiliary A) :=by
  constructor
  · intro before result reached
    simp only [StateT.run_lift,bind_pure_comp,support_map] at reached
    obtain ⟨reply,_called,same⟩:=reached
    cases same
    rfl
  · intro before
    simpa only [StateT.run_lift,bind_pure_comp] using map_allowed (fun value=>(value,before)) work held

private theorem coins_allowed (work :ProbComp A) :
    AllQueriesSatisfy (RegistrationNativeAgreementJournal.coins (n:=n) (KemSK:=KemSK) work) (Allowed (n:=n) (KemSK:=KemSK)) :=by
  apply oracle_simulate
  intro query
  exact (allQueriesSatisfy_query_iff _ _).mpr trivial

private theorem primitive_allowed (setup :PqxdhServerAuthExperiment.Setup base KemSK) (owner :Owner source)
    (scalar :PqxdhJointGapDh.ScalarBytes) (query :RegistrationAgreementShared.PrimitiveRequest) :
    AllQueriesSatisfy (RegistrationNativeAgreementJournal.primitive (n:=n) setup owner scalar query) (Allowed (n:=n) (KemSK:=KemSK)) :=by
  unfold RegistrationNativeAgreementJournal.primitive
  apply oracle_simulate
  intro lower
  cases lower with
  | inl other=>exact coins_allowed _
  | inr other=>exact (allQueriesSatisfy_query_iff _ _).mpr trivial

private theorem agreement_allowed (setup :PqxdhServerAuthExperiment.Setup base KemSK) (owner :Owner source)
    (scalar :PqxdhJointGapDh.ScalarBytes) (query :RegistrationAgreementExecutor.Request) :
    AllQueriesSatisfy (RegistrationNativeAgreementJournal.core (n:=n) setup owner scalar query) (Allowed (n:=n) (KemSK:=KemSK)) :=by
  cases query <;> first
    | exact primitive_allowed setup owner scalar _
    | exact allQueriesSatisfy_pure _ _

private theorem record_allowed (setup :PqxdhServerAuthExperiment.Setup base KemSK) (wire :RegistrationNativeWire.Wire)
    (query :RegistrationRecordPrimitives.Request) :
    AllQueriesSatisfy (RegistrationNativeRecordJournal.core (n:=n) (KemSK:=KemSK) setup wire query) (Allowed (n:=n) (KemSK:=KemSK)) :=by
  cases query with
  | hash request=>
    exact allQueriesSatisfy_bind ((allQueriesSatisfy_query_iff _ _).mpr trivial) (fun _=>allQueriesSatisfy_pure _ _)
  | _=>exact coins_allowed _

theorem agreement (setup :PqxdhServerAuthExperiment.Setup base KemSK) (owner :Owner source)
    (scalar :PqxdhJointGapDh.ScalarBytes) (query :RegistrationAgreementExecutor.Request) :
    Holds (RegistrationNativeBeaconPhaseCommutation.agreement (n:=n) (Auxiliary:=Auxiliary) setup owner scalar query) :=by
  constructor
  · intro before result reached
    simp only [RegistrationNativeBeaconPhaseCommutation.agreement,StateT.run,support_map] at reached
    obtain ⟨reply,_called,same⟩:=reached
    cases same
    rfl
  · intro before
    unfold RegistrationNativeBeaconPhaseCommutation.agreement
    exact map_allowed _ _ (agreement_allowed setup owner scalar query)

theorem record (setup :PqxdhServerAuthExperiment.Setup base KemSK) (wire :RegistrationNativeWire.Wire)
    (query :RegistrationRecordPrimitives.Request) :
    Holds (RegistrationNativeBeaconPhaseCommutation.record (n:=n) (KemSK:=KemSK) (Auxiliary:=Auxiliary) setup wire query) :=by
  constructor
  · intro before result reached
    simp only [RegistrationNativeBeaconPhaseCommutation.record,StateT.run,support_map] at reached
    obtain ⟨reply,_called,same⟩:=reached
    cases same
    rfl
  · intro before
    unfold RegistrationNativeBeaconPhaseCommutation.record
    exact map_allowed _ _ (record_allowed setup wire query)

theorem authentication (setup :PqxdhServerAuthExperiment.Setup base KemSK) (query :RegistrationAuthenticationExecutor.Request) :
    Holds (RegistrationNativeBeaconPhaseCommutation.authentication (n:=n) (KemSK:=KemSK) (Auxiliary:=Auxiliary) (source:=source) setup query) :=by
  cases query with
  | hash request=>
    change Holds ((fun digest=>core.option.Option.Some (RegistrationAuthenticationShared.digestArray digest)) <$>
      (StateT.lift (((Trusted n KemSK).query (.inl (.inr (.hash (BeaconcryptCore.Refinement.RegistrationInputs.hashBytes request))))) : OracleComp (Trusted n KemSK) CtxRomAuth.CtxDigest)))
    exact map_holds _ _ (lift_holds _ ((allQueriesSatisfy_query_iff _ _).mpr trivial))
  | mldsa request | ed25519 request=>exact pure_holds _
private theorem after_agreement (setup : PqxdhServerAuthExperiment.Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (result : RustM agreement.AgreementEffect) :
    Holds (RegistrationNativeFinishFactor.afterAgreement (n:=n) (Auxiliary:=Auxiliary) setup wire result) :=by
  cases result with
  | fail error | div=>exact pure_holds _
  | ok effect=>cases effect with
    | BeaconComplete agreed=>
      exact map_holds _ _ (simulate_holds _ (record setup wire) _)
    | _=>exact pure_holds _

private theorem accepted (setup : PqxdhServerAuthExperiment.Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (owner : Owner source) (scalar : PqxdhJointGapDh.ScalarBytes) (authenticated : registration.AuthenticatedResponse) :
    Holds (RegistrationNativeFinishFactor.accepted (n:=n) (Auxiliary:=Auxiliary) setup wire owner scalar authenticated) :=by
  unfold RegistrationNativeFinishFactor.accepted
  exact bind_holds _ _ (simulate_holds _ (agreement setup owner scalar) _) (after_agreement setup wire)

private theorem after_authentication (setup : PqxdhServerAuthExperiment.Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (owner : Owner source) (scalar : PqxdhJointGapDh.ScalarBytes) (result : RustM RegistrationResponseExecutor.ResponseResult) :
    Holds (RegistrationNativeFinishFactor.afterAuthentication (n:=n) (Auxiliary:=Auxiliary) setup wire owner scalar result) :=by
  cases result with
  | fail error | div=>exact pure_holds _
  | ok optional=>cases optional with
    | Err control=>exact pure_holds _
    | Ok authenticated=>exact accepted setup wire owner scalar authenticated

theorem body (setup : PqxdhServerAuthExperiment.Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (pending : registration.BeaconPending) (packet : core.option.Option registration.ResponsePacket)
    (owner : Owner source) (scalar : PqxdhJointGapDh.ScalarBytes) :
    Holds (RegistrationNativeFinishFactor.body (n:=n) (Auxiliary:=Auxiliary) setup wire pending packet owner scalar) :=by
  unfold RegistrationNativeFinishFactor.body
  exact bind_holds _ _ (simulate_holds _ (authentication setup) _) (after_authentication setup wire owner scalar)

end BeaconcryptCore.Computational.RegistrationNativePlatformSdkFinishAuxiliaryCore

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSdkFinishAuxiliaryCore.agreement' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSdkFinishAuxiliaryCore.agreement

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSdkFinishAuxiliaryCore.record' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSdkFinishAuxiliaryCore.record

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSdkFinishAuxiliaryCore.authentication' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSdkFinishAuxiliaryCore.authentication

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSdkFinishAuxiliaryCore.body' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSdkFinishAuxiliaryCore.body
