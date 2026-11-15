-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterFinishSampleStageCut
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAgreementGivenCut
import BeaconcryptCore.Computational.RegistrationNativePlatformHashReceipt
/-! The specified source agreement/record cut projects to that same native primitive path. Only the external platform interpretation is forgotten; the actual initializer, complete native state and exact source request journals are preserved. No independently chosen compatible path is introduced. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAgreementCutSource
open BeaconcryptCore.Refinement
open RegistrationNativeBeaconFrontend (Owner)
open RegistrationWorldAgreementCompiler (EnvState)
open RegistrationNativeMldsaShared (Local)
variable {n :Nat} {I KemSK P A :Type} {base :OracleSpec I} {source :RegistrationNativeMldsa.Source}
local notation "Native"=>RegistrationNativeExperiment.State n KemSK source
local notation "Env"=>EnvState RegistrationServerRoleBackend.State
local notation "Lower"=>RegistrationNativeBeaconPhaseCommutation.Lower n KemSK RegistrationServerRoleBackend.State
variable (coins :QueryImpl unifSpec (StateT P ProbComp))
variable (setup :PqxdhServerAuthExperiment.Setup base KemSK) (checks :PqxdhServerAuthExperiment.Checks)
variable (representation :RegistrationServerRoleBackend.ConvertedIdentity setup) (created :PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))

theorem lower (work :Lower A) (owners :List (Owner source)) (env :Env) (before :Native) (previous :P)
    (value :A) (nextEnv :Env) (after :Native) (next :P)
    (supported :((value,nextEnv),(after,next))∈support
      (RegistrationNativePlatformPublicAdapterFinishStageCut.run
        (RegistrationNativePlatformPublicAdapterFinishSampleStageCut.implementation coins setup checks representation created)
        work env (before,previous))) :
    (value,(owners,(nextEnv,after)))∈support
      ((RegistrationNativeMldsaShared.lower setup checks representation created
        (RegistrationNativeBeaconPhaseCommutation.lift work)).run (owners,(env,before))) :=by
  unfold RegistrationNativePlatformPublicAdapterFinishStageCut.run at supported
  rw [RegistrationNativePlatformPublicAdapterFinishSampleStageCut.free_source,support_map] at supported
  obtain ⟨inner,called,same⟩:=supported
  have native:=RegistrationNativePlatformHashReceipt.native_support coins _ inner.1 previous inner.2 called
  have equal :inner.1=((value,nextEnv),after):=by
    have first:=congrArg (fun result=>(result.1,result.2.1)) same
    exact first
  rw [equal] at native
  change (value,(owners,(nextEnv,after)))∈support
    ((fun result :((A×List (Owner source))×Env)×Native =>
      (result.1.1.1,(result.1.1.2,(result.1.2,result.2)))) <$>
      (simulateQ (RegistrationNativeExperiment.trusted setup checks representation created source)
        (((RegistrationNativeBeaconPhaseCommutation.lift work).run owners).run env)).run before)
  rw [RegistrationNativeBeaconPhaseCommutation.lift_run,simulateQ_map,StateT.run_map]
  simp only [Functor.map_map,support_map]
  exact ⟨((value,nextEnv),after),native,rfl⟩

theorem agreement (owner :Owner source) (scalar :PqxdhJointGapDh.ScalarBytes)
    (work :OracleComp RegistrationAgreementExecutor.Spec A) (owners :List (Owner source)) (env :Env)
    (before :Native) (previous :P) (value :A) (nextEnv :Env) (after :Native) (next :P)
    (supported :((value,nextEnv),(after,next))∈support
      (RegistrationNativePlatformPublicAdapterFinishStageCut.run
        (RegistrationNativePlatformPublicAdapterFinishSampleStageCut.implementation coins setup checks representation created)
        (simulateQ (RegistrationNativeBeaconPhaseCommutation.agreement setup owner scalar) work) env (before,previous))) :
    (value,(owners,(nextEnv,after)))∈support
      ((RegistrationNativeMldsaShared.lower setup checks representation created
        (simulateQ (RegistrationNativeBeaconFrontend.agreement setup owner scalar) work)).run (owners,(env,before))) :=by
  have same :simulateQ (RegistrationNativeBeaconFrontend.agreement (n:=n) (Auxiliary:=RegistrationServerRoleBackend.State) setup owner scalar) work=
      RegistrationNativeBeaconPhaseCommutation.lift (simulateQ (RegistrationNativeBeaconPhaseCommutation.agreement setup owner scalar) work) :=by
    rw [←RegistrationNativeBeaconPhaseCommutation.simulate_lift]
    apply congrArg (fun handler=>simulateQ handler work)
    funext query
    exact RegistrationNativeBeaconPhaseCommutation.agreement_lift setup owner scalar query
  rw [same]
  exact lower coins setup checks representation created _ owners env before previous value nextEnv after next supported

theorem record (wire :RegistrationNativeWire.Wire)
    (work :OracleComp RegistrationRecordPrimitives.Spec A) (owners :List (Owner source)) (env :Env)
    (before :Native) (previous :P) (value :A) (nextEnv :Env) (after :Native) (next :P)
    (supported :((value,nextEnv),(after,next))∈support
      (RegistrationNativePlatformPublicAdapterFinishStageCut.run
        (RegistrationNativePlatformPublicAdapterFinishSampleStageCut.implementation coins setup checks representation created)
        (simulateQ (RegistrationNativeBeaconPhaseCommutation.record setup wire) work) env (before,previous))) :
    (value,(owners,(nextEnv,after)))∈support
      ((RegistrationNativeMldsaShared.lower setup checks representation created
        (simulateQ (RegistrationNativeBeaconFrontend.record setup wire) work)).run (owners,(env,before))) :=by
  have same :simulateQ (RegistrationNativeBeaconFrontend.record (n:=n) (mldsaSource:=source) (Auxiliary:=RegistrationServerRoleBackend.State) setup wire) work=
      RegistrationNativeBeaconPhaseCommutation.lift (simulateQ (RegistrationNativeBeaconPhaseCommutation.record setup wire) work) :=by
    rw [←RegistrationNativeBeaconPhaseCommutation.simulate_lift]
    apply congrArg (fun handler=>simulateQ handler work)
    funext query
    exact RegistrationNativeBeaconPhaseCommutation.record_lift setup wire query
  rw [same]
  exact lower coins setup checks representation created _ owners env before previous value nextEnv after next supported


theorem authentication (work :OracleComp RegistrationAuthenticationExecutor.Spec A)
    (owners :List (Owner source)) (env :Env)
    (before :Native) (previous :P) (value :A) (nextEnv :Env) (after :Native) (next :P)
    (supported :((value,nextEnv),(after,next))∈support
      (RegistrationNativePlatformPublicAdapterFinishStageCut.run
        (RegistrationNativePlatformPublicAdapterFinishSampleStageCut.implementation coins setup checks representation created)
        (simulateQ (RegistrationNativeBeaconPhaseCommutation.authentication (source:=source) setup) work) env (before,previous))) :
    (value,(owners,(nextEnv,after)))∈support
      ((RegistrationNativeMldsaShared.lower setup checks representation created
        (simulateQ (RegistrationNativeBeaconFrontend.authentication setup source) work)).run (owners,(env,before))) :=by
  have same :simulateQ (RegistrationNativeBeaconFrontend.authentication (n:=n) (Auxiliary:=RegistrationServerRoleBackend.State) setup source) work=
      RegistrationNativeBeaconPhaseCommutation.lift (simulateQ (RegistrationNativeBeaconPhaseCommutation.authentication (source:=source) setup) work) :=by
    rw [←RegistrationNativeBeaconPhaseCommutation.simulate_lift]
    apply congrArg (fun handler=>simulateQ handler work)
    funext query
    exact RegistrationNativeBeaconPhaseCommutation.authentication_lift setup query
  rw [same]
  exact lower coins setup checks representation created _ owners env before previous value nextEnv after next supported

theorem authenticated (wire :RegistrationNativeWire.Wire) (pending :registration.BeaconPending) (packet :registration.ResponsePacket)
    (before after :Local n KemSK source) (authenticated :registration.AuthenticatedResponse)
    (supported :(.ok (.Ok authenticated),after)∈support
      ((RegistrationNativeMldsaShared.lower setup checks representation created
        (simulateQ (RegistrationNativeBeaconFrontend.authentication setup source)
          (RegistrationResponseExecutor.begin pending (.Some packet)))).run before)) :
    ∃ adDigest, authenticated=RegistrationResponseExecutor.acceptedResponse pending packet adDigest :=by
  have projected :(.ok (.Ok authenticated),RegistrationNativeMldsaShared.project after)∈support
      ((RegistrationResponseExecutor.execute setup.source.crypto source.verify wire.frameWrite
        (RawCtxSourceHkdf.kdfImpl setup.source) pending (.Some packet)).run (RegistrationNativeMldsaShared.project before)) :=by
    rw [RegistrationResponseExecutor.execute,←RegistrationNativeResponseAuthentication.program setup checks representation created wire,support_map]
    exact ⟨(.ok (.Ok authenticated),after),supported,rfl⟩
  obtain ⟨_digest,same,_verified,_receipts,_earlier,_cached⟩:=RegistrationResponseExecutor.accepted_receipt
    setup.source.crypto source.verify wire.frameWrite (RawCtxSourceHkdf.kdfImpl setup.source) pending packet
      (RegistrationNativeMldsaShared.project before) (RegistrationNativeMldsaShared.project after) authenticated projected
  exact same

end BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAgreementCutSource

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAgreementCutSource.lower' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAgreementCutSource.lower

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAgreementCutSource.agreement' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAgreementCutSource.agreement

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAgreementCutSource.record' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAgreementCutSource.record

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAgreementCutSource.authentication' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAgreementCutSource.authentication

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAgreementCutSource.authenticated' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAgreementCutSource.authenticated
