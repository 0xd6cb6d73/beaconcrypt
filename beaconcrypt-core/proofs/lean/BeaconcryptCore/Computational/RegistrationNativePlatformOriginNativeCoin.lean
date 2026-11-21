-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformOriginNativeTails
import BeaconcryptCore.Computational.RegistrationNativePlatformOriginErasedFields
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformOriginNativeCoin
open PqxdhRecordLiftProtocol (ServiceSpec Control)
open PqxdhRecordLiftInterface (Environment)
open PqxdhServerAuthExperiment (Setup Codec)
variable {n : Nat} {I KemSK Platform Failure Reader Response : Type} {base : OracleSpec I}

/-- The actual native experiment coin retains platform, shell and control and compiles to the literal charged independent source coin. -/
theorem source (env : Environment n Platform)
    (reserve : Nat → StateT Platform ProbComp (core.result.Result Unit Failure))
    (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder) (amount : Nat)
    (beforeP : Platform) (shell : CborRecordWorldClient.Shell) (control : Control n) :
    RegistrationNativePlatformOriginNativeTails.source env reserve codec route
      (PqxdhDeploymentInterface.Spec.query (.inl amount)) beforeP shell control =
      (fun reply=>(((reply,beforeP),shell),control)) <$>
        RegistrationNativePlatformOriginGateSource.coins amount := by
  simp only [RegistrationNativePlatformOriginNativeTails.source,simulateQ_spec_query,
    RegistrationNativePlatformGatedRecordInterface.native,StateT.run_bind,PqxdhRecordLiftInterface.native,
    RegistrationNativePlatformGatedRecordInterface.post,StateT.run_pure,StateT.run_lift,bind_pure_comp,simulateQ_map,StateT.run_map,Functor.map_map]
  have closed:=RegistrationNativePlatformOriginGateSource.closed_program
    (unifSpec.query amount :ProbComp _) codec route shell control
  have mapped:=congrArg (Functor.map (fun result=>(((result.1.1,beforeP),result.1.2),result.2))) closed
  simp only [simulateQ_spec_query,Functor.map_map] at mapped
  convert mapped using 1 <;>rfl

/-- The same experiment coin emits only ordinary base operations and cannot touch a hidden CTX key history. -/
theorem base_syntax (amount : Nat) :
    (RegistrationNativePlatformOriginGateSource.coins (n:=n) amount).AllQueriesSatisfy
      RegistrationNativePlatformOriginErasedFields.BaseOnly := by
  rw [RegistrationNativePlatformOriginGateSource.coins,allQueriesSatisfy_query_bind_iff]
  exact ⟨trivial,fun _=>by rw [allQueriesSatisfy_query_iff];trivial⟩
end BeaconcryptCore.Computational.RegistrationNativePlatformOriginNativeCoin

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOriginNativeCoin.source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOriginNativeCoin.source


/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOriginNativeCoin.base_syntax' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOriginNativeCoin.base_syntax
