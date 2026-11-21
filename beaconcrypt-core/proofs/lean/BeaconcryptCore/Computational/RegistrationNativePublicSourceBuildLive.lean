-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePublicSourceExecution
import BeaconcryptCore.Computational.RegistrationServerMaterialSessions

/-! Actual build execution consumes only its one-use capability and preserves every other live root receipt. This invariant is derived from the concrete compiler's support and native session behavior, including cancellation and all post-take failures. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePublicSourceBuildLive
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativePublicSourceServer (State)
open RegistrationNativePublicSourceState (Live MemoCorrect)
open RegistrationNativePublicSourceExecution (execute)
variable {n : Nat} {ι KemSK : Type} {base : OracleSpec ι} {source : RegistrationNativeMldsa.Source}

private theorem build_support (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (checks : Checks) (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (handle : Nat) (application : Option (Slice U8)) (before : RegistrationNativePublicFrontend.State source)
    (output : RegistrationServerMaterialFrontend.Result × RegistrationNativePublicFrontend.State source)
    (supported : output ∈ support ((RegistrationNativePublicFrontend.serverOpen false
      (RegistrationServerOpenReferenceCompiler.build (n := n) (KemSK := KemSK) setup.source wire checks sign handle application)).run before)) :
    (output.1, output.2.server) ∈ support
      ((RegistrationServerMaterialFrontend.build (n := n) wire checks.reservePeer handle application).run before.server) := by
  simp only [RegistrationNativePublicFrontend.serverOpen, StateT.run, support_map] at supported
  obtain ⟨inner, possible, equal⟩ := supported
  have interpreted := RegistrationNativePublicSourceSupport.simulate_support (RegistrationNativePublicFrontend.liftLocal false)
    (((RegistrationServerOpenReferenceCompiler.build setup.source wire checks sign handle application).run before.server).run before.environment)
    inner possible
  change inner ∈ support ((simulateQ (RegistrationNativeCommonCompiler.service RegistrationBeaconReferenceCompiler.effect
    RegistrationServerOpenReferenceCompiler.demand setup.source wire.frameWrite sign)
    ((RegistrationServerMaterialFrontend.build wire checks.reservePeer handle application).run before.server)).run before.environment) at interpreted
  have raw := support_simulateQ_run'_subset
    (RegistrationNativeCommonCompiler.service RegistrationBeaconReferenceCompiler.effect
      RegistrationServerOpenReferenceCompiler.demand setup.source wire.frameWrite sign)
    ((RegistrationServerMaterialFrontend.build wire checks.reservePeer handle application).run before.server) before.environment
    (by rw [StateT.run'_eq, support_map]; exact ⟨inner, interpreted, rfl⟩)
  have same : inner.1 = (output.1, output.2.server) := congrArg (fun result => (result.1, result.2.server)) equal
  rw [← same]
  exact raw

/-- All actual build outcomes retain the internal live-root invariant after the original one-use take. -/
theorem build_live (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (checks : Checks) (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (handle : Nat) (application : Option (Slice U8))
    (before : State n KemSK source) (result : RegistrationServerMaterialFrontend.Result × State n KemSK source)
    (live : Live before.1 before.2) (correct : MemoCorrect setup seed scalar before.2.roots)
    (supported : result ∈ support ((execute setup wire route sign seed scalar
      (RegistrationNativePublicFrontend.serverOpen false
        (RegistrationServerOpenReferenceCompiler.build setup.source wire checks sign handle application))).run before)) :
    Live result.2.1 result.2.2 ∧ MemoCorrect setup seed scalar result.2.2.roots := by
  have stable := RegistrationNativePublicSourceExecution.roots setup wire route sign seed scalar _ before result correct supported
  have observed := RegistrationNativePublicSourceExecution.observed_support setup wire route sign seed scalar _ before result supported
  have raw := build_support setup wire checks sign handle application before.1 (result.1, result.2.1) observed
  have sessions := RegistrationServerMaterialSessions.build_sessions wire checks.reservePeer handle application
    before.1.server (result.1, result.2.1.server) raw
  have remaining := (RegistrationServerMaterialRoots.take_live handle before.1.server before.2.roots live).1
  refine ⟨?_, stable.1⟩
  intro ready member
  rw [sessions] at member
  obtain ⟨root, stored⟩ := remaining ready member
  exact ⟨root, stable.2 ready.reference root stored⟩

end BeaconcryptCore.Computational.RegistrationNativePublicSourceBuildLive
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePublicSourceBuildLive.build_live' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePublicSourceBuildLive.build_live
