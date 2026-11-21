-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicSourceExecution
import BeaconcryptCore.Computational.RegistrationNativePublicRetained

/-! The actual shared-platform query tree relocates its retained roots into the private prepare/material service, preserving external uniform positions and all platform continuations. This compiler receives full material rather than roots; opaque material44/slot interpretation remains a separate step. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicRetained
open PqxdhServerAuthExperiment (Setup)
open PqxdhSecretInputKdf (HmacSha512 HmacOracle)
open RegistrationNativePublicInterpreter (State)
open RegistrationNativePublicRetained (clear project)
open RegistrationNativeRetainedService (Spec)
variable {n : Nat} {ι KemSK Value : Type} {base : OracleSpec ι}

noncomputable def compiler (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply) :
    QueryImpl (RegistrationNativePlatformPublicFrontend.Spec n KemSK) (StateT (State n KemSK) (OracleComp Spec))
  | .inl query => RegistrationNativePublicRetained.compiler setup wire route sign query
  | .inr coin => StateT.lift (Spec.query (.inl coin))

noncomputable def source (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes) :=
  ((RegistrationNativeRootCacheProjection.implementation setup.source setup.hmac setup.joint setup.dh seed scalar).mapStateTBase
    (RegistrationNativePlatformPublicSourceExecution.handler (n := n) setup wire route sign)).flattenStateT

noncomputable def retained (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes) :=
  ((RegistrationNativeRetainedSource.implementation setup.source setup.hmac
    (RegistrationNativeRelatedFamily.input setup.joint setup.dh seed scalar)
    (RegistrationNativeKeyFamilyPreparation.inside (setup.joint.staticDh seed (setup.dh.publicKey scalar)))).mapStateTBase
      (compiler (n := n) setup wire route sign)).flattenStateT

/-- The entire actual mixed dispatch retains every reply and semantic state under the explicit private root-service projection. -/
theorem query_project (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (query : (RegistrationNativePlatformPublicFrontend.Spec n KemSK).Domain)
    (before : State n KemSK × HmacOracle.QueryCache) :
    Prod.map id project <$> (source setup wire route sign seed scalar query).run before =
      (retained setup wire route sign seed scalar query).run (project before) := by
  cases query with
  | inl query =>
      exact RegistrationNativePublicRetained.query_project setup wire route sign seed scalar query before
  | inr coin => rfl

/-- Arbitrary adaptive mixed-role programs preserve their complete result and semantic state after relocating only private root bookkeeping. -/
theorem program_project (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (work : OracleComp (RegistrationNativePlatformPublicFrontend.Spec n KemSK) Value)
    (before : State n KemSK × HmacOracle.QueryCache) :
    Prod.map id project <$> (simulateQ (source setup wire route sign seed scalar) work).run before =
      (simulateQ (retained setup wire route sign seed scalar) work).run (project before) :=
  OracleComp.map_run_simulateQ_eq_of_query_map_eq _ _ project
    (query_project setup wire route sign seed scalar) work before

noncomputable def client (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (work : OracleComp (RegistrationNativePlatformPublicFrontend.Spec n KemSK) Value)
    (before : State n KemSK) : OracleComp Spec Value :=
  (simulateQ (compiler setup wire route sign) work).run' (clear before)

/-- The complete concrete mixed frontend is an executable retained-service client; no source execution equality is assumed. -/
theorem client_source (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (work : OracleComp (RegistrationNativePlatformPublicFrontend.Spec n KemSK) Value)
    (before : State n KemSK) (cache : HmacOracle.QueryCache) :
    (simulateQ (RegistrationNativeRootCacheProjection.implementation setup.source setup.hmac setup.joint setup.dh seed scalar)
      ((simulateQ (RegistrationNativePlatformPublicSourceExecution.handler setup wire route sign) work).run' before)).run' cache =
      (simulateQ (RegistrationNativeRetainedSource.implementation setup.source setup.hmac
        (RegistrationNativeRelatedFamily.input setup.joint setup.dh seed scalar)
        (RegistrationNativeKeyFamilyPreparation.inside (setup.joint.staticDh seed (setup.dh.publicKey scalar))))
        (client setup wire route sign work before)).run' (before.roots, cache) := by
  have projected := congrArg (fun game => Prod.fst <$> game)
    (program_project setup wire route sign seed scalar work (before, cache))
  simp only [source, retained, project, StateT.run'_eq, simulateQ_map, StateT.run_map,
    Functor.map_map, Prod.map, id_eq, client] at projected ⊢
  rw [simulateQ_mapStateTBase_run_eq_map_flattenStateT,
    simulateQ_mapStateTBase_run_eq_map_flattenStateT]
  simpa only [Functor.map_map, Prod.map, id_eq] using projected

end BeaconcryptCore.Computational.RegistrationNativePlatformPublicRetained

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicRetained.query_project' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicRetained.query_project

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicRetained.program_project' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicRetained.program_project

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicRetained.client_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicRetained.client_source
