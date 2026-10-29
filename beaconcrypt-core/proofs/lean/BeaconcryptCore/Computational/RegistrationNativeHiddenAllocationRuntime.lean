-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeHiddenAllocationService
import BeaconcryptCore.Computational.RegistrationNativeHiddenAllocationWorld
import BeaconcryptCore.Computational.RegistrationNativeHiddenBeaconAllocationCaps

/-! Native Beacon callbacks execute in the actual thin-service, cursor, Protocol control and private-service state. Non-append callbacks retain physical owner count; the literal append keeps local service state and returns the actual allocator's old length. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeHiddenAllocationRuntime
open PqxdhServerAuthExperiment (Setup Codec)
open RegistrationNativeHiddenInterpreter (Provider)
open RegistrationNativeHiddenAllocationCore (Allowed WorldAllowed mapped simulation)
variable {n : Nat} {ι KemSK ProviderState Reader Response Secret Value : Type} {base : OracleSpec ι}

abbrev State (n : Nat) (KemSK ProviderState Secret : Type) := RegistrationNativeHiddenEnvironmentWorld.State n
  (RegistrationNativeHiddenInterpreter.State n KemSK ProviderState) Secret

def lift : QueryImpl (RegistrationNativeBeaconFrontend.Trusted n KemSK)
    (OracleComp (RegistrationNativePublicFrontend.Spec n KemSK)) :=
  RegistrationNativePublicFrontend.liftLocal false ∘ₛ RegistrationBeaconReferenceCompiler.trustedLift

noncomputable def callback (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (provider : Provider KemSK ProviderState)
    (service : QueryImpl (PqxdhRecordLiftProtocol.ServiceSpec n) (StateT Secret ProbComp))
    (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder) :
    QueryImpl (RegistrationNativeBeaconFrontend.Trusted n KemSK) (StateT (State n KemSK ProviderState Secret) ProbComp) :=
  fun query => RegistrationNativeHiddenEnvironmentWorld.lower service codec route
    (simulateQ (RegistrationNativeHiddenInterpreter.handler setup wire sign seed scalar provider) (lift query))

private theorem lift_safe (query : (RegistrationNativeBeaconFrontend.Trusted n KemSK).Domain)
    (safe : RegistrationNativeHiddenBeaconAllocationCaps.Allowed query) : AllQueriesSatisfy (lift query) Allowed := by
  cases query with
  | inl query =>
      simp only [lift, QueryImpl.apply_compose, RegistrationBeaconReferenceCompiler.trustedLift,
        RegistrationBeaconReferenceCompiler.effect, simulateQ_spec_query, RegistrationNativePublicFrontend.liftLocal]
      exact (allQueriesSatisfy_query_iff _ _).mpr safe
  | inr query =>
      simp only [lift, QueryImpl.apply_compose, RegistrationBeaconReferenceCompiler.trustedLift,
        RegistrationBeaconReferenceCompiler.indexed, simulateQ_spec_query, RegistrationNativePublicFrontend.liftLocal]
      rcases query with query | (query | query)
      all_goals simp only [RegistrationNativeKemRouting.route, Bool.false_eq_true, ite_false, simulateQ_spec_query, RegistrationNativePublicFrontend.liftRoutedKem]
      all_goals exact (allQueriesSatisfy_query_iff _ _).mpr trivial

/-- Every non-append actual native callback preserves physical allocation under the same arbitrary KEM provider and private service. -/
theorem query_noappend (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (provider : Provider KemSK ProviderState)
    (service : QueryImpl (PqxdhRecordLiftProtocol.ServiceSpec n) (StateT Secret ProbComp))
    (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (query : (RegistrationNativeBeaconFrontend.Trusted n KemSK).Domain)
    (before : State n KemSK ProviderState Secret)
    (result : (RegistrationNativeBeaconFrontend.Trusted n KemSK).Range query × State n KemSK ProviderState Secret)
    (safe : RegistrationNativeHiddenBeaconAllocationCaps.Allowed query)
    (supported : result ∈ support ((callback setup wire sign seed scalar provider service codec route query).run before)) :
    result.2.1.2.owners.length = before.1.2.owners.length := by
  exact RegistrationNativeHiddenAllocationWorld.noappend service codec route _ before result
    (RegistrationNativeHiddenAllocationService.program setup wire sign seed scalar provider _ before.1.1.1 (lift_safe query safe)) supported

/-- The actual native append reaches the literal Protocol allocator; no wrapper chooses its reply or mutates a local service coordinate. -/
theorem query_append (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (provider : Provider KemSK ProviderState)
    (service : QueryImpl (PqxdhRecordLiftProtocol.ServiceSpec n) (StateT Secret ProbComp))
    (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (sender : U64) (identity : RawCtxServerRouting.Identity) (phase : PqxdhRecordLiftInterface.InactivePhase)
    (before : State n KemSK ProviderState Secret) (result : Nat × State n KemSK ProviderState Secret)
    (supported : result ∈ support ((callback setup wire sign seed scalar provider service codec route
      (.inl (.inr (.appendOwner sender identity phase)))).run before)) :
    result.1 = before.1.2.owners.length ∧ result.2.1.2.owners.length = before.1.2.owners.length + 1 := by
  have same : callback setup wire sign seed scalar provider service codec route
      (.inl (.inr (.appendOwner sender identity phase))) =
      RegistrationNativeHiddenEnvironmentWorld.lower service codec route
        (StateT.lift (PqxdhRecordLiftInterface.effectLift (.inr (.appendOwner sender identity phase)))) := by
    simp only [callback, lift, QueryImpl.apply_compose, RegistrationBeaconReferenceCompiler.trustedLift,
      RegistrationBeaconReferenceCompiler.effect, simulateQ_spec_query, RegistrationNativePublicFrontend.liftLocal,
      RegistrationNativeHiddenInterpreter.handler, RegistrationNativeHiddenInterpreter.effect]
  rw [same] at supported
  exact (RegistrationNativeHiddenAllocationWorld.append_facts service codec route sender identity phase before result supported).imp_right And.left

/-- Allocation-free actual native programs preserve the physical roster through every callback and reply. -/
theorem program_noappend (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (provider : Provider KemSK ProviderState)
    (service : QueryImpl (PqxdhRecordLiftProtocol.ServiceSpec n) (StateT Secret ProbComp))
    (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (work : OracleComp (RegistrationNativeBeaconFrontend.Trusted n KemSK) Value)
    (before : State n KemSK ProviderState Secret) (result : Value × State n KemSK ProviderState Secret)
    (safe : AllQueriesSatisfy work (RegistrationNativeHiddenBeaconAllocationCaps.Allowed (KemSK := KemSK)))
    (supported : result ∈ support ((simulateQ (callback setup wire sign seed scalar provider service codec route) work).run before)) :
    result.2.1.2.owners.length = before.1.2.owners.length := by
  induction work using OracleComp.inductionOn generalizing before with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at supported
      cases supported
      rfl
  | query_bind query next ih =>
      obtain ⟨first, later⟩ := (allQueriesSatisfy_query_bind_iff _ _ _).mp safe
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at supported
      obtain ⟨middle, reached, continued⟩ := supported
      exact (ih middle.1 middle.2 (later middle.1) continued).trans
        (query_noappend setup wire sign seed scalar provider service codec route query before middle first reached)

/-- The actual native-to-public query compiler preserves the non-append footprint. -/
theorem lift_query (query : (RegistrationNativeBeaconFrontend.Trusted n KemSK).Domain)
    (safe : RegistrationNativeHiddenBeaconAllocationCaps.Allowed query) : AllQueriesSatisfy (lift query) Allowed :=
  lift_safe query safe

end BeaconcryptCore.Computational.RegistrationNativeHiddenAllocationRuntime
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeHiddenAllocationRuntime.query_noappend' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeHiddenAllocationRuntime.query_noappend
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeHiddenAllocationRuntime.query_append' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeHiddenAllocationRuntime.query_append
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeHiddenAllocationRuntime.program_noappend' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeHiddenAllocationRuntime.program_noappend

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeHiddenAllocationRuntime.lift_query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeHiddenAllocationRuntime.lift_query
