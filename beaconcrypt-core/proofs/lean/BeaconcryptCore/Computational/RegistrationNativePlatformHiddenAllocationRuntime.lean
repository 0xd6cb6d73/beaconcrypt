-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformHiddenAllocationBackend
import BeaconcryptCore.Computational.RegistrationNativePlatformHiddenAllocationBirth
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformHiddenAllocationRuntime
open PqxdhServerAuthExperiment (Setup Codec)
open RegistrationNativeHiddenInterpreter (Provider)
open RegistrationNativeHiddenEnvironmentWorld (lower)
open RegistrationNativeHiddenAllocationCore (WorldAllowed mapped simulation)
open RegistrationNativeHiddenBeaconAllocationCaps (Allowed)
variable {n : Nat} {I KemSK ProviderState Platform Reader Response Secret A : Type} {base : OracleSpec I}
abbrev State (n : Nat) (KemSK ProviderState Secret : Type) :=
  RegistrationNativeHiddenEnvironmentWorld.State n
    (RegistrationNativeSelectiveHiddenInterpreter.State n KemSK ProviderState) Secret

private theorem trusted_public (query : (RegistrationNativeBeaconFrontend.Trusted n KemSK).Domain) (previous : Platform) :
    simulateQ RegistrationNativePlatformPublicFrontend.embedLocal
      ((RegistrationNativePlatformPublicFrontend.trusted query).run previous) =
    (fun value => (value, previous)) <$>
      simulateQ RegistrationNativePlatformPublicFrontend.old (RegistrationNativeHiddenAllocationRuntime.lift query) := by
  simp only [RegistrationNativePlatformPublicFrontend.trusted, StateT.run_lift, bind_pure_comp, simulateQ_map,
    ← QueryImpl.simulateQ_compose, RegistrationNativeHiddenAllocationRuntime.lift]
  congr 1
  rw [QueryImpl.apply_compose, ← QueryImpl.simulateQ_compose]
  congr 1
  funext request
  rcases request with message | common | kem
  · rfl
  · rfl
  · simp only [QueryImpl.compose, RegistrationNativePlatformPublicFrontend.localQuery,
      RegistrationNativePublicFrontend.liftLocal, ← QueryImpl.simulateQ_compose]
    congr 1

/-- Actual trusted native programs retain the same persistent platform state under their literal public request compiler. -/
theorem native_program (work : OracleComp (RegistrationNativeBeaconFrontend.Trusted n KemSK) A) (previous : Platform) :
    simulateQ RegistrationNativePlatformPublicFrontend.embedLocal
      ((simulateQ RegistrationNativePlatformPublicFrontend.trusted work).run previous) =
    (fun value => (value, previous)) <$>
      simulateQ (RegistrationNativePlatformPublicFrontend.old ∘ₛ RegistrationNativeHiddenAllocationRuntime.lift) work := by
  induction work using OracleComp.inductionOn generalizing previous with
  | pure value => rfl
  | query_bind query next ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, simulateQ_bind, map_bind]
    rw [trusted_public]
    simp only [bind_map_left, QueryImpl.apply_compose]
    apply bind_congr
    intro reply
    exact ih reply previous

variable (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret) (provider : Provider KemSK ProviderState)
    (service : QueryImpl (PqxdhRecordLiftProtocol.ServiceSpec n) (StateT Secret ProbComp))
    (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
local notation "backend" => RegistrationNativePlatformSelectiveEntropyBackend.handler setup wire sign seed scalar candidate provider

noncomputable def closed (query : (RegistrationNativeBeaconFrontend.Trusted n KemSK).Domain) :
    StateT (RegistrationNativeSelectiveHiddenInterpreter.State n KemSK ProviderState)
      (OracleComp (PqxdhRecordLiftInterface.WorldSpec n)) ((RegistrationNativeBeaconFrontend.Trusted n KemSK).Range query) :=
  simulateQ backend ((RegistrationNativePlatformPublicFrontend.old ∘ₛ RegistrationNativeHiddenAllocationRuntime.lift) query)

/-- The genuine native program closes through the exact new selective backend while its common platform state is retained literally. -/
theorem native_world (work : OracleComp (RegistrationNativeBeaconFrontend.Trusted n KemSK) A)
    (previous : Platform) (before : RegistrationNativeSelectiveHiddenInterpreter.State n KemSK ProviderState) :
    (simulateQ backend (simulateQ RegistrationNativePlatformPublicFrontend.embedLocal
      ((simulateQ RegistrationNativePlatformPublicFrontend.trusted work).run previous))).run before =
    (fun result => ((result.1, previous), result.2)) <$>
      (simulateQ (closed setup wire sign seed scalar candidate provider) work).run before := by
  rw [native_program, simulateQ_map, StateT.run_map]
  rw [← QueryImpl.simulateQ_compose]
  rfl

noncomputable def callback : QueryImpl (RegistrationNativeBeaconFrontend.Trusted n KemSK)
    (StateT (State n KemSK ProviderState Secret) ProbComp) := fun query =>
  lower service codec route (closed setup wire sign seed scalar candidate provider query)

/-- Every actual native trusted leaf except physical append retains the Protocol owner count through its same platform/private state. -/
theorem query_noappend (query : (RegistrationNativeBeaconFrontend.Trusted n KemSK).Domain)
    (before : State n KemSK ProviderState Secret)
    (result : (RegistrationNativeBeaconFrontend.Trusted n KemSK).Range query × State n KemSK ProviderState Secret)
    (safe : Allowed query)
    (supported : result ∈ support ((callback setup wire sign seed scalar candidate provider service codec route query).run before)) :
    result.2.1.2.owners.length = before.1.2.owners.length := by
  apply RegistrationNativeHiddenAllocationWorld.noappend service codec route _ before result _ supported
  apply RegistrationNativePlatformHiddenAllocationBackend.program setup wire sign seed scalar candidate provider
  apply simulation RegistrationNativePlatformPublicFrontend.old RegistrationNativeHiddenAllocationCore.Allowed
    RegistrationNativePlatformHiddenAllocationBackend.Allowed
  · intro request permitted
    exact (allQueriesSatisfy_query_iff _ _).mpr permitted
  · exact RegistrationNativeHiddenAllocationRuntime.lift_query query safe

/-- The literal new trusted append reaches the same physical allocator and keeps both persistent P and private cache intact. -/
theorem query_append (sender : U64) (identity : RawCtxServerRouting.Identity)
    (phase : PqxdhRecordLiftInterface.InactivePhase)
    (before : State n KemSK ProviderState Secret) (result : Nat × State n KemSK ProviderState Secret)
    (supported : result ∈ support ((callback setup wire sign seed scalar candidate provider service codec route
      (.inl (.inr (.appendOwner sender identity phase)))).run before)) :
    result.1 = before.1.2.owners.length ∧ result.2.1.2.owners.length = before.1.2.owners.length + 1 := by
  have same : closed (n := n) setup wire sign seed scalar candidate provider
      (.inl (.inr (.appendOwner sender identity phase))) =
      StateT.lift (PqxdhRecordLiftInterface.effectLift (n := n) (.inr (.appendOwner sender identity phase))) := by
    rfl
  unfold callback at supported
  rw [same] at supported
  exact (RegistrationNativeHiddenAllocationWorld.append_facts service codec route sender identity phase before result supported).imp_right And.left

end BeaconcryptCore.Computational.RegistrationNativePlatformHiddenAllocationRuntime

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformHiddenAllocationRuntime.native_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformHiddenAllocationRuntime.native_program

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformHiddenAllocationRuntime.native_world' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformHiddenAllocationRuntime.native_world

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformHiddenAllocationRuntime.query_noappend' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformHiddenAllocationRuntime.query_noappend

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformHiddenAllocationRuntime.query_append' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformHiddenAllocationRuntime.query_append
