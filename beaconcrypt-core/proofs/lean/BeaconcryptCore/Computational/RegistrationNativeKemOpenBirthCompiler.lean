-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeKemOpenBirthFrame
import BeaconcryptCore.Computational.RegistrationNativeKemCompilerFootprint
import BeaconcryptCore.Computational.RegistrationNativeKemOpenFrame

/-! Native controller creation footprints transfer to the actual candidate source. Original trusted code and the complete local-owner wrapper retain their exact indexed birth allowances before private KEM interpretation. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeKemOpenBirthCompiler
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeWire (Wire)
open RegistrationNativeKemOpenBirthFrame (IsCreate)
open RegistrationNativeKemOpenBirth (borns)
open RegistrationNativeKemOpenFrame (lower)
open RegistrationNativeKemCompilerFootprint (predicate)
open RegistrationNativeKemBeaconFootprint (Bounded counted)
open RegistrationNativeOptionalFrame (Keeps)
variable {ι KemSK Value : Type} {base : OracleSpec ι} {n : Nat} {mlSource : RegistrationNativeMldsa.Source}

private theorem predicate_eq : predicate (RegistrationNativeKemParsedRouting.Ambient n mlSource) KemSK .create =
    IsCreate (n := n) (mlSource := mlSource) := by
  funext query
  apply propext
  rcases query with other | (pool | key)
  · rfl
  · cases pool <;> simp [predicate, IsCreate]
  · rfl

/-- The actual frontend and chosen-accept route preserve the literal native private creation allowance. -/
theorem lower_bound (chosen : Bool) (work : OracleComp (RegistrationNativeKemServerInterface.Spec n mlSource KemSK) Value)
    (cap : Nat) (bounded : work.IsQueryBoundP (predicate (RegistrationNativeKemServerInterface.Ambient n mlSource) KemSK .create) cap) :
    (simulateQ (lower chosen) work).IsQueryBoundP IsCreate cap := by
  simpa only [lower, QueryImpl.simulateQ_compose, predicate_eq] using
    RegistrationNativeKemCompilerFootprint.route_bound .create chosen _ cap
      (RegistrationNativeKemCompilerFootprint.frontend_lift_bound .create work cap bounded)

private theorem trusted_step (chosen : Bool) (query : (RegistrationNativeBeaconFrontend.Trusted n KemSK).Domain) :
    (simulateQ (lower (mlSource := mlSource) chosen) (RegistrationNativeKemBeaconCompiler.trusted query)).IsQueryBoundP
      IsCreate (if counted (n := n) (KemSK := KemSK) .create query then 1 else 0) := by
  rcases query with world | (other | (pool | key))
  · simp [RegistrationNativeKemBeaconCompiler.trusted, lower, QueryImpl.apply_compose,
      RegistrationNativeKemFrontendInterface.lift, RegistrationNativeKemRouting.route,
      counted, IsCreate, isQueryBoundP_query_iff]
  · simp [RegistrationNativeKemBeaconCompiler.trusted, lower, QueryImpl.apply_compose,
      RegistrationNativeKemServerInterface.lift, RegistrationNativeKemFrontendInterface.lift,
      RegistrationNativeKemRouting.route, counted, IsCreate, isQueryBoundP_query_iff]
  · cases pool <;> simp [RegistrationNativeKemBeaconCompiler.trusted, lower, QueryImpl.apply_compose,
      RegistrationNativeKemServerInterface.lift, RegistrationNativeKemFrontendInterface.lift,
      RegistrationNativeKemRouting.route, counted, IsCreate, isQueryBoundP_query_iff]
  · cases chosen <;> simp [RegistrationNativeKemBeaconCompiler.trusted, lower, QueryImpl.apply_compose,
      RegistrationNativeKemServerInterface.lift, RegistrationNativeKemFrontendInterface.lift,
      RegistrationNativeKemRouting.route, counted, IsCreate, isQueryBoundP_query_iff]

private theorem trusted_bound (chosen : Bool)
    (work : OracleComp (RegistrationNativeBeaconFrontend.Trusted n KemSK) Value) (cap : Nat)
    (bounded : work.IsQueryBoundP (counted (n := n) (KemSK := KemSK) .create) cap) :
    (simulateQ (lower (mlSource := mlSource) chosen) (simulateQ RegistrationNativeKemBeaconCompiler.trusted work)).IsQueryBoundP IsCreate cap := by
  rw [← QueryImpl.simulateQ_compose]
  apply RawCtxSourceOpen.simulate_bound _ _ _ _ cap bounded
  exact trusted_step chosen

variable (setup : Setup base KemSK) (checks : Checks) (wire : Wire)
  (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
  (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (credential : RegistrationNativeMldsa.Credential mlSource)
  (selected : Nat) (pairs : List (PqxdhKemIndCca.MlKem768PublicKey × KemSK))
  (publicKey : PqxdhKemIndCca.MlKem768PublicKey) (real : Bool)
local notation "provider" => RegistrationNativeKemOpenProvider.implementation (n := n) setup checks wire route representation created credential selected pairs publicKey real

/-- Original native trusted continuations with no birth request preserve the actual current genuine private prefix. -/
theorem trusted_keeps (chosen : Bool) (work : OracleComp (RegistrationNativeBeaconFrontend.Trusted n KemSK) Value)
    (bounded : work.IsQueryBoundP (counted (n := n) (KemSK := KemSK) .create) 0) :
    Keeps borns ((provider ∘ₛ lower chosen) ∘ₛ RegistrationNativeKemBeaconCompiler.trusted) work := by
  intro before after value supported
  apply RegistrationNativeKemOpenBirthFrame.no_create_keeps setup checks wire route representation created credential
    selected pairs publicKey real _ (trusted_bound chosen work 0 bounded) before after value
  simpa only [QueryImpl.simulateQ_compose] using supported

/-- The whole actual native Beacon wrapper preserves its private birth prefix whenever its derived controller bill is zero. -/
theorem beacon_keeps (chosen : Bool)
    (work : RegistrationNativeBeaconFrontend.M n KemSK mlSource RegistrationServerRoleBackend.State Value)
    (bounded : Bounded .create 0 work) :
    Keeps borns provider (simulateQ (lower chosen) (RegistrationNativeKemBeaconCompiler.beacon work)) :=
  RegistrationNativeKemOpenBirthFrame.no_create_keeps setup checks wire route representation created credential
    selected pairs publicKey real _
    (lower_bound chosen _ 0 (RegistrationNativeKemCompilerFootprint.beacon_bound .create work 0 bounded))

end BeaconcryptCore.Computational.RegistrationNativeKemOpenBirthCompiler

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemOpenBirthCompiler.lower_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemOpenBirthCompiler.lower_bound
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemOpenBirthCompiler.trusted_keeps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemOpenBirthCompiler.trusted_keeps
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemOpenBirthCompiler.beacon_keeps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemOpenBirthCompiler.beacon_keeps
