-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealTraceRealization
import BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealBeaconMap
import BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealOrdinaryLeaves
import BeaconcryptCore.Computational.RegistrationNativePlatformLorCtxRealization
import BeaconcryptCore.Computational.RegistrationNativeSecretWordCheckedFrontendLift
import BeaconcryptCore.Computational.RegistrationNativeSecretWordBeaconSource
/-! The literal native request surface realizes through the open symbolic dictionary while the physical World remains free. The proof uses the concrete per-query source equations, not a whole-controller law. All arbitrary adaptive native work and its complete private/physical poststate can then be transported by the generic state projection theorem. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealTraceBeacon
open PqxdhServerAuthExperiment (Setup)
open PqxdhKemIndCca
open RegistrationNativePlatformLorCtxLeaves (World)
open RegistrationNativePlatformLorIdealTraceLeaves (project)
open RegistrationNativePlatformLorIdealTraceRealization (Symbolic)
local notation "frame" => project
variable {n : Nat} {I KemSK Value : Type} {base : OracleSpec I}
variable (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes) (candidate : MlKemSharedSecret)
    (unused : QueryImpl RegistrationNativeSecretWordService.Combined (World n))
    (selected : Nat) (pairs : List (MlKem768PublicKey × KemSK)) (publicKey : MlKem768PublicKey) (challenge : MlKem768Ciphertext)
local notation "symbolic" => RegistrationNativePlatformLorIdealTraceLeaves.symbolicTrace setup wire sign seed scalar candidate unused selected pairs publicKey challenge
local notation "actual" => RegistrationNativePlatformLorIdealTraceLeaves.nativeTrace setup wire sign seed scalar candidate selected pairs publicKey challenge

local notation "wordLocal" => symbolic ∘ₛ RegistrationNativeSecretWordInterface.liftLocal false
local notation "nativeLocal" => actual ∘ₛ RegistrationNativePublicFrontend.liftLocal false

theorem local_leaves : RegistrationNativePlatformLorIdealAcceptCore.Leaves candidate nativeLocal wordLocal (frame candidate) := by
  constructor
  · intro query before
    have compared := RegistrationNativePlatformLorIdealTraceRealization.local_program_source setup wire sign seed scalar candidate unused selected pairs publicKey challenge false
      (((RegistrationBeaconReferenceCompiler.Spec n KemSK).query query) : OracleComp (RegistrationBeaconReferenceCompiler.Spec n KemSK) _) before
    simpa only [simulateQ_spec_query,QueryImpl.apply_compose] using compared
  · intro message before
    have compared := RegistrationNativePlatformLorIdealTraceLeaves.query_source setup wire sign seed scalar candidate unused selected pairs publicKey challenge
      (.inl (.inl message)) before
    convert compared using 1 <;>
      simp only [QueryImpl.compose,RegistrationNativeSecretWordInterface.prepare,RegistrationBeaconReferenceCompiler.prepare,
        simulateQ_spec_query,RegistrationNativeSecretWordInterface.liftLocal,RegistrationNativePublicFrontend.liftLocal,
        RegistrationNativePlatformLorCtxLeaves.nativeQuery]; rfl

noncomputable def wordLocalScalar (localScalar : Option PqxdhJointGapDh.ScalarBytes) :
    QueryImpl (RegistrationNativeSecretWordInterface.LocalSpec n KemSK) (StateT (Symbolic n KemSK) (World n)) :=
  match localScalar with
  | none => wordLocal
  | some localScalar => wordLocal ∘ₛ RegistrationNativeSecretWordOwners.ordinary setup localScalar
noncomputable def nativeLocalScalar (localScalar : Option PqxdhJointGapDh.ScalarBytes) :
    QueryImpl (RegistrationBeaconReferenceCompiler.Spec n KemSK)
      (StateT (RegistrationNativeG2Trace.State × RegistrationNativeSelectiveHiddenInterpreter.State n KemSK RegistrationNativeKemSwitchSource.Phase) (World n)) :=
  match localScalar with
  | none => nativeLocal
  | some localScalar => nativeLocal ∘ₛ RegistrationNativePublicOwners.ordinary setup localScalar
local notation "wordChosen" => wordLocalScalar setup wire sign seed scalar candidate unused selected pairs publicKey challenge
local notation "nativeChosen" => nativeLocalScalar setup wire sign seed scalar candidate selected pairs publicKey challenge

theorem scalar_leaves (localScalar : Option PqxdhJointGapDh.ScalarBytes) :
    RegistrationNativePlatformLorIdealAcceptCore.Leaves candidate (nativeChosen localScalar) (wordChosen localScalar) (frame candidate) := by
  cases localScalar with
  | none => exact local_leaves setup wire sign seed scalar candidate unused selected pairs publicKey challenge
  | some localScalar =>
    exact RegistrationNativePlatformLorIdealOrdinaryLeaves.ordinary_leaves candidate nativeLocal wordLocal (frame candidate)
      (local_leaves setup wire sign seed scalar candidate unused selected pairs publicKey challenge) setup localScalar

theorem demand_source (localScalar : Option PqxdhJointGapDh.ScalarBytes) (reference : RegistrationNativeSecretWordMessage.Message)
    (before : Symbolic n KemSK) :
    Prod.map id (frame candidate) <$>
      (simulateQ (wordChosen localScalar) (RegistrationNativeSecretWordInterface.demand reference)).run before =
      (simulateQ (nativeChosen localScalar) (RegistrationNativePlatformBeaconMaterialInterpreter.demand
        (RegistrationNativeSecretWordMessage.eval candidate reference))).run (frame candidate before) := by
  have compared := RegistrationNativePlatformLorIdealTraceLeaves.query_source setup wire sign seed scalar candidate unused selected pairs publicKey challenge
    (.inl (.inr (.inl (.inl reference)))) before
  cases localScalar <;>
    convert compared using 1 <;>
      simp only [wordLocalScalar,nativeLocalScalar,QueryImpl.compose,RegistrationNativeSecretWordInterface.demand,
        RegistrationNativePlatformBeaconMaterialInterpreter.demand,simulateQ_spec_query,
        RegistrationNativeSecretWordInterface.liftLocal,RegistrationNativePublicFrontend.liftLocal,
        RegistrationNativeSecretWordOwners.ordinary,RegistrationNativePublicOwners.ordinary,
        RegistrationNativePlatformLorCtxLeaves.nativeQuery] <;> rfl

variable {source : RegistrationNativeMldsa.Source}
theorem finish_source (localScalar : Option PqxdhJointGapDh.ScalarBytes)
    (owner : RegistrationBeaconReferenceCompiler.SelectedOwner source) (packet : Option registration.ResponsePacket)
    (env : RegistrationWorldAgreementCompiler.EnvState RegistrationServerRoleBackend.State) (before : Symbolic n KemSK) :
    Prod.map id (frame candidate) <$>
      (simulateQ (wordChosen localScalar) (((RegistrationNativePlatformSecretWordFinish.finish setup wire source packet).run owner).run env)).run before =
      (simulateQ (nativeChosen localScalar) (((RegistrationNativePlatformBeaconReferenceFinish.finish setup wire source packet).run owner).run env)).run (frame candidate before) :=
  RegistrationNativePlatformLorIdealBeaconMap.finish_source candidate (nativeChosen localScalar) (wordChosen localScalar) (frame candidate)
    (scalar_leaves setup wire sign seed scalar candidate unused selected pairs publicKey challenge localScalar)
    (demand_source setup wire sign seed scalar candidate unused selected pairs publicKey challenge localScalar) setup wire owner packet env before

end BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealTraceBeacon

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealTraceBeacon.local_leaves' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealTraceBeacon.local_leaves

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealTraceBeacon.scalar_leaves' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealTraceBeacon.scalar_leaves

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealTraceBeacon.demand_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealTraceBeacon.demand_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealTraceBeacon.finish_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealTraceBeacon.finish_source
