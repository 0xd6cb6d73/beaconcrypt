-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealTraceLeaves
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
namespace BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealTraceRealization
open PqxdhServerAuthExperiment (Setup)
open PqxdhKemIndCca
open RegistrationNativePlatformLorCtxLeaves (World)
open RegistrationNativePlatformLorIdealTraceLeaves (project)
abbrev Symbolic (n : Nat) (KemSK : Type) := RegistrationNativeSecretWordFrontendTrace.State × RegistrationNativePlatformLorCtxLeaves.Symbolic n KemSK
local notation "frame" => project
variable {n : Nat} {I KemSK Value : Type} {base : OracleSpec I}
variable (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes) (candidate : MlKemSharedSecret)
    (unused : QueryImpl RegistrationNativeSecretWordService.Combined (World n))
    (selected : Nat) (pairs : List (MlKem768PublicKey × KemSK)) (publicKey : MlKem768PublicKey) (challenge : MlKem768Ciphertext)
local notation "symbolic" => RegistrationNativePlatformLorIdealTraceLeaves.symbolicTrace setup wire sign seed scalar candidate unused selected pairs publicKey challenge
local notation "actual" => RegistrationNativePlatformLorIdealTraceLeaves.nativeTrace setup wire sign seed scalar candidate selected pairs publicKey challenge

noncomputable def implementation : QueryImpl (RegistrationNativePublicFrontend.Spec n KemSK)
    (StateT (Symbolic n KemSK) (World n)) :=
  symbolic ∘ₛ RegistrationNativeSecretWordCheckedFrontend.realization candidate

theorem query_source (query : (RegistrationNativePublicFrontend.Spec n KemSK).Domain) (before : Symbolic n KemSK) :
    Prod.map id (frame candidate) <$>
      ((implementation setup wire sign seed scalar candidate unused selected pairs publicKey challenge query).run before) =
      (actual query).run (frame candidate before) := by
  rcases query with (message | (message | commonQuery) | routedQuery) | recordQuery
  · convert RegistrationNativePlatformLorIdealTraceLeaves.query_source setup wire sign seed scalar candidate unused
      selected pairs publicKey challenge (.inl (.inl (RegistrationNativeSecretWordMessage.literal message))) before using 1 <;>
      simp only [implementation,QueryImpl.compose,RegistrationNativeSecretWordCheckedFrontend.realization,
        RegistrationNativePlatformLorCtxLeaves.nativeReply,RegistrationNativePlatformLorCtxLeaves.nativeQuery,
        simulateQ_map,simulateQ_spec_query,StateT.run_map,
        Functor.map_map,Prod.map_def,id_eq] <;> rfl
  · convert RegistrationNativePlatformLorIdealTraceLeaves.query_source setup wire sign seed scalar candidate unused
      selected pairs publicKey challenge (.inl (.inr (.inl (.inl (RegistrationNativeSecretWordMessage.literal message))))) before using 1 <;>
      simp only [implementation,QueryImpl.compose,RegistrationNativeSecretWordCheckedFrontend.realization,
        RegistrationNativePlatformLorCtxLeaves.nativeReply,RegistrationNativePlatformLorCtxLeaves.nativeQuery,
        simulateQ_spec_query,Prod.map_def,id_eq] <;> rfl
  · rcases commonQuery with publication | effect
    · convert RegistrationNativePlatformLorIdealTraceLeaves.query_source setup wire sign seed scalar candidate unused
        selected pairs publicKey challenge (.inl (.inr (.inl (.inr (.inl publication))))) before using 1 <;>
        simp only [implementation,QueryImpl.compose,RegistrationNativeSecretWordCheckedFrontend.realization,
          RegistrationNativePlatformLorCtxLeaves.nativeReply,RegistrationNativePlatformLorCtxLeaves.nativeQuery,
          simulateQ_spec_query,Prod.map_def,id_eq]; rfl
    · convert RegistrationNativePlatformLorIdealTraceLeaves.query_source setup wire sign seed scalar candidate unused
        selected pairs publicKey challenge (.inl (.inr (.inl (.inr (.inr effect))))) before using 1 <;>
        simp only [implementation,QueryImpl.compose,RegistrationNativeSecretWordCheckedFrontend.realization,
          RegistrationNativePlatformLorCtxLeaves.nativeReply,RegistrationNativePlatformLorCtxLeaves.nativeQuery,
          simulateQ_spec_query,Prod.map_def,id_eq]; rfl
  · simp only [implementation,QueryImpl.compose,RegistrationNativeSecretWordCheckedFrontend.realization]
    rw [RegistrationNativePlatformLorCtxRealization.routed_realization]
    convert RegistrationNativePlatformLorIdealTraceLeaves.query_source setup wire sign seed scalar candidate unused selected pairs publicKey challenge
      (.inl (.inr (.inr routedQuery))) before using 1 <;>
      simp only [RegistrationNativePlatformLorCtxLeaves.nativeReply,RegistrationNativePlatformLorCtxLeaves.nativeQuery,
        StateT.run_map,Functor.map_map,Prod.map_def,id_eq]; rfl
  · convert RegistrationNativePlatformLorIdealTraceLeaves.query_source setup wire sign seed scalar candidate unused selected pairs publicKey challenge
      (.inr recordQuery) before using 1 <;>
      simp only [implementation,QueryImpl.compose,RegistrationNativeSecretWordCheckedFrontend.realization,
        RegistrationNativePlatformLorCtxLeaves.nativeReply,RegistrationNativePlatformLorCtxLeaves.nativeQuery,
        simulateQ_spec_query,Prod.map_def,id_eq]; rfl

theorem program_source (work : OracleComp (RegistrationNativePublicFrontend.Spec n KemSK) Value) (before : Symbolic n KemSK) :
    Prod.map id (frame candidate) <$>
      (simulateQ (implementation setup wire sign seed scalar candidate unused selected pairs publicKey challenge) work).run before =
      (simulateQ actual work).run (frame candidate before) :=
  OracleComp.map_run_simulateQ_eq_of_query_map_eq
    (implementation setup wire sign seed scalar candidate unused selected pairs publicKey challenge) actual (frame candidate)
    (query_source setup wire sign seed scalar candidate unused selected pairs publicKey challenge) work before
theorem local_program_source (routed : Bool)
    (work : OracleComp (RegistrationBeaconReferenceCompiler.Spec n KemSK) Value) (before : Symbolic n KemSK) :
    Prod.map id (frame candidate) <$>
      (simulateQ (symbolic ∘ₛ RegistrationNativeSecretWordInterface.liftLocal routed)
        (simulateQ (RegistrationNativeSecretWordServerSource.realize candidate) work)).run before =
      (simulateQ (actual ∘ₛ RegistrationNativePublicFrontend.liftLocal routed) work).run (frame candidate before) := by
  have localEq : simulateQ (RegistrationNativeSecretWordCheckedFrontend.realization candidate)
      (simulateQ (RegistrationNativePublicFrontend.liftLocal routed) work) =
      simulateQ (RegistrationNativeSecretWordInterface.liftLocal routed)
        (simulateQ (RegistrationNativeSecretWordServerSource.realize candidate) work) := by
    rw [←QueryImpl.simulateQ_compose,RegistrationNativeSecretWordCheckedFrontendLift.realization_local,QueryImpl.simulateQ_compose]
  have sourceEq := program_source setup wire sign seed scalar candidate unused selected pairs publicKey challenge
    (simulateQ (RegistrationNativePublicFrontend.liftLocal routed) work) before
  simp only [implementation,QueryImpl.simulateQ_compose] at sourceEq
  rw [localEq] at sourceEq
  simpa only [QueryImpl.simulateQ_compose] using sourceEq


end BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealTraceRealization

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealTraceRealization.query_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealTraceRealization.query_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealTraceRealization.program_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealTraceRealization.program_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealTraceRealization.local_program_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealTraceRealization.local_program_source
