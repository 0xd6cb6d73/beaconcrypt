-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformLorCtxLeaves
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
namespace BeaconcryptCore.Computational.RegistrationNativePlatformLorCtxRealization
open PqxdhServerAuthExperiment (Setup)
open PqxdhKemIndCca
open RegistrationNativePlatformLorCtxLeaves (World Symbolic frame)
variable {n : Nat} {I KemSK Value : Type} {base : OracleSpec I}
variable (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes) (candidate : MlKemSharedSecret)
    (unused : QueryImpl RegistrationNativeSecretWordService.Combined (World n))
    (selected : Nat) (pairs : List (MlKem768PublicKey × KemSK)) (publicKey : MlKem768PublicKey) (challenge : MlKem768Ciphertext)
local notation "symbolicProvider" => RegistrationNativeSecretWordKemEarly.early setup.baseImpl setup.kem selected pairs publicKey challenge
local notation "actualProvider" => RegistrationNativeSecretWordKemEarly.actual setup.baseImpl setup.kem selected pairs publicKey challenge candidate
local notation "symbolic" => RegistrationNativePlatformLorCtxLeaves.lower setup wire sign seed scalar candidate unused symbolicProvider
local notation "actual" => RegistrationNativeSelectiveHiddenInterpreter.handler setup wire sign seed scalar candidate actualProvider

noncomputable def implementation : QueryImpl (RegistrationNativePublicFrontend.Spec n KemSK)
    (StateT (Symbolic n KemSK) (World n)) :=
  symbolic ∘ₛ RegistrationNativeSecretWordCheckedFrontend.realization candidate

section Routed
variable {m : Type → Type} [Monad m] [LawfulMonad m]
theorem routed_realization (lower : QueryImpl (RegistrationNativeSecretWordInterface.Spec n KemSK) m)
    (query : (RegistrationNativePublicFrontend.RoutedKem KemSK).Domain) :
    simulateQ lower (simulateQ RegistrationNativeSecretWordInterface.routedKem
      (RegistrationNativeSecretWordKemInterface.realize candidate query)) =
        RegistrationNativeSecretWordKemProvider.evalReply candidate query <$>
          lower (.inl (.inr (.inr query))) := by
  rcases query with (other | key) | (pool | key)
  all_goals try cases pool
  all_goals simp only [RegistrationNativeSecretWordKemInterface.realize,simulateQ_map,simulateQ_spec_query,
    RegistrationNativeSecretWordInterface.routedKem]
  all_goals first
    | rfl
    | (change _ = id <$> _; rw [id_map])
end Routed

theorem query_source (query : (RegistrationNativePublicFrontend.Spec n KemSK).Domain) (before : Symbolic n KemSK) :
    Prod.map id (frame candidate) <$>
      ((implementation setup wire sign seed scalar candidate unused selected pairs publicKey challenge query).run before) =
      (actual query).run (frame candidate before) := by
  rcases query with (message | (message | commonQuery) | routedQuery) | recordQuery
  · have sourceEq := RegistrationNativePlatformLorCtxLeaves.prepare_source setup wire sign seed scalar candidate unused
      symbolicProvider actualProvider (RegistrationNativeSecretWordMessage.literal message) before
    rw [RegistrationNativeSecretWordMessage.eval_literal] at sourceEq
    simpa only [implementation,QueryImpl.compose,RegistrationNativeSecretWordCheckedFrontend.realization,
      simulateQ_map,simulateQ_spec_query,StateT.run_map,Functor.map_map,Prod.map_def,id_eq] using sourceEq
  · have sourceEq := RegistrationNativePlatformLorCtxLeaves.demand_source setup wire sign seed scalar candidate unused
      symbolicProvider actualProvider (RegistrationNativeSecretWordMessage.literal message) before
    rw [RegistrationNativeSecretWordMessage.eval_literal] at sourceEq
    simpa only [implementation,QueryImpl.compose,RegistrationNativeSecretWordCheckedFrontend.realization,
      simulateQ_spec_query] using sourceEq
  · rcases commonQuery with publication | effect
    · simpa only [implementation,QueryImpl.compose,RegistrationNativeSecretWordCheckedFrontend.realization,
        simulateQ_spec_query] using RegistrationNativePlatformLorCtxLeaves.publication_source setup wire sign seed scalar candidate unused symbolicProvider actualProvider publication before
    · simpa only [implementation,QueryImpl.compose,RegistrationNativeSecretWordCheckedFrontend.realization,
        simulateQ_spec_query] using RegistrationNativePlatformLorCtxLeaves.effect_query_source setup wire sign seed scalar candidate unused symbolicProvider actualProvider effect before
  · simp only [implementation,QueryImpl.compose,RegistrationNativeSecretWordCheckedFrontend.realization]
    rw [routed_realization]
    simpa only [StateT.run_map,Functor.map_map,Prod.map_def,id_eq] using
      RegistrationNativePlatformLorCtxLeaves.kem_source setup wire sign seed scalar candidate unused selected pairs publicKey challenge routedQuery before
  · simpa only [implementation,QueryImpl.compose,RegistrationNativeSecretWordCheckedFrontend.realization,
      simulateQ_spec_query] using RegistrationNativePlatformLorCtxLeaves.record_source setup wire sign seed scalar candidate unused symbolicProvider actualProvider recordQuery before

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

variable {Auxiliary : Type} {source : RegistrationNativeMldsa.Source}
theorem beacon_collect_source (owner : RegistrationBeaconReferenceCompiler.SelectedOwner source)
    (oneTime : PqxdhJointGapDh.ScalarBytes) (authenticated : registration.AuthenticatedResponse)
    (env : RegistrationWorldAgreementCompiler.EnvState Auxiliary) (before : Symbolic n KemSK) :
    Prod.map (Prod.map (Option.map (RegistrationNativeSecretWordBeaconPrepare.eval candidate)) id) (frame candidate) <$>
      (simulateQ (symbolic ∘ₛ RegistrationNativeSecretWordInterface.liftLocal false)
        ((RegistrationNativeSecretWordBeaconCompiler.collect setup owner oneTime authenticated).run env)).run before =
      (simulateQ (actual ∘ₛ RegistrationNativePublicFrontend.liftLocal false)
        ((RegistrationBeaconReferenceCompiler.collect setup owner oneTime authenticated).run env)).run (frame candidate before) := by
  have sourceEq := local_program_source setup wire sign seed scalar candidate unused selected pairs publicKey challenge false
    ((RegistrationBeaconReferenceCompiler.collect setup owner oneTime authenticated).run env) before
  rw [RegistrationNativeSecretWordBeaconSource.collector_source] at sourceEq
  simpa only [simulateQ_map,StateT.run_map,Functor.map_map,Prod.map_def,id_eq] using sourceEq

end BeaconcryptCore.Computational.RegistrationNativePlatformLorCtxRealization

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorCtxRealization.routed_realization' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorCtxRealization.routed_realization

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorCtxRealization.query_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorCtxRealization.query_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorCtxRealization.program_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorCtxRealization.program_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorCtxRealization.local_program_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorCtxRealization.local_program_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorCtxRealization.beacon_collect_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorCtxRealization.beacon_collect_source
