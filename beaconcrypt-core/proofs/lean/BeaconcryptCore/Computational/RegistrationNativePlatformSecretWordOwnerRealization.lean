-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordOwnerSyntax
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicFrontend
import BeaconcryptCore.Computational.RegistrationNativeSecretWordCheckedFrontendLift
/-! Actual creation and stateful Init publication retain every common platform result under candidate-free Word realization. The source-derived no-shared-secret footprint is used only for these literal controller bodies. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordOwnerRealization
open PqxdhServerAuthExperiment (Setup)
open RegistrationNativeSecretWordMessage (zero)
open RegistrationNativeSecretWordCheckedFrontend (realization)
open RegistrationNativePlatformPublicFrontend (LocalSpec trusted writer)
variable {n : Nat} {I KemSK Platform E A B : Type} {source : RegistrationNativeMldsa.Source} {spec : OracleSpec I}

def base (candidate : PqxdhKemIndCca.MlKemSharedSecret) :
    QueryImpl (LocalSpec n KemSK) (OracleComp (RegistrationNativeSecretWordInterface.Spec n KemSK))
  | .inl query => realization candidate (.inl query)
  | .inr coin => RegistrationNativeSecretWordFrontend.effect (.inl coin)

def evaluated (candidate : PqxdhKemIndCca.MlKemSharedSecret)
    (work : StateT Platform (OracleComp (LocalSpec n KemSK)) A) :
    StateT Platform (OracleComp (RegistrationNativeSecretWordInterface.Spec n KemSK)) A :=
  fun previous => simulateQ (base candidate) (work.run previous)

private theorem program_evaluated (candidate : PqxdhKemIndCca.MlKemSharedSecret)
    (implementation : QueryImpl spec (StateT Platform (OracleComp (LocalSpec n KemSK))))
    (work : OracleComp spec A) (previous : Platform) :
    simulateQ (base candidate) ((simulateQ implementation work).run previous) =
      (simulateQ (fun query => evaluated candidate (implementation query)) work).run previous := by
  induction work using OracleComp.inductionOn generalizing previous with
  | pure value => rfl
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, simulateQ_bind]
      congr 1
      funext result
      exact ih result.1 result.2

private theorem local_embedding (candidate : PqxdhKemIndCca.MlKemSharedSecret) :
    base (n := n) (KemSK := KemSK) candidate ∘ₛ RegistrationNativePlatformPublicFrontend.localQuery false =
      RegistrationNativeSecretWordInterface.liftLocal false ∘ₛ RegistrationNativeSecretWordServerSource.realize candidate := by
  rw [← RegistrationNativeSecretWordCheckedFrontendLift.realization_local]
  funext query
  rcases query with message | common | kem
  · rfl
  · rfl
  · simp only [QueryImpl.compose, RegistrationNativePlatformPublicFrontend.localQuery,
      RegistrationNativePublicFrontend.liftLocal, ← QueryImpl.simulateQ_compose]
    congr 1

private theorem trusted_evaluated (candidate : PqxdhKemIndCca.MlKemSharedSecret)
    (query : (RegistrationNativeBeaconFrontend.Trusted n KemSK).Domain)
    (safe : RegistrationNativeSecretWordTargetBirthCaps.Allowed (KemSK := KemSK) query) (previous : Platform) :
    (evaluated candidate (trusted query)).run previous = (evaluated zero (trusted query)).run previous := by
  change simulateQ (base candidate) ((trusted query).run previous) =
    simulateQ (base zero) ((trusted query).run previous)
  simp only [RegistrationNativePlatformPublicFrontend.trusted, StateT.run_lift,
    bind_pure_comp, simulateQ_map]
  rw [← QueryImpl.simulateQ_compose, local_embedding, QueryImpl.simulateQ_compose,
    RegistrationNativeSecretWordTargetBirth.query_realize candidate query safe,
    ← QueryImpl.simulateQ_compose, ← local_embedding, QueryImpl.simulateQ_compose]

private theorem writer_evaluated (candidate : PqxdhKemIndCca.MlKemSharedSecret)
    (implementation : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (query : (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E).Domain) (previous : Platform) :
    (evaluated (n := n) (KemSK := KemSK) candidate (writer implementation query)).run previous =
      (evaluated zero (writer implementation query)).run previous := by
  simp only [evaluated, writer, RegistrationNativePlatformPublicFrontend.platform, StateT.run,
    ← QueryImpl.simulateQ_compose]
  rfl
private theorem program_same (candidate : PqxdhKemIndCca.MlKemSharedSecret)
    (implementation : QueryImpl spec (StateT Platform (OracleComp (LocalSpec n KemSK))))
    (predicate : I → Prop)
    (same : ∀ query, predicate query → ∀ previous, (evaluated candidate (implementation query)).run previous =
      (evaluated zero (implementation query)).run previous)
    (work : OracleComp spec A) (safe : AllQueriesSatisfy work predicate) (previous : Platform) :
    simulateQ (base candidate) ((simulateQ implementation work).run previous) =
      simulateQ (base zero) ((simulateQ implementation work).run previous) := by
  rw [program_evaluated, program_evaluated]
  induction work using OracleComp.inductionOn generalizing previous with
  | pure value => rfl
  | query_bind query next ih =>
      obtain ⟨first, later⟩ := (allQueriesSatisfy_query_bind_iff _ _ _).mp safe
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
      rw [same query first previous]
      congr 1
      funext result
      exact ih result.1 (later result.1) result.2

private theorem map_apply {S X Y : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (f : X → Y) (work : StateT S m X) (before : S) :
    (f <$> work) before = Prod.map f id <$> work before := StateT.run_map f work before

variable {baseSpec : OracleSpec I}
/-- Actual creation is independent of the unrealized shared-secret atom, including every source failure and common platform result. -/
theorem create (setup : Setup baseSpec KemSK) (selected : Nat)
    (publicPrekey : PqxdhJointIdentity.PeerEncoding) (candidate : PqxdhKemIndCca.MlKemSharedSecret)
    (edPin : Std.Array U8 32#usize) (mlPin : Std.Array U8 1952#usize) (keyId : U64)
    (owners : RegistrationNativePublicOwners.State source)
    (env : RegistrationServerReferenceCompiler.Environment) (previous : Platform) :
    simulateQ (base (n := n) candidate)
      ((((RegistrationNativePlatformPublicOwners.create trusted setup source selected publicPrekey edPin mlPin keyId).run owners).run env).run previous) =
    simulateQ (base zero)
      ((((RegistrationNativePlatformPublicOwners.create trusted setup source selected publicPrekey edPin mlPin keyId).run owners).run env).run previous) := by
  simp only [RegistrationNativePlatformPublicOwners.create, RegistrationNativePlatformPublicOwners.executeLocal,
    RegistrationNativePlatformGenericBundle.liftLegacy, StateT.run, map_apply, simulateQ_map]
  apply congrArg (Functor.map _)
  exact program_same candidate trusted RegistrationNativeSecretWordTargetBirthCaps.Allowed
    (trusted_evaluated candidate) _
    (RegistrationNativeSecretWordTargetBirthCaps.create_safe setup edPin mlPin keyId _ env) previous
/-- The actual effectful writer runs in the same platform state at every Word realization. -/
theorem bundle (setup : Setup baseSpec KemSK) (selected : Nat)
    (publicPrekey : PqxdhJointIdentity.PeerEncoding) (candidate : PqxdhKemIndCca.MlKemSharedSecret)
    (implementation : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (index : Nat) (owners : RegistrationNativePublicOwners.State source)
    (env : RegistrationServerReferenceCompiler.Environment) (previous : Platform) :
    simulateQ (base (n := n) candidate)
      ((((RegistrationNativePlatformPublicOwners.bundle trusted (writer implementation) setup source selected publicPrekey index).run owners).run env).run previous) =
    simulateQ (base zero)
      ((((RegistrationNativePlatformPublicOwners.bundle trusted (writer implementation) setup source selected publicPrekey index).run owners).run env).run previous) := by
  let joint : QueryImpl (RegistrationNativePlatformGenericBundle.Spec E n KemSK)
      (StateT Platform (OracleComp (LocalSpec n KemSK)))
    | .inl query => trusted query
    | .inr query => writer implementation query
  have actual := RegistrationNativePlatformGenericBundle.program_evaluate
    (source := source) (Auxiliary := RegistrationServerRoleBackend.State) joint setup index
  change RegistrationNativePlatformGenericBundle.evaluate joint _ =
    RegistrationNativePlatformGenericBundle.bundle trusted setup source
      (RegistrationNativePlatformGenericBundle.encoderWith (writer implementation)) index at actual
  simp only [RegistrationNativePlatformPublicOwners.bundle, RegistrationNativePlatformPublicOwners.executeLocal,
    StateT.run, map_apply, simulateQ_map]
  rw [← actual]
  unfold RegistrationNativePlatformGenericBundle.evaluate
  apply congrArg (Functor.map _)
  apply program_same candidate joint RegistrationNativePlatformSecretWordOwnerSyntax.Allowed
  · intro query safe current
    cases query with
    | inl query => exact trusted_evaluated candidate query safe current
    | inr query => exact writer_evaluated candidate implementation query current
  · exact RegistrationNativePlatformSecretWordOwnerSyntax.program_free setup index _ env
end BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordOwnerRealization

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordOwnerRealization.create' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordOwnerRealization.create

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordOwnerRealization.bundle' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordOwnerRealization.bundle
