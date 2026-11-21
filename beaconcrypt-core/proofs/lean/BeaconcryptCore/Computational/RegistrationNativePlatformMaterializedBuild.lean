-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformMaterializedServerFrontend
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicCoinEmbedding
import BeaconcryptCore.Computational.RegistrationNativeG3MaterializedLocal
/-! The complete corrected public build callback inherits the actual moved-token source materialization equation. The proof follows its literal effect/demand embeddings and retains its complete frontend and persistent platform poststate. No previous native build identity is used. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformMaterializedBuild
variable {n : Nat} {E Platform KemSK A : Type}

noncomputable def embedding : QueryImpl (RegistrationNativePlatformServerFrontendCompiler.Spec n)
    (OracleComp (RegistrationNativePublicFrontend.Spec n KemSK)) :=
  RegistrationNativePlatformPublicCoinEmbedding.embed ∘ₛ RegistrationNativePlatformPublicFrontend.embedLocal ∘ₛ
    RegistrationNativePlatformPublicFrontend.buildEmbedding

private theorem translation (full : Bool) (seeds : RegistrationNativeG3AuditedWorld.Seeds n) :
    RegistrationNativeG3MaterializedLocal.translate (KemSK := KemSK) full seeds ∘ₛ embedding =
      embedding ∘ₛ RegistrationNativePlatformMaterializedServerFrontend.translate full seeds := by
  funext query
  rcases query with message | query
  · cases full <;> rfl
  · cases query with
    | inr coin => cases full <;> rfl
    | inl effect => cases effect with
      | inl coin => cases full <;> rfl
      | inr capability =>
        cases capability <;> try (cases full <;> rfl)
        case installServer keyId binding kernel => cases kernel <;> cases full <;> rfl
        case installBeacon owner shell kernel => cases kernel <;> cases full <;> rfl
private theorem translated (full : Bool) (seeds : RegistrationNativeG3AuditedWorld.Seeds n)
    (work : OracleComp (RegistrationNativePlatformServerFrontendCompiler.Spec n) A) :
    simulateQ (RegistrationNativeG3MaterializedLocal.translate (KemSK := KemSK) full seeds)
      (simulateQ embedding work) =
      simulateQ embedding (simulateQ (RegistrationNativePlatformMaterializedServerFrontend.translate full seeds) work) := by
  rw [← QueryImpl.simulateQ_compose, ← QueryImpl.simulateQ_compose, translation]

open PqxdhServerAuthExperiment (Setup)
variable {I : Type} {base : OracleSpec I}
variable [primitive : BeaconcryptCore.Refinement.AdapterSealPrimitive.Operations]
variable (setup : Setup base KemSK)
    (source : RegistrationNativeMldsa.Source)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (BeaconcryptCore.Refinement.AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (reserve : StateT Platform ProbComp Bool)

/-- The literal corrected full public build callback preserves its returned frontend/P value under fixed private-seed materialization on the global mixed interface. -/
theorem build_source (seeds : RegistrationNativeG3AuditedWorld.Seeds n)
    (handle : Nat) (application : Option (Slice U8)) (before : RegistrationNativePlatformPublicFrontend.State source Platform) :
    simulateQ (RegistrationNativeG3MaterializedLocal.translate true seeds)
      (simulateQ RegistrationNativePlatformPublicCoinEmbedding.embed
        ((RegistrationNativePlatformPublicFrontend.executeLocal (KemSK := KemSK)
          (RegistrationNativePlatformPublicFrontend.build setup sign view failure allocation erased helper writer reserve handle application source)).run before)) =
      simulateQ (RegistrationNativeG3MaterializedLocal.translate false seeds)
        (simulateQ RegistrationNativePlatformPublicCoinEmbedding.embed
          ((RegistrationNativePlatformPublicFrontend.executeLocal (KemSK := KemSK)
            (RegistrationNativePlatformPublicFrontend.build setup sign view failure allocation erased helper writer reserve handle application source)).run before)) := by
  have same := congrArg (simulateQ (embedding (KemSK := KemSK)))
    (RegistrationNativePlatformMaterializedServerFrontend.build_source setup.source view failure allocation erased helper sign writer reserve seeds handle application before.1.server (before.1.environment.receipts, before.2))
  rw [← translated true seeds, ← translated false seeds] at same
  have mapped := congrArg (fun action => (fun result =>
    (RegistrationNativePlatformPublicFrontend.responseBytes result.1.1,
      ({ before.1 with server := result.1.2, environment :=
        { before.1.environment with receipts := result.2.1, recordRequests := [] } }, result.2.2))) <$> action) same
  simpa only [embedding, QueryImpl.simulateQ_compose,
    RegistrationNativePlatformPublicFrontend.executeLocal, RegistrationNativePlatformPublicFrontend.build,
    StateT.run, simulateQ_map] using mapped

end BeaconcryptCore.Computational.RegistrationNativePlatformMaterializedBuild

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformMaterializedBuild.build_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformMaterializedBuild.build_source
