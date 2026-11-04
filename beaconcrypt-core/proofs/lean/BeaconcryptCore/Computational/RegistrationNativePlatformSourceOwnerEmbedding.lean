-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformSourceOwnerJoint
/-! The joint owner language embeds exactly into the corrected public frontend's local language. The interpreted source program is obtained by composition of the literal source dictionary, including every external uniform draw; no native controller equation is an input. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformSourceOwnerEmbedding
open PqxdhServerAuthExperiment (Setup)
open RegistrationNativePlatformSourceOwnerJoint (Spec sourceHandler)
open RegistrationNativePublicSourceEffects (close)
variable {n : Nat} {ι KemSK Value : Type} {base : OracleSpec ι}

def embed : QueryImpl (Spec n KemSK) (OracleComp (RegistrationNativePlatformPublicFrontend.LocalSpec n KemSK))
  | .inl query => simulateQ (RegistrationNativePlatformPublicFrontend.localQuery false)
      (RegistrationBeaconReferenceCompiler.trustedLift query)
  | .inr query => RegistrationNativePlatformPublicFrontend.localCoin query

private theorem reference_query (query : (RegistrationNativeKemReferenceCompiler.Spec n KemSK).Domain) :
    simulateQ RegistrationNativePlatformPublicFrontend.embedLocal
      (RegistrationNativePlatformPublicFrontend.localQuery false query) =
    simulateQ RegistrationNativePlatformPublicFrontend.old
      (RegistrationNativePublicFrontend.liftLocal false query) := by
  rcases query with message | message | query | query
  · rfl
  · rfl
  · cases query <;> rfl
  · cases query <;> rfl

private theorem reference_program (work : OracleComp (RegistrationNativeKemReferenceCompiler.Spec n KemSK) Value) :
    simulateQ RegistrationNativePlatformPublicFrontend.embedLocal
      (simulateQ (RegistrationNativePlatformPublicFrontend.localQuery false) work) =
    simulateQ RegistrationNativePlatformPublicFrontend.old
      (simulateQ (RegistrationNativePublicFrontend.liftLocal false) work) := by
  rw [← QueryImpl.simulateQ_compose, ← QueryImpl.simulateQ_compose]
  congr 1
  funext query
  exact reference_query query

private theorem old_program (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (work : OracleComp (RegistrationNativePublicFrontend.Spec n KemSK) Value) :
    simulateQ (RegistrationNativePlatformPublicSourceExecution.handler setup wire route sign)
      (simulateQ RegistrationNativePlatformPublicFrontend.old work) =
    simulateQ (RegistrationNativePublicInterpreter.handler setup wire route sign) work := by
  rw [← QueryImpl.simulateQ_compose]
  congr 1
  funext query
  simp only [QueryImpl.compose, RegistrationNativePlatformPublicFrontend.old, simulateQ_spec_query,
    RegistrationNativePlatformPublicSourceExecution.handler]

/-- A single embedded joint query closes to the exact existing source request or external coin leaf. -/
theorem query_source (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (query : (Spec n KemSK).Domain) :
    close setup seed scalar (simulateQ (RegistrationNativePlatformPublicSourceExecution.handler setup wire route sign)
      (simulateQ RegistrationNativePlatformPublicFrontend.embedLocal (embed query))) =
      sourceHandler setup wire route sign seed scalar query := by
  cases query with
  | inl query =>
    simp only [embed, reference_program, old_program, sourceHandler, RegistrationNativePublicSourceTrusted.implementation]
  | inr query =>
    funext before
    simp only [embed, RegistrationNativePlatformPublicFrontend.localCoin, simulateQ_spec_query,
      RegistrationNativePlatformPublicFrontend.embedLocal, RegistrationNativePlatformPublicFrontend.publicCoin,
      RegistrationNativePlatformPublicSourceExecution.handler, sourceHandler, close, StateT.run]
    rfl

/-- Every adaptive embedded joint program uses that same complete source dictionary. -/
theorem program_source (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (work : OracleComp (Spec n KemSK) Value) :
    close setup seed scalar (simulateQ (RegistrationNativePlatformPublicSourceExecution.handler setup wire route sign)
      (simulateQ RegistrationNativePlatformPublicFrontend.embedLocal (simulateQ embed work))) =
      simulateQ (sourceHandler setup wire route sign seed scalar) work := by
  funext before
  induction work using OracleComp.inductionOn generalizing before with
  | pure value => rfl
  | query_bind query next ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, close, StateT.run,
      StateT.monad_bind_def, StateT.bind, simulateQ_bind]
    have leaf := congrFun (query_source setup wire route sign seed scalar query) before
    simp only [close, StateT.run] at leaf
    rw [leaf]
    apply bind_congr
    rintro ⟨value, current⟩
    exact ih value current
end BeaconcryptCore.Computational.RegistrationNativePlatformSourceOwnerEmbedding

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSourceOwnerEmbedding.query_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSourceOwnerEmbedding.query_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSourceOwnerEmbedding.program_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSourceOwnerEmbedding.program_source
