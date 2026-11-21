-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeObservedStageTrace
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildPublication
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterLowSpec
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterSourceRuntime
/-! The source observer records actual source requests and replies, before the enclosing continuation can fail. Its live state is the complete physical source state. Removing the private observation log retains that same source execution; no native audit call is manufactured or used as a source observation. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterSourceTrace
open BeaconcryptCore.Refinement

/-- Each entry is an actual reached source operation, including absent signatures and unsuccessful first-record results. -/
inductive Stage where
  | hash (request : registration.HashRequest) (digest : CtxRomAuth.CtxDigest)
  | sign (request : registration.MldsaSigningRequest) (payload : MldsaTranscriptAuth.Payload)
      (digest : CtxRomAuth.CtxDigest) (reply : RegistrationSigningShared.SignReply)
  | firstRecord (initial : registration.ServerInitialKdf) (reply : RustM RegistrationServerRecordExecutor.Result)
  | beaconFirstRecord (initial : registration.BeaconInitialKdf) (reply : RustM RegistrationBeaconRecordExecutor.Result)

variable {Q S T Log A : Type} {spec : OracleSpec Q}
variable {m : Type → Type} [Monad m] [LawfulMonad m]

/-- Execute the source leaf once, then append observations of that exact reply. -/
def recorded (implementation : QueryImpl spec (StateT S m))
    (observe : (query : spec.Domain) → spec.Range query → List Log) :
    QueryImpl spec (StateT (S × List Log) m) := fun query before =>
  (fun result => (result.1, (result.2, before.2 ++ observe query result.1))) <$>
    (implementation query).run before.1

theorem erase (implementation : QueryImpl spec (StateT S m))
    (observe : (query : spec.Domain) → spec.Range query → List Log)
    (work : OracleComp spec A) (before : S × List Log) :
    Prod.map id Prod.fst <$> (simulateQ (recorded implementation observe) work).run before =
      (simulateQ implementation work).run before.1 := by
  apply OracleComp.map_run_simulateQ_eq_of_query_map_eq
  intro query current
  simp only [recorded, StateT.run, Functor.map_map, Prod.map, id_eq]
  exact id_map _

/-- The same source-state interpretation preserves the actual reply log jointly, rather than selecting a compatible log afterward. -/
theorem source (left : QueryImpl spec (StateT S m)) (right : QueryImpl spec (StateT T m))
    (projection : S → T)
    (step : ∀ query before, Prod.map id projection <$> (left query).run before = (right query).run (projection before))
    (observe : (query : spec.Domain) → spec.Range query → List Log)
    (work : OracleComp spec A) (before : S × List Log) :
    Prod.map id (Prod.map projection id) <$> (simulateQ (recorded left observe) work).run before =
      (simulateQ (recorded right observe) work).run (projection before.1, before.2) := by
  apply OracleComp.map_run_simulateQ_eq_of_query_map_eq
  intro query current
  have same := congrArg (fun distribution =>
    (fun result : spec.Range query × T =>
      (result.1, (result.2, current.2 ++ observe query result.1))) <$> distribution) (step query current.1)
  simpa only [recorded, StateT.run, Functor.map_map, Prod.map, id_eq] using same

/-- Each later source continuation retains every earlier reached observation, regardless of its own return value. -/
theorem append_only (implementation : QueryImpl spec (StateT S ProbComp))
    (observe : (query : spec.Domain) → spec.Range query → List Log)
    (work : OracleComp spec A) (before : S × List Log) (result : A × (S × List Log))
    (supported : result ∈ support ((simulateQ (recorded implementation observe) work).run before)) :
    ∃ suffix, result.2.2 = before.2 ++ suffix := by
  induction work using OracleComp.inductionOn generalizing before result with
  | pure value =>
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
    cases supported
    exact ⟨[], by simp only [List.append_nil]⟩
  | query_bind query next ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, support_bind, Set.mem_iUnion] at supported
    obtain ⟨middle, called, following⟩ := supported
    simp only [recorded, StateT.run, support_map] at called
    obtain ⟨inner, _called, same⟩ := called
    cases same
    obtain ⟨suffix, kept⟩ := ih inner.1 _ _ following
    exact ⟨observe query inner.1 ++ suffix, kept.trans (List.append_assoc _ _ _)⟩

def signingObservation : (query : RegistrationSigningShared.Spec.Domain) →
    RegistrationSigningShared.Spec.Range query → List Stage
  | .hash request, digest => [.hash request digest]
  | .sign request payload digest, reply => [.sign request payload digest reply]

end BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterSourceTrace

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterSourceTrace.erase' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterSourceTrace.erase
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterSourceTrace.source' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterSourceTrace.source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterSourceTrace.append_only' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterSourceTrace.append_only
