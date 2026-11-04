-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRecordFactsPrivateCacheWorld
open OracleComp OracleSpec CoreModels
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
namespace BeaconcryptCore.Computational.RegistrationNativePlatformOriginPublicNormalization
open PqxdhRecordLiftWorldCompiler (Label)
open PqxdhRecordLiftIdeal (KeyMode CtxPrivate ctxInterpreter)
open PqxdhRecordLiftProtocol (ServiceSpec)
open PqxdhServerAuthExperiment (Setup Codec)
variable {n : Nat} {I KemSK Reader Response Result : Type} {base : OracleSpec I}
variable (modes : Label n → KeyMode) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (setup : Setup base KemSK) (codec : Codec Reader Response)
    (supported : ∀label,modes label≠.real)
    (client : OracleComp (ServiceSpec n) Result) (before : CtxPrivate n)

include supported in
/-- The complete public result has the same evaluated law under actual CTX and the named discarded-cache interpreter. No counter, cache or private-state equality is asserted. -/
theorem value : LazyOracleDiscard.LawEq
    (Prod.fst <$> (simulateQ (ctxInterpreter modes replace setup codec) client).run before)
    (Prod.fst <$> (simulateQ (PqxdhRecordFactsPrivateCacheWorld.erased modes replace setup codec) client).run
      (PqxdhRecordFactsCounter.zeroCtx before)) := by
  have same := (PqxdhRecordFactsPrivateCacheWorld.program_observation modes replace setup codec supported client before).map Prod.fst
  simpa only [Functor.map_map,Prod.map_def,id_eq,id_map'] using same

include supported in
/-- Every original public-result event, including a ledger-only origin decision, keeps exactly its actual probability after normalization at an arbitrary reached private state. -/
theorem event (predicate : Result → Prop) :
    Pr{let result ← (simulateQ (ctxInterpreter modes replace setup codec) client).run before}[predicate result.1] =
    Pr{let result ← (simulateQ (PqxdhRecordFactsPrivateCacheWorld.erased modes replace setup codec) client).run (PqxdhRecordFactsCounter.zeroCtx before)}[predicate result.1] := by
  let : MeasurableSpace Result := ⊤
  have same := value modes replace setup codec supported client before Result (fun result=>pure result)
  simp only [bind_pure] at same
  have equal := (EvalDistEq.of_evalDist_eq same) predicate
  simpa only [prEvent_map] using equal
end BeaconcryptCore.Computational.RegistrationNativePlatformOriginPublicNormalization
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOriginPublicNormalization.value' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOriginPublicNormalization.value
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOriginPublicNormalization.event' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOriginPublicNormalization.event
