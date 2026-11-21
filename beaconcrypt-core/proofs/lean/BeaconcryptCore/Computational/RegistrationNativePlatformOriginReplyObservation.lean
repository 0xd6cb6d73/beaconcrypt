-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformOriginResumedCallback
import BeaconcryptCore.Computational.RegistrationNativePlatformOriginSendAcquisition
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1800000
namespace BeaconcryptCore.Computational.RegistrationNativePlatformOriginReplyObservation
open PqxdhRecordLiftIdeal (CtxPrivate)
open PqxdhRecordLiftProtocol (ServiceSpec)
open PqxdhRecordLiftWorldCompiler (Label)
open RegistrationNativePlatformOriginReserveContinuationBound (continued)
open PqxdhRecordFactsOriginMuteAdaptive (marked)
variable {n : Nat} {Platform Failure A X : Type}
variable (reserve : Nat → StateT Platform ProbComp (core.result.Result Unit Failure))
    (after : Option RawCtxSourceSend.Encrypted → Platform → A)
    (current : A → Bool) (future : A → OracleComp (ServiceSpec n) X)
    (beforeP : Platform) (tag : PqxdhDeploymentInterface.FrameTag)

/-- Returning the actual callback reply before its same adaptive suffix exposes exactly the real publication/refusal bit. -/
theorem source (form : ∀output reachedP,current (after output reachedP)=output.isNone)
    (reply : Option RawCtxSourceSend.Encrypted) :
    (do let localResult ← continued reserve (fun output reachedP=>pure (after output reachedP)) beforeP tag reply
        let result ← future localResult
        pure (current localResult,result)) =
      continued reserve (fun output reachedP=>(fun result=>(output.isNone,result)) <$>future (after output reachedP)) beforeP tag reply := by
  simp only [continued,bind_assoc,bind_pure_comp,bind_map_left,form]

noncomputable def observation (target : Label n) (decode : AdaptiveCtxReceive.RawDecoder)
    (service : QueryImpl (ServiceSpec n) (StateT (CtxPrivate n) ProbComp))
    (reply : Option RawCtxSourceSend.Encrypted) (before : CtxPrivate n) : ProbComp ((X × CtxPrivate n) × Bool) :=
  (fun result=>((result.1.2,result.2.1),result.1.1 &&result.2.2)) <$>
    (simulateQ (marked target decode service)
      (do let localResult ← continued reserve (fun output reachedP=>pure (after output reachedP)) beforeP tag reply
          let result ←future localResult
          pure (current localResult,result))).run (before,false)

/-- The current public reply is observed before the future runs; the guarded distribution is exactly the existing resumed reserve observation, retaining the same complete private state. -/
theorem resumed (form : ∀output reachedP,current (after output reachedP)=output.isNone)
    (target : Label n) (decode : AdaptiveCtxReceive.RawDecoder)
    (service : QueryImpl (ServiceSpec n) (StateT (CtxPrivate n) ProbComp))
    (reply : Option RawCtxSourceSend.Encrypted) (before : CtxPrivate n) :
    observation reserve after current future beforeP tag target decode service reply before =
      RegistrationNativePlatformOriginResumedCallback.observation reserve
        (fun output reachedP=>future (after output reachedP)) beforeP tag target decode service reply before := by
  unfold observation RegistrationNativePlatformOriginResumedCallback.observation
  rw [source reserve after current future beforeP tag form reply]

/-- The actual strong native send envelope supplies the reply-bit relation without a caller publication law. -/
theorem send (advancedShell : CborRecordWorldClient.Shell) (advancedControl : PqxdhRecordLiftProtocol.Control n)
    (afterSend : Option RawCtxSourceSend.Encrypted → Platform → RegistrationNativePlatformOriginSendAcquisition.SendResult n Platform)
    (exactAfter : ∀output reachedP,afterSend output reachedP=(((output,reachedP),advancedShell),advancedControl))
    (futureSend : RegistrationNativePlatformOriginSendAcquisition.SendResult n Platform → OracleComp (ServiceSpec n) X)
    (target : Label n) (decode : AdaptiveCtxReceive.RawDecoder)
    (service : QueryImpl (ServiceSpec n) (StateT (CtxPrivate n) ProbComp))
    (reply : Option RawCtxSourceSend.Encrypted) (before : CtxPrivate n) :
    observation reserve afterSend (fun result=>result.1.1.1.isNone) futureSend beforeP tag target decode service reply before =
      RegistrationNativePlatformOriginResumedCallback.observation reserve
        (fun output reachedP=>futureSend (afterSend output reachedP)) beforeP tag target decode service reply before := by
  apply resumed
  intro output reachedP
  rw [exactAfter]
end BeaconcryptCore.Computational.RegistrationNativePlatformOriginReplyObservation

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOriginReplyObservation.source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOriginReplyObservation.source


/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOriginReplyObservation.resumed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOriginReplyObservation.resumed


/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOriginReplyObservation.send' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOriginReplyObservation.send
