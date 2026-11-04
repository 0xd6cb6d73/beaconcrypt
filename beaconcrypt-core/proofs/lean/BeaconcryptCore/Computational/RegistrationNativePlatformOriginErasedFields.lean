-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRecordFactsPrivateCacheSource
/-! Exact coordinate framing for the named private-cache-erased service, retaining its counter-normalized base implementation and real source effects. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
namespace BeaconcryptCore.Computational.RegistrationNativePlatformOriginErasedFields
open PqxdhRecordLiftIdeal (CtxPrivate KeyMode onBase)
open PqxdhRecordLiftProtocol (Service ServiceSpec)
open PqxdhRecordLiftWorldCompiler (Label)
open PqxdhServerAuthExperiment (Setup Codec)
variable {n : Nat} {I KemSK Reader Response A : Type} {base : OracleSpec I}
variable (modes : Label n → KeyMode) (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : Setup base KemSK) (codec : Codec Reader Response)
local notation "service" => PqxdhRecordFactsPrivateCacheWorld.erased modes replace setup codec

def BaseOnly : Service n → Prop
  | .opening _ | .sealing _=>False
  | _=>True

/-- Each actual erased base service preserves every coordinate, independently of its complete base effects and uniform counter. -/
theorem base_call (request : Service n) (quiet : BaseOnly request)
    (before : CtxPrivate n) (result : (ServiceSpec n).Range request × CtxPrivate n)
    (supported : result∈support ((service request).run before)) : result.2.keys=before.keys := by
  cases request
  all_goals first
    | exact False.elim quiet
    | (simp only [PqxdhRecordFactsPrivateCacheWorld.erased,PqxdhRecordFactsPrivateCacheCompiler.erasedInterpreter,
        QueryImpl.apply_compose,PqxdhRecordFactsPrivateCacheCompiler.compile,simulateQ_spec_query,
        PqxdhRecordFactsPrivateCacheSource.erased_base,onBase,StateT.run,support_map] at supported
       obtain ⟨inner,_called,rfl⟩ := supported
       rfl)

/-- Adaptive continuations of the genuine publication and public-reserve base syntax retain all coordinates exactly. -/
theorem program (work : OracleComp (ServiceSpec n) A) (quiet : work.AllQueriesSatisfy BaseOnly)
    (before : CtxPrivate n) (result : A × CtxPrivate n)
    (supported : result∈support ((simulateQ service work).run before)) : result.2.keys=before.keys := by
  induction work using OracleComp.inductionOn generalizing before result with
  | pure value=>
    simp only [simulateQ_pure,StateT.run_pure,mem_support_pure_iff] at supported
    cases supported
    rfl
  | query_bind request next ih=>
    rw [allQueriesSatisfy_query_bind_iff] at quiet
    rw [simulateQ_bind,simulateQ_spec_query,StateT.run_bind,mem_support_bind_iff] at supported
    obtain ⟨middle,called,continued⟩ := supported
    exact (ih middle.1 (quiet.2 middle.1) middle.2 result continued).trans
      (base_call modes replace setup codec request quiet.1 before middle called)

private theorem bind_apply {S X Y : Type} (work : StateT S ProbComp X) (next : X → StateT S ProbComp Y) (before : S) :
    (work >>= next) before=(work before >>= fun result=>next result.1 result.2) := rfl
private theorem pure_apply {S X : Type} (value : X) (before : S) :
    (pure value : StateT S ProbComp X) before=pure (value,before) := rfl

/-- The erased hidden seal changes only its literal material coordinate; full writer-buffer reinstallation and all base effects remain retained. -/
theorem sealing_other (pending : PqxdhRecordLiftProtocol.Sealing n) (before : CtxPrivate n)
    (result : Option RawCtxSourceSend.Encrypted × CtxPrivate n)
    (supported : result∈support ((service (.sealing pending)).run before))
    (label : Label n) (different : label≠pending.material) : result.2.keys label=before.keys label := by
  change result∈support ((simulateQ (PqxdhRecordFactsPrivateCacheServices.erased modes
    (RawCtxUniversalDecoder.decoder codec.frameRead) setup.source.crypto
    (PqxdhRecordFactsPrivateCacheCompiler.base (PqxdhRecordFactsPrivateCacheWorld.baseInterpreter setup codec)))
    (PqxdhRecordFactsPrivateCacheCompiler.compile codec.frameWrite replace (.sealing pending))).run before) at supported
  rw [PqxdhRecordFactsPrivateCacheSource.erased_sealing,mem_support_bind_iff] at supported
  obtain ⟨middle,called,returned⟩ := supported
  simp only [mem_support_pure_iff] at returned
  cases returned
  simp only [PqxdhRecordLiftIdeal.hiddenSealing,StateT.run] at called
  split at called
  · simp only [simulateQ_bind,simulateQ_spec_query,bind_apply,mem_support_bind_iff] at called
    obtain ⟨sealed,reached,finished⟩ := called
    have kept := PqxdhRecordFactsPrivateCacheSource.erasedKeyed_other modes
      (RawCtxUniversalDecoder.decoder codec.frameRead) setup.source.crypto _ before sealed reached label different
    cases reply : sealed.1 <;> simp only [reply,simulateQ_pure,pure_apply,mem_support_pure_iff] at finished
    all_goals exact finished ▸ kept
  · simp only [simulateQ_pure,pure_apply,mem_support_pure_iff] at called
    exact called ▸ rfl
end BeaconcryptCore.Computational.RegistrationNativePlatformOriginErasedFields

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOriginErasedFields.base_call' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOriginErasedFields.base_call

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOriginErasedFields.program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOriginErasedFields.program

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOriginErasedFields.sealing_other' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOriginErasedFields.sealing_other
