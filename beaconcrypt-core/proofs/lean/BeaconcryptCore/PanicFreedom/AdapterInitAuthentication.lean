-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.PanicFreedom.AdapterResponseAuthentication
import BeaconcryptCore.PanicFreedom.Registration
import BeaconcryptCore.PanicFreedom.AdapterNormal
import BeaconcryptCore.Refinement.AdapterInitAuthenticationSourceLoop

/-! Direct normal returns for the extracted Init controller, with the source-derived four-callback rank. Invalid public keys, absent hashes/openings and false verification remain ordinary replies. -/
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM ControlFlow beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.PanicFreedom.AdapterInitAuthentication
variable [operations : beaconcrypt.auth.Operations]
variable [primitive : Refinement.AdapterInitEdPrimitive.Operations]

structure Contracts : Prop where
  hash : ∀ request, ∃ result, operations.hash request = ok result
  parse : ∀ input, ∃ result, primitive.parse input = ok result
  edVerify : ∀ signed key, ∃ result, primitive.verify signed key = ok result

theorem closure_call_total (contracts : Contracts) (c : beaconcrypt.auth.authenticate_init.closure)
    (args : Unit) :
    ∃ result, beaconcrypt.auth.authenticate_init.closure.Insts.CoreOpsFunctionFnTupleOptionVecU8.call c args = ok result := by
  rcases c with ⟨keyBytes, signed⟩
  obtain ⟨parsed, parsedRun⟩ := contracts.parse (Std.Array.to_slice keyBytes)
  cases parsed with
  | Err error =>
    exact ⟨.None, by simp [beaconcrypt.auth.authenticate_init.closure.Insts.CoreOpsFunctionFnTupleOptionVecU8.call, beaconcrypt_crypto.crypto_sign.PublicKey.from_bytes, lift, parsedRun, core.result.Result.ok,
      core.option.Option.Insts.CoreOpsTry_traitTry.branch,
      core.option.Option.Insts.CoreOpsTry_traitTryTOptionInfallible.branch,
      core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual]⟩
  | Ok key =>
    simpa [beaconcrypt.auth.authenticate_init.closure.Insts.CoreOpsFunctionFnTupleOptionVecU8.call,
      beaconcrypt_crypto.crypto_sign.PublicKey.from_bytes, lift, parsedRun, bind_tc_ok,
      core.result.Result.ok, core.option.Option.Insts.CoreOpsTry_traitTry.branch,
      core.option.Option.Insts.CoreOpsTry_traitTryTOptionInfallible.branch,
      beaconcrypt_crypto.crypto_sign.verify] using contracts.edVerify signed key

theorem closure_call_mut_total (contracts : Contracts) (state : beaconcrypt.auth.authenticate_init.closure)
    (args : Unit) :
    ∃ result, beaconcrypt.auth.authenticate_init.closure.Insts.CoreOpsFunctionFnMutTupleOptionVecU8.call_mut state args = ok result := by
  exact (closure_call_total contracts state ()).elim fun result returned =>
    ⟨(result, state), by simp only [beaconcrypt.auth.authenticate_init.closure.Insts.CoreOpsFunctionFnMutTupleOptionVecU8.call_mut,
      returned, bind_tc_ok]⟩

theorem closure_call_once_total (contracts : Contracts) (c : beaconcrypt.auth.authenticate_init.closure)
    (args : Unit) :
    ∃ result, beaconcrypt.auth.authenticate_init.closure.Insts.CoreOpsFunctionFnOnceTupleOptionVecU8.call_once c args = ok result := by
  exact (closure_call_mut_total contracts c ()).elim fun result returned =>
    ⟨result.1, by cases result; simp [beaconcrypt.auth.authenticate_init.closure.Insts.CoreOpsFunctionFnOnceTupleOptionVecU8.call_once,
      returned, bind_tc_ok]⟩

theorem authenticate_init_loop_body_total (contracts : Contracts) (effect : registration.InitAuthentication) :
    ∃ result, beaconcrypt.auth.authenticate_init_loop.body effect = ok result := by
  cases effect with
  | HashRequested pending =>
    exact (RegistrationTrivial.InitHash_request_total pending).elim fun request requested =>
      (contracts.hash request).elim fun reply replied =>
      (Registration.InitHash_resume_total pending reply).elim fun next resumed =>
      ⟨.cont next, by simp only [beaconcrypt.auth.authenticate_init_loop.body, requested,
        beaconcrypt.auth.execute_hash, replied, resumed, bind_tc_ok]⟩
  | Ed25519VerificationRequested pending =>
    exact (Registration.InitEd25519Verification_request_total pending).elim fun request requested =>
      (closure_call_total contracts (request.public_key, request.signed) ()).elim fun opened openedRun =>
      (Registration.InitEd25519Verification_resume_total pending opened).elim fun next resumed =>
      ⟨.cont next, by simp! only [beaconcrypt.auth.authenticate_init_loop.body, requested,
        openedRun, Refinement.AdapterOptionDeref.byte_vector, resumed, bind_tc_ok]⟩
  | Accepted authenticated => exact ⟨_, rfl⟩
  | Rejected => exact ⟨_, rfl⟩

/-- The actual unbounded source loop terminates because every continued callback consumes the source rank; primitive failure values may stop it earlier. -/
theorem authenticate_init_loop_total (contracts : Contracts) (effect : registration.InitAuthentication) :
    ∃ result, beaconcrypt.auth.authenticate_init_loop effect = ok result := by
  exact AdapterNormal.normal_loop beaconcrypt.auth.authenticate_init_loop.body
    Computational.RegistrationAuthenticationTermination.rank
    (authenticate_init_loop_body_total contracts)
    Refinement.AdapterInitAuthenticationSourceLoop.body_progress effect

theorem authenticate_init_total (contracts : Contracts) (pin : session.ServerAuthenticationPin)
    (packet : registration.InitPacket) :
    ∃ result, beaconcrypt.auth.authenticate_init pin packet = ok result := by
  exact AdapterNormal.normal_bind (registration.begin_init_authentication pin packet)
    beaconcrypt.auth.authenticate_init_loop (Registration.begin_init_authentication_total pin packet)
    (authenticate_init_loop_total contracts)

end BeaconcryptCore.PanicFreedom.AdapterInitAuthentication
