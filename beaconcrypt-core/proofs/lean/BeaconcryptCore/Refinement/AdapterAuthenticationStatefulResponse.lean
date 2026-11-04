-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.AdapterAuthenticationRequestExtraction
import BeaconcryptCore.Computational.RegistrationResponseExecutor

/-! The source-extracted response-authentication body is lifted without replacing its control flow. Exact free-request equality transfers through arbitrary shared stateful primitive implementations and later callbacks. Hash and ML-verification security and implementation contracts remain assumed; no security conclusion is an input. -/

open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core

set_option autoImplicit false
set_option warningAsError true

namespace BeaconcryptCore.Refinement.AdapterAuthenticationStatefulResponse
open AdapterAuthenticationRequestMonad
open AdapterRecordRequestMonad (LiftRust liftRust)
open BeaconcryptCore.Computational

/-- Every original primitive implementation specializes to the actual extracted body, including failure and divergence. -/
theorem controller_specializes [beaconcrypt.auth.Operations]
    (pending : registration.BeaconPending) (packet : Option registration.ResponsePacket) :
    AdapterAuthenticationRequestExtraction.authenticate (m := RustM) pending packet =
      beaconcrypt.auth.authenticate_response pending packet := by
  rfl

/-- These are the same concrete hash and verifier requests already used by the native executor. -/
def native : QueryImpl Spec (OracleComp RegistrationAuthenticationExecutor.Spec)
  | .hash request => .ok <$>
      (RegistrationAuthenticationExecutor.Spec.query (.hash request) :
        OracleComp RegistrationAuthenticationExecutor.Spec (Option (Array Std.U8 64#usize)))
  | .verify request => .ok <$>
      (RegistrationAuthenticationExecutor.Spec.query (.mldsa request) :
        OracleComp RegistrationAuthenticationExecutor.Spec Bool)

def authenticate (pending : registration.BeaconPending) (packet : Option registration.ResponsePacket) :
    OracleComp RegistrationAuthenticationExecutor.Spec (RustM RegistrationResponseExecutor.ResponseResult) :=
  simulateQ native (AdapterAuthenticationRequestExtraction.authenticate (m := Program) pending packet).run

/-- Exact correspondence covers every optional response packet, hash failure, verifier verdict and complete authenticated/aborted result. -/
theorem source (pending : registration.BeaconPending) (packet : Option registration.ResponsePacket) :
    authenticate pending packet = RegistrationResponseExecutor.begin pending packet := by
  cases packet with
  | none => rfl
  | some packet =>
      obtain ⟨stage, admitted, samePending, samePacket, parts, requested, bytes⟩ :=
        RegistrationResponse.begin_response_some_exact pending packet
      simp only [authenticate, AdapterAuthenticationRequestExtraction.authenticate,
        Lifted.begin, Lifted.branch, Lifted.hashRequest, Lifted.hashResume,
        Lifted.verifyRequest, Lifted.verifyResume, Lifted.fromResidual, Operations.hash,
        Operations.verify, Program.run_bind, Program.run_lift,
        Program.query, admitted, requested, simulateQ_bind, simulateQ_spec_query,
        pure_bind, core.result.Result.Insts.CoreOpsTry_traitTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitTryTResultInfallibleE.branch,
        RegistrationResponseExecutor.begin, RegistrationResponseExecutor.continueResult,
        RegistrationAuthenticationExecutor.continueWith]
      simp only [native, bind_map_left]
      refine bind_congr fun digest => ?_
      cases digest with
      | none =>
          simp only [(RegistrationResponse.malformed_and_hash_failure_exact pending stage).2,
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResultInfallibleE.from_residual,
            core.convert.From.Blanket.from, bind_tc_ok, Program.run_lift, simulateQ_pure]
      | some digest =>
          obtain ⟨verification, resumed, _, _, request, requestRun, _⟩ :=
            RegistrationResponse.response_hash_some_exact stage digest
          simp only [resumed, requestRun, Program.run_bind, Program.run_lift,
            simulateQ_bind, simulateQ_spec_query, pure_bind, native, bind_map_left,
            simulateQ_pure]

/-- The checked transformation retains both its actual-source specialization and its free-request correspondence. -/
theorem source_certificate (pending : registration.BeaconPending)
    (packet : Option registration.ResponsePacket) :
    (∀ (ops : beaconcrypt.auth.Operations),
      letI : beaconcrypt.auth.Operations := ops
      AdapterAuthenticationRequestExtraction.authenticate (m := RustM) pending packet =
        beaconcrypt.auth.authenticate_response pending packet) ∧
    authenticate pending packet = RegistrationResponseExecutor.begin pending packet := by
  exact ⟨fun ops => @controller_specializes ops pending packet, source pending packet⟩

/-- The joint returned authentication state and full primitive state are preserved for arbitrary prior histories. -/
theorem stateful {PrimitiveState ι : Type} {base : OracleSpec ι}
    (impl : QueryImpl RegistrationAuthenticationExecutor.Spec
      (StateT PrimitiveState (OracleComp base)))
    (pending : registration.BeaconPending) (packet : Option registration.ResponsePacket)
    (before : PrimitiveState) :
    (simulateQ impl (authenticate pending packet)).run before =
      (simulateQ impl (RegistrationResponseExecutor.begin pending packet)).run before := by
  exact congrArg (fun work => (simulateQ impl work).run before)
    (source_certificate pending packet).2

/-- Later callbacks consume exactly the same result and shared primitive poststate, including after hash rejection. -/
theorem stateful_continuation {PrimitiveState ι Output : Type} {base : OracleSpec ι}
    (impl : QueryImpl RegistrationAuthenticationExecutor.Spec
      (StateT PrimitiveState (OracleComp base)))
    (pending : registration.BeaconPending) (packet : Option registration.ResponsePacket)
    (later : RustM RegistrationResponseExecutor.ResponseResult →
      OracleComp RegistrationAuthenticationExecutor.Spec Output) (before : PrimitiveState) :
    (simulateQ impl (do let result ← authenticate pending packet; later result)).run before =
      (simulateQ impl (do let result ← RegistrationResponseExecutor.begin pending packet; later result)).run before := by
  simp only [simulateQ_bind, StateT.run_bind]
  rw [stateful]

end BeaconcryptCore.Refinement.AdapterAuthenticationStatefulResponse

/-- info: 'BeaconcryptCore.Refinement.AdapterAuthenticationStatefulResponse.controller_specializes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterAuthenticationStatefulResponse.controller_specializes

/-- info: 'BeaconcryptCore.Refinement.AdapterAuthenticationStatefulResponse.source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterAuthenticationStatefulResponse.source

/-- info: 'BeaconcryptCore.Refinement.AdapterAuthenticationStatefulResponse.source_certificate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterAuthenticationStatefulResponse.source_certificate

/-- info: 'BeaconcryptCore.Refinement.AdapterAuthenticationStatefulResponse.stateful' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterAuthenticationStatefulResponse.stateful

/-- info: 'BeaconcryptCore.Refinement.AdapterAuthenticationStatefulResponse.stateful_continuation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterAuthenticationStatefulResponse.stateful_continuation
