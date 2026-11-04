-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.AdapterInitAuthenticationRequestExtraction
import BeaconcryptCore.Computational.RegistrationAuthenticationExecutor

/-! The actual source Init closure and loop body specialize exactly to Aeneas. Their stateful free-request interpretation retains the two distinct Ed leaves, including parse error, absent opening, hash failure and every reached primitive poststate. No protocol-security property is supplied by this translation. -/
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM ControlFlow beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Refinement.AdapterInitAuthenticationStateful
open AdapterInitAuthenticationRequestMonad
open AdapterRecordRequestMonad (LiftRust liftRust)
open BeaconcryptCore.Computational
variable [primitive : AdapterInitEdPrimitive.Operations]

/-- The original actual Ed closure is preserved for every concrete primitive implementation. -/
theorem ed_specializes [beaconcrypt.auth.Operations] (closure : beaconcrypt.auth.authenticate_init.closure) :
    AdapterInitAuthenticationRequestExtraction.ed (m := RustM) closure () =
      beaconcrypt.auth.authenticate_init.closure.Insts.CoreOpsFunctionFnTupleOptionVecU8.call closure () := rfl

/-- Every branch is the literal original extracted loop body, including both Ed leaves and the borrowed opened buffer. -/
theorem body_specializes [beaconcrypt.auth.Operations] (state : registration.InitAuthentication) :
    AdapterInitAuthenticationRequestExtraction.body (m := RustM) state =
      beaconcrypt.auth.authenticate_init_loop.body state := by
  cases state <;> rfl

inductive EdRequest where
  | parse (bytes : Slice U8)
  | open (signed : Slice U8) (publicKey : primitive.PublicKey)

abbrev EdSpec : OracleSpec EdRequest
  | .parse _ => core.result.Result primitive.PublicKey primitive.Error
  | .open _ _ => core.option.Option (alloc.vec.Vec U8)

abbrev NativeSpec := RegistrationAuthenticationExecutor.Spec + EdSpec

/-- Parse and attached opening remain two distinct dynamic calls in the actual source order. -/
def native : QueryImpl Spec (OracleComp NativeSpec)
  | .hash request => .ok <$> NativeSpec.query (.inl (.hash request))
  | .verifyMldsa request => .ok <$> NativeSpec.query (.inl (.mldsa request))
  | .parseEd bytes => .ok <$> NativeSpec.query (.inr (.parse bytes))
  | .verifyEd signed publicKey => .ok <$> NativeSpec.query (.inr (.open signed publicKey))

def opened (request : registration.Ed25519VerificationRequest) :
    OracleComp NativeSpec RegistrationAuthenticationFlow.Opened := do
  let parsed ← NativeSpec.query (.inr (.parse (Array.to_slice request.public_key)))
  match parsed with
  | .Err _ => pure .None
  | .Ok key => NativeSpec.query (.inr (.open request.signed key))

/-- The maintained callback executor sees the same source Ed parse/open sequence; hash and ML requests are retained literally. -/
def abstractNative : QueryImpl RegistrationAuthenticationExecutor.Spec (OracleComp NativeSpec)
  | .hash request => NativeSpec.query (.inl (.hash request))
  | .mldsa request => NativeSpec.query (.inl (.mldsa request))
  | .ed25519 request => opened request

def interpret {A : Type} (work : Program A) : OracleComp NativeSpec (RustM A) := simulateQ native work.run

@[simp] theorem interpret_pure {A : Type} (value : A) :
    interpret (pure value) = pure (.ok value) := rfl
@[simp] theorem interpret_lift {A : Type} (value : RustM A) :
    interpret (liftRust value) = pure value := rfl

theorem interpret_bind {A B : Type} (work : Program A) (next : A → Program B) :
    interpret (work >>= next) = (do
      let result ← interpret work
      match result with
      | .ok value => interpret (next value)
      | .fail error => pure (.fail error)
      | .div => pure .div) := by
  unfold interpret
  rw [Program.run_bind, simulateQ_bind]
  apply bind_congr
  intro result
  cases result <;> rfl

/-- Parse failure returns the original absent opening; a parsed key invokes exactly the original attached-signature leaf. -/
theorem ed_source (request : registration.Ed25519VerificationRequest) :
    interpret (AdapterInitAuthenticationRequestExtraction.ed (m := Program) (request.public_key, request.signed) ()) =
      .ok <$> opened request := by
  simp only [AdapterInitAuthenticationRequestExtraction.ed,
    Lifted.toSlice, lift, Lifted.resultOk, Lifted.branch, Lifted.fromResidual, Operations.parseEd,
    Operations.verifyEd, interpret, Program.run_bind, Program.run_lift, Program.query, opened, map_bind,
    pure_bind]
  simp only [simulateQ_bind, simulateQ_spec_query, native, bind_map_left]
  apply bind_congr
  intro parsed
  cases parsed <;> simp only [core.result.Result.ok, core.option.Option.Insts.CoreOpsTry_traitTry.branch,
    core.option.Option.Insts.CoreOpsTry_traitTryTOptionInfallible.branch,
    core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual, Program.run_lift, simulateQ_spec_query, native, map_pure, simulateQ_pure]

def stateOption : registration.InitAuthentication → core.option.Option registration.AuthenticatedInit
  | .Accepted authenticated => .Some authenticated
  | _ => .None

def control (state : registration.InitAuthentication) :
    RustM (Option (RegistrationAuthenticationFlow.Event × registration.InitAuthentication)) →
      RustM (ControlFlow registration.InitAuthentication (core.option.Option registration.AuthenticatedInit))
  | .ok none => .ok (.done (stateOption state))
  | .ok (some (_, next)) => .ok (.cont next)
  | .fail error => .fail error
  | .div => .div

/-- The actual body equals one maintained native callback step, retaining every optional reply, source error and distinct Ed operation. -/
theorem body_source (state : registration.InitAuthentication) :
    interpret (AdapterInitAuthenticationRequestExtraction.body (m := Program) state) =
      control state <$> simulateQ abstractNative (RegistrationAuthenticationExecutor.step state) := by
  cases state with
  | Accepted authenticated | Rejected => rfl
  | HashRequested pending =>
      cases requested : pending.request with
      | fail error | div =>
          simp only [AdapterInitAuthenticationRequestExtraction.body, Lifted.hashRequest, requested,
            interpret_bind, interpret_lift, pure_bind, RegistrationAuthenticationExecutor.step,
            RegistrationAuthenticationExecutor.continueWith, simulateQ_pure, map_pure, control]
      | ok request =>
          simp only [AdapterInitAuthenticationRequestExtraction.body, Lifted.hashRequest, requested, pure_bind, Operations.hash, interpret, Program.run_bind, Program.run_lift, Program.run_pure, Program.query,
            simulateQ_spec_query, native, RegistrationAuthenticationExecutor.step,
            RegistrationAuthenticationExecutor.continueWith, simulateQ_bind, simulateQ_pure,
            abstractNative, bind_map_left, map_bind]
          apply bind_congr
          intro reply
          cases resumed : pending.resume reply <;>
            simp only [Lifted.hashResume, resumed, Program.run_lift,
              simulateQ_pure, pure_bind, map_pure, RegistrationAuthenticationExecutor.edge, control]
  | MldsaVerificationRequested pending =>
      cases requested : pending.request with
      | fail error | div =>
          simp only [AdapterInitAuthenticationRequestExtraction.body, Lifted.mldsaRequest, requested,
            interpret_bind, interpret_lift, pure_bind, RegistrationAuthenticationExecutor.step,
            RegistrationAuthenticationExecutor.continueWith, simulateQ_pure, map_pure, control]
      | ok request =>
          simp only [AdapterInitAuthenticationRequestExtraction.body, Lifted.mldsaRequest, requested, pure_bind, Operations.verifyMldsa, interpret, Program.run_bind, Program.run_lift, Program.run_pure, Program.query,
            simulateQ_spec_query, native, RegistrationAuthenticationExecutor.step,
            RegistrationAuthenticationExecutor.continueWith, simulateQ_bind, simulateQ_pure,
            abstractNative, bind_map_left, map_bind]
          apply bind_congr
          intro reply
          cases resumed : pending.resume reply <;>
            simp only [Lifted.mldsaResume, resumed, Program.run_lift,
              simulateQ_pure, pure_bind, map_pure, RegistrationAuthenticationExecutor.edge, control]
  | Ed25519VerificationRequested pending =>
      cases requested : pending.request with
      | fail error | div =>
          simp only [AdapterInitAuthenticationRequestExtraction.body, Lifted.edRequest, requested,
            interpret_bind, interpret_lift, pure_bind, RegistrationAuthenticationExecutor.step,
            RegistrationAuthenticationExecutor.continueWith, simulateQ_pure, map_pure, control]
      | ok request =>
          simp only [AdapterInitAuthenticationRequestExtraction.body, Lifted.edRequest, requested,
            interpret_bind, interpret_lift, pure_bind, ed_source,
            RegistrationAuthenticationExecutor.step, RegistrationAuthenticationExecutor.continueWith,
            simulateQ_bind, simulateQ_spec_query, simulateQ_pure, abstractNative, bind_map_left, map_bind]
          apply bind_congr
          intro reply
          cases resumed : pending.resume reply <;>
            simp only [Lifted.asDeref, AdapterOptionDeref.byte_vector, Lifted.edResume, resumed, Program.run_lift, Program.run_pure, interpret,
              simulateQ_pure, pure_bind, map_pure, RegistrationAuthenticationExecutor.edge, control]
  | ServerFingerprintRequested pending =>
      cases requested : pending.request with
      | fail error | div =>
          simp only [AdapterInitAuthenticationRequestExtraction.body, Lifted.serverRequest, requested,
            interpret_bind, interpret_lift, pure_bind, RegistrationAuthenticationExecutor.step,
            RegistrationAuthenticationExecutor.continueWith, simulateQ_pure, map_pure, control]
      | ok request =>
          simp only [AdapterInitAuthenticationRequestExtraction.body, Lifted.serverRequest, requested, pure_bind, Operations.hash, interpret, Program.run_bind, Program.run_lift, Program.run_pure, Program.query,
            simulateQ_spec_query, native, RegistrationAuthenticationExecutor.step,
            RegistrationAuthenticationExecutor.continueWith, simulateQ_bind, simulateQ_pure,
            abstractNative, bind_map_left, map_bind]
          apply bind_congr
          intro reply
          cases resumed : pending.resume reply <;>
            simp only [Lifted.serverResume, resumed, Program.run_lift,
              simulateQ_pure, pure_bind, map_pure, RegistrationAuthenticationExecutor.edge, control]
  | BeaconFingerprintRequested pending =>
      cases requested : pending.request with
      | fail error | div =>
          simp only [AdapterInitAuthenticationRequestExtraction.body, Lifted.beaconRequest, requested,
            interpret_bind, interpret_lift, pure_bind, RegistrationAuthenticationExecutor.step,
            RegistrationAuthenticationExecutor.continueWith, simulateQ_pure, map_pure, control]
      | ok request =>
          simp only [AdapterInitAuthenticationRequestExtraction.body, Lifted.beaconRequest, requested, pure_bind, Operations.hash, interpret, Program.run_bind, Program.run_lift, Program.run_pure, Program.query,
            simulateQ_spec_query, native, RegistrationAuthenticationExecutor.step,
            RegistrationAuthenticationExecutor.continueWith, simulateQ_bind, simulateQ_pure,
            abstractNative, bind_map_left, map_bind]
          apply bind_congr
          intro reply
          cases resumed : pending.resume reply <;>
            simp only [Lifted.beaconResume, resumed, Program.run_lift,
              simulateQ_pure, pure_bind, map_pure, RegistrationAuthenticationExecutor.edge, control]

end BeaconcryptCore.Refinement.AdapterInitAuthenticationStateful
/-- info: 'BeaconcryptCore.Refinement.AdapterInitAuthenticationStateful.ed_specializes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterInitAuthenticationStateful.ed_specializes
/-- info: 'BeaconcryptCore.Refinement.AdapterInitAuthenticationStateful.body_specializes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterInitAuthenticationStateful.body_specializes
/-- info: 'BeaconcryptCore.Refinement.AdapterInitAuthenticationStateful.interpret_pure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterInitAuthenticationStateful.interpret_pure
/-- info: 'BeaconcryptCore.Refinement.AdapterInitAuthenticationStateful.interpret_lift' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterInitAuthenticationStateful.interpret_lift
/-- info: 'BeaconcryptCore.Refinement.AdapterInitAuthenticationStateful.interpret_bind' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterInitAuthenticationStateful.interpret_bind
/-- info: 'BeaconcryptCore.Refinement.AdapterInitAuthenticationStateful.ed_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterInitAuthenticationStateful.ed_source
/-- info: 'BeaconcryptCore.Refinement.AdapterInitAuthenticationStateful.body_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterInitAuthenticationStateful.body_source
