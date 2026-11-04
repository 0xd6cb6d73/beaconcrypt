-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.AdapterInitAuthenticationDriver
import BeaconcryptCore.Computational.RegistrationAuthenticationTermination

/-! The actual Aeneas Init loop equals its finite source-body driver for every concrete primitive implementation. Source RustM errors, divergence, parse errors and absent primitive replies are retained; a continued source iteration must reduce the actual seven-callback rank. -/
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM ControlFlow beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Refinement.AdapterInitAuthenticationSourceLoop
open AdapterInitAuthenticationRequestMonad
open AdapterRecordRequestMonad (LiftRust liftRust)
open BeaconcryptCore.Computational
open RegistrationAuthenticationFlow (Event Step)

private theorem callback_progress {Request Reply : Type} (before after : registration.InitAuthentication)
    (request : RustM Request) (respond : Request → RustM Reply)
    (resume : Reply → RustM registration.InitAuthentication) (event : Reply → Event)
    (step : ∀ reply next, resume reply = .ok next → Step before (event reply) next)
    (actual : (do
      let selected ← request
      let reply ← respond selected
      let next ← resume reply
      .ok (.cont next : ControlFlow registration.InitAuthentication (core.option.Option registration.AuthenticatedInit))) =
        .ok (.cont after)) :
    RegistrationAuthenticationTermination.rank after < RegistrationAuthenticationTermination.rank before := by
  cases requested : request with
  | fail error | div => simp only [requested] at actual; cases actual
  | ok selected =>
      simp only [requested, bind_tc_ok] at actual
      cases replied : respond selected with
      | fail error | div => simp only [replied] at actual; cases actual
      | ok reply =>
          simp only [replied, bind_tc_ok] at actual
          cases resumed : resume reply with
          | fail error | div => simp only [resumed] at actual; cases actual
          | ok next =>
              simp only [resumed, bind_tc_ok] at actual
              have same : next = after := ControlFlow.cont.inj (RustM.ok.inj actual)
              subst next
              exact RegistrationAuthenticationTermination.step_progress (step reply after resumed)

/-- A continued actual Rust source iteration has a genuine core continuation and strictly fewer remaining callbacks, without any primitive-success condition. -/
theorem body_progress [primitive : AdapterInitEdPrimitive.Operations] [beaconcrypt.auth.Operations]
    (before after : registration.InitAuthentication)
    (actual : beaconcrypt.auth.authenticate_init_loop.body before = .ok (.cont after)) :
    RegistrationAuthenticationTermination.rank after < RegistrationAuthenticationTermination.rank before := by
  cases before with
  | HashRequested pending =>
      exact callback_progress _ after pending.request beaconcrypt.auth.execute_hash pending.resume Event.hash
        (fun reply next resumed => .hash pending reply next resumed) actual
  | MldsaVerificationRequested pending =>
      exact callback_progress _ after pending.request beaconcrypt.auth.verify_requested pending.resume Event.mldsa
        (fun reply next resumed => .mldsa pending reply next resumed) actual
  | Ed25519VerificationRequested pending =>
      exact callback_progress _ after pending.request (fun request => do
        let opened ← beaconcrypt.auth.authenticate_init.closure.Insts.CoreOpsFunctionFnTupleOptionVecU8.call
          (request.public_key, request.signed) ()
        core.option.Option.as_deref (alloc.vec.Vec.Insts.CoreOpsDerefDerefSlice U8) opened)
        pending.resume (Event.ed25519 pending.stage)
        (fun reply next resumed => .ed25519 pending reply next resumed)
        (by simpa only [beaconcrypt.auth.authenticate_init_loop.body, bind_assoc_eq] using actual)
  | ServerFingerprintRequested pending =>
      exact callback_progress _ after pending.request beaconcrypt.auth.execute_hash pending.resume Event.serverFingerprint
        (fun reply next resumed => .serverFingerprint pending reply next resumed) actual
  | BeaconFingerprintRequested pending =>
      exact callback_progress _ after pending.request beaconcrypt.auth.execute_hash pending.resume Event.beaconFingerprint
        (fun reply next resumed => .beaconFingerprint pending reply next resumed) actual
  | Accepted authenticated | Rejected => cases actual

variable [primitive : AdapterInitEdPrimitive.Operations]

def drive {m : Type → Type} [Monad m] [LiftRust m] [Operations m] :
    Nat → registration.InitAuthentication → m (core.option.Option registration.AuthenticatedInit)
  | 0, _ => liftRust .div
  | fuel + 1, state => do
      let decision ← AdapterInitAuthenticationRequestExtraction.body (m := m) state
      match decision with
      | .cont next => drive fuel next
      | .done result => pure result

/-- The lifted source loop, specialized back to RustM, equals the actual original unbounded Aeneas loop for every source primitive implementation. -/
theorem loop_specializes [beaconcrypt.auth.Operations] (fuel : Nat) (state : registration.InitAuthentication)
    (enough : RegistrationAuthenticationTermination.rank state < fuel) :
    drive (m := RustM) fuel state = beaconcrypt.auth.authenticate_init_loop state := by
  induction fuel generalizing state with
  | zero => omega
  | succ fuel ih =>
      rw [drive, AdapterInitAuthenticationStateful.body_specializes,
        beaconcrypt.auth.authenticate_init_loop, loop.eq_def]
      cases actual : beaconcrypt.auth.authenticate_init_loop.body state with
      | fail error | div => rfl
      | ok decision => cases decision with
        | done result => rfl
        | cont next =>
            have progress := body_progress state next actual
            change drive (m := RustM) fuel next = loop beaconcrypt.auth.authenticate_init_loop.body next
            exact ih next (by omega)

def authenticate {m : Type → Type} [Monad m] [LiftRust m] [Operations m]
    (pin : session.ServerAuthenticationPin) (packet : registration.InitPacket) :
    m (core.option.Option registration.AuthenticatedInit) := do
  let state ← liftRust (registration.begin_init_authentication pin packet)
  drive 8 state

/-- The complete lifted Init entrypoint specializes to the exact original Rust controller, including all optional failures and source errors. -/
theorem specializes [beaconcrypt.auth.Operations] (pin : session.ServerAuthenticationPin) (packet : registration.InitPacket) :
    authenticate (m := RustM) pin packet = beaconcrypt.auth.authenticate_init pin packet := by
  obtain ⟨initial, started, _packet, _pin, _input⟩ := RegistrationAuthentication.begin_init_exact pin packet
  simp only [authenticate, beaconcrypt.auth.authenticate_init, started, liftRust, bind_tc_ok]
  exact loop_specializes 8 _ (by simpa only [RegistrationAuthenticationTermination.rank] using (by decide : 7 < 8))

/-- The generic source driver is the same free Program used by the checked native controller bridge. -/
theorem program_drive (fuel : Nat) (state : registration.InitAuthentication) :
    drive (m := Program) fuel state = AdapterInitAuthenticationDriver.drive fuel state := by
  induction fuel generalizing state with
  | zero => rfl
  | succ fuel ih =>
      simp only [drive, AdapterInitAuthenticationDriver.drive]
      congr 1
      funext decision
      cases decision with
      | done result => rfl
      | cont next => exact ih next

/-- Actual entrypoint lifting is exactly the native bridge's free program. -/
theorem program_authenticate (pin : session.ServerAuthenticationPin) (packet : registration.InitPacket) :
    authenticate (m := Program) pin packet = AdapterInitAuthenticationDriver.authenticate pin packet := by
  rfl

/-- The full original Rust-loop specialization and the full native stateful equality are certified together, including distinct Ed leaves and all optional failures. -/
theorem stateful {PrimitiveState Index : Type} {base : OracleSpec Index}
    (implementation : QueryImpl AdapterInitAuthenticationStateful.NativeSpec
      (StateT PrimitiveState (OracleComp base)))
    (pin : session.ServerAuthenticationPin) (packet : registration.InitPacket) (before : PrimitiveState) :
    (∀ (ops : beaconcrypt.auth.Operations),
      letI : beaconcrypt.auth.Operations := ops
      authenticate (m := RustM) pin packet = beaconcrypt.auth.authenticate_init pin packet) ∧
    (simulateQ implementation
      (AdapterInitAuthenticationStateful.interpret (authenticate (m := Program) pin packet))).run before =
      (simulateQ implementation (AdapterInitAuthenticationDriver.observe <$>
        simulateQ AdapterInitAuthenticationStateful.abstractNative
          (RegistrationAuthenticationExecutor.begin pin packet))).run before := by
  constructor
  · intro ops
    exact @specializes primitive ops pin packet
  · rw [program_authenticate, AdapterInitAuthenticationDriver.source]

/-- Arbitrary later callbacks consume the same returned source authentication and complete shared primitive state. -/
theorem stateful_continuation {PrimitiveState Index Value : Type} {base : OracleSpec Index}
    (implementation : QueryImpl AdapterInitAuthenticationStateful.NativeSpec
      (StateT PrimitiveState (OracleComp base)))
    (pin : session.ServerAuthenticationPin) (packet : registration.InitPacket)
    (later : RustM (core.option.Option registration.AuthenticatedInit) →
      OracleComp AdapterInitAuthenticationStateful.NativeSpec Value) (before : PrimitiveState) :
    (simulateQ implementation (do
      let result ← AdapterInitAuthenticationStateful.interpret (authenticate (m := Program) pin packet)
      later result)).run before =
      (simulateQ implementation (do
        let result ← AdapterInitAuthenticationDriver.observe <$>
          simulateQ AdapterInitAuthenticationStateful.abstractNative (RegistrationAuthenticationExecutor.begin pin packet)
        later result)).run before := by
  rw [program_authenticate, AdapterInitAuthenticationDriver.source]

end BeaconcryptCore.Refinement.AdapterInitAuthenticationSourceLoop
/-- info: 'BeaconcryptCore.Refinement.AdapterInitAuthenticationSourceLoop.body_progress' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterInitAuthenticationSourceLoop.body_progress
/-- info: 'BeaconcryptCore.Refinement.AdapterInitAuthenticationSourceLoop.loop_specializes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterInitAuthenticationSourceLoop.loop_specializes
/-- info: 'BeaconcryptCore.Refinement.AdapterInitAuthenticationSourceLoop.specializes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterInitAuthenticationSourceLoop.specializes

/-- info: 'BeaconcryptCore.Refinement.AdapterInitAuthenticationSourceLoop.program_drive' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterInitAuthenticationSourceLoop.program_drive

/-- info: 'BeaconcryptCore.Refinement.AdapterInitAuthenticationSourceLoop.program_authenticate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterInitAuthenticationSourceLoop.program_authenticate

/-- info: 'BeaconcryptCore.Refinement.AdapterInitAuthenticationSourceLoop.stateful' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterInitAuthenticationSourceLoop.stateful

/-- info: 'BeaconcryptCore.Refinement.AdapterInitAuthenticationSourceLoop.stateful_continuation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterInitAuthenticationSourceLoop.stateful_continuation
