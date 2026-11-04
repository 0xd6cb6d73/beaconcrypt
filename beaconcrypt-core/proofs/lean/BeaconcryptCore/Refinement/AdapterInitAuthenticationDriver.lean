-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.AdapterInitAuthenticationStateful
import BeaconcryptCore.Computational.RegistrationAuthenticationTermination

/-! The lifted actual Init loop runs to its source terminal branch within seven callbacks plus one terminal inspection. The comparison retains its separate Ed parse/open calls and every optional primitive failure, with the complete state of arbitrary preceding calls. -/
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM ControlFlow beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Refinement.AdapterInitAuthenticationDriver
open AdapterInitAuthenticationRequestMonad
open AdapterRecordRequestMonad (liftRust)
open AdapterInitAuthenticationStateful
open BeaconcryptCore.Computational
open RegistrationAuthenticationFlow (Event)
variable [primitive : AdapterInitEdPrimitive.Operations]

def drive : Nat → registration.InitAuthentication → Program (core.option.Option registration.AuthenticatedInit)
  | 0, _ => liftRust .div
  | fuel + 1, state => do
      let decision ← AdapterInitAuthenticationRequestExtraction.body (m := Program) state
      match decision with
      | .cont next => drive fuel next
      | .done result => pure result

def observe : RustM (List Event × registration.InitAuthentication) →
    RustM (core.option.Option registration.AuthenticatedInit)
  | .ok (_, state) => .ok (stateOption state)
  | .fail error => .fail error
  | .div => .div

omit primitive in
private theorem simulate_support {Query Other : Type} {queries : OracleSpec Query} {target : OracleSpec Other}
    {Value : Type} (implementation : QueryImpl queries (OracleComp target)) (work : OracleComp queries Value)
    (value : Value) (supported : value ∈ support (simulateQ implementation work)) : value ∈ support work := by
  induction work using OracleComp.inductionOn with
  | pure input =>
      simp only [simulateQ_pure, support_pure, Set.mem_singleton_iff] at supported ⊢
      exact supported
  | query_bind query next ih =>
      rw [simulateQ_bind, simulateQ_spec_query, mem_support_bind_iff] at supported
      obtain ⟨reply, _queried, continued⟩ := supported
      rw [mem_support_bind_iff]
      exact ⟨reply, mem_support_query query reply, ih reply continued⟩

/-- Sufficient source-derived fuel removes the actual driver's divergence boundary and recovers exactly the maintained callback executor's returned authentication result. -/
theorem drive_source (fuel : Nat) (state : registration.InitAuthentication)
    (enough : RegistrationAuthenticationTermination.rank state < fuel) :
    interpret (drive fuel state) =
      observe <$> simulateQ abstractNative (RegistrationAuthenticationExecutor.execute fuel state) := by
  induction fuel generalizing state with
  | zero => omega
  | succ fuel ih =>
      rw [drive, interpret_bind, body_source, bind_map_left]
      simp only [RegistrationAuthenticationExecutor.execute, simulateQ_bind, map_bind]
      apply OracleComp.bind_congr_of_forall_mem_support
      intro result supported
      cases result with
      | fail error | div =>
          simp only [AdapterInitAuthenticationStateful.control, RegistrationAuthenticationExecutor.continueWith, simulateQ_pure, map_pure, observe]
      | ok option => cases option with
        | none =>
            simp only [AdapterInitAuthenticationStateful.control, interpret_pure, RegistrationAuthenticationExecutor.continueWith,
              simulateQ_pure, map_pure, observe]
        | some next =>
            rcases next with ⟨event, after⟩
            have progress := RegistrationAuthenticationTermination.executable_step
              (simulate_support abstractNative (RegistrationAuthenticationExecutor.step state) _ supported)
            have remaining : RegistrationAuthenticationTermination.rank after < fuel := by omega
            simp only [AdapterInitAuthenticationStateful.control, RegistrationAuthenticationExecutor.continueWith,
              simulateQ_bind, map_bind]
            rw [ih after remaining]
            rw [← bind_pure_comp]
            apply bind_congr
            intro rest
            cases rest <;> simp only [ simulateQ_pure,
              map_pure, observe]

def authenticate (pin : session.ServerAuthenticationPin) (packet : registration.InitPacket) :
    Program (core.option.Option registration.AuthenticatedInit) := do
  let state ← liftRust (registration.begin_init_authentication pin packet)
  drive 8 state

/-- The actual Init entrypoint followed by its complete source loop equals the mandatory native authentication controller; malformed/absent primitive replies and failed Ed parsing remain explicit. -/
theorem source (pin : session.ServerAuthenticationPin) (packet : registration.InitPacket) :
    interpret (authenticate pin packet) =
      observe <$> simulateQ abstractNative (RegistrationAuthenticationExecutor.begin pin packet) := by
  obtain ⟨initial, started, _packet, _pin, _input⟩ := RegistrationAuthentication.begin_init_exact pin packet
  simp only [authenticate, interpret_bind, interpret_lift, started, pure_bind,
    RegistrationAuthenticationExecutor.begin, RegistrationAuthenticationExecutor.continueWith]
  exact drive_source 8 _ (by simpa only [RegistrationAuthenticationTermination.rank] using (by decide : 7 < 8))

/-- The source transformation and complete stateful native execution equality hold together for every actual original implementation and arbitrary reached shared primitive state. -/
theorem stateful {PrimitiveState Index : Type} {base : OracleSpec Index}
    (implementation : QueryImpl NativeSpec (StateT PrimitiveState (OracleComp base)))
    (pin : session.ServerAuthenticationPin) (packet : registration.InitPacket) (before : PrimitiveState) :
    (∀ (ops : beaconcrypt.auth.Operations) (state : registration.InitAuthentication),
      letI : beaconcrypt.auth.Operations := ops
      AdapterInitAuthenticationRequestExtraction.body (m := RustM) state =
        beaconcrypt.auth.authenticate_init_loop.body state) ∧
    (simulateQ implementation (interpret (authenticate pin packet))).run before =
      (simulateQ implementation (observe <$> simulateQ abstractNative
        (RegistrationAuthenticationExecutor.begin pin packet))).run before := by
  exact ⟨fun ops state => @body_specializes primitive ops state,
    congrArg (fun work => (simulateQ implementation work).run before) (source pin packet)⟩

/-- All later API calls consume the same original result and complete shared poststate after the actual source loop. -/
theorem stateful_continuation {PrimitiveState Index Value : Type} {base : OracleSpec Index}
    (implementation : QueryImpl NativeSpec (StateT PrimitiveState (OracleComp base)))
    (pin : session.ServerAuthenticationPin) (packet : registration.InitPacket)
    (later : RustM (core.option.Option registration.AuthenticatedInit) → OracleComp NativeSpec Value)
    (before : PrimitiveState) :
    (simulateQ implementation (do let result ← interpret (authenticate pin packet); later result)).run before =
      (simulateQ implementation (do
        let result ← observe <$> simulateQ abstractNative (RegistrationAuthenticationExecutor.begin pin packet)
        later result)).run before := by
  rw [source]

end BeaconcryptCore.Refinement.AdapterInitAuthenticationDriver
/-- info: 'BeaconcryptCore.Refinement.AdapterInitAuthenticationDriver.drive_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterInitAuthenticationDriver.drive_source
/-- info: 'BeaconcryptCore.Refinement.AdapterInitAuthenticationDriver.source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterInitAuthenticationDriver.source
/-- info: 'BeaconcryptCore.Refinement.AdapterInitAuthenticationDriver.stateful' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterInitAuthenticationDriver.stateful
/-- info: 'BeaconcryptCore.Refinement.AdapterInitAuthenticationDriver.stateful_continuation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterInitAuthenticationDriver.stateful_continuation
