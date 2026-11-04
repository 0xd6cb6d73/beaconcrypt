-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformSourceCompletion

/-! The Server SDK retains its literal moved-token, pin lookup, preflight, occupancy, reservation and commitment stages while accepting an effectful first-record completion. Pin computation and reservations execute at each reached call and retain their poststates, including failures. The stored-pin specialization recovers the existing logical native SDK; recomputing the actual source pin is an additive callback rather than a claimed equality of complete Worlds. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformCompletionSdk
open RegistrationServerFrontendCompiler (State)
open RegistrationServerRootCompiler (Local)
open PqxdhServerAuthExperiment (Setup Codec)
variable {n : Nat} {Encoded Value ι KemSK Reader Response : Type} {base : OracleSpec ι}
variable {m : Type → Type} [Monad m]

abbrev Completion (n : Nat) (m : Type → Type) [Monad m] (Encoded : Type) :=
  pqxdh.ServerState → registration.ServerInitialKdf →
    StateT (Local n) m (RustM (RegistrationWorldServerCompletion.Result Encoded))

def fromInitial (finish : Completion n m Encoded)
    (control : pqxdh.ServerState) (pending : registration.ServerInitialKdf) :
    StateT (State n) m (RustM (Option (U64 × Encoded))) := do
  let published ← RegistrationNativePlatformServerSdk.world (finish control pending)
  RegistrationNativePlatformServerSdk.commit published

def afterOccupancy (reserve : StateT (State n) m Bool) (finish : Completion n m Encoded)
    (control : pqxdh.ServerState) (lookup : peer.CompletionLookup) (occupied : Bool) :
    StateT (State n) m (RustM (Option (U64 × Encoded))) :=
  match lookup.resume occupied with
  | .fail error => pure (.fail error)
  | .div => pure .div
  | .ok (.Err _) => pure (.ok none)
  | .ok (.Ok pending) => do
      let admitted ← reserve
      if admitted then fromInitial finish control pending else pure (.ok none)

def afterPin (reserve : StateT (State n) m Bool) (present : U64 → StateT (State n) m Bool)
    (finish : Completion n m Encoded) (control : pqxdh.ServerState)
    (token : peer.ConsumedRegistration) (application : Slice U8)
    (result : RustM (core.option.Option session.ServerAuthenticationPin)) :
    StateT (State n) m (RustM (Option (U64 × Encoded))) :=
  match result with
  | .fail error => pure (.fail error)
  | .div => pure .div
  | .ok .None => pure (.ok none)
  | .ok (.Some pin) => match peer.begin_completion_lookup control pin token application with
    | .fail error => pure (.fail error)
    | .div => pure .div
    | .ok (.Err _) => pure (.ok none)
    | .ok (.Ok lookup) => match lookup.request with
      | .fail error => pure (.fail error)
      | .div => pure .div
      | .ok keyId => if RegistrationServerSdkSource.preflight application keyId then do
          let occupied ← present keyId
          afterOccupancy reserve finish control lookup occupied
        else pure (.ok none)

def complete (pin : StateT (State n) m (RustM (core.option.Option session.ServerAuthenticationPin)))
    (reserve : StateT (State n) m Bool) (present : U64 → StateT (State n) m Bool)
    (finish : Completion n m Encoded) (token : peer.ConsumedRegistration) (application : Slice U8) :
    StateT (State n) m (RustM (Option (U64 × Encoded))) := do
  let before ← get
  let current ← pin
  afterPin reserve present finish before.control token application current

def build (pin : StateT (State n) m (RustM (core.option.Option session.ServerAuthenticationPin)))
    (reserve : StateT (State n) m Bool) (present : U64 → StateT (State n) m Bool)
    (finish : Completion n m Encoded) (handle : Nat) (application : Option (Slice U8)) :
    StateT (State n) m (RustM (Option (U64 × Encoded))) := fun before =>
  match RegistrationServerSdkSource.take handle before with
  | (none, current) => pure (.ok none, current)
  | (some token, current) => match application with
    | none => pure (.ok none, current)
    | some application => (complete pin reserve present finish token application).run current

def storedPin : StateT (State n) m (RustM (core.option.Option session.ServerAuthenticationPin)) :=
  fun before => pure (.ok (.Some before.pin), before)

noncomputable def nativePresent (coins : QueryImpl unifSpec m) (keyId : U64) : StateT (State n) m Bool :=
  RegistrationNativePlatformServerSdk.world (RegistrationNativePlatformServerCompletion.capability coins (.peerPresent keyId))

noncomputable def nativeFinish (coins : QueryImpl unifSpec m) (setup : Setup base KemSK) (codec : Codec Reader Response)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (encode : registration.SignedResponseView → StateT (Local n) m (RustM (core.option.Option Encoded))) :
    Completion n m Encoded := RegistrationNativePlatformServerCompletion.fromInitial coins setup codec sign encode

theorem fromInitial_native (coins : QueryImpl unifSpec m) (setup : Setup base KemSK) (codec : Codec Reader Response)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (encode : registration.SignedResponseView → StateT (Local n) m (RustM (core.option.Option Encoded)))
    (control : pqxdh.ServerState) (pending : registration.ServerInitialKdf) :
    fromInitial (nativeFinish coins setup codec sign encode) control pending =
      RegistrationNativePlatformServerSdk.fromInitial coins setup codec sign encode control pending := rfl

theorem afterOccupancy_native (coins : QueryImpl unifSpec m) (setup : Setup base KemSK) (codec : Codec Reader Response)
    (reserve : StateT (State n) m Bool)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (encode : registration.SignedResponseView → StateT (Local n) m (RustM (core.option.Option Encoded)))
    (control : pqxdh.ServerState) (lookup : peer.CompletionLookup) (occupied : Bool) :
    afterOccupancy reserve (nativeFinish coins setup codec sign encode) control lookup occupied =
      RegistrationNativePlatformServerSdk.afterOccupancy coins setup codec reserve sign encode control lookup occupied := rfl

variable [LawfulMonad m]

theorem complete_native (coins : QueryImpl unifSpec m) (setup : Setup base KemSK) (codec : Codec Reader Response)
    (reserve : StateT (State n) m Bool)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (encode : registration.SignedResponseView → StateT (Local n) m (RustM (core.option.Option Encoded)))
    (token : peer.ConsumedRegistration) (application : Slice U8) :
    complete storedPin reserve (nativePresent coins) (nativeFinish coins setup codec sign encode) token application =
      RegistrationNativePlatformServerSdk.complete coins setup codec reserve sign encode token application := by
  funext before
  change (complete storedPin reserve (nativePresent coins) (nativeFinish coins setup codec sign encode)
    token application).run before =
      (RegistrationNativePlatformServerSdk.complete coins setup codec reserve sign encode token application).run before
  simp only [complete, StateT.run_bind, StateT.run_get, pure_bind]
  have pinRun : (storedPin : StateT (State n) m _).run before = pure (.ok (.Some before.pin), before) := rfl
  rw [pinRun, pure_bind]
  unfold afterPin RegistrationNativePlatformServerSdk.complete StateT.run
  cases peer.begin_completion_lookup before.control before.pin token application with
  | fail error => rfl
  | div => rfl
  | ok result =>
      cases result with
      | Err previous => rfl
      | Ok lookup =>
          dsimp only
          cases lookup.request with
          | fail error => rfl
          | div => rfl
          | ok keyId =>
              dsimp only
              split
              · rfl
              · rfl

theorem build_native (coins : QueryImpl unifSpec m) (setup : Setup base KemSK) (codec : Codec Reader Response)
    (reserve : StateT (State n) m Bool)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (encode : registration.SignedResponseView → StateT (Local n) m (RustM (core.option.Option Encoded)))
    (handle : Nat) (application : Option (Slice U8)) :
    build storedPin reserve (nativePresent coins) (nativeFinish coins setup codec sign encode) handle application =
      RegistrationNativePlatformServerSdk.build coins setup codec reserve sign encode handle application := by
  funext before
  unfold build RegistrationNativePlatformServerSdk.build
  cases RegistrationServerSdkSource.take handle before with
  | mk selected current =>
      cases selected with
      | none => rfl
      | some token =>
          cases application with
          | none => rfl
          | some application =>
              exact congrFun (complete_native coins setup codec reserve sign encode token application) current

theorem complete_run
    (pin : StateT (State n) m (RustM (core.option.Option session.ServerAuthenticationPin)))
    (reserve : StateT (State n) m Bool) (present : U64 → StateT (State n) m Bool)
    (finish : Completion n m Encoded) (token : peer.ConsumedRegistration) (application : Slice U8)
    (before : State n) :
    (complete pin reserve present finish token application).run before = (do
      let current ← pin.run before
      (afterPin reserve present finish before.control token application current.1).run current.2) := by
  simp only [complete, StateT.run_bind, StateT.run_get, pure_bind]

section Interpret
open RegistrationNativePlatformInterpret (state state_pure state_bind)
variable {κ : Type} {spec : OracleSpec.{0, 0} κ}

private theorem world_interpret (implementation : QueryImpl spec m)
    (work : StateT (Local n) (OracleComp spec) Value) :
    state implementation (RegistrationNativePlatformServerSdk.world work) =
      RegistrationNativePlatformServerSdk.world (state implementation work) := by
  funext before
  simp only [state, RegistrationNativePlatformServerSdk.world, StateT.run, simulateQ_map]

omit [LawfulMonad m] in
private theorem commit_interpret (implementation : QueryImpl spec m)
    (result : RustM (RegistrationWorldServerCompletion.Result Encoded)) :
    state implementation (RegistrationNativePlatformServerSdk.commit (n := n) result) =
      RegistrationNativePlatformServerSdk.commit result := by
  funext before
  cases result with
  | fail error => rfl
  | div => rfl
  | ok result => cases result <;> rfl

theorem fromInitial_interpret (implementation : QueryImpl spec m)
    (finish : Completion n (OracleComp spec) Encoded)
    (control : pqxdh.ServerState) (pending : registration.ServerInitialKdf) :
    state implementation (fromInitial finish control pending) =
      fromInitial (fun control pending => state implementation (finish control pending)) control pending := by
  unfold fromInitial
  rw [state_bind, world_interpret]
  apply bind_congr
  intro published
  exact commit_interpret implementation published

theorem afterOccupancy_interpret (implementation : QueryImpl spec m)
    (reserve : StateT (State n) (OracleComp spec) Bool) (finish : Completion n (OracleComp spec) Encoded)
    (control : pqxdh.ServerState) (lookup : peer.CompletionLookup) (occupied : Bool) :
    state implementation (afterOccupancy reserve finish control lookup occupied) =
      afterOccupancy (state implementation reserve)
        (fun control pending => state implementation (finish control pending)) control lookup occupied := by
  unfold afterOccupancy
  cases lookup.resume occupied with
  | fail error => exact state_pure implementation _
  | div => exact state_pure implementation _
  | ok result =>
      cases result with
      | Err previous => exact state_pure implementation _
      | Ok pending =>
          rw [state_bind]
          apply bind_congr
          intro admitted
          cases admitted with
          | false => exact state_pure implementation _
          | true => exact fromInitial_interpret implementation finish control pending

theorem afterPin_interpret (implementation : QueryImpl spec m)
    (reserve : StateT (State n) (OracleComp spec) Bool)
    (present : U64 → StateT (State n) (OracleComp spec) Bool)
    (finish : Completion n (OracleComp spec) Encoded) (control : pqxdh.ServerState)
    (token : peer.ConsumedRegistration) (application : Slice U8)
    (result : RustM (core.option.Option session.ServerAuthenticationPin)) :
    state implementation (afterPin reserve present finish control token application result) =
      afterPin (state implementation reserve) (fun keyId => state implementation (present keyId))
        (fun control pending => state implementation (finish control pending)) control token application result := by
  unfold afterPin
  cases result with
  | fail error => exact state_pure implementation _
  | div => exact state_pure implementation _
  | ok value =>
      cases value with
      | none => exact state_pure implementation _
      | some pin =>
          dsimp only
          cases peer.begin_completion_lookup control pin token application with
          | fail error => exact state_pure implementation _
          | div => exact state_pure implementation _
          | ok result =>
              cases result with
              | Err previous => exact state_pure implementation _
              | Ok lookup =>
                  dsimp only
                  cases lookup.request with
                  | fail error => exact state_pure implementation _
                  | div => exact state_pure implementation _
                  | ok keyId =>
                      dsimp only
                      split
                      · rw [state_bind]
                        apply bind_congr
                        intro occupied
                        exact afterOccupancy_interpret implementation reserve finish control lookup occupied
                      · exact state_pure implementation _

theorem complete_interpret (implementation : QueryImpl spec m)
    (pin : StateT (State n) (OracleComp spec) (RustM (core.option.Option session.ServerAuthenticationPin)))
    (reserve : StateT (State n) (OracleComp spec) Bool)
    (present : U64 → StateT (State n) (OracleComp spec) Bool)
    (finish : Completion n (OracleComp spec) Encoded)
    (token : peer.ConsumedRegistration) (application : Slice U8) :
    state implementation (complete pin reserve present finish token application) =
      complete (state implementation pin) (state implementation reserve)
        (fun keyId => state implementation (present keyId))
        (fun control pending => state implementation (finish control pending)) token application := by
  unfold complete
  rw [state_bind]
  have getInterpret : state implementation (get : StateT (State n) (OracleComp spec) (State n)) = get := rfl
  rw [getInterpret]
  apply bind_congr
  intro before
  rw [state_bind]
  apply bind_congr
  intro current
  exact afterPin_interpret implementation reserve present finish before.control token application current

theorem build_interpret (implementation : QueryImpl spec m)
    (pin : StateT (State n) (OracleComp spec) (RustM (core.option.Option session.ServerAuthenticationPin)))
    (reserve : StateT (State n) (OracleComp spec) Bool)
    (present : U64 → StateT (State n) (OracleComp spec) Bool)
    (finish : Completion n (OracleComp spec) Encoded) (handle : Nat) (application : Option (Slice U8)) :
    state implementation (build pin reserve present finish handle application) =
      build (state implementation pin) (state implementation reserve)
        (fun keyId => state implementation (present keyId))
        (fun control pending => state implementation (finish control pending)) handle application := by
  funext before
  unfold build state StateT.run
  cases RegistrationServerSdkSource.take handle before with
  | mk selected current =>
      cases selected with
      | none => rfl
      | some token =>
          cases application with
          | none => rfl
          | some application =>
              exact congrFun (complete_interpret implementation pin reserve present finish token application) current

theorem build_continuation (implementation : QueryImpl spec m)
    (pin : StateT (State n) (OracleComp spec) (RustM (core.option.Option session.ServerAuthenticationPin)))
    (reserve : StateT (State n) (OracleComp spec) Bool)
    (present : U64 → StateT (State n) (OracleComp spec) Bool)
    (finish : Completion n (OracleComp spec) Encoded) (handle : Nat) (application : Option (Slice U8))
    (next : RustM (Option (U64 × Encoded)) → StateT (State n) (OracleComp spec) Value) :
    state implementation (build pin reserve present finish handle application >>= next) = (do
      let result ← build (state implementation pin) (state implementation reserve)
        (fun keyId => state implementation (present keyId))
        (fun control pending => state implementation (finish control pending)) handle application
      state implementation (next result)) := by
  rw [state_bind, build_interpret]

end Interpret

end BeaconcryptCore.Computational.RegistrationNativePlatformCompletionSdk

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformCompletionSdk.fromInitial_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformCompletionSdk.fromInitial_native
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformCompletionSdk.afterOccupancy_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformCompletionSdk.afterOccupancy_native
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformCompletionSdk.complete_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformCompletionSdk.complete_native
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformCompletionSdk.build_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformCompletionSdk.build_native
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformCompletionSdk.complete_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformCompletionSdk.complete_run
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformCompletionSdk.fromInitial_interpret' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformCompletionSdk.fromInitial_interpret
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformCompletionSdk.afterOccupancy_interpret' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformCompletionSdk.afterOccupancy_interpret
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformCompletionSdk.afterPin_interpret' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformCompletionSdk.afterPin_interpret
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformCompletionSdk.complete_interpret' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformCompletionSdk.complete_interpret
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformCompletionSdk.build_interpret' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformCompletionSdk.build_interpret
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformCompletionSdk.build_continuation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformCompletionSdk.build_continuation
