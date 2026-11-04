-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformServerRestrictedService
/-! The derived corrected Server reference frontend is an exact free request program. The four leaves are its literal repeated pin hash, peer occupancy, stateful reservation and admitted material service; no whole frontend law is an interpretation field. -/
open OracleComp OracleSpec CoreModels Aeneas beaconcrypt_core
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformServerFrontendProgram
open RegistrationNativePlatformServerMaterialFrontend (Result)
variable {m : Type → Type} [Monad m] [LawfulMonad m]

inductive Request where
  | pin (current : session.ServerAuthenticationPin)
  | reserve
  | present (keyId : U64)
  | service (control : pqxdh.ServerState) (initial : RegistrationBoundKeySchedule.PublicInitial)
      (message : RegistrationNativeRelatedFamily.Message)

def Reply : Request → Type
  | .pin _ => RustM (core.option.Option session.ServerAuthenticationPin)
  | .reserve | .present _ => Bool
  | .service _ _ _ => RustM (RegistrationHiddenInstall.Result (alloc.vec.Vec U8))

abbrev Spec : OracleSpec Request := Reply

def pin (current : session.ServerAuthenticationPin) : OracleComp Spec (Reply (.pin current)) := Spec.query (.pin current)
def reserve : OracleComp Spec Bool := Spec.query .reserve
def present (keyId : U64) : OracleComp Spec Bool := Spec.query (.present keyId)
def service (control : pqxdh.ServerState) (initial : RegistrationBoundKeySchedule.PublicInitial)
    (message : RegistrationNativeRelatedFamily.Message) : OracleComp Spec (Reply (.service control initial message)) :=
  Spec.query (.service control initial message)

def program (handle : Nat) (application : Option (Slice U8)) :
    StateT RegistrationServerMaterialFrontend.State (OracleComp Spec) (Result (alloc.vec.Vec U8)) :=
  RegistrationNativePlatformServerMaterialFrontend.build pin reserve present service handle application

private theorem bind_apply {S V W : Type} {q : Type → Type} [Monad q]
    (work : StateT S q V) (next : V → StateT S q W) (before : S) :
    (work >>= next) before = (do let result ← work before; next result.1 result.2) := rfl

private theorem pure_apply {S V : Type} {q : Type → Type} [Monad q] (value : V) (before : S) :
    (pure value : StateT S q V) before = pure (value, before) := rfl

private theorem lift_apply {S V : Type} {q : Type → Type} [Monad q] [LawfulMonad q]
    (work : q V) (before : S) :
    (StateT.lift work : StateT S q V) before = (fun value => (value, before)) <$> work := bind_pure_comp _ _

private theorem afterResult_interpret (implementation : QueryImpl Spec m)
    (control : pqxdh.ServerState) (message : RegistrationNativeRelatedFamily.Message)
    (action : RustM (core.result.Result RegistrationBoundKeySchedule.PublicInitial pqxdh.ServerState))
    (before : RegistrationServerMaterialFrontend.State) :
    simulateQ implementation
      ((RegistrationNativePlatformServerMaterialFrontend.afterResult reserve service control message action).run before) =
      (RegistrationNativePlatformServerMaterialFrontend.afterResult (implementation .reserve)
        (fun control initial message => implementation (.service control initial message)) control message action).run before := by
  cases action with
  | fail error => simp only [RegistrationNativePlatformServerMaterialFrontend.afterResult, StateT.run_pure, simulateQ_pure]
  | div => simp only [RegistrationNativePlatformServerMaterialFrontend.afterResult, StateT.run_pure, simulateQ_pure]
  | ok answer => cases answer with
    | Err previous => simp only [RegistrationNativePlatformServerMaterialFrontend.afterResult, StateT.run_pure, simulateQ_pure]
    | Ok selected =>
      simp only [RegistrationNativePlatformServerMaterialFrontend.afterResult, StateT.run_bind, StateT.run_lift,
        bind_pure_comp, simulateQ_bind, reserve, simulateQ_spec_query, bind_map_left]
      apply bind_congr
      intro admitted
      cases admitted <;> simp only [Bool.false_eq_true, ite_false, ite_true, StateT.run,
        bind_apply, pure_apply, lift_apply, bind_pure_comp, simulateQ_pure,
        simulateQ_map, service, simulateQ_spec_query]


private theorem afterOccupancy_interpret (implementation : QueryImpl Spec m)
    (control : pqxdh.ServerState) (lookup : peer.CompletionLookup)
    (message : RegistrationNativeRelatedFamily.Message) (occupied : Bool)
    (before : RegistrationServerMaterialFrontend.State) :
    simulateQ implementation
      ((RegistrationNativePlatformServerMaterialFrontend.afterOccupancy reserve service control lookup message occupied).run before) =
      (RegistrationNativePlatformServerMaterialFrontend.afterOccupancy (implementation .reserve)
        (fun control initial message => implementation (.service control initial message)) control lookup message occupied).run before :=
  afterResult_interpret implementation control message _ before

private theorem afterPin_interpret (implementation : QueryImpl Spec m)
    (control : pqxdh.ServerState) (ready : RegistrationServerReferenceRoot.Ready) (application : Slice U8)
    (current : RustM (core.option.Option session.ServerAuthenticationPin)) (before : RegistrationServerMaterialFrontend.State) :
    simulateQ implementation
      ((RegistrationNativePlatformServerMaterialFrontend.afterPin reserve present service control ready application current).run before) =
      (RegistrationNativePlatformServerMaterialFrontend.afterPin (implementation .reserve)
        (fun keyId => implementation (.present keyId))
        (fun control initial message => implementation (.service control initial message)) control ready application current).run before := by
  cases current with
  | fail error => simp only [RegistrationNativePlatformServerMaterialFrontend.afterPin, StateT.run, simulateQ_pure]
  | div => simp only [RegistrationNativePlatformServerMaterialFrontend.afterPin, StateT.run, simulateQ_pure]
  | ok answer => cases answer with
    | none => simp only [RegistrationNativePlatformServerMaterialFrontend.afterPin, StateT.run, simulateQ_pure]
    | some current =>
      unfold RegistrationNativePlatformServerMaterialFrontend.afterPin
      dsimp! only
      cases peer.begin_completion_lookup control current (RegistrationServerMaterialFrontend.token ready) application with
      | fail error => simp only [StateT.run, simulateQ_pure]
      | div => simp only [StateT.run, simulateQ_pure]
      | ok answer => cases answer with
        | Err previous => simp only [StateT.run, simulateQ_pure]
        | Ok selected =>
          simp only [StateT.run]
          cases selected.request with
          | fail error => simp only [simulateQ_pure]
          | div => simp only [simulateQ_pure]
          | ok keyId =>
            by_cases fits : RegistrationServerSdkSource.preflight application keyId = true
            · simp only [ite_eq_left fits, simulateQ_bind, present, simulateQ_spec_query]
              apply bind_congr
              intro occupied
              exact afterOccupancy_interpret implementation control selected ready.reference occupied before
            · simp only [ite_eq_right fits, simulateQ_pure]


private theorem complete_interpret (implementation : QueryImpl Spec m)
    (ready : RegistrationServerReferenceRoot.Ready) (application : Slice U8) (before : RegistrationServerMaterialFrontend.State) :
    simulateQ implementation
      ((RegistrationNativePlatformServerMaterialFrontend.complete pin reserve present service ready application).run before) =
      (RegistrationNativePlatformServerMaterialFrontend.complete (fun current => implementation (.pin current))
        (implementation .reserve) (fun keyId => implementation (.present keyId))
        (fun control initial message => implementation (.service control initial message)) ready application).run before := by
  simp only [RegistrationNativePlatformServerMaterialFrontend.complete, StateT.run,
    simulateQ_bind, pin, simulateQ_spec_query]
  apply bind_congr
  intro current
  exact afterPin_interpret implementation before.control ready application current before

/-- Every complete source-reference build phase is the fold of these four exact leaves. One-use take/cancel, all enclosing Rust outcomes and every reached external state are retained. -/
theorem interpret (implementation : QueryImpl Spec m) (handle : Nat) (application : Option (Slice U8))
    (before : RegistrationServerMaterialFrontend.State) :
    simulateQ implementation ((program handle application).run before) =
      (RegistrationNativePlatformServerMaterialFrontend.build (fun current => implementation (.pin current))
        (implementation .reserve) (fun keyId => implementation (.present keyId))
        (fun control initial message => implementation (.service control initial message)) handle application).run before := by
  unfold program RegistrationNativePlatformServerMaterialFrontend.build
  simp only [StateT.run]
  cases RegistrationServerMaterialFrontend.take handle before with
  | mk selected current => cases selected with
    | none => simp only [simulateQ_pure]
    | some ready => cases application with
      | none => simp only [simulateQ_pure]
      | some application => exact complete_interpret implementation ready application current

end BeaconcryptCore.Computational.RegistrationNativePlatformServerFrontendProgram

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformServerFrontendProgram.interpret' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformServerFrontendProgram.interpret
