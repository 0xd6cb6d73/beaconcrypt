-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformServerSdk

/-! A common interpreter threads external platform state through native StateT programs. These are exact whole value/state equations, including adaptive continuations and failed requests. They provide interpretation algebra for the additive platform model; they do not identify its stateful allocator with the older pure native profile. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformInterpret
variable {κ State Value Next : Type} {spec : OracleSpec.{0, 0} κ}
variable {m : Type → Type} [Monad m]

def state (implementation : QueryImpl spec m) (work : StateT State (OracleComp spec) Value) :
    StateT State m Value := fun before => simulateQ implementation (work.run before)

theorem state_pure (implementation : QueryImpl spec m) (value : Value) :
    state implementation (pure value : StateT State (OracleComp spec) Value) = pure value := by
  funext before
  rfl

variable [LawfulMonad m]

theorem state_bind (implementation : QueryImpl spec m)
    (work : StateT State (OracleComp spec) Value)
    (next : Value → StateT State (OracleComp spec) Next) :
    state implementation (work >>= next) =
      (state implementation work >>= fun value => state implementation (next value)) := by
  funext before
  simp only [state, StateT.run_bind, simulateQ_bind]
  rfl

theorem state_simulate {ι : Type} {source : OracleSpec ι}
    (implementation : QueryImpl spec m)
    (handler : QueryImpl source (StateT State (OracleComp spec))) (work : OracleComp source Value) :
    state implementation (simulateQ handler work) =
      simulateQ (fun query => state implementation (handler query)) work := by
  induction work using OracleComp.inductionOn with
  | pure value => simp only [simulateQ_pure, state_pure]
  | query_bind query next ih => simp only [simulateQ_bind, simulateQ_spec_query, state_bind, ih]

omit [LawfulMonad m] in
private theorem state_get (implementation : QueryImpl spec m) :
    state implementation (get : StateT State (OracleComp spec) State) = get := by
  funext before
  rfl

theorem state_native {n : Nat} (implementation : QueryImpl spec m)
    (coins : QueryImpl unifSpec (OracleComp spec))
    (work : StateT (RegistrationServerFrontendCompiler.State n) ProbComp Value) :
    state implementation (RegistrationNativePlatformServerSdk.liftNative coins work) =
      RegistrationNativePlatformServerSdk.liftNative (fun query => simulateQ implementation (coins query)) work := by
  funext before
  exact (QueryImpl.simulateQ_compose implementation coins (work.run before)).symm
theorem afterAuthentication {n : Nat} {ι KemSK : Type} {base : OracleSpec ι}
    (implementation : QueryImpl spec m) (coins : QueryImpl unifSpec (OracleComp spec))
    (setup : PqxdhServerAuthExperiment.Setup base KemSK) (checks : PqxdhServerAuthExperiment.Checks)
    (reserve : StateT (RegistrationServerFrontendCompiler.State n) (OracleComp spec) Bool)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit)
    (packet : registration.InitPacket) (authenticated : registration.AuthenticatedInit) :
    state implementation (RegistrationNativePlatformServerSdk.afterAuthentication coins setup checks reserve
      representation created packet authenticated) =
      RegistrationNativePlatformServerSdk.afterAuthentication (fun query => simulateQ implementation (coins query))
        setup checks (state implementation reserve) representation created packet authenticated := by
  unfold RegistrationNativePlatformServerSdk.afterAuthentication
  rw [state_bind, state_get]
  apply bind_congr
  intro before
  cases consumed : before.consumed.contains (RegistrationReplaySchedule.identifier authenticated) with
  | true => exact state_pure implementation _
  | false =>
    simp only [Bool.false_eq_true, ite_false]
    rw [state_bind]
    apply bind_congr
    intro admitted
    cases admitted with
    | false => exact state_pure implementation _
    | true =>
      simp only [ite_true]
      rw [state_bind, state_native]
      apply bind_congr
      intro completed
      cases completed with
      | fail error => exact state_pure implementation _
      | div => exact state_pure implementation _
      | ok effect =>
        cases effect <;> first | exact state_native implementation coins _ | exact state_pure implementation _
theorem accept {n : Nat} {ι KemSK Reader Response : Type} {base : OracleSpec ι}
    (implementation : QueryImpl spec m) (coins : QueryImpl unifSpec (OracleComp spec))
    (setup : PqxdhServerAuthExperiment.Setup base KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (checks : PqxdhServerAuthExperiment.Checks)
    (reserve : StateT (RegistrationServerFrontendCompiler.State n) (OracleComp spec) Bool)
    (route : RawCtxServerRouting.SenderDecoder) (verify : MldsaTranscriptAuth.Verify)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (packet : registration.InitPacket) :
    state implementation (RegistrationNativePlatformServerSdk.accept coins setup codec checks reserve
      route verify representation created packet) =
      RegistrationNativePlatformServerSdk.accept (fun query => simulateQ implementation (coins query))
        setup codec checks (state implementation reserve) route verify representation created packet := by
  unfold RegistrationNativePlatformServerSdk.accept
  rw [state_bind, state_native]
  apply bind_congr
  intro checked
  cases checked with
  | fail error => exact state_pure implementation _
  | div => exact state_pure implementation _
  | ok result =>
    rcases result with ⟨events, verdict⟩
    cases verdict with
    | Accepted authenticated => exact afterAuthentication implementation coins setup checks reserve representation created packet authenticated
    | _ => exact state_pure implementation _
end BeaconcryptCore.Computational.RegistrationNativePlatformInterpret

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformInterpret.state_pure' depends on axioms: [Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformInterpret.state_pure

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformInterpret.state_bind' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformInterpret.state_bind

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformInterpret.state_simulate' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformInterpret.state_simulate

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformInterpret.state_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformInterpret.state_native

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformInterpret.afterAuthentication' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformInterpret.afterAuthentication

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformInterpret.accept' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformInterpret.accept
