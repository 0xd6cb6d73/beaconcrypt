-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformServerOpenAuthentication
open OracleComp OracleSpec CoreModels Aeneas beaconcrypt_core
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
/-! The corrected OPEN Server controller is retained as an exact free program. Its indexed protocol requests and actual stateful public reservation have distinct branches. Interpreting this syntax preserves every source control branch, public material state and scalar-free environment. -/
namespace BeaconcryptCore.Computational.RegistrationNativePlatformServerOpenSyntax
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativePlatformServerReferenceAccept (PublicM)
variable {n : Nat} {ι KemSK Value Next : Type} {base : OracleSpec ι}
variable {m : Type → Type} [Monad m] [LawfulMonad m]

abbrev Spec (n : Nat) (KemSK : Type) := RegistrationNativeKemReferenceCompiler.Spec n KemSK + (Unit →ₒ Bool)

def protocol : QueryImpl (RegistrationNativeKemReferenceCompiler.Spec n KemSK) (OracleComp (Spec n KemSK)) := fun query => (Spec n KemSK).query (.inl query)
def reserve : OracleComp (Spec n KemSK) Bool := (Spec n KemSK).query (.inr ())

def implementation (handler : QueryImpl (Spec n KemSK) m) : QueryImpl (RegistrationNativeKemReferenceCompiler.Spec n KemSK) m :=
  fun query => handler (.inl query)

def evaluate (handler : QueryImpl (Spec n KemSK) m) (work : PublicM (OracleComp (Spec n KemSK)) Value) : PublicM m Value :=
  fun before env => simulateQ handler ((work.run before).run env)

noncomputable def accept (setup : Setup base KemSK) (checks : Checks) (verify : MldsaTranscriptAuth.Verify) (packet : registration.InitPacket) : PublicM (OracleComp (Spec n KemSK)) (RustM (Option Nat)) :=
  RegistrationNativePlatformServerOpenControl.accept protocol reserve setup checks verify packet

omit [LawfulMonad m] in
theorem evaluate_pure (handler : QueryImpl (Spec n KemSK) m) (value : Value) :
    evaluate handler (pure value : PublicM (OracleComp (Spec n KemSK)) Value) = pure value := by
  funext before env
  rfl

theorem evaluate_bind (handler : QueryImpl (Spec n KemSK) m) (work : PublicM (OracleComp (Spec n KemSK)) Value)
    (next : Value → PublicM (OracleComp (Spec n KemSK)) Next) :
    evaluate handler (work >>= next) = (evaluate handler work >>= fun value => evaluate handler (next value)) := by
  funext before env
  simp only [evaluate, StateT.run_bind, simulateQ_bind]
  rfl

omit [LawfulMonad m] in
theorem evaluate_get (handler : QueryImpl (Spec n KemSK) m) :
    evaluate handler (get : PublicM (OracleComp (Spec n KemSK)) RegistrationServerMaterialFrontend.State) = get := by
  funext before env
  rfl

theorem evaluate_lift (handler : QueryImpl (Spec n KemSK) m) (work : OracleComp (Spec n KemSK) Value) :
    evaluate handler (StateT.lift (StateT.lift work)) = StateT.lift (StateT.lift (simulateQ handler work)) := by
  funext before env
  change simulateQ handler (((StateT.lift (StateT.lift work) : PublicM (OracleComp (Spec n KemSK)) Value).run before).run env) =
    (((StateT.lift (StateT.lift (simulateQ handler work)) : PublicM m Value).run before).run env)
  simp only [StateT.run_lift, bind_pure_comp, StateT.run_map, simulateQ_map, Functor.map_map]

theorem protocol_program (handler : QueryImpl (Spec n KemSK) m)
    (work : OracleComp (RegistrationNativeKemReferenceCompiler.Spec n KemSK) Value) :
    simulateQ handler (simulateQ protocol work) = simulateQ (implementation handler) work := by
  rw [← QueryImpl.simulateQ_compose]
  apply congrArg (fun interpreted => simulateQ interpreted work)
  funext query
  simp only [QueryImpl.apply_compose, protocol, simulateQ_spec_query, implementation]

theorem effects (handler : QueryImpl (Spec n KemSK) m)
    (work : OracleComp (PqxdhRecordLiftInterface.EnvEffects n) Value) :
    simulateQ handler (simulateQ (RegistrationNativePlatformServerOpenControl.effects protocol) work) =
      simulateQ (RegistrationNativePlatformServerOpenControl.effects (implementation handler)) work := by
  rw [← QueryImpl.simulateQ_compose]
  apply congrArg (fun interpreted => simulateQ interpreted work)
  funext query
  simp only [RegistrationNativePlatformServerOpenControl.effects, QueryImpl.compose]
  exact protocol_program handler (RegistrationBeaconReferenceCompiler.effect query)

theorem pin (handler : QueryImpl (Spec n KemSK) m) (current : session.ServerAuthenticationPin) :
    simulateQ handler (RegistrationNativePlatformServerReferenceAccept.pin (RegistrationNativePlatformServerOpenControl.effects protocol) current) =
      RegistrationNativePlatformServerReferenceAccept.pin (RegistrationNativePlatformServerOpenControl.effects (implementation handler)) current := by
  unfold RegistrationNativePlatformServerReferenceAccept.pin
  rw [← QueryImpl.simulateQ_compose]
  apply congrArg (fun interpreted => simulateQ interpreted (RegistrationNativeServerPinRecompute.program current.binding current.public_key))
  funext request
  simp only [QueryImpl.apply_compose, RegistrationNativePlatformServerReferenceAccept.hash,
    simulateQ_bind, simulateQ_pure]
  have effect := effects handler ((PqxdhRecordLiftInterface.EnvEffects n).query
    (.inr (.hash (BeaconcryptCore.Refinement.RegistrationInputs.hashBytes request))))
  simp only [simulateQ_spec_query] at effect
  rw [effect]

theorem agreement (handler : QueryImpl (Spec n KemSK) m) (setup : Setup base KemSK) (checks : Checks)
    (packet : registration.InitPacket) (authenticated : registration.AuthenticatedInit) :
    evaluate handler (RegistrationNativePlatformServerOpenKernel.agreement protocol setup checks packet authenticated) =
      RegistrationNativePlatformServerOpenKernel.agreement (implementation handler) setup checks packet authenticated := by
  funext before env
  change simulateQ handler (simulateQ protocol (((RegistrationServerOpenReferenceCompiler.agreement setup checks packet authenticated).run before).run env)) = _
  rw [← QueryImpl.simulateQ_compose]
  apply congrArg (fun interpreted => simulateQ interpreted (((RegistrationServerOpenReferenceCompiler.agreement setup checks packet authenticated).run before).run env))
  funext query
  simp only [QueryImpl.apply_compose, protocol, simulateQ_spec_query, implementation]

omit [LawfulMonad m] in
theorem retain (handler : QueryImpl (Spec n KemSK) m) (ready : RegistrationServerReferenceRoot.Ready) :
    evaluate handler (RegistrationNativePlatformServerReferenceAccept.retain ready) = RegistrationNativePlatformServerReferenceAccept.retain ready := by
  funext before env
  unfold evaluate
  dsimp only [RegistrationNativePlatformServerReferenceAccept.retain, StateT.run]
  cases current : RegistrationServerMaterialFrontend.retain ready before <;> rfl

theorem afterAuthentication (handler : QueryImpl (Spec n KemSK) m) (setup : Setup base KemSK) (checks : Checks)
    (packet : registration.InitPacket) (authenticated : registration.AuthenticatedInit) :
    evaluate handler (RegistrationNativePlatformServerOpenControl.afterAuthentication protocol reserve setup checks packet authenticated) =
      RegistrationNativePlatformServerOpenControl.afterAuthentication (implementation handler) (handler (.inr ())) setup checks packet authenticated := by
  unfold RegistrationNativePlatformServerOpenControl.afterAuthentication
  rw [evaluate_bind, evaluate_get]
  apply bind_congr
  intro before
  split
  · exact evaluate_pure handler _
  · rw [evaluate_bind, evaluate_lift]
    simp only [reserve, simulateQ_spec_query]
    apply bind_congr
    intro admitted
    cases admitted with
    | false => exact evaluate_pure handler _
    | true =>
      simp only [ite_true]
      rw [evaluate_bind, agreement]
      apply bind_congr
      intro accepted
      cases accepted with
      | fail error | div => exact evaluate_pure handler _
      | ok selected => cases selected with
        | none => exact evaluate_pure handler _
        | some ready => exact retain handler ready

theorem afterPin (handler : QueryImpl (Spec n KemSK) m) (setup : Setup base KemSK) (checks : Checks)
    (verify : MldsaTranscriptAuth.Verify) (packet : registration.InitPacket) (current : RegistrationNativeServerPinRecompute.PinReply) :
    evaluate handler (RegistrationNativePlatformServerOpenControl.afterPin protocol reserve setup checks verify packet current) =
      RegistrationNativePlatformServerOpenControl.afterPin (implementation handler) (handler (.inr ())) setup checks verify packet current := by
  unfold RegistrationNativePlatformServerOpenControl.afterPin
  cases current with
  | fail error | div => exact evaluate_pure handler _
  | ok selected => cases selected with
    | none => exact evaluate_pure handler _
    | some pin =>
      rw [evaluate_bind, evaluate_lift, effects]
      apply bind_congr
      intro checked
      cases checked with
      | fail error | div => exact evaluate_pure handler _
      | ok pair =>
        rcases pair with ⟨events, authenticated⟩
        cases authenticated
        all_goals first
          | exact afterAuthentication handler setup checks packet _
          | exact evaluate_pure handler _

theorem accept_source (handler : QueryImpl (Spec n KemSK) m) (setup : Setup base KemSK) (checks : Checks)
    (verify : MldsaTranscriptAuth.Verify) (packet : registration.InitPacket) :
    evaluate handler (accept setup checks verify packet) =
      RegistrationNativePlatformServerOpenControl.accept (implementation handler) (handler (.inr ())) setup checks verify packet := by
  unfold accept RegistrationNativePlatformServerOpenControl.accept
  rw [evaluate_bind, evaluate_get]
  apply bind_congr
  intro before
  rw [evaluate_bind, evaluate_lift, pin]
  apply bind_congr
  intro current
  exact afterPin handler setup checks verify packet current

end BeaconcryptCore.Computational.RegistrationNativePlatformServerOpenSyntax

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformServerOpenSyntax.evaluate_pure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformServerOpenSyntax.evaluate_pure

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformServerOpenSyntax.evaluate_bind' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformServerOpenSyntax.evaluate_bind

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformServerOpenSyntax.evaluate_get' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformServerOpenSyntax.evaluate_get

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformServerOpenSyntax.evaluate_lift' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformServerOpenSyntax.evaluate_lift

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformServerOpenSyntax.protocol_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformServerOpenSyntax.protocol_program

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformServerOpenSyntax.effects' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformServerOpenSyntax.effects

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformServerOpenSyntax.pin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformServerOpenSyntax.pin

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformServerOpenSyntax.agreement' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformServerOpenSyntax.agreement

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformServerOpenSyntax.retain' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformServerOpenSyntax.retain

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformServerOpenSyntax.afterAuthentication' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformServerOpenSyntax.afterAuthentication

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformServerOpenSyntax.afterPin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformServerOpenSyntax.afterPin

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformServerOpenSyntax.accept_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformServerOpenSyntax.accept_source
