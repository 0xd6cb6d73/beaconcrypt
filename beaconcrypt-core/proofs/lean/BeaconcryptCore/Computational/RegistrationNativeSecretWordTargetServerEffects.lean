-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetServerExecution
import BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetAuthentication

/-! The selected Server's actual authentication hashes and pure signature callbacks run under the same mutable environment/private interpreter used by its later getter. Querywise lowering derives the generic verifier source needed for the original accepted-key tuple; no shared-cache equality or real SDK backend is assumed. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetServerEffects
open RegistrationNativeSecretWordTargetServerExecution (Auxiliary lower lower_bind lower_program)
open RegistrationNativeSecretWordInterface (LocalSpec effect)
open RegistrationServerReferenceCompiler (Environment)
variable {n : Nat} {KemSK Value Next : Type}

def environment (implementation : QueryImpl (LocalSpec n KemSK)
    (StateT (RegistrationNativeSecretWordInterpreter.State n KemSK) ProbComp)) :
    QueryImpl (PqxdhRecordLiftInterface.EnvEffects n) (StateT (Auxiliary n KemSK) ProbComp) :=
  fun query => lower implementation (StateT.lift (effect query))

private theorem lift_bind (work : OracleComp (LocalSpec n KemSK) Value)
    (next : Value → OracleComp (LocalSpec n KemSK) Next) :
    (StateT.lift (work >>= next) : StateT Environment (OracleComp (LocalSpec n KemSK)) Next) =
      (StateT.lift work >>= fun value => StateT.lift (next value)) := by
  apply StateT.ext
  intro before
  simp only [StateT.run_lift, StateT.run_bind, bind_pure_comp, map_bind, bind_map_left]

private theorem lift_pure (value : Value) :
    (StateT.lift (pure value : OracleComp (LocalSpec n KemSK) Value) : StateT Environment (OracleComp (LocalSpec n KemSK)) Value) = pure value := by
  apply StateT.ext
  intro before
  simp only [StateT.run_lift, StateT.run_pure, pure_bind]

/-- Actual effectful authentication and primitive programs lower to their same concrete querywise environment source. -/
theorem effect_program (implementation : QueryImpl (LocalSpec n KemSK)
    (StateT (RegistrationNativeSecretWordInterpreter.State n KemSK) ProbComp))
    (work : OracleComp (PqxdhRecordLiftInterface.EnvEffects n) Value) :
    lower implementation (StateT.lift (simulateQ effect work)) = simulateQ (environment implementation) work := by
  have lifted : (StateT.lift (simulateQ effect work) : StateT Environment (OracleComp (LocalSpec n KemSK)) Value) =
      simulateQ (fun query => StateT.lift (effect query)) work := by
    induction work using OracleComp.inductionOn with
    | pure value => simp only [simulateQ_pure, lift_pure]
    | query_bind query next ih =>
        simp only [simulateQ_bind, simulateQ_spec_query, lift_bind]
        congr 1
        funext reply
        exact ih reply
  rw [lifted, lower_program]
  rfl

attribute [local irreducible] RegistrationAuthenticationCompiler.program RegistrationRootInput.candidate
  PqxdhDeploymentTranscript.acceptedKeys

/-- The actual reached selected Server authentication yields exactly the original broad designation's verified tuple. -/
theorem accepted_keys (implementation : QueryImpl (LocalSpec n KemSK)
    (StateT (RegistrationNativeSecretWordInterpreter.State n KemSK) ProbComp))
    (crypto : Pqxdh.Crypto) (verify : MldsaTranscriptAuth.Verify)
    (pin : session.ServerAuthenticationPin) (packet : registration.InitPacket)
    (before after : Auxiliary n KemSK)
    (events : List BeaconcryptCore.Refinement.RegistrationAuthenticationFlow.Event)
    (authenticated : registration.AuthenticatedInit)
    (supported : (.ok (events, .Accepted authenticated), after) ∈ support
      ((lower implementation (StateT.lift (simulateQ effect
        (RegistrationAuthenticationCompiler.program crypto verify pin packet)))).run before)) :
    PqxdhDeploymentTranscript.acceptedKeys crypto (RegistrationRootInput.candidate packet) =
      some (RegistrationRootInput.identity authenticated.registration, RegistrationRootInput.keys authenticated.registration) := by
  rw [effect_program] at supported
  exact RegistrationNativeSecretWordTargetAuthentication.compiler_accepted (n := n) (S := Auxiliary n KemSK) crypto verify (environment implementation)
    pin packet before after events authenticated supported

end BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetServerEffects
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetServerEffects.effect_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetServerEffects.effect_program
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetServerEffects.accepted_keys' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetServerEffects.accepted_keys
