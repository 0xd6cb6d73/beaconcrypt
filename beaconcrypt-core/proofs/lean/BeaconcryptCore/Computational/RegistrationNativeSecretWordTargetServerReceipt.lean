-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetServerEffects

/-! Successful actual Word Server acceptance exposes the reached mandatory authentication and actual successful collector under the same concrete current-environment source. Replay and allocation failures remain before collection. The original public accepted-key tuple is derived from the actual pure signature callbacks, independently of random material and root-service replies. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetServerReceipt
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeSecretWordMessage (ServerState ServerReady)
open RegistrationNativeSecretWordInterface (LocalSpec effect prepare)
open RegistrationNativeSecretWordTargetServerExecution (Auxiliary lower lower_bind)
open RegistrationServerReferenceCompiler (Environment)
variable {n : Nat} {ι KemSK : Type} {base : OracleSpec ι}

private theorem lower_pure (implementation : QueryImpl (LocalSpec n KemSK)
      (StateT (RegistrationNativeSecretWordInterpreter.State n KemSK) ProbComp)) {Value : Type} (value : Value) :
    lower implementation (pure value) = pure value := by
  apply StateT.ext
  intro before
  simp only [RegistrationNativeSecretWordTargetServerExecution.lower_run, StateT.run_pure, simulateQ_pure, map_pure]

attribute [local irreducible] RegistrationAuthenticationCompiler.program
  RegistrationNativeSecretWordServerCompiler.afterAuthentication RegistrationNativeSecretWordServerCompiler.agreement
  RegistrationNativeSecretWordServerCompiler.collect RegistrationNativeSecretWordServerRoot.client
  RegistrationNativeSecretWordServerCompiler.retain

private theorem select_run {S Result : Type} {m : Type → Type} [Monad m]
    (checked : RustM (List BeaconcryptCore.Refinement.RegistrationAuthenticationFlow.Event × registration.InitAuthentication))
    (failed : Error → StateT S m Result) (diverged absent : StateT S m Result)
    (accepted : registration.AuthenticatedInit → StateT S m Result) (before : S) :
    ((match checked with
      | .fail error => failed error
      | .div => diverged
      | .ok (_events, .Accepted authenticated) => accepted authenticated
      | .ok _ => absent) : StateT S m Result).run before =
      match checked with
      | .fail error => (failed error).run before
      | .div => diverged.run before
      | .ok (_events, .Accepted authenticated) => (accepted authenticated).run before
      | .ok _ => absent.run before := by
  cases checked with
  | fail error | div => rfl
  | ok checked => rcases checked with ⟨events, stage⟩; cases stage <;> rfl

set_option maxRecDepth 4096 in
private theorem accept_program (setup : Setup base KemSK) (checks : Checks) (verify : MldsaTranscriptAuth.Verify)
    (packet : registration.InitPacket) (before : ServerState) :
    (RegistrationNativeSecretWordServerCompiler.accept (n := n) setup checks verify packet).run before = (do
      let checked ← StateT.lift (simulateQ effect (RegistrationAuthenticationCompiler.program setup.source.crypto verify before.pin packet))
      match checked with
      | .fail error => pure (.fail error, before)
      | .div => pure (.div, before)
      | .ok (_events, .Accepted authenticated) =>
          (RegistrationNativeSecretWordServerCompiler.afterAuthentication setup checks packet authenticated).run before
      | .ok _ => pure (.ok none, before)) := by
  apply StateT.ext
  intro env
  simp only [RegistrationNativeSecretWordServerCompiler.accept, StateT.run_bind, StateT.run_get,
    StateT.run_lift, pure_bind, bind_pure_comp, bind_map_left]
  apply bind_congr
  intro checked
  have dispatched := select_run (m := StateT Environment (OracleComp (LocalSpec n KemSK))) checked (fun error => pure (.fail error)) (pure .div) (pure (.ok none))
    (fun authenticated => RegistrationNativeSecretWordServerCompiler.afterAuthentication (n := n) setup checks packet authenticated) before
  have actual := congrArg (fun work => work.run env) dispatched
  simp only [StateT.run_pure] at actual
  convert actual using 1 <;> rfl

/-- Actual native acceptance has this complete current-state authentication dispatch before replay admission and collection. -/
theorem accept_program_source (setup : Setup base KemSK) (checks : Checks) (verify : MldsaTranscriptAuth.Verify)
    (packet : registration.InitPacket) (before : ServerState) :
    (RegistrationNativeSecretWordServerCompiler.accept (n := n) setup checks verify packet).run before = (do
      let checked ← StateT.lift (simulateQ effect (RegistrationAuthenticationCompiler.program setup.source.crypto verify before.pin packet))
      match checked with
      | .fail error => pure (.fail error, before)
      | .div => pure (.div, before)
      | .ok (_events, .Accepted authenticated) =>
          (RegistrationNativeSecretWordServerCompiler.afterAuthentication setup checks packet authenticated).run before
      | .ok _ => pure (.ok none, before)) :=
  accept_program setup checks verify packet before

private theorem after_program (setup : Setup base KemSK) (checks : Checks)
    (packet : registration.InitPacket) (authenticated : registration.AuthenticatedInit) (before : ServerState) :
    (RegistrationNativeSecretWordServerCompiler.afterAuthentication (n := n) setup checks packet authenticated).run before =
      (if before.consumed.contains (RegistrationReplaySchedule.identifier authenticated) then pure (.ok none, before)
       else if checks.reserveRegistration then do
         let result ← (RegistrationNativeSecretWordServerCompiler.agreement setup checks packet authenticated).run before
         match result.1 with
         | .fail error => pure (.fail error, result.2)
         | .div => pure (.div, result.2)
         | .ok none => pure (.ok none, result.2)
         | .ok (some ready) => (RegistrationNativeSecretWordServerCompiler.retain ready).run result.2
       else pure (.ok none, before)) := by
  apply StateT.ext
  intro env
  simp only [RegistrationNativeSecretWordServerCompiler.afterAuthentication, StateT.run_bind,
    StateT.run_get, pure_bind]
  split <;> try rfl
  split <;> try rfl
  simp only [StateT.run_bind]
  apply bind_congr
  rintro ⟨⟨accepted, server⟩, afterEnv⟩
  cases accepted with
  | fail error | div => rfl
  | ok accepted => cases accepted <;> rfl

private theorem agreement_program (setup : Setup base KemSK) (checks : Checks)
    (packet : registration.InitPacket) (authenticated : registration.AuthenticatedInit) (before : ServerState) :
    (RegistrationNativeSecretWordServerCompiler.agreement (n := n) setup checks packet authenticated).run before = (do
      let result ← RegistrationNativeSecretWordServerCompiler.collect setup checks packet authenticated
      match result with
      | none => pure (.ok none, before)
      | some input =>
          (fun reply => (reply, before)) <$> StateT.lift
            (simulateQ prepare (RegistrationNativeSecretWordServerRoot.client authenticated.binding input))) := by
  apply StateT.ext
  intro env
  simp only [RegistrationNativeSecretWordServerCompiler.agreement, StateT.run_bind, StateT.run_lift,
    bind_pure_comp, bind_map_left]
  apply bind_congr
  intro result
  cases result.1 <;> rfl

private theorem agreement_collected
    (implementation : QueryImpl (LocalSpec n KemSK) (StateT (RegistrationNativeSecretWordInterpreter.State n KemSK) ProbComp))
    (setup : Setup base KemSK) (checks : Checks) (packet : registration.InitPacket)
    (authenticated : registration.AuthenticatedInit) (before : ServerState) (initial reached : Auxiliary n KemSK)
    (ready : ServerReady) (after : ServerState)
    (supported : ((.ok (some ready), after), reached) ∈ support
      ((lower implementation ((RegistrationNativeSecretWordServerCompiler.agreement setup checks packet authenticated).run before)).run initial)) :
    ∃ input middle, (some input, middle) ∈ support
      ((lower implementation (RegistrationNativeSecretWordServerCompiler.collect setup checks packet authenticated)).run initial) := by
  rw [agreement_program, lower_bind, StateT.run_bind, mem_support_bind_iff] at supported
  obtain ⟨⟨input, middle⟩, collected, continued⟩ := supported
  cases input with
  | none => simp only [lower_pure, StateT.run_pure, mem_support_pure_iff, Prod.mk.injEq, RustM.ok.injEq,
      reduceCtorEq, false_and] at continued
  | some input => exact ⟨input, middle, collected⟩

private theorem after_collected
    (implementation : QueryImpl (LocalSpec n KemSK) (StateT (RegistrationNativeSecretWordInterpreter.State n KemSK) ProbComp))
    (setup : Setup base KemSK) (checks : Checks) (packet : registration.InitPacket)
    (authenticated : registration.AuthenticatedInit) (before : ServerState) (initial reached : Auxiliary n KemSK)
    (session : Nat) (after : ServerState)
    (supported : ((.ok (some session), after), reached) ∈ support
      ((lower implementation ((RegistrationNativeSecretWordServerCompiler.afterAuthentication setup checks packet authenticated).run before)).run initial)) :
    ∃ input middle, (some input, middle) ∈ support
      ((lower implementation (RegistrationNativeSecretWordServerCompiler.collect setup checks packet authenticated)).run initial) := by
  rw [after_program] at supported
  split at supported
  · simp only [lower_pure, StateT.run_pure, mem_support_pure_iff, Prod.mk.injEq, RustM.ok.injEq,
      reduceCtorEq, false_and] at supported
  · split at supported
    · rw [lower_bind, StateT.run_bind, mem_support_bind_iff] at supported
      obtain ⟨⟨⟨accepted, current⟩, middle⟩, called, continued⟩ := supported
      cases accepted with
      | fail error | div => simp only [lower_pure, StateT.run_pure, mem_support_pure_iff,
          Prod.mk.injEq, reduceCtorEq, false_and] at continued
      | ok accepted => cases accepted with
        | none => simp only [lower_pure, StateT.run_pure, mem_support_pure_iff,
            Prod.mk.injEq, RustM.ok.injEq, reduceCtorEq, false_and] at continued
        | some ready => exact agreement_collected implementation setup checks packet authenticated before initial middle ready current called
    · simp only [lower_pure, StateT.run_pure, mem_support_pure_iff, Prod.mk.injEq, RustM.ok.injEq,
        reduceCtorEq, false_and] at supported

/-- Successful actual acceptance reaches mandatory authentication and its own successful collector, with the original public verified tuple derived internally. -/
theorem accept_collected
    (implementation : QueryImpl (LocalSpec n KemSK) (StateT (RegistrationNativeSecretWordInterpreter.State n KemSK) ProbComp))
    (setup : Setup base KemSK) (checks : Checks) (verify : MldsaTranscriptAuth.Verify) (packet : registration.InitPacket)
    (before : ServerState) (initial reached : Auxiliary n KemSK) (session : Nat) (after : ServerState)
    (supported : ((.ok (some session), after), reached) ∈ support
      ((lower implementation ((RegistrationNativeSecretWordServerCompiler.accept setup checks verify packet).run before)).run initial)) :
    ∃ events authenticated afterAuthentication input afterCollection,
      (.ok (events, .Accepted authenticated), afterAuthentication) ∈ support
        ((lower implementation (StateT.lift (simulateQ effect
          (RegistrationAuthenticationCompiler.program setup.source.crypto verify before.pin packet)))).run initial) ∧
      (some input, afterCollection) ∈ support
        ((lower implementation (RegistrationNativeSecretWordServerCompiler.collect setup checks packet authenticated)).run afterAuthentication) ∧
      PqxdhDeploymentTranscript.acceptedKeys setup.source.crypto (RegistrationRootInput.candidate packet) =
        some (RegistrationRootInput.identity authenticated.registration, RegistrationRootInput.keys authenticated.registration) := by
  rw [accept_program, lower_bind, StateT.run_bind, mem_support_bind_iff] at supported
  obtain ⟨⟨checked, middle⟩, authenticated, continued⟩ := supported
  cases checked with
  | fail error | div => simp only [lower_pure, StateT.run_pure, mem_support_pure_iff,
      Prod.mk.injEq, reduceCtorEq, false_and] at continued
  | ok checked =>
      rcases checked with ⟨events, stage⟩
      cases stage <;> try simp only [lower_pure, StateT.run_pure, mem_support_pure_iff,
        Prod.mk.injEq, RustM.ok.injEq, reduceCtorEq, false_and] at continued
      case Accepted accepted =>
          obtain ⟨input, afterCollection, collected⟩ := after_collected implementation setup checks packet accepted
            before middle reached session after continued
          exact ⟨events, accepted, middle, input, afterCollection, authenticated, collected,
            RegistrationNativeSecretWordTargetServerEffects.accepted_keys implementation setup.source.crypto verify
              before.pin packet initial middle events accepted authenticated⟩

end BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetServerReceipt
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetServerReceipt.accept_collected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetServerReceipt.accept_collected

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetServerReceipt.accept_program_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetServerReceipt.accept_program_source
