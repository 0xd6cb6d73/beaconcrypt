-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetServerReceipt
import BeaconcryptCore.Computational.RegistrationNativeSecretWordLiveServerOriginRetain

/-! Actual outer probability interpretation retains the authentication, collector, root continuation and appended handle of the same successful Server accept. The callback's derived pure echo law, rather than raw support projection, identifies that retained reference. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSecretWordLiveServerOriginOuter
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeSecretWordMessage (Message ServerState ServerReady)
open RegistrationNativeSecretWord (Key)
open RegistrationNativeSecretWordInterface (LocalSpec effect prepare)
open RegistrationNativeSecretWordInterpreter (Provider State)
open RegistrationNativeSecretWordService (Combined)
open RegistrationNativeSecretWordTargetServerExecution (Auxiliary lower lower_bind localImpl)
open RegistrationServerReferenceCompiler (Environment)
variable {n : Nat} {ι KemSK Value Next : Type} {base : OracleSpec ι}

attribute [local irreducible] RegistrationAuthenticationCompiler.program
  RegistrationNativeSecretWordServerCompiler.afterAuthentication RegistrationNativeSecretWordServerCompiler.agreement
  RegistrationNativeSecretWordServerCompiler.collect RegistrationNativeSecretWordServerRoot.client
  RegistrationNativeSecretWordServerCompiler.retain

private theorem lift_pure (value : Value) :
    (StateT.lift (pure value : OracleComp (LocalSpec n KemSK) Value) :
      StateT Environment (OracleComp (LocalSpec n KemSK)) Value) = pure value := by
  apply StateT.ext
  intro before
  simp only [StateT.run_lift, StateT.run_pure, pure_bind]

private theorem lower_pure (implementation : QueryImpl (LocalSpec n KemSK) (StateT (State n KemSK) ProbComp)) (value : Value) :
    lower implementation (pure value) = pure value := by
  apply StateT.ext
  intro before
  simp only [RegistrationNativeSecretWordTargetServerExecution.lower_run, StateT.run_pure, simulateQ_pure, map_pure]

private theorem lower_map (implementation : QueryImpl (LocalSpec n KemSK) (StateT (State n KemSK) ProbComp))
    (observe : Value → Next) (work : StateT Environment (OracleComp (LocalSpec n KemSK)) Value) :
    lower implementation (observe <$> work) = observe <$> lower implementation work := by
  apply StateT.ext
  intro before
  simp only [RegistrationNativeSecretWordTargetServerExecution.lower_run, StateT.run_map, simulateQ_map, Functor.map_map]

private theorem agreement_program (setup : Setup base KemSK) (checks : Checks) (packet : registration.InitPacket)
    (authenticated : registration.AuthenticatedInit) (before : ServerState) :
    (RegistrationNativeSecretWordServerCompiler.agreement (n := n) setup checks packet authenticated).run before = (do
      let result ← RegistrationNativeSecretWordServerCompiler.collect setup checks packet authenticated
      match result with
      | none => pure (.ok none, before)
      | some collected =>
          (fun reply => (reply, before)) <$> StateT.lift
            (simulateQ prepare (RegistrationNativeSecretWordServerRoot.client authenticated.binding collected))) := by
  apply StateT.ext
  intro env
  simp only [RegistrationNativeSecretWordServerCompiler.agreement, StateT.run_bind, StateT.run_lift,
    bind_pure_comp, bind_map_left]
  apply bind_congr
  intro result
  cases result.1 <;> rfl

private theorem after_program (setup : Setup base KemSK) (checks : Checks) (packet : registration.InitPacket)
    (authenticated : registration.AuthenticatedInit) (before : ServerState) :
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

private theorem retain_result (implementation : QueryImpl (LocalSpec n KemSK) (StateT (State n KemSK) ProbComp))
    (ready : ServerReady) (before after : ServerState) (initial reached : Auxiliary n KemSK) (handle : Nat)
    (supported : ((.ok (some handle), after), reached) ∈ support
      ((lower implementation ((RegistrationNativeSecretWordServerCompiler.retain ready).run before)).run initial)) :
    reached = initial ∧ after.sessions[handle]? = some (some ready) := by
  simp only [RegistrationNativeSecretWordServerCompiler.retain, StateT.run] at supported
  cases actual : RegistrationNativeSecretWordServerMaterial.retain ready before with
  | fail error | div => simp only [actual, lower_pure] at supported; cases supported
  | ok pair =>
      rcases pair with ⟨reply, current⟩
      simp only [actual, lower_pure] at supported
      obtain ⟨⟨replyEqual, stateEqual⟩, reachedEqual⟩ := supported
      refine ⟨rfl, ?_⟩
      cases consumed : RegistrationReplaySchedule.consume
          (RegistrationBoundGate.atRoot ready.agreement RegistrationBoundKeySchedule.zero) before.consumed with
      | fail error | div => simp only [RegistrationNativeSecretWordServerMaterial.retain, consumed] at actual; cases actual
      | ok pair =>
          rcases pair with ⟨entry, history⟩
          cases entry with
          | none => simp only [RegistrationNativeSecretWordServerMaterial.retain, consumed] at actual; cases actual
          | some token =>
              simp only [RegistrationNativeSecretWordServerMaterial.retain, consumed, RustM.ok.injEq, Prod.mk.injEq, Option.some.injEq] at actual
              obtain ⟨rfl, rfl⟩ := actual
              simp only [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self, List.getElem?_cons_zero]

variable (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (input : Message → Option Key) (inside : RegistrationNativeSuffixKeyPrf.Prefix → Bool) (provider : Provider KemSK)
    (outer : QueryImpl Combined ProbComp) (selected : Bool)

private theorem prepare_run (message : Message) (before : State n KemSK) :
    (localImpl setup wire route sign input inside provider outer selected (.inl message)).run before =
      pure ((input message).map (fun _ => message), { before with flags := Function.update before.flags message (input message).isSome }) := by
  simp only [localImpl, QueryImpl.compose, RegistrationNativeSecretWordInterface.liftLocal,
    simulateQ_spec_query, RegistrationNativeSecretWordTargetSource.implementation,
    QueryImpl.mapStateTBase, StateT.run_mk]
  rw [RegistrationNativeSecretWordInterpreter.prepare_run, simulateQ_pure]

private theorem root_echo (binding : session.RegistrationBinding)
    (collected : RegistrationNativeSecretWordServerCollect.Input registration.InitPacket Unit PqxdhJointIdentity.PeerEncoding)
    (ready : ServerReady) (before after : Auxiliary n KemSK)
    (supported : (.ok (some ready), after) ∈ support
      ((lower (localImpl setup wire route sign input inside provider outer selected)
        (StateT.lift (simulateQ prepare (RegistrationNativeSecretWordServerRoot.client binding collected)))).run before)) :
    ready.reference = RegistrationNativeSecretWordServerRoot.message collected := by
  classical
  simp only [RegistrationNativeSecretWordServerRoot.client] at supported
  split at supported
  · simp only [simulateQ_pure, lift_pure, lower_pure, StateT.run_pure, mem_support_pure_iff] at supported
    cases supported
  · simp only [bind_pure_comp, simulateQ_map, simulateQ_spec_query,
      RegistrationNativeSecretWordTargetServerExecution.lower_run, StateT.run_lift,
      simulateQ_map, StateT.run_map, Functor.map_map, support_map] at supported
    obtain ⟨result, reached, equal⟩ := supported
    change result ∈ support ((localImpl setup wire route sign input inside provider outer selected
      (.inl (RegistrationNativeSecretWordServerRoot.message collected))).run before.2) at reached
    rw [prepare_run, mem_support_pure_iff] at reached
    cases formed : input (RegistrationNativeSecretWordServerRoot.message collected) with
    | none => simp only [formed, Option.map_none] at reached; cases reached; cases equal
    | some key =>
        simp only [formed, Option.map_some] at reached
        cases reached
        simp only [Option.map_some, Prod.mk.injEq, RustM.ok.injEq, Option.some.injEq] at equal
        exact (congrArg (fun value : ServerReady => value.reference) equal.1).symm

/-- The actual outer-interpreted successful agreement exposes its own supported collector, root reply and exact retained descriptor. -/
theorem agreement (checks : Checks) (packet : registration.InitPacket) (authenticated : registration.AuthenticatedInit)
    (before after : ServerState) (initial reached : Auxiliary n KemSK) (ready : ServerReady)
    (supported : ((.ok (some ready), after), reached) ∈ support
      ((lower (localImpl setup wire route sign input inside provider outer selected)
        ((RegistrationNativeSecretWordServerCompiler.agreement setup checks packet authenticated).run before)).run initial)) :
    ∃ collected middle,
      (some collected, middle) ∈ support
        ((lower (localImpl setup wire route sign input inside provider outer selected)
          (RegistrationNativeSecretWordServerCompiler.collect setup checks packet authenticated)).run initial) ∧
      (.ok (some ready), reached) ∈ support
        ((lower (localImpl setup wire route sign input inside provider outer selected)
          (StateT.lift (simulateQ prepare (RegistrationNativeSecretWordServerRoot.client authenticated.binding collected)))).run middle) ∧
      ready.reference = RegistrationNativeSecretWordServerRoot.message collected := by
  rw [agreement_program, lower_bind, StateT.run_bind, mem_support_bind_iff] at supported
  obtain ⟨⟨collected, middle⟩, called, supported⟩ := supported
  cases collected with
  | none => simp only [lower_pure, StateT.run_pure, mem_support_pure_iff] at supported; cases supported
  | some collected =>
      rw [lower_map, StateT.run_map, support_map] at supported
      obtain ⟨result, possible, equal⟩ := supported
      have pairEqual : result = (.ok (some ready), reached) :=
        Prod.ext (congrArg (fun result => result.1.1) equal) (congrArg (fun result => result.2) equal)
      rw [pairEqual] at possible
      exact ⟨collected, middle, called, possible,
        root_echo setup wire route sign input inside provider outer selected authenticated.binding collected ready middle reached possible⟩

private theorem after_origin (checks : Checks) (packet : registration.InitPacket) (authenticated : registration.AuthenticatedInit)
    (before after : ServerState) (initial reached : Auxiliary n KemSK) (handle : Nat)
    (supported : ((.ok (some handle), after), reached) ∈ support
      ((lower (localImpl setup wire route sign input inside provider outer selected)
        ((RegistrationNativeSecretWordServerCompiler.afterAuthentication setup checks packet authenticated).run before)).run initial)) :
    ∃ ready collected middle,
      after.sessions[handle]? = some (some ready) ∧
      (some collected, middle) ∈ support
        ((lower (localImpl setup wire route sign input inside provider outer selected)
          (RegistrationNativeSecretWordServerCompiler.collect setup checks packet authenticated)).run initial) ∧
      (.ok (some ready), reached) ∈ support
        ((lower (localImpl setup wire route sign input inside provider outer selected)
          (StateT.lift (simulateQ prepare (RegistrationNativeSecretWordServerRoot.client authenticated.binding collected)))).run middle) ∧
      ready.reference = RegistrationNativeSecretWordServerRoot.message collected := by
  rw [after_program] at supported
  split at supported
  · simp only [lower_pure, StateT.run_pure, mem_support_pure_iff] at supported; cases supported
  · split at supported
    · rw [lower_bind, StateT.run_bind, mem_support_bind_iff] at supported
      obtain ⟨⟨⟨prepared, current⟩, afterAgreement⟩, called, supported⟩ := supported
      cases prepared with
      | fail error | div => simp only [lower_pure, StateT.run_pure, mem_support_pure_iff] at supported; cases supported
      | ok prepared => cases prepared with
        | none => simp only [lower_pure, StateT.run_pure, mem_support_pure_iff] at supported; cases supported
        | some ready =>
            have inserted := retain_result (localImpl setup wire route sign input inside provider outer selected)
              ready current after afterAgreement reached handle supported
            obtain ⟨collected, middle, collectedSupport, rootSupport, echo⟩ :=
              agreement setup wire route sign input inside provider outer selected checks packet authenticated before current initial afterAgreement ready called
            refine ⟨ready, collected, middle, inserted.2, collectedSupport, ?_, echo⟩
            rw [inserted.1]
            exact rootSupport
    · simp only [lower_pure, StateT.run_pure, mem_support_pure_iff] at supported; cases supported

/-- Actual successful acceptance retains the authenticated collector and root continuation of the exact appended session under the same outer probability interpreter. -/
theorem accept (checks : Checks) (verify : MldsaTranscriptAuth.Verify) (packet : registration.InitPacket)
    (before after : ServerState) (initial reached : Auxiliary n KemSK) (handle : Nat)
    (supported : ((.ok (some handle), after), reached) ∈ support
      ((lower (localImpl setup wire route sign input inside provider outer selected)
        ((RegistrationNativeSecretWordServerCompiler.accept setup checks verify packet).run before)).run initial)) :
    ∃ events authenticated afterAuthentication ready collected middle,
      (.ok (events, .Accepted authenticated), afterAuthentication) ∈ support
        ((lower (localImpl setup wire route sign input inside provider outer selected)
          (StateT.lift (simulateQ effect (RegistrationAuthenticationCompiler.program setup.source.crypto verify before.pin packet)))).run initial) ∧
      after.sessions[handle]? = some (some ready) ∧
      (some collected, middle) ∈ support
        ((lower (localImpl setup wire route sign input inside provider outer selected)
          (RegistrationNativeSecretWordServerCompiler.collect setup checks packet authenticated)).run afterAuthentication) ∧
      (.ok (some ready), reached) ∈ support
        ((lower (localImpl setup wire route sign input inside provider outer selected)
          (StateT.lift (simulateQ prepare (RegistrationNativeSecretWordServerRoot.client authenticated.binding collected)))).run middle) ∧
      ready.reference = RegistrationNativeSecretWordServerRoot.message collected := by
  rw [RegistrationNativeSecretWordTargetServerReceipt.accept_program_source, lower_bind,
    StateT.run_bind, mem_support_bind_iff] at supported
  obtain ⟨⟨checked, middle⟩, authenticated, continued⟩ := supported
  cases checked with
  | fail error | div => simp only [lower_pure, StateT.run_pure, mem_support_pure_iff] at continued; cases continued
  | ok checked =>
      rcases checked with ⟨events, verdict⟩
      cases verdict <;> try {
        simp only [lower_pure, StateT.run_pure, mem_support_pure_iff] at continued
        cases continued }
      case Accepted accepted =>
        obtain ⟨ready, collected, afterCollection, retained, called, rooted, echo⟩ :=
          after_origin setup wire route sign input inside provider outer selected checks packet accepted before after middle reached handle continued
        exact ⟨events, accepted, middle, ready, collected, afterCollection, authenticated, retained, called, rooted, echo⟩

end BeaconcryptCore.Computational.RegistrationNativeSecretWordLiveServerOriginOuter
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordLiveServerOriginOuter.agreement' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordLiveServerOriginOuter.agreement
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordLiveServerOriginOuter.accept' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordLiveServerOriginOuter.accept
