-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSecretWordLiveServerOrigin

/-! A successful actual replay insertion returns the exact appended one-use handle. The complete collector and root-service continuation belong to the same agreement that produced that retained Ready. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSecretWordLiveServerOriginRetain
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeSecretWordMessage (Message ServerReady ServerState)
open RegistrationNativeSecretWord (Key)
open RegistrationNativeSecretWordInterpreter (Provider)
open RegistrationNativeSecretWordLiveServerRun (State Auxiliary close lower)
open RegistrationNativeSecretWordLiveServer (implementation)
variable {n : Nat} {ι KemSK : Type} {base : OracleSpec ι}

private theorem retained (ready : ServerReady) (before after : ServerState) (handle : Nat)
    (actual : RegistrationNativeSecretWordServerMaterial.retain ready before = .ok (some handle, after)) :
    handle = before.sessions.length ∧ after.sessions = before.sessions ++ [some ready] := by
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
          exact ⟨rfl, rfl⟩

variable (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (input : Message → Option Key) (inside : RegistrationNativeSuffixKeyPrf.Prefix → Bool) (provider : Provider KemSK)
    (selected : Bool)

/-- A successful actual retained handle names precisely the appended Ready, while its complete current environment and private state remain unchanged. -/
theorem retain (ready : ServerReady) (before after : State n KemSK) (handle : Nat)
    (supported : (.ok (some handle), after) ∈ support
      ((close (implementation setup wire route sign input inside provider selected)
        (RegistrationNativeSecretWordServerCompiler.retain ready)).run before)) :
    after.2 = before.2 ∧ after.1.sessions[handle]? = some (some ready) := by
  rw [RegistrationNativeSecretWordLiveServerRun.retain_run] at supported
  cases actual : RegistrationNativeSecretWordServerMaterial.retain ready before.1 with
  | fail error | div => simp only [actual, mem_support_pure_iff] at supported; cases supported
  | ok pair =>
      rcases pair with ⟨reply, current⟩
      simp only [actual, mem_support_pure_iff, Prod.mk.injEq, RustM.ok.injEq] at supported
      obtain ⟨replyEqual, stateEqual⟩ := supported
      subst after
      rw [← replyEqual] at actual
      have shape := retained ready before.1 current handle actual
      refine ⟨rfl, ?_⟩
      rw [shape.2, shape.1]
      simp only [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self, List.getElem?_cons_zero]

/-- Replay admission retains the very same successful collector/root-client continuation that supplies its returned handle. -/
theorem afterAuthentication (checks : Checks) (packet : registration.InitPacket)
    (authenticated : registration.AuthenticatedInit) (before after : State n KemSK) (handle : Nat)
    (supported : (.ok (some handle), after) ∈ support
      ((close (implementation setup wire route sign input inside provider selected)
        (RegistrationNativeSecretWordServerCompiler.afterAuthentication setup checks packet authenticated)).run before)) :
    ∃ ready collected middle,
      after.1.sessions[handle]? = some (some ready) ∧
      (some collected, middle) ∈ support
        ((lower (implementation setup wire route sign input inside provider selected)
          (RegistrationNativeSecretWordServerCompiler.collect setup checks packet authenticated)).run before.2) ∧
      (.ok (some ready), after.2.2) ∈ support
        ((simulateQ (RegistrationNativeSecretWordLiveRoot.preparation setup wire route sign input inside provider)
          (RegistrationNativeSecretWordServerRoot.client authenticated.binding collected)).run middle.2) ∧
      ready.reference = RegistrationNativeSecretWordServerRoot.message collected := by
  rw [RegistrationNativeSecretWordLiveServerRun.after_run] at supported
  split at supported
  · rw [mem_support_pure_iff] at supported; cases supported
  · split at supported
    · rw [mem_support_bind_iff] at supported
      obtain ⟨completed, reached, supported⟩ := supported
      cases completedEq : completed.1 with
      | fail error | div => simp only [completedEq, mem_support_pure_iff] at supported; cases supported
      | ok value => cases value with
        | none => simp only [completedEq, mem_support_pure_iff] at supported; cases supported
        | some ready =>
            simp only [completedEq] at supported
            have inserted := retain setup wire route sign input inside provider selected ready completed.2 after handle supported
            have agreementSupport : (.ok (some ready), completed.2) ∈ support
                ((close (implementation setup wire route sign input inside provider selected)
                  (RegistrationNativeSecretWordServerCompiler.agreement setup checks packet authenticated)).run before) := by
              simpa only [← completedEq, Prod.mk.eta] using reached
            obtain ⟨collected, middle, called, rooted, echo⟩ := RegistrationNativeSecretWordLiveServerOrigin.agreement setup wire route sign input inside provider selected checks packet authenticated before completed.2 ready agreementSupport
            exact ⟨ready, collected, middle, inserted.2, called, congrArg Prod.snd inserted.1 ▸ rooted, echo⟩
    · rw [mem_support_pure_iff] at supported; cases supported

attribute [local irreducible] RegistrationAuthenticationCompiler.program

/-- Successful actual acceptance exposes its own authentication, collector, root reply and exact appended session, without a separate provenance premise. -/
theorem accept (checks : Checks) (verify : MldsaTranscriptAuth.Verify) (packet : registration.InitPacket)
    (before after : State n KemSK) (handle : Nat)
    (supported : (.ok (some handle), after) ∈ support
      ((close (implementation setup wire route sign input inside provider selected)
        (RegistrationNativeSecretWordServerCompiler.accept setup checks verify packet)).run before)) :
    ∃ events authenticated afterAuthentication ready collected middle,
      (.ok (events, .Accepted authenticated), afterAuthentication) ∈ support
        ((close (implementation setup wire route sign input inside provider selected)
          (StateT.lift (StateT.lift (simulateQ RegistrationNativeSecretWordInterface.effect
            (RegistrationAuthenticationCompiler.program setup.source.crypto verify before.1.pin packet))))).run before) ∧
      after.1.sessions[handle]? = some (some ready) ∧
      (some collected, middle) ∈ support
        ((lower (implementation setup wire route sign input inside provider selected)
          (RegistrationNativeSecretWordServerCompiler.collect setup checks packet authenticated)).run afterAuthentication.2) ∧
      (.ok (some ready), after.2.2) ∈ support
        ((simulateQ (RegistrationNativeSecretWordLiveRoot.preparation setup wire route sign input inside provider)
          (RegistrationNativeSecretWordServerRoot.client authenticated.binding collected)).run middle.2) ∧
      ready.reference = RegistrationNativeSecretWordServerRoot.message collected := by
  rw [RegistrationNativeSecretWordServerCompiler.accept,
    RegistrationNativeSecretWordLiveServerRun.close_bind, RegistrationNativeSecretWordLiveServerRun.close_get,
    pure_bind, RegistrationNativeSecretWordLiveServerRun.close_bind, mem_support_bind_iff] at supported
  obtain ⟨checked, reached, supported⟩ := supported
  cases checkedEq : checked.1 with
  | fail error | div =>
      simp only [checkedEq, RegistrationNativeSecretWordLiveServerRun.close_pure, mem_support_pure_iff] at supported
      cases supported
  | ok reply =>
      rcases reply with ⟨events, verdict⟩
      cases verdict <;> simp only [checkedEq] at supported
      all_goals try {
        rw [RegistrationNativeSecretWordLiveServerRun.close_pure, mem_support_pure_iff] at supported
        cases supported }
      case Accepted authenticated =>
        obtain ⟨ready, collected, middle, retained, called, rooted, echo⟩ :=
          afterAuthentication setup wire route sign input inside provider selected checks packet authenticated checked.2 after handle supported
        refine ⟨events, authenticated, checked.2, ready, collected, middle, ?_, retained, called, rooted, echo⟩
        simpa only [← checkedEq, Prod.mk.eta] using reached

end BeaconcryptCore.Computational.RegistrationNativeSecretWordLiveServerOriginRetain
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordLiveServerOriginRetain.retain' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordLiveServerOriginRetain.retain
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordLiveServerOriginRetain.afterAuthentication' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordLiveServerOriginRetain.afterAuthentication
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordLiveServerOriginRetain.accept' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordLiveServerOriginRetain.accept
