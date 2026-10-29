-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeProviderAcceptRun
import BeaconcryptCore.Computational.RegistrationNativePublicSourceMemo

/-! Successful native Server preparation records the exact root under the returned reference, even when its collection used an arbitrary candidate KEM provider. These actual callback receipts compose through agreement, retention and authentication without replacing the provider by a real KEM interpretation. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeProviderMemoReceipt
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeProviderInterpreter (Provider)
open RegistrationNativeProviderSource (localImpl)
open RegistrationNativeProviderAcceptRun (State close)
open RegistrationNativeRelatedFamily (Message)
attribute [local irreducible] RegistrationAuthenticationCompiler.program
attribute [local irreducible] RegistrationNativeProviderSource.localImpl
variable {n : Nat} {ι KemSK ProviderState : Type} {base : OracleSpec ι}

theorem client (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (provider : Provider KemSK ProviderState) (selected : Bool) (binding : session.RegistrationBinding)
    (input : PqxdhServerRootPreparation.Inputs registration.InitPacket Unit PqxdhJointIdentity.PeerEncoding)
    (ready : RegistrationServerReferenceRoot.Ready)
    (before after : RegistrationNativeProviderInterpreter.State n KemSK ProviderState)
    (supported : (.ok (some ready), after) ∈ support
      ((simulateQ (localImpl setup wire route sign seed scalar provider selected)
        (simulateQ RegistrationBeaconReferenceCompiler.prepare (RegistrationServerReferenceRoot.client binding input))).run before)) :
    ∃ root, after.1.roots ready.reference = some root ∧
      RegistrationNativeSourceRoot.value setup.source setup.joint setup.dh seed scalar ready.reference = some root := by
  classical
  by_cases admitted : PqxdhServerRelatedRootInput.localNonzero input
  · simp only [RegistrationServerReferenceRoot.client, admitted, not_true_eq_false, ite_false,
      simulateQ_bind, simulateQ_spec_query, RegistrationBeaconReferenceCompiler.prepare,
      StateT.run_bind, simulateQ_pure, StateT.run_pure] at supported
    rw [RegistrationNativeProviderLocal.prepare_run] at supported
    simp only [pure_bind, mem_support_pure_iff] at supported
    cases computed : RegistrationNativeSourceRoot.value setup.source setup.joint setup.dh seed scalar
        (Message.ofLegacy (PqxdhServerRelatedRootInput.message input)) with
    | none => simp only [computed, Option.map_none] at supported; cases supported
    | some root =>
        simp only [computed, Option.map_some, Prod.mk.injEq, RustM.ok.injEq, Option.some.injEq] at supported
        obtain ⟨readyEq, afterEq⟩ := supported
        subst ready
        subst after
        exact ⟨root, Function.update_self _ _ _, computed⟩
  · simp only [RegistrationServerReferenceRoot.client, admitted, not_false_eq_true, ite_true,
      simulateQ_pure, StateT.run_pure, mem_support_pure_iff, Prod.mk.injEq, RustM.ok.injEq] at supported
    cases supported.1

/-- Successful agreement retains the root just prepared after the actual provider-dependent collection. -/
theorem agreement (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (provider : Provider KemSK ProviderState) (selected : Bool) (packet : registration.InitPacket)
    (authenticated : registration.AuthenticatedInit) (ready : RegistrationServerReferenceRoot.Ready)
    (before after : State n KemSK ProviderState)
    (supported : (.ok (some ready), after) ∈ support
      ((close (localImpl setup wire route sign seed scalar provider selected)
        (RegistrationServerOpenReferenceCompiler.agreement setup checks packet authenticated)).run before)) :
    ∃ root, after.2.2.1.roots ready.reference = some root ∧
      RegistrationNativeSourceRoot.value setup.source setup.joint setup.dh seed scalar ready.reference = some root := by
  rw [RegistrationNativeProviderAcceptRun.agreement_run] at supported
  simp only [mem_support_bind_iff] at supported
  obtain ⟨collected, _possible, supported⟩ := supported
  cases collectedValue : collected.1 with
  | none => simp [collectedValue] at supported
  | some input =>
      simp only [collectedValue, support_map] at supported
      obtain ⟨prepared, possible, equal⟩ := supported
      have output : prepared.1 = .ok (some ready) := congrArg Prod.fst equal
      have reached : prepared.2 = after.2.2 := congrArg (fun result => result.2.2.2) equal
      have receipt := client setup wire route sign seed scalar provider selected authenticated.binding input ready
        collected.2.2 prepared.2 (by simpa only [← output] using possible)
      simpa only [← reached] using receipt

theorem retain (implementation : QueryImpl (RegistrationBeaconReferenceCompiler.Spec n KemSK)
    (StateT (RegistrationNativeProviderInterpreter.State n KemSK ProviderState) ProbComp))
    (ready : RegistrationServerReferenceRoot.Ready) (handle : Nat) (before after : State n KemSK ProviderState)
    (supported : (.ok (some handle), after) ∈ support
      ((close implementation (RegistrationServerOpenReferenceCompiler.retain ready)).run before)) :
    after.1.sessions[handle]? = some (some ready) ∧ after.2 = before.2 := by
  rw [RegistrationNativeProviderAcceptRun.retain_run] at supported
  cases fresh : before.1.consumed.contains (absBytes ready.agreement.pending.registration_id.bytes) with
  | false =>
      rw [RegistrationServerMaterialFrontend.retain_fresh ready before.1 fresh] at supported
      simp only [mem_support_pure_iff, Prod.mk.injEq, RustM.ok.injEq, Option.some.injEq] at supported
      obtain ⟨handleEq, afterEq⟩ := supported
      subst handle
      subst after
      constructor
      · simp only [List.getElem?_append, Nat.lt_irrefl, ite_false, Nat.sub_self, List.getElem?_cons_zero]
      · rfl
  | true =>
      have replay := RegistrationReplaySchedule.consume_replayed
        (RegistrationServerReferenceRoot.atRoot ready RegistrationBoundKeySchedule.zero) before.1.consumed
          (by simpa only [RegistrationServerReferenceRoot.atRoot, RegistrationBoundGate.atRoot] using fresh)
      simp only [RegistrationServerMaterialFrontend.retain, replay, mem_support_pure_iff,
        Prod.mk.injEq, RustM.ok.injEq] at supported
      cases supported.1

theorem after (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (provider : Provider KemSK ProviderState) (selected : Bool) (packet : registration.InitPacket)
    (authenticated : registration.AuthenticatedInit) (handle : Nat) (before afterState : State n KemSK ProviderState)
    (supported : (.ok (some handle), afterState) ∈ support
      ((close (localImpl setup wire route sign seed scalar provider selected)
        (RegistrationServerOpenReferenceCompiler.afterAuthentication setup checks packet authenticated)).run before)) :
    ∃ ready root, afterState.1.sessions[handle]? = some (some ready) ∧
      afterState.2.2.1.roots ready.reference = some root ∧
      RegistrationNativeSourceRoot.value setup.source setup.joint setup.dh seed scalar ready.reference = some root := by
  rw [RegistrationNativeProviderAcceptRun.after_run] at supported
  split at supported
  · simp at supported
  · split at supported
    · simp only [mem_support_bind_iff] at supported
      obtain ⟨completed, possible, supported⟩ := supported
      cases accepted : completed.1 with
      | fail error | div => simp [accepted] at supported
      | ok outcome => cases outcome with
        | none => simp [accepted] at supported
        | some ready =>
            simp only [accepted] at supported
            have stored := retain (localImpl setup wire route sign seed scalar provider selected) ready handle completed.2 afterState supported
            have reached : (.ok (some ready), completed.2) ∈ support
                ((close (localImpl setup wire route sign seed scalar provider selected)
                  (RegistrationServerOpenReferenceCompiler.agreement setup checks packet authenticated)).run before) := by
              simpa only [← accepted] using possible
            obtain ⟨root, memo, computed⟩ := agreement setup checks wire route sign seed scalar provider selected
              packet authenticated ready before completed.2 reached
            exact ⟨ready, root, stored.1, by simpa only [stored.2] using memo, computed⟩
    · simp at supported

/-- A successful complete native accept returns a handle whose exact retained root was recorded by its actual provider-source preparation. -/
theorem accept (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (verify : MldsaTranscriptAuth.Verify) (seed : PqxdhJointIdentity.IdentitySeed)
    (scalar : PqxdhJointGapDh.ScalarBytes) (provider : Provider KemSK ProviderState) (selected : Bool)
    (packet : registration.InitPacket) (handle : Nat) (before afterState : State n KemSK ProviderState)
    (supported : (.ok (some handle), afterState) ∈ support
      ((close (localImpl setup wire route sign seed scalar provider selected)
        (RegistrationServerOpenReferenceCompiler.accept setup checks verify packet)).run before)) :
    ∃ ready root, afterState.1.sessions[handle]? = some (some ready) ∧
      afterState.2.2.1.roots ready.reference = some root ∧
      RegistrationNativeSourceRoot.value setup.source setup.joint setup.dh seed scalar ready.reference = some root := by
  rw [RegistrationServerOpenReferenceCompiler.accept, RegistrationNativeProviderAcceptRun.close_bind,
    RegistrationNativeProviderAcceptRun.close_get, pure_bind,
    RegistrationNativeProviderAcceptRun.close_bind] at supported
  simp only [mem_support_bind_iff] at supported
  obtain ⟨checked, _possible, supported⟩ := supported
  cases checkedValue : checked.1 with
  | fail error | div => simp [checkedValue, RegistrationNativeProviderAcceptRun.close_pure] at supported
  | ok checkedReply =>
      rcases checkedReply with ⟨events, verdict⟩
      cases verdict <;> simp only [checkedValue] at supported
      all_goals try { simp [RegistrationNativeProviderAcceptRun.close_pure] at supported }
      case Accepted authenticated =>
        exact after setup checks wire route sign seed scalar provider selected packet authenticated handle checked.2 afterState supported

end BeaconcryptCore.Computational.RegistrationNativeProviderMemoReceipt

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeProviderMemoReceipt.client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeProviderMemoReceipt.client
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeProviderMemoReceipt.agreement' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeProviderMemoReceipt.agreement
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeProviderMemoReceipt.retain' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeProviderMemoReceipt.retain
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeProviderMemoReceipt.after' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeProviderMemoReceipt.after
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeProviderMemoReceipt.accept' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeProviderMemoReceipt.accept
