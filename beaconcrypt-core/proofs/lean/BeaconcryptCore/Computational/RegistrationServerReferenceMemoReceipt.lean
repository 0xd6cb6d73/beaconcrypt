-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationServerOpenReferenceSourceAccept
import BeaconcryptCore.Computational.RegistrationNativeReferenceInterpreter

/-! Successful source preparation supplies an actual retained memo receipt for its returned public descriptor. The memo is private source interpretation state; no successful-prepare or live-token premise is added to the public experiment. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
namespace BeaconcryptCore.Computational.RegistrationServerReferenceMemoReceipt
open PqxdhServerAuthExperiment (Setup)
open RegistrationNativeKemReferenceEffects (Callbacks implementation)
open RegistrationNativeKemReferenceWorld (Private)
open RegistrationNativeRelatedFamily (Message)
open PqxdhSecretInputKdf (RootOutput)
variable {n : Nat} {ι KemSK : Type} {base : OracleSpec ι}
attribute [local irreducible] RegistrationAuthenticationExecutor.execute registration.begin_init_authentication

abbrev Memo := RegistrationNativeReferenceInterpreter.State

/-- A private memo may sit beside other bookkeeping; preparation updates only through this explicit internal lens. -/
class MemoStore (Extra : Type) where
  read : Extra → Memo
  remember : Extra → Message → Option RootOutput → Extra
  read_remember (before : Extra) (message : Message) (root : Option RootOutput) :
    read (remember before message root) message = root

instance : MemoStore Memo where
  read := id
  remember := Function.update
  read_remember := by
    intro before message root
    change Function.update before message root message = root
    exact Function.update_self _ _ _

def remember {Extra : Type} [MemoStore Extra] (before : Extra)
    (message : Message) (root : Option RootOutput) : Extra :=
  MemoStore.remember before message root

variable {Extra : Type} [MemoStore Extra]

private theorem state_pure_apply {S X : Type} {m : Type → Type} [Monad m]
    (value : X) (before : S) : (pure value : StateT S m X) before = pure (value, before) := rfl

private theorem state_bind_apply {S X Y : Type} {m : Type → Type} [Monad m]
    (work : StateT S m X) (next : X → StateT S m Y) (before : S) :
    (work >>= next) before = (do let result ← work before; next result.1 result.2) := rfl

/-- A real successful native reference preparation stores the actual returned source root at exactly its retained descriptor. -/
theorem client (setup : Setup base KemSK) (seed : PqxdhJointIdentity.IdentitySeed)
    (scalar : PqxdhJointGapDh.ScalarBytes) (services : Callbacks n KemSK Extra)
    (binding : session.RegistrationBinding)
    (input : PqxdhServerRootPreparation.Inputs registration.InitPacket Unit PqxdhJointIdentity.PeerEncoding)
    (ready : RegistrationServerReferenceRoot.Ready) (before after : Private n KemSK Extra)
    (supported : (.ok (some ready), after) ∈ support
      ((simulateQ (implementation setup (RegistrationServerOpenReferenceSourceStage.callbacks setup seed scalar remember services))
        (simulateQ RegistrationBeaconReferenceCompiler.prepare (RegistrationServerReferenceRoot.client binding input))).run before)) :
    ∃ root, MemoStore.read after.extra ready.reference = some root ∧
      RegistrationNativeSourceRoot.value setup.source setup.joint setup.dh seed scalar ready.reference = some root := by
  classical
  by_cases admitted : PqxdhServerRelatedRootInput.localNonzero input
  · simp only [RegistrationServerReferenceRoot.client, admitted, not_true_eq_false, ite_false,
      simulateQ_bind, simulateQ_spec_query, RegistrationBeaconReferenceCompiler.prepare,
      implementation, RegistrationNativeKemReferenceWorld.handler,
      RegistrationServerOpenReferenceSourceStage.callbacks, RegistrationServerOpenReferenceSourceStage.prepare,
      StateT.run, state_bind_apply, state_pure_apply, simulateQ_pure, pure_bind, support_pure,
      Set.mem_singleton_iff] at supported
    cases computed : RegistrationNativeSourceRoot.value setup.source setup.joint setup.dh seed scalar
        (Message.ofLegacy (PqxdhServerRelatedRootInput.message input)) with
    | none => simp only [computed, Option.map_none] at supported; cases supported
    | some root =>
        simp only [computed, Option.map_some, Prod.mk.injEq, RustM.ok.injEq, Option.some.injEq] at supported
        obtain ⟨readyEq, afterEq⟩ := supported
        subst ready
        subst after
        exact ⟨root, MemoStore.read_remember _ _ _, computed⟩
  · simp only [RegistrationServerReferenceRoot.client, admitted, not_false_eq_true, ite_true,
      simulateQ_pure, StateT.run_pure, mem_support_pure_iff, Prod.mk.injEq, RustM.ok.injEq] at supported
    cases supported.1

/-- Every actual successful Server agreement carries the root memo installed by its successful preparation, regardless of earlier collector outcomes. -/
theorem agreement (setup : Setup base KemSK) (checks : PqxdhServerAuthExperiment.Checks)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (services : Callbacks n KemSK Extra) (packet : registration.InitPacket)
    (authenticated : registration.AuthenticatedInit) (ready : RegistrationServerReferenceRoot.Ready)
    (before after : RegistrationNativeKemReferenceBackend.State n KemSK Extra)
    (supported : (.ok (some ready), after) ∈ support
      ((RegistrationServerOpenReferenceSourceStage.agreement setup checks seed scalar remember services packet authenticated).run before)) :
    ∃ root, MemoStore.read after.2.extra ready.reference = some root ∧
      RegistrationNativeSourceRoot.value setup.source setup.joint setup.dh seed scalar ready.reference = some root := by
  rw [RegistrationServerOpenReferenceSourceStage.agreement_run] at supported
  simp only [mem_support_bind_iff] at supported
  obtain ⟨collected, _possible, supported⟩ := supported
  cases collectedValue : collected.1 with
  | none => simp [collectedValue] at supported
  | some input =>
      simp only [collectedValue, support_map] at supported
      obtain ⟨prepared, possible, equal⟩ := supported
      simp only [Prod.mk.injEq] at equal
      have receipt := client setup seed scalar services authenticated.binding input ready collected.2.2 prepared.2
        (by simpa only [← equal.1] using possible)
      simpa only [← equal.2] using receipt

open RegistrationServerOpenReferenceSourceAccept (State close)

/-- Returning a fresh live handle stores the exact ready capability at that handle; the private memo is unchanged by owned retention. -/
theorem retain (setup : Setup base KemSK) (seed : PqxdhJointIdentity.IdentitySeed)
    (scalar : PqxdhJointGapDh.ScalarBytes) (services : Callbacks n KemSK Extra)
    (ready : RegistrationServerReferenceRoot.Ready) (handle : Nat) (before after : State n KemSK Extra)
    (supported : (.ok (some handle), after) ∈ support
      ((close setup seed scalar remember services (RegistrationServerOpenReferenceCompiler.retain ready)).run before)) :
    after.1.sessions[handle]? = some (some ready) ∧ after.2.2.extra = before.2.2.extra := by
  rw [RegistrationServerOpenReferenceSourceAccept.retain_run] at supported
  cases fresh : before.1.consumed.contains (absBytes ready.agreement.pending.registration_id.bytes) with
  | false =>
      simp only [RegistrationServerReferenceSourceRetain.retain,
        RegistrationServerOpenReferenceSourceAccept.project,
        RegistrationServerMaterialFrontend.retain_fresh ready before.1 fresh,
        StateT.run, support_map] at supported
      obtain ⟨result, equal, mapped⟩ := supported
      subst result
      simp only [Prod.mk.injEq, RustM.ok.injEq, Option.some.injEq] at mapped
      obtain ⟨handleEq, afterEq⟩ := mapped
      subst handle
      subst after
      constructor
      · simp only [List.getElem?_append, Nat.lt_irrefl, ↓reduceIte, Nat.sub_self, List.getElem?_cons_zero]
      · rfl
  | true =>
      simp only [RegistrationServerReferenceSourceRetain.retain,
        RegistrationServerOpenReferenceSourceAccept.project, RegistrationServerMaterialFrontend.retain,
        RegistrationReplaySchedule.consume_replayed (RegistrationServerReferenceRoot.atRoot ready RegistrationBoundKeySchedule.zero) before.1.consumed (by
          simpa only [RegistrationServerReferenceRoot.atRoot, RegistrationBoundGate.atRoot] using fresh),
        StateT.run, map_pure, mem_support_pure_iff, Prod.mk.injEq, RustM.ok.injEq] at supported
      cases supported.1

/-- A successful actual post-authentication accept returns a live token whose root is already in the actual private memo. -/
theorem after (setup : Setup base KemSK) (checks : PqxdhServerAuthExperiment.Checks)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (services : Callbacks n KemSK Extra) (packet : registration.InitPacket)
    (authenticated : registration.AuthenticatedInit) (handle : Nat) (before afterState : State n KemSK Extra)
    (supported : (.ok (some handle), afterState) ∈ support
      ((close setup seed scalar remember services
        (RegistrationServerOpenReferenceCompiler.afterAuthentication setup checks packet authenticated)).run before)) :
    ∃ ready root, afterState.1.sessions[handle]? = some (some ready) ∧
      MemoStore.read afterState.2.2.extra ready.reference = some root ∧
      RegistrationNativeSourceRoot.value setup.source setup.joint setup.dh seed scalar ready.reference = some root := by
  rw [RegistrationServerOpenReferenceSourceAccept.after_run] at supported
  split at supported
  · simp at supported
  · split at supported
    · simp only [mem_support_bind_iff] at supported
      obtain ⟨completed, possible, supported⟩ := supported
      cases accepted : completed.1 with
      | fail error => simp [accepted] at supported
      | div => simp [accepted] at supported
      | ok outcome =>
          cases outcome with
          | none => simp [accepted] at supported
          | some ready =>
              simp only [accepted] at supported
              have stored := retain setup seed scalar services ready handle completed.2 afterState supported
              rw [RegistrationServerOpenReferenceSourceAccept.agreement_run] at possible
              simp only [support_map] at possible
              obtain ⟨inner, possible, equal⟩ := possible
              have valueEq := congrArg Prod.fst equal
              have stateEq := congrArg Prod.snd equal
              have actual : inner.1 = .ok (some ready) := valueEq.trans accepted
              have reached : (.ok (some ready), inner.2) ∈ support
                  ((RegistrationServerOpenReferenceSourceStage.agreement setup checks seed scalar remember services packet authenticated).run before.2) := by
                simpa only [← actual] using possible
              obtain ⟨root, memo, computed⟩ := agreement setup checks seed scalar services packet authenticated ready before.2 inner.2 reached
              refine ⟨ready, root, stored.1, ?_, computed⟩
              rw [stored.2, ← stateEq]
              exact memo
    · simp at supported

/-- The literal full native accept entry returns only handles whose retained reference already has an actual source root memo. -/
theorem accept (setup : Setup base KemSK) (checks : PqxdhServerAuthExperiment.Checks)
    (verify : MldsaTranscriptAuth.Verify) (seed : PqxdhJointIdentity.IdentitySeed)
    (scalar : PqxdhJointGapDh.ScalarBytes) (services : Callbacks n KemSK Extra)
    (packet : registration.InitPacket) (handle : Nat) (before afterState : State n KemSK Extra)
    (supported : (.ok (some handle), afterState) ∈ support
      ((close setup seed scalar remember services
        (RegistrationServerOpenReferenceCompiler.accept setup checks verify packet)).run before)) :
    ∃ ready root, afterState.1.sessions[handle]? = some (some ready) ∧
      MemoStore.read afterState.2.2.extra ready.reference = some root ∧
      RegistrationNativeSourceRoot.value setup.source setup.joint setup.dh seed scalar ready.reference = some root := by
  rw [RegistrationServerOpenReferenceCompiler.accept,
    RegistrationServerOpenReferenceSourceAccept.close_bind,
    RegistrationServerOpenReferenceSourceAccept.close_get, pure_bind,
    RegistrationServerOpenReferenceSourceAccept.close_bind] at supported
  simp only [mem_support_bind_iff] at supported
  obtain ⟨checked, _possible, supported⟩ := supported
  cases checkedValue : checked.1 with
  | fail error => simp [checkedValue, RegistrationServerOpenReferenceSourceAccept.close_pure] at supported
  | div => simp [checkedValue, RegistrationServerOpenReferenceSourceAccept.close_pure] at supported
  | ok checkedReply =>
      rcases checkedReply with ⟨events, verdict⟩
      cases verdict <;> simp only [checkedValue] at supported
      all_goals try { simp [RegistrationServerOpenReferenceSourceAccept.close_pure] at supported }
      case Accepted authenticated =>
        exact after setup checks seed scalar services packet authenticated handle checked.2 afterState supported

end BeaconcryptCore.Computational.RegistrationServerReferenceMemoReceipt

/-- info: 'BeaconcryptCore.Computational.RegistrationServerReferenceMemoReceipt.client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationServerReferenceMemoReceipt.client

/-- info: 'BeaconcryptCore.Computational.RegistrationServerReferenceMemoReceipt.agreement' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationServerReferenceMemoReceipt.agreement

/-- info: 'BeaconcryptCore.Computational.RegistrationServerReferenceMemoReceipt.retain' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationServerReferenceMemoReceipt.retain
/-- info: 'BeaconcryptCore.Computational.RegistrationServerReferenceMemoReceipt.after' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationServerReferenceMemoReceipt.after

/-- info: 'BeaconcryptCore.Computational.RegistrationServerReferenceMemoReceipt.accept' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationServerReferenceMemoReceipt.accept
