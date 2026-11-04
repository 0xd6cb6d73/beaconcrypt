-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceRetainedControl
import BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomSessionShape
/-! Corrected OPEN acceptance preserves its complete old capability table or appends exactly its returned Ready. This follows from the actual repeated-pin/authentication/reserve/collector/retain source, under arbitrary concrete private interpretation and all failures. No successful-admission or source-controller law is assumed. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceSessionShape
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeSecretWordMessage (ServerState ServerReady)
open RegistrationServerReferenceCompiler (Environment)
open RegistrationNativeSecretWordAtomSessionShape (Shape)
open RegistrationNativePlatformLorSourceRetainedControl (State close Work)
variable {n : Nat} {I KemSK Private A B : Type} {base : OracleSpec I}
variable (localImpl : QueryImpl (RegistrationNativeSecretWordInterface.LocalSpec n KemSK) (StateT Private ProbComp))

private theorem map_apply {S X Y : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (observe : X → Y) (work : StateT S m X) (before : S) :
    (observe <$> work) before = Prod.map observe id <$> work before := StateT.run_map _ _ _
private theorem lift_apply {S X : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (work : m X) (before : S) : (StateT.lift work : StateT S m X) before = (fun value => (value, before)) <$> work :=
  bind_pure_comp _ _

private theorem bind_apply {S X Y : Type} {m : Type → Type} [Monad m]
    (work : StateT S m X) (next : X → StateT S m Y) (before : S) :
    (work >>= next) before = (work before >>= fun result => next result.1 result.2) := rfl
private theorem pure_apply {S X : Type} {m : Type → Type} [Monad m]
    (value : X) (before : S) : (pure value : StateT S m X) before = pure (value,before) := rfl
private theorem get_apply {S : Type} {m : Type → Type} [Monad m]
    (before : S) : (get : StateT S m S) before = pure (before,before) := rfl

private theorem pure_run (value : A) (before : State Private) :
    (close (pure value)).run before = pure (value,before) := by
  simp only [close,StateT.run,pure_apply,map_pure]
private theorem get_run (before : State Private) :
    (close get).run before = pure (before.1,before) := by
  simp only [close,StateT.run,get_apply,pure_apply,map_pure]
private theorem bind_run (work : Work Private A) (next : A → Work Private B) (before : State Private) :
    (close (work >>= next)).run before = (do let reached ← (close work).run before; (close (next reached.1)).run reached.2) := by
  simp only [close,StateT.run,bind_apply,map_bind,bind_map_left]
private theorem retain_run (ready : ServerReady) (before : State Private) :
    (close (RegistrationNativePlatformSecretWordOpen.retain ready)).run before =
      match RegistrationNativeSecretWordServerMaterial.retain ready before.1 with
      | .fail error => pure (.fail error,before)
      | .div => pure (.div,before)
      | .ok (reply,after) => pure (.ok reply,(after,before.2)) := by
  cases kept : RegistrationNativeSecretWordServerMaterial.retain ready before.1 <;>
    simp only [close,RegistrationNativePlatformSecretWordOpen.retain,kept,StateT.run,pure_apply,map_pure]

private theorem lifted_server (action : StateT Private ProbComp A) (before : State Private) (result : A × State Private)
    (supported : result ∈ support ((close (StateT.lift (StateT.lift action))).run before)) : result.2.1=before.1 := by
  simp only [close,StateT.run,lift_apply,map_apply,Functor.map_map,support_map] at supported
  obtain ⟨returned,_called,rfl⟩ := supported
  rfl

private theorem source_agreement_server (setup : Setup base KemSK) (checks : Checks) (packet : registration.InitPacket)
    (authenticated : registration.AuthenticatedInit) (before : ServerState) (env : Environment)
    (result : (RustM (Option ServerReady) × ServerState) × Environment)
    (supported : result ∈ support (((RegistrationNativeSecretWordServerCompiler.agreement (n := n) setup checks packet authenticated).run before).run env)) :
    result.1.2 = before := by
  simp only [RegistrationNativeSecretWordServerCompiler.agreement, StateT.run_bind, StateT.run_lift,
    bind_assoc, pure_bind, mem_support_bind_iff] at supported
  obtain ⟨collected, _possible, supported⟩ := supported
  cases formed : collected.1 with
  | none =>
    simp only [formed, StateT.run_pure, mem_support_pure_iff] at supported
    cases supported
    rfl
  | some pending =>
    simp only [formed, StateT.run, lift_apply, map_apply, Functor.map_map, support_map] at supported
    obtain ⟨returned, _possible, equal⟩ := supported
    exact (congrArg (fun result => result.1.2) equal).symm

/-- The actual ordered collector and root preparation change no retained Server capability. -/
private theorem agreement_server (setup : Setup base KemSK) (checks : Checks)
    (packet : registration.InitPacket) (authenticated : registration.AuthenticatedInit)
    (before : State Private) (result : RustM (Option ServerReady) × State Private)
    (supported : result ∈ support ((close
      (RegistrationNativePlatformSecretWordOpen.agreement localImpl setup checks packet authenticated)).run before)) :
    result.2.1 = before.1 := by
  simp only [close,StateT.run,RegistrationNativePlatformSecretWordOpen.agreement,support_map] at supported
  obtain ⟨reached,called,equal⟩ := supported
  have possible : reached.1 ∈ support (((RegistrationNativeSecretWordServerCompiler.agreement (n := n) setup checks packet authenticated).run before.1).run before.2.1) := by
    apply OracleComp.support_simulateQ_run'_subset localImpl _ before.2.2
    rw [StateT.run'_eq,support_map]
    exact Set.mem_image_of_mem Prod.fst called
  have retained := source_agreement_server setup checks packet authenticated before.1 before.2.1 reached.1 possible
  cases equal
  exact retained

/-- One-use retention adds exactly its actual returned capability and leaves every older slot intact. -/
private theorem retain_shape (ready : ServerReady) (before : State Private)
    (result : RustM (Option Nat) × State Private)
    (supported : result ∈ support ((close (RegistrationNativePlatformSecretWordOpen.retain ready)).run before)) :
    Shape before.1.sessions result.1 result.2.1.sessions := by
  rw [retain_run] at supported
  cases consumed : RegistrationReplaySchedule.consume
      (RegistrationBoundGate.atRoot ready.agreement RegistrationBoundKeySchedule.zero) before.1.consumed with
  | fail error | div =>
    simp only [RegistrationNativeSecretWordServerMaterial.retain, consumed, mem_support_pure_iff] at supported
    cases supported
    exact Or.inl rfl
  | ok pair =>
    rcases pair with ⟨entry, history⟩
    cases entry with
    | none =>
      simp only [RegistrationNativeSecretWordServerMaterial.retain, consumed, mem_support_pure_iff] at supported
      cases supported
      exact Or.inl rfl
    | some token =>
      simp only [RegistrationNativeSecretWordServerMaterial.retain, consumed, mem_support_pure_iff] at supported
      cases supported
      exact Or.inr ⟨ready, rfl, rfl⟩

/-- Effectful reservation still precedes collection and the only possible capability append. -/
private theorem afterAuthentication (setup : Setup base KemSK) (checks : Checks)
    (reserve : StateT Private ProbComp Bool) (packet : registration.InitPacket) (authenticated : registration.AuthenticatedInit)
    (before : State Private) (result : RustM (Option Nat) × State Private)
    (supported : result ∈ support ((close
      (RegistrationNativePlatformSecretWordOpen.afterAuthentication localImpl reserve setup checks packet authenticated)).run before)) :
    Shape before.1.sessions result.1 result.2.1.sessions := by
  rw [RegistrationNativePlatformSecretWordOpen.afterAuthentication,
    bind_run,
    get_run, pure_bind] at supported
  split at supported
  · rw [pure_run, mem_support_pure_iff] at supported
    cases supported
    exact Or.inl rfl
  · rw [bind_run, mem_support_bind_iff] at supported
    obtain ⟨reserved, called, supported⟩ := supported
    have same := lifted_server reserve before reserved called
    cases allowed : reserved.1 with
    | false =>
      simp only [allowed, Bool.false_eq_true, ite_false,
        pure_run, mem_support_pure_iff] at supported
      cases supported
      exact Or.inl (congrArg (fun current => current.sessions) same)
    | true =>
      simp only [allowed, ite_true, bind_run,
        mem_support_bind_iff] at supported
      obtain ⟨accepted, reached, supported⟩ := supported
      have unchanged := agreement_server localImpl setup checks packet authenticated reserved.2 accepted reached
      have original : accepted.2.1 = before.1 := unchanged.trans same
      cases outcome : accepted.1 with
      | fail error | div =>
        simp only [outcome, pure_run, mem_support_pure_iff] at supported
        cases supported
        exact Or.inl (congrArg (fun current => current.sessions) original)
      | ok value => cases value with
        | none =>
          simp only [outcome, pure_run, mem_support_pure_iff] at supported
          cases supported
          exact Or.inl (congrArg (fun current => current.sessions) original)
        | some ready =>
          simp only [outcome] at supported
          have appended := retain_shape ready accepted.2 result supported
          simpa only [original] using appended

attribute [local irreducible] RegistrationAuthenticationCompiler.program
  RegistrationNativePlatformServerReferenceAccept.pin

/-- Mandatory authentication and repeated-pin failure preserve the same append-only shape. -/
private theorem afterPin (setup : Setup base KemSK) (checks : Checks)
    (reserve : StateT Private ProbComp Bool) (verify : MldsaTranscriptAuth.Verify) (packet : registration.InitPacket)
    (current : RegistrationNativeServerPinRecompute.PinReply)
    (before : State Private) (result : RustM (Option Nat) × State Private)
    (supported : result ∈ support ((close
      (RegistrationNativePlatformSecretWordOpen.afterPin localImpl reserve setup checks verify packet current)).run before)) :
    Shape before.1.sessions result.1 result.2.1.sessions := by
  cases current with
  | fail error | div =>
    rw [RegistrationNativePlatformSecretWordOpen.afterPin,
      pure_run, mem_support_pure_iff] at supported
    cases supported
    exact Or.inl rfl
  | ok value => cases value with
    | none =>
      rw [RegistrationNativePlatformSecretWordOpen.afterPin,
        pure_run, mem_support_pure_iff] at supported
      cases supported
      exact Or.inl rfl
    | some pin =>
      rw [RegistrationNativePlatformSecretWordOpen.afterPin,
        bind_run, mem_support_bind_iff] at supported
      obtain ⟨checked, called, supported⟩ := supported
      have same := lifted_server _ before checked called
      cases checkedEq : checked.1 with
      | fail error | div =>
        simp only [checkedEq, pure_run, mem_support_pure_iff] at supported
        cases supported
        exact Or.inl (congrArg (fun current => current.sessions) same)
      | ok checked =>
        rcases checked with ⟨events, verdict⟩
        cases verdict <;> simp only [checkedEq] at supported
        all_goals try {
          rw [pure_run, mem_support_pure_iff] at supported
          cases supported
          exact Or.inl (congrArg (fun current => current.sessions) same) }
        case Accepted authenticated =>
          have shape := afterAuthentication localImpl setup checks reserve packet authenticated _ result supported
          simpa only [same] using shape

/-- Every supported corrected accept preserves the old table or appends its exact returned Ready. -/
theorem accept (setup : Setup base KemSK) (checks : Checks)
    (reserve : StateT Private ProbComp Bool) (verify : MldsaTranscriptAuth.Verify) (packet : registration.InitPacket)
    (before : State Private) (result : RustM (Option Nat) × State Private)
    (supported : result ∈ support ((close
      (RegistrationNativePlatformSecretWordOpen.accept localImpl reserve setup checks verify packet)).run before)) :
    Shape before.1.sessions result.1 result.2.1.sessions := by
  rw [RegistrationNativePlatformSecretWordOpen.accept,
    bind_run,
    get_run, pure_bind,
    bind_run, mem_support_bind_iff] at supported
  obtain ⟨pinned, called, supported⟩ := supported
  have same := lifted_server _ before pinned called
  have shape := afterPin localImpl setup checks reserve verify packet pinned.1 pinned.2 result supported
  simpa only [same] using shape

private theorem retain_fresh (ready : RegistrationNativeSecretWordMessage.ServerReady) (before after : State Private) (handle : Nat)
    (supported : (.ok (some handle),after) ∈ support ((close (RegistrationNativePlatformSecretWordOpen.retain ready)).run before)) :
    handle=before.1.sessions.length := by
  rw [retain_run] at supported
  cases consumed : RegistrationReplaySchedule.consume
      (RegistrationBoundGate.atRoot ready.agreement RegistrationBoundKeySchedule.zero) before.1.consumed with
  | fail error | div =>
    simp only [RegistrationNativeSecretWordServerMaterial.retain,consumed,mem_support_pure_iff] at supported
    cases supported
  | ok pair =>
    rcases pair with ⟨entry,history⟩
    cases entry with
    | none =>
      simp only [RegistrationNativeSecretWordServerMaterial.retain,consumed,mem_support_pure_iff] at supported
      cases supported
    | some token =>
      simp only [RegistrationNativeSecretWordServerMaterial.retain,consumed,mem_support_pure_iff,
        Prod.mk.injEq,RustM.ok.injEq,Option.some.injEq] at supported
      exact supported.1

/-- Successful current source acceptance returns its exact new capability ordinal. -/
theorem fresh (setup : Setup base KemSK) (checks : Checks) (reserve : StateT Private ProbComp Bool)
    (verify : MldsaTranscriptAuth.Verify) (packet : registration.InitPacket) (before after : State Private) (handle : Nat)
    (supported : (.ok (some handle),after) ∈ support ((close
      (RegistrationNativePlatformSecretWordOpen.accept localImpl reserve setup checks verify packet)).run before)) :
    handle=before.1.sessions.length := by
  obtain ⟨pinned,pinAt,afterPinAt⟩ := RegistrationNativePlatformLorSourceRetainedControl.accept setup checks localImpl reserve packet verify before after handle supported
  have pinSame := lifted_server _ before pinned pinAt
  obtain ⟨pin,events,authenticated,checked,_pinReply,authenticatedAt,_checkedReply,afterAuthenticationAt⟩ :=
    RegistrationNativePlatformLorSourceRetainedControl.after_pin setup checks localImpl reserve packet verify pinned.1 pinned.2 after handle afterPinAt
  have authSame := lifted_server _ pinned.2 checked authenticatedAt
  obtain ⟨reserved,ready,agreed,reservedAt,_admitted,agreedAt,_agreedReply,retainedAt,_stored⟩ :=
    RegistrationNativePlatformLorSourceRetainedControl.after_authentication setup checks localImpl reserve packet authenticated checked.2 after handle afterAuthenticationAt
  have reserveSame := lifted_server reserve checked.2 reserved reservedAt
  have agreementSame := agreement_server localImpl setup checks packet authenticated reserved.2 agreed agreedAt
  have ordinal := retain_fresh ready agreed.2 after handle retainedAt
  rw [agreementSame,reserveSame,authSame,pinSame] at ordinal
  exact ordinal

end BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceSessionShape

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceSessionShape.accept' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceSessionShape.accept

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceSessionShape.fresh' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceSessionShape.fresh
