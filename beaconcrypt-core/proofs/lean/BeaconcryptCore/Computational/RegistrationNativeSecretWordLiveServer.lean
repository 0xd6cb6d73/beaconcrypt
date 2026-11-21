-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSecretWordLiveServerRun
import BeaconcryptCore.Computational.RegistrationNativeSecretWordLiveSessions
import BeaconcryptCore.Computational.RegistrationNativeSecretWordMaterialSessions

/-! Actual Server preparation establishes the exact retained reference flag. Native replay retention extends the session invariant only with that reached receipt; every earlier prepared reference survives all intervening checked callbacks. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSecretWordLiveServer
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeSecretWordMessage (Message ServerReady)
open RegistrationNativeSecretWord (Key)
open RegistrationNativeSecretWordInterpreter (Provider)
open RegistrationNativeSecretWordInterpreterChecked (handlerChecked)
open RegistrationNativeSecretWordLiveFlags (Valid Keeps)
open RegistrationNativeSecretWordLiveSessions (Live)
open RegistrationNativeSecretWordLiveServerRun (State close)
variable {n : Nat} {ι KemSK Value : Type} {base : OracleSpec ι}
variable (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (input : Message → Option Key) (inside : RegistrationNativeSuffixKeyPrf.Prefix → Bool) (provider : Provider KemSK)
    (selected : Bool)

noncomputable def implementation : QueryImpl (RegistrationNativeSecretWordInterface.LocalSpec n KemSK)
    (RegistrationNativeSecretWordInterpreter.M n KemSK) :=
  handlerChecked setup wire route sign input inside provider ∘ₛ RegistrationNativeSecretWordInterface.liftLocal selected

/-- Every actual closed Server computation preserves all earlier descriptor flags and their optional-input validity. -/
theorem receipts (work : RegistrationNativeSecretWordServerCompiler.M n KemSK Value)
    (before : State n KemSK) (result : Value × State n KemSK) (valid : Valid input before.2.2)
    (supported : result ∈ support ((close (implementation setup wire route sign input inside provider selected) work).run before)) :
    Valid input result.2.2.2 ∧ Keeps before.2.2 result.2.2.2 := by
  rw [RegistrationNativeSecretWordLiveServerRun.close_program, support_map] at supported
  obtain ⟨reached, possible, equal⟩ := supported
  cases equal
  unfold implementation at possible
  rw [QueryImpl.simulateQ_compose] at possible
  have kept := RegistrationNativeSecretWordLiveFlags.program_receipts setup wire route sign input inside provider _ _ valid reached possible
  exact kept

private theorem preparation_program (work : OracleComp RegistrationNativeSecretWordMessage.PrepareSpec Value)
    (before : RegistrationNativeSecretWordInterpreter.State n KemSK) :
    (simulateQ (implementation setup wire route sign input inside provider selected)
      (simulateQ RegistrationNativeSecretWordInterface.prepare work)).run before =
    (simulateQ (RegistrationNativeSecretWordLiveRoot.preparation setup wire route sign input inside provider) work).run before := by
  rw [← QueryImpl.simulateQ_compose]
  congr 2

/-- Actual agreement leaves the local Server state unchanged and every successful returned Ready has a live flag. -/
theorem agreement (checks : Checks) (packet : registration.InitPacket)
    (authenticated : registration.AuthenticatedInit) (before : State n KemSK)
    (result : RustM (Option ServerReady) × State n KemSK)
    (supported : result ∈ support ((close (implementation setup wire route sign input inside provider selected)
      (RegistrationNativeSecretWordServerCompiler.agreement setup checks packet authenticated)).run before)) :
    result.2.1 = before.1 ∧ ∀ ready, result.1 = .ok (some ready) → result.2.2.2.flags ready.reference = true := by
  rw [RegistrationNativeSecretWordLiveServerRun.agreement_run, mem_support_bind_iff] at supported
  obtain ⟨collected, _possible, supported⟩ := supported
  cases formed : collected.1 with
  | none =>
      simp only [formed, mem_support_pure_iff] at supported
      cases supported
      exact ⟨rfl, fun _ impossible => by cases impossible⟩
  | some pending =>
      simp only [formed, support_map] at supported
      obtain ⟨reached, possible, equal⟩ := supported
      cases equal
      refine ⟨rfl, ?_⟩
      intro ready success
      rw [preparation_program] at possible
      apply RegistrationNativeSecretWordLiveRoot.server setup wire route sign input inside provider authenticated.binding pending ready collected.2.2 reached.2
      simpa only [← success, Prod.mk.eta] using possible

/-- Native replay retention preserves live sessions once supplied with its actual preparation receipt. -/
theorem retain (ready : ServerReady) (before : State n KemSK) (result : RustM (Option Nat) × State n KemSK)
    (live : Live before.1 before.2.2.flags) (prepared : before.2.2.flags ready.reference = true)
    (supported : result ∈ support ((close (implementation setup wire route sign input inside provider selected)
      (RegistrationNativeSecretWordServerCompiler.retain ready)).run before)) :
    Live result.2.1 result.2.2.2.flags := by
  rw [RegistrationNativeSecretWordLiveServerRun.retain_run] at supported
  cases actual : RegistrationNativeSecretWordServerMaterial.retain ready before.1 with
  | fail error =>
      simp only [actual, mem_support_pure_iff] at supported
      cases supported
      exact live
  | div =>
      simp only [actual, mem_support_pure_iff] at supported
      cases supported
      exact live
  | ok result =>
      rcases result with ⟨reply, after⟩
      simp only [actual, mem_support_pure_iff] at supported
      cases supported
      exact RegistrationNativeSecretWordLiveSessions.retain_live ready before.1 after before.2.2.flags live prepared reply actual

/-- Rejection, optional agreement failure and successful replay insertion all preserve preparation of every retained Server handle. -/
theorem afterAuthentication (checks : Checks) (packet : registration.InitPacket)
    (authenticated : registration.AuthenticatedInit) (before : State n KemSK)
    (result : RustM (Option Nat) × State n KemSK) (valid : Valid input before.2.2)
    (live : Live before.1 before.2.2.flags)
    (supported : result ∈ support ((close (implementation setup wire route sign input inside provider selected)
      (RegistrationNativeSecretWordServerCompiler.afterAuthentication setup checks packet authenticated)).run before)) :
    Live result.2.1 result.2.2.2.flags := by
  rw [RegistrationNativeSecretWordLiveServerRun.after_run] at supported
  split at supported
  · rw [mem_support_pure_iff] at supported
    cases supported
    exact live
  · split at supported
    · rw [mem_support_bind_iff] at supported
      obtain ⟨completed, reached, supported⟩ := supported
      have shape := agreement setup wire route sign input inside provider selected checks packet authenticated before completed reached
      have kept := receipts setup wire route sign input inside provider selected _ before completed valid reached
      have liveMiddle : Live completed.2.1 completed.2.2.2.flags := by
        rw [shape.1]
        exact RegistrationNativeSecretWordLiveSessions.mono _ _ _ kept.2 live
      cases completedEq : completed.1 with
      | fail error | div =>
          simp only [completedEq, mem_support_pure_iff] at supported
          cases supported
          exact liveMiddle
      | ok value => cases value with
        | none =>
            simp only [completedEq, mem_support_pure_iff] at supported
            cases supported
            exact liveMiddle
        | some ready =>
            simp only [completedEq] at supported
            exact retain setup wire route sign input inside provider selected ready completed.2 result liveMiddle
              (shape.2 ready completedEq) supported
    · rw [mem_support_pure_iff] at supported
      cases supported
      exact live

private theorem state_lift_apply {S X : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (work : m X) (state : S) : (StateT.lift work) state = (fun value => (value, state)) <$> work := by
  change (work >>= fun value => pure (value, state)) = _
  rw [bind_pure_comp]

private theorem state_map_apply {S X Y : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (observe : X → Y) (work : StateT S m X) (state : S) : (observe <$> work) state = Prod.map observe id <$> work state := by
  change (work state >>= fun result => pure (observe result.1, result.2)) = _
  rw [bind_pure_comp]
  rfl

private theorem effect_server (work : OracleComp (PqxdhRecordLiftInterface.EnvEffects n) Value)
    (before : State n KemSK) (result : Value × State n KemSK)
    (supported : result ∈ support ((close (implementation setup wire route sign input inside provider selected)
      (StateT.lift (StateT.lift (simulateQ RegistrationNativeSecretWordInterface.effect work)))).run before)) :
    result.2.1 = before.1 := by
  simp only [close, RegistrationNativeSecretWordLiveServerRun.lower, StateT.run, state_lift_apply,
    state_map_apply, simulateQ_map, Functor.map_map, Prod.map_def, id_eq, support_map] at supported
  obtain ⟨inner, _possible, equal⟩ := supported
  exact (congrArg (fun output => output.2.1) equal).symm

attribute [local irreducible] RegistrationAuthenticationCompiler.program

/-- Actual mandatory authentication, replay and preparation preserve the live-session invariant on every supported accept result. -/
theorem accept (checks : Checks) (verify : MldsaTranscriptAuth.Verify) (packet : registration.InitPacket)
    (before : State n KemSK) (result : RustM (Option Nat) × State n KemSK)
    (valid : Valid input before.2.2) (live : Live before.1 before.2.2.flags)
    (supported : result ∈ support ((close (implementation setup wire route sign input inside provider selected)
      (RegistrationNativeSecretWordServerCompiler.accept setup checks verify packet)).run before)) :
    Live result.2.1 result.2.2.2.flags := by
  rw [RegistrationNativeSecretWordServerCompiler.accept,
    RegistrationNativeSecretWordLiveServerRun.close_bind, RegistrationNativeSecretWordLiveServerRun.close_get,
    pure_bind, RegistrationNativeSecretWordLiveServerRun.close_bind, mem_support_bind_iff] at supported
  obtain ⟨checked, reached, supported⟩ := supported
  have same := effect_server setup wire route sign input inside provider selected
    (RegistrationAuthenticationCompiler.program setup.source.crypto verify before.1.pin packet) before checked reached
  have kept := receipts setup wire route sign input inside provider selected _ before checked valid reached
  have liveMiddle : Live checked.2.1 checked.2.2.2.flags := by
    rw [same]
    exact RegistrationNativeSecretWordLiveSessions.mono _ _ _ kept.2 live
  cases value : checked.1 with
  | fail error | div =>
      simp only [value, RegistrationNativeSecretWordLiveServerRun.close_pure, mem_support_pure_iff] at supported
      cases supported
      exact liveMiddle
  | ok checkedReply =>
      rcases checkedReply with ⟨events, verdict⟩
      cases verdict <;> simp only [value] at supported
      all_goals try {
        rw [RegistrationNativeSecretWordLiveServerRun.close_pure, mem_support_pure_iff] at supported
        cases supported
        exact liveMiddle }
      case Accepted authenticated =>
        exact afterAuthentication setup wire route sign input inside provider selected checks packet authenticated checked.2 result kept.1 liveMiddle supported

/-- Actual one-use completion never inserts a new descriptor, and every remaining session stays prepared through all publication callbacks. -/
theorem build (checks : Checks) (handle : Nat) (application : Option (Slice U8))
    (before : State n KemSK) (result : RegistrationNativeSecretWordServerMaterial.Result × State n KemSK)
    (valid : Valid input before.2.2) (live : Live before.1 before.2.2.flags)
    (supported : result ∈ support ((close (implementation setup wire route sign input inside provider selected)
      (RegistrationNativeSecretWordServerCompiler.build setup.source wire checks sign handle application)).run before)) :
    Live result.2.1 result.2.2.2.flags := by
  have kept := receipts setup wire route sign input inside provider selected _ before result valid supported
  rw [RegistrationNativeSecretWordLiveServerRun.close_program, support_map] at supported
  obtain ⟨reached, possible, equal⟩ := supported
  have localSupport : reached.1 ∈ support
      (((RegistrationNativeSecretWordServerCompiler.build (n := n) (KemSK := KemSK) setup.source wire checks sign handle application).run before.1).run before.2.1) := by
    apply OracleComp.support_simulateQ_run'_subset (implementation setup wire route sign input inside provider selected) _ before.2.2
    rw [StateT.run'_eq, support_map]
    exact Set.mem_image_of_mem Prod.fst possible
  have materialSupport : reached.1.1 ∈ support
      ((RegistrationNativeSecretWordServerMaterial.build (n := n) wire checks.reservePeer handle application).run before.1) := by
    apply OracleComp.support_simulateQ_run'_subset
      (RegistrationNativeSecretWordServerCompiler.service setup.source wire sign) _ before.2.1
    rw [StateT.run'_eq, support_map]
    exact Set.mem_image_of_mem Prod.fst localSupport
  have roster := RegistrationNativeSecretWordMaterialSessions.build_sessions wire checks.reservePeer handle application before.1 reached.1.1 materialSupport
  cases equal
  change Live reached.1.1.2 reached.2.flags
  intro ready member
  rw [roster] at member
  exact kept.2 ready.reference ((RegistrationNativeSecretWordLiveSessions.take_live handle before.1 before.2.2.flags live).1 ready member)

end BeaconcryptCore.Computational.RegistrationNativeSecretWordLiveServer
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordLiveServer.receipts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordLiveServer.receipts
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordLiveServer.agreement' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordLiveServer.agreement
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordLiveServer.retain' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordLiveServer.retain
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordLiveServer.afterAuthentication' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordLiveServer.afterAuthentication
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordLiveServer.accept' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordLiveServer.accept
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordLiveServer.build' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordLiveServer.build
