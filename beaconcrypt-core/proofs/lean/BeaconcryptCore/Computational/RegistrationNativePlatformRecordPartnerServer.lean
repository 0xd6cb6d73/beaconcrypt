-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerKem
import BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceRetainedCore
import BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceRetainedControl
import BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealStateLift
import BeaconcryptCore.Computational.RegistrationNativeSecretWordGenericLower

/-! An actual Server collector atom identifies the selected exposed getter. The ordinary public getter cannot manufacture it, and the actual root echo retains its collector's word. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerServer
open PqxdhServerAuthExperiment (Setup Checks)
open PqxdhKemIndCca
open RegistrationNativeSecretWord (Word Key)
open RegistrationNativeSecretWordInterface (LocalSpec liftLocal)
open RegistrationServerReferenceCompiler (Environment)
open RegistrationNativeSecretWordMessage (Message ServerReady)
open RegistrationNativeSecretWordGenericLower (Auxiliary lower lower_run)
variable {n : Nat} {I KemSK Private A B : Type} {base : OracleSpec I}
variable (setup : Setup base KemSK) (checks : Checks)
    (implementation : QueryImpl (RegistrationNativeSecretWordInterface.Spec n KemSK) (StateT Private ProbComp))
    (selected : Nat) (pairs : List (MlKem768PublicKey × KemSK)) (publicKey : MlKem768PublicKey) (challenge : MlKem768Ciphertext)
    (kem : Private → RegistrationNativeSecretWordKemProvider.State KemSK) (input : Message → Option Key)
    (contract : RegistrationNativePlatformLorSourceKem.Contract implementation kem input
      (RegistrationNativeSecretWordKemEarly.early setup.baseImpl setup.kem selected pairs publicKey challenge))
local notation "localImpl(" routed ")" => implementation ∘ₛ RegistrationNativeSecretWordInterface.liftLocal routed

private theorem map_apply {S X Y : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (f : X → Y) (work : StateT S m X) (before : S) :
    (f <$> work) before=Prod.map f id <$> work before := StateT.run_map _ _ _
private theorem pure_apply {S X : Type} {m : Type → Type} [Monad m] (value : X) (before : S) :
    (pure value : StateT S m X) before=pure (value,before) := rfl
private theorem pq_key (key : MlKem768PublicKey) :
    RegistrationRootInput.pqKey (RegistrationAgreementRoot.pqArray key)=key := by
  change RegistrationRootInput.pqKey (RegistrationNativeBeaconFrontend.pqArray key)=key
  exact RegistrationNativeBeaconPublication.pq_key key

private theorem lower_program {J B : Type} {queries : OracleSpec J} (routed : Bool)
    (inner : QueryImpl queries (StateT RegistrationServerReferenceCompiler.Environment
      (OracleComp (RegistrationNativeSecretWordInterface.LocalSpec n KemSK)))) (work : OracleComp queries B) :
    lower localImpl(routed) (simulateQ inner work)=simulateQ (fun query => lower localImpl(routed) (inner query)) work :=
  RegistrationNativePlatformLorIdealStateLift.simulate localImpl(routed) inner work

private def getterRaw (routed : Bool) (key : MlKem768PublicKey) : StateT Private ProbComp (MlKem768Ciphertext × Word) :=
  if routed then implementation (.inl (.inr (.inr (.inr (.inr key)))))
  else implementation (.inl (.inr (.inr (.inl (.inr key)))))

private theorem lower_pure (implementation : QueryImpl (LocalSpec n KemSK) (StateT Private ProbComp)) (value : A) :
    lower implementation (pure value) = pure value := by
  apply StateT.ext
  intro before
  simp only [lower,StateT.run,StateT.monad_pure_def,StateT.pure,simulateQ_pure,map_pure]

private theorem lower_bind (implementation : QueryImpl (LocalSpec n KemSK) (StateT Private ProbComp))
    (work : StateT Environment (OracleComp (LocalSpec n KemSK)) A)
    (next : A → StateT Environment (OracleComp (LocalSpec n KemSK)) B) :
    lower implementation (work >>= next) = (lower implementation work >>= fun value => lower implementation (next value)) := by
  apply StateT.ext
  intro before
  simp only [lower_run,StateT.run_bind,simulateQ_bind,map_bind,bind_map_left]

private theorem lower_map (implementation : QueryImpl (LocalSpec n KemSK) (StateT Private ProbComp))
    (observe : A → B) (work : StateT Environment (OracleComp (LocalSpec n KemSK)) A) :
    lower implementation (observe <$> work) = observe <$> lower implementation work := by
  apply StateT.ext
  intro before
  simp only [lower_run,StateT.run_map,simulateQ_map,Functor.map_map]

private theorem lift_pure (value : A) :
    (StateT.lift (pure value : OracleComp (LocalSpec n KemSK) A) : StateT Environment (OracleComp (LocalSpec n KemSK)) A) = pure value := by
  apply StateT.ext
  intro before
  simp only [StateT.run_lift,StateT.run_pure,pure_bind]

private theorem agreement_program (setup : Setup base KemSK) (checks : Checks) (packet : registration.InitPacket)
    (authenticated : registration.AuthenticatedInit) (server : RegistrationNativeSecretWordMessage.ServerState) :
    (RegistrationNativeSecretWordServerCompiler.agreement (n := n) setup checks packet authenticated).run server =
    (show StateT Environment (OracleComp (LocalSpec n KemSK)) (RustM (Option ServerReady) × RegistrationNativeSecretWordMessage.ServerState) from do
      let result ← RegistrationNativeSecretWordServerCompiler.collect setup checks packet authenticated
      match result with
      | none => pure (.ok none,server)
      | some collected =>
          (fun reply => (reply,server)) <$> StateT.lift
            (simulateQ RegistrationNativeSecretWordInterface.prepare
              (RegistrationNativeSecretWordServerRoot.client authenticated.binding collected))) := by
  apply StateT.ext
  intro env
  simp only [RegistrationNativeSecretWordServerCompiler.agreement,StateT.run_bind,StateT.run_lift,bind_pure_comp,bind_map_left]
  apply bind_congr
  intro result
  cases result.1 <;> rfl

omit contract in
private theorem getter_run (routed : Bool) (key : MlKem768PublicKey) (before : Auxiliary Private) :
    (lower localImpl(routed) (RegistrationNativeSecretWordServerCompiler.prefixImpl setup checks (.encapsulate key))).run before =
      if checks.kemKey key then
        (fun result => (some (PqxdhAcceptedRegistration.ciphertextArray result.1.1,result.1.2),
          ({before.1 with requests:=before.1.requests++RegistrationWorldAgreement.recorded (.encapsulate (.Some (RegistrationAgreementRoot.pqArray key)))},result.2))) <$>
          (getterRaw implementation routed key).run before.2
      else pure (none,({before.1 with requests:=before.1.requests++RegistrationWorldAgreement.recorded (.encapsulate (.Some (RegistrationAgreementRoot.pqArray key)))},before.2)) := by
  rw [lower_run]
  simp only [RegistrationNativeSecretWordServerCompiler.prefixImpl,StateT.run,pq_key]
  by_cases valid : checks.kemKey key=true
  · simp only [valid,ite_true,simulateQ_map,map_apply,QueryImpl.compose,
      RegistrationNativeSecretWordInterface.localKem,simulateQ_spec_query,RegistrationNativeSecretWordInterface.liftLocal,
      RegistrationNativeSecretWordInterface.route,Functor.map_map,Prod.map_def,id_eq]
    rw [pq_key]
    cases routed with
    | false => simp only [getterRaw,Bool.false_eq_true,ite_false,RegistrationNativeSecretWordInterface.routedKem,simulateQ_spec_query]; rfl
    | true => simp only [getterRaw,ite_true,RegistrationNativeSecretWordInterface.routedKem,simulateQ_spec_query]; rfl
  · simp only [valid,Bool.false_eq_true,ite_false,simulateQ_pure,pure_apply,map_pure]

include contract in
/-- A source getter carrying an atom necessarily uses the selected route and first matching challenge reply. -/
theorem getter_atom (routed : Bool) (key : MlKem768PublicKey) (before after : Auxiliary Private)
    (pair : PqxdhBeaconPhase2Preparation.Ciphertext × Word) (atom : pair.2=Word.atom)
    (supported : (some pair,after) ∈ support
      ((lower localImpl(routed) (RegistrationNativeSecretWordServerCompiler.prefixImpl setup checks (.encapsulate key))).run before)) :
    routed=true ∧ key=publicKey ∧ pair.1=PqxdhAcceptedRegistration.ciphertextArray challenge ∧ (kem before.2).2=none := by
  rw [getter_run setup checks implementation routed key before] at supported
  split at supported
  · rw [support_map] at supported
    obtain ⟨result,called,equal⟩ := supported
    have option := congrArg Prod.fst equal
    simp only [Option.some.injEq] at option
    have word : result.1.2=Word.atom := (congrArg Prod.snd option).trans atom
    have same : result.1=(result.1.1,Word.atom) := Prod.ext rfl word
    have equalResult : result=((result.1.1,Word.atom),result.2) := Prod.ext same rfl
    rw [equalResult] at called
    cases chosen : routed with
    | false =>
        simp only [getterRaw,chosen,Bool.false_eq_true,ite_false] at called
        exact False.elim (RegistrationNativePlatformRecordPartnerKem.public_getter setup selected pairs publicKey challenge implementation kem input contract
          key result.1.1 before.2 result.2 called)
    | true =>
        simp only [getterRaw,chosen,ite_true] at called
        have receipt := RegistrationNativePlatformRecordPartnerKem.getter setup selected pairs publicKey challenge implementation kem input contract
          key result.1.1 before.2 result.2 called
        exact ⟨rfl,receipt.2.1,(congrArg Prod.fst option).symm.trans (congrArg PqxdhAcceptedRegistration.ciphertextArray receipt.2.2),receipt.1⟩
  · simp only [mem_support_pure_iff,Prod.mk.injEq,reduceCtorEq,false_and] at supported

include contract in
/-- The atom of the literal successful collector comes from its same selected getter and challenge, with the actual prefix state retained. -/
theorem collect_atom (routed : Bool) (packet : registration.InitPacket) (authenticated : registration.AuthenticatedInit)
    (before after : Auxiliary Private)
    (collected : RegistrationNativeSecretWordServerCollect.Input registration.InitPacket Unit PqxdhJointIdentity.PeerEncoding)
    (atom : collected.kem=Word.atom)
    (supported : (some collected,after) ∈ support
      ((lower localImpl(routed) (RegistrationNativeSecretWordServerCompiler.collect setup checks packet authenticated)).run before)) :
    routed=true ∧ (RegistrationRootInput.keys authenticated.registration).pqKey=publicKey ∧
      collected.plain.ciphertext=PqxdhAcceptedRegistration.ciphertextArray challenge ∧
      ∃ first,(kem first.2).2=none ∧ ∃ pair second,
        pair.2=Word.atom ∧ (some pair,second) ∈ support
          ((lower localImpl(routed) (RegistrationNativeSecretWordServerCompiler.prefixImpl setup checks
            (.encapsulate (RegistrationRootInput.keys authenticated.registration).pqKey))).run first) := by
  rw [RegistrationNativeSecretWordServerCompiler.collect,lower_program] at supported
  obtain ⟨_ephemeral,first,second,pair,_earlier,getter,_later,_verified,ciphertext,word⟩ :=
    RegistrationNativeSecretWordTargetCollector.collect_receipt
      (fun query => lower localImpl(routed) (RegistrationNativeSecretWordServerCompiler.prefixImpl setup checks query))
      (RegistrationRootInput.verified packet authenticated) before after collected supported
  have actual := getter_atom setup checks implementation selected pairs publicKey challenge kem input contract
    routed _ first second pair (word.symm.trans atom) getter
  exact ⟨actual.1,actual.2.1,ciphertext.trans actual.2.2.1,first,actual.2.2.2,pair,second,word.symm.trans atom,getter⟩

include contract in
/-- The same successful root reply stores its own prepared descriptor and original public agreement. -/
theorem root_fields (routed : Bool) (binding : session.RegistrationBinding)
    (collected : RegistrationNativeSecretWordServerCollect.Input registration.InitPacket Unit PqxdhJointIdentity.PeerEncoding)
    (ready : ServerReady) (before after : Auxiliary Private)
    (supported : (.ok (some ready),after) ∈ support ((lower localImpl(routed) (StateT.lift
      (simulateQ RegistrationNativeSecretWordInterface.prepare (RegistrationNativeSecretWordServerRoot.client binding collected)))).run before)) :
    ready.reference = RegistrationNativeSecretWordServerRoot.message collected ∧
    ready.agreement = ⟨PqxdhServerClearedRoot.pending binding.server_pin.binding collected.plain,binding⟩ := by
  classical
  simp only [RegistrationNativeSecretWordServerRoot.client] at supported
  split at supported
  · simp only [simulateQ_pure,lift_pure,lower_pure,StateT.run_pure,mem_support_pure_iff] at supported
    cases supported
  · simp only [bind_pure_comp,simulateQ_map,simulateQ_spec_query,lower_run,StateT.run_lift,
      simulateQ_map,StateT.run_map,Functor.map_map,support_map] at supported
    obtain ⟨result,reached,equal⟩ := supported
    simp only [QueryImpl.compose,RegistrationNativeSecretWordInterface.prepare,RegistrationNativeSecretWordInterface.liftLocal,simulateQ_spec_query] at reached
    change result ∈ support ((implementation (.inl (.inl (RegistrationNativeSecretWordServerRoot.message collected)))).run before.2) at reached
    have echo := (contract.prepare (RegistrationNativeSecretWordServerRoot.message collected) before.2 result reached).1
    dsimp only at equal
    rw [echo] at equal
    cases formed : input (RegistrationNativeSecretWordServerRoot.message collected) with
    | none => simp [formed] at equal
    | some key =>
      simp only [formed,Option.map_some,Prod.mk.injEq,RustM.ok.injEq,Option.some.injEq] at equal
      exact ⟨(congrArg (fun value : ServerReady => value.reference) equal.1).symm,
        (congrArg (fun value : ServerReady => value.agreement) equal.1).symm⟩

include contract in
/-- A successful actual agreement retaining an atom uses the selected getter and that same collector's challenge ciphertext. -/
theorem agreement_atom (routed : Bool) (packet : registration.InitPacket) (authenticated : registration.AuthenticatedInit)
    (server afterServer : RegistrationNativeSecretWordMessage.ServerState) (before after : Auxiliary Private) (ready : ServerReady)
    (atom : ready.reference.kem=Word.atom)
    (supported : ((.ok (some ready),afterServer),after) ∈ support
      ((lower localImpl(routed) ((RegistrationNativeSecretWordServerCompiler.agreement setup checks packet authenticated).run server)).run before)) :
    routed=true ∧ (RegistrationRootInput.keys authenticated.registration).pqKey=publicKey ∧
      ∃ collected middle,
        (some collected,middle) ∈ support ((lower localImpl(routed)
          (RegistrationNativeSecretWordServerCompiler.collect setup checks packet authenticated)).run before) ∧
        ready.reference=RegistrationNativeSecretWordServerRoot.message collected ∧
        collected.plain.ciphertext=PqxdhAcceptedRegistration.ciphertextArray challenge := by
  rw [agreement_program,lower_bind,StateT.run_bind,mem_support_bind_iff] at supported
  obtain ⟨⟨collected,middle⟩,called,supported⟩ := supported
  cases collected with
  | none =>
      simp only [lower_pure,StateT.run_pure,mem_support_pure_iff] at supported
      cases supported
  | some collected =>
      rw [lower_map,StateT.run_map,support_map] at supported
      obtain ⟨result,possible,equal⟩ := supported
      have pairEqual : result=(.ok (some ready),after) := Prod.ext
        (congrArg (fun result => result.1.1) equal) (congrArg (fun result => result.2) equal)
      rw [pairEqual] at possible
      have fields := root_fields setup implementation selected pairs publicKey challenge kem input contract
        routed authenticated.binding collected ready middle after possible
      have word : collected.kem=Word.atom := by
        change (RegistrationNativeSecretWordServerRoot.message collected).kem=Word.atom
        rw [←fields.1]
        exact atom
      have getter := collect_atom setup checks implementation selected pairs publicKey challenge kem input contract
        routed packet authenticated before middle collected word called
      exact ⟨getter.1,getter.2.1,collected,middle,called,fields.1,getter.2.2.1⟩

include contract in
/-- The actual corrected OPEN agreement keeps the collector's atom provenance through its literal state-stack closing. -/
theorem open_agreement_atom (routed : Bool) (packet : registration.InitPacket) (authenticated : registration.AuthenticatedInit)
    (before after : RegistrationNativePlatformLorSourceRetainedControl.State Private) (ready : ServerReady)
    (atom : ready.reference.kem=Word.atom)
    (supported : (.ok (some ready),after) ∈ support
      ((RegistrationNativePlatformLorSourceRetainedControl.close
        (RegistrationNativePlatformSecretWordOpen.agreement localImpl(routed) setup checks packet authenticated)).run before)) :
    routed=true := by
  simp only [RegistrationNativePlatformLorSourceRetainedControl.close,RegistrationNativePlatformSecretWordOpen.agreement,
    StateT.run,support_map] at supported
  obtain ⟨reached,called,equal⟩ := supported
  have replyEq : reached.1.1.1=.ok (some ready) := congrArg Prod.fst equal
  have actual : ((.ok (some ready),reached.1.1.2),(reached.1.2,reached.2)) ∈ support
      ((lower localImpl(routed) ((RegistrationNativeSecretWordServerCompiler.agreement setup checks packet authenticated).run before.1)).run before.2) := by
    rw [lower_run,support_map]
    exact ⟨reached,called,by dsimp only; exact Prod.ext (Prod.ext replyEq rfl) rfl⟩
  exact (agreement_atom setup checks implementation selected pairs publicKey challenge kem input contract
    routed packet authenticated before.1 reached.1.1.2 before.2 (reached.1.2,reached.2) ready atom actual).1

attribute [local irreducible] RegistrationNativePlatformLorSourceRetainedControl.close
  RegistrationNativePlatformSecretWordOpen.accept RegistrationNativePlatformSecretWordOpen.afterPin
  RegistrationNativePlatformSecretWordOpen.afterAuthentication RegistrationNativePlatformSecretWordOpen.agreement
  RegistrationNativePlatformServerReferenceAccept.pin RegistrationAuthenticationCompiler.program

include contract in
/-- A successful corrected OPEN call storing an atom Ready must be its selected route, despite all preceding authentication and mutable reservation effects. -/
theorem accept_atom (routed : Bool) (verify : MldsaTranscriptAuth.Verify)
    (reserve : StateT Private ProbComp Bool) (packet : registration.InitPacket)
    (before after : RegistrationNativePlatformLorSourceRetainedControl.State Private) (handle : Nat) (ready : ServerReady)
    (stored : after.1.sessions[handle]?=some (some ready)) (atom : ready.reference.kem=Word.atom)
    (supported : (.ok (some handle),after) ∈ support
      ((RegistrationNativePlatformLorSourceRetainedControl.close
        (RegistrationNativePlatformSecretWordOpen.accept localImpl(routed) reserve setup checks verify packet)).run before)) :
    routed=true := by
  obtain ⟨pinned,_pin,afterPin⟩ := RegistrationNativePlatformLorSourceRetainedControl.accept
    setup checks localImpl(routed) reserve packet verify before after handle supported
  obtain ⟨_pin,_events,authenticated,checked,_current,_authenticated,_verdict,afterAuthentication⟩ :=
    RegistrationNativePlatformLorSourceRetainedControl.after_pin setup checks localImpl(routed) reserve packet
      verify pinned.1 pinned.2 after handle afterPin
  obtain ⟨reserved,current,agreed,_reserved,_admitted,reached,returned,_retained,found⟩ :=
    RegistrationNativePlatformLorSourceRetainedControl.after_authentication setup checks localImpl(routed) reserve packet
      authenticated checked.2 after handle afterAuthentication
  have same : current=ready := Option.some.inj (Option.some.inj (found.symm.trans stored))
  have currentAtom : current.reference.kem=Word.atom := by rw [same];exact atom
  have called : (.ok (some current),agreed.2) ∈ support
      ((RegistrationNativePlatformLorSourceRetainedControl.close
        (RegistrationNativePlatformSecretWordOpen.agreement localImpl(routed) setup checks packet authenticated)).run reserved.2) := by
    rw [←returned]
    exact reached
  exact open_agreement_atom setup checks implementation selected pairs publicKey challenge kem input contract
    routed packet authenticated reserved.2 agreed.2 current currentAtom called

end BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerServer

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerServer.getter_atom' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerServer.getter_atom

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerServer.collect_atom' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerServer.collect_atom

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerServer.root_fields' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerServer.root_fields

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerServer.agreement_atom' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerServer.agreement_atom

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerServer.open_agreement_atom' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerServer.open_agreement_atom

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerServer.accept_atom' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerServer.accept_atom
