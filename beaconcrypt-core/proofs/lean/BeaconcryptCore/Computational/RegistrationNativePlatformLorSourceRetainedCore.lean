-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformLorSourcePhase
import BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetCollector
import BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetBeforeGetter
import BeaconcryptCore.Computational.RegistrationNativeSecretWordRootMetadata
import BeaconcryptCore.Computational.RegistrationNativeBeaconPublication
/-! The genuine source collector retains its matching marked ciphertext and opaque atom under the granular source KEM contract and arbitrary persistent World interpretation. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceRetainedCore
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeSecretWordMessage (Message ServerReady)
open RegistrationNativeSecretWord (Key Word)
open RegistrationNativeSecretWordInterface (Spec LocalSpec liftLocal)
open RegistrationServerReferenceCompiler (Environment)
open PqxdhKemIndCca
variable {n : Nat} {I KemSK Private A B : Type} {base : OracleSpec I}
abbrev Auxiliary (Private : Type) := Environment × Private

def lower (implementation : QueryImpl (LocalSpec n KemSK) (StateT Private ProbComp))
    (work : StateT Environment (OracleComp (LocalSpec n KemSK)) A) : StateT (Auxiliary Private) ProbComp A := fun before =>
  (fun result => (result.1.1,(result.1.2,result.2))) <$> (simulateQ implementation (work.run before.1)).run before.2

private theorem lower_run (implementation : QueryImpl (LocalSpec n KemSK) (StateT Private ProbComp))
    (work : StateT Environment (OracleComp (LocalSpec n KemSK)) A) (before : Auxiliary Private) :
    (lower implementation work).run before =
      (fun result => (result.1.1,(result.1.2,result.2))) <$> (simulateQ implementation (work.run before.1)).run before.2 := rfl

private theorem map_apply {S X Y : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (f : X → Y) (work : StateT S m X) (before : S) :
    (f <$> work) before = Prod.map f id <$> work before := StateT.run_map _ _ _
private theorem pure_apply {S X : Type} {m : Type → Type} [Monad m] (value : X) (before : S) :
    (pure value : StateT S m X) before = pure (value,before) := rfl

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

private theorem lower_program {J : Type} {queries : OracleSpec J}
    (implementation : QueryImpl (LocalSpec n KemSK) (StateT Private ProbComp))
    (compiler : QueryImpl queries (StateT Environment (OracleComp (LocalSpec n KemSK)))) (work : OracleComp queries A) :
    lower implementation (simulateQ compiler work) = simulateQ (fun query => lower implementation (compiler query)) work := by
  induction work using OracleComp.inductionOn with
  | pure value => simp only [simulateQ_pure,lower_pure]
  | query_bind query next ih =>
    simp only [simulateQ_bind,simulateQ_spec_query,lower_bind]
    congr 1
    funext reply
    exact ih reply

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

variable (setup : Setup base KemSK) (checks : Checks) (selected : Nat) (pairs : List (MlKem768PublicKey × KemSK))
    (publicKey : MlKem768PublicKey) (challenge : MlKem768Ciphertext)
    (implementation : QueryImpl (Spec n KemSK) (StateT Private ProbComp))
    (kem : Private → RegistrationNativeSecretWordKemProvider.State KemSK) (input : Message → Option Key)
    (contract : RegistrationNativePlatformLorSourceKem.Contract implementation kem input
      (RegistrationNativeSecretWordKemEarly.early setup.baseImpl setup.kem selected pairs publicKey challenge))
local notation "local" => implementation ∘ₛ RegistrationNativeSecretWordInterface.liftLocal true
local notation "prefix" => (fun query => lower local (RegistrationNativeSecretWordServerCompiler.prefixImpl setup checks query))
include contract

/-- The actual pre-getter prefix preserves its same absent marker without restricting World replies. -/
theorem before_phase (verified : PqxdhServerRootPreparation.Verified registration.InitPacket)
    (before : Auxiliary Private) (result : Option (PqxdhServerRootPreparation.Ephemeral Unit) × Auxiliary Private)
    (supported : result ∈ support ((lower local
      (simulateQ (RegistrationNativeSecretWordServerCompiler.prefixImpl setup checks)
        (RegistrationNativeSecretWordTargetCollector.beforeGetter verified))).run before)) :
    (kem result.2.2).2 = (kem before.2).2 := by
  simp only [lower_run,support_map] at supported
  obtain ⟨reached,called,equal⟩ := supported
  have actual := RegistrationNativePlatformLorSourcePhase.program_phase setup selected pairs publicKey challenge implementation kem input contract
    (simulateQ (RegistrationNativeSecretWordInterface.liftLocal true)
      ((simulateQ (RegistrationNativeSecretWordServerCompiler.prefixImpl setup checks)
        (RegistrationNativeSecretWordTargetCollector.beforeGetter verified)).run before.1))
    (RegistrationNativeSecretWordTargetBeforeGetter.before_free setup checks verified before.1) before.2 reached
    (by simpa only [QueryImpl.simulateQ_compose] using called)
  cases equal
  exact actual

omit contract in
private theorem pq_key (key : MlKem768PublicKey) :
    RegistrationRootInput.pqKey (RegistrationAgreementRoot.pqArray key) = key := by
  change RegistrationRootInput.pqKey (RegistrationNativeBeaconFrontend.pqArray key) = key
  exact RegistrationNativeBeaconPublication.pq_key key

omit contract in
private theorem getter_run (before : Auxiliary Private) :
    (lower local (RegistrationNativeSecretWordServerCompiler.prefixImpl setup checks (.encapsulate publicKey))).run before =
      if checks.kemKey publicKey then
        (fun result => (some (PqxdhAcceptedRegistration.ciphertextArray result.1.1,result.1.2),
          ({ before.1 with requests := before.1.requests ++ RegistrationWorldAgreement.recorded (.encapsulate (.Some (RegistrationAgreementRoot.pqArray publicKey))) },result.2))) <$>
          (implementation (.inl (.inr (.inr (.inr (.inr publicKey)))))).run before.2
      else pure (none,({ before.1 with requests := before.1.requests ++ RegistrationWorldAgreement.recorded (.encapsulate (.Some (RegistrationAgreementRoot.pqArray publicKey))) },before.2)) := by
  rw [lower_run]
  simp only [RegistrationNativeSecretWordServerCompiler.prefixImpl,StateT.run,pq_key]
  by_cases valid : checks.kemKey publicKey = true
  · simp only [valid,ite_true,simulateQ_map,map_apply,QueryImpl.compose,
      RegistrationNativeSecretWordInterface.localKem,simulateQ_spec_query,liftLocal,
      RegistrationNativeSecretWordInterface.route,RegistrationNativeSecretWordInterface.routedKem,
      ite_true,Functor.map_map,Prod.map_def,id_eq]
    rw [pq_key]
    rfl
  · simp only [valid,Bool.false_eq_true,ite_false,simulateQ_pure,pure_apply,map_pure]

/-- The exact optional getter returns its marked challenge and atom at the same reached provider state. -/
theorem getter_atom (before after : Auxiliary Private) (initial : (kem before.2).2 = none)
    (pair : PqxdhBeaconPhase2Preparation.Ciphertext × Word)
    (supported : (some pair,after) ∈ support ((lower local
      (RegistrationNativeSecretWordServerCompiler.prefixImpl setup checks (.encapsulate publicKey))).run before)) :
    pair = (PqxdhAcceptedRegistration.ciphertextArray challenge,Word.atom) := by
  rw [getter_run setup checks publicKey implementation] at supported
  split at supported
  · rw [support_map] at supported
    obtain ⟨reply,called,equal⟩ := supported
    have actual := contract.routed (.inr (.inr publicKey)) before.2 reply called
    simp only [RegistrationNativeSecretWordKemEarly.early,StateT.run,initial,ite_true,pure_bind,
      mem_support_bind_iff,mem_support_pure_iff] at actual
    obtain ⟨_dummy,_sampled,returned⟩ := actual
    have replyEqual : reply.1 = (challenge,Word.atom) := congrArg Prod.fst returned
    have option := congrArg Prod.fst equal
    simp only [replyEqual,Option.some.injEq] at option
    exact option.symm
  · simp only [mem_support_pure_iff,Prod.mk.injEq,reduceCtorEq,false_and] at supported

/-- Every successful source collection names the exact matching getter in that same run. -/
theorem collect_atom (packet : registration.InitPacket) (authenticated : registration.AuthenticatedInit)
    (before after : Auxiliary Private)
    (collected : RegistrationNativeSecretWordServerCollect.Input registration.InitPacket Unit PqxdhJointIdentity.PeerEncoding)
    (initial : (kem before.2).2 = none)
    (matching : (RegistrationRootInput.keys authenticated.registration).pqKey = publicKey)
    (supported : (some collected,after) ∈ support ((lower local
      (RegistrationNativeSecretWordServerCompiler.collect setup checks packet authenticated)).run before)) :
    collected.plain.verified = RegistrationRootInput.verified packet authenticated ∧
      collected.plain.ciphertext = PqxdhAcceptedRegistration.ciphertextArray challenge ∧ collected.kem = Word.atom := by
  rw [RegistrationNativeSecretWordServerCompiler.collect,lower_program] at supported
  obtain ⟨ephemeral,first,second,pair,earlier,getter,later,verified,ciphertext,word⟩ :=
    RegistrationNativeSecretWordTargetCollector.collect_receipt prefix (RegistrationRootInput.verified packet authenticated) before after collected supported
  have prefixSource : (some ephemeral,first) ∈ support ((lower local
      (simulateQ (RegistrationNativeSecretWordServerCompiler.prefixImpl setup checks)
        (RegistrationNativeSecretWordTargetCollector.beforeGetter (RegistrationRootInput.verified packet authenticated)))).run before) := by
    rw [lower_program]
    exact earlier
  have prefixMarker := before_phase setup checks selected pairs publicKey challenge implementation kem input contract _ before _ prefixSource
  have getterSource : (some pair,second) ∈ support ((lower local
      (RegistrationNativeSecretWordServerCompiler.prefixImpl setup checks (.encapsulate publicKey))).run first) := by
    change (some pair,second) ∈ support ((lower local
      (RegistrationNativeSecretWordServerCompiler.prefixImpl setup checks (.encapsulate (RegistrationRootInput.keys authenticated.registration).pqKey))).run first) at getter
    rw [matching] at getter
    exact getter
  have value := getter_atom setup checks selected pairs publicKey challenge implementation kem input contract first second (prefixMarker.trans initial) pair getterSource
  exact ⟨verified,ciphertext.trans (congrArg Prod.fst value),word.trans (congrArg Prod.snd value)⟩
/-- The same successful root reply stores its own prepared descriptor and original public agreement. -/
theorem root_fields (binding : session.RegistrationBinding)
    (collected : RegistrationNativeSecretWordServerCollect.Input registration.InitPacket Unit PqxdhJointIdentity.PeerEncoding)
    (ready : ServerReady) (before after : Auxiliary Private)
    (supported : (.ok (some ready),after) ∈ support ((lower local (StateT.lift
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

/-- Successful agreement exposes its own collector and root call at their exact reached private states. -/
theorem agreement_receipt (packet : registration.InitPacket) (authenticated : registration.AuthenticatedInit)
    (server afterServer : RegistrationNativeSecretWordMessage.ServerState) (before after : Auxiliary Private) (ready : ServerReady)
    (supported : ((.ok (some ready),afterServer),after) ∈ support
      ((lower local ((RegistrationNativeSecretWordServerCompiler.agreement setup checks packet authenticated).run server)).run before)) :
    ∃ collected middle,
      (some collected,middle) ∈ support ((lower local (RegistrationNativeSecretWordServerCompiler.collect setup checks packet authenticated)).run before) ∧
      (.ok (some ready),after) ∈ support ((lower local (StateT.lift (simulateQ RegistrationNativeSecretWordInterface.prepare
        (RegistrationNativeSecretWordServerRoot.client authenticated.binding collected)))).run middle) ∧
      ready.reference = RegistrationNativeSecretWordServerRoot.message collected ∧
      ready.agreement = ⟨PqxdhServerClearedRoot.pending authenticated.binding.server_pin.binding collected.plain,authenticated.binding⟩ := by
  rw [agreement_program,lower_bind,StateT.run_bind,mem_support_bind_iff] at supported
  obtain ⟨⟨collected,middle⟩,called,supported⟩ := supported
  cases collected with
  | none => simp only [lower_pure,StateT.run_pure,mem_support_pure_iff] at supported; cases supported
  | some collected =>
    rw [lower_map,StateT.run_map,support_map] at supported
    obtain ⟨result,possible,equal⟩ := supported
    have pairEqual : result = (.ok (some ready),after) := Prod.ext
      (congrArg (fun result => result.1.1) equal) (congrArg (fun result => result.2) equal)
    rw [pairEqual] at possible
    have fields := root_fields setup selected pairs publicKey challenge implementation kem input contract authenticated.binding collected ready middle after possible
    exact ⟨collected,middle,called,possible,fields⟩

end BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceRetainedCore

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceRetainedCore.before_phase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceRetainedCore.before_phase

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceRetainedCore.getter_atom' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceRetainedCore.getter_atom

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceRetainedCore.collect_atom' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceRetainedCore.collect_atom

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceRetainedCore.root_fields' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceRetainedCore.root_fields

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceRetainedCore.agreement_receipt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceRetainedCore.agreement_receipt
