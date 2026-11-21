-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSecretWordLifecycleCounter
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordExecution
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordTargetCounter
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordAtomOrdinaryOpen
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordLiveState
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordLiveBuild
/-! The actual corrected common-state Word frontend conserves one total Server opaque-atom capability: its future selected accept credit or its same retained Ready. The real one-use take removes that capability before every source publication failure. -/
open OracleComp OracleSpec CoreModels Aeneas ENNReal
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordAtomServerCredit
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeSecretWordMessage (Message)
open RegistrationNativeSecretWord (Key)
open RegistrationNativeSecretWordInterpreter (Provider)
open RegistrationNativeSecretWordService (Combined)
open RegistrationNativeSecretWordServiceCaps (Kind Counted)
variable {n : Nat} {I KemSK Platform E A Observation : Type} {base : OracleSpec I}

open RegistrationNativeSecretWordAtomSessionCredit (count weight)
open RegistrationNativeSecretWordLifecycleCounter (available)
open RegistrationNativePlatformSecretWordExecution (State)


variable [primitive : BeaconcryptCore.Refinement.AdapterSealPrimitive.Operations]
    (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire) (source : RegistrationNativeMldsa.Source)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (selectedOwner selectedAccept : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
    (reserveFrame : Nat → StateT Platform ProbComp (core.result.Result Unit E)) (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (BeaconcryptCore.Refinement.AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))

variable (route : RawCtxServerRouting.SenderDecoder) (input : Message → Option Key)
    (inside : RegistrationNativeSuffixKeyPrf.Prefix → Bool) (kemSelected : Nat)
    (pairs : List (PqxdhKemIndCca.MlKem768PublicKey × KemSK)) (publicKey : PqxdhKemIndCca.MlKem768PublicKey)
    (challenge : PqxdhKemIndCca.MlKem768Ciphertext) (outer : QueryImpl Combined ProbComp)
local notation "provider" => RegistrationNativeSecretWordKemEarly.early setup.baseImpl setup.kem kemSelected pairs publicKey challenge
local notation "implementation" => RegistrationNativeSecretWordTargetSource.implementation (n := n) setup wire route sign input inside provider outer
local notation "controller" => RegistrationNativePlatformSecretWordFrontend.handler (n := n) setup checks wire source sign
  selectedOwner selectedAccept publicPrekey view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
local notation "typed" => RegistrationNativePlatformSecretWordExecution.typed setup wire route sign input inside provider outer controller
abbrev Front (source : RegistrationNativeMldsa.Source) (Platform : Type) := RegistrationNativePlatformSecretWordOrdinary.State source Platform

def credit {source : RegistrationNativeMldsa.Source} (selected : Nat) (before : State (Front source Platform) n KemSK) : Nat :=
  count before.1.1.server.sessions + available selected before.1.1.parsedAccepts

def cost {source : RegistrationNativeMldsa.Source} (query : RegistrationNativeRawAdapter.TypedSpec.Domain) (before : Front source Platform) : Nat :=
  match query with
  | .inr (.build handle _) => weight (RegistrationNativeSecretWordServerMaterial.take handle before.1.server).1
  | _ => 0

omit primitive in
private theorem bind_apply {S X Y : Type} {m : Type → Type} [Monad m]
    (work : StateT S m X) (next : X → StateT S m Y) (before : S) :
    (work >>= next) before = (work before >>= fun reached => next reached.1 reached.2) := rfl
omit primitive in
private theorem get_apply {S : Type} {m : Type → Type} [Monad m]
    (before : S) : (get : StateT S m S) before = pure (before, before) := rfl
omit primitive in
private theorem modify_apply {S : Type} {m : Type → Type} [Monad m]
    (change : S → S) (before : S) : (modify change : StateT S m Unit) before = pure ((), change before) := rfl
omit primitive in
private theorem map_apply {S X Y : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (observe : X → Y) (work : StateT S m X) (before : S) :
    (observe <$> work) before = Prod.map observe id <$> work before := StateT.run_map _ _ _
attribute [local irreducible] RegistrationNativePlatformSecretWordOpen.accept

private theorem accept_run (packet : registration.InitPacket) (before : State (Front source Platform) n KemSK) :
    (typed (.inr (.accept packet))).run before =
      (fun result => (result.1, (({ before.1.1 with server := result.2.1, environment := result.2.2.1, parsedAccepts := before.1.1.parsedAccepts + 1 }, result.2.2.2.1), result.2.2.2.2))) <$>
        (RegistrationNativePlatformSecretWordAtomOpenRun.close implementation
          (RegistrationNativePlatformSecretWordOpen.accept
            (RegistrationNativePlatformSecretWordFrontendView.wordLocal (decide (before.1.1.parsedAccepts = selectedAccept)))
            (RegistrationNativePlatformSecretWordOrdinary.platform reserveRegistration) setup checks source.verify packet)).run
          (before.1.1.server, (before.1.1.environment, (before.1.2, before.2))) := by
  rw [RegistrationNativePlatformSecretWordExecution.typed_run]
  simp only [RegistrationNativePlatformSecretWordFrontend.handler, RegistrationNativePlatformSecretWordFrontend.accept,
    bind_apply, get_apply, modify_apply, pure_bind,
    RegistrationNativePlatformSecretWordFrontend.serverOpen, RegistrationNativePlatformSecretWordAtomOpenRun.close,
    StateT.run, simulateQ_map, map_apply, Functor.map_map]
  rfl

/-- The actual interpreted callback increments the original public accept ordinal exactly once, including failed prefixes. -/
theorem query_counter (query : RegistrationNativeRawAdapter.TypedSpec.Domain) (before : State (Front source Platform) n KemSK)
    (result : RegistrationNativeRawAdapter.TypedSpec.Range query × State (Front source Platform) n KemSK)
    (supported : result ∈ support ((typed query).run before)) :
    result.2.1.1.parsedAccepts = before.1.1.parsedAccepts + (RegistrationNativeSecretWordTargetCounter.isAccept query).toNat := by
  have original := RegistrationNativePlatformSecretWordExecution.typed_support setup wire route sign input inside provider outer controller query before result supported
  exact RegistrationNativePlatformSecretWordTargetCounter.handler_counter setup checks wire source sign selectedOwner selectedAccept
    publicPrekey view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer query before.1 (result.1, result.2.1) original

private theorem accept_credit (packet : registration.InitPacket) (before : State (Front source Platform) n KemSK)
    (result : RegistrationNativeRawAdapter.TypedSpec.Range (.inr (.accept packet)) × State (Front source Platform) n KemSK)
    (supported : result ∈ support ((typed (.inr (.accept packet))).run before)) :
    credit selectedAccept result.2 ≤ credit selectedAccept before := by
  rw [accept_run, support_map] at supported
  obtain ⟨reached, called, equal⟩ := supported
  cases equal
  have shape := RegistrationNativePlatformSecretWordAtomSessionShape.accept implementation setup checks
    (decide (before.1.1.parsedAccepts = selectedAccept)) (RegistrationNativePlatformSecretWordOrdinary.platform reserveRegistration)
    source.verify packet (before.1.1.server, (before.1.1.environment, (before.1.2, before.2))) reached called
  by_cases chosen : before.1.1.parsedAccepts = selectedAccept
  · have atMost := RegistrationNativeSecretWordAtomSessionShape.count_le _ _ _ shape
    simp only [credit, available, chosen]
    split_ifs <;> omega
  · have ordinary := RegistrationNativePlatformSecretWordAtomOrdinaryOpen.accept_count setup wire route sign input inside
      kemSelected pairs publicKey challenge outer (RegistrationNativePlatformSecretWordOrdinary.platform reserveRegistration)
      checks source.verify packet (before.1.1.server, (before.1.1.environment, (before.1.2, before.2))) reached
      (by simpa only [chosen, decide_false] using called)
    simp only [credit, ordinary, available]
    split_ifs <;> omega

private theorem build_credit (handle : Nat) (application : Option (Slice U8)) (before : State (Front source Platform) n KemSK)
    (result : RegistrationNativeRawAdapter.TypedSpec.Range (.inr (.build handle application)) × State (Front source Platform) n KemSK)
    (supported : result ∈ support ((typed (.inr (.build handle application))).run before)) :
    credit selectedAccept result.2 + cost (.inr (.build handle application)) before.1 = credit selectedAccept before := by
  have original := RegistrationNativePlatformSecretWordExecution.typed_support setup wire route sign input inside provider outer controller
    (.inr (.build handle application)) before result supported
  have sessions := RegistrationNativePlatformSecretWordLiveBuild.sessions setup sign view failure allocation erased helper writer reservePeer
    source handle application before.1 (result.1, result.2.1) original
  dsimp only at sessions
  have counter := query_counter setup checks wire source sign selectedOwner selectedAccept publicPrekey view failure allocation
    reserveRegistration reservePeer reserveFrame erased helper writer route input inside kemSelected pairs publicKey challenge outer
    (.inr (.build handle application)) before result supported
  simp only [RegistrationNativeSecretWordTargetCounter.isAccept, Bool.toNat_false, Nat.add_zero] at counter
  have moved := RegistrationNativeSecretWordAtomSessionCredit.take_credit handle before.1.1.server
  simp only [credit, cost, sessions, counter]
  omega

private theorem quiet_credit (query : RegistrationNativeRawAdapter.TypedSpec.Domain)
    (quiet : RegistrationNativeRawAdapter.kind query ≠ 3 ∧ RegistrationNativeRawAdapter.kind query ≠ 4)
    (increment : RegistrationNativeSecretWordTargetCounter.isAccept query = false)
    (before : State (Front source Platform) n KemSK)
    (result : RegistrationNativeRawAdapter.TypedSpec.Range query × State (Front source Platform) n KemSK)
    (supported : result ∈ support ((typed query).run before)) :
    credit selectedAccept result.2 = credit selectedAccept before := by
  have original := RegistrationNativePlatformSecretWordExecution.typed_support setup wire route sign input inside provider outer controller
    query before result supported
  have same := RegistrationNativePlatformSecretWordLiveState.quiet_server setup checks wire source sign selectedOwner selectedAccept
    publicPrekey view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer query quiet before.1 (result.1, result.2.1) original
  have counter := query_counter setup checks wire source sign selectedOwner selectedAccept publicPrekey view failure allocation
    reserveRegistration reservePeer reserveFrame erased helper writer route input inside kemSelected pairs publicKey challenge outer
    query before result supported
  dsimp only at same
  simp only [credit, same, counter, increment, Bool.toNat_false, Nat.add_zero]

/-- Each actual corrected typed call conserves stored/future opaque-atom credit, spending exactly the moved token before every build outcome. -/
theorem query_credit (query : RegistrationNativeRawAdapter.TypedSpec.Domain) (before : State (Front source Platform) n KemSK)
    (result : RegistrationNativeRawAdapter.TypedSpec.Range query × State (Front source Platform) n KemSK)
    (supported : result ∈ support ((typed query).run before)) :
    credit selectedAccept result.2 + cost query before.1 ≤ credit selectedAccept before := by
  cases query with
  | inl coin =>
    simpa only [cost, Nat.add_zero] using le_of_eq (quiet_credit setup checks wire source sign selectedOwner selectedAccept publicPrekey view failure allocation
      reserveRegistration reservePeer reserveFrame erased helper writer route input inside kemSelected pairs publicKey challenge outer
      (.inl coin) (by simp [RegistrationNativeRawAdapter.kind]) rfl before result supported)
  | inr query => cases query with
    | accept packet =>
      simpa only [cost, Nat.add_zero] using accept_credit setup checks wire source sign selectedOwner selectedAccept publicPrekey view failure allocation
        reserveRegistration reservePeer reserveFrame erased helper writer route input inside kemSelected pairs publicKey challenge outer packet before result supported
    | build handle application =>
      exact le_of_eq (build_credit setup checks wire source sign selectedOwner selectedAccept publicPrekey view failure allocation
        reserveRegistration reservePeer reserveFrame erased helper writer route input inside kemSelected pairs publicKey challenge outer handle application before result supported)
    | _ =>
      simpa only [cost, Nat.add_zero] using le_of_eq (quiet_credit setup checks wire source sign selectedOwner selectedAccept publicPrekey view failure allocation
        reserveRegistration reservePeer reserveFrame erased helper writer route input inside kemSelected pairs publicKey challenge outer
        _ (by simp [RegistrationNativeRawAdapter.kind]) rfl before result supported)

end BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordAtomServerCredit

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordAtomServerCredit.query_counter' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordAtomServerCredit.query_counter

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordAtomServerCredit.query_credit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordAtomServerCredit.query_credit
