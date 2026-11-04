-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordOtherInstall
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordAtomServerFrontend
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordAtomServerCredit
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordAliasClient
/-! Every actual corrected typed/raw Word prefix conserves its same stored/future Server capability together with the chronological atom-attempt counter. The concrete new build spends the moved token and other callbacks cannot install Server peers. All original ledger, private provider and persistent platform coordinates remain in the traced run. -/
open OracleComp OracleSpec CoreModels Aeneas ENNReal
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordAtomServerAttempts
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeSecretWordMessage (Message)
open RegistrationNativeSecretWord (Key)
open RegistrationNativeSecretWordInterpreter (Provider)
open RegistrationNativeSecretWordService (Combined)
open RegistrationNativeSecretWordServiceCaps (Kind Counted)
variable {n : Nat} {I KemSK Platform E A Observation : Type} {base : OracleSpec I}

open RegistrationNativeSecretWordAtomSessionCredit (weight)
open RegistrationNativeSecretWordLifecycleCounter (available)
open RegistrationNativePlatformSecretWordExecution (TracedState drop)
open RegistrationNativePlatformSecretWordAtomServerCredit (credit cost)
open RegistrationNativeSecretWordAtomInstallTrace (count)


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
local notation "untraced" => RegistrationNativePlatformSecretWordExecution.typed setup wire route sign input inside provider outer controller
abbrev Front (source : RegistrationNativeMldsa.Source) (Platform : Type) := RegistrationNativePlatformSecretWordOrdinary.State source Platform

local notation "typed" => RegistrationNativePlatformSecretWordExecution.traced setup wire route sign input inside provider outer controller

private theorem trace_cost (query : RegistrationNativeRawAdapter.TypedSpec.Domain) (before : TracedState (Front source Platform) n KemSK)
    (result : RegistrationNativeRawAdapter.TypedSpec.Range query × TracedState (Front source Platform) n KemSK)
    (supported : result ∈ support ((typed query).run before)) :
    count .server result.2.2.1 ≤ count .server before.2.1 + cost query before.1 := by
  have observed := RegistrationNativePlatformSecretWordExecution.traced_support setup wire route sign input inside provider outer controller
    query before result supported
  cases query with
  | inl coin =>
    simpa only [cost, Nat.add_zero] using RegistrationNativeSecretWordAtomInstallTrace.free .server _
      (RegistrationNativePlatformSecretWordOtherInstall.other_free setup checks wire source sign selectedOwner selectedAccept publicPrekey
        view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer .server (.inl coin)
        (by simp [RegistrationNativeRawAdapter.kind]) before.1)
      before.2.1 ((result.1, result.2.1), result.2.2.1) observed
  | inr query => cases query with
    | build handle application =>
      simpa only [cost, ite_true, Nat.one_mul] using
        RegistrationNativePlatformSecretWordAtomServerFrontend.build_count setup checks wire source sign selectedOwner selectedAccept publicPrekey
          view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer .server handle application before.1
          before.2.1 ((result.1, result.2.1), result.2.2.1) observed
    | finish index packet =>
      simpa only [cost, Nat.add_zero] using RegistrationNativeSecretWordAtomInstallTrace.free .server _
        (RegistrationNativePlatformSecretWordOtherInstall.finish_server_free setup checks wire source sign selectedOwner selectedAccept publicPrekey
          view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer index packet before.1)
        before.2.1 ((result.1, result.2.1), result.2.2.1) observed
    | _ =>
      simpa only [cost, Nat.add_zero] using RegistrationNativeSecretWordAtomInstallTrace.free .server _
        (RegistrationNativePlatformSecretWordOtherInstall.other_free setup checks wire source sign selectedOwner selectedAccept publicPrekey
          view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer .server _
          (by simp [RegistrationNativeRawAdapter.kind]) before.1)
        before.2.1 ((result.1, result.2.1), result.2.2.1) observed

/-- The same actual source callback spends its retained/future Server credit for every chronological atom attempt. -/
theorem query_credit (query : RegistrationNativeRawAdapter.TypedSpec.Domain) (before : TracedState (Front source Platform) n KemSK)
    (result : RegistrationNativeRawAdapter.TypedSpec.Range query × TracedState (Front source Platform) n KemSK)
    (supported : result ∈ support ((typed query).run before)) :
    count .server result.2.2.1 + credit selectedAccept (drop result.2) ≤
      count .server before.2.1 + credit selectedAccept (drop before) := by
  have original : (result.1, drop result.2) ∈ support ((untraced query).run (drop before)) := by
    rw [← RegistrationNativePlatformSecretWordExecution.traced_source setup wire route sign input inside provider outer controller query before, support_map]
    exact Set.mem_image_of_mem (Prod.map id drop) supported
  have consumed := RegistrationNativePlatformSecretWordAtomServerCredit.query_credit setup checks wire source sign selectedOwner selectedAccept publicPrekey
    view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer route input inside kemSelected pairs publicKey challenge outer
    query (drop before) (result.1, drop result.2) original
  dsimp only [drop] at consumed ⊢
  have attempts := trace_cost setup checks wire source sign selectedOwner selectedAccept publicPrekey view failure allocation
    reserveRegistration reservePeer reserveFrame erased helper writer route input inside kemSelected pairs publicKey challenge outer query before result supported
  omega

/-- Every adaptive source prefix conserves that same complete chronological Server capability. -/
theorem program_credit (work : OracleComp RegistrationNativeRawAdapter.TypedSpec A) (before : TracedState (Front source Platform) n KemSK)
    (result : A × TracedState (Front source Platform) n KemSK)
    (supported : result ∈ support ((simulateQ typed work).run before)) :
    count .server result.2.2.1 + credit selectedAccept (drop result.2) ≤
      count .server before.2.1 + credit selectedAccept (drop before) := by
  induction work using OracleComp.inductionOn generalizing before with
  | pure value =>
    simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at supported
    cases supported
    exact Nat.le_refl _
  | query_bind query next ih =>
    rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at supported
    obtain ⟨middle, called, continued⟩ := supported
    exact (ih middle.1 middle.2 continued).trans
      (query_credit setup checks wire source sign selectedOwner selectedAccept publicPrekey view failure allocation
        reserveRegistration reservePeer reserveFrame erased helper writer route input inside kemSelected pairs publicKey challenge outer query before middle called)

/-- Initialized actual raw compilation has at most one Server atom installation attempt on every outcome, including failed publication. -/
theorem run_one (serverKeyId : U64) (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) A) (front : Front source Platform)
    (privateState : RegistrationNativeSecretWordInterpreter.State n KemSK)
    (sessions : front.1.server.sessions = []) (parsed : front.1.parsedAccepts = 0)
    (result : A × (RegistrationNativeLedger.State × TracedState (Front source Platform) n KemSK))
    (supported : result ∈ support (RegistrationNativeFullCompiler.run setup.source.crypto wire serverKeyId bounds typed mode work
      (front, RegistrationNativeSecretWordFrontendTrace.initial, privateState))) :
    count .server result.2.2.2.1 ≤ 1 := by
  rw [RegistrationNativeFullCompiler.compile_run, support_map] at supported
  obtain ⟨reached, called, equal⟩ := supported
  cases equal
  have conserved := program_credit setup checks wire source sign selectedOwner selectedAccept publicPrekey view failure allocation
    reserveRegistration reservePeer reserveFrame erased helper writer route input inside kemSelected pairs publicKey challenge outer _
    (front, RegistrationNativeSecretWordFrontendTrace.initial, privateState) reached called
  simp only [credit, drop, count, sessions, parsed, RegistrationNativeSecretWordAtomSessionCredit.count,
    available, Nat.zero_le, ite_true, RegistrationNativeSecretWordFrontendTrace.initial, List.countP_nil, Nat.zero_add] at conserved
  dsimp only
  unfold count
  omega

/-- The actual complete candidate-independent new client has at most one Server atom attempt under arbitrary outer table replies. -/
theorem client_one (serverKeyId : U64) (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) A) (front : Front source Platform)
    (ordinary : RegistrationNativePublicInterpreter.State n KemSK) (kem : RegistrationNativeSecretWordKemProvider.State KemSK)
    (sessions : front.1.server.sessions = []) (parsed : front.1.parsedAccepts = 0)
    (result : RegistrationNativePlatformSecretWordAliasClient.Result source n KemSK A Platform)
    (supported : result ∈ support (simulateQ outer (RegistrationNativePlatformSecretWordAliasClient.client setup checks wire source sign
      selectedOwner selectedAccept publicPrekey view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
      route input inside provider serverKeyId bounds mode work front ordinary kem))) :
    count .server result.1.2 ≤ 1 := by
  let canonical := RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire
  let localController := RegistrationNativePlatformSecretWordFrontend.handler (n := n) setup checks canonical source sign
    selectedOwner selectedAccept publicPrekey view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
  let initial := RegistrationNativeSecretWordInterpreter.initial ordinary kem
  have actual : result ∈ support ((simulateQ (RegistrationNativeSecretWordTargetSource.implementation setup canonical route sign input inside provider outer)
      (RegistrationNativeSecretWordFrontendTrace.program
        (RegistrationNativePlatformSecretWordFrontend.run (n := n) setup checks wire source sign selectedOwner selectedAccept publicPrekey
          view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer serverKeyId bounds mode work front))).run initial) := by
    change result ∈ support ((simulateQ (outer.mapStateTBase
      (RegistrationNativeSecretWordInterpreter.handler setup canonical route sign input inside provider))
      (RegistrationNativeSecretWordFrontendTrace.program
        (RegistrationNativePlatformSecretWordFrontend.run (n := n) setup checks wire source sign selectedOwner selectedAccept publicPrekey
          view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer serverKeyId bounds mode work front))).run initial)
    rw [← QueryImpl.simulateQ_mapStateTBase_run]
    exact supported
  change result ∈ support ((simulateQ (RegistrationNativeSecretWordTargetSource.implementation setup canonical route sign input inside provider outer)
    ((simulateQ RegistrationNativeSecretWordFrontendTrace.handler
      ((simulateQ localController (RegistrationNativeFullCompiler.compile setup.source.crypto canonical serverKeyId bounds mode work)).run front)).run
        RegistrationNativeSecretWordFrontendTrace.initial)).run initial) at actual
  rw [← RegistrationNativePlatformSecretWordExecution.run_trace setup canonical route sign input inside provider outer localController
    serverKeyId bounds mode work (front, RegistrationNativeSecretWordFrontendTrace.initial, initial), support_map] at actual
  obtain ⟨reached, called, equal⟩ := actual
  cases equal
  exact run_one setup checks canonical source sign selectedOwner selectedAccept publicPrekey view failure allocation reserveRegistration reservePeer reserveFrame
    erased helper writer route input inside kemSelected pairs publicKey challenge outer serverKeyId bounds mode work front initial sessions parsed reached called

end BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordAtomServerAttempts

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordAtomServerAttempts.query_credit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordAtomServerAttempts.query_credit

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordAtomServerAttempts.program_credit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordAtomServerAttempts.program_credit

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordAtomServerAttempts.run_one' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordAtomServerAttempts.run_one

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordAtomServerAttempts.client_one' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordAtomServerAttempts.client_one
