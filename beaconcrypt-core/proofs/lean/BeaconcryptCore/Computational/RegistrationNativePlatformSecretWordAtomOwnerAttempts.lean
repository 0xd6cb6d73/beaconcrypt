-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordAtomOwnerFrontend
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordOwnerCredit
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordAliasAlignment
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordOtherInstall
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordAtomServerFrontend
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordAliasClient
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordAtomServerAttempts
open OracleComp OracleSpec CoreModels Aeneas ENNReal
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordAtomOwnerAttempts
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
open RegistrationNativeSecretWordOwnerCredit (credit cost)
open RegistrationNativeSecretWordTargetAlignment (Aligned)
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
    (inside : RegistrationNativeSuffixKeyPrf.Prefix → Bool)
    (pairs : List (PqxdhKemIndCca.MlKem768PublicKey × KemSK)) (publicKey : PqxdhKemIndCca.MlKem768PublicKey)
    (challenge : PqxdhKemIndCca.MlKem768Ciphertext) (outer : QueryImpl Combined ProbComp)
local notation "provider" => RegistrationNativeSecretWordKemEarly.early setup.baseImpl setup.kem selectedOwner pairs publicKey challenge
local notation "implementation" => RegistrationNativeSecretWordTargetSource.implementation (n := n) setup wire route sign input inside provider outer
local notation "controller" => RegistrationNativePlatformSecretWordFrontend.handler (n := n) setup checks wire source sign
  selectedOwner selectedAccept publicPrekey view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
local notation "untraced" => RegistrationNativePlatformSecretWordExecution.typed setup wire route sign input inside provider outer controller
abbrev Front (source : RegistrationNativeMldsa.Source) (Platform : Type) := RegistrationNativePlatformSecretWordOrdinary.State source Platform

local notation "typed" => RegistrationNativePlatformSecretWordExecution.traced setup wire route sign input inside provider outer controller


private theorem trace_cost (query : RegistrationNativeRawAdapter.TypedSpec.Domain) (before : TracedState (Front source Platform) n KemSK)
    (aligned : Aligned before.1.1.beacons before.2.2.kem.1.keys)
    (result : RegistrationNativeRawAdapter.TypedSpec.Range query × TracedState (Front source Platform) n KemSK)
    (supported : result ∈ support ((typed query).run before)) :
    count .beacon result.2.2.1 ≤ count .beacon before.2.1 + cost selectedOwner query before.1.1 := by
  have observed := RegistrationNativePlatformSecretWordExecution.traced_support setup wire route sign input inside provider outer controller
    query before result supported
  cases query with
  | inl coin =>
    simpa only [cost, Nat.add_zero] using RegistrationNativeSecretWordAtomInstallTrace.free .beacon _
      (RegistrationNativePlatformSecretWordOtherInstall.other_free setup checks wire source sign selectedOwner selectedAccept publicPrekey
        view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer .beacon (.inl coin)
        (by simp [RegistrationNativeRawAdapter.kind]) before.1)
      before.2.1 ((result.1, result.2.1), result.2.2.1) observed
  | inr query => cases query with
    | build handle application =>
      simpa only [cost, reduceCtorEq, ite_false, Nat.zero_mul, Nat.add_zero] using
        RegistrationNativePlatformSecretWordAtomServerFrontend.build_count setup checks wire source sign selectedOwner selectedAccept publicPrekey
          view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer .beacon handle application before.1
          before.2.1 ((result.1, result.2.1), result.2.2.1) observed
    | finish index packet =>
      exact RegistrationNativePlatformSecretWordAtomOwnerFrontend.finish_count setup checks wire source sign selectedOwner selectedAccept publicPrekey
        view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer route input inside pairs publicKey challenge outer
        before index packet aligned result supported
    | _ =>
      simpa only [cost, Nat.add_zero] using RegistrationNativeSecretWordAtomInstallTrace.free .beacon _
        (RegistrationNativePlatformSecretWordOtherInstall.other_free setup checks wire source sign selectedOwner selectedAccept publicPrekey
          view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer .beacon _
          (by simp [RegistrationNativeRawAdapter.kind]) before.1)
        before.2.1 ((result.1, result.2.1), result.2.2.1) observed

/-- The actual source credit funds Beacon attempts, while its reached row alignment is preserved. -/
theorem query_credit (query : RegistrationNativeRawAdapter.TypedSpec.Domain) (before : TracedState (Front source Platform) n KemSK)
    (aligned : Aligned before.1.1.beacons before.2.2.kem.1.keys)
    (result : RegistrationNativeRawAdapter.TypedSpec.Range query × TracedState (Front source Platform) n KemSK)
    (supported : result ∈ support ((typed query).run before)) :
    count .beacon result.2.2.1 + credit selectedOwner result.2.1.1 ≤
      count .beacon before.2.1 + credit selectedOwner before.1.1 ∧
    Aligned result.2.1.1.beacons result.2.2.2.kem.1.keys := by
  have original : (result.1, drop result.2) ∈ support ((untraced query).run (drop before)) := by
    rw [← RegistrationNativePlatformSecretWordExecution.traced_source setup wire route sign input inside provider outer controller query before, support_map]
    exact Set.mem_image_of_mem (Prod.map id drop) supported
  have free := RegistrationNativePlatformSecretWordExecution.typed_support setup wire route sign input inside provider outer controller
    query (drop before) (result.1, drop result.2) original
  have consumed := RegistrationNativePlatformSecretWordOwnerCredit.query_credit setup checks wire sign selectedOwner selectedAccept publicPrekey
    view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer query before.1 (result.1, result.2.1) free
  have attempts := trace_cost setup checks wire source sign selectedOwner selectedAccept publicPrekey view failure allocation
    reserveRegistration reservePeer reserveFrame erased helper writer route input inside pairs publicKey challenge outer query before aligned result supported
  dsimp only at consumed
  constructor
  · omega
  · exact RegistrationNativePlatformSecretWordAliasAlignment.typed_keeps setup checks wire source route sign input inside selectedOwner pairs publicKey challenge outer
      selectedOwner selectedAccept publicPrekey view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
      query (drop before) aligned (result.1, drop result.2) original

/-- Every adaptive typed continuation conserves this same source credit and row alignment. -/
theorem program_credit (work : OracleComp RegistrationNativeRawAdapter.TypedSpec A) (before : TracedState (Front source Platform) n KemSK)
    (aligned : Aligned before.1.1.beacons before.2.2.kem.1.keys)
    (result : A × TracedState (Front source Platform) n KemSK)
    (supported : result ∈ support ((simulateQ typed work).run before)) :
    count .beacon result.2.2.1 + credit selectedOwner result.2.1.1 ≤
      count .beacon before.2.1 + credit selectedOwner before.1.1 ∧
    Aligned result.2.1.1.beacons result.2.2.2.kem.1.keys := by
  induction work using OracleComp.inductionOn generalizing before with
  | pure value =>
    simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at supported
    cases supported
    exact ⟨Nat.le_refl _, aligned⟩
  | query_bind query next ih =>
    rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at supported
    obtain ⟨middle, called, continued⟩ := supported
    have first := query_credit setup checks wire source sign selectedOwner selectedAccept publicPrekey view failure allocation
      reserveRegistration reservePeer reserveFrame erased helper writer route input inside pairs publicKey challenge outer query before aligned middle called
    have rest := ih middle.1 middle.2 first.2 continued
    exact ⟨rest.1.trans first.1, rest.2⟩

/-- Empty public and private rosters derive the actual all-mode raw Beacon attempt cap. -/
theorem run_one (serverKeyId : U64) (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) A) (front : Front source Platform)
    (privateState : RegistrationNativeSecretWordInterpreter.State n KemSK)
    (owners : front.1.beacons = []) (keys : privateState.kem.1.keys = [])
    (result : A × (RegistrationNativeLedger.State × TracedState (Front source Platform) n KemSK))
    (supported : result ∈ support (RegistrationNativeFullCompiler.run setup.source.crypto wire serverKeyId bounds typed mode work
      (front, RegistrationNativeSecretWordFrontendTrace.initial, privateState))) :
    count .beacon result.2.2.2.1 ≤ 1 := by
  rw [RegistrationNativeFullCompiler.compile_run, support_map] at supported
  obtain ⟨reached, called, equal⟩ := supported
  cases equal
  have aligned : Aligned front.1.beacons privateState.kem.1.keys := by
    rw [owners, keys]
    exact RegistrationNativeSecretWordTargetAlignment.empty
  have conserved := (program_credit setup checks wire source sign selectedOwner selectedAccept publicPrekey view failure allocation
    reserveRegistration reservePeer reserveFrame erased helper writer route input inside pairs publicKey challenge outer _
    (front, RegistrationNativeSecretWordFrontendTrace.initial, privateState) aligned reached called).1
  simp only [credit, owners, List.getElem?_nil, count, RegistrationNativeSecretWordFrontendTrace.initial, List.countP_nil, Nat.zero_add] at conserved
  dsimp only
  unfold count
  omega
/-- The actual complete candidate-independent new client has at most one Server atom attempt under arbitrary outer table replies. -/
theorem client_one (serverKeyId : U64) (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) A) (front : Front source Platform)
    (ordinary : RegistrationNativePublicInterpreter.State n KemSK) (kem : RegistrationNativeSecretWordKemProvider.State KemSK)
    (owners : front.1.beacons = []) (keys : kem.1.keys = [])
    (result : RegistrationNativePlatformSecretWordAliasClient.Result source n KemSK A Platform)
    (supported : result ∈ support (simulateQ outer (RegistrationNativePlatformSecretWordAliasClient.client setup checks wire source sign
      selectedOwner selectedAccept publicPrekey view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
      route input inside provider serverKeyId bounds mode work front ordinary kem))) :
    count .beacon result.1.2 ≤ 1 := by
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
    erased helper writer route input inside pairs publicKey challenge outer serverKeyId bounds mode work front initial owners keys reached called


end BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordAtomOwnerAttempts

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordAtomOwnerAttempts.query_credit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordAtomOwnerAttempts.query_credit

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordAtomOwnerAttempts.program_credit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordAtomOwnerAttempts.program_credit

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordAtomOwnerAttempts.run_one' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordAtomOwnerAttempts.run_one

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordAtomOwnerAttempts.client_one' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordAtomOwnerAttempts.client_one
