-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomServerFrontend
import BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomTracedSource
import BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomServerCredit
import BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomOwnerOpposite

/-! Actual Server atom installation attempts conserve the same stored/future one-use credit over the original adaptive raw ledger. The pure chronological observer is projected from the concrete early-provider execution, so ordinary accepted references remain literal and no analysis trace is reset between commands. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomServerAttempts
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeSecretWordMessage (Message)
open RegistrationNativeSecretWord (Key)
open RegistrationNativeSecretWordService (Combined)
open RegistrationNativeSecretWordAtomTracedSource (State drop)
open RegistrationNativeSecretWordAtomInstallTrace (count)
open RegistrationNativeSecretWordAtomServerCredit (credit cost)
open PqxdhKemIndCca
variable {n : Nat} {ι KemSK Value : Type} {base : OracleSpec ι}
variable {source : RegistrationNativeMldsa.Source}

variable (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
  (route : RawCtxServerRouting.SenderDecoder)
  (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
  (input : Message → Option Key) (inside : RegistrationNativeSuffixKeyPrf.Prefix → Bool)
  (selected : Nat) (pairs : List (MlKem768PublicKey × KemSK)) (publicKey : MlKem768PublicKey)
  (challenge : MlKem768Ciphertext) (outer : QueryImpl Combined ProbComp)
  (selectedOwner selectedAccept : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
local notation "provider" => RegistrationNativeSecretWordKemEarly.early setup.baseImpl setup.kem selected pairs publicKey challenge
local notation "typed" => RegistrationNativeSecretWordAtomTracedSource.typed (n := n)
  setup wire route sign input inside provider outer checks selectedOwner selectedAccept publicPrekey

attribute [local irreducible] RegistrationNativeSecretWordFrontend.handler
  RegistrationNativeSecretWordServerCompiler.accept RegistrationNativeSecretWordServerCompiler.build

private theorem trace_cost (query : RegistrationNativeRawAdapter.TypedSpec.Domain) (before : State n KemSK source)
    (result : RegistrationNativeRawAdapter.TypedSpec.Range query × State n KemSK source)
    (supported : result ∈ support ((typed query).run before)) :
    count .server result.2.2.1 ≤ count .server before.2.1 + cost query (drop before) := by
  have actual := RegistrationNativeSecretWordAtomTracedSource.typed_support setup wire route sign input inside provider outer checks
    selectedOwner selectedAccept publicPrekey query before result supported
  cases query with
  | inl coin =>
      exact RegistrationNativeSecretWordAtomInstallTrace.free .server _
        (RegistrationNativeSecretWordAtomServerFrontend.other_free .server setup checks wire sign selectedOwner selectedAccept publicPrekey
          (.inl coin) (by simp only [RegistrationNativeRawAdapter.kind]; exact ⟨by decide, by decide⟩) before.1)
        before.2.1 ((result.1, result.2.1), result.2.2.1) actual
  | inr query => cases query with
    | build handle application =>
        simpa only [cost, drop, ite_true, Nat.one_mul] using
          RegistrationNativeSecretWordAtomServerFrontend.build_count .server setup checks wire sign selectedOwner selectedAccept publicPrekey
            handle application before.1 before.2.1 ((result.1, result.2.1), result.2.2.1) actual
    | finish index packet =>
        have free : ((RegistrationNativeSecretWordFrontend.handler (n := n) setup checks wire source sign selectedOwner selectedAccept publicPrekey
              (.inr (.finish index packet))).run before.1).IsQueryBoundP
            (RegistrationNativeSecretWordAtomInstallPredicate.GlobalInstall (KemSK := KemSK) .server) 0 := by
          simp only [RegistrationNativeSecretWordFrontend.handler, RegistrationNativeSecretWordFrontend.beacon, StateT.run, isQueryBoundP_map_iff]
          exact RegistrationNativeSecretWordAtomInstallPredicate.local_bound .server false _ 0
            (RegistrationNativeSecretWordAtomOwnerOpposite.owners_free setup source index packet before.1.beacons before.1.environment)
        exact RegistrationNativeSecretWordAtomInstallTrace.free .server _ free before.2.1 ((result.1, result.2.1), result.2.2.1) actual
    | _ =>
        exact RegistrationNativeSecretWordAtomInstallTrace.free .server _
          (RegistrationNativeSecretWordAtomServerFrontend.other_free .server setup checks wire sign selectedOwner selectedAccept publicPrekey
            _ (by simp only [RegistrationNativeRawAdapter.kind]; exact ⟨by decide, by decide⟩) before.1)
          before.2.1 ((result.1, result.2.1), result.2.2.1) actual

/-- The actual traced typed source spends one and the same native Server atom credit for each atom installation attempt. -/
theorem query_credit (query : RegistrationNativeRawAdapter.TypedSpec.Domain) (before : State n KemSK source)
    (result : RegistrationNativeRawAdapter.TypedSpec.Range query × State n KemSK source)
    (supported : result ∈ support ((typed query).run before)) :
    count .server result.2.2.1 + credit selectedAccept (drop result.2) ≤
      count .server before.2.1 + credit selectedAccept (drop before) := by
  have original : (result.1, drop result.2) ∈ support
      ((RegistrationNativeSecretWordTargetSource.typed setup checks wire route sign input inside provider outer
        selectedOwner selectedAccept publicPrekey query).run (drop before)) := by
    rw [← RegistrationNativeSecretWordAtomTracedSource.typed_source setup wire route sign input inside provider outer checks
      selectedOwner selectedAccept publicPrekey query before, support_map]
    exact Set.mem_image_of_mem (Prod.map id drop) supported
  have tokens := RegistrationNativeSecretWordAtomServerCredit.query_credit setup checks wire route sign input inside selected pairs
    publicKey challenge outer selectedOwner selectedAccept publicPrekey query (drop before) (result.1, drop result.2) original
  dsimp only at tokens
  have attempts := trace_cost setup checks wire route sign input inside selected pairs publicKey challenge outer selectedOwner selectedAccept publicPrekey
    query before result supported
  omega

/-- Every adaptive typed prefix retains the complete source state while conserving the actual chronological Server attempt credit. -/
theorem program_credit (work : OracleComp RegistrationNativeRawAdapter.TypedSpec Value) (before : State n KemSK source)
    (result : Value × State n KemSK source) (supported : result ∈ support ((simulateQ typed work).run before)) :
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
        (query_credit setup checks wire route sign input inside selected pairs publicKey challenge outer selectedOwner selectedAccept publicPrekey
          query before middle called)

/-- Actual initialized full-ledger execution has at most one Server installation attempt whose demanded suffix is the selected opaque atom. -/
theorem run_one (serverKeyId : U64) (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (front : RegistrationNativeSecretWordMessage.State source) (privateState : RegistrationNativeSecretWordInterpreter.State n KemSK)
    (sessions : front.server.sessions = []) (parsed : front.parsedAccepts = 0)
    (result : Value × (RegistrationNativeLedger.State × State n KemSK source))
    (supported : result ∈ support (RegistrationNativeFullCompiler.run setup.source.crypto wire serverKeyId bounds typed mode work
      (front, RegistrationNativeSecretWordFrontendTrace.initial, privateState))) : count .server result.2.2.2.1 ≤ 1 := by
  rw [RegistrationNativeFullCompiler.compile_run, support_map] at supported
  obtain ⟨reached, called, equal⟩ := supported
  cases equal
  have conserved := program_credit setup checks wire route sign input inside selected pairs publicKey challenge outer selectedOwner selectedAccept publicPrekey
    _ (front, RegistrationNativeSecretWordFrontendTrace.initial, privateState) reached called
  simp only [credit, drop, count, sessions, parsed, RegistrationNativeSecretWordAtomSessionCredit.count,
    RegistrationNativeSecretWordLifecycleCounter.available, Nat.zero_le, ite_true, RegistrationNativeSecretWordFrontendTrace.initial,
    List.countP_nil, Nat.zero_add] at conserved
  dsimp only
  unfold count
  omega

end BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomServerAttempts
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomServerAttempts.query_credit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomServerAttempts.query_credit
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomServerAttempts.program_credit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomServerAttempts.program_credit
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomServerAttempts.run_one' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomServerAttempts.run_one
