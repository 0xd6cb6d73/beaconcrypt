import BeaconcryptCore.Computational.RegistrationNativeTargetLedgerCore
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordTargetRetained
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordTargetOpenOrigin
-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordTargetCreateBounds
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordAliasAlignment
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordTargetOpenSelected
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordTargetCounter
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordTargetPath
/-! The current full Word source consumes the early KEM reservation in exact birth order under its original public create allowance. The current source-derived constructor cap rules out fallback; no final-owner activation or private row association is supplied as a premise. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordAcceptFresh
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeSecretWordMessage (Message)
open RegistrationNativeSecretWord (Key)
open RegistrationNativeSecretWordService (Combined)
open RegistrationNativeSecretWordTargetAlignment (Aligned)
open RegistrationNativeSecretWordTargetPublication (key)
open PqxdhKemIndCca
variable {n : Nat} {I KemSK Platform E A : Type} {base : OracleSpec I}
variable [primitive : BeaconcryptCore.Refinement.AdapterSealPrimitive.Operations]
    (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire) (source : RegistrationNativeMldsa.Source)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (input : Message → Option Key) (inside : RegistrationNativeSuffixKeyPrf.Prefix → Bool)
    (selected : Nat) (pairs : List (MlKem768PublicKey × KemSK)) (publicKey : MlKem768PublicKey)
    (challenge : MlKem768Ciphertext) (outer : QueryImpl Combined ProbComp)
    (selectedOwner selectedAccept : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
    (reserveFrame : Nat → StateT Platform ProbComp (core.result.Result Unit E)) (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (BeaconcryptCore.Refinement.AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))

open RegistrationNativePlatformSecretWordAliasAlignment (State)
local notation "provider" => RegistrationNativeSecretWordKemEarly.early setup.baseImpl setup.kem selected pairs publicKey challenge
local notation "implementation" => RegistrationNativeSecretWordTargetSource.implementation (n := n) setup (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) route sign input inside provider outer
local notation "controller" => RegistrationNativePlatformSecretWordFrontend.handler (n := n) setup checks (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) source sign
  selectedOwner selectedAccept publicPrekey view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
local notation "typed" => RegistrationNativePlatformSecretWordExecution.typed (n := n) setup (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) route sign input inside provider outer controller



local notation "openState" => RegistrationNativePlatformSecretWordAtomOpenRun.State n KemSK Platform
local notation "close" => RegistrationNativePlatformSecretWordAtomOpenRun.close implementation

omit primitive in
private theorem retain_fresh (ready : RegistrationNativeSecretWordMessage.ServerReady) (before after : openState) (handle : Nat)
    (supported : (.ok (some handle),after) ∈ support ((close (RegistrationNativePlatformSecretWordOpen.retain ready)).run before)) :
    handle=before.1.sessions.length := by
  rw [RegistrationNativePlatformSecretWordAtomOpenRun.retain_run] at supported
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

attribute [local irreducible] RegistrationAuthenticationCompiler.program

omit primitive in
/-- Every successful actual OPEN callback returns its original fresh session index, under arbitrary live reservation outcomes. -/
theorem open_fresh (selectedCall : Bool) (packet : registration.InitPacket) (before after : openState) (handle : Nat)
    (supported : (.ok (some handle),after) ∈ support ((close (RegistrationNativePlatformSecretWordOpen.accept
      (RegistrationNativePlatformSecretWordFrontendView.wordLocal selectedCall)
      (RegistrationNativePlatformSecretWordOrdinary.platform reserveRegistration) setup checks source.verify packet)).run before)) :
    handle=before.1.sessions.length := by
  obtain ⟨pinned,pinAt,afterPinAt⟩ := RegistrationNativePlatformSecretWordTargetOpenOrigin.accept implementation setup checks selectedCall
    (RegistrationNativePlatformSecretWordOrdinary.platform reserveRegistration) packet source.verify before after handle supported
  have pinSame := RegistrationNativePlatformSecretWordAtomOpenRun.lifted_server implementation _ before pinned pinAt
  obtain ⟨pin,events,authenticated,checked,_pinReply,authenticatedAt,_checkedReply,afterAuthenticationAt⟩ :=
    RegistrationNativePlatformSecretWordTargetOpenOrigin.after_pin implementation setup checks selectedCall
      (RegistrationNativePlatformSecretWordOrdinary.platform reserveRegistration) packet source.verify pinned.1 pinned.2 after handle afterPinAt
  have authSame := RegistrationNativePlatformSecretWordAtomOpenRun.lifted_server implementation _ pinned.2 checked authenticatedAt
  obtain ⟨reserved,ready,agreed,reservedAt,_admitted,agreedAt,_agreedReply,retainedAt,_stored⟩ :=
    RegistrationNativePlatformSecretWordTargetOpenOrigin.after_authentication implementation setup checks selectedCall
      (RegistrationNativePlatformSecretWordOrdinary.platform reserveRegistration) packet authenticated checked.2 after handle afterAuthenticationAt
  have reserveSame := RegistrationNativePlatformSecretWordAtomOpenRun.lifted_server implementation _ checked.2 reserved reservedAt
  have agreementSame := RegistrationNativePlatformSecretWordAtomSessionShape.agreement_server implementation setup checks selectedCall
    packet authenticated reserved.2 agreed agreedAt
  have fresh := retain_fresh setup wire route sign input inside selected pairs publicKey challenge outer ready agreed.2 after handle retainedAt
  rw [agreementSame,reserveSame,authSame,pinSame] at fresh
  exact fresh

/-- The current typed callback returns its same original fresh index even after stateful authentication and reserve effects. -/
theorem typed_fresh (packet : registration.InitPacket) (handle : Nat) (before after : State n KemSK source Platform)
    (supported : (.ok (some handle),after) ∈ support ((typed (.inr (.accept packet))).run before)) :
    handle=before.1.1.server.sessions.length := by
  rw [RegistrationNativePlatformSecretWordTargetRetained.accept_run,support_map] at supported
  obtain ⟨⟨reply,reached⟩,called,returned⟩ := supported
  have success : reply=.ok (some handle) := congrArg Prod.fst returned
  subst reply
  exact open_fresh setup checks wire source route sign input inside selected pairs publicKey challenge outer reserveRegistration
    (decide (before.1.1.parsedAccepts=selectedAccept)) packet
    (before.1.1.server,(before.1.1.environment,(before.1.2,before.2))) reached handle called

/-- Successfully decoded original raw accepts return exactly that same fresh source slot. -/
theorem raw (raw : Pqxdh.Bytes) (packet : registration.InitPacket) (handle : Nat)
    (decoded : RegistrationNativeWire.readInit (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) raw=some packet)
    (before after : State n KemSK source Platform)
    (supported : (some handle,after) ∈ support ((RegistrationNativeRawAdapter.handler
      (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) typed (.inr (.accept raw))).run before)) :
    handle=before.1.1.server.sessions.length := by
  simp only [RegistrationNativeRawAdapter.handler,QueryImpl.apply_compose,RegistrationNativeRawAdapter.adapter,
    decoded,simulateQ_map,simulateQ_spec_query,StateT.run_map,support_map] at supported
  obtain ⟨⟨reply,current⟩,reached,returned⟩ := supported
  cases actual : reply with
  | fail error | div => simp [actual,RegistrationNativeRawAdapter.resultOption] at returned
  | ok reply =>
    simp only [actual,RegistrationNativeRawAdapter.resultOption,Prod.mk.injEq] at returned
    obtain ⟨rfl,rfl⟩ := returned
    exact typed_fresh setup checks wire source route sign input inside selected pairs publicKey challenge outer selectedOwner selectedAccept publicPrekey
      view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer packet handle before _
      (by simpa only [actual] using reached)

/-- The original complete ledger callback retains its actual pre-call fresh index and all failure semantics. -/
theorem full (serverKeyId : U64) (bounds : PqxdhDeploymentInterface.FreshBounds) (raw : Pqxdh.Bytes)
    (packet : registration.InitPacket) (handle : Nat)
    (decoded : RegistrationNativeWire.readInit (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) raw=some packet)
    (before after : RegistrationNativeLedger.State × State n KemSK source Platform)
    (supported : (some handle,after) ∈ support ((RegistrationNativeFullCompiler.handler setup.source.crypto
      (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) serverKeyId bounds typed (.inl (.inr (.accept raw)))).run before)) :
    handle=before.2.1.1.server.sessions.length := by
  rw [RegistrationNativeTargetLedgerCore.run,support_map] at supported
  obtain ⟨⟨reply,current⟩,reached,returned⟩ := supported
  have success : reply=some handle := congrArg Prod.fst returned
  subst reply
  exact RegistrationNativePlatformSecretWordAcceptFresh.raw setup checks wire source route sign input inside selected pairs publicKey challenge outer selectedOwner selectedAccept publicPrekey
    view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer _ packet handle decoded before.2 current reached

end BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordAcceptFresh

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordAcceptFresh.open_fresh' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordAcceptFresh.open_fresh

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordAcceptFresh.typed_fresh' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordAcceptFresh.typed_fresh

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordAcceptFresh.raw' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordAcceptFresh.raw

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordAcceptFresh.full' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordAcceptFresh.full
