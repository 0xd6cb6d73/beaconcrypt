import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordInstallServerTyped
import BeaconcryptCore.Computational.RegistrationNativeTargetRawSuccess
import BeaconcryptCore.Computational.RegistrationNativeTargetLedgerCore
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
namespace BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordInstallPeerTraced
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



open RegistrationNativeSecretWordInstallOrdinals (messages)
open RegistrationNativeInstallBeaconComplete (present)
open RegistrationNativePlatformSecretWordExecution (TracedState traced)
local notation "traceState" => TracedState (RegistrationNativePlatformSecretWordOrdinary.State source Platform) n KemSK
local notation "traceTyped" => traced (n := n) setup (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) route sign input inside provider outer controller

omit primitive in
private theorem map_apply {S X Y : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (observe : X → Y) (work : StateT S m X) (before : S) :
    (observe <$> work) before = Prod.map observe id <$> work before := StateT.run_map _ _ _

/-- A successful actual source build appends exactly the same consumed Ready descriptor to the Server installation trace. -/
theorem build (handle : Nat) (application : Option (Slice U8))
    (before : RegistrationNativePlatformSecretWordOrdinary.State source Platform)
    (ready : RegistrationNativeSecretWordMessage.ServerReady) (stored : before.1.server.sessions[handle]?=some (some ready))
    (trace : RegistrationNativeSecretWordFrontendTrace.State)
    (result : (RustM (Option (U64 × Pqxdh.Bytes)) × RegistrationNativePlatformSecretWordOrdinary.State source Platform) × RegistrationNativeSecretWordFrontendTrace.State)
    (supported : result ∈ support ((simulateQ RegistrationNativeSecretWordFrontendTrace.handler
      ((controller (.inr (.build handle application))).run before)).run trace))
    (keyId : U64) (bytes : Pqxdh.Bytes) (returned : result.1.1=.ok (some (keyId,bytes))) :
    messages .server result.2.events=messages .server trace.events++[ready.reference] := by
  simp only [RegistrationNativePlatformSecretWordFrontend.handler,RegistrationNativePlatformSecretWordFrontend.build,
    StateT.run,simulateQ_map,map_apply,support_map] at supported
  obtain ⟨reached,called,equal⟩ := supported
  cases equal
  simp only [Prod.map_def,id_eq] at returned ⊢
  have own := RegistrationNativePlatformSecretWordInstallServerControl.body_live setup.source view failure allocation erased helper sign writer reservePeer
    .server handle application before.1.server ready stored (before.1.environment.receipts,before.2) trace reached called
  have same (reply : RustM (Option (U64 × alloc.vec.Vec U8))) :
      present (RegistrationNativePlatformPublicFrontend.responseBytes reply)=present reply := by
    cases reply with
    | fail error | div => rfl
    | ok value => cases value <;> rfl
  have actualPresent : present reached.1.1.1=true := by
    rw [←same,returned]
    rfl
  simpa only [actualPresent,and_self,ite_true] using own

/-- Actual private interpretation keeps that same complete callback and its original returned reply. -/
theorem interpreted (handle : Nat) (application : Option (Slice U8)) (before after : traceState)
    (ready : RegistrationNativeSecretWordMessage.ServerReady) (stored : before.1.1.server.sessions[handle]?=some (some ready))
    (keyId : U64) (bytes : Pqxdh.Bytes)
    (supported : (.ok (some (keyId,bytes)),after) ∈ support ((traceTyped (.inr (.build handle application))).run before)) :
    messages .server after.2.1.events=messages .server before.2.1.events++[ready.reference] :=
  build setup checks wire source sign selectedOwner selectedAccept publicPrekey view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
    handle application before.1 ready stored before.2.1 ((.ok (some (keyId,bytes)),after.1),after.2.1)
    (RegistrationNativePlatformSecretWordExecution.traced_support setup (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire)
      route sign input inside provider outer controller (.inr (.build handle application)) before (.ok (some (keyId,bytes)),after) supported)
    keyId bytes rfl

/-- The original full raw ledger records that same descriptor at its actual successful linked build. -/
theorem full (serverKeyId : U64) (bounds : PqxdhDeploymentInterface.FreshBounds) (handle : Nat) (payload : Option Pqxdh.Bytes)
    (response : PqxdhServerRegistrationPublication.Response)
    (before after : RegistrationNativeLedger.State × traceState)
    (ready : RegistrationNativeSecretWordMessage.ServerReady) (stored : before.2.1.1.server.sessions[handle]?=some (some ready))
    (supported : (some response,after) ∈ support ((RegistrationNativeFullCompiler.handler setup.source.crypto
      (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) serverKeyId bounds traceTyped (.inl (.inr (.build handle payload)))).run before)) :
    messages .server after.2.2.1.events=messages .server before.2.2.1.events++[ready.reference] := by
  rw [RegistrationNativeTargetLedgerCore.run,support_map] at supported
  obtain ⟨⟨reply,current⟩,reached,equal⟩ := supported
  have replyEq : reply=some response := congrArg Prod.fst equal
  have stateEq : current=after.2 := congrArg (fun output => output.2.2) equal
  subst reply
  rw [stateEq] at reached
  exact interpreted setup checks wire source route sign input inside selected pairs publicKey challenge outer selectedOwner selectedAccept publicPrekey
    view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer handle (RegistrationNativeRawAdapter.application payload)
    before.2 after.2 ready stored response.keyId response.serialized
    (RegistrationNativeTargetRawSuccess.build (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) traceTyped handle payload response before.2 after.2 reached)

end BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordInstallPeerTraced

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordInstallPeerTraced.build' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordInstallPeerTraced.build

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordInstallPeerTraced.interpreted' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordInstallPeerTraced.interpreted

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordInstallPeerTraced.full' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordInstallPeerTraced.full
