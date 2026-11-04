-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformDesignatedPeerTraced
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordInstallLedger
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordInstallMonotone
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordInstallPeerTraced
import BeaconcryptCore.Computational.RegistrationNativeSecretWordInstallWitness
import BeaconcryptCore.Computational.RegistrationNativeSelectiveHiddenDemand
import BeaconcryptCore.Computational.RegistrationNativeInstallKernelStorage

/-! The original broadly designated peer has its protected descriptor at the matching actual successful public installation ordinal. The proof pairs one same-run descriptor append with the original reply journal and preserves its full source prefix, failed calls, platform state and later callbacks. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformDesignatedPeerOrdinal
open PqxdhServerAuthExperiment (Setup Checks)
open PqxdhDeploymentInterface (FreshBounds Mode Budget)
open RegistrationNativeSecretWordMessage (Message)
open RegistrationNativeSecretWord (Key Word)
open RegistrationNativeSecretWordService (Combined)
open RegistrationNativePlatformSecretWordExecution (TracedState drop)
open RegistrationNativeSecretWordTargetPath (Path)
open PqxdhKemIndCca
variable {n : Nat} {I KemSK Platform E A : Type} {base : OracleSpec I}
variable [primitive : BeaconcryptCore.Refinement.AdapterSealPrimitive.Operations]
    (setup : Setup base KemSK) (checks : Checks) (source : RegistrationNativeMldsa.Source)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (pairs : List (MlKem768PublicKey × KemSK)) (chosen : MlKem768PublicKey × KemSK) (challenge : MlKem768Ciphertext)
    (outer : QueryImpl Combined ProbComp)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
    (reserveFrame : Nat → StateT Platform ProbComp (core.result.Result Unit E)) (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (BeaconcryptCore.Refinement.AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (reservePackets : Usize → StateT Platform ProbComp (core.result.Result Unit E))
    (serverKeyId : U64) (bounds : FreshBounds) (mode : Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) A) (budget : Budget)
    (target : Fin budget.accept × Fin budget.capacity)
local notation "wire" => RegistrationNativePlatformOrdinaryExperiment.canonicalWire RegistrationNativePlatformConcreteSource.wire
local notation "writer" => RegistrationNativePlatformConcreteSource.writer reservePackets
local notation "nativeInput" => RegistrationNativeSecretWordMessage.input setup.joint setup.dh seed scalar
local notation "nativeInside" => RegistrationNativeSecretWordProtection.inside (setup.joint.staticDh seed (setup.dh.publicKey scalar))
local notation "publicPrekey" => setup.dh.publicKey scalar
local notation "provider" => RegistrationNativeSecretWordKemEarly.early setup.baseImpl setup.kem (Fin.val (Prod.snd target)) pairs (Prod.fst chosen) challenge
local notation "controller" => RegistrationNativePlatformSecretWordFrontend.handler (n := n) setup checks wire source sign
  (Fin.val (Prod.snd target)) (Fin.val (Prod.fst target)) publicPrekey view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
local notation "plainTyped" => RegistrationNativePlatformSecretWordExecution.typed (n := n) setup wire route sign nativeInput nativeInside provider outer controller
local notation "typed" => RegistrationNativePlatformSecretWordExecution.traced (n := n) setup wire route sign nativeInput nativeInside provider outer controller
local notation "State" => TracedState (RegistrationNativePlatformSecretWordOrdinary.State source Platform) n KemSK
local notation "full" => RegistrationNativeFullCompiler.handler setup.source.crypto wire serverKeyId bounds typed
local notation "FullState" => RegistrationNativeLedger.State × State
attribute [local irreducible] RegistrationNativeSecretWordTargetSource.implementation
  RegistrationNativeSecretWordKemEarly.early

/-- Every original broadly designated peer has its protected descriptor at the matching actual source installation ordinal. -/
theorem ordinal (bounded : RegistrationNativeInterface.Respects budget work) (reserved : budget.create ≤ pairs.length)
    (chosenAt : pairs[target.2.val]?=some chosen) (before : State)
    (initialCounter : before.1.1.parsedAccepts=0) (initialMarker : before.2.2.kem.2=none)
    (ownersEmpty : before.1.1.beacons=[]) (keysEmpty : before.2.2.kem.1.keys=[])
    (candidate : MlKemSharedSecret) (initialTrace : before.2.1.events=[])
    (observed : RegistrationNativeEvents.Observed A State)
    (supported : observed ∈ support (RegistrationNativeFullCompiler.run setup.source.crypto wire serverKeyId bounds typed mode work before))
    (session : Fin budget.accept) (keyId : U64)
    (designated : PqxdhDeploymentTranscript.designateIn setup.source.crypto (RegistrationNativeWire.ledgerCodec wire)
      serverKeyId budget observed.2.1.ledger.transcript (.peer keyId)=some (session,target.2))
    (accepted : RegistrationNativeParsedTargetCanonical.AcceptedAt wire observed.2.1.transcript session.val target.1.val)
    (pinned : RegistrationNativePrekeyEvents.Pinned setup.source.crypto (RegistrationNativeWire.ledgerCodec wire)
      serverKeyId observed.2.1.ledger.transcript (.peer keyId)) :
    ∃ ordinal message, RegistrationNativeInstallOrdinals.At .server
      (observed.2.2.2.1.events.map (RegistrationNativeSecretWordCheckedTrace.event candidate)) observed.2.1.transcript ordinal message (.peer keyId) ∧
      RegistrationNativeInstallKernelStorage.Selected setup seed scalar candidate message := by
  obtain ⟨payload,response,ready,first,last,pre,post,responseKey,recorded,prior,called,later,stored,atom,protectedHeads⟩ :=
    RegistrationNativePlatformDesignatedPeerTraced.selected setup checks source route sign seed scalar pairs chosen challenge outer view failure allocation
      reserveRegistration reservePeer reserveFrame erased helper reservePackets serverKeyId bounds mode work budget target bounded reserved chosenAt
      before initialCounter initialMarker ownersEmpty keysEmpty observed supported session keyId designated accepted pinned
  have own := RegistrationNativePlatformSecretWordInstallPeerTraced.full setup checks RegistrationNativePlatformConcreteSource.wire source route sign nativeInput nativeInside
    target.2.val pairs chosen.1 challenge outer target.2.val target.1.val publicPrekey view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
    serverKeyId bounds session.val payload response first last ready stored called
  have counted := RegistrationNativePlatformSecretWordInstallLedger.path setup checks RegistrationNativePlatformConcreteSource.wire source route sign nativeInput nativeInside
    target.2.val pairs chosen.1 challenge outer target.2.val target.1.val publicPrekey view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
    candidate serverKeyId bounds before initialTrace prior .server
  have recordedPrefix := RegistrationNativePlatformSecretWordTargetPath.records setup wire route sign nativeInput nativeInside provider outer controller
    serverKeyId bounds prior
  simp only [RegistrationNativeLedger.empty,List.nil_append] at recordedPrefix
  have count : (RegistrationNativeSecretWordInstallOrdinals.messages .server first.2.2.1.events).length=
      (RegistrationNativeInstallOrdinals.handles .server pre).length := by
    simpa only [RegistrationNativeInstallOrdinals.Counts,RegistrationNativePlatformSecretWordInstallLedger.events,
      RegistrationNativeSecretWordInstallOrdinals.messages_eval,List.length_map,recordedPrefix] using counted
  obtain ⟨tail,suffix⟩ := RegistrationNativePlatformSecretWordInstallMonotone.path setup wire route sign nativeInput nativeInside provider outer controller
    serverKeyId bounds .server later
  have joined : RegistrationNativeSecretWordInstallOrdinals.messages .server observed.2.2.2.1.events=
      RegistrationNativeSecretWordInstallOrdinals.messages .server first.2.2.1.events++ready.reference::tail := by
    rw [suffix,own,List.append_assoc]
    rfl
  have handles : RegistrationNativeInstallOrdinals.handles .server observed.2.1.transcript=
      RegistrationNativeInstallOrdinals.handles .server pre++(.peer keyId)::RegistrationNativeInstallOrdinals.handles .server post := by
    rw [recorded,RegistrationNativeInstallOrdinals.handles_append]
    simp only [RegistrationNativeInstallOrdinals.handles,List.filterMap_cons]
    rw [responseKey]
  obtain ⟨ordinal,paired⟩ := RegistrationNativeSecretWordInstallWitness.at_append .server first.2.2.1.events observed.2.2.2.1.events pre
    observed.2.1.transcript ready.reference (.peer keyId) tail (RegistrationNativeInstallOrdinals.handles .server post) count joined handles
  refine ⟨ordinal,RegistrationNativeSecretWordMessage.eval candidate ready.reference,
    RegistrationNativeSecretWordInstallOrdinals.at_eval candidate .server _ _ ordinal ready.reference (.peer keyId) paired,?_⟩
  intro bytes realized
  exact RegistrationNativeSelectiveHiddenDemand.selected_descriptor setup.joint setup.dh seed scalar candidate
    (setup.joint.staticDh seed (setup.dh.publicKey scalar)) ready.reference bytes atom protectedHeads realized

end BeaconcryptCore.Computational.RegistrationNativePlatformDesignatedPeerOrdinal

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformDesignatedPeerOrdinal.ordinal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformDesignatedPeerOrdinal.ordinal
