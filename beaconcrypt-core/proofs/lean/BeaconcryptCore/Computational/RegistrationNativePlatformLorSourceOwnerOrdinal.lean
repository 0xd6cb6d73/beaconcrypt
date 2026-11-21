import BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceOwnerInputs
import BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceOwnerTraced
import BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceKemTrace
import BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceInstall
import BeaconcryptCore.Computational.RegistrationNativeSecretWordInstallWitness
import BeaconcryptCore.Computational.RegistrationNativeSelectiveHiddenDemand
import BeaconcryptCore.Computational.RegistrationNativeInstallKernelStorage
import BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceBuildChronology
import BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceOwnerPin
import BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceDesignatedRetained
import BeaconcryptCore.Computational.RegistrationNativePlatformLorSourcePolicies
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordServerPinSource
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordOwnerPinPath
import BeaconcryptCore.Computational.RegistrationNativeOwnerLinkedFields
import BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetOwnerCallPath
-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordTargetDesignatedRetained
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordPrekeyPublicationRun
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordBuildChronology
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordSessionSlotsSource
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordBuildStored
import BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetProtected
import BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetPathConcat
import BeaconcryptCore.Computational.RegistrationNativeLinkedBuild
/-! Original broad peer designation and its transported public pin conjunct identify the exact protected Ready at the actual later successful moved-token build. The proof uses the current stateful source writer and retains one original run, all failed prefixes, complete platform/private state and its full suffix. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceOwnerOrdinal
open PqxdhServerAuthExperiment (Setup Checks)
open PqxdhDeploymentInterface (FreshBounds Mode Budget)
open RegistrationNativeSecretWordMessage (Message)
open RegistrationNativeSecretWord (Key Word)
open RegistrationNativeSecretWordService (Combined)
open RegistrationNativeSecretWordTargetPath (Path)
open PqxdhKemIndCca
variable {n : Nat} {I KemSK Platform E Private A : Type} {base : OracleSpec I}
variable [primitive : BeaconcryptCore.Refinement.AdapterSealPrimitive.Operations]
    (setup : Setup base KemSK) (checks : Checks) (source : RegistrationNativeMldsa.Source)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (pairs : List (MlKem768PublicKey × KemSK)) (chosen : MlKem768PublicKey × KemSK) (challenge : MlKem768Ciphertext)
    (implementation : QueryImpl (RegistrationNativeSecretWordInterface.Spec n KemSK) (StateT Private ProbComp))
    (kem : Private → RegistrationNativeSecretWordKemProvider.State KemSK)
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
variable (contract : RegistrationNativePlatformLorSourceKem.Contract implementation kem
  (RegistrationNativeSecretWordMessage.input setup.joint setup.dh seed scalar)
  (RegistrationNativeSecretWordKemEarly.early setup.baseImpl setup.kem target.2.val pairs chosen.1 challenge))
local notation "controller" => RegistrationNativePlatformSecretWordFrontend.handler (n := n) setup checks wire source sign
  (Fin.val (Prod.snd target)) (Fin.val (Prod.fst target)) publicPrekey view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
local notation "typed" => RegistrationNativePlatformLorStatefulSupport.traced implementation controller
local notation "State" => RegistrationNativePlatformLorStatefulSupport.TracedState (RegistrationNativePlatformSecretWordOrdinary.State source Platform) Private
local notation "full" => RegistrationNativeFullCompiler.handler setup.source.crypto wire serverKeyId bounds typed
local notation "FullState" => RegistrationNativeLedger.State × State
include contract

/-- Every original broadly designated owner has its protected descriptor at its matching actual successful public installation ordinal. -/
theorem ordinal (bounded : RegistrationNativeInterface.Respects budget work) (reserved : budget.create ≤ pairs.length)
    (chosenAt : pairs[target.2.val]?=some chosen) (before : State)
    (initialCounter : before.1.1.parsedAccepts=0) (initialMarker : (kem before.2.2).2=none)
    (ownersEmpty : before.1.1.beacons=[]) (keysEmpty : (kem before.2.2).1.keys=[])
    (candidate : MlKemSharedSecret) (initialTrace : before.2.1.events=[])
    (serverPin : PqxdhRefinement.absBytes before.1.1.server.pin.binding.identity_public_key=(setup.joint.publicKeys seed).ed25519.toList)
    (observed : RegistrationNativeEvents.Observed A State)
    (supported : observed ∈ support (RegistrationNativeFullCompiler.run setup.source.crypto wire serverKeyId bounds typed mode work before))
    (session : Fin budget.accept) (owner : Nat)
    (designated : PqxdhDeploymentTranscript.designateIn setup.source.crypto (RegistrationNativeWire.ledgerCodec wire)
      serverKeyId budget observed.2.1.ledger.transcript (.owner owner)=some (session,target.2))
    (accepted : RegistrationNativeParsedTargetCanonical.AcceptedAt wire observed.2.1.transcript session.val target.1.val) :
    ∃ ordinal message, RegistrationNativeInstallOrdinals.At .beacon
      (observed.2.2.2.1.events.map (RegistrationNativeSecretWordCheckedTrace.event candidate)) observed.2.1.transcript ordinal message (.owner owner) ∧
      RegistrationNativeInstallKernelStorage.Selected setup seed scalar candidate message := by
  have tracedContract := RegistrationNativePlatformLorSourceKemTrace.contract implementation kem nativeInput _ contract
  obtain ⟨same,raw,packet,application,pre,post,first,last,recorded,prior,called,later,_decoded,ciphertext,pins⟩ :=
    RegistrationNativePlatformLorSourceOwnerInputs.selected setup checks source sign seed scalar pairs chosen challenge
      (RegistrationNativePlatformLorStatefulSupport.trace implementation) (fun current => kem current.2)
      view failure allocation reserveRegistration reservePeer reserveFrame erased helper reservePackets serverKeyId bounds mode work budget target tracedContract
      bounded reserved chosenAt before initialCounter initialMarker ownersEmpty keysEmpty observed supported session owner designated accepted
  subst owner
  have policies := RegistrationNativePlatformLorSourcePolicies.path_holds setup checks wire sign target.2.val target.1.val publicPrekey
    view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
    (RegistrationNativePlatformLorStatefulSupport.trace implementation) serverKeyId bounds prior
    (by constructor
        · rw [ownersEmpty]; exact RegistrationNativePublicOwnerMask.empty _ _
        · rw [ownersEmpty]; intro index current found; simp only [List.getElem?_nil] at found; cases found)
  have canonical := policies.1
  have coherent := policies.2
  have aligned := RegistrationNativePlatformLorSourceAlignment.path_keeps setup checks wire source sign target.2.val target.1.val publicPrekey
    view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer target.2.val pairs chosen.1 challenge
    (RegistrationNativePlatformLorStatefulSupport.trace implementation) (fun current => kem current.2) nativeInput tracedContract serverKeyId bounds prior
    (by rw [ownersEmpty,keysEmpty]; exact RegistrationNativeSecretWordTargetAlignment.empty)
  have actualFinish := called
  rw [RegistrationNativePlatformLorStatefulSupport.typed_run] at actualFinish
  obtain ⟨ready,atom,_realized,protectedHeads,own⟩ := RegistrationNativePlatformLorSourceOwnerTraced.finish setup wire seed scalar
    target.2.val pairs chosen.1 challenge implementation kem contract packet application first.2 last.2 canonical aligned
    (fun current found => (congrArg PqxdhRefinement.absBytes (pins current found)).trans serverPin)
    (by intro current found pending oneTime phase;have valid:=coherent target.2.val current found;unfold RegistrationNativeSecretWordPendingPin.Coherent at valid;rw [phase] at valid;exact valid)
    ciphertext (by
      simp only [RegistrationNativePlatformSecretWordFrontend.handler] at actualFinish
      convert actualFinish using 1 <;> rfl)
  have counted := RegistrationNativePlatformLorSourceInstall.path_counts setup checks RegistrationNativePlatformConcreteSource.wire source sign target.2.val target.1.val publicPrekey
    view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer implementation candidate serverKeyId bounds before initialTrace prior .beacon
  have recordedPrefix := RegistrationNativeSecretWordTargetPath.records full (fun current => current.1.transcript)
    (fun query current next reached => RegistrationNativeLedgerJournal.handler_records _ setup.source.crypto (RegistrationNativeWire.ledgerCodec wire) serverKeyId bounds query current next reached) prior
  simp only [RegistrationNativeLedger.empty,List.nil_append] at recordedPrefix
  have count : (RegistrationNativeSecretWordInstallOrdinals.messages .beacon first.2.2.1.events).length=
      (RegistrationNativeInstallOrdinals.handles .beacon pre).length := by
    simpa only [RegistrationNativeInstallOrdinals.Counts,RegistrationNativePlatformLorSourceInstall.events,
      RegistrationNativeSecretWordInstallOrdinals.messages_eval,List.length_map,recordedPrefix] using counted
  obtain ⟨tail,suffix⟩ := RegistrationNativePlatformLorSourceInstall.path_suffix setup checks RegistrationNativePlatformConcreteSource.wire source sign target.2.val target.1.val publicPrekey
    view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer implementation serverKeyId bounds .beacon later
  have joined : RegistrationNativeSecretWordInstallOrdinals.messages .beacon observed.2.2.2.1.events=
      RegistrationNativeSecretWordInstallOrdinals.messages .beacon first.2.2.1.events++ready.reference::tail := by
    rw [suffix,own .beacon,List.append_assoc]
    rfl
  have handles : RegistrationNativeInstallOrdinals.handles .beacon observed.2.1.transcript=
      RegistrationNativeInstallOrdinals.handles .beacon pre++(.owner target.2.val)::RegistrationNativeInstallOrdinals.handles .beacon post := by
    rw [recorded,RegistrationNativeInstallOrdinals.handles_append]
    rfl
  obtain ⟨ordinal,paired⟩ := RegistrationNativeSecretWordInstallWitness.at_append .beacon first.2.2.1.events observed.2.2.2.1.events pre
    observed.2.1.transcript ready.reference (.owner target.2.val) tail (RegistrationNativeInstallOrdinals.handles .beacon post) count joined handles
  refine ⟨ordinal,RegistrationNativeSecretWordMessage.eval candidate ready.reference,
    RegistrationNativeSecretWordInstallOrdinals.at_eval candidate .beacon _ _ ordinal ready.reference (.owner target.2.val) paired,?_⟩
  intro bytes realized
  exact RegistrationNativeSelectiveHiddenDemand.selected_descriptor setup.joint setup.dh seed scalar candidate
    (setup.joint.staticDh seed (setup.dh.publicKey scalar)) ready.reference bytes atom protectedHeads realized
end BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceOwnerOrdinal

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceOwnerOrdinal.ordinal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceOwnerOrdinal.ordinal
