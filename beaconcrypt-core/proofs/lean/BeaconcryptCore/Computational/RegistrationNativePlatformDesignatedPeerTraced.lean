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
namespace BeaconcryptCore.Computational.RegistrationNativePlatformDesignatedPeerTraced
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

/-- A broadly designated peer has the protected same Ready at its exact later successful source build. -/
theorem selected (bounded : RegistrationNativeInterface.Respects budget work) (reserved : budget.create ≤ pairs.length)
    (chosenAt : pairs[target.2.val]?=some chosen) (before : State)
    (initialCounter : before.1.1.parsedAccepts=0) (initialMarker : before.2.2.kem.2=none)
    (ownersEmpty : before.1.1.beacons=[]) (keysEmpty : before.2.2.kem.1.keys=[])
    (observed : RegistrationNativeEvents.Observed A State)
    (supported : observed ∈ support (RegistrationNativeFullCompiler.run setup.source.crypto wire serverKeyId bounds typed mode work before))
    (session : Fin budget.accept) (keyId : U64)
    (designated : PqxdhDeploymentTranscript.designateIn setup.source.crypto (RegistrationNativeWire.ledgerCodec wire)
      serverKeyId budget observed.2.1.ledger.transcript (.peer keyId)=some (session,target.2))
    (accepted : RegistrationNativeParsedTargetCanonical.AcceptedAt wire observed.2.1.transcript session.val target.1.val)
    (pinned : RegistrationNativePrekeyEvents.Pinned setup.source.crypto (RegistrationNativeWire.ledgerCodec wire)
      serverKeyId observed.2.1.ledger.transcript (.peer keyId)) :
    ∃ payload response, ∃ ready : RegistrationNativeSecretWordMessage.ServerReady,
      ∃ (buildFirst buildLast : FullState) (left right : List RegistrationNativeInterface.Entry),
        response.keyId=keyId ∧ observed.2.1.transcript=left++⟨.inl (.inr (.build session.val payload)),some response⟩::right ∧
        Path full (RegistrationNativeLedger.empty,before) left buildFirst ∧
        (some response,buildLast) ∈ support ((full (.inl (.inr (.build session.val payload)))).run buildFirst) ∧
        Path full buildLast right observed.2 ∧
        buildFirst.2.1.1.server.sessions[session.val]?=some (some ready) ∧ ready.reference.kem=Word.atom ∧
        ∀ key, nativeInput ready.reference=some key → nativeInside key.head=true := by
  obtain ⟨call,marker,traceFirst,traceLast,firstEq,lastEq,priorTrace,calledTrace,laterTrace,
      ready,_authenticated,collected,stored,reference,_agreement,_verified,_ciphertext,_atom,readyAtom,acceptedKeys⟩ :=
    RegistrationNativePlatformSecretWordTargetDesignatedRetained.designated_retained setup checks source route sign nativeInput nativeInside
      target.2.val pairs chosen.1 challenge outer target.2.val target.1.val publicPrekey view failure allocation reserveRegistration reservePeer reserveFrame
      erased helper reservePackets serverKeyId bounds mode work budget bounded reserved before initialCounter initialMarker ownersEmpty keysEmpty observed supported
      session target.2 chosen.2 chosenAt (.peer keyId) designated accepted
  let plainObserved := (observed.1,(observed.2.1,drop observed.2.2))
  have plainSupport := Set.mem_image_of_mem (Prod.map id (Prod.map id drop)) supported
  rw [←support_map,RegistrationNativePlatformSecretWordTargetPath.erase_run] at plainSupport
  have ledger := RegistrationNativeFullCompiler.ledger_projection setup.source.crypto wire serverKeyId bounds typed mode work before observed supported
  have plain := PqxdhDeploymentKemTransfer.designateIn_some setup.source.crypto (RegistrationNativeWire.ledgerCodec wire)
    serverKeyId budget observed.2.1.ledger.transcript (.peer keyId) (session,target.2) designated
  have acceptedOriginal := call.canonical
  rw [←ledger] at acceptedOriginal
  have prekey := RegistrationNativePlatformSecretWordPrekeyPublicationRun.peer_prekey setup checks source route sign nativeInput nativeInside
    target.2.val pairs chosen.1 challenge outer target.2.val target.1.val publicPrekey view failure allocation reserveRegistration reservePeer reserveFrame erased
    helper reservePackets serverKeyId bounds mode work (drop before) plainObserved ownersEmpty plainSupport keyId session.val call.raw
    (RegistrationRootInput.candidate call.packet) (collected.plain.verified.identity,collected.plain.verified.keys) pinned plain acceptedOriginal
    (RegistrationNativeKemPublicTarget.candidate_read wire call.raw call.packet call.decoded) acceptedKeys
  obtain ⟨response,_raw,_accepted,_keys,linked,_rawFound,_acceptedFound,_keysFound,_ownerBound,_published⟩ :=
    PqxdhDeploymentTranscript.designate_peer setup.source.crypto (RegistrationNativeWire.ledgerCodec wire) serverKeyId keyId
      observed.2.1.ledger.transcript session.val target.2.val plain
  rw [ledger] at linked
  obtain ⟨sameKey,payload,member⟩ := RegistrationNativeLinkedBuild.original observed.2.1.transcript keyId session.val response linked
  rw [call.recorded] at member
  have prior := RegistrationNativePlatformSecretWordTargetPath.path setup wire route sign nativeInput nativeInside provider outer controller serverKeyId bounds priorTrace
  have later := RegistrationNativePlatformSecretWordTargetPath.path setup wire route sign nativeInput nativeInside provider outer controller serverKeyId bounds laterTrace
  have called := Set.mem_image_of_mem (Prod.map id (Prod.map id drop)) calledTrace
  rw [←support_map,RegistrationNativePlatformSecretWordTargetPath.full] at called
  simp only [Prod.map_def,id_eq] at prior later called
  rw [←firstEq] at prior called
  rw [←lastEq] at later called
  obtain ⟨_plainFirst,_plainLast,left,right,recorded,_prior,_built,_later,_stored⟩ :=
    RegistrationNativePlatformSecretWordBuildChronology.response setup checks RegistrationNativePlatformConcreteSource.wire source route sign nativeInput nativeInside
      target.2.val pairs chosen.1 challenge outer target.2.val target.1.val publicPrekey view failure allocation reserveRegistration reservePeer reserveFrame erased
      helper writer serverKeyId bounds call.raw call.packet session.val call.decoded prior called later ready stored payload response member
  obtain ⟨buildFirst,buildLast,beforeBuild,built,afterBuild⟩ :=
    RegistrationNativeSecretWordTargetPath.split full laterTrace left _ right recorded
  have beforeSource := RegistrationNativePlatformSecretWordTargetPath.path setup wire route sign nativeInput nativeInside provider outer controller serverKeyId bounds beforeBuild
  have builtSource := Set.mem_image_of_mem (Prod.map id (Prod.map id drop)) built
  rw [←support_map,RegistrationNativePlatformSecretWordTargetPath.full] at builtSource
  simp only [Prod.map_def,id_eq] at beforeSource builtSource
  rw [←lastEq] at beforeSource
  obtain ⟨actual,selectedReady⟩ := RegistrationNativePlatformSecretWordBuildStored.full setup checks RegistrationNativePlatformConcreteSource.wire source route sign nativeInput nativeInside
    target.2.val pairs chosen.1 challenge outer target.2.val target.1.val publicPrekey view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
    serverKeyId bounds session.val payload response (buildFirst.1,drop buildFirst.2) (buildLast.1,drop buildLast.2) builtSource
  have slots := RegistrationNativePlatformSecretWordSessionSlotsSource.path setup checks RegistrationNativePlatformConcreteSource.wire source route sign nativeInput nativeInside
    target.2.val pairs chosen.1 challenge outer target.2.val target.1.val publicPrekey view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
    serverKeyId bounds beforeSource
  have equal := slots.2 session.val (List.getElem?_eq_some_iff.mp stored).1 actual selectedReady
  have same : actual=ready := Option.some.inj (Option.some.inj (equal.symm.trans stored))
  subst actual
  have throughAccept : Path full traceFirst [⟨.inl (.inr (.accept call.raw)),some session.val⟩] traceLast :=
    .cons _ _ _ _ _ [] calledTrace (.nil _)
  have buildPrefix := RegistrationNativeSecretWordTargetPathConcat.append full
    (RegistrationNativeSecretWordTargetPathConcat.append full priorTrace throughAccept) beforeBuild
  refine ⟨payload,response,ready,buildFirst,buildLast,
    (call.pre++[⟨.inl (.inr (.accept call.raw)),some session.val⟩])++left,right,sameKey,?_,buildPrefix,built,afterBuild,selectedReady,readyAtom,?_⟩
  · apply call.recorded.trans
    rw [recorded]
    simp only [List.append_assoc,List.cons_append,List.nil_append]
  · intro key realized
    rw [reference] at realized
    exact RegistrationNativeSecretWordTargetProtected.server_inside setup seed scalar RegistrationNativeSecretWordMessage.zero collected prekey key realized

end BeaconcryptCore.Computational.RegistrationNativePlatformDesignatedPeerTraced

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformDesignatedPeerTraced.selected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformDesignatedPeerTraced.selected
