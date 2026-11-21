import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordTargetPublicationRun
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordTargetAcceptedCall
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordTargetBornKey
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordTargetRetained
-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordTargetPublication
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordTargetRoster
import BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetPublicationRun
import BeaconcryptCore.Computational.RegistrationNativeTargetLedgerCore
import BeaconcryptCore.Computational.RegistrationNativeLedgerJournal
import BeaconcryptCore.Computational.RegistrationNativeKemPublicTarget
import BeaconcryptCore.Computational.RegistrationNativeParsedTargetCanonical
/-! The current concrete dynamic publication is attached to the original full native ledger and the retained final owner roster. Constructor extensions, stateful writer failures and later callbacks retain all earlier successful publication receipts. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordTargetDesignatedRetained
attribute [local irreducible] RegistrationNativePlatformSecretWordOpen.accept
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeSecretWordMessage (Message)
open RegistrationNativeSecretWord (Key)
open RegistrationNativeSecretWordService (Combined)
open RegistrationNativeSecretWordTargetAlignment (Aligned)
open RegistrationNativeSecretWordTargetPublication (key)
open PqxdhKemIndCca
variable {n : Nat} {I KemSK Platform E A : Type} {base : OracleSpec I}
variable [primitive : BeaconcryptCore.Refinement.AdapterSealPrimitive.Operations]
    (setup : Setup base KemSK) (checks : Checks) (source : RegistrationNativeMldsa.Source)
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
    (reservePackets : Usize → StateT Platform ProbComp (core.result.Result Unit E))

open RegistrationNativePlatformSecretWordAliasAlignment (State)
local notation "wire" => RegistrationNativePlatformOrdinaryExperiment.canonicalWire RegistrationNativePlatformConcreteSource.wire
local notation "writer" => RegistrationNativePlatformConcreteSource.writer reservePackets
local notation "provider" => RegistrationNativeSecretWordKemEarly.early setup.baseImpl setup.kem selected pairs publicKey challenge
local notation "implementation" => RegistrationNativeSecretWordTargetSource.implementation (n := n) setup wire route sign input inside provider outer
local notation "controller" => RegistrationNativePlatformSecretWordFrontend.handler (n := n) setup checks wire source sign
  selectedOwner selectedAccept publicPrekey view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
local notation "typed" => RegistrationNativePlatformSecretWordExecution.typed (n := n) setup wire route sign input inside provider outer controller



open RegistrationNativePlatformSecretWordExecution (TracedState drop)
open RegistrationNativeSecretWordTargetCall (Call)
open RegistrationNativeSecretWordTargetPath (Path)
local notation "traceState" => TracedState (RegistrationNativePlatformSecretWordOrdinary.State source Platform) n KemSK
local notation "traceTyped" => RegistrationNativePlatformSecretWordExecution.traced (n := n) setup wire route sign input inside provider outer controller

/-- Broad original designation identifies the same canonical source accept and its actual atom-bearing Ready, including later-created owner aliases and stateful writer failures. -/
theorem designated_retained (serverKeyId : U64) (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) A) (budget : PqxdhDeploymentInterface.Budget)
    (bounded : RegistrationNativeInterface.Respects budget work) (reserved : budget.create ≤ pairs.length)
    (before : traceState) (initialCounter : before.1.1.parsedAccepts=0) (initialMarker : before.2.2.kem.2=none)
    (ownersEmpty : before.1.1.beacons=[]) (keysEmpty : before.2.2.kem.1.keys=[])
    (result : A × (RegistrationNativeLedger.State × traceState))
    (supported : result ∈ support (RegistrationNativeFullCompiler.run setup.source.crypto wire serverKeyId bounds traceTyped mode work before))
    (session : Fin budget.accept) (ownerIndex : Fin budget.capacity) (privateKey : KemSK)
    (chosenAt : pairs[ownerIndex.val]? = some (publicKey,privateKey))
    (handle : PqxdhDeploymentInterface.Handle)
    (designated : PqxdhDeploymentTranscript.designateIn setup.source.crypto (RegistrationNativeWire.ledgerCodec wire)
      serverKeyId budget result.2.1.ledger.transcript handle = some (session,ownerIndex))
    (accepted : RegistrationNativeParsedTargetCanonical.AcceptedAt wire result.2.1.transcript session.val selectedAccept) :
    ∃ call : Call traceState traceTyped (fun current => current.1.1.parsedAccepts) wire selectedAccept result.2.1.transcript session.val,
      call.first.2.2.kem.2=none ∧
      ∃ first last : RegistrationNativeLedger.State × traceState,
        call.first=first.2 ∧ call.last=last.2 ∧
        Path (RegistrationNativeFullCompiler.handler setup.source.crypto wire serverKeyId bounds traceTyped)
          (RegistrationNativeLedger.empty,before) call.pre first ∧
        (some session.val,last) ∈ support ((RegistrationNativeFullCompiler.handler setup.source.crypto wire serverKeyId bounds traceTyped
          (.inl (.inr (.accept call.raw)))).run first) ∧
        Path (RegistrationNativeFullCompiler.handler setup.source.crypto wire serverKeyId bounds traceTyped) last call.post result.2 ∧
      ∃ (ready : RegistrationNativeSecretWordMessage.ServerReady) (authenticated : registration.AuthenticatedInit)
        (collected : RegistrationNativeSecretWordServerCollect.Input registration.InitPacket Unit PqxdhJointIdentity.PeerEncoding),
        call.last.1.1.server.sessions[session.val]?=some (some ready) ∧
        ready.reference=RegistrationNativeSecretWordServerRoot.message collected ∧
        ready.agreement=⟨PqxdhServerClearedRoot.pending authenticated.binding.server_pin.binding collected.plain,authenticated.binding⟩ ∧
        collected.plain.verified=RegistrationRootInput.verified call.packet authenticated ∧
        collected.plain.ciphertext=PqxdhAcceptedRegistration.ciphertextArray challenge ∧
        collected.kem=RegistrationNativeSecretWord.Word.atom ∧ ready.reference.kem=RegistrationNativeSecretWord.Word.atom ∧
        PqxdhDeploymentTranscript.acceptedKeys setup.source.crypto (RegistrationRootInput.candidate call.packet)=
          some (collected.plain.verified.identity,collected.plain.verified.keys) := by
  have erasedSupport := Set.mem_image_of_mem (Prod.map id (Prod.map id drop)) supported
  rw [←support_map,RegistrationNativePlatformSecretWordTargetPath.erase_run] at erasedSupport
  let plainResult := (result.1,(result.2.1,drop result.2.2))
  have plainSupport : plainResult ∈ support (RegistrationNativeFullCompiler.run setup.source.crypto wire serverKeyId bounds typed mode work (drop before)) := erasedSupport
  obtain ⟨call,marker,first,last,firstEq,lastEq,prior,called,suffix⟩ :=
    RegistrationNativePlatformSecretWordTargetAcceptedCall.accepted_call setup checks RegistrationNativePlatformConcreteSource.wire source
      route sign input inside selected pairs publicKey challenge outer selectedOwner selectedAccept publicPrekey view failure allocation
      reserveRegistration reservePeer reserveFrame erased helper writer serverKeyId bounds mode work before initialCounter initialMarker result supported session.val accepted
  obtain ⟨owner,raw,packet,keys,ownerAt,acceptFound,parsed,keysFound,publicMatches⟩ :=
    RegistrationNativePlatformSecretWordTargetPublicationRun.designated_public setup checks source route sign input inside selected pairs publicKey challenge outer
      selectedOwner selectedAccept publicPrekey view failure allocation reserveRegistration reservePeer reserveFrame erased helper reservePackets serverKeyId
      bounds mode work (drop before) plainResult plainSupport budget handle (session,ownerIndex) designated
  obtain ⟨pair,pairAt,_row,ownerKey⟩ := RegistrationNativePlatformSecretWordTargetBornKey.full_born_key setup checks
    RegistrationNativePlatformConcreteSource.wire source route sign input inside selected pairs publicKey challenge outer selectedOwner selectedAccept publicPrekey
    view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer serverKeyId bounds mode work budget bounded reserved
    (drop before) ownersEmpty keysEmpty plainResult plainSupport ownerIndex.val owner ownerAt
  have pairEq : pair=(publicKey,privateKey) := Option.some.inj (pairAt.symm.trans chosenAt)
  have chosenKey : owner.view.kemPublic=publicKey := ownerKey.trans (congrArg Prod.fst pairEq)
  have consistent := RegistrationNativeFullCompiler.ledger_projection setup.source.crypto wire serverKeyId bounds typed mode work (drop before) plainResult plainSupport
  rw [consistent,call.canonical] at acceptFound
  have sameRaw : call.raw=raw := Option.some.inj acceptFound
  rw [←sameRaw,call.decoded] at parsed
  have samePacket : call.packet=packet := Option.some.inj parsed
  have matching : (PqxdhDeploymentTranscript.acceptedKeys setup.source.crypto (RegistrationRootInput.candidate call.packet)).map
      (fun keys => keys.2.pqKey)=some publicKey := by
    rw [samePacket,keysFound,Option.map_some,publicMatches,chosenKey]
  have plainCall := Set.mem_image_of_mem (Prod.map id drop) call.reached
  rw [←support_map,RegistrationNativePlatformSecretWordExecution.traced_source] at plainCall
  have retained := RegistrationNativePlatformSecretWordTargetRetained.accept_retained setup checks RegistrationNativePlatformConcreteSource.wire source
    route sign input inside selected pairs publicKey challenge outer selectedOwner selectedAccept publicPrekey view failure allocation reserveRegistration reservePeer
    reserveFrame erased helper writer call.packet (drop call.first) (drop call.last) session.val call.selected marker matching plainCall
  exact ⟨call,marker,first,last,firstEq,lastEq,prior,called,suffix,retained⟩

end BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordTargetDesignatedRetained

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordTargetDesignatedRetained.designated_retained' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordTargetDesignatedRetained.designated_retained
