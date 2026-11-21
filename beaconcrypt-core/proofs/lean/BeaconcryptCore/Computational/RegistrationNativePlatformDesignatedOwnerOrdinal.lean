import BeaconcryptCore.Computational.RegistrationNativePlatformDesignatedOwnerInputs
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordOwnerTracedFinish
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordPendingPin
-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformDesignatedPeerTraced
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordInstallLedger
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordInstallMonotone
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordInstallPeerTraced
import BeaconcryptCore.Computational.RegistrationNativeSecretWordInstallWitness
import BeaconcryptCore.Computational.RegistrationNativeSelectiveHiddenDemand
import BeaconcryptCore.Computational.RegistrationNativeInstallKernelStorage

/-! The original broadly designated owner has its protected descriptor at the matching actual successful public installation ordinal. Actual source readback fixes its response ciphertext and configured pin; the current immutable pin, pending binding, public mask and private row invariants are derived on its same full-ledger prefix. Failed calls, platform state and later callbacks remain literal. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformDesignatedOwnerOrdinal
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

/-- Every original broadly designated owner has its protected descriptor at its matching actual successful public installation ordinal. -/
theorem ordinal (bounded : RegistrationNativeInterface.Respects budget work) (reserved : budget.create ≤ pairs.length)
    (chosenAt : pairs[target.2.val]?=some chosen) (before : State)
    (initialCounter : before.1.1.parsedAccepts=0) (initialMarker : before.2.2.kem.2=none)
    (ownersEmpty : before.1.1.beacons=[]) (keysEmpty : before.2.2.kem.1.keys=[])
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
  obtain ⟨same,raw,packet,application,pre,post,first,last,recorded,prior,called,later,_decoded,ciphertext,pins⟩ :=
    RegistrationNativePlatformDesignatedOwnerInputs.selected setup checks source route sign seed scalar pairs chosen challenge outer view failure allocation
      reserveRegistration reservePeer reserveFrame erased helper reservePackets serverKeyId bounds mode work budget target bounded reserved chosenAt
      before initialCounter initialMarker ownersEmpty keysEmpty observed supported session owner designated accepted
  subst owner
  have plainPrior := RegistrationNativePlatformSecretWordTargetPath.path setup wire route sign nativeInput nativeInside provider outer controller serverKeyId bounds prior
  simp only [Prod.map_def,id_eq] at plainPrior
  have canonical := RegistrationNativePlatformSecretWordPrekeyMask.path_keeps setup checks wire source sign target.2.val target.1.val publicPrekey
    view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer route nativeInput nativeInside provider outer serverKeyId bounds plainPrior
    (by change RegistrationNativePublicOwnerMask.Canonical target.2.val publicPrekey before.1.1.beacons;rw [ownersEmpty];exact RegistrationNativePublicOwnerMask.empty _ _)
  have coherent := RegistrationNativePlatformSecretWordPendingPin.path_keeps setup checks wire source sign target.2.val target.1.val publicPrekey
    view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer route nativeInput nativeInside provider outer serverKeyId bounds plainPrior
    (by change RegistrationNativeSecretWordPendingPin.Holds before.1.1.beacons;rw [ownersEmpty];intro index current found;simp only [List.getElem?_nil] at found;cases found)
  let plainFull := RegistrationNativeFullCompiler.handler setup.source.crypto wire serverKeyId bounds plainTyped
  have alignment : ∀ (query : RegistrationNativeInterface.FullSpec.Domain)
      (before : RegistrationNativeLedger.State × RegistrationNativePlatformSecretWordAliasAlignment.State n KemSK source Platform)
      (result : RegistrationNativeInterface.FullSpec.Range query × (RegistrationNativeLedger.State × RegistrationNativePlatformSecretWordAliasAlignment.State n KemSK source Platform)),
      RegistrationNativeSecretWordTargetAlignment.Aligned before.2.1.1.beacons before.2.2.kem.1.keys →
      result ∈ support ((plainFull query).run before) →
      RegistrationNativeSecretWordTargetAlignment.Aligned result.2.2.1.1.beacons result.2.2.2.kem.1.keys := by
    intro query current result valid reached
    dsimp only [plainFull] at reached
    rw [RegistrationNativeFullCompiler.handler,RegistrationNativeLedger.interpreted,
      QueryImpl.flattenStateT_mapStateTBase_apply_run,support_map] at reached
    obtain ⟨returned,queried,equal⟩ := reached
    rw [RegistrationNativeRawAdapter.program_native] at queried
    have kept := RegistrationNativePlatformSecretWordAliasAlignment.program_keeps setup checks wire source route sign nativeInput nativeInside
      target.2.val pairs chosen.1 challenge outer target.2.val target.1.val publicPrekey view failure allocation reserveRegistration reservePeer reserveFrame erased
      helper writer _ current.2 valid returned queried
    cases equal
    exact kept
  have aligned := RegistrationNativeSecretWordTargetPath.preserves plainFull
    (fun current => RegistrationNativeSecretWordTargetAlignment.Aligned current.2.1.1.beacons current.2.2.kem.1.keys)
    (fun query current result valid reached => alignment query current result valid reached) plainPrior
    (by change RegistrationNativeSecretWordTargetAlignment.Aligned before.1.1.beacons before.2.2.kem.1.keys;rw [ownersEmpty,keysEmpty];exact RegistrationNativeSecretWordTargetAlignment.empty)
  obtain ⟨ready,atom,_realized,protectedHeads,own⟩ := RegistrationNativePlatformSecretWordOwnerTracedFinish.finish setup checks wire route sign seed scalar
    target.2.val target.1.val pairs chosen.1 challenge outer view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer packet application
    first.2 last.2 canonical aligned
    (fun current found => (congrArg PqxdhRefinement.absBytes (pins current found)).trans serverPin)
    (by intro current found pending oneTime phase;have valid:=coherent target.2.val current found;unfold RegistrationNativeSecretWordPendingPin.Coherent at valid;rw [phase] at valid;exact valid)
    ciphertext called
  have counted := RegistrationNativePlatformSecretWordInstallLedger.path setup checks RegistrationNativePlatformConcreteSource.wire source route sign nativeInput nativeInside
    target.2.val pairs chosen.1 challenge outer target.2.val target.1.val publicPrekey view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
    candidate serverKeyId bounds before initialTrace prior .beacon
  have recordedPrefix := RegistrationNativePlatformSecretWordTargetPath.records setup wire route sign nativeInput nativeInside provider outer controller serverKeyId bounds prior
  simp only [RegistrationNativeLedger.empty,List.nil_append] at recordedPrefix
  have count : (RegistrationNativeSecretWordInstallOrdinals.messages .beacon first.2.2.1.events).length=
      (RegistrationNativeInstallOrdinals.handles .beacon pre).length := by
    simpa only [RegistrationNativeInstallOrdinals.Counts,RegistrationNativePlatformSecretWordInstallLedger.events,
      RegistrationNativeSecretWordInstallOrdinals.messages_eval,List.length_map,recordedPrefix] using counted
  obtain ⟨tail,suffix⟩ := RegistrationNativePlatformSecretWordInstallMonotone.path setup wire route sign nativeInput nativeInside provider outer controller
    serverKeyId bounds .beacon later
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
end BeaconcryptCore.Computational.RegistrationNativePlatformDesignatedOwnerOrdinal

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformDesignatedOwnerOrdinal.ordinal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformDesignatedOwnerOrdinal.ordinal
