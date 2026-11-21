-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformRecordPinnedDescriptor
import BeaconcryptCore.Computational.RegistrationNativePlatformRecordDesignatedHandle
import BeaconcryptCore.Computational.RegistrationNativePlatformRecordPhysicalWitness
import BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerJointSlots
import BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerJointG2Source
import BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerJointHidden
import BeaconcryptCore.Computational.RegistrationNativePlatformG3UniformRecordSample
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformRecordSessionIdealAttachment
open PqxdhServerAuthExperiment (Setup Checks)
open PqxdhDeploymentInterface (FreshBounds Mode Budget)
open RegistrationNativeSecretWordMessage (Message)
open RegistrationNativeSecretWord (Key Word)
open RegistrationNativeSecretWordService (Combined)
open RegistrationNativeSecretWordTargetPath (Path)
open PqxdhKemIndCca
variable {n : Nat} {I KemSK Platform E Physical A : Type} {base : OracleSpec I}
variable [primitive : BeaconcryptCore.Refinement.AdapterSealPrimitive.Operations]
    (setup : Setup base KemSK) (checks : Checks) (source : RegistrationNativeMldsa.Source)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (pairs : List (MlKem768PublicKey × KemSK)) (chosen : MlKem768PublicKey × KemSK) (challenge : MlKem768Ciphertext)
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
open RegistrationNativePlatformLorIdealSelected (unused NativePrivate NativeResult SourceResult sourceBefore)
variable (candidate : MlKemSharedSecret)
variable (physical : QueryImpl (PqxdhRecordLiftInterface.WorldSpec n) (StateT Physical ProbComp))
local notation "closedImpl" => RegistrationNativePlatformLorCtxClosed.implementation setup wire sign seed scalar candidate
  (unused (n := n)) (Fin.val (Prod.snd target)) pairs (Prod.fst chosen) challenge physical
local notation "nativeHandler" => RegistrationNativeSelectiveHiddenInterpreter.handler setup wire sign seed scalar candidate
  (RegistrationNativeSecretWordKemEarly.actual setup.baseImpl setup.kem (Fin.val (Prod.snd target)) pairs (Prod.fst chosen) challenge candidate)


local notation "nativeProvider"=>RegistrationNativeSecretWordKemEarly.actual setup.baseImpl setup.kem (Fin.val (Prod.snd target)) pairs (Prod.fst chosen) challenge candidate

omit primitive in
private theorem trace_source {B : Type}
    (body : OracleComp (RegistrationNativePublicFrontend.Spec n KemSK) B)
    (privateBefore : NativePrivate n KemSK) (physicalBefore : Physical)
    (slots : RegistrationNativePlatformPublicRecordSlots.State n) :
    (fun result=>(((result.1,result.2.2.1),result.2.2.2.1),result.2.2.2.2)) <$>
      (simulateQ (RegistrationNativePlatformRecordPartnerSlotTrace.handler setup wire sign seed scalar candidate nativeProvider physical) body).run
        (slots,RegistrationNativeG2Trace.initial,(privateBefore,physicalBefore))=
      (simulateQ physical ((simulateQ nativeHandler (RegistrationNativeG2Trace.program body)).run privateBefore)).run physicalBefore := by
  simpa only [RegistrationNativeG2Trace.program] using
    RegistrationNativePlatformRecordPartnerJointG2Source.source setup wire sign seed scalar candidate nativeProvider physical
      body privateBefore physicalBefore slots RegistrationNativeG2Trace.initial


omit primitive in
private theorem startup_pin (setup : Setup base KemSK) (source : RegistrationNativeMldsa.Source)
    (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64)
    (identity : PqxdhJointIdentity.PublicIdentity) (born : RegistrationNativeHiddenStartup.Started source)
    (supported : some born ∈ support (RegistrationNativeHiddenStartup.start (n := n) setup source ensureInit identityIndex serverKeyId identity)) :
    PqxdhRefinement.absBytes born.native.frontend.server.pin.binding.identity_public_key = identity.ed25519.toList := by
  simp only [RegistrationNativeHiddenStartup.start, mem_support_bind_iff] at supported
  obtain ⟨constructed, _constructed, continued⟩ := supported
  cases built : constructed.1 with
  | none => simp only [built, mem_support_pure_iff] at continued; cases continued
  | some created =>
      simp only [built, mem_support_bind_iff] at continued
      obtain ⟨generated, _generated, continued⟩ := continued
      cases sampled : generated with
      | none => simp only [sampled, mem_support_pure_iff] at continued; cases continued
      | some credential =>
          simp only [sampled, mem_support_bind_iff] at continued
          obtain ⟨installed, _installed, returned⟩ := continued
          simp only [mem_support_pure_iff, Option.some.injEq] at returned
          cases returned
          exact PqxdhRootTableInitialization.rootArray_bytes identity.ed25519

variable (route : RawCtxServerRouting.SenderDecoder)
local notation "codec"=>RegistrationNativeWire.ledgerCodec wire
local notation "service"=>PqxdhRecordLiftIdeal.ctxInterpreter (fun _=>PqxdhRecordLiftIdeal.KeyMode.random) id setup codec
local notation "actualPhysical"=>RegistrationNativePlatformLorIdealPhysical.implementation service codec route

/-- A pin-filtered original broad event on the actual joint source retains its original session, parsed selector and before-entry chronology in the physical or same-slot mismatch alternative. -/
theorem startup
    (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat)
    (previous : Platform) (privateBefore : NativePrivate n KemSK)
    (adversary : RegistrationNativeExperiment.Public →OracleComp (RegistrationNativeInterface.ModeSpec mode) A)
    (bounded : ∀publicInput,RegistrationNativeInterface.Respects budget (adversary publicInput))
    (reserved : budget.create≤pairs.length) (chosenAt : pairs[target.2.val]?=some chosen)
    (pool : privateBefore.1.pool=PqxdhLiveKemBirth.empty) (phase : privateBefore.1.provider=none)
    (warm : PqxdhRecordLiftIdeal.CtxPrivate n)
    (result : RegistrationNativeEntropyRun.Outcome
      (RegistrationNativePlatformSelectiveEntropyEnvironment.State n KemSK RegistrationNativeKemSwitchSource.Phase Platform source) A ×
      (RegistrationNativePlatformPublicRecordSlots.State n ×RegistrationNativeG2Trace.State ×
        RegistrationNativePlatformLorIdealPhysical.State n (PqxdhRecordLiftIdeal.CtxPrivate n)))
    (supported : result∈support (RegistrationNativePlatformRecordPartnerJointStartup.joint setup checks RegistrationNativePlatformConcreteSource.wire source
      seed scalar candidate nativeProvider target.2.val target.1.val view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
      actualPhysical ensureInit identityIndex serverKeyId previous privateBefore bounds mode adversary
      (CborRecordWorldClient.initial,PqxdhRecordLiftProtocol.initialControl,warm)))
    (finished : PqxdhRegistrationJointServerBirth.ClientCreated PqxdhTranscriptAd.AssociatedData ×(A×RegistrationNativeLedger.State)×
      RegistrationNativePlatformSelectiveEntropyEnvironment.State n KemSK RegistrationNativeKemSwitchSource.Phase Platform source)
    (present : finished∈result.1)
    (kind : RegistrationNativePlatformRecordSessionTargets.Kind)
    (event : RegistrationNativePlatformRecordSessionTargets.PinnedAt setup.source.crypto wire serverKeyId budget route kind target finished.2.1) :
    ∃priorList entry later,∃session:Fin budget.accept,
      finished.2.1.2.ledger.transcript=priorList++entry::later ∧
      RegistrationNativePlatformRecordSessionTargets.Witness setup.source.crypto codec serverKeyId budget route kind (session,target.2)
        finished.2.1.2.ledger.transcript priorList entry ∧
      RegistrationNativeParsedTargetCanonical.AcceptedAt wire finished.2.1.2.transcript session.val target.1.val ∧
      (RegistrationNativePlatformRecordPhysicalWitness.Physical codec route kind
        (PqxdhRecordLiftIdeal.viewOf (RegistrationNativeRecordPackage.encode result.1,result.2.2.2.2.1) result.2.2.2.2.2.base.produced) priorList entry ∨
        RegistrationNativePlatformRecordPartnerEvents.Mismatch budget (session,target.2) finished.2.1.2.ledger.transcript
          (PqxdhRecordLiftIdeal.handleSlot result.2.2.2.2.1)) := by
  have hiddenKept:=RegistrationNativePlatformRecordPartnerJointHidden.startup setup checks RegistrationNativePlatformConcreteSource.wire source
    seed scalar candidate nativeProvider target.2.val target.1.val view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
    route ensureInit identityIndex serverKeyId previous privateBefore bounds mode adversary warm result supported
  unfold RegistrationNativePlatformRecordPartnerJointStartup.joint at supported
  rw [mem_support_bind_iff] at supported
  obtain ⟨started,startedSupport,continued⟩:=supported
  cases built : started.1 with
  | none=>
    simp only [built,mem_support_pure_iff] at continued
    subst result
    cases present
  | some born=>
    have free : some born∈support (RegistrationNativeHiddenStartup.start (n:=n) setup source ensureInit identityIndex serverKeyId (setup.joint.publicKeys seed)) := by
      apply OracleComp.support_simulateQ_run'_subset actualPhysical _ (CborRecordWorldClient.initial,(PqxdhRecordLiftProtocol.initialControl,warm))
      rw [StateT.run'_eq,support_map]
      exact ⟨started,startedSupport,built⟩
    simp only [built,support_map] at continued
    obtain ⟨body,bodyCalled,rfl⟩:=continued
    have same : finished=(PqxdhRegistrationJointServerBirth.encode born.created,body.1.1,(body.1.2,body.2.2.2.1)) := by
      symm
      simpa only [Option.mem_some_iff] using present
    subst finished
    have cold:=RegistrationNativeG3NativeStartupFields.start_cold setup source ensureInit identityIndex serverKeyId (setup.joint.publicKeys seed) born free
    have pin:=startup_pin setup source ensureInit identityIndex serverKeyId (setup.joint.publicKeys seed) born free
    have traceCalled : (((body.1,body.2.2.1),body.2.2.2.1),body.2.2.2.2)∈support
      ((simulateQ actualPhysical ((simulateQ
        (RegistrationNativeSelectiveHiddenInterpreter.handler setup wire (RegistrationNativeMldsa.owned source born.native.credential) seed scalar candidate nativeProvider)
        (RegistrationNativeG2Trace.program (simulateQ RegistrationNativePlatformPublicCoinEmbedding.embed
          (RegistrationNativePlatformPublicFrontend.run setup checks RegistrationNativePlatformConcreteSource.wire source
            (RegistrationNativeMldsa.owned source born.native.credential) target.2.val target.1.val publicPrekey
            view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer serverKeyId bounds mode
            (adversary ⟨setup.joint.publicKeys seed,born.native.credential.publicKey,serverKeyId⟩) (born.native.frontend,previous))))).run privateBefore)).run started.2) := by
      rw [←trace_source setup (RegistrationNativeMldsa.owned source born.native.credential) seed scalar pairs chosen challenge
        budget target candidate actualPhysical _ privateBefore started.2 RegistrationNativePlatformPublicRecordSlots.initial,support_map]
      exact ⟨body,bodyCalled,rfl⟩
    obtain ⟨priorList,entry,later,session,handle,role,ordinal,message,ledger,witness,claimed,designated,accepted,pinned,installed,selected⟩:=
      RegistrationNativePlatformRecordPinnedDescriptor.selected setup checks source (RegistrationNativeMldsa.owned source born.native.credential)
        seed scalar pairs chosen challenge view failure allocation reserveRegistration reservePeer reserveFrame erased helper reservePackets
        serverKeyId bounds mode (adversary ⟨setup.joint.publicKeys seed,born.native.credential.publicKey,serverKeyId⟩) budget target candidate actualPhysical
        (bounded _) reserved chosenAt (born.native.frontend,previous) cold.2.2 cold.2.1 pin privateBefore started.2 pool phase
        (((body.1,body.2.2.1),body.2.2.2.1),body.2.2.2.2) traceCalled route kind event
    suffices hidden : (PqxdhRecordLiftIdeal.handleSlot body.2.2.2.2.2.1 handle).isSome by
      refine ⟨priorList,entry,later,session,ledger,witness,accepted,?_⟩
      exact RegistrationNativePlatformRecordPhysicalWitness.witness setup.source.crypto codec serverKeyId budget route kind (session,target.2)
        (PqxdhRecordLiftIdeal.viewOf
          (RegistrationNativeRecordPackage.encode (some (PqxdhRegistrationJointServerBirth.encode born.created,body.1.1,(body.1.2,body.2.2.2.1))),body.2.2.2.2.2.1)
          body.2.2.2.2.2.2.base.produced)
        (body.1.1.1,body.1.1.2.ledger,(PqxdhRegistrationJointServerBirth.encode born.created,body.1.1.2.transcript,(body.1.2,body.2.2.2.1)))
        (by rfl) priorList entry later ledger witness handle claimed hidden
    exact hiddenKept role ordinal message handle installed selected


/-- The genuine complete uniform sampler and warm startup internally discharge the reserved row and source-state conditions for the unchanged broad public event. -/
theorem initialized
    (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (previous : Platform)
    (adversary : RegistrationNativeExperiment.Public →OracleComp (RegistrationNativeInterface.ModeSpec mode) A)
    (bounded : ∀publicInput,RegistrationNativeInterface.Respects budget (adversary publicInput))
    (result : RegistrationNativeEntropyRun.Outcome
      (RegistrationNativePlatformSelectiveEntropyEnvironment.State (budget.cap 4+budget.cap 5) KemSK RegistrationNativeKemSwitchSource.Phase Platform source) A ×
      (RegistrationNativePlatformPublicRecordSlots.State (budget.cap 4+budget.cap 5) ×RegistrationNativeG2Trace.State ×
        RegistrationNativePlatformLorIdealPhysical.State (budget.cap 4+budget.cap 5) (PqxdhRecordLiftIdeal.CtxPrivate (budget.cap 4+budget.cap 5))))
    (supported : result∈support (RegistrationNativePlatformRecordPartnerJointUniform.joint setup checks RegistrationNativePlatformConcreteSource.wire route source
      ensureInit identityIndex serverKeyId target.1.val view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
      bounds mode adversary budget target.2 previous))
    (finished : PqxdhRegistrationJointServerBirth.ClientCreated PqxdhTranscriptAd.AssociatedData ×(A×RegistrationNativeLedger.State)×
      RegistrationNativePlatformSelectiveEntropyEnvironment.State (budget.cap 4+budget.cap 5) KemSK RegistrationNativeKemSwitchSource.Phase Platform source)
    (present : finished∈result.1)
    (kind : RegistrationNativePlatformRecordSessionTargets.Kind)
    (event : RegistrationNativePlatformRecordSessionTargets.PinnedAt setup.source.crypto wire serverKeyId budget route kind target finished.2.1) :
    ∃priorList entry later,∃session:Fin budget.accept,
      finished.2.1.2.ledger.transcript=priorList++entry::later ∧
      RegistrationNativePlatformRecordSessionTargets.Witness setup.source.crypto codec serverKeyId budget route kind (session,target.2)
        finished.2.1.2.ledger.transcript priorList entry ∧
      RegistrationNativeParsedTargetCanonical.AcceptedAt wire finished.2.1.2.transcript session.val target.1.val ∧
      (RegistrationNativePlatformRecordPhysicalWitness.Physical codec route kind
        (PqxdhRecordLiftIdeal.viewOf (RegistrationNativeRecordPackage.encode result.1,result.2.2.2.2.1) result.2.2.2.2.2.base.produced) priorList entry ∨
        RegistrationNativePlatformRecordPartnerEvents.Mismatch budget (session,target.2) finished.2.1.2.ledger.transcript
          (PqxdhRecordLiftIdeal.handleSlot result.2.2.2.2.1)) := by
  unfold RegistrationNativePlatformRecordPartnerJointUniform.joint at supported
  rw [mem_support_bind_iff] at supported
  obtain ⟨parameters,sampled,continued⟩:=supported
  have free : parameters.1∈support (RegistrationNativePlatformG3UniformRecordProgram.sample setup budget target.2) := by
    have inner : parameters.1∈support (simulateQ (PqxdhRecordLiftInterface.coinLift (n:=budget.cap 4+budget.cap 5))
        (RegistrationNativePlatformG3UniformRecordProgram.sample setup budget target.2)) := by
      apply OracleComp.support_simulateQ_run'_subset
        (RegistrationNativePlatformLorIdealPhysical.implementation
          (PqxdhRecordLiftIdeal.ctxInterpreter (fun _=>PqxdhRecordLiftIdeal.KeyMode.random) id setup codec) codec route)
        _ (CborRecordWorldClient.initial,PqxdhRecordLiftProtocol.initialControl,PqxdhRecordLiftIdeal.CtxPrivate.initial)
      rw [StateT.run'_eq,support_map]
      exact ⟨parameters,sampled,rfl⟩
    exact PqxdhDeploymentEnvironment.support_simulateQ_subset (PqxdhRecordLiftInterface.coinLift (n:=budget.cap 4+budget.cap 5)) _ inner
  obtain ⟨reserved,chosen,chosenAt,chosenPublic⟩:=RegistrationNativePlatformG3UniformRecordSample.sample_selected setup budget target.2 parameters.1 free
  have genuine : parameters.1.profile.pairs[target.2.val]?=some (parameters.1.profile.publicKey,chosen.2) :=
    chosenAt.trans (congrArg some (Prod.ext chosenPublic rfl))
  have frame:=RegistrationNativePlatformRecordPartnerSampler.frame
    (PqxdhRecordLiftIdeal.ctxInterpreter (fun _=>PqxdhRecordLiftIdeal.KeyMode.random) id setup codec) codec route
    (RegistrationNativePlatformG3UniformRecordProgram.sample setup budget target.2)
    (CborRecordWorldClient.initial,PqxdhRecordLiftProtocol.initialControl,PqxdhRecordLiftIdeal.CtxPrivate.initial) parameters sampled
  have physicalEq : parameters.2=(CborRecordWorldClient.initial,PqxdhRecordLiftProtocol.initialControl,parameters.2.2.2) :=
    Prod.ext frame.1 (Prod.ext frame.2 rfl)
  rw [physicalEq] at continued
  exact startup setup checks source parameters.1.seed parameters.1.scalar parameters.1.profile.pairs
    (parameters.1.profile.publicKey,chosen.2) parameters.1.profile.challenge view failure allocation reserveRegistration reservePeer reserveFrame erased helper reservePackets
    serverKeyId bounds mode budget target parameters.1.candidate route ensureInit identityIndex previous
    (RegistrationNativePlatformG3UniformOpaqueNative.privateState none budget parameters.1.materials) adversary bounded reserved genuine rfl rfl
    parameters.2.2.2 result continued finished present kind event

end BeaconcryptCore.Computational.RegistrationNativePlatformRecordSessionIdealAttachment

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordSessionIdealAttachment.startup' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordSessionIdealAttachment.startup

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordSessionIdealAttachment.initialized' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordSessionIdealAttachment.initialized
