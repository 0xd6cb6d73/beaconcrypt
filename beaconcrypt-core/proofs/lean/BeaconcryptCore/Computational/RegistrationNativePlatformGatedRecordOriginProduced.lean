-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformGatedRecordOriginStartup
import BeaconcryptCore.Computational.PqxdhRecordFactsOriginInvariant
/-! Genuine current source startup and every post-send reserve retain produced-frame dictionary origin. A refused reserve never erases the already attempted source frame. -/
open OracleComp OracleSpec CoreModels Aeneas ENNReal
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformGatedRecordOriginProduced
open PqxdhServerAuthExperiment (Setup Checks)
open PqxdhRecordLiftInterface (WorldSpec coinLift effectLift)
open RegistrationNativeHiddenInterpreter (Provider)
open RegistrationNativePlatformSelectiveEntropyEnvironment (State)
open RegistrationNativePlatformSelectiveEntropyEffects (close close_run effect_source)
variable [primitive : BeaconcryptCore.Refinement.AdapterSealPrimitive.Operations]
variable {n : Nat} {I KemSK ProviderState Platform E Secret Reader Response Value : Type} {base : OracleSpec I}
variable (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (source : RegistrationNativeMldsa.Source)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret) (provider : Provider KemSK ProviderState)
    (selectedOwner selectedAccept : Nat)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
    (reserveFrame : Nat → StateT Platform ProbComp (core.result.Result Unit E)) (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (BeaconcryptCore.Refinement.AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))



open PqxdhRecordLiftIdeal (CtxPrivate KeyMode)
open PqxdhRecordLiftWorldCompiler (Label)
variable (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64)
    (previous : Platform) (privateBefore : RegistrationNativeSelectiveHiddenInterpreter.State n KemSK ProviderState)
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (route : RawCtxServerRouting.SenderDecoder)
local notation "codec" => RegistrationNativeWire.ledgerCodec (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire)
local notation "reference" => RegistrationNativePlatformSelectiveEntropyStartup.referenceProgram (n := n) setup checks wire source seed scalar candidate provider selectedOwner selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer ensureInit identityIndex serverKeyId previous privateBefore bounds mode adversary
local notation "FullResult" => RegistrationNativeEntropyRun.Result n (State n KemSK ProviderState Platform source) Value


local notation "run" => RegistrationNativePlatformGatedRecordBindingStartup.run (n := n) setup checks wire source seed scalar candidate provider selectedOwner selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer ensureInit identityIndex serverKeyId previous privateBefore bounds mode adversary route
local notation "startup" => RegistrationNativeHiddenStartup.start setup source ensureInit identityIndex serverKeyId (setup.joint.publicKeys seed)

/-- The actual complete source run derives its dictionary/produced-frame invariant directly from its own literal World program, including all public reserve failures. -/
theorem invariant (modes : Label n → KeyMode) (ideal : ∀label,modes label ≠ .real)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (result : FullResult) (supported : result ∈ support (run modes replace)) :
    PqxdhRecordFactsOriginInvariant.Invariant result.1.2 result.2 := by
  rw [← RegistrationNativePlatformGatedRecordBindingStartup.source_run setup checks wire source seed scalar candidate provider selectedOwner selectedAccept
    view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer ensureInit identityIndex serverKeyId previous privateBefore bounds mode adversary route modes replace,support_map] at supported
  obtain ⟨full,called,rfl⟩ := supported
  exact PqxdhRecordFactsOriginInvariant.schedule_invariant modes ideal replace setup codec route
    ((simulateQ CborRecordWorldClient.handler
      (RegistrationNativePlatformSelectiveEntropyStartup.program (n := n) setup checks wire source seed scalar candidate provider selectedOwner selectedAccept
        view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer ensureInit identityIndex serverKeyId previous privateBefore bounds mode adversary)).run CborRecordWorldClient.initial)
    PqxdhRecordLiftProtocol.initialControl CtxPrivate.initial PqxdhRecordFactsOriginInvariant.initial_invariant full called

/-- Every reached hidden seal has its exact attempted source frame at the same final counterpart handle; successful encoder output is not required. -/
theorem dictionary (modes : Label n → KeyMode) (ideal : ∀label,modes label ≠ .real)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (result : FullResult) (supported : result ∈ support (run modes replace))
    (label : Label n) (entry : CtxRomAuth.CtxSuccessfulSeal) (member : entry ∈ (result.2.keys label).1.successfulSeals) :
    ∃ handle frame,PqxdhRecordFactsOriginHandles.OwnsLabel result.1.2 label handle ∧
      (some handle,frame) ∈ result.2.base.produced ∧ PqxdhRecordFactsOriginReplay.Matches frame entry := by
  have good := invariant setup checks wire source seed scalar candidate provider selectedOwner selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame
    erased helper writer ensureInit identityIndex serverKeyId previous privateBefore bounds mode adversary route modes ideal replace result supported
  obtain ⟨tag,frame,⟨handle,rfl,owned⟩,produced,matched⟩ := good.2.1 label entry member
  exact ⟨handle,frame,owned,produced,matched⟩
/-- Every original ledger record of the actual warm source run has same-run acceptance and publication evidence. -/
theorem ledger (modes : Label n → KeyMode) (ideal : ∀label,modes label ≠ .real)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (readback : PqxdhServerAuthNegativeControl.FrameReadBack codec)
    (result : FullResult) (supported : result ∈ support (run modes replace)) :
    ∀ born ∈ result.1.1,PqxdhRecordFactsBindingLedger.LedgerEvidence codec route result.1.2 result.2 born.2.1.2.ledger.transcript := by
  rw [RegistrationNativePlatformGatedRecordBindingStartup.run_start,mem_support_bind_iff] at supported
  obtain ⟨started,startReached,continued⟩ := supported
  rcases started with ⟨⟨⟨_ | born,shell⟩,control⟩,secret⟩
  · simp only [mem_support_pure_iff] at continued
    subst result
    simp
  · have safe := (RegistrationNativeRecordHandleSlots.interpreted
      (PqxdhRecordLiftIdeal.ctxInterpreter modes replace setup codec) codec route _ _ _
      PqxdhRecordLiftProtocolHistory.initial_safe _ _ startReached).1
    exact RegistrationNativePlatformGatedNativeRecordLedger.initialized modes ideal replace setup codec route readback
      (RegistrationNativePlatformSelectiveEntropyQuery.environment setup checks (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) source born.native.credential seed scalar candidate provider selectedOwner selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer (pure none))
      (fun amount => RegistrationNativePlatformSelectiveEntropyEffects.liftPlatform (reserveFrame amount)) serverKeyId bounds mode
      (adversary ⟨setup.joint.publicKeys seed,born.native.credential.publicKey,serverKeyId⟩) born.created
      ((born.native.frontend,previous),privateBefore) shell control safe secret result continued

/-- A hidden receive in the actual source run cannot lack an attempted counterpart frame, including sends refused only after sealing. -/
theorem not_unproduced (modes : Label n → KeyMode) (ideal : ∀label,modes label ≠ .real)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (readback : PqxdhServerAuthNegativeControl.FrameReadBack codec)
    (result : FullResult) (supported : result ∈ support (run modes replace)) :
    ¬PqxdhRecordLiftIdeal.UnproducedAccept codec route (RegistrationNativeRecordBindingEvent.view result) := by
  rintro ⟨value,valueMember,entry,entryMember,receiver,raw,decrypted,handle,slot,frame,
    received,routed,hidden,decoded,neverProduced⟩
  change value ∈ result.1.1.map _ at valueMember
  rw [Option.mem_def,Option.map_eq_some_iff] at valueMember
  obtain ⟨born,bornMember,rfl⟩ := valueMember
  have facts := ledger setup checks wire source seed scalar candidate provider selectedOwner selectedAccept
    view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer ensureInit identityIndex serverKeyId previous privateBefore bounds mode adversary route
    modes ideal replace readback result supported born bornMember
  rcases facts.accepted entry entryMember receiver raw decrypted handle received routed with known | ⟨label,installed,direction,actualFrame,actualDecoded,sealedEntry,member,matched,_⟩
  · have absent := PqxdhRecordFactsOriginAccepted.known_no_slot result.1.2 handle known
    change PqxdhRecordLiftIdeal.handleSlot result.1.2 handle = some slot at hidden
    rw [absent] at hidden
    cases hidden
  · have slotEq : label.slot = slot := Option.some.inj (installed.symm.trans hidden)
    have frameEq : actualFrame = frame := Option.some.inj (actualDecoded.symm.trans decoded)
    subst actualFrame
    obtain ⟨sender,producedFrame,owns,produced,producedMatches⟩ := dictionary setup checks wire source seed scalar candidate provider selectedOwner selectedAccept
      view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer ensureInit identityIndex serverKeyId previous privateBefore bounds mode adversary route
      modes ideal replace result supported label sealedEntry member
    have sameFrame := PqxdhRecordFactsOriginAccepted.matches_unique frame producedFrame sealedEntry matched producedMatches
    subst producedFrame
    have counterpart := PqxdhRecordFactsOriginHandles.counterpart_of_opposite result.1.2 label sender handle owns direction
    rw [slotEq] at counterpart
    exact neverProduced sender counterpart produced

/-- The structural unproduced-frame event has probability zero in the literal complete source execution. -/
theorem unproduced_zero (modes : Label n → KeyMode) (ideal : ∀label,modes label ≠ .real)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (readback : PqxdhServerAuthNegativeControl.FrameReadBack codec) :
    𝒟[(fun result => PqxdhRecordLiftIdeal.unproducedEvent codec route (RegistrationNativeRecordBindingEvent.view result)) <$> run modes replace] {true} = 0 := by
  rw [←prEvent_eq_evalDist_singleton _ true]
  apply prEvent_eq_zero_of_not_mem_support
  rw [support_map]
  rintro ⟨result,supported,winning⟩
  have impossible := not_unproduced setup checks wire source seed scalar candidate provider selectedOwner selectedAccept
    view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer ensureInit identityIndex serverKeyId previous privateBefore bounds mode adversary route
    modes ideal replace readback result supported
  simp only [PqxdhRecordLiftIdeal.unproducedEvent,decide_eq_true_eq] at winning
  exact impossible winning

end BeaconcryptCore.Computational.RegistrationNativePlatformGatedRecordOriginProduced

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformGatedRecordOriginProduced.invariant' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformGatedRecordOriginProduced.invariant

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformGatedRecordOriginProduced.dictionary' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformGatedRecordOriginProduced.dictionary

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformGatedRecordOriginProduced.ledger' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformGatedRecordOriginProduced.ledger

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformGatedRecordOriginProduced.not_unproduced' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformGatedRecordOriginProduced.not_unproduced

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformGatedRecordOriginProduced.unproduced_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformGatedRecordOriginProduced.unproduced_zero
