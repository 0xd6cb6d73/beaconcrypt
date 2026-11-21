-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerHandleLedger
import BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerSnapshotExecution
import BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerSnapshot
import BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerSnapshotCoverage
import BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceAcceptedCall
import BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealSelected
/-! Every actual native snapshot run has the same complete candidate-independent symbolic source execution. Native trace, public successful-session ledger, persistent platform/private state, and physical state are retained; the selected parsed accept coordinate remains separate from the public session coordinate. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerPointwise
open PqxdhServerAuthExperiment (Setup Checks)
open PqxdhKemIndCca
variable {n : Nat} {I KemSK Platform E Physical A : Type} {base : OracleSpec I}
variable [primitive : BeaconcryptCore.Refinement.AdapterSealPrimitive.Operations]
    (setup : Setup base KemSK) (checks : Checks) (source : RegistrationNativeMldsa.Source)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (pairs : List (MlKem768PublicKey × KemSK)) (chosen : MlKem768PublicKey × KemSK) (challenge : MlKem768Ciphertext)
    (selectedOwner selectedAccept : Nat)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
    (reserveFrame : Nat → StateT Platform ProbComp (core.result.Result Unit E)) (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (BeaconcryptCore.Refinement.AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (reservePackets : Usize → StateT Platform ProbComp (core.result.Result Unit E))
    (serverKeyId : U64) (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) A)
    (candidate : MlKemSharedSecret)
    (physical : QueryImpl (PqxdhRecordLiftInterface.WorldSpec n) (StateT Physical ProbComp))
local notation "wire" => RegistrationNativePlatformOrdinaryExperiment.canonicalWire RegistrationNativePlatformConcreteSource.wire
local notation "writer" => RegistrationNativePlatformConcreteSource.writer reservePackets
local notation "unused" => RegistrationNativePlatformLorIdealSelected.unused (n := n)
local notation "actualProvider" => RegistrationNativeSecretWordKemEarly.actual setup.baseImpl setup.kem selectedOwner pairs (Prod.fst chosen) challenge candidate
local notation "closedImpl" => RegistrationNativePlatformLorCtxClosed.implementation setup wire sign seed scalar candidate unused selectedOwner pairs (Prod.fst chosen) challenge physical
local notation "controller" => RegistrationNativePlatformSecretWordFrontend.handler (n := n) setup checks wire source sign selectedOwner selectedAccept
  (setup.dh.publicKey scalar) view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
abbrev NativePrivate (n : Nat) (KemSK : Type) := RegistrationNativePlatformLorIdealSelected.NativePrivate n KemSK
abbrev Result (n : Nat) (KemSK Platform Physical A : Type) (source : RegistrationNativeMldsa.Source) :=
  ((A × RegistrationNativeLedger.State) × RegistrationNativePlatformPublicFrontend.State source Platform) ×
    RegistrationNativePlatformRecordPartnerSlotTrace.State n KemSK RegistrationNativeKemSwitchSource.Phase Physical

local notation "sourceRun" => RegistrationNativeFullCompiler.run setup.source.crypto wire serverKeyId bounds
  (RegistrationNativePlatformLorStatefulSupport.traced closedImpl controller) mode work

/-- The same complete symbolic source result exposes the literal candidate in its original final recovery log. -/
def Exposure (before : RegistrationNativePlatformPublicFrontend.State source Platform)
    (privateBefore : NativePrivate n KemSK) (physicalBefore : Physical) (result : Result n KemSK Platform Physical A source) : Prop :=
  ∃ reached : RegistrationNativePlatformLorIdealSelected.SourceResult n KemSK Platform Physical A source,
    reached∈support (sourceRun (RegistrationNativePlatformLorIdealSelected.sourceBefore source before privateBefore physicalBefore)) ∧
    RegistrationNativePlatformLorIdealTraceRun.projectResult candidate reached=RegistrationNativePlatformRecordPartnerSnapshotSource.project result ∧
    RegistrationNativeSecretWordAliasExposureBound.Exposure
      (RegistrationNativeSecretWordMessage.input setup.joint setup.dh seed scalar)
      (RegistrationNativeSecretWordProtection.inside (setup.joint.staticDh seed (setup.dh.publicKey scalar))) candidate reached.2.2.2.1

private theorem from_lift (before : RegistrationNativePlatformPublicFrontend.State source Platform)
    (initialSessions : before.1.server.sessions=[]) (initialCounter : before.1.parsedAccepts=0) (ownersEmpty : before.1.beacons=[])
    (privateBefore : NativePrivate n KemSK) (physicalBefore : Physical)
    (good : RegistrationNativeSelectiveHiddenDictionaryRun.Good privateBefore)
    (result : Result n KemSK Platform Physical A source)
    (supported : result∈support ((simulateQ (RegistrationNativePlatformRecordPartnerSlotTrace.handler setup wire sign seed scalar candidate actualProvider physical)
      (simulateQ RegistrationNativePlatformPublicCoinEmbedding.embed
        (RegistrationNativePlatformPublicFrontend.run setup checks RegistrationNativePlatformConcreteSource.wire source sign selectedOwner selectedAccept
          (setup.dh.publicKey scalar) view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer serverKeyId bounds mode work before))).run
            (RegistrationNativePlatformPublicRecordSlots.initial,RegistrationNativeG2Trace.initial,(privateBefore,physicalBefore))))
    (reached : RegistrationNativePlatformLorIdealSelected.SourceResult n KemSK Platform Physical A source)
    (called : reached∈support (sourceRun (RegistrationNativePlatformLorIdealSelected.sourceBefore source before privateBefore physicalBefore)))
    (equal : RegistrationNativePlatformLorIdealTraceRun.projectResult candidate reached=RegistrationNativePlatformRecordPartnerSnapshotSource.project result)
    (publicHandles : ∀role,RegistrationNativePlatformRecordPartnerSnapshotOrdinal.receiptHandles role result.2.1.snapshot=
      RegistrationNativeInstallOrdinals.handles role result.1.1.2.transcript)
    (budget : PqxdhDeploymentInterface.Budget) (target : Fin budget.accept × Fin budget.capacity)
    (selectedOwnerEq : selectedOwner=target.2.val)
    (keyId : U64) (owner : Nat) (slot : PqxdhRecordLiftInterface.Slot n)
    (peerSlot : RegistrationNativePlatformRecordSlotGhost.slots result.2.1.snapshot (.peer keyId)=some slot)
    (ownerSlot : RegistrationNativePlatformRecordSlotGhost.slots result.2.1.snapshot (.owner owner)=some slot)
    (accepted : RegistrationNativeParsedTargetCanonical.AcceptedAt wire result.1.1.2.transcript target.1.val selectedAccept) :
    RegistrationNativeSessionEvents.CEPartners budget target (result.1.1.2.transcript.map RegistrationNativeInterface.Entry.erase) (.peer keyId) (.owner owner) ∨
      RegistrationNativeSecretWordAliasExposureBound.Exposure
        (RegistrationNativeSecretWordMessage.input setup.joint setup.dh seed scalar)
        (RegistrationNativeSecretWordProtection.inside (setup.joint.staticDh seed (setup.dh.publicKey scalar))) candidate reached.2.2.2.1 := by
  have path := RegistrationNativePlatformLorSourceAcceptedCall.full_path setup checks wire source sign selectedOwner selectedAccept (setup.dh.publicKey scalar)
    view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
    (RegistrationNativePlatformLorStatefulSupport.trace closedImpl) serverKeyId bounds mode work
    (RegistrationNativePlatformLorIdealSelected.sourceBefore source before privateBefore physicalBefore) reached called
  have valid := RegistrationNativePlatformRecordPartnerSlotTrace.program setup wire sign seed scalar candidate actualProvider physical _ _
    (RegistrationNativePlatformRecordPartnerSlotTrace.initial setup seed scalar candidate privateBefore physicalBefore good) result supported
  have covered := RegistrationNativePlatformRecordPartnerSnapshotCoverage.program setup wire sign seed scalar candidate actualProvider physical _ _
    RegistrationNativePlatformRecordSlotReceipt.initial result supported
  obtain ⟨peerReceipt,peerMember,peerHandle,peerHidden,peerRole⟩ := covered (.peer keyId) slot peerSlot
  obtain ⟨ownerReceipt,ownerMember,ownerHandle,ownerHidden,ownerRole⟩ := covered (.owner owner) slot ownerSlot
  obtain ⟨peerPosition,peerFound⟩ := List.mem_iff_getElem?.mp peerMember
  obtain ⟨ownerPosition,ownerFound⟩ := List.mem_iff_getElem?.mp ownerMember
  have traceEq := congrArg (fun current => current.1.1.2.events) equal
  change reached.2.2.2.1.events.map (RegistrationNativeSecretWordCheckedTrace.event candidate)=result.2.2.1.events at traceEq
  have ledgerEq := congrArg (fun current => current.1.1.1.1.2) equal
  change reached.2.1=result.1.1.2 at ledgerEq
  have contract := RegistrationNativePlatformLorCtxClosed.contract setup wire sign seed scalar candidate unused selectedOwner pairs (Prod.fst chosen) challenge physical
  have decided := RegistrationNativePlatformRecordPartnerSnapshot.from_snapshot setup checks RegistrationNativePlatformConcreteSource.wire source sign selectedOwner selectedAccept (setup.dh.publicKey scalar)
    view failure allocation reserveRegistration reservePeer reserveFrame erased helper reservePackets closedImpl selectedOwner pairs (Prod.fst chosen) challenge
    (fun current=>current.1.1.kem) (RegistrationNativeSecretWordMessage.input setup.joint setup.dh seed scalar) contract serverKeyId bounds
    seed scalar candidate (RegistrationNativePlatformLorIdealSelected.sourceBefore source before privateBefore physicalBefore) rfl
    (by simp only [RegistrationNativePlatformLorIdealSelected.sourceBefore,RegistrationNativeG3NativeStartupFields.word,initialSessions,List.map_nil]) initialCounter ownersEmpty rfl
    path budget target selectedOwnerEq result.2 valid traceEq.symm
    (fun role=>by rw [ledgerEq];exact publicHandles role)
    peerPosition ownerPosition peerReceipt ownerReceipt peerFound ownerFound peerRole ownerRole keyId owner peerHandle ownerHandle slot peerHidden ownerHidden
    (by rw [ledgerEq];exact accepted)
  rcases decided with partnered|exposed
  · exact Or.inl (by simpa only [ledgerEq] using partnered)
  · exact Or.inr exposed

private theorem from_handles (before : RegistrationNativePlatformPublicFrontend.State source Platform)
    (initialSessions : before.1.server.sessions=[]) (initialCounter : before.1.parsedAccepts=0) (ownersEmpty : before.1.beacons=[])
    (privateBefore : NativePrivate n KemSK) (physicalBefore : Physical)
    (pool : privateBefore.1.pool=PqxdhLiveKemBirth.empty) (phase : privateBefore.1.provider=none)
    (good : RegistrationNativeSelectiveHiddenDictionaryRun.Good privateBefore)
    (result : Result n KemSK Platform Physical A source)
    (supported : result∈support ((simulateQ (RegistrationNativePlatformRecordPartnerSlotTrace.handler setup wire sign seed scalar candidate actualProvider physical)
      (simulateQ RegistrationNativePlatformPublicCoinEmbedding.embed
        (RegistrationNativePlatformPublicFrontend.run setup checks RegistrationNativePlatformConcreteSource.wire source sign selectedOwner selectedAccept
          (setup.dh.publicKey scalar) view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer serverKeyId bounds mode work before))).run
            (RegistrationNativePlatformPublicRecordSlots.initial,RegistrationNativeG2Trace.initial,(privateBefore,physicalBefore))))
    (publicHandles : ∀role,RegistrationNativePlatformRecordPartnerSnapshotOrdinal.receiptHandles role result.2.1.snapshot=
      RegistrationNativeInstallOrdinals.handles role result.1.1.2.transcript)
    (budget : PqxdhDeploymentInterface.Budget) (target : Fin budget.accept × Fin budget.capacity)
    (selectedOwnerEq : selectedOwner=target.2.val)
    (keyId : U64) (owner : Nat) (slot : PqxdhRecordLiftInterface.Slot n)
    (peerSlot : RegistrationNativePlatformRecordSlotGhost.slots result.2.1.snapshot (.peer keyId)=some slot)
    (ownerSlot : RegistrationNativePlatformRecordSlotGhost.slots result.2.1.snapshot (.owner owner)=some slot)
    (accepted : RegistrationNativeParsedTargetCanonical.AcceptedAt wire result.1.1.2.transcript target.1.val selectedAccept) :
    RegistrationNativeSessionEvents.CEPartners budget target (result.1.1.2.transcript.map RegistrationNativeInterface.Entry.erase) (.peer keyId) (.owner owner) ∨
      Exposure setup checks source sign seed scalar pairs chosen challenge selectedOwner selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper reservePackets
        serverKeyId bounds mode work candidate physical before privateBefore physicalBefore result := by
  obtain ⟨reached,called,equal⟩ := RegistrationNativePlatformRecordPartnerSnapshotExecution.source_result setup checks source sign seed scalar pairs chosen challenge
    selectedOwner selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper reservePackets serverKeyId bounds mode work candidate physical
    before privateBefore physicalBefore pool phase result supported
  rcases from_lift setup checks source sign seed scalar pairs chosen challenge selectedOwner selectedAccept view failure allocation
    reserveRegistration reservePeer reserveFrame erased helper reservePackets serverKeyId bounds mode work candidate physical before initialSessions initialCounter ownersEmpty
    privateBefore physicalBefore good result supported reached called equal publicHandles budget target selectedOwnerEq keyId owner slot peerSlot ownerSlot accepted with partnered|exposed
  · exact Or.inl partnered
  · exact Or.inr ⟨reached,called,equal,exposed⟩

variable {Reader Response Secret : Type}

/-- The literal current source run derives corrected successful-session partners or the same recovery exposure from two actual opposite-role handles occupying one hidden slot. -/
theorem run (credential : RegistrationNativeMldsa.Credential source)
    (service : QueryImpl (PqxdhRecordLiftProtocol.ServiceSpec n) (StateT Secret ProbComp))
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (before : RegistrationNativePlatformPublicFrontend.State source Platform)
    (initialSessions : before.1.server.sessions=[]) (initialCounter : before.1.parsedAccepts=0) (ownersEmpty : before.1.beacons=[])
    (privateBefore : NativePrivate n KemSK) (physicalBefore : RegistrationNativePlatformLorIdealPhysical.State n Secret)
    (pool : privateBefore.1.pool=PqxdhLiveKemBirth.empty) (phase : privateBefore.1.provider=none)
    (good : RegistrationNativeSelectiveHiddenDictionaryRun.Good privateBefore)
    (held : RegistrationNativePlatformRecordPartnerHandleLedger.Held
      (before,(RegistrationNativePlatformPublicRecordSlots.initial,RegistrationNativeG2Trace.initial,(privateBefore,physicalBefore))))
    (result : Result n KemSK Platform (RegistrationNativePlatformLorIdealPhysical.State n Secret) A source)
    (supported : result∈support ((simulateQ (RegistrationNativePlatformRecordPartnerSlotTrace.handler setup wire
      (RegistrationNativeMldsa.owned source credential) seed scalar candidate actualProvider
      (RegistrationNativePlatformLorIdealPhysical.implementation service codec route))
      (simulateQ RegistrationNativePlatformPublicCoinEmbedding.embed
        (RegistrationNativePlatformPublicFrontend.run setup checks RegistrationNativePlatformConcreteSource.wire source
          (RegistrationNativeMldsa.owned source credential) selectedOwner selectedAccept (setup.dh.publicKey scalar)
          view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer serverKeyId bounds mode work before))).run
            (RegistrationNativePlatformPublicRecordSlots.initial,RegistrationNativeG2Trace.initial,(privateBefore,physicalBefore))))
    (budget : PqxdhDeploymentInterface.Budget) (target : Fin budget.accept × Fin budget.capacity)
    (selectedOwnerEq : selectedOwner=target.2.val)
    (keyId : U64) (owner : Nat) (slot : PqxdhRecordLiftInterface.Slot n)
    (peerSlot : RegistrationNativePlatformRecordSlotGhost.slots result.2.1.snapshot (.peer keyId)=some slot)
    (ownerSlot : RegistrationNativePlatformRecordSlotGhost.slots result.2.1.snapshot (.owner owner)=some slot)
    (accepted : RegistrationNativeParsedTargetCanonical.AcceptedAt wire result.1.1.2.transcript target.1.val selectedAccept) :
    RegistrationNativeSessionEvents.CEPartners budget target (result.1.1.2.transcript.map RegistrationNativeInterface.Entry.erase) (.peer keyId) (.owner owner) ∨
      Exposure setup checks source (RegistrationNativeMldsa.owned source credential) seed scalar pairs chosen challenge selectedOwner selectedAccept view failure allocation
        reserveRegistration reservePeer reserveFrame erased helper reservePackets serverKeyId bounds mode work candidate
        (RegistrationNativePlatformLorIdealPhysical.implementation service codec route) before privateBefore physicalBefore result := by
  have handles := RegistrationNativePlatformRecordPartnerHandleLedger.from_source setup checks RegistrationNativePlatformConcreteSource.wire credential
    seed scalar candidate actualProvider selectedOwner selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
    service codec route serverKeyId bounds mode work
    (before,(RegistrationNativePlatformPublicRecordSlots.initial,RegistrationNativeG2Trace.initial,(privateBefore,physicalBefore))) result held supported
  have publicHandles : ∀role,RegistrationNativePlatformRecordPartnerSnapshotOrdinal.receiptHandles role result.2.1.snapshot=
      RegistrationNativeInstallOrdinals.handles role result.1.1.2.transcript := by
    intro role
    simpa only [RegistrationNativePlatformRecordPartnerHandleLedger.handleList,RegistrationNativePlatformRecordPartnerSnapshotHandleSource.handleList,
      RegistrationNativePlatformRecordPartnerSnapshotOrdinal.receiptHandles,RegistrationNativePlatformPublicRecordSlots.initial,
      RegistrationNativePlatformRecordSlotGhost.initial,List.filterMap_nil,List.nil_append] using handles role
  exact from_handles setup checks source (RegistrationNativeMldsa.owned source credential) seed scalar pairs chosen challenge selectedOwner selectedAccept
    view failure allocation reserveRegistration reservePeer reserveFrame erased helper reservePackets serverKeyId bounds mode work candidate
    (RegistrationNativePlatformLorIdealPhysical.implementation service codec route) before initialSessions initialCounter ownersEmpty privateBefore physicalBefore
    pool phase good result supported publicHandles budget target selectedOwnerEq keyId owner slot peerSlot ownerSlot accepted

/-- Every specified supported symbolic lift has partnership or exposure on THAT same lift; no existential event probability is used. -/
theorem from_source (credential : RegistrationNativeMldsa.Credential source)
    (service : QueryImpl (PqxdhRecordLiftProtocol.ServiceSpec n) (StateT Secret ProbComp))
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (before : RegistrationNativePlatformPublicFrontend.State source Platform)
    (initialSessions : before.1.server.sessions=[]) (initialCounter : before.1.parsedAccepts=0) (ownersEmpty : before.1.beacons=[])
    (privateBefore : NativePrivate n KemSK) (physicalBefore : RegistrationNativePlatformLorIdealPhysical.State n Secret)
    (good : RegistrationNativeSelectiveHiddenDictionaryRun.Good privateBefore)
    (held : RegistrationNativePlatformRecordPartnerHandleLedger.Held
      (before,(RegistrationNativePlatformPublicRecordSlots.initial,RegistrationNativeG2Trace.initial,(privateBefore,physicalBefore))))
    (result : Result n KemSK Platform (RegistrationNativePlatformLorIdealPhysical.State n Secret) A source)
    (supported : result∈support ((simulateQ (RegistrationNativePlatformRecordPartnerSlotTrace.handler setup wire
      (RegistrationNativeMldsa.owned source credential) seed scalar candidate actualProvider
      (RegistrationNativePlatformLorIdealPhysical.implementation service codec route))
      (simulateQ RegistrationNativePlatformPublicCoinEmbedding.embed
        (RegistrationNativePlatformPublicFrontend.run setup checks RegistrationNativePlatformConcreteSource.wire source
          (RegistrationNativeMldsa.owned source credential) selectedOwner selectedAccept (setup.dh.publicKey scalar)
          view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer serverKeyId bounds mode work before))).run
            (RegistrationNativePlatformPublicRecordSlots.initial,RegistrationNativeG2Trace.initial,(privateBefore,physicalBefore))))
    (reached : RegistrationNativePlatformLorIdealSelected.SourceResult n KemSK Platform (RegistrationNativePlatformLorIdealPhysical.State n Secret) A source)
    (called : reached∈support (RegistrationNativeFullCompiler.run setup.source.crypto wire serverKeyId bounds
      (RegistrationNativePlatformLorStatefulSupport.traced
        (RegistrationNativePlatformLorCtxClosed.implementation setup wire (RegistrationNativeMldsa.owned source credential) seed scalar candidate unused
          selectedOwner pairs (Prod.fst chosen) challenge (RegistrationNativePlatformLorIdealPhysical.implementation service codec route))
        (RegistrationNativePlatformSecretWordFrontend.handler setup checks wire source (RegistrationNativeMldsa.owned source credential) selectedOwner selectedAccept
          (setup.dh.publicKey scalar) view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer)) mode work
        (RegistrationNativePlatformLorIdealSelected.sourceBefore source before privateBefore physicalBefore)))
    (equal : RegistrationNativePlatformLorIdealTraceRun.projectResult candidate reached=RegistrationNativePlatformRecordPartnerSnapshotSource.project result)
    (budget : PqxdhDeploymentInterface.Budget) (target : Fin budget.accept × Fin budget.capacity)
    (selectedOwnerEq : selectedOwner=target.2.val)
    (keyId : U64) (owner : Nat) (slot : PqxdhRecordLiftInterface.Slot n)
    (peerSlot : RegistrationNativePlatformRecordSlotGhost.slots result.2.1.snapshot (.peer keyId)=some slot)
    (ownerSlot : RegistrationNativePlatformRecordSlotGhost.slots result.2.1.snapshot (.owner owner)=some slot)
    (accepted : RegistrationNativeParsedTargetCanonical.AcceptedAt wire result.1.1.2.transcript target.1.val selectedAccept) :
    RegistrationNativeSessionEvents.CEPartners budget target (result.1.1.2.transcript.map RegistrationNativeInterface.Entry.erase) (.peer keyId) (.owner owner) ∨
      RegistrationNativeSecretWordAliasExposureBound.Exposure
        (RegistrationNativeSecretWordMessage.input setup.joint setup.dh seed scalar)
        (RegistrationNativeSecretWordProtection.inside (setup.joint.staticDh seed (setup.dh.publicKey scalar))) candidate reached.2.2.2.1 := by
  have handles := RegistrationNativePlatformRecordPartnerHandleLedger.from_source setup checks RegistrationNativePlatformConcreteSource.wire credential
    seed scalar candidate actualProvider selectedOwner selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
    service codec route serverKeyId bounds mode work
    (before,(RegistrationNativePlatformPublicRecordSlots.initial,RegistrationNativeG2Trace.initial,(privateBefore,physicalBefore))) result held supported
  have publicHandles : ∀role,RegistrationNativePlatformRecordPartnerSnapshotOrdinal.receiptHandles role result.2.1.snapshot=
      RegistrationNativeInstallOrdinals.handles role result.1.1.2.transcript := by
    intro role
    simpa only [RegistrationNativePlatformRecordPartnerHandleLedger.handleList,RegistrationNativePlatformRecordPartnerSnapshotHandleSource.handleList,
      RegistrationNativePlatformRecordPartnerSnapshotOrdinal.receiptHandles,RegistrationNativePlatformPublicRecordSlots.initial,
      RegistrationNativePlatformRecordSlotGhost.initial,List.filterMap_nil,List.nil_append] using handles role
  exact from_lift setup checks source (RegistrationNativeMldsa.owned source credential) seed scalar pairs chosen challenge selectedOwner selectedAccept
    view failure allocation reserveRegistration reservePeer reserveFrame erased helper reservePackets serverKeyId bounds mode work candidate
    (RegistrationNativePlatformLorIdealPhysical.implementation service codec route) before initialSessions initialCounter ownersEmpty privateBefore physicalBefore
    good result supported reached called equal publicHandles budget target selectedOwnerEq keyId owner slot peerSlot ownerSlot accepted

end BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerPointwise
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerPointwise.run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerPointwise.run

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerPointwise.from_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerPointwise.from_source
