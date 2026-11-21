-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerSnapshotSource
import BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerPointwise
import BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerEvents
import BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerJointPhysical
/-! Every actual native snapshot run has the same complete candidate-independent symbolic source execution. Native trace, public successful-session ledger, persistent platform/private state, and physical state are retained; the selected parsed accept coordinate remains separate from the public session coordinate. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerWordMarginal
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


local notation "sourceRun"=>RegistrationNativeFullCompiler.run setup.source.crypto wire serverKeyId bounds
  (RegistrationNativePlatformLorStatefulSupport.traced closedImpl controller) mode work
local notation "snapshotRun(" before "," privateBefore "," physicalBefore ")"=>
  StateT.run (simulateQ (RegistrationNativePlatformRecordPartnerSlotTrace.handler setup wire sign seed scalar candidate actualProvider physical)
    (simulateQ RegistrationNativePlatformPublicCoinEmbedding.embed
      (RegistrationNativePlatformPublicFrontend.run setup checks RegistrationNativePlatformConcreteSource.wire source sign selectedOwner selectedAccept
        (setup.dh.publicKey scalar) view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer serverKeyId bounds mode work before)))
          (RegistrationNativePlatformPublicRecordSlots.initial,RegistrationNativeG2Trace.initial,(privateBefore,physicalBefore))

/-- Actual Word and slot-observed native source runs have exactly the same complete native/G2/private/physical marginal. -/
theorem marginal (before : RegistrationNativePlatformPublicFrontend.State source Platform)
    (privateBefore : NativePrivate n KemSK) (physicalBefore : Physical)
    (pool : privateBefore.1.pool=PqxdhLiveKemBirth.empty) (phase : privateBefore.1.provider=none) :
    RegistrationNativePlatformLorIdealTraceRun.projectResult candidate <$>
      sourceRun (RegistrationNativePlatformLorIdealSelected.sourceBefore source before privateBefore physicalBefore)=
        RegistrationNativePlatformRecordPartnerSnapshotSource.project <$>snapshotRun(before,privateBefore,physicalBefore) := by
  have related:=RegistrationNativePlatformLorIdealTraceRun.closed_source setup sign seed scalar candidate unused
    selectedOwner pairs (Prod.fst chosen) challenge checks selectedOwner selectedAccept (setup.dh.publicKey scalar) view failure allocation
    reserveRegistration reservePeer reserveFrame erased helper writer physical serverKeyId bounds mode work
    (RegistrationNativeG3NativeStartupFields.word before.1,before.2)
    (RegistrationNativePlatformLorIdealInitial.symbolicPrivate privateBefore) physicalBefore
  rw [RegistrationNativePlatformLorIdealInitial.frame_private candidate privateBefore pool phase] at related
  simp only [RegistrationNativePlatformSecretWordOrdinary.evaluate,Prod.map_apply,RegistrationNativeG3NativeStartupFields.word_eval,id_eq,Prod.mk.eta] at related
  simp only [RegistrationNativeG2Trace.program] at related
  rw [RegistrationNativePlatformRecordPartnerSnapshotSource.native_source]
  exact related

/-- Each specified actual Word outcome has a compatible slot ghost from the same marginal. The Word outcome itself is never chosen existentially. -/
theorem lift (before : RegistrationNativePlatformPublicFrontend.State source Platform)
    (privateBefore : NativePrivate n KemSK) (physicalBefore : Physical)
    (pool : privateBefore.1.pool=PqxdhLiveKemBirth.empty) (phase : privateBefore.1.provider=none)
    (reached : RegistrationNativePlatformLorIdealSelected.SourceResult n KemSK Platform Physical A source)
    (called : reached∈support (sourceRun (RegistrationNativePlatformLorIdealSelected.sourceBefore source before privateBefore physicalBefore))) :
    ∃result:Result n KemSK Platform Physical A source,result∈support (snapshotRun(before,privateBefore,physicalBefore)) ∧
      RegistrationNativePlatformLorIdealTraceRun.projectResult candidate reached=RegistrationNativePlatformRecordPartnerSnapshotSource.project result := by
  have projected:=Set.mem_image_of_mem (RegistrationNativePlatformLorIdealTraceRun.projectResult candidate) called
  rw [←support_map,marginal setup checks source sign seed scalar pairs chosen challenge selectedOwner selectedAccept view failure allocation
    reserveRegistration reservePeer reserveFrame erased helper reservePackets serverKeyId bounds mode work candidate physical before privateBefore physicalBefore pool phase,
    support_map] at projected
  obtain ⟨result,supported,same⟩:=projected
  exact ⟨result,supported,same.symm⟩


/-- Every decision of the common native/G2/private/physical result has exactly the same probability on the actual Word and slot-observed source runs. -/
theorem event (before : RegistrationNativePlatformPublicFrontend.State source Platform)
    (privateBefore : NativePrivate n KemSK) (physicalBefore : Physical)
    (pool : privateBefore.1.pool=PqxdhLiveKemBirth.empty) (phase : privateBefore.1.provider=none)
    (predicate : RegistrationNativePlatformLorIdealSelected.NativeResult n KemSK Platform Physical A source →Prop) :
    Pr{let reached←sourceRun (RegistrationNativePlatformLorIdealSelected.sourceBefore source before privateBefore physicalBefore)}[
      predicate (RegistrationNativePlatformLorIdealTraceRun.projectResult candidate reached)]=
    Pr{let result←snapshotRun(before,privateBefore,physicalBefore)}[
      predicate (RegistrationNativePlatformRecordPartnerSnapshotSource.project result)] := by
  have same:=marginal setup checks source sign seed scalar pairs chosen challenge selectedOwner selectedAccept view failure allocation
    reserveRegistration reservePeer reserveFrame erased helper reservePackets serverKeyId bounds mode work candidate physical before privateBefore physicalBefore pool phase
  have equal:=congrArg (fun distribution : ProbComp (RegistrationNativePlatformLorIdealSelected.NativeResult n KemSK Platform Physical A source)=>
    Pr{let result←distribution}[predicate result]) same
  simpa only [prEvent_map] using equal

variable {Secret Reader Response : Type} (credential : RegistrationNativeMldsa.Credential source)
    (service : QueryImpl (PqxdhRecordLiftProtocol.ServiceSpec n) (StateT Secret ProbComp))
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
local notation "owned"=>RegistrationNativeMldsa.owned source credential
local notation "namedPhysical"=>RegistrationNativePlatformLorIdealPhysical.implementation service codec route
local notation "ownedImpl"=>RegistrationNativePlatformLorCtxClosed.implementation setup wire owned seed scalar candidate unused selectedOwner pairs (Prod.fst chosen) challenge namedPhysical
local notation "ownedController"=>RegistrationNativePlatformSecretWordFrontend.handler (n:=n) setup checks wire source owned selectedOwner selectedAccept
  (setup.dh.publicKey scalar) view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
local notation "ownedRun"=>RegistrationNativeFullCompiler.run setup.source.crypto wire serverKeyId bounds
  (RegistrationNativePlatformLorStatefulSupport.traced ownedImpl ownedController) mode work

/-- A public same-slot partner mismatch implies Exposure on each specified actual Word source result, rather than on an existentially selected lift. -/
theorem mismatch_exposure
    (before : RegistrationNativePlatformPublicFrontend.State source Platform)
    (initialSessions : before.1.server.sessions=[]) (initialCounter : before.1.parsedAccepts=0) (ownersEmpty : before.1.beacons=[])
    (privateBefore : NativePrivate n KemSK)
    (physicalBefore : RegistrationNativePlatformLorIdealPhysical.State n Secret)
    (good : RegistrationNativeSelectiveHiddenDictionaryRun.Good privateBefore)
    (held : RegistrationNativePlatformRecordPartnerHandleLedger.Held
      (before,(RegistrationNativePlatformPublicRecordSlots.initial,RegistrationNativeG2Trace.initial,(privateBefore,physicalBefore))))
    (pool : privateBefore.1.pool=PqxdhLiveKemBirth.empty) (phase : privateBefore.1.provider=none)
    (origins : RegistrationNativePlatformRecordSlotGhost.initial.origins=RegistrationNativePlatformRecordSlotControl.origins physicalBefore.2.1)
    (reached : RegistrationNativePlatformLorIdealSelected.SourceResult n KemSK Platform (RegistrationNativePlatformLorIdealPhysical.State n Secret) A source)
    (called : reached∈support (ownedRun (RegistrationNativePlatformLorIdealSelected.sourceBefore source before privateBefore physicalBefore)))
    (budget : PqxdhDeploymentInterface.Budget) (target : Fin budget.accept×Fin budget.capacity)
    (selectedOwnerEq : selectedOwner=target.2.val)
    (accepted : RegistrationNativeParsedTargetCanonical.AcceptedAt wire reached.2.1.transcript target.1.val selectedAccept)
    (mismatch : RegistrationNativePlatformRecordPartnerEvents.Mismatch budget target reached.2.1.ledger.transcript
      (PqxdhRecordLiftIdeal.handleSlot reached.2.2.2.2.2.2.1)) :
    RegistrationNativeSecretWordAliasExposureBound.Exposure
      (RegistrationNativeSecretWordMessage.input setup.joint setup.dh seed scalar)
      (RegistrationNativeSecretWordProtection.inside (setup.joint.staticDh seed (setup.dh.publicKey scalar))) candidate reached.2.2.2.1 := by
  obtain ⟨result,supported,equal⟩:=lift setup checks source owned seed scalar pairs chosen challenge selectedOwner selectedAccept view failure allocation
    reserveRegistration reservePeer reserveFrame erased helper reservePackets serverKeyId bounds mode work candidate namedPhysical before privateBefore physicalBefore pool phase reached called
  have sameLedger:=congrArg (fun current=>current.1.1.1.1.2) equal
  change reached.2.1=result.1.1.2 at sameLedger
  have samePhysical:=congrArg Prod.snd equal
  change reached.2.2.2.2.2=result.2.2.2.2 at samePhysical
  have slots:=RegistrationNativePlatformRecordPartnerJointPhysical.run service codec route setup RegistrationNativePlatformConcreteSource.wire
    owned seed scalar candidate actualProvider checks source selectedOwner selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
    serverKeyId bounds mode work before (RegistrationNativePlatformPublicRecordSlots.initial,RegistrationNativeG2Trace.initial,(privateBefore,physicalBefore)) origins result supported
  have sameSlots : RegistrationNativePlatformRecordSlotGhost.slots result.2.1.snapshot=
      PqxdhRecordLiftIdeal.handleSlot reached.2.2.2.2.2.2.1 := by
    rw [slots,←samePhysical]
  have partnersOrExposure : ∀keyId owner slot,
      PqxdhRecordLiftIdeal.handleSlot reached.2.2.2.2.2.2.1 (.peer keyId)=some slot →
      PqxdhRecordLiftIdeal.handleSlot reached.2.2.2.2.2.2.1 (.owner owner)=some slot →
      RegistrationNativeSessionEvents.CEPartners budget target reached.2.1.ledger.transcript (.peer keyId) (.owner owner) ∨
        RegistrationNativeSecretWordAliasExposureBound.Exposure
          (RegistrationNativeSecretWordMessage.input setup.joint setup.dh seed scalar)
          (RegistrationNativeSecretWordProtection.inside (setup.joint.staticDh seed (setup.dh.publicKey scalar))) candidate reached.2.2.2.1 := by
    intro keyId owner slot peerSlot ownerSlot
    have answer:=RegistrationNativePlatformRecordPartnerPointwise.from_source setup checks source seed scalar pairs chosen challenge selectedOwner selectedAccept
      view failure allocation reserveRegistration reservePeer reserveFrame erased helper reservePackets serverKeyId bounds mode work candidate credential service codec route
      before initialSessions initialCounter ownersEmpty privateBefore physicalBefore good held result supported reached called equal budget target selectedOwnerEq
      keyId owner slot (by rw [sameSlots];exact peerSlot) (by rw [sameSlots];exact ownerSlot) (by rw [←sameLedger];exact accepted)
    rcases answer with partners|exposed
    · left
      have projection:=RegistrationNativeFullCompiler.ledger_projection setup.source.crypto wire serverKeyId bounds
        (RegistrationNativePlatformLorStatefulSupport.traced ownedImpl ownedController) mode work
        (RegistrationNativePlatformLorIdealSelected.sourceBefore source before privateBefore physicalBefore) reached called
      rw [projection,sameLedger]
      exact partners
    · exact Or.inr exposed
  obtain ⟨first,second,⟨slot,firstAt,secondAt⟩,unrelated⟩:=mismatch
  cases first with
  | peer keyId=>
    cases second with
    | peer other=>exact secondAt.elim
    | owner owner=>
      rcases partnersOrExposure keyId owner slot firstAt secondAt with partners|exposed
      · exact (unrelated partners).elim
      · exact exposed
  | owner owner=>
    cases second with
    | peer keyId=>
      rcases partnersOrExposure keyId owner slot secondAt firstAt with partners|exposed
      · apply (unrelated ?_).elim
        exact partners.symm
      · exact exposed
    | owner other=>exact secondAt.elim


def MismatchAt (budget : PqxdhDeploymentInterface.Budget) (owner : Fin budget.capacity)
    (nativeResult : RegistrationNativePlatformLorIdealSelected.NativeResult n KemSK Platform
      (RegistrationNativePlatformLorIdealPhysical.State n Secret) A source) : Prop :=
  ∃session:Fin budget.accept,
    RegistrationNativeParsedTargetCanonical.AcceptedAt wire nativeResult.1.1.1.1.2.transcript session.val selectedAccept ∧
      RegistrationNativePlatformRecordPartnerEvents.Mismatch budget (session,owner) nativeResult.1.1.1.1.2.ledger.transcript
        (PqxdhRecordLiftIdeal.handleSlot nativeResult.2.2.1)

/-- The mismatch event on the actual slot-observed run is bounded by Exposure on the genuine Word run through their exact common marginal. -/
theorem mismatch_bound
    (before : RegistrationNativePlatformPublicFrontend.State source Platform)
    (initialSessions : before.1.server.sessions=[]) (initialCounter : before.1.parsedAccepts=0) (ownersEmpty : before.1.beacons=[])
    (privateBefore : NativePrivate n KemSK)
    (physicalBefore : RegistrationNativePlatformLorIdealPhysical.State n Secret)
    (good : RegistrationNativeSelectiveHiddenDictionaryRun.Good privateBefore)
    (held : RegistrationNativePlatformRecordPartnerHandleLedger.Held
      (before,(RegistrationNativePlatformPublicRecordSlots.initial,RegistrationNativeG2Trace.initial,(privateBefore,physicalBefore))))
    (pool : privateBefore.1.pool=PqxdhLiveKemBirth.empty) (phase : privateBefore.1.provider=none)
    (origins : RegistrationNativePlatformRecordSlotGhost.initial.origins=RegistrationNativePlatformRecordSlotControl.origins physicalBefore.2.1)
    (budget : PqxdhDeploymentInterface.Budget) (owner : Fin budget.capacity) (selectedOwnerEq : selectedOwner=owner.val) :
    Pr{let result←(simulateQ (RegistrationNativePlatformRecordPartnerSlotTrace.handler setup wire owned seed scalar candidate actualProvider namedPhysical)
      (simulateQ RegistrationNativePlatformPublicCoinEmbedding.embed
        (RegistrationNativePlatformPublicFrontend.run setup checks RegistrationNativePlatformConcreteSource.wire source owned selectedOwner selectedAccept
          (setup.dh.publicKey scalar) view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer serverKeyId bounds mode work before))).run
            (RegistrationNativePlatformPublicRecordSlots.initial,RegistrationNativeG2Trace.initial,(privateBefore,physicalBefore))}[
      MismatchAt (source:=source) selectedAccept budget owner (RegistrationNativePlatformRecordPartnerSnapshotSource.project result)]≤
    Pr{let reached←ownedRun (RegistrationNativePlatformLorIdealSelected.sourceBefore source before privateBefore physicalBefore)}[
      RegistrationNativeSecretWordAliasExposureBound.Exposure
        (RegistrationNativeSecretWordMessage.input setup.joint setup.dh seed scalar)
        (RegistrationNativeSecretWordProtection.inside (setup.joint.staticDh seed (setup.dh.publicKey scalar))) candidate reached.2.2.2.1] := by
  rw [←event setup checks source owned seed scalar pairs chosen challenge selectedOwner selectedAccept view failure allocation
    reserveRegistration reservePeer reserveFrame erased helper reservePackets serverKeyId bounds mode work candidate namedPhysical
    before privateBefore physicalBefore pool phase (MismatchAt (source:=source) selectedAccept budget owner)]
  apply prEvent_mono_of_support
  intro reached called mismatch
  obtain ⟨session,accepted,unrelated⟩:=mismatch
  exact mismatch_exposure setup checks source seed scalar pairs chosen challenge selectedOwner selectedAccept view failure allocation
    reserveRegistration reservePeer reserveFrame erased helper reservePackets serverKeyId bounds mode work candidate credential service codec route
    before initialSessions initialCounter ownersEmpty privateBefore physicalBefore good held pool phase origins reached called budget (session,owner) selectedOwnerEq accepted unrelated

end BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerWordMarginal

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerWordMarginal.marginal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerWordMarginal.marginal

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerWordMarginal.lift' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerWordMarginal.lift

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerWordMarginal.event' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerWordMarginal.event

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerWordMarginal.mismatch_exposure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerWordMarginal.mismatch_exposure

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerWordMarginal.mismatch_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerWordMarginal.mismatch_bound
