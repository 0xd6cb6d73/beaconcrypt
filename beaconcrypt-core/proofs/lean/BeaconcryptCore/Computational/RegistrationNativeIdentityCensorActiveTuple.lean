-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorPostselectionBundleCut
import BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxTuplePublication
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorBundleDispatchSource
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorSampleSource
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorAdaptivePostselection
/-! An actual active successful source publication belongs to the selected opaque handle and publishes exactly its selected one-time unsigned tuple. Canonical source interpretation, concrete source writer and readback are derived per operation; no exact randomized-signature claim is made. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityCensorActiveTuple
open PqxdhServerAuthExperiment (Setup Checks)
open PqxdhEd25519EufCma (Ed25519Signature)
open RegistrationNativeIdentityCensorEdOutgoingSource (Full interpret)
open RegistrationNativeIdentityCensorBundleStopCut (cut)
variable {n : Nat} {I KemSK Platform E : Type} {base : OracleSpec I} {mlSource : RegistrationNativeMldsa.Source}
variable (setup : Setup base KemSK) (checks : Checks)
variable (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
variable (selected index : Nat) (placeholder : Ed25519Signature)
variable (reserve : Usize → StateT Platform ProbComp (core.result.Result Unit E))
local notation "FullState" => Full (n := n) (KemSK := KemSK) (Platform := Platform) (mlSource := mlSource)
local notation "Main" => RegistrationNativePlatformIdentityCtxMain.beacon (n := n) (Platform := Platform) (source := mlSource) setup checks representation created
local notation "source(" censored "," work ")" => interpret setup.joint selected placeholder censored work
local notation "writer" => RegistrationNativePlatformConcreteSource.writer reserve
local notation "body(" owner "," scalar ")" => Main (RegistrationNativePlatformIdentityBundle.bundled setup index owner scalar writer)


/-- The existing active publication observer can stop only on the selected handle's actual selected one-time field. The concrete bytes decode to that same source tuple. -/
theorem body (owner : RegistrationNativeIdentityFrontend.Owner mlSource) (scalar : PqxdhJointGapDh.ScalarBytes)
    (target : Pqxdh.Bytes) (targetRole : RegistrationNativeIdentitySigningRole.oneTime target = true)
    (before after : FullState) (seed : PqxdhJointIdentity.IdentitySeed)
    (held : before.1.2.target = some target) (sourceTarget : before.2.target = some target)
    (inactive : before.1.2.active = false) (found : before.2.pool.seeds[selected]? = some seed)
    (bytes : alloc.vec.Vec U8)
    (supported : (.ok (some bytes),after) ∈ support ((source(false,body(owner,scalar))).run before))
    (active : after.1.2.active = true) :
    owner.identity.handle = selected ∧ target = PqxdhEd25519EufCma.oneTimeMessage (setup.dh.publicKey scalar) ∧
      (PqxdhDeploymentTranscript.candidateOf (RegistrationNativeWire.ledgerCodec RegistrationNativePlatformConcreteSource.wire)
        (TranscriptAuthParts.absSlice bytes)).bind PqxdhDeploymentPublishedTuple.candidateTuple =
          some ⟨PqxdhPhase2InputBytes.word owner.prekeyPublic,setup.dh.publicKey scalar,owner.kemPublic⟩ := by
  obtain ⟨started,built,tagged⟩ := RegistrationNativeIdentitySigningRole.initial
    (pqxdh.BeaconFresh.mk owner.pin.binding) (RegistrationNativeIdentityFrontend.inputs owner)
      (pqxdh.BeaconCoins.mk (PqxdhRootTableInitialization.rootArray (setup.dh.publicKey scalar)))
  have handle : owner.identity.handle = selected := by
    by_contra other
    have quiet := RegistrationNativeIdentityCensorOtherOwnerSource.inactive setup checks representation created selected index owner placeholder writer
      target other false scalar before ⟨held,inactive⟩ (.ok (some bytes),after) supported
    rw [active] at quiet
    cases quiet
  have message : target = PqxdhRefinement.absBytes started.message.one_time_key := by
    by_contra different
    have quiet := RegistrationNativeIdentityCensorOtherMessageSource.inactive setup checks representation created selected index owner placeholder writer
      target targetRole false scalar started built tagged different before ⟨held,inactive⟩ (.ok (some bytes),after) supported
    rw [active] at quiet
    cases quiet
  have original := Set.mem_image_of_mem (Prod.map id RegistrationNativeIdentityCensorActualHashSource.project) supported
  rw [←support_map,RegistrationNativeIdentityCensorPostselectionBundleCut.body_original setup checks representation created selected index placeholder reserve
    owner scalar target targetRole before seed held sourceTarget inactive found] at original
  obtain ⟨tuple,oneTime⟩ := RegistrationNativePlatformIdentityCtxTuplePublication.bundled_started setup checks representation created index owner scalar reserve
    started built (RegistrationNativeIdentityCensorActualHashSource.project before) (RegistrationNativeIdentityCensorActualHashSource.project after) bytes original
  exact ⟨handle,message.trans oneTime,tuple⟩

/-- The literal owner lookup and supplied/fresh sampler retain this same selected unsigned tuple at every actual active successful outer bundle. -/
theorem bundle (target : Pqxdh.Bytes) (targetRole : RegistrationNativeIdentitySigningRole.oneTime target = true)
    (before after : FullState) (seed : PqxdhJointIdentity.IdentitySeed)
    (held : before.1.2.target = some target) (sourceTarget : before.2.target = some target)
    (inactive : before.1.2.active = false) (found : before.2.pool.seeds[selected]? = some seed)
    (bytes : alloc.vec.Vec U8)
    (supported : (.ok (some bytes),after) ∈ support ((source(false,Main (RegistrationNativePlatformIdentityBundleRun.bundle setup index writer))).run before))
    (active : after.1.2.active = true) :
    ∃ owner scalar, before.1.1.1.beacons[index]? = some owner ∧ owner.identity.handle = selected ∧
      target = PqxdhEd25519EufCma.oneTimeMessage (setup.dh.publicKey scalar) ∧
      (PqxdhDeploymentTranscript.candidateOf (RegistrationNativeWire.ledgerCodec RegistrationNativePlatformConcreteSource.wire)
        (TranscriptAuthParts.absSlice bytes)).bind PqxdhDeploymentPublishedTuple.candidateTuple =
          some ⟨PqxdhPhase2InputBytes.word owner.prekeyPublic,setup.dh.publicKey scalar,owner.kemPublic⟩ := by
  rcases RegistrationNativeIdentityCensorBundleDispatchSource.cut setup checks representation created selected index placeholder writer false before
      (.ok (some bytes),after) supported with rejected | ⟨owner,scalar,middle,lookup,picked,called⟩
  · have impossible := congrArg Prod.fst rejected
    cases impossible
  · have fields : middle.1.2.target = some target ∧ middle.2.target = some target ∧ middle.1.2.active = false ∧
        middle.2.pool.seeds[selected]? = some seed := by
      rcases picked with ⟨_fresh,sampled⟩ | ⟨_supplied,same⟩
      · have frame := RegistrationNativeIdentityCensorSampleSource.frame setup checks representation created selected placeholder false
          PqxdhJointGapDh.sampleScalar before (scalar,middle) sampled
        exact ⟨(congrArg (fun after => after.1.target) frame).trans held,
          (congrArg (fun after => after.2.target) frame).trans sourceTarget,
          (congrArg (fun after => after.1.active) frame).trans inactive,
          (congrArg (fun after => after.2.pool.seeds[selected]?) frame).trans found⟩
      · subst middle
        exact ⟨held,sourceTarget,inactive,found⟩
    obtain ⟨handle,message,tuple⟩ := body setup checks representation created selected index placeholder reserve owner scalar target targetRole middle after seed
      fields.1 fields.2.1 fields.2.2.1 fields.2.2.2 bytes called active
    exact ⟨owner,scalar,lookup,handle,message,tuple⟩

private theorem source_map {A B : Type} (change : A → B)
    (work : RegistrationNativePlatformIdentityCtxMain.M n KemSK Platform mlSource A) :
    source(false,change <$> work) = change <$> source(false,work) := by
  rw [map_eq_bind_pure_comp,RegistrationNativeIdentityCensorSourceFold.bind_source]
  simp only [Function.comp_apply,RegistrationNativeIdentityCensorSourceFold.pure_source,bind_pure_comp]

/-- Public Vec-to-byte conversion retains the exact active selected tuple. This is the literal callback used by the before-accept stop. -/
theorem callback (target : Pqxdh.Bytes) (targetRole : RegistrationNativeIdentitySigningRole.oneTime target = true)
    (before after : FullState) (seed : PqxdhJointIdentity.IdentitySeed)
    (held : before.1.2.target = some target) (sourceTarget : before.2.target = some target)
    (inactive : before.1.2.active = false) (found : before.2.pool.seeds[selected]? = some seed)
    (bytes : Pqxdh.Bytes)
    (supported : (.ok (some bytes),after) ∈ support ((source(false,RegistrationNativePlatformIdentityCtxLifecycle.bundle setup checks representation created writer index)).run before))
    (active : after.1.2.active = true) :
    ∃ owner scalar, before.1.1.1.beacons[index]? = some owner ∧ owner.identity.handle = selected ∧
      target = PqxdhEd25519EufCma.oneTimeMessage (setup.dh.publicKey scalar) ∧
      (PqxdhDeploymentTranscript.candidateOf (RegistrationNativeWire.ledgerCodec RegistrationNativePlatformConcreteSource.wire)
        bytes).bind PqxdhDeploymentPublishedTuple.candidateTuple =
          some ⟨PqxdhPhase2InputBytes.word owner.prekeyPublic,setup.dh.publicKey scalar,owner.kemPublic⟩ := by
  rw [RegistrationNativePlatformIdentityCtxLifecycle.bundle,source_map,StateT.run_map,support_map] at supported
  obtain ⟨⟨raw,finished⟩,called,same⟩ := supported
  have afterEq : finished = after := congrArg Prod.snd same
  subst finished
  have replied := congrArg Prod.fst same
  cases raw with
  | fail error | div => cases replied
  | ok optional => cases optional with
    | none => cases replied
    | some encoded =>
      have bytesEq : TranscriptAuthParts.absSlice encoded = bytes := Option.some.inj (RustM.ok.inj replied)
      rw [←bytesEq]
      exact bundle setup checks representation created selected index placeholder reserve target targetRole before after seed held sourceTarget inactive found encoded called active

section Typed
variable [primitives : BeaconcryptCore.Refinement.AdapterSealPrimitive.Operations]
variable (wire : RegistrationNativeWire.Wire) (route : RawCtxServerRouting.SenderDecoder)
variable (credential : RegistrationNativeMldsa.Credential mlSource) (keys : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitives.Error)
variable (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
variable (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
variable (reserveFrame : Nat → StateT Platform ProbComp (core.result.Result Unit E)) (erased : commitment.CommitmentTranscript)
variable (helper : QueryImpl (BeaconcryptCore.Refinement.AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
local notation "actual" => RegistrationNativePlatformIdentityCtxTyped.handler setup checks wire route representation created credential keys failure allocation
  reserveRegistration reservePeer reserveFrame erased helper writer
local notation "current" => RegistrationNativeIdentityCensorAdaptivePostselection.normalized setup checks wire route representation created credential keys failure allocation
  reserveRegistration reservePeer reserveFrame erased helper reserve placeholder

omit primitives in
private theorem map_apply {S A B : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (change : A → B) (work : StateT S m A) (before : S) :
    (change <$> work) before = Prod.map change id <$> work before := StateT.run_map change work before

private theorem normalized_source (before : FullState) :
    (source(false,current (.inr (.bundle index)))).run before =
      Prod.map id (RegistrationNativeIdentityCensorOutgoingView.view placeholder) <$>
        (source(false,actual (.inr (.bundle index)))).run before := by
  simp only [RegistrationNativeIdentityCensorAdaptivePostselection.normalized,interpret,StateT.run,simulateQ_map,map_apply,
    bind_pure_comp,Functor.map_map,RegistrationNativeIdentityCensorOutgoingView.view,Prod.map_def,id_eq]

/-- The actual normalized, publicly marked callback has this same active unsigned-tuple consequence. Prior signature slots and ML receipts are the only stored metadata viewed away. -/
theorem marked (position : Nat) (target : Pqxdh.Bytes) (targetRole : RegistrationNativeIdentitySigningRole.oneTime target = true)
    (before after : FullState) (seed : PqxdhJointIdentity.IdentitySeed)
    (held : before.1.2.target = some target) (sourceTarget : before.2.target = some target)
    (found : before.2.pool.seeds[selected]? = some seed) (bytes : Pqxdh.Bytes)
    (supported : (.ok (some bytes),after) ∈ support (RegistrationNativeIdentityCensorAdaptivePostselection.call setup checks wire route representation created credential keys
      failure allocation reserveRegistration reservePeer reserveFrame erased helper reserve selected position placeholder false (.inr (.bundle index)) before))
    (active : after.1.2.active = true) :
    ∃ owner scalar, before.1.1.1.beacons[index]? = some owner ∧ owner.identity.handle = selected ∧
      target = PqxdhEd25519EufCma.oneTimeMessage (setup.dh.publicKey scalar) ∧
      (PqxdhDeploymentTranscript.candidateOf (RegistrationNativeWire.ledgerCodec RegistrationNativePlatformConcreteSource.wire)
        bytes).bind PqxdhDeploymentPublishedTuple.candidateTuple =
          some ⟨PqxdhPhase2InputBytes.word owner.prekeyPublic,setup.dh.publicKey scalar,owner.kemPublic⟩ := by
  rw [RegistrationNativeIdentityCensorAdaptivePostselection.call,normalized_source,support_map] at supported
  obtain ⟨⟨reply,actualAfter⟩,called,same⟩ := supported
  have replyEq : reply = .ok (some bytes) := congrArg Prod.fst same
  subst reply
  have afterActive := congrArg (fun result => result.2.1.2.active) same
  change actualAfter.1.2.active = after.1.2.active at afterActive
  exact callback setup checks representation created selected index placeholder reserve target targetRole
    (RegistrationNativeIdentityCensorAdaptivePostselection.entered position (.inr (.bundle index)) before) actualAfter seed held sourceTarget
    (RegistrationNativeIdentityCensorCompiler.enter_inactive position (.inr (.bundle index)) before.1.2) found bytes called (afterActive.trans active)
end Typed

end BeaconcryptCore.Computational.RegistrationNativeIdentityCensorActiveTuple

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorActiveTuple.body' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorActiveTuple.body

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorActiveTuple.bundle' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorActiveTuple.bundle

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorActiveTuple.callback' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorActiveTuple.callback

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorActiveTuple.marked' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorActiveTuple.marked
