-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformResponseBoundFields
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordBuild
/-! The actual stateful known and hidden response branches retain the same source candidate fields through record, signature, dynamic serialization and installation. Success data lineage is derived from the concrete writer rather than supplied as a codec premise. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformResponseBranchFields
open RegistrationNativePlatformBoundCompiler (PublicState)
variable {n : Nat} {Platform E : Type}
variable [primitive : BeaconcryptCore.Refinement.AdapterSealPrimitive.Operations]
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (BeaconcryptCore.Refinement.AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (reserve : Usize → StateT Platform ProbComp (core.result.Result Unit E))
local notation "writer" => RegistrationNativePlatformConcreteSource.writer reserve

theorem branch (control : pqxdh.ServerState) (initial : RegistrationBoundKeySchedule.PublicInitial)
    (choice : RegistrationNativePairedChoice.Choice n) (published : peer.PublishedPeer (alloc.vec.Vec U8))
    (before after : PublicState Platform)
    (supported : (.ok (.Ok published),after) ∈ support ((RegistrationNativePlatformServerRestrictedService.branch
      source view failure allocation erased helper sign writer control initial choice).run before)) :
    RegistrationNativeResponsePaired.EncodedFrom RegistrationNativePlatformConcreteSource.wire.encodeResponse initial
      (TranscriptAuthParts.absSlice published.encoded) := by
  cases choice with
  | known output =>
    simp only [RegistrationNativePlatformServerRestrictedService.branch,RegistrationNativePlatformPairedServerCompiler.known,
      simulateQ_bind,simulateQ_spec_query,StateT.run_bind,RegistrationNativePlatformPairedServerCompiler.target,mem_support_bind_iff] at supported
    obtain ⟨publication,called,continued⟩ := supported
    rw [←QueryImpl.simulateQ_compose] at continued
    have inserted : .ok (.Ok published) ∈ support (RegistrationNativePairedServerService.knownAfter (n := n) control publication.1) := by
      apply OracleComp.support_simulateQ_run'_subset
        (RegistrationNativePlatformPairedServerCompiler.target source view failure allocation erased helper sign writer initial output ∘ₛ RegistrationNativePlatformPairedServerCompiler.forward) _ publication.2
      rw [StateT.run'_eq,support_map]
      exact ⟨(.ok (.Ok published),after),continued,rfl⟩
    cases actual : publication.1 with
    | fail error | div => simp only [actual,RegistrationNativePairedServerService.knownAfter] at inserted; cases inserted
    | ok result => cases result with
      | Err previous => simp only [actual,RegistrationNativePairedServerService.knownAfter] at inserted; cases inserted
      | Ok response =>
        rw [actual] at inserted
        change .ok (.Ok published) ∈ support (RegistrationNativePairedServerService.knownInstall (n := n) control response) at inserted
        have equal := RegistrationNativeResponsePaired.known_encoded control response published inserted
        have fields := RegistrationNativePlatformResponseBoundFields.compile source view failure allocation erased helper sign reserve initial output response before publication.2
          (by simpa only [←actual,Prod.mk.eta] using called)
        rw [equal]
        exact fields
  | hidden reference =>
    simp only [RegistrationNativePlatformServerRestrictedService.branch,RegistrationNativePlatformPairedServerCompiler.hidden,
      simulateQ_bind,simulateQ_spec_query,StateT.run_bind,RegistrationNativePlatformPairedServerCompiler.target,mem_support_bind_iff] at supported
    obtain ⟨publication,called,continued⟩ := supported
    rw [←QueryImpl.simulateQ_compose] at continued
    have inserted : .ok (.Ok published) ∈ support (RegistrationHiddenInstall.after control reference.slot publication.1) := by
      apply OracleComp.support_simulateQ_run'_subset
        (RegistrationNativePlatformPairedServerCompiler.target source view failure allocation erased helper sign writer initial
          (PqxdhDeploymentHiddenLayout.joinOutput reference.material RegistrationBoundPublication.fixedSeed) ∘ₛ RegistrationNativePlatformPairedServerCompiler.forward) _ publication.2
      rw [StateT.run'_eq,support_map]
      exact ⟨(.ok (.Ok published),after),continued,rfl⟩
    cases actual : publication.1 with
    | fail error | div => simp only [actual,RegistrationHiddenInstall.after] at inserted; cases inserted
    | ok result => cases result with
      | Err previous => simp only [actual,RegistrationHiddenInstall.after] at inserted; cases inserted
      | Ok response =>
        rw [actual] at inserted
        change .ok (.Ok published) ∈ support (RegistrationHiddenInstall.install control reference.slot response) at inserted
        have equal := RegistrationNativeResponsePaired.hidden_encoded control reference.slot response published inserted
        have fields := RegistrationNativePlatformResponseBoundFields.compile source view failure allocation erased helper sign reserve initial
          (PqxdhDeploymentHiddenLayout.joinOutput reference.material RegistrationBoundPublication.fixedSeed) response before publication.2
          (by simpa only [←actual,Prod.mk.eta] using called)
        rw [equal]
        exact fields

/-- The literal symbolic material demand and actual dynamic branch preserve the same admitted response metadata. -/
theorem service (control : pqxdh.ServerState) (initial : RegistrationBoundKeySchedule.PublicInitial)
    (message : RegistrationNativeSecretWordMessage.Message) (published : peer.PublishedPeer (alloc.vec.Vec U8))
    (before after : PublicState Platform)
    (supported : (.ok (.Ok published),after) ∈ support ((RegistrationNativePlatformSecretWordBuild.service (n := n)
      source view failure allocation erased helper sign writer control initial message).run before)) :
    RegistrationNativeResponsePaired.EncodedFrom RegistrationNativePlatformConcreteSource.wire.encodeResponse initial
      (TranscriptAuthParts.absSlice published.encoded) := by
  simp only [RegistrationNativePlatformSecretWordBuild.service,StateT.run_bind,StateT.run_lift,
    bind_pure_comp,bind_map_left,mem_support_bind_iff] at supported
  obtain ⟨choice,_demanded,continued⟩ := supported
  cases choice with
  | none => simp only [StateT.run_pure,mem_support_pure_iff] at continued; cases continued
  | some choice =>
    simp only [RegistrationNativePlatformSecretWordBuild.liftEffects,RegistrationNativePlatformInterpret.state,StateT.run] at continued
    exact branch source view failure allocation erased helper sign reserve control initial choice published before after
      (PqxdhDeploymentEnvironment.support_simulateQ_subset _ _ continued)
end BeaconcryptCore.Computational.RegistrationNativePlatformResponseBranchFields

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformResponseBranchFields.branch' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformResponseBranchFields.branch

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformResponseBranchFields.service' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformResponseBranchFields.service
