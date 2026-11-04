-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerServerControl
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicSlotBuildSafe
/-! The corrected public build embeds the actual moved-token Server controller and all stateful publication callbacks into the literal paired observer. This is only same-demand installation safety, including failed allocations and insertions. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerServerTyped
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativePlatformPublicFrontend
variable {n : Nat} {E Platform ι KemSK : Type} {base : OracleSpec ι}
variable [primitive : BeaconcryptCore.Refinement.AdapterSealPrimitive.Operations]
variable (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire) (source : RegistrationNativeMldsa.Source)
variable (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
variable (selectedOwner selectedAccept : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
variable (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
variable (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
variable (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
variable (reserveFrame : Nat → StateT Platform ProbComp (core.result.Result Unit E)) (erased : commitment.CommitmentTranscript)
variable (helper : QueryImpl (BeaconcryptCore.Refinement.AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
variable (implementation : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))



open RegistrationNativePlatformRecordPartnerSnapshotHandles (handler)
open RegistrationNativePlatformRecordPartnerServerControl (resultHandles)

omit primitive in
private theorem embedding :
    (RegistrationNativePlatformPublicCoinEmbedding.embed (n := n) (KemSK := KemSK) ∘ₛ embedLocal) ∘ₛ buildEmbedding =
      RegistrationNativePlatformRecordPartnerServerBranch.embed := by
  funext query
  cases query with
  | inl message => simp only [QueryImpl.compose,buildEmbedding,localQuery,embedLocal,
      simulateQ_spec_query,RegistrationNativePlatformPublicCoinEmbedding.embed,
      RegistrationNativePlatformRecordPartnerServerBranch.embed,RegistrationNativePlatformPublicSlotEffects.demand]
  | inr query => cases query with
    | inl query => simp [QueryImpl.compose,buildEmbedding,effect,localQuery,embedLocal,
        RegistrationNativePlatformPublicCoinEmbedding.embed,RegistrationNativePlatformRecordPartnerServerBranch.embed,
        RegistrationNativePlatformPublicSlotEffects.effects,RegistrationNativePairedCompile.effects]
    | inr coin => simp [QueryImpl.compose,buildEmbedding,localCoin,embedLocal,publicCoin,
        RegistrationNativePlatformPublicCoinEmbedding.embed,RegistrationNativePublicFrontend.effect,
        RegistrationNativePublicFrontend.liftLocal,RegistrationNativePlatformRecordPartnerServerBranch.embed,
        RegistrationNativePlatformPublicSlotEffects.effects,RegistrationNativePairedCompile.effects]

omit primitive in
private theorem response_handles (reply : RustM (Option (U64 × alloc.vec.Vec U8))) :
    resultHandles (responseBytes reply)=resultHandles reply := by
  cases reply with
  | fail error | div => rfl
  | ok optional => cases optional <;> rfl

private def attach (before : State source Platform)
    (result : (RustM (Option (U64 × alloc.vec.Vec U8)) × RegistrationServerMaterialFrontend.State) × RegistrationNativePlatformBoundCompiler.PublicState Platform) :
    RustM (Option (U64 × Pqxdh.Bytes)) × State source Platform :=
  (responseBytes result.1.1, ({ before.1 with server := result.1.2, environment := { before.1.environment with receipts := result.2.1, recordRequests := [] } }, result.2.2))

private theorem build_source (handle : Nat) (application : Option (Slice U8)) (before : State source Platform) :
    simulateQ (RegistrationNativePlatformPublicCoinEmbedding.embed (n := n) (KemSK := KemSK))
      ((executeLocal (RegistrationNativePlatformPublicFrontend.build setup sign view failure allocation erased helper implementation reservePeer handle application source)).run before) =
      attach source before <$> simulateQ RegistrationNativePlatformRecordPartnerServerBranch.embed
        (((RegistrationNativePlatformRecordPartnerServerControl.body setup.source view failure allocation erased helper sign implementation reservePeer handle application).run before.1.server).run (before.1.environment.receipts,before.2)) := by
  have actual := congrArg (fun action => action.run (before.1.environment.receipts,before.2))
    (RegistrationNativePlatformRecordPartnerServerControl.program_source (n := n) setup.source view failure allocation erased helper sign implementation reservePeer handle application before.1.server)
  simp only [StateT.run] at actual
  simp only [executeLocal,RegistrationNativePlatformPublicFrontend.build,StateT.run,simulateQ_map]
  rw [←QueryImpl.simulateQ_compose,←QueryImpl.simulateQ_compose,embedding,actual]
  rfl

/-- The exact public build callback appends precisely the successful response key returned by that same callback. -/
theorem build (handle : Nat) (application : Option (Slice U8)) (before : State source Platform)
    (trace : List PqxdhDeploymentInterface.Handle)
    (result : ((RustM (Option (U64 × Pqxdh.Bytes)) × State source Platform) × List PqxdhDeploymentInterface.Handle))
    (supported : result∈support ((simulateQ (handler PqxdhRecordLiftInterface.Role.server)
      (simulateQ (RegistrationNativePlatformPublicCoinEmbedding.embed (n := n) (KemSK := KemSK))
        ((executeLocal (RegistrationNativePlatformPublicFrontend.build setup sign view failure allocation erased helper implementation reservePeer handle application source)).run before))).run trace)) :
    result.2=trace++resultHandles result.1.1 := by
  rw [build_source] at supported
  simp only [simulateQ_map,StateT.run_map,support_map] at supported
  obtain ⟨finished,called,equal⟩ := supported
  cases equal
  have counted := RegistrationNativePlatformRecordPartnerServerControl.body_handles
    setup.source view failure allocation erased helper sign implementation reservePeer handle application
      before.1.server (before.1.environment.receipts,before.2) trace finished called
  simpa only [attach,response_handles] using counted

end BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerServerTyped
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerServerTyped.build' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerServerTyped.build
