import BeaconcryptCore.Computational.PqxdhLaterSavedRecord

/-! The saved initial Beacon finish retains its pending owner response, original publication checks and complete outside Post continuation. -/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.refined ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhLaterSavedFinish
open PqxdhSecretInputKdf PqxdhFullSecretInputKdf PqxdhJointKdfGame PqxdhNativeSharedPrefix
open RawCtxSelectedParentTable RawCtxSelectedParentEntry RawCtxSelectedMessageDriver
open PqxdhSelectedFirstRecord
variable {ι I D K X Response Shared A N C M P Result : Type} {extra : OracleSpec ι} {S B : Nat}

noncomputable def afterOwner (index : Fin B) (before : PqxdhSelectedPostCompiler.Front M P I D K S B)
    (control : pqxdh.BeaconInitSent) (candidate : pqxdh.BeaconRegistrationCandidate)
    (result : core.option.Option RawCtxWholeOwner.Decrypted ×
      RawCtxChainOwner.State RawCtxSelectedMessageReveals.Kernel Unit) :=
  let staged := PqxdhInitialGenericBeacon.afterOpening candidate result.2.kernel result.1
  let published := PqxdhInitialGenericBeacon.finish control (before.roles.1.2 index) staged
  (published.1, PqxdhSelectedPostCompiler.install index before published.2)

/-- Kernel interpretation commutes with every original finish check, terminal failure and installation tick. -/
theorem afterOwner_source (key : RootOutput) (index : Fin B)
    (before : PqxdhSelectedPostCompiler.Front M P I D K S B)
    (control : pqxdh.BeaconInitSent) (candidate : pqxdh.BeaconRegistrationCandidate)
    (result : core.option.Option RawCtxWholeOwner.Decrypted ×
      RawCtxChainOwner.State RawCtxSelectedMessageReveals.Kernel Unit) :
    PqxdhInitialPostContext.finishResult index (frontOf key before) control candidate
      (result.1, RawCtxGenericOwnerMap.mapOwner
        (RawCtxMaterialInterpretation.mapRefined (RawCtxSelectedMessageKey.interpret key)) result.2) =
      Prod.map id (frontOf key) (afterOwner index before control candidate result) := by
  simp only [PqxdhInitialPostContext.finishResult, afterOwner, RawCtxGenericOwnerMap.mapOwner]
  rw [PqxdhInitialGenericBeacon.opening_map
    (RawCtxMaterialInterpretation.mapRefined (RawCtxSelectedMessageKey.interpret key))]
  rw [show (frontOf key before).roles.1.2 index =
    RawCtxGenericRoleStorage.mapBeacon
      (RawCtxMaterialInterpretation.mapRefined (RawCtxSelectedMessageKey.interpret key))
      (before.roles.1.2 index) from
        congrArg (fun roles => roles.2 index) (rolesOf_roles key before.roles),
    PqxdhInitialGenericBeacon.finish_map]
  exact Prod.ext rfl (frontOf_install key index before _).symm

variable
    (pre : QueryImpl (PqxdhBeaconPhase2Shared.Spec I D K X Response Shared) (StateT (ExternalState A N C) ProbComp))
    (application : Response → LocalCallback A N C (Option Pqxdh.Bytes))
    (initial : PqxdhBeaconPhase2Shared.Secrets Shared → LocalCallback A N C PqxdhInitialNativeAudit.InitialReply)
    (selector : QueryImpl extra (StateT (ExternalState A N C) ProbComp))
    (aux : QueryImpl PqxdhServerRegistrationPublication.AuxSpec (StateT (ExternalState A N C) ProbComp))
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (key target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (mark : PqxdhBeaconPhase2Shared.Secrets Shared → Bool)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (read : RawCtxReceive.FrameDecoder)
    (index : Fin B) (before : PqxdhInitialPostContext.NativeFront M P I D K S B)
    (trace : PqxdhInitialOriginPost.Trace Bool S B) (origin : Option Bool)
    (control : pqxdh.BeaconInitSent) (candidate : pqxdh.BeaconRegistrationCandidate)
    (outside : Option Pqxdh.Bytes → OracleComp (PqxdhInitialGenericPost.Spec extra S B) Result)
    (inner : RawCtxSelectedFamilyContext.OwnerContext Unit (core.option.Option RawCtxWholeOwner.Decrypted))
    (material : PqxdhOrderedChainHybrids.Material)

local notation "parent" => RawCtxSelectedPendingOwnerCompiler.entry inner material

noncomputable def nativeFinish (state : RawCtxSelectedReceiveCompiler.State (Local A N C)) := do
  let result ← (simulateQ (RawCtxSelectedParentNativeCompiler.pending source writer
    (RawCtxSelectedParentPrivatePatch.privatePatch prior target (RawCtxSelectedMessageKdf.response key nonce next)) parent target)
    ((RawCtxSelectedFamilyContext.ownerFrame candidate.server_binding.identity_key_id read inner).2
      (RawCtxSelectedFamilyNativeContext.ownerReply candidate.server_binding.identity_key_id read inner
        (realize parent target)))).run (RawCtxSelectedReceiveCompiler.project state)
  let finished := PqxdhInitialPostContext.finishResult index before control candidate result.1
  (simulateQ (nativeFlat pre application initial selector aux source writer prior (some parent) key target nonce next
    sender route read mark) (outside finished.1)).run
      ((finished.2, PqxdhInitialOriginContext.finishedTrace trace origin index finished.1), result.2)

noncomputable def selectedPendingFinish (quiet : RawCtxQuietOwnerTails.Quiet inner)
    (state : RawCtxSelectedReceiveCompiler.State (Local A N C)) := do
  let result ← (RawCtxSelectedReceiveCompiler.evaluated source key read
    (RawCtxSelectedPendingOwnerCompiler.owner source writer prior target nonce next read inner material quiet)).run state
  let finished := afterOwner index (initialFront before) control candidate result.1
  Prod.map id (tracedProj key) <$>
    (simulateQ (tracedPlain pre application initial selector aux source writer prior (some parent) key target nonce next
      sender route read mark) (outside finished.1)).run
        ((finished.2, RawCtxSelectedReceiveCompiler.project result.2),
          PqxdhInitialOriginContext.finishedTrace trace origin index finished.1)

/-- The saved owner completion, actual initial acceptance and full outside schedule agree with all source failures and state effects retained. -/
theorem finish_source (quiet : RawCtxQuietOwnerTails.Quiet inner)
    (admitted : RawCtxForwardOwnerScope.Valid read inner)
    (state : RawCtxSelectedReceiveCompiler.State (Local A N C)) :
    nativeFinish pre application initial selector aux source writer prior key target nonce next mark sender route read
      index before trace origin control candidate outside inner material state =
    selectedPendingFinish pre application initial selector aux source writer prior key target nonce next mark sender route read
      index before trace origin control candidate outside inner material quiet state := by
  rw [nativeFinish, RawCtxSelectedPendingOwnerCompiler.owner_source source writer prior key target nonce next read
    candidate.server_binding.identity_key_id inner material state quiet admitted]
  simp only [selectedPendingFinish, bind_map_left]
  apply bind_congr
  intro result
  have finished := afterOwner_source key index (initialFront before) control candidate result.1
  simp only [frontOf_initial] at finished
  rw [finished]
  exact (post_program (P := P) (S := S) (B := B) pre application initial selector aux source writer prior
    (some parent) key target nonce next sender route read mark
    (outside (afterOwner index (initialFront before) control candidate result.1).1)
    (((afterOwner index (initialFront before) control candidate result.1).2,
      RawCtxSelectedReceiveCompiler.project result.2),
      PqxdhInitialOriginContext.finishedTrace trace origin index
        (afterOwner index (initialFront before) control candidate result.1).1)).symm

/-- The source completion is the literal saved initial-finish descriptor with its already retained installation marker. -/
theorem finish_resume (state : RawCtxSelectedReceiveCompiler.State (Local A N C)) :
    (fun result => (result.1.1, (result.1.2, result.2))) <$>
    (simulateQ (lowered pre application initial selector aux source writer
      (privateTable prior (some parent) target (RawCtxSelectedMessageKdf.response key nonce next)))
      (PqxdhInitialOriginContext.resume mark sender route read
        ⟨.inl (.finish index before control candidate outside inner), trace, origin⟩
        (RawCtxSelectedFamilyNativeContext.ownerReply candidate.server_binding.identity_key_id read inner
          (realize parent target)))).run (RawCtxSelectedReceiveCompiler.project state) =
      nativeFinish pre application initial selector aux source writer prior key target nonce next mark sender route read
        index before trace origin control candidate outside inner material state := by
  simp only [PqxdhInitialOriginContext.resume, simulateQ_bind, StateT.run_bind]
  simp only [map_bind, ← QueryImpl.simulateQ_compose,
    simulateQ_mapStateTBase_run_eq_map_flattenStateT, Functor.map_map, nativeFinish, nativeFlat,
    privateTable]
  simp only [Prod.eta, id_map']
  have forwarded : (lowered (S := S) (B := B) pre application initial selector aux source writer
      (lookup (RawCtxSelectedParentPrivatePatch.privatePatch prior target
        (RawCtxSelectedMessageKdf.response key nonce next)) parent target) ∘ₛ
      PqxdhInitialPendingPost.primitiveForward) =
      RawCtxSelectedParentNativeCompiler.pending source writer
        (RawCtxSelectedParentPrivatePatch.privatePatch prior target
          (RawCtxSelectedMessageKdf.response key nonce next)) parent target := by
    funext query
    simp only [QueryImpl.compose, PqxdhInitialPendingPost.primitiveForward, simulateQ_spec_query,
      lowered, RawCtxRetainedParentBackend.retained_live, RawCtxSelectedParentFamilyMap.nativeLive,
      RawCtxPendingFamilyLiveQueries.handler]
  rw [forwarded]

/-- The exact retained saved finish is the selected owner followed by all original publication and Post work, projecting only auxiliary instrumentation. -/
theorem retained_finish (quiet : RawCtxQuietOwnerTails.Quiet inner)
    (admitted : RawCtxForwardOwnerScope.Valid read inner)
    (state : RawCtxSelectedReceiveCompiler.State (Local A N C)) :
    (simulateQ (PqxdhInitialNativeRetained.retained source writer
      (privateTable prior (some parent) target (RawCtxSelectedMessageKdf.response key nonce next))
      (lifted pre application initial selector aux))
      (PqxdhInitialOriginContext.resume mark sender route read
        ⟨.inl (.finish index before control candidate outside inner), trace, origin⟩
        (RawCtxSelectedFamilyNativeContext.ownerReply candidate.server_binding.identity_key_id read inner
          (realize parent target)))).run
          (retainedOf (RawCtxSelectedReceiveCompiler.project state)) =
      (fun result => ((result.1, result.2.1), retainedOf result.2.2)) <$>
        selectedPendingFinish pre application initial selector aux source writer prior key target nonce next mark sender route read
          index before trace origin control candidate outside inner material quiet state := by
  rw [← low_program pre application initial selector aux]
  have actual := congrArg (fun work => (fun result => ((result.1, result.2.1), retainedOf result.2.2)) <$> work)
    ((finish_resume pre application initial selector aux source writer prior key target nonce next mark sender route read
      index before trace origin control candidate outside inner material state).trans
      (finish_source pre application initial selector aux source writer prior key target nonce next mark sender route read
        index before trace origin control candidate outside inner material quiet admitted state))
  simpa only [Functor.map_map, Prod.map_def, id_eq] using actual

end BeaconcryptCore.Computational.PqxdhLaterSavedFinish

/-- info: 'BeaconcryptCore.Computational.PqxdhLaterSavedFinish.afterOwner_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterSavedFinish.afterOwner_source
/-- info: 'BeaconcryptCore.Computational.PqxdhLaterSavedFinish.finish_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterSavedFinish.finish_source
/-- info: 'BeaconcryptCore.Computational.PqxdhLaterSavedFinish.finish_resume' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterSavedFinish.finish_resume
/-- info: 'BeaconcryptCore.Computational.PqxdhLaterSavedFinish.retained_finish' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterSavedFinish.retained_finish
