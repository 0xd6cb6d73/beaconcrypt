import BeaconcryptCore.Computational.PqxdhSelectedFirstRecord
import BeaconcryptCore.Computational.PqxdhPreparedDescriptorScope
import BeaconcryptCore.Computational.RawCtxSelectedPendingRoleCompiler

/-! The saved record cut completes its actual pending request and then the same entire Post continuation, retaining the original publication trace and shared source state. -/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.refined ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhLaterSavedRecord
open PqxdhSecretInputKdf PqxdhFullSecretInputKdf PqxdhJointKdfGame PqxdhNativeSharedPrefix
open RawCtxSelectedParentTable RawCtxSelectedParentEntry RawCtxSelectedMessageDriver
open PqxdhSelectedFirstRecord
variable {ι I D K X Response Shared A N C M P Result : Type} {extra : OracleSpec ι} {S B : Nat}

private theorem roles_afterRecord (key : RootOutput)
    (roles : RawCtxGenericFamilyLive.State RawCtxSelectedMessageReveals.Kernel M P I D K S B) :
    rolesOf key (roles.1, RawCtxSelectedMessageRevealInitialization.fromHistory roles.2) =
      RawCtxGenericFamilyLive.mapState
        (RawCtxMaterialInterpretation.mapRefined (RawCtxSelectedMessageKey.interpret key)) roles :=
  Prod.ext (rolesOf_roles key _)
    ((rolesOf_history key _).trans (RawCtxSelectedMessageRevealInitialization.history_roundtrip key roles.2))

def afterRecord (before : PqxdhInitialPostContext.NativeFront M P I D K S B)
    (roles : RawCtxGenericFamilyLive.State RawCtxSelectedMessageReveals.Kernel M P I D K S B) :
    PqxdhSelectedPostCompiler.Front M P I D K S B :=
  ⟨(roles.1, RawCtxSelectedMessageRevealInitialization.fromHistory roles.2), before.controls, before.consumed⟩

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
    (request : (RawCtxProtocolReveals.SourceSpec S B).Domain)
    (before : PqxdhInitialPostContext.NativeFront M P I D K S B)
    (trace : PqxdhInitialOriginPost.Trace Bool S B)
    (outside : (RawCtxProtocolReveals.SourceSpec S B).Range request →
      OracleComp (PqxdhInitialGenericPost.Spec extra S B) Result)
    (inner : RawCtxSelectedFamilyContext.Context M P I D K
      ((RawCtxProtocolReveals.SourceSpec S B).Range request) S B)
    (material : PqxdhOrderedChainHybrids.Material)

local notation "parent" => RawCtxSelectedPendingRoleCompiler.liveEntry inner material

noncomputable def nativeRecord (state : RawCtxSelectedReceiveCompiler.State (Local A N C)) := do
  let result ← (simulateQ (RawCtxSelectedParentFamilyMap.nativeLive source writer
    (RawCtxSelectedParentPrivatePatch.privatePatch prior target (RawCtxSelectedMessageKdf.response key nonce next)) parent target)
    ((RawCtxSelectedFamilyContext.frame sender route read inner).2
      (RawCtxSelectedFamilyNativeContext.reply sender route read inner (realize parent target)))).run
        (RawCtxSelectedReceiveCompiler.project state)
  (simulateQ (nativeFlat pre application initial selector aux source writer prior (some parent) key target nonce next
    sender route read mark) (outside result.1.1)).run
      (({ before with roles := result.1.2 }, PqxdhInitialOriginPost.record trace request result.1.1), result.2)

noncomputable def selectedRecord (quiet : PqxdhInitialPostCertificates.LiveQuiet inner)
    (state : RawCtxSelectedReceiveCompiler.State (Local A N C)) := do
  let result ← (RawCtxSelectedReceiveCompiler.evaluated source key read
    (RawCtxSelectedPendingRoleCompiler.live source writer prior target nonce next read inner material quiet)).run state
  Prod.map id (tracedProj key) <$>
    (simulateQ (tracedPlain pre application initial selector aux source writer prior (some parent) key target nonce next
      sender route read mark) (outside result.1.1)).run
        ((afterRecord before result.1.2, RawCtxSelectedReceiveCompiler.project result.2),
          PqxdhInitialOriginPost.record trace request result.1.1)

/-- The exact pending record and complete saved outside client agree jointly with every retained role, disclosure, publication annotation and shared cache. -/
theorem record_source (quiet : PqxdhInitialPostCertificates.LiveQuiet inner)
    (admitted : RawCtxForwardRoleScope.LiveValid read inner)
    (state : RawCtxSelectedReceiveCompiler.State (Local A N C)) :
    nativeRecord pre application initial selector aux source writer prior key target nonce next mark sender route read
      request before trace outside inner material state =
    selectedRecord pre application initial selector aux source writer prior key target nonce next mark sender route read
      request before trace outside inner material quiet state := by
  rw [nativeRecord, RawCtxSelectedPendingRoleCompiler.live_source source writer prior key target nonce next
    sender route read inner material state quiet admitted]
  simp only [selectedRecord, bind_map_left, post_program, tracedProj, frontOf, afterRecord,
    roles_afterRecord]


/-- The source side is the literal saved record descriptor under the same retained lookup, not a replacement record scheduler. -/
theorem record_resume (origin : Option Bool)
    (state : RawCtxSelectedReceiveCompiler.State (Local A N C)) :
    (fun result => (result.1.1, (result.1.2, result.2))) <$>
    (simulateQ (lowered pre application initial selector aux source writer
      (privateTable prior (some parent) target (RawCtxSelectedMessageKdf.response key nonce next)))
      (PqxdhInitialOriginContext.resume mark sender route read
        ⟨.inl (.record request before outside inner), trace, origin⟩
        (RawCtxSelectedFamilyNativeContext.reply sender route read inner (realize parent target)))).run
          (RawCtxSelectedReceiveCompiler.project state) =
      nativeRecord pre application initial selector aux source writer prior key target nonce next mark sender route read
        request before trace outside inner material state := by
  simp only [PqxdhInitialOriginContext.resume, simulateQ_bind, StateT.run_bind]
  simp only [map_bind, ← QueryImpl.simulateQ_compose,
    simulateQ_mapStateTBase_run_eq_map_flattenStateT, Functor.map_map, nativeRecord, nativeFlat,
    privateTable, ← RawCtxRetainedParentBackend.retained_live]
  simp only [Prod.eta, id_map']
  have forwarded := live_forward (S := S) (B := B) pre application initial selector aux source writer prior
    (some parent) key target nonce next
  simp only [privateTable] at forwarded
  rw [forwarded]
  rfl


/-- The retained source completion of the exact descriptor is the selected record and full outside Post execution after projecting only auxiliary instrumentation. -/
theorem retained_record (origin : Option Bool)
    (quiet : PqxdhInitialPostCertificates.LiveQuiet inner)
    (admitted : RawCtxForwardRoleScope.LiveValid read inner)
    (state : RawCtxSelectedReceiveCompiler.State (Local A N C)) :
    (simulateQ (PqxdhInitialNativeRetained.retained source writer
      (privateTable prior (some parent) target (RawCtxSelectedMessageKdf.response key nonce next))
      (lifted pre application initial selector aux))
      (PqxdhInitialOriginContext.resume mark sender route read
        ⟨.inl (.record request before outside inner), trace, origin⟩
        (RawCtxSelectedFamilyNativeContext.reply sender route read inner (realize parent target)))).run
          (retainedOf (RawCtxSelectedReceiveCompiler.project state)) =
      (fun result => ((result.1, result.2.1), retainedOf result.2.2)) <$>
        selectedRecord pre application initial selector aux source writer prior key target nonce next mark sender route read
          request before trace outside inner material quiet state := by
  rw [← low_program pre application initial selector aux]
  have actual := congrArg (fun work => (fun result => ((result.1, result.2.1), retainedOf result.2.2)) <$> work)
    ((record_resume pre application initial selector aux source writer prior key target nonce next mark sender route read
      request before trace outside inner material origin state).trans
      (record_source pre application initial selector aux source writer prior key target nonce next mark sender route read
        request before trace outside inner material quiet admitted state))
  simpa only [Functor.map_map, Prod.map_def, id_eq] using actual

end BeaconcryptCore.Computational.PqxdhLaterSavedRecord

/-- info: 'BeaconcryptCore.Computational.PqxdhLaterSavedRecord.record_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterSavedRecord.record_source
/-- info: 'BeaconcryptCore.Computational.PqxdhLaterSavedRecord.record_resume' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterSavedRecord.record_resume
/-- info: 'BeaconcryptCore.Computational.PqxdhLaterSavedRecord.retained_record' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterSavedRecord.retained_record
