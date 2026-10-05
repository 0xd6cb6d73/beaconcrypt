import BeaconcryptCore.Computational.PqxdhLaterSavedPostComparison

/-! Join the complete saved-source comparison to its literal source frame, preserving its true decision, publication trace and reached native cache. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.refined ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhLaterSavedFrameJoin
open PqxdhSecretInputKdf PqxdhFullSecretInputKdf PqxdhJointKdfGame PqxdhNativeSharedPrefix
open RawCtxSelectedParentTable RawCtxSelectedParentEntry RawCtxSelectedMessageDriver
open PqxdhSelectedFirstRecord PqxdhFirstRecordConfidentiality
variable {ι I D K X Response Shared A N C M P : Type} {extra : OracleSpec ι} {S B : Nat}
variable
    (pre : QueryImpl (PqxdhBeaconPhase2Shared.Spec I D K X Response Shared) (StateT (ExternalState A N C) ProbComp))
    (application : Response → LocalCallback A N C (Option Pqxdh.Bytes))
    (initial : PqxdhBeaconPhase2Shared.Secrets Shared → LocalCallback A N C PqxdhInitialNativeAudit.InitialReply)
    (selector : QueryImpl extra (StateT (ExternalState A N C) ProbComp))
    (aux : QueryImpl PqxdhServerRegistrationPublication.AuxSpec (StateT (ExternalState A N C) ProbComp))
    (fixed : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (key target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (mark : PqxdhBeaconPhase2Shared.Secrets Shared → Bool)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (read : RawCtxReceive.FrameDecoder)
    (monitor : Fin B) (qPost : Nat)
    (context : PqxdhInitialOriginContext.Context extra M P I D K Bool Bool S B)
    (material : PqxdhOrderedChainHybrids.Material)
    (fits : PqxdhInitialOriginCertificates.Fits qPost context)
    (state : RawCtxSelectedReceiveCompiler.State (Local A N C))
local notation "parent" => Entry.mk (PqxdhInitialBuilderContext.address context.original) material

/-- Projecting the original saved-source comparison retains the same complete frame execution and native state, including optional source replies and the original outside schedule. -/
theorem original_frame (admitted : PqxdhInitialDescriptorScope.Valid read context) :
    (fun result => (result.1, ((tracedProj key result.2).1,
      retainedOf (tracedProj key result.2).2))) <$>
      PqxdhLaterSavedPostComparison.original pre application initial selector aux fixed writer prior key target nonce next mark sender route
        read qPost context material fits state =
    (fun result => (some result.1.1, (result.1.2, result.2))) <$>
      (simulateQ (PqxdhInitialNativeRetained.retained fixed writer
        (privateTable prior (some parent) target (RawCtxSelectedMessageKdf.response key nonce next))
        (lifted pre application initial selector aux))
        (PqxdhInitialOriginContext.resume mark sender route read context
          (PqxdhInitialParentBuilderContext.reply sender route read context.original (realize parent target)))).run
            (retainedOf (RawCtxSelectedReceiveCompiler.project state)) := by
  rw [PqxdhLaterSavedContext.retained_complete pre application initial selector aux fixed writer prior key target nonce next mark
    sender route read qPost context material fits admitted state]
  have projected := congrArg (fun computation =>
    (fun result => (result.1, (result.2.1, retainedOf result.2.2))) <$> computation)
    (PqxdhLaterSavedPostComparison.original_source pre application initial selector aux fixed writer prior key target nonce next mark
      sender route read qPost context material fits state)
  simpa only [Functor.map_map] using projected

/-- A successful original comparison result supplies the literal resumed frame result with the same returned bit, complete frontend, publication trace and projected native state. -/
theorem original_frame_support (admitted : PqxdhInitialDescriptorScope.Valid read context)
    (value : Bool) (after : Traced M P I D K A N C S B)
    (supported : (some value, after) ∈ support (PqxdhLaterSavedPostComparison.original pre application initial selector aux fixed writer prior
      key target nonce next mark sender route read qPost context material fits state)) :
    ((value, (tracedProj key after).1), retainedOf (tracedProj key after).2) ∈ support
      ((simulateQ (PqxdhInitialNativeRetained.retained fixed writer
        (privateTable prior (some parent) target (RawCtxSelectedMessageKdf.response key nonce next))
        (lifted pre application initial selector aux))
        (PqxdhInitialOriginContext.resume mark sender route read context
          (PqxdhInitialParentBuilderContext.reply sender route read context.original (realize parent target)))).run
            (retainedOf (RawCtxSelectedReceiveCompiler.project state))) := by
  have projected : (some value, ((tracedProj key after).1, retainedOf (tracedProj key after).2)) ∈ support
      ((fun result => (result.1, ((tracedProj key result.2).1, retainedOf (tracedProj key result.2).2))) <$>
        PqxdhLaterSavedPostComparison.original pre application initial selector aux fixed writer prior key target nonce next mark sender route
          read qPost context material fits state) := by
    rw [support_map]
    exact ⟨(some value, after), supported, rfl⟩
  rw [original_frame pre application initial selector aux fixed writer prior key target nonce next mark sender route read qPost
    context material fits state admitted, support_map] at projected
  obtain ⟨finished, actual, same⟩ := projected
  have equal : finished = ((value, (tracedProj key after).1), retainedOf (tracedProj key after).2) := by
    rcases finished with ⟨⟨result, front⟩, backend⟩
    simpa only [Prod.mk.injEq, Option.some.injEq, and_assoc] using same
  exact equal ▸ actual

end BeaconcryptCore.Computational.PqxdhLaterSavedFrameJoin

/-- info: 'BeaconcryptCore.Computational.PqxdhLaterSavedFrameJoin.original_frame' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterSavedFrameJoin.original_frame
/-- info: 'BeaconcryptCore.Computational.PqxdhLaterSavedFrameJoin.original_frame_support' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterSavedFrameJoin.original_frame_support
