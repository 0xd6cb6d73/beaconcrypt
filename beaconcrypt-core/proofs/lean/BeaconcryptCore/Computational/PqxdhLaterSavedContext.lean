import BeaconcryptCore.Computational.PqxdhLaterSavedBuilder

/-! A single completion consumes the actual saved record, Beacon finish or Server builder descriptor and retains its complete original outside schedule. -/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.refined ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhLaterSavedContext
open PqxdhSecretInputKdf PqxdhFullSecretInputKdf PqxdhJointKdfGame PqxdhNativeSharedPrefix
open RawCtxSelectedParentTable RawCtxSelectedParentEntry RawCtxSelectedMessageDriver
open PqxdhSelectedFirstRecord
variable {ι I D K X Response Shared A N C M P Result : Type} {extra : OracleSpec ι} {S B : Nat}
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
    (qPost : Nat)
    (context : PqxdhInitialOriginContext.Context extra M P I D K Result Bool S B)
    (material : PqxdhOrderedChainHybrids.Material)

noncomputable def complete (fits : PqxdhInitialOriginCertificates.Fits qPost context)
    (state : RawCtxSelectedReceiveCompiler.State (Local A N C)) :
    ProbComp (Result × ((PqxdhInitialPostContext.NativeFront M P I D K S B × PqxdhInitialOriginPost.Trace Bool S B) ×
      RawCtxSharedPrimitive.SharedState (Local A N C))) :=
  match context, fits with
  | ⟨.inl (.record request before outside inner), trace, _⟩, fits =>
      PqxdhLaterSavedRecord.selectedRecord pre application initial selector aux source writer prior key target nonce next
        mark sender route read request before trace outside inner material fits.2 state
  | ⟨.inl (.finish index before control candidate outside inner), trace, origin⟩, fits =>
      PqxdhLaterSavedFinish.selectedPendingFinish pre application initial selector aux source writer prior key target nonce next
        mark sender route read index before trace origin control candidate outside inner material fits.2 state
  | ⟨.inr builder, trace, origin⟩, _ =>
      PqxdhLaterSavedBuilder.selectedBuilder pre application initial selector aux source writer prior key target nonce next
        mark sender route read trace origin builder material state

local notation "parent" => Entry.mk (PqxdhInitialBuilderContext.address context.original) material

/-- Every literal source descriptor completes through its corresponding selected-material operation and the same full adaptive Post continuation. -/
theorem retained_complete (fits : PqxdhInitialOriginCertificates.Fits qPost context)
    (admitted : PqxdhInitialDescriptorScope.Valid read context)
    (state : RawCtxSelectedReceiveCompiler.State (Local A N C)) :
    (simulateQ (PqxdhInitialNativeRetained.retained source writer
      (privateTable prior (some parent) target (RawCtxSelectedMessageKdf.response key nonce next))
      (lifted pre application initial selector aux))
      (PqxdhInitialOriginContext.resume mark sender route read context
        (PqxdhInitialParentBuilderContext.reply sender route read context.original (realize parent target)))).run
          (retainedOf (RawCtxSelectedReceiveCompiler.project state)) =
      (fun result => ((result.1, result.2.1), retainedOf result.2.2)) <$>
        complete pre application initial selector aux source writer prior key target nonce next mark sender route read
          qPost context material fits state := by
  rcases context with ⟨original, trace, origin⟩
  cases original with
  | inl original =>
      cases original with
      | record request before outside inner =>
          exact PqxdhLaterSavedRecord.retained_record pre application initial selector aux source writer prior key target nonce next
            mark sender route read request before trace outside inner material origin fits.2 admitted state
      | finish index before control candidate outside inner =>
          exact PqxdhLaterSavedFinish.retained_finish pre application initial selector aux source writer prior key target nonce next
            mark sender route read index before trace origin control candidate outside inner material fits.2 admitted state
  | inr builder =>
      exact PqxdhLaterSavedBuilder.retained_builder pre application initial selector aux source writer prior key target nonce next
        mark sender route read trace origin builder material state

end BeaconcryptCore.Computational.PqxdhLaterSavedContext

/-- info: 'BeaconcryptCore.Computational.PqxdhLaterSavedContext.retained_complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterSavedContext.retained_complete
