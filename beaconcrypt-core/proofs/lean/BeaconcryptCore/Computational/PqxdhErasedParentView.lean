import BeaconcryptCore.Computational.PqxdhInitialSourcePreparedSecrecy

/-! The complete final-material observer depends on the actual retained descriptor and state, not on support-proof annotations or the no-longer-used initial commitment cache. Erasure exposes the exact runtime carrier needed by the ordinary shared-ROM compiler; all original Gate/Fresh checks remain present. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhErasedParentView
open PqxdhJointKdf PqxdhJointKdfGame PqxdhSecretInputKdf PqxdhFullSecretInputKdf
open PqxdhInitialBeaconAmbient PqxdhInitialSupportedCertificate RawCtxSelectedParentEntry
variable {ι M P I D K X Response Shared A N C : Type} {extra : OracleSpec ι} {S B : Nat}

variable (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
  (pre : QueryImpl (PqxdhBeaconPhase2Shared.Spec I D K X Response Shared) (Ambient A N C))
  (application : Response → Ambient A N C (Option Pqxdh.Bytes))
  (initializer : PqxdhBeaconPhase2Shared.Secrets Shared → Ambient A N C PqxdhInitialNativeAudit.InitialReply)
  (selector : QueryImpl extra (Ambient A N C))
  (aux : QueryImpl PqxdhServerRegistrationPublication.AuxSpec (Ambient A N C))
  (mark : PqxdhBeaconPhase2Shared.Secrets Shared → Bool)
  (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)

variable (root : RootOutput) (ancestors disclosed : List RatchetChain)
  (selected : RawCtxProtocolReveals.Owner S B) (number : Std.U64) (remaining : Nat)

noncomputable def view : PqxdhInitialCommonSecrecy.View
    (Input extra M P I D K Bool Bool A N C S B) extra M P I D K X Response Shared A N C S B where
  continuation := {
    cut input := input.1
    depth _ := some remaining
    prior input := RawCtxSelectedParentTable.view (productionStream source.crypto) input.2.1.1.1.2.1
    initial input := PqxdhInitialStoppedDisclosure.initial disclosed input.1.1 (ambient input.1) input.1.2.2
    pre _ := pre
    application _ := application
    initializer _ := initializer
    selector _ := selector
    aux _ := aux
    event input := PqxdhInitialPrivateCheckedFreshness.remainingEvent
      (PqxdhInitialSourceSecrecyResources.earlier root ancestors input.1) disclosed
      (fun result => PqxdhInitialPublishedEvent.Gate selected number result.1.1) }
  disclosed := disclosed
  earlier input := PqxdhInitialSourceSecrecyResources.earlier root ancestors input
  ambient input := ambient input
  priorCandidates input := input.2.2
  selected := selected
  number := number
  remaining := remaining
  depth _ := rfl

variable (execution : PqxdhInitialNativeCarried.Execution extra M P I D K Bool Bool S B)
    (depth : Nat) (state : PqxdhInitialNativeAudit.State A N C)
local notation "sourceRun" => PqxdhInitialNativeAuditCarried.carried source writer pre application initializer selector aux
  mark sender route decode execution depth (depth + 1) state

set_option maxRecDepth 8192 in
/-- The complete native source event and continuation factor through the retained descriptor/state; no final event equality is assumed. -/
theorem native_erase (context : (Bool ⊕ Supported sourceRun) × Entry) (target : RootOutput) (output : FullOutput) :
    PqxdhInitialCommonSecrecy.native source writer mark sender route decode
      (PqxdhInitialSourceSecrecyResources.view source writer pre application initializer selector aux mark sender route decode
        execution depth state root ancestors disclosed selected number remaining) context target output =
    PqxdhInitialCommonSecrecy.native source writer mark sender route decode
      (view source pre application initializer selector aux root ancestors disclosed selected number remaining)
      (Sum.map id Subtype.val context.1, context.2) target output := by
  rcases context with ⟨common | pending, entry⟩ <;> rfl

end BeaconcryptCore.Computational.PqxdhErasedParentView


/-- info: 'BeaconcryptCore.Computational.PqxdhErasedParentView.native_erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhErasedParentView.native_erase
