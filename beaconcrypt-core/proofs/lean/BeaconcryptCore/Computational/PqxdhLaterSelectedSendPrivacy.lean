import BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality

/-! The selected challenge send at a later retained-parent cut. The parent-priority collision remains an explicit branch; outside it, the complete optional send is the already checked selected send. This is an operational two-plaintext relation, not a source-origin or freshness assumption. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhLaterSelectedSendPrivacy
open PqxdhSecretInputKdf PqxdhJointKdfGame PqxdhFullSecretInputKdf
open RawCtxSelectedParentTable RawCtxSelectedParentEntry

/-- At the actual selected address, a distinct retained-parent address leaves the complete selected response unchanged. The separate parent-alias event is not removed from the source experiment. -/
theorem derive_target (prior : Prior) (parent : Entry) (target : RootOutput)
    (nonce : NonceOutput) (next : RootOutput) (request : SymmetricRatchetKdfRequest)
    (selected : RawCtxKdfRequestTable.address request = RawCtxSelectedParentPrivatePatch.targetAddress target)
    (separate : RawCtxSelectedParentPrivatePatch.targetAddress target ≠ parent.address) :
    RawCtxSelectedSendCompiler.deriveValue prior (some parent) target nonce next request =
      RawCtxSelectedSendCompiler.deriveValue prior none target nonce next request := by
  simp only [RawCtxSelectedSendCompiler.deriveValue, RawCtxSelectedMessageKdf.later, selected, ite_eq_right (fun h => (separate h).elim)]

/-- The whole later selected send is literally the existing selected-send program, including exhaustion, nonce refusal, optional writer failure and the advanced complete kernel. No continuation is discarded. -/
theorem send_selected (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (parent : Entry) (target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (kernel : RawCtxSelectedMessageReveals.Kernel) (context : RawCtxSourceSend.SealContext)
    (selected : RawCtxSelectedPendingCut.requestAddress kernel.send_chain = RawCtxSelectedParentPrivatePatch.targetAddress target)
    (separate : RawCtxSelectedParentPrivatePatch.targetAddress target ≠ parent.address) :
    RawCtxSelectedSendCompiler.send source writer prior (some parent) target nonce next kernel context =
      RawCtxSelectedSendCompiler.send source writer prior none target nonce next kernel context := by
  rw [RawCtxSelectedSendCompiler.send_cases, RawCtxSelectedSendCompiler.send_cases]
  cases admitted : RawCtxInterpretedSend.normalBegin kernel context with
  | exhausted entry actual => rfl
  | requested pending =>
    simp only [derive_target prior parent target nonce next pending.request
      ((RawCtxSelectedSendAddress.admitted_address kernel context pending admitted).trans selected) separate]

/-- For the same reached selected input, both challenge plaintexts use the unchanged selected seal interface and retain identical full optional continuations. This relation is valid at any source send counter and for either role's supplied seal context. -/
theorem send_twin (left right : Pqxdh.Bytes) (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (parent : Entry) (target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (kernel : RawCtxSelectedMessageReveals.Kernel) (context : RawCtxSourceSend.SealContext)
    (selected : RawCtxSelectedPendingCut.requestAddress kernel.send_chain = RawCtxSelectedParentPrivatePatch.targetAddress target)
    (separate : RawCtxSelectedParentPrivatePatch.targetAddress target ≠ parent.address) :
    PqxdhFirstRecordConfidentiality.Twin left right (fun a b => a = b) (fun _ => False) (fun _ => False)
      (RawCtxSelectedSendCompiler.send source writer prior (some parent) target nonce next kernel { context with plaintext := left })
      (RawCtxSelectedSendCompiler.send source writer prior (some parent) target nonce next kernel { context with plaintext := right }) := by
  rw [send_selected source writer prior parent target nonce next kernel _ selected separate,
    send_selected source writer prior parent target nonce next kernel _ selected separate]
  exact PqxdhFirstRecordConfidentiality.send_twin left right source writer prior target nonce next kernel context selected

end BeaconcryptCore.Computational.PqxdhLaterSelectedSendPrivacy

/-- info: 'BeaconcryptCore.Computational.PqxdhLaterSelectedSendPrivacy.derive_target' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterSelectedSendPrivacy.derive_target
/-- info: 'BeaconcryptCore.Computational.PqxdhLaterSelectedSendPrivacy.send_selected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterSelectedSendPrivacy.send_selected
/-- info: 'BeaconcryptCore.Computational.PqxdhLaterSelectedSendPrivacy.send_twin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterSelectedSendPrivacy.send_twin
