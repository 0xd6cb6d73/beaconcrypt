import BeaconcryptCore.Computational.RawCtxSelectedMessageDriver
import BeaconcryptCore.Computational.RawCtxSelectedSealConsumer

/-!
A selected seal is attributed to an actual send derivation at the exact selected full76 address. Retained predecessor priority, known byte aliases and the original send advancement stay explicit. Repeated receive derivations are not sealing occurrences. These operational facts identify the source event needed for nonce accounting; they do not assume or prove that address recurrences are unlikely.
-/
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.refined ratchet.concrete
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RawCtxSelectedSendAddress
open PqxdhSecretInputKdf PqxdhFullSecretInputKdf RawCtxSelectedMessageKey
open RawCtxSelectedMessageKdf RawCtxSelectedParentTable RawCtxSelectedParentEntry RawCtxFreshChainCut

/-- A selected material marker is produced only by the exact full input/domain match, and carries the retained nonce from that one complete response. -/
theorem step_selected (prior : Prior) (target : RootOutput) (nonce chosen : NonceOutput) (next : RootOutput)
    (request : SymmetricRatchetKdfRequest) :
    (RawCtxSelectedMessageKdf.step prior target nonce next request).2 = .hidden chosen ↔
      RawCtxKdfRequestTable.address request = RawCtxSelectedParentPrivatePatch.targetAddress target ∧ chosen = nonce := by
  unfold RawCtxSelectedMessageKdf.step
  split <;> simp_all [known, eq_comm]

/-- A retained predecessor always stays known; a selected child marker additionally requires the exact target address outside that predecessor branch. -/
theorem later_selected (prior : Prior) (parent : Entry) (target : RootOutput) (nonce chosen : NonceOutput)
    (next : RootOutput) (request : SymmetricRatchetKdfRequest) :
    (later prior parent target nonce next request).2 = .hidden chosen ↔
      RawCtxKdfRequestTable.address request ≠ parent.address ∧
        RawCtxKdfRequestTable.address request = RawCtxSelectedParentPrivatePatch.targetAddress target ∧ chosen = nonce := by
  unfold later
  split
  · simp_all [known]
  · rw [step_selected]
    simp_all

/-- Every admitted send requests the actual old sending chain under the production label, with its original complete entry and context. -/
theorem admitted_request {Material Context : Type}
    (entry : RefinedRatchet RatchetChain RatchetChain Material) (context : Context)
    (pending : RawCtxInterpretedSend.Kdf Material Context)
    (admitted : RawCtxInterpretedSend.normalBegin entry context = .requested pending) :
    pending.entry = entry ∧ pending.context = context ∧ pending.request.input = entry.send_chain.bytes ∧
      pending.request.info = SYM_RATCHET_INFO := by
  have begun := RawCtxInterpretedSend.normalBegin_exact entry context
  rw [admitted] at begun
  simp only [RawCtxInterpretedSend.beginSend, RatchetChain.as_bytes, SymmetricRatchetKdfRequest.new,
    Bind.bind, Aeneas.Std.bind] at begun
  repeat' split at begun
  all_goals simp_all only [RustM.ok.injEq, reduceCtorEq]
  all_goals cases begun
  all_goals exact ⟨rfl, rfl, rfl, rfl⟩

/-- The admitted source address is determined by the old send chain and the production label, independently of owner and sequence metadata. -/
theorem admitted_address {Material Context : Type}
    (entry : RefinedRatchet RatchetChain RatchetChain Material) (context : Context)
    (pending : RawCtxInterpretedSend.Kdf Material Context)
    (admitted : RawCtxInterpretedSend.normalBegin entry context = .requested pending) :
    RawCtxKdfRequestTable.address pending.request = RawCtxSelectedPendingCut.requestAddress entry.send_chain := by
  obtain ⟨_, _, input, info⟩ := admitted_request entry context pending admitted
  simp only [RawCtxKdfRequestTable.address, input, info, RawCtxSelectedPendingCut.requestAddress,
    RawCtxChainSend.nativeRequest]

/-- The selected seal marker belongs to an actual admitted sending-chain address. Receiving the same cached material is absent from this event. -/
theorem selected_send {Context : Type} (prior : Prior) (target : RootOutput) (nonce chosen : NonceOutput)
    (next : RootOutput) (entry : RefinedRatchet RatchetChain RatchetChain Slot) (context : Context)
    (pending : RawCtxInterpretedSend.Kdf Slot Context)
    (admitted : RawCtxInterpretedSend.normalBegin entry context = .requested pending) :
    (RawCtxInterpretedSend.ready pending
      (RawCtxSelectedMessageKdf.step prior target nonce next pending.request)).material = .hidden chosen ↔
      RawCtxSelectedPendingCut.requestAddress entry.send_chain =
        RawCtxSelectedParentPrivatePatch.targetAddress target ∧ chosen = nonce := by
  change (RawCtxSelectedMessageKdf.step prior target nonce next pending.request).2 = .hidden chosen ↔ _
  rw [step_selected, admitted_address entry context pending admitted]

/-- The later source retains predecessor priority when attributing a selected send, even for an address collision. -/
theorem selected_later_send {Context : Type} (prior : Prior) (parent : Entry) (target : RootOutput)
    (nonce chosen : NonceOutput) (next : RootOutput)
    (entry : RefinedRatchet RatchetChain RatchetChain Slot) (context : Context)
    (pending : RawCtxInterpretedSend.Kdf Slot Context)
    (admitted : RawCtxInterpretedSend.normalBegin entry context = .requested pending) :
    (RawCtxInterpretedSend.ready pending
      (later prior parent target nonce next pending.request)).material = .hidden chosen ↔
      RawCtxSelectedPendingCut.requestAddress entry.send_chain ≠ parent.address ∧
        RawCtxSelectedPendingCut.requestAddress entry.send_chain =
          RawCtxSelectedParentPrivatePatch.targetAddress target ∧ chosen = nonce := by
  change (later prior parent target nonce next pending.request).2 = .hidden chosen ↔ _
  rw [later_selected, admitted_address entry context pending admitted]

/-- A selected send installs its retained next chain while preserving every other entry field, independently of the eventual writer outcome. -/
theorem selected_advance {Context : Type} (prior : Prior) (target : RootOutput) (nonce chosen : NonceOutput)
    (next : RootOutput) (pending : RawCtxInterpretedSend.Kdf Slot Context)
    (selected : (RawCtxSelectedMessageKdf.step prior target nonce next pending.request).2 = .hidden chosen) :
    (RawCtxInterpretedSend.ready pending (RawCtxSelectedMessageKdf.step prior target nonce next pending.request)).advanced =
      { pending.entry with control := pending.committed_control, send_chain := concreteChain next } := by
  have same := (step_selected prior target nonce chosen next pending.request).mp selected
  simp only [RawCtxInterpretedSend.ready, RawCtxSelectedMessageKdf.step, if_pos same.1]

/-- Address equality at the fixed production label means actual chain-byte equality; this is representation injectivity, not HKDF injectivity. -/
theorem address_injective : Function.Injective RawCtxSelectedPendingCut.requestAddress := by
  intro left right same
  apply BeaconcryptCore.Refinement.RepresentationBridge.absChain_injective
  exact congrArg PqxdhJointKdf.JointKdfAddress.input same

/-- Selected sending means the actual old chain equals the selected input bytes, not merely that a material label happened to match. -/
theorem selected_chain {Context : Type} (prior : Prior) (target : RootOutput) (nonce chosen : NonceOutput)
    (next : RootOutput) (entry : RefinedRatchet RatchetChain RatchetChain Slot) (context : Context)
    (pending : RawCtxInterpretedSend.Kdf Slot Context)
    (admitted : RawCtxInterpretedSend.normalBegin entry context = .requested pending)
    (selected : (RawCtxInterpretedSend.ready pending
      (RawCtxSelectedMessageKdf.step prior target nonce next pending.request)).material = .hidden chosen) :
    entry.send_chain = concreteChain target := by
  exact address_injective ((selected_send prior target nonce chosen next entry context pending admitted).mp selected).1

/-- Retained-parent routing advances selected sends identically, without discarding the predecessor-collision branch. -/
theorem selected_later_advance {Context : Type} (prior : Prior) (parent : Entry) (target : RootOutput)
    (nonce chosen : NonceOutput) (next : RootOutput) (pending : RawCtxInterpretedSend.Kdf Slot Context)
    (selected : (later prior parent target nonce next pending.request).2 = .hidden chosen) :
    (RawCtxInterpretedSend.ready pending (later prior parent target nonce next pending.request)).advanced =
      { pending.entry with control := pending.committed_control, send_chain := concreteChain next } := by
  have same := (later_selected prior parent target nonce chosen next pending.request).mp selected
  simp only [RawCtxInterpretedSend.ready, later, if_neg same.1, RawCtxSelectedMessageKdf.step, if_pos same.2.1]

/-- Every selected seal attempt publishes send advancement even when its exact optional writer reply is None. -/
theorem selected_finish {Context Output : Type} (prior : Prior) (target : RootOutput)
    (nonce chosen : NonceOutput) (next : RootOutput) (pending : RawCtxInterpretedSend.Kdf Slot Context)
    (selected : (RawCtxSelectedMessageKdf.step prior target nonce next pending.request).2 = .hidden chosen)
    (reply : core.option.Option Output) :
    RawCtxInterpretedSend.finish
      (RawCtxInterpretedSend.ready pending (RawCtxSelectedMessageKdf.step prior target nonce next pending.request)) reply =
      ok ({ pending.entry with control := pending.committed_control, send_chain := concreteChain next }, reply) := by
  rw [RawCtxInterpretedSend.finish_exact, selected_advance prior target nonce chosen next pending selected]

/-- Later selected sends likewise finish with the new chain for every native optional result, including failure. -/
theorem selected_later_finish {Context Output : Type} (prior : Prior) (parent : Entry) (target : RootOutput)
    (nonce chosen : NonceOutput) (next : RootOutput) (pending : RawCtxInterpretedSend.Kdf Slot Context)
    (selected : (later prior parent target nonce next pending.request).2 = .hidden chosen)
    (reply : core.option.Option Output) :
    RawCtxInterpretedSend.finish
      (RawCtxInterpretedSend.ready pending (later prior parent target nonce next pending.request)) reply =
      ok ({ pending.entry with control := pending.committed_control, send_chain := concreteChain next }, reply) := by
  rw [RawCtxInterpretedSend.finish_exact, selected_later_advance prior parent target nonce chosen next pending selected]

/-- Two selected send occurrences, including occurrences owned by different roles, have equal actual old sending chains. This classifies the source bad event without asserting that it is negligible. -/
theorem repeated_send {Left Right : Type} (leftPrior rightPrior : Prior) (target : RootOutput)
    (nonce leftNonce rightNonce : NonceOutput) (next : RootOutput)
    (left : RefinedRatchet RatchetChain RatchetChain Slot) (leftContext : Left)
    (right : RefinedRatchet RatchetChain RatchetChain Slot) (rightContext : Right)
    (leftPending : RawCtxInterpretedSend.Kdf Slot Left) (rightPending : RawCtxInterpretedSend.Kdf Slot Right)
    (leftAdmitted : RawCtxInterpretedSend.normalBegin left leftContext = .requested leftPending)
    (rightAdmitted : RawCtxInterpretedSend.normalBegin right rightContext = .requested rightPending)
    (leftSelected : (RawCtxInterpretedSend.ready leftPending
      (RawCtxSelectedMessageKdf.step leftPrior target nonce next leftPending.request)).material = .hidden leftNonce)
    (rightSelected : (RawCtxInterpretedSend.ready rightPending
      (RawCtxSelectedMessageKdf.step rightPrior target nonce next rightPending.request)).material = .hidden rightNonce) :
    left.send_chain = right.send_chain ∧ leftNonce = rightNonce := by
  exact ⟨(selected_chain leftPrior target nonce leftNonce next left leftContext leftPending leftAdmitted leftSelected).trans
    (selected_chain rightPrior target nonce rightNonce next right rightContext rightPending rightAdmitted rightSelected).symm,
    ((selected_send leftPrior target nonce leftNonce next left leftContext leftPending leftAdmitted).mp leftSelected).2.trans
      ((selected_send rightPrior target nonce rightNonce next right rightContext rightPending rightAdmitted).mp rightSelected).2.symm⟩

/-- The immediately following send of this advanced kernel can select the same response only on an actual next-chain/input self-loop. This includes a previous failed writer. -/
theorem consecutive_repeat {First Second : Type} (firstPrior secondPrior : Prior) (target : RootOutput)
    (nonce firstNonce secondNonce : NonceOutput) (next : RootOutput)
    (firstPending : RawCtxInterpretedSend.Kdf Slot First) (secondContext : Second)
    (secondPending : RawCtxInterpretedSend.Kdf Slot Second)
    (firstSelected : (RawCtxSelectedMessageKdf.step firstPrior target nonce next firstPending.request).2 = .hidden firstNonce)
    (secondAdmitted : RawCtxInterpretedSend.normalBegin
      (RawCtxInterpretedSend.ready firstPending
        (RawCtxSelectedMessageKdf.step firstPrior target nonce next firstPending.request)).advanced secondContext = .requested secondPending)
    (secondSelected : (RawCtxInterpretedSend.ready secondPending
      (RawCtxSelectedMessageKdf.step secondPrior target nonce next secondPending.request)).material = .hidden secondNonce) :
    next = target := by
  have chain := selected_chain secondPrior target nonce secondNonce next _ secondContext secondPending secondAdmitted secondSelected
  rw [selected_advance firstPrior target nonce firstNonce next firstPending firstSelected] at chain
  have bytes := congrArg RawCtxSelectedQueryTrace.rootVector chain
  simpa only [RawCtxSelectedQueryTrace.rootVector_concrete] using bytes

end BeaconcryptCore.Computational.RawCtxSelectedSendAddress

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedSendAddress.step_selected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedSendAddress.step_selected

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedSendAddress.later_selected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedSendAddress.later_selected

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedSendAddress.admitted_request' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedSendAddress.admitted_request

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedSendAddress.admitted_address' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedSendAddress.admitted_address

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedSendAddress.selected_send' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedSendAddress.selected_send

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedSendAddress.selected_later_send' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedSendAddress.selected_later_send

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedSendAddress.selected_advance' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedSendAddress.selected_advance

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedSendAddress.address_injective' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedSendAddress.address_injective

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedSendAddress.selected_chain' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedSendAddress.selected_chain

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedSendAddress.selected_later_advance' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedSendAddress.selected_later_advance

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedSendAddress.selected_finish' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedSendAddress.selected_finish

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedSendAddress.selected_later_finish' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedSendAddress.selected_later_finish

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedSendAddress.repeated_send' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedSendAddress.repeated_send

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedSendAddress.consecutive_repeat' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedSendAddress.consecutive_repeat
