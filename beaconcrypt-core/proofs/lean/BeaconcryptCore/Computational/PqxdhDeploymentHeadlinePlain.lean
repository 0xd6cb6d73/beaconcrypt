-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePin
import BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePlainUnique
import BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePlainSend

/-!
# AG lift R2: the mode-O plaintext on the common deployment experiment (CE-12 P4 step 3, design-v2 section 7.6)

The mode-O plaintext rows of design-v2 section 7.6 (ProVerif L2-origin, b2s-C2 and b2s-C4 for b2s; S2b-origin, s2b-C1 and s2b-C4 for s2b: the record a party accepted carries the plaintext that its peer sent), from symbolic-only to computational, through the record-level agreement fact of P2b (`PqxdhDeploymentHeadlineAgree`):

- `PlainAt direction g`: an accepted raw receive in the direction on a handle designating `g = (i, k)`, with decoded frame `f` and returned plaintext `m`, such that the handle's CE counterpart (`PqxdhDeploymentHeadlineEvents.cpart`: owner `k` for a Server peer, the target's Server peer for an owner) produced a record of frame `f` with a plaintext other than `m`. Productions are read on the observation's ledger (`PqxdhDeploymentHeadlinePlainSend.Sent`): an explicit send with its query plaintext, an admitted test with the message of the ledger's hidden bit, an admitted fresh message. `PlainFailure`, `plainEvent`, the claim `plainClaim` (the receiving handle of the first failing entry) and `plain_named`. The reading "the returned plaintext differs from every counterpart production of the frame, and one exists" is `PlainEveryAt` (`PlainEveryFailure`, `plainEveryEvent`), contained in it (`plainEvery_plain`).
- The ideal-world facts `PlainFacts` (`ctxRun_plainFacts`, `idealAuth_plainFacts`): every production of the final ledger has a seal with its plaintext (`PqxdhDeploymentHeadlinePlainSend.ctxRun_sentPlain`), and the seal dictionaries are aligned and hold one seal per label (`PqxdhDeploymentHeadlinePlainUnique`).
- The containment (`plain_core`; `plain_agree_b2s` with `dec_g ∧ ISs_g`, `plain_agree_s2b` with `dec_g ∧ IS_g`): such an outcome is an AG failure (`PqxdhDeploymentHeadlineAgree.AgreeFailure`). The slot restrictions make the CE counterpart the only counterpart of the receiving handle's slot. If it produced the frame from a seal with the received plaintext (the AG fact), that seal and the seal behind the production with the other plaintext both match the frame at labels of the counterpart's slot and direction, so they are one seal and the two plaintexts are equal. The event has no AD field (handle ADs are not observable); the AD's identity pair is the designation's identity row and, for b2s, the Server-pin row of `PqxdhDeploymentHeadlinePin`.
- `idealAuth_plain_b2s_zero`, `idealAuth_plain_s2b_zero`: in `idealAuth` with the ideal environment of the target the event has probability zero (`PqxdhDeploymentHeadlineAgree.agreement_statement`).
- `ce_plain_b2s_target`, `ce_plain_b2s`: at most the sum over the targets of `kemLoss + slotLoss + authLoss_g(dec_g ∧ ISs_g)` (`PqxdhDeploymentHeadlineChain.chain_server`, `PqxdhDeploymentHeadlineChain.auth_le`); `ce_plain_s2b_target`, `ce_plain_s2b`: at most the sum of `kemLoss + slotLoss + β_g + authLoss_g(dec_g ∧ IS_g)` (`PqxdhDeploymentHeadlineAnomaly.chain_beta`, `auth_le`); each term with coefficient one and no publication term. `ce_plain_every_b2s`, `ce_plain_every_s2b`: the same bounds for the every-production reading.
- CE-OR with the plaintext field: `OriginPlainFailure direction` (the frozen origin failure or the plaintext failure), `originPlainEvent`, `originPlainClaim`, `originPlain_named`, `originPlain_contain_b2s`, `originPlain_contain_s2b`, `idealAuth_originPlain_b2s_le`, `idealAuth_originPlain_s2b_le` and `ce_or_plain_b2s(_target)`, `ce_or_plain_s2b(_target)`: the bounds of the frozen `PqxdhDeploymentHeadlineOrigin.ce_or_b2s` and `ce_or_s2b` with the plaintext field computational.
- CE-OR b2s with every computational field: `OriginFieldsFailure` (the frozen b2s origin failure, the Server pin failure `PqxdhDeploymentHeadlinePin.PinFailure` or the b2s plaintext failure), `originFieldsEvent`, `originFieldsClaim`, `originFields_named`, `originFields_contain`, `idealAuth_originFields_le` and `ce_or_fields_b2s(_target)`: the bound of the frozen `ce_or_b2s`.

Premises: those of the frozen `ce_or_b2s` and `ce_or_s2b` (`FunctionalDecapsulation`, `Phase1ReadBack`, `Phase2ReadBack`, `SourceFullCorrect`, `KemBound`, the initializer's query bound, `FrameReadBack` and `budget.Respects`); the AEAD forgery fallback is a parameter of the integrity loss. Unlike the pin event of step 2, the plaintext events need `FrameReadBack` themselves: a production's frame is read back from its returned ciphertext. No new assumption or contract. The statements hold in both observation modes; the rows are the mode-O ones (the transcript keeps mode-O replies in both modes). Not claimed here: the root, plaintext-linked UKS (no CE event, design-v2 section 7.6) and any statement in the later-quantum mode. No `PqxdhBoundary*` module is imported.
-/

open OracleComp OracleSpec ENNReal

set_option autoImplicit false

namespace BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePlain
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhDeploymentInterface (Handle Entry Budget FreshBounds Mode ModeSpec)
open PqxdhDeploymentKemTransfer (Observed happens designated)
open PqxdhDeploymentIdealParams (Target)
open PqxdhDeploymentTranscript (designateIn)
open PqxdhDeploymentHeadlineEvents (Direction cpart firstHandle receivedHandle firstHandle_some firstHandle_isSome)
open PqxdhRecordLiftIdeal (View ctxView idealAuth handleSlot publicationTerm receivingHandle Counterpart)
open PqxdhDeploymentIdealHandoff (decisionOn viewObserved)
open PqxdhDeploymentHeadlineChain (ServerSlots slotted serverSlotted kemLoss slotLoss authLoss)
open PqxdhDeploymentHeadlineAnomaly (beta)
open PqxdhDeploymentHeadlineAgree (AgreeFailure agreeEvent)
open PqxdhDeploymentHeadlinePlainSend (Sent PublishedPlain)
open PqxdhDeploymentHeadlinePin (chance_mono_support chance_or_le decision_transfer)
open PqxdhServerAuthSourceCosts (KemCaps KemBound)

variable {Reader Response X : Type}

/-! ### The mode-O plaintext event -/

section Event
variable (crypto : Pqxdh.Crypto) (codec : Codec Reader Response) (serverKid : Aeneas.Std.U64) (budget : Budget)
  (route : RawCtxServerRouting.SenderDecoder)

/-- `PlainAt direction g`: the entry is an accepted raw receive in the direction on a handle designated `g`, with a decoded frame, and the CE counterpart of the handle produced a record of that frame (`PqxdhDeploymentHeadlinePlainSend.Sent` on the final ledger) with a plaintext other than the received one. -/
def PlainAt (direction : Direction) (g : Fin budget.accept × Fin budget.capacity)
    (ledger : PqxdhDeploymentSecrecy.Ledger) (entry : Entry) : Prop :=
  ∃ receiver raw decrypted handle frame, entry.received = some (receiver, raw, .Some decrypted) ∧
    receivingHandle route receiver raw = some handle ∧ direction.Receives handle ∧
    designateIn crypto codec serverKid budget ledger.transcript handle = some g ∧ codec.frameRead raw = some frame ∧
    ∃ counterpart encrypted plaintext, cpart budget g ledger.transcript handle = some counterpart ∧
      Sent ledger counterpart encrypted plaintext ∧ codec.frameRead encrypted.ciphertext = some frame ∧
      plaintext ≠ decrypted.plaintext

/-- The entry fails the plaintext field in the direction for some target. -/
def PlainFailsAt (direction : Direction) (ledger : PqxdhDeploymentSecrecy.Ledger) (entry : Entry) : Prop :=
  ∃ g, PlainAt crypto codec serverKid budget route direction g ledger entry

/-- The plaintext failure in a direction (design-v2 section 7.6, mode-O plaintext): some entry of the final transcript fails the plaintext field. -/
def PlainFailure (direction : Direction) (observed : Observed X) : Prop :=
  ∃ entry ∈ observed.2.1.transcript, PlainFailsAt crypto codec serverKid budget route direction observed.2.1 entry

open Classical in
/-- The plaintext failure as a Boolean of the observation. -/
noncomputable def plainEvent (direction : Direction) (observed : Observed X) : Bool :=
  decide (PlainFailure crypto codec serverKid budget route direction observed)

/-- The claim of the plaintext failure: the receiving handle of the first transcript entry that fails it. -/
noncomputable def plainClaim (direction : Direction) (observed : Observed X) : Option Handle :=
  firstHandle (fun _ entry => PlainFailsAt crypto codec serverKid budget route direction observed.2.1 entry)
    (receivedHandle route) observed.2.1.transcript

/-- A plaintext failure names a designated claim: the first failing entry's receiving handle designates a target. -/
theorem plain_named (direction : Direction) (observed : Observed X)
    (failed : plainEvent crypto codec serverKid budget route direction observed = true) :
    (PqxdhDeploymentKemTransfer.target crypto codec serverKid budget
      (plainClaim crypto codec serverKid budget route direction) observed).isSome := by
  classical
  unfold plainEvent at failed
  obtain ⟨entry, member, g, witness⟩ := of_decide_eq_true failed
  obtain ⟨receiver, raw, decrypted, handle, frame, received, routed, _, _, _, _⟩ := id witness
  obtain ⟨before, after, split⟩ := List.append_of_mem member
  have named : (receivedHandle route entry).isSome := by
    simp [receivedHandle, received, routed]
  obtain ⟨claimed, found⟩ := Option.isSome_iff_exists.mp (firstHandle_isSome
    (fun _ entry => PlainFailsAt crypto codec serverKid budget route direction observed.2.1 entry)
    (receivedHandle route) _ before entry after split ⟨g, witness⟩ named)
  obtain ⟨before', entry', after', split', ⟨g', receiver', raw', decrypted', handle', frame', received', routed', _,
    designated', _, _⟩, handled⟩ := firstHandle_some _ _ _ claimed found
  simp only [receivedHandle, received', Option.bind_some, routed', Option.some.injEq] at handled
  subst handled
  unfold PqxdhDeploymentKemTransfer.target plainClaim
  rw [found]
  simp [designated']

end Event

/-! ### CE-OR with the plaintext field -/

section OriginPlain
variable (crypto : Pqxdh.Crypto) (codec : Codec Reader Response) (serverKid : Aeneas.Std.U64) (budget : Budget)
  (route : RawCtxServerRouting.SenderDecoder)

/-- The origin failure with the plaintext field in a direction: the frozen origin failure (`PqxdhDeploymentHeadlineEvents.OriginFailure`: an accepted raw receive on a designated handle whose decoded frame its CE counterpart did not publish before) or the plaintext failure. -/
def OriginPlainFailure (direction : Direction) (observed : Observed X) : Prop :=
  PqxdhDeploymentHeadlineEvents.OriginFailure crypto codec serverKid budget route direction observed ∨
    PlainFailure crypto codec serverKid budget route direction observed

open Classical in
/-- The origin failure with the plaintext field as a Boolean of the observation. -/
noncomputable def originPlainEvent (direction : Direction) (observed : Observed X) : Bool :=
  decide (OriginPlainFailure crypto codec serverKid budget route direction observed)

open Classical in
/-- The claim of the origin failure with the plaintext field: the frozen origin claim when the origin fails, else the plaintext claim. -/
noncomputable def originPlainClaim (direction : Direction) (observed : Observed X) : Option Handle :=
  if PqxdhDeploymentHeadlineEvents.OriginFailure crypto codec serverKid budget route direction observed then
    PqxdhDeploymentHeadlineEvents.orClaim crypto codec serverKid budget route direction observed
  else plainClaim crypto codec serverKid budget route direction observed

/-- The origin failure with the plaintext field names a designated claim. -/
theorem originPlain_named (direction : Direction) (observed : Observed X)
    (failed : originPlainEvent crypto codec serverKid budget route direction observed = true) :
    (PqxdhDeploymentKemTransfer.target crypto codec serverKid budget
      (originPlainClaim crypto codec serverKid budget route direction) observed).isSome := by
  classical
  simp only [originPlainEvent, decide_eq_true_eq] at failed
  by_cases origin : PqxdhDeploymentHeadlineEvents.OriginFailure crypto codec serverKid budget route direction observed
  · have named := PqxdhDeploymentHeadlineEvents.origin_named crypto codec serverKid budget route direction observed
      (by simp only [PqxdhDeploymentHeadlineEvents.originEvent, decide_eq_true_eq]; exact origin)
    unfold PqxdhDeploymentKemTransfer.target at named ⊢
    simp only [originPlainClaim, origin, ↓reduceIte]
    exact named
  · have named := plain_named crypto codec serverKid budget route direction observed
      (by simp only [plainEvent, decide_eq_true_eq]; exact failed.resolve_left origin)
    unfold PqxdhDeploymentKemTransfer.target at named ⊢
    simp only [originPlainClaim, origin, ↓reduceIte]
    exact named

end OriginPlain

/-! ### The reading with every production, and CE-OR b2s with all computational fields -/

section Every
variable (crypto : Pqxdh.Crypto) (codec : Codec Reader Response) (serverKid : Aeneas.Std.U64) (budget : Budget)
  (route : RawCtxServerRouting.SenderDecoder)

/-- `PlainEveryAt direction g`: the entry is an accepted raw receive in the direction on a handle designated `g`, with a decoded frame, the CE counterpart of the handle produced a record of that frame, and every production of that frame by the counterpart carries a plaintext other than the received one. -/
def PlainEveryAt (direction : Direction) (g : Fin budget.accept × Fin budget.capacity)
    (ledger : PqxdhDeploymentSecrecy.Ledger) (entry : Entry) : Prop :=
  ∃ receiver raw decrypted handle frame, entry.received = some (receiver, raw, .Some decrypted) ∧
    receivingHandle route receiver raw = some handle ∧ direction.Receives handle ∧
    designateIn crypto codec serverKid budget ledger.transcript handle = some g ∧ codec.frameRead raw = some frame ∧
    ∃ counterpart, cpart budget g ledger.transcript handle = some counterpart ∧
      (∃ encrypted plaintext, Sent ledger counterpart encrypted plaintext ∧
        codec.frameRead encrypted.ciphertext = some frame) ∧
      ∀ encrypted plaintext, Sent ledger counterpart encrypted plaintext →
        codec.frameRead encrypted.ciphertext = some frame → plaintext ≠ decrypted.plaintext

/-- The plaintext failure with every production: some entry of the final transcript fails `PlainEveryAt` for some target. -/
def PlainEveryFailure (direction : Direction) (observed : Observed X) : Prop :=
  ∃ entry ∈ observed.2.1.transcript, ∃ g, PlainEveryAt crypto codec serverKid budget route direction g observed.2.1
      entry

open Classical in
/-- The plaintext failure with every production as a Boolean of the observation. -/
noncomputable def plainEveryEvent (direction : Direction) (observed : Observed X) : Bool :=
  decide (PlainEveryFailure crypto codec serverKid budget route direction observed)

/-- The plaintext failure with every production is a plaintext failure: the production that exists carries another plaintext. -/
theorem plainEvery_plain (direction : Direction) (observed : Observed X)
    (failed : plainEveryEvent crypto codec serverKid budget route direction observed = true) :
    plainEvent crypto codec serverKid budget route direction observed = true := by
  classical
  simp only [plainEveryEvent, decide_eq_true_eq] at failed
  obtain ⟨entry, member, g, receiver, raw, decrypted, handle, frame, received, routed, receives, designated, framed,
    counterpart, cparted, ⟨encrypted, plaintext, sent, sentFramed⟩, every⟩ := failed
  simp only [plainEvent, decide_eq_true_eq]
  exact ⟨entry, member, g, receiver, raw, decrypted, handle, frame, received, routed, receives, designated, framed,
    counterpart, encrypted, plaintext, cparted, sent, sentFramed, every encrypted plaintext sent sentFramed⟩

/-- The b2s origin failure with every computational field of design-v2 section 7.6: the frozen b2s origin failure, the Server pin failure (`PqxdhDeploymentHeadlinePin.PinFailure`) or the b2s plaintext failure. -/
def OriginFieldsFailure (observed : Observed X) : Prop :=
  PqxdhDeploymentHeadlineEvents.OriginFailure crypto codec serverKid budget route .b2s observed ∨
    PqxdhDeploymentHeadlinePin.PinFailure crypto codec serverKid budget route observed ∨
    PlainFailure crypto codec serverKid budget route .b2s observed

open Classical in
/-- The b2s origin failure with every computational field as a Boolean of the observation. -/
noncomputable def originFieldsEvent (observed : Observed X) : Bool :=
  decide (OriginFieldsFailure crypto codec serverKid budget route observed)

open Classical in
/-- The claim of the b2s origin failure with every computational field: the frozen origin claim when the origin fails, else the pin claim when the pin fails, else the plaintext claim. -/
noncomputable def originFieldsClaim (observed : Observed X) : Option Handle :=
  if PqxdhDeploymentHeadlineEvents.OriginFailure crypto codec serverKid budget route .b2s observed then
    PqxdhDeploymentHeadlineEvents.orClaim crypto codec serverKid budget route .b2s observed
  else if PqxdhDeploymentHeadlinePin.PinFailure crypto codec serverKid budget route observed then
    PqxdhDeploymentHeadlinePin.pinClaim crypto codec serverKid budget route observed
  else plainClaim crypto codec serverKid budget route .b2s observed

/-- The b2s origin failure with every computational field names a designated claim. -/
theorem originFields_named (observed : Observed X)
    (failed : originFieldsEvent crypto codec serverKid budget route observed = true) :
    (PqxdhDeploymentKemTransfer.target crypto codec serverKid budget
      (originFieldsClaim crypto codec serverKid budget route) observed).isSome := by
  classical
  simp only [originFieldsEvent, decide_eq_true_eq] at failed
  by_cases origin : PqxdhDeploymentHeadlineEvents.OriginFailure crypto codec serverKid budget route .b2s observed
  · have named := PqxdhDeploymentHeadlineEvents.origin_named crypto codec serverKid budget route .b2s observed
      (by simp only [PqxdhDeploymentHeadlineEvents.originEvent, decide_eq_true_eq]; exact origin)
    unfold PqxdhDeploymentKemTransfer.target at named ⊢
    simp only [originFieldsClaim, origin, ↓reduceIte]
    exact named
  · by_cases pin : PqxdhDeploymentHeadlinePin.PinFailure crypto codec serverKid budget route observed
    · have named := PqxdhDeploymentHeadlinePin.pin_named crypto codec serverKid budget route observed
        (by simp only [PqxdhDeploymentHeadlinePin.pinEvent, decide_eq_true_eq]; exact pin)
      unfold PqxdhDeploymentKemTransfer.target at named ⊢
      simp only [originFieldsClaim, origin, pin, ↓reduceIte]
      exact named
    · have named := plain_named crypto codec serverKid budget route .b2s observed
        (by simp only [plainEvent, decide_eq_true_eq]; exact (failed.resolve_left origin).resolve_left pin)
      unfold PqxdhDeploymentKemTransfer.target at named ⊢
      simp only [originFieldsClaim, origin, pin, ↓reduceIte]
      exact named

end Every

/-! ### The ideal-world facts and the containment -/

section Contain
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK : Type}

/-- The three ideal-world facts of the plaintext lift on a CTX-world outcome: every CE production of the final ledger has a seal with its plaintext (`PqxdhDeploymentHeadlinePlainSend.ctxRun_sentPlain`), the seal dictionaries are aligned (`PqxdhDeploymentHeadlinePlainUnique.ctxRun_aligned`) and hold one seal per label (`PqxdhDeploymentHeadlinePlainUnique.ctxRun_unique`). -/
def PlainFacts {E : Type} (codec : Codec Reader Response)
    (result : PqxdhRecordLiftIdeal.Client 2 E X × PqxdhRecordLiftIdeal.CtxPrivate 2) : Prop :=
  (∀ value ∈ result.1.1, ∀ handle encrypted plaintext, Sent value.2.1.2 handle encrypted plaintext →
      PublishedPlain codec result.1.2 result.2 handle encrypted plaintext) ∧
    PqxdhDeploymentHeadlinePlainUnique.Aligned result.2 ∧
    ∀ label, ∀ first ∈ (result.2.keys label).1.successfulSeals, ∀ second ∈ (result.2.keys label).1.successfulSeals,
      first = second

/-- The plaintext facts hold on every supported outcome of every ideal CTX world without plaintext replacement. -/
theorem ctxRun_plainFacts {E : Type} (modes : PqxdhRecordLiftWorldCompiler.Label 2 → PqxdhRecordLiftIdeal.KeyMode)
    (ideal : ∀ label, modes label ≠ .real) (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (readback : PqxdhServerAuthNegativeControl.FrameReadBack codec)
    (env : PqxdhRecordLiftInterface.Environment 2 E) (serverKid : Aeneas.Std.U64) (bounds : FreshBounds)
    (mode : Mode) (adversary : OracleComp (ModeSpec mode) X)
    (result : PqxdhRecordLiftIdeal.Client 2 E X × PqxdhRecordLiftIdeal.CtxPrivate 2)
    (supported : result ∈ support (PqxdhRecordLiftIdeal.ctxRun modes id setup codec route env serverKid bounds mode
      adversary)) :
    PlainFacts codec result :=
  ⟨fun value member handle encrypted plaintext sent => PqxdhDeploymentHeadlinePlainSend.ctxRun_sentPlain modes ideal id
      setup codec route readback env serverKid bounds mode adversary result supported value member handle encrypted
      plaintext sent,
    PqxdhDeploymentHeadlinePlainUnique.ctxRun_aligned modes ideal id setup codec route env serverKid bounds mode
        adversary
      result supported,
    fun label first firstMember second secondMember => PqxdhDeploymentHeadlinePlainUnique.ctxRun_unique modes ideal id
      setup codec route env serverKid bounds mode adversary result supported label first second firstMember
      secondMember⟩

/-- The plaintext facts hold on every supported outcome of `idealAuth`. -/
theorem idealAuth_plainFacts {E : Type} (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (readback : PqxdhServerAuthNegativeControl.FrameReadBack codec)
    (env : PqxdhRecordLiftInterface.Environment 2 E) (serverKid : Aeneas.Std.U64) (bounds : FreshBounds)
    (mode : Mode) (adversary : OracleComp (ModeSpec mode) X)
    (result : PqxdhRecordLiftIdeal.Client 2 E X × PqxdhRecordLiftIdeal.CtxPrivate 2)
    (supported : result ∈ support (idealAuth setup codec route env serverKid bounds mode adversary)) :
    PlainFacts codec result :=
  ctxRun_plainFacts (fun _ => .replay) (by intro label; decide) setup codec route readback env serverKid bounds mode
    adversary result supported

/-- A counterpart of a handle holds the handle's slot. -/
theorem counterpart_slot (slots : Handle → Option (PqxdhRecordLiftInterface.Slot 2))
    (slot : PqxdhRecordLiftInterface.Slot 2) (handle other : Handle) (counter : Counterpart slots slot handle other) :
    slots other = some slot := by
  cases handle <;> cases other <;> first | exact counter | exact False.elim counter

/-- The core containment: on an outcome with the plaintext facts, an accepted raw receive on a handle holding a hidden slot, whose only counterpart produced the decoded frame with another plaintext, is an AG failure. The AG seal of the receive and the seal behind the production are at labels of the counterpart's slot and direction and match one frame, so they are one seal (`PqxdhDeploymentHeadlinePlainUnique.frame_seal_unique`), and the received plaintext is the produced one. -/
theorem plain_core {E : Type} (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (result : PqxdhRecordLiftIdeal.Client 2 E X × PqxdhRecordLiftIdeal.CtxPrivate 2) (facts : PlainFacts codec result)
    (value : PqxdhRegistrationJointServerBirth.ClientCreated Unit × (X × PqxdhDeploymentSecrecy.Ledger) × E)
    (valueMember : value ∈ result.1.1) (entry : Entry) (entryMember : entry ∈ value.2.1.2.transcript)
    (receiver : PqxdhDeploymentInterface.Receiver) (raw : Pqxdh.Bytes) (decrypted : RawCtxWholeOwner.Decrypted)
    (handle : Handle) (slot : PqxdhRecordLiftInterface.Slot 2) (frame : PqxdhDeploymentNative.Frame)
    (received : entry.received = some (receiver, raw, .Some decrypted))
    (routed : receivingHandle route receiver raw = some handle) (hidden : handleSlot result.1.2 handle = some slot)
    (decoded : codec.frameRead raw = some frame) (counterpart : Handle)
    (unique : ∀ other, Counterpart (handleSlot result.1.2) slot handle other → other = counterpart)
    (encrypted : RawCtxSourceSend.Encrypted) (plaintext : Pqxdh.Bytes)
    (sent : Sent value.2.1.2 counterpart encrypted plaintext)
    (framed : codec.frameRead encrypted.ciphertext = some frame) (differ : plaintext ≠ decrypted.plaintext) :
    AgreeFailure codec route result := by
  refine ⟨value, valueMember, entry, entryMember, receiver, raw, decrypted, handle, slot, frame, received, routed,
    hidden, decoded, ?_⟩
  rintro ⟨other, ad, counter, ⟨label, sealed, owns, member, matched, _, _, plainEq⟩, _, _⟩
  have otherEq := unique other counter
  subst otherEq
  rcases facts.1 value valueMember other encrypted plaintext sent with known | ⟨label', owns', frame', framed', sealed',
    member', matched', plainEq'⟩
  · have absent := PqxdhRecordFactsOriginAccepted.known_no_slot result.1.2 other known
    have present := counterpart_slot (handleSlot result.1.2) slot handle other counter
    rw [absent] at present
    cases present
  · rw [framed] at framed'
    cases framed'
    have same := PqxdhDeploymentHeadlinePlainUnique.frame_seal_unique result.2 facts.2.1 facts.2.2 frame label label'
      (Option.some.inj (owns.1.symm.trans owns'.1)) (owns.2.trans owns'.2.symm) sealed sealed' member member'
      matched matched'
    subst same
    exact differ (plainEq'.symm.trans plainEq)

/-- The view of a CTX-world outcome with a result is the view of one of the outcome's values. -/
theorem view_value {E : Type} (result : PqxdhRecordLiftIdeal.Client 2 E X × PqxdhRecordLiftIdeal.CtxPrivate 2)
    (view : X × PqxdhDeploymentSecrecy.Ledger × E) (found : (ctxView result).result = some view) :
    ∃ value ∈ result.1.1, view = (value.2.1.1, value.2.1.2, value.2.2) := by
  rcases existing : result.1.1 with _ | value
  · simp [ctxView, PqxdhRecordLiftIdeal.viewOf, existing] at found
  · simp only [ctxView, PqxdhRecordLiftIdeal.viewOf, existing, Option.map_some, Option.some.injEq] at found
    exact ⟨value, rfl, found.symm⟩

variable (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (budget : Budget)
  (route : RawCtxServerRouting.SenderDecoder)

/-- **The b2s containment**: on every CTX-world outcome with the plaintext facts, `dec_g ∧ ISs_g` of the b2s plaintext failure implies AG's failure event. The receiving Server peer designates `g`, so it holds slot 0 (Server converse), and a counterpart of it is an owner holding slot 0, hence owner `k`, its CE counterpart (Beacon restriction). -/
theorem plain_agree_b2s {E : Type} (g : Fin budget.accept × Fin budget.capacity)
    (result : PqxdhRecordLiftIdeal.Client 2 E X × PqxdhRecordLiftIdeal.CtxPrivate 2) (facts : PlainFacts codec result)
    (held : serverSlotted setup codec budget (plainEvent setup.source.crypto codec setup.serverKeyId budget route .b2s)
      (plainClaim setup.source.crypto codec setup.serverKeyId budget route .b2s) g (ctxView result) = true) :
    AgreeFailure codec route result := by
  classical
  unfold serverSlotted at held
  obtain ⟨decided, server⟩ := of_decide_eq_true held
  obtain ⟨view, found, _, handle, claimed, designated⟩ :=
    PqxdhDeploymentHeadlineContain.decision_unpack setup codec budget _ _ g (ctxView result) decided
  have slots := server view found
  obtain ⟨value, valueMember, rfl⟩ := view_value result view found
  obtain ⟨before, entry, after, split, ⟨g', receiver, raw, decrypted, handle', frame, received, routed, receives,
    designated', framed, counterpart, encrypted, plaintext, cparted, sent, sentFramed, differ⟩, handled⟩ :=
    firstHandle_some _ _ _ handle claimed
  simp only [receivedHandle, received, Option.bind_some, routed, Option.some.injEq] at handled
  subst handled
  rw [designated] at designated'
  cases designated'
  have entryMember : entry ∈ value.2.1.2.transcript := by
    rw [split]
    simp
  cases handle' with
  | owner _ => exact absurd receives (by simp [Direction.Receives])
  | peer keyId =>
    obtain ⟨zero, _⟩ := PqxdhDeploymentHeadlineContain.designation_peer setup.source.crypto codec setup.serverKeyId
      budget g (ctxView result).slots value.2.1.2.transcript keyId slots designated
    simp only [cpart, Option.some.injEq] at cparted
    subst cparted
    refine plain_core codec route result facts value valueMember entry entryMember receiver raw decrypted (.peer
        keyId) 0
      frame received routed zero framed _ (fun other counter => ?_) encrypted plaintext sent sentFramed differ
    obtain ⟨owner, rfl, ownerSlot⟩ := PqxdhDeploymentHeadlineAgree.counterpart_peer _ 0 keyId other counter
    have ownerEq : owner = g.2.val := slots.2.1 owner 0 ownerSlot
    rw [ownerEq]

/-- **The s2b containment**: on every CTX-world outcome with the plaintext facts, `dec_g ∧ IS_g` of the s2b plaintext failure implies AG's failure event. The receiving owner designates `g`, so it holds a slot (Beacon converse), and a counterpart of it is a Server peer holding that slot, hence the target's peer, its CE counterpart (Server restriction). -/
theorem plain_agree_s2b {E : Type} (g : Fin budget.accept × Fin budget.capacity)
    (result : PqxdhRecordLiftIdeal.Client 2 E X × PqxdhRecordLiftIdeal.CtxPrivate 2) (facts : PlainFacts codec result)
    (held : slotted setup codec budget (plainEvent setup.source.crypto codec setup.serverKeyId budget route .s2b)
      (plainClaim setup.source.crypto codec setup.serverKeyId budget route .s2b) g (ctxView result) = true) :
    AgreeFailure codec route result := by
  classical
  unfold slotted at held
  obtain ⟨decided, ideal⟩ := of_decide_eq_true held
  obtain ⟨view, found, _, handle, claimed, designated⟩ :=
    PqxdhDeploymentHeadlineContain.decision_unpack setup codec budget _ _ g (ctxView result) decided
  have slots := ideal view found
  obtain ⟨value, valueMember, rfl⟩ := view_value result view found
  obtain ⟨before, entry, after, split, ⟨g', receiver, raw, decrypted, handle', frame, received, routed, receives,
    designated', framed, counterpart, encrypted, plaintext, cparted, sent, sentFramed, differ⟩, handled⟩ :=
    firstHandle_some _ _ _ handle claimed
  simp only [receivedHandle, received, Option.bind_some, routed, Option.some.injEq] at handled
  subst handled
  rw [designated] at designated'
  cases designated'
  have entryMember : entry ∈ value.2.1.2.transcript := by
    rw [split]
    simp
  cases handle' with
  | peer _ => exact absurd receives (by simp [Direction.Receives])
  | owner owner =>
    obtain ⟨_, holds⟩ := PqxdhDeploymentHeadlineContain.designation_owner setup.source.crypto codec setup.serverKeyId
      budget g (ctxView result).slots value.2.1.2.transcript owner slots designated
    obtain ⟨slot, slotFound⟩ := Option.isSome_iff_exists.mp holds
    refine plain_core codec route result facts value valueMember entry entryMember receiver raw decrypted (.owner owner)
      slot frame received routed slotFound framed counterpart (fun other counter => ?_) encrypted plaintext sent
      sentFramed differ
    obtain ⟨keyId, rfl, peerSlot⟩ := PqxdhDeploymentHeadlineAgree.counterpart_owner _ slot owner other counter
    obtain ⟨_, peer⟩ := slots.1 keyId slot peerSlot
    simp only [cpart, peer, Option.map_some, Option.some.injEq] at cparted
    exact cparted


/-- The containment of the b2s origin failure with the plaintext field: on every CTX-world outcome with the plaintext facts, `dec_g ∧ ISs_g` of it implies the record lift's unpublished-accept event (the frozen origin containment `PqxdhDeploymentHeadlineContain.origin_b2s`) or AG's failure event (`plain_agree_b2s`). -/
theorem originPlain_contain_b2s {E : Type} (g : Fin budget.accept × Fin budget.capacity)
    (result : PqxdhRecordLiftIdeal.Client 2 E X × PqxdhRecordLiftIdeal.CtxPrivate 2) (facts : PlainFacts codec result)
    (held : serverSlotted setup codec budget (originPlainEvent setup.source.crypto codec setup.serverKeyId budget
        route .b2s) (originPlainClaim setup.source.crypto codec setup.serverKeyId budget route .b2s) g (ctxView
        result) = true) :
    PqxdhRecordLiftIdeal.unpublishedEvent codec route (ctxView result) = true ∨ AgreeFailure codec route result := by
  classical
  simp only [serverSlotted, decide_eq_true_eq] at held
  obtain ⟨decided, server⟩ := held
  rcases found : viewObserved (ctxView result) with _ | observed
  · rw [found] at decided
    cases decided
  · have happened : originPlainEvent setup.source.crypto codec setup.serverKeyId budget route .b2s observed = true := by
      rw [found] at decided
      simp only [Option.any_some, decisionOn, Bool.and_eq_true] at decided
      exact decided.1
    simp only [originPlainEvent, decide_eq_true_eq] at happened
    by_cases origin : PqxdhDeploymentHeadlineEvents.OriginFailure setup.source.crypto codec setup.serverKeyId budget
        route
      .b2s observed
    · left
      apply PqxdhDeploymentHeadlineContain.origin_b2s setup codec budget route g (ctxView result)
      simp only [serverSlotted, decide_eq_true_eq]
      refine ⟨decision_transfer setup codec budget _ _ _ _ g _ decided fun other same _ => ?_, server⟩
      rw [found, Option.some.injEq] at same
      subst same
      refine ⟨by simp only [PqxdhDeploymentHeadlineEvents.originEvent, decide_eq_true_eq]; exact origin, ?_⟩
      simp only [originPlainClaim, origin, ↓reduceIte]
    · right
      apply plain_agree_b2s setup codec budget route g result facts
      simp only [serverSlotted, decide_eq_true_eq]
      refine ⟨decision_transfer setup codec budget _ _ _ _ g _ decided fun other same _ => ?_, server⟩
      rw [found, Option.some.injEq] at same
      subst same
      refine ⟨by simp only [plainEvent, decide_eq_true_eq]; exact happened.resolve_left origin, ?_⟩
      simp only [originPlainClaim, origin, ↓reduceIte]

/-- The containment of the s2b origin failure with the plaintext field: on every CTX-world outcome with the plaintext facts, `dec_g ∧ IS_g` of it implies the record lift's unpublished-accept event (`PqxdhDeploymentHeadlineContain.origin_s2b`) or AG's failure event (`plain_agree_s2b`). -/
theorem originPlain_contain_s2b {E : Type} (g : Fin budget.accept × Fin budget.capacity)
    (result : PqxdhRecordLiftIdeal.Client 2 E X × PqxdhRecordLiftIdeal.CtxPrivate 2) (facts : PlainFacts codec result)
    (held : slotted setup codec budget (originPlainEvent setup.source.crypto codec setup.serverKeyId budget route
        .s2b) (originPlainClaim setup.source.crypto codec setup.serverKeyId budget route .s2b) g (ctxView result) =
        true) :
    PqxdhRecordLiftIdeal.unpublishedEvent codec route (ctxView result) = true ∨ AgreeFailure codec route result := by
  classical
  simp only [slotted, decide_eq_true_eq] at held
  obtain ⟨decided, ideal⟩ := held
  rcases found : viewObserved (ctxView result) with _ | observed
  · rw [found] at decided
    cases decided
  · have happened : originPlainEvent setup.source.crypto codec setup.serverKeyId budget route .s2b observed = true := by
      rw [found] at decided
      simp only [Option.any_some, decisionOn, Bool.and_eq_true] at decided
      exact decided.1
    simp only [originPlainEvent, decide_eq_true_eq] at happened
    by_cases origin : PqxdhDeploymentHeadlineEvents.OriginFailure setup.source.crypto codec setup.serverKeyId budget
        route
      .s2b observed
    · left
      apply PqxdhDeploymentHeadlineContain.origin_s2b setup codec budget route g (ctxView result)
      simp only [slotted, decide_eq_true_eq]
      refine ⟨decision_transfer setup codec budget _ _ _ _ g _ decided fun other same _ => ?_, ideal⟩
      rw [found, Option.some.injEq] at same
      subst same
      refine ⟨by simp only [PqxdhDeploymentHeadlineEvents.originEvent, decide_eq_true_eq]; exact origin, ?_⟩
      simp only [originPlainClaim, origin, ↓reduceIte]
    · right
      apply plain_agree_s2b setup codec budget route g result facts
      simp only [slotted, decide_eq_true_eq]
      refine ⟨decision_transfer setup codec budget _ _ _ _ g _ decided fun other same _ => ?_, ideal⟩
      rw [found, Option.some.injEq] at same
      subst same
      refine ⟨by simp only [plainEvent, decide_eq_true_eq]; exact happened.resolve_left origin, ?_⟩
      simp only [originPlainClaim, origin, ↓reduceIte]


/-- The containment of the b2s origin failure with every computational field: on every CTX-world outcome with the pin facts and the plaintext facts, `dec_g ∧ ISs_g` of it implies the record lift's unpublished-accept event (`PqxdhDeploymentHeadlineContain.origin_b2s`) or AG's failure event (`PqxdhDeploymentHeadlinePin.pin_agree`, `plain_agree_b2s`). -/
theorem originFields_contain {E : Type} (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec)
    (g : Fin budget.accept × Fin budget.capacity)
    (result : PqxdhRecordLiftIdeal.Client 2 E X × PqxdhRecordLiftIdeal.CtxPrivate 2)
    (pinFacts : PqxdhDeploymentHeadlinePinInvariant.PinFacts codec result) (facts : PlainFacts codec result)
    (held : serverSlotted setup codec budget (originFieldsEvent setup.source.crypto codec setup.serverKeyId budget
        route)
      (originFieldsClaim setup.source.crypto codec setup.serverKeyId budget route) g (ctxView result) = true) :
    PqxdhRecordLiftIdeal.unpublishedEvent codec route (ctxView result) = true ∨ AgreeFailure codec route result := by
  classical
  simp only [serverSlotted, decide_eq_true_eq] at held
  obtain ⟨decided, server⟩ := held
  rcases found : viewObserved (ctxView result) with _ | observed
  · rw [found] at decided
    cases decided
  · have happened : originFieldsEvent setup.source.crypto codec setup.serverKeyId budget route observed = true := by
      rw [found] at decided
      simp only [Option.any_some, decisionOn, Bool.and_eq_true] at decided
      exact decided.1
    simp only [originFieldsEvent, decide_eq_true_eq] at happened
    by_cases origin : PqxdhDeploymentHeadlineEvents.OriginFailure setup.source.crypto codec setup.serverKeyId budget
        route
      .b2s observed
    · left
      apply PqxdhDeploymentHeadlineContain.origin_b2s setup codec budget route g (ctxView result)
      simp only [serverSlotted, decide_eq_true_eq]
      refine ⟨decision_transfer setup codec budget _ _ _ _ g _ decided fun other same _ => ?_, server⟩
      rw [found, Option.some.injEq] at same
      subst same
      refine ⟨by simp only [PqxdhDeploymentHeadlineEvents.originEvent, decide_eq_true_eq]; exact origin, ?_⟩
      simp only [originFieldsClaim, origin, ↓reduceIte]
    · right
      by_cases pin : PqxdhDeploymentHeadlinePin.PinFailure setup.source.crypto codec setup.serverKeyId budget route
        observed
      · apply PqxdhDeploymentHeadlinePin.pin_agree setup codec budget route phase2 g result pinFacts
        simp only [serverSlotted, decide_eq_true_eq]
        refine ⟨decision_transfer setup codec budget _ _ _ _ g _ decided fun other same _ => ?_, server⟩
        rw [found, Option.some.injEq] at same
        subst same
        refine ⟨by simp only [PqxdhDeploymentHeadlinePin.pinEvent, decide_eq_true_eq]; exact pin, ?_⟩
        simp only [originFieldsClaim, origin, pin, ↓reduceIte]
      · apply plain_agree_b2s setup codec budget route g result facts
        simp only [serverSlotted, decide_eq_true_eq]
        refine ⟨decision_transfer setup codec budget _ _ _ _ g _ decided fun other same _ => ?_, server⟩
        rw [found, Option.some.injEq] at same
        subst same
        refine ⟨by simp only [plainEvent, decide_eq_true_eq]; exact (happened.resolve_left origin).resolve_left pin, ?_⟩
        simp only [originFieldsClaim, origin, pin, ↓reduceIte]

end Contain


/-! ### The plaintext field in `idealAuth` and on the common deployment experiment -/

section Headline
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK A : Type}

/-- **R2 b2s in `idealAuth`.** With the ideal environment of the target of `g`, the probability that the record lift's view of `idealAuth` ends with `dec_g ∧ ISs_g` of the b2s plaintext failure is zero: such an outcome is an AG failure (`plain_agree_b2s`, with the plaintext facts `idealAuth_plainFacts`), and AG's failure event has probability zero (`PqxdhDeploymentHeadlineAgree.agreement_statement`). -/
theorem idealAuth_plain_b2s_zero (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (ensureInit : StateT A ProbComp Bool)
    (frameReadBack : PqxdhServerAuthNegativeControl.FrameReadBack codec) (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) (budget : Budget) (g : Fin budget.accept × Fin budget.capacity)
    (runtime : A) :
    𝒟[serverSlotted setup codec budget (plainEvent setup.source.crypto codec setup.serverKeyId budget route .b2s)
        (plainClaim setup.source.crypto codec setup.serverKeyId budget route .b2s) g <$>
      (ctxView <$> idealAuth setup codec route
        (PqxdhDeploymentIdealEnv.envGD setup codec checks (Target.ofCE budget g) ensureInit 0 runtime)
        setup.serverKeyId bounds mode adversary)] {true} = 0 := by
  apply nonpos_iff_eq_zero.mp
  rw [Functor.map_map]
  calc _ ≤ 𝒟[agreeEvent codec route <$> idealAuth setup codec route
        (PqxdhDeploymentIdealEnv.envGD setup codec checks (Target.ofCE budget g) ensureInit 0 runtime)
        setup.serverKeyId bounds mode adversary] {true} :=
        chance_mono_support _ _ _ fun result member held => by
          simp only [agreeEvent, decide_eq_true_eq]
          exact plain_agree_b2s setup codec budget route g result (idealAuth_plainFacts setup codec route
              frameReadBack _
            setup.serverKeyId bounds mode adversary result member) held
    _ = 0 := PqxdhDeploymentHeadlineAgree.agreement_statement setup codec route setup.serverKeyId bounds 2 _ mode
        adversary

/-- **R2 s2b in `idealAuth`.** With the ideal environment of the target of `g`, the probability that the record lift's view of `idealAuth` ends with `dec_g ∧ IS_g` of the s2b plaintext failure is zero (`plain_agree_s2b` and AG). -/
theorem idealAuth_plain_s2b_zero (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (ensureInit : StateT A ProbComp Bool)
    (frameReadBack : PqxdhServerAuthNegativeControl.FrameReadBack codec) (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) (budget : Budget) (g : Fin budget.accept × Fin budget.capacity)
    (runtime : A) :
    𝒟[slotted setup codec budget (plainEvent setup.source.crypto codec setup.serverKeyId budget route .s2b)
        (plainClaim setup.source.crypto codec setup.serverKeyId budget route .s2b) g <$>
      (ctxView <$> idealAuth setup codec route
        (PqxdhDeploymentIdealEnv.envGD setup codec checks (Target.ofCE budget g) ensureInit 0 runtime)
        setup.serverKeyId bounds mode adversary)] {true} = 0 := by
  apply nonpos_iff_eq_zero.mp
  rw [Functor.map_map]
  calc _ ≤ 𝒟[agreeEvent codec route <$> idealAuth setup codec route
        (PqxdhDeploymentIdealEnv.envGD setup codec checks (Target.ofCE budget g) ensureInit 0 runtime)
        setup.serverKeyId bounds mode adversary] {true} :=
        chance_mono_support _ _ _ fun result member held => by
          simp only [agreeEvent, decide_eq_true_eq]
          exact plain_agree_s2b setup codec budget route g result (idealAuth_plainFacts setup codec route
              frameReadBack _
            setup.serverKeyId bounds mode adversary result member) held
    _ = 0 := PqxdhDeploymentHeadlineAgree.agreement_statement setup codec route setup.serverKeyId bounds 2 _ mode
        adversary

/-- **R2 b2s, per target** (design-v2 section 7.6, mode-O plaintext, b2s): the probability that the deployment experiment ends with a b2s plaintext failure whose first failing entry's receiving Server peer designates `g` is at most `kemLoss + slotLoss + authLoss_g(dec_g ∧ ISs_g)`, each with coefficient one; no anomaly term and no publication term. -/
theorem ce_plain_b2s_target (setup : Setup baseSpec KemSK)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem)
    (codec : Codec Reader Response) (checks : Checks) (route : RawCtxServerRouting.SenderDecoder)
    (ensureInit : StateT A ProbComp Bool) (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec)
    (correct : PqxdhFullSecretInputKdf.SourceFullCorrect setup.source setup.hmac) (caps : KemCaps)
    (bounded : KemBound setup caps) (qInit : ℕ) (initBound : ∀ state, (ensureInit.run state).IsTotalQueryBound qInit)
    (frameReadBack : PqxdhServerAuthNegativeControl.FrameReadBack codec)
    (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) (budget : Budget) (respects : budget.Respects adversary) (runtime : A)
    (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery) (g : Fin budget.accept × Fin budget.capacity) :
    𝒟[(fun outcome => decide (happens (plainEvent setup.source.crypto codec setup.serverKeyId budget route .b2s)
        outcome = true ∧ designated setup.source.crypto codec setup.serverKeyId budget
          (plainClaim setup.source.crypto codec setup.serverKeyId budget route .b2s) outcome = some g)) <$>
      (PqxdhDeploymentSecrecy.game setup codec checks route ensureInit 0 bounds mode adversary).run runtime] {true} ≤
      ENNReal.ofReal (kemLoss setup codec checks route ensureInit bounds mode adversary budget
        (plainEvent setup.source.crypto codec setup.serverKeyId budget route .b2s)
        (plainClaim setup.source.crypto codec setup.serverKeyId budget route .b2s) g runtime) +
      ENNReal.ofReal (slotLoss setup codec checks route ensureInit bounds mode adversary budget
        (plainEvent setup.source.crypto codec setup.serverKeyId budget route .b2s)
        (plainClaim setup.source.crypto codec setup.serverKeyId budget route .b2s) g runtime) +
      authLoss setup codec checks route ensureInit bounds mode adversary budget g runtime fallback caps qInit
        (serverSlotted setup codec budget (plainEvent setup.source.crypto codec setup.serverKeyId budget route .b2s)
          (plainClaim setup.source.crypto codec setup.serverKeyId budget route .b2s) g) := by
  have chain := PqxdhDeploymentHeadlineChain.chain_server setup functional codec checks route ensureInit phase1 phase2
    correct bounds mode adversary budget respects (plainEvent setup.source.crypto codec setup.serverKeyId budget route
        .b2s) (plainClaim setup.source.crypto codec setup.serverKeyId budget route .b2s) g runtime
  have lift := PqxdhDeploymentHeadlineChain.auth_le setup codec checks route correct caps bounded ensureInit qInit
    initBound bounds mode adversary budget respects g runtime fallback
    (serverSlotted setup codec budget (plainEvent setup.source.crypto codec setup.serverKeyId budget route .b2s)
        (plainClaim setup.source.crypto codec setup.serverKeyId budget route .b2s) g)
  rw [idealAuth_plain_b2s_zero setup codec checks route ensureInit frameReadBack bounds mode adversary budget g runtime,
    zero_add] at lift
  calc _ ≤ _ := chain
    _ ≤ (authLoss setup codec checks route ensureInit bounds mode adversary budget g runtime fallback caps qInit
        (serverSlotted setup codec budget (plainEvent setup.source.crypto codec setup.serverKeyId budget route .b2s)
          (plainClaim setup.source.crypto codec setup.serverKeyId budget route .b2s) g) +
        ENNReal.ofReal (kemLoss setup codec checks route ensureInit bounds mode adversary budget
        (plainEvent setup.source.crypto codec setup.serverKeyId budget route .b2s)
        (plainClaim setup.source.crypto codec setup.serverKeyId budget route .b2s) g runtime)) +
        ENNReal.ofReal (slotLoss setup codec checks route ensureInit bounds mode adversary budget
        (plainEvent setup.source.crypto codec setup.serverKeyId budget route .b2s)
        (plainClaim setup.source.crypto codec setup.serverKeyId budget route .b2s) g runtime) :=
        add_le_add (add_le_add lift le_rfl) le_rfl
    _ = _ := by ring

/-- **R2 b2s** (`ce_plain_b2s`, design-v2 section 7.6, mode-O plaintext, b2s): the probability that the deployment experiment ends with a b2s plaintext failure (an accepted Server raw receive on a peer designating a target whose decoded frame the counterpart owner produced with another plaintext) is at most the sum over `g` in `Fin qAccept × Fin qCreate` (with `k` read in `Fin (qCreate + 1)`) of `kemLoss + slotLoss + authLoss_g(dec_g ∧ ISs_g)`, each with coefficient one. -/
theorem ce_plain_b2s (setup : Setup baseSpec KemSK)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem)
    (codec : Codec Reader Response) (checks : Checks) (route : RawCtxServerRouting.SenderDecoder)
    (ensureInit : StateT A ProbComp Bool) (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec)
    (correct : PqxdhFullSecretInputKdf.SourceFullCorrect setup.source setup.hmac) (caps : KemCaps)
    (bounded : KemBound setup caps) (qInit : ℕ) (initBound : ∀ state, (ensureInit.run state).IsTotalQueryBound qInit)
    (frameReadBack : PqxdhServerAuthNegativeControl.FrameReadBack codec)
    (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) (budget : Budget) (respects : budget.Respects adversary) (runtime : A)
    (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery) :
    𝒟[(fun outcome => happens (plainEvent setup.source.crypto codec setup.serverKeyId budget route .b2s) outcome) <$>
      (PqxdhDeploymentSecrecy.game setup codec checks route ensureInit 0 bounds mode adversary).run runtime] {true} ≤
      ∑ g : Fin budget.accept × Fin budget.create,
        (ENNReal.ofReal (kemLoss setup codec checks route ensureInit bounds mode adversary budget
        (plainEvent setup.source.crypto codec setup.serverKeyId budget route .b2s)
        (plainClaim setup.source.crypto codec setup.serverKeyId budget route .b2s) (g.1, g.2.castSucc) runtime) +
          ENNReal.ofReal (slotLoss setup codec checks route ensureInit bounds mode adversary budget
        (plainEvent setup.source.crypto codec setup.serverKeyId budget route .b2s)
        (plainClaim setup.source.crypto codec setup.serverKeyId budget route .b2s) (g.1, g.2.castSucc) runtime) +
          authLoss setup codec checks route ensureInit bounds mode adversary budget (g.1, g.2.castSucc) runtime
              fallback caps qInit
        (serverSlotted setup codec budget (plainEvent setup.source.crypto codec setup.serverKeyId budget route .b2s)
          (plainClaim setup.source.crypto codec setup.serverKeyId budget route .b2s) (g.1, g.2.castSucc))) := by
  rw [PqxdhDeploymentHeadlineChain.split_named setup codec checks route ensureInit phase1 phase2 bounds mode adversary
    budget respects _ _ runtime (plain_named setup.source.crypto codec setup.serverKeyId budget route .b2s)]
  exact Finset.sum_le_sum fun g _ => ce_plain_b2s_target setup functional codec checks route ensureInit phase1 phase2
    correct caps bounded qInit initBound frameReadBack bounds mode adversary budget respects runtime fallback
    (g.1, g.2.castSucc)

/-- **R2 s2b, per target** (design-v2 section 7.6, mode-O plaintext, s2b): the probability that the deployment experiment ends with an s2b plaintext failure whose first failing entry's receiving owner designates `g` is at most `kemLoss + slotLoss + β_g + authLoss_g(dec_g ∧ IS_g)`, each with coefficient one; no publication term. -/
theorem ce_plain_s2b_target (setup : Setup baseSpec KemSK)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem)
    (codec : Codec Reader Response) (checks : Checks) (route : RawCtxServerRouting.SenderDecoder)
    (ensureInit : StateT A ProbComp Bool) (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec)
    (correct : PqxdhFullSecretInputKdf.SourceFullCorrect setup.source setup.hmac) (caps : KemCaps)
    (bounded : KemBound setup caps) (qInit : ℕ) (initBound : ∀ state, (ensureInit.run state).IsTotalQueryBound qInit)
    (frameReadBack : PqxdhServerAuthNegativeControl.FrameReadBack codec)
    (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) (budget : Budget) (respects : budget.Respects adversary) (runtime : A)
    (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery) (g : Fin budget.accept × Fin budget.capacity) :
    𝒟[(fun outcome => decide (happens (plainEvent setup.source.crypto codec setup.serverKeyId budget route .s2b)
        outcome = true ∧ designated setup.source.crypto codec setup.serverKeyId budget
          (plainClaim setup.source.crypto codec setup.serverKeyId budget route .s2b) outcome = some g)) <$>
      (PqxdhDeploymentSecrecy.game setup codec checks route ensureInit 0 bounds mode adversary).run runtime] {true} ≤
      ENNReal.ofReal (kemLoss setup codec checks route ensureInit bounds mode adversary budget
        (plainEvent setup.source.crypto codec setup.serverKeyId budget route .s2b)
        (plainClaim setup.source.crypto codec setup.serverKeyId budget route .s2b) g runtime) +
      ENNReal.ofReal (slotLoss setup codec checks route ensureInit bounds mode adversary budget
        (plainEvent setup.source.crypto codec setup.serverKeyId budget route .s2b)
        (plainClaim setup.source.crypto codec setup.serverKeyId budget route .s2b) g runtime) +
      beta setup codec route checks ensureInit bounds mode adversary budget g runtime +
      authLoss setup codec checks route ensureInit bounds mode adversary budget g runtime fallback caps qInit
        (slotted setup codec budget (plainEvent setup.source.crypto codec setup.serverKeyId budget route .s2b)
          (plainClaim setup.source.crypto codec setup.serverKeyId budget route .s2b) g) := by
  have chain := PqxdhDeploymentHeadlineAnomaly.chain_beta setup functional codec checks route ensureInit phase1 phase2
    correct bounds mode adversary budget respects (plainEvent setup.source.crypto codec setup.serverKeyId budget route
        .s2b) (plainClaim setup.source.crypto codec setup.serverKeyId budget route .s2b) g runtime
  have lift := PqxdhDeploymentHeadlineChain.auth_le setup codec checks route correct caps bounded ensureInit qInit
    initBound bounds mode adversary budget respects g runtime fallback
    (slotted setup codec budget (plainEvent setup.source.crypto codec setup.serverKeyId budget route .s2b) (plainClaim
        setup.source.crypto codec setup.serverKeyId budget route .s2b) g)
  rw [idealAuth_plain_s2b_zero setup codec checks route ensureInit frameReadBack bounds mode adversary budget g runtime,
    zero_add] at lift
  calc _ ≤ _ := chain
    _ ≤ ((authLoss setup codec checks route ensureInit bounds mode adversary budget g runtime fallback caps qInit
        (slotted setup codec budget (plainEvent setup.source.crypto codec setup.serverKeyId budget route .s2b)
          (plainClaim setup.source.crypto codec setup.serverKeyId budget route .s2b) g) +
        beta setup codec route checks ensureInit bounds mode adversary budget g runtime) +
        ENNReal.ofReal (kemLoss setup codec checks route ensureInit bounds mode adversary budget
        (plainEvent setup.source.crypto codec setup.serverKeyId budget route .s2b)
        (plainClaim setup.source.crypto codec setup.serverKeyId budget route .s2b) g runtime)) +
        ENNReal.ofReal (slotLoss setup codec checks route ensureInit bounds mode adversary budget
        (plainEvent setup.source.crypto codec setup.serverKeyId budget route .s2b)
        (plainClaim setup.source.crypto codec setup.serverKeyId budget route .s2b) g runtime) :=
        add_le_add (add_le_add (add_le_add lift le_rfl) le_rfl) le_rfl
    _ = _ := by ring

/-- **R2 s2b** (`ce_plain_s2b`, design-v2 section 7.6, mode-O plaintext, s2b): the probability that the deployment experiment ends with an s2b plaintext failure (an accepted Beacon raw receive on an owner designating a target whose decoded frame the target's Server peer produced with another plaintext) is at most the sum over `g` in `Fin qAccept × Fin qCreate` (with `k` read in `Fin (qCreate + 1)`) of `kemLoss + slotLoss + β_g + authLoss_g(dec_g ∧ IS_g)`, each with coefficient one. -/
theorem ce_plain_s2b (setup : Setup baseSpec KemSK)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem)
    (codec : Codec Reader Response) (checks : Checks) (route : RawCtxServerRouting.SenderDecoder)
    (ensureInit : StateT A ProbComp Bool) (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec)
    (correct : PqxdhFullSecretInputKdf.SourceFullCorrect setup.source setup.hmac) (caps : KemCaps)
    (bounded : KemBound setup caps) (qInit : ℕ) (initBound : ∀ state, (ensureInit.run state).IsTotalQueryBound qInit)
    (frameReadBack : PqxdhServerAuthNegativeControl.FrameReadBack codec)
    (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) (budget : Budget) (respects : budget.Respects adversary) (runtime : A)
    (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery) :
    𝒟[(fun outcome => happens (plainEvent setup.source.crypto codec setup.serverKeyId budget route .s2b) outcome) <$>
      (PqxdhDeploymentSecrecy.game setup codec checks route ensureInit 0 bounds mode adversary).run runtime] {true} ≤
      ∑ g : Fin budget.accept × Fin budget.create,
        (ENNReal.ofReal (kemLoss setup codec checks route ensureInit bounds mode adversary budget
        (plainEvent setup.source.crypto codec setup.serverKeyId budget route .s2b)
        (plainClaim setup.source.crypto codec setup.serverKeyId budget route .s2b) (g.1, g.2.castSucc) runtime) +
          ENNReal.ofReal (slotLoss setup codec checks route ensureInit bounds mode adversary budget
        (plainEvent setup.source.crypto codec setup.serverKeyId budget route .s2b)
        (plainClaim setup.source.crypto codec setup.serverKeyId budget route .s2b) (g.1, g.2.castSucc) runtime) +
          beta setup codec route checks ensureInit bounds mode adversary budget (g.1, g.2.castSucc) runtime +
          authLoss setup codec checks route ensureInit bounds mode adversary budget (g.1, g.2.castSucc) runtime
              fallback caps qInit
        (slotted setup codec budget (plainEvent setup.source.crypto codec setup.serverKeyId budget route .s2b)
          (plainClaim setup.source.crypto codec setup.serverKeyId budget route .s2b) (g.1, g.2.castSucc))) := by
  rw [PqxdhDeploymentHeadlineChain.split_named setup codec checks route ensureInit phase1 phase2 bounds mode adversary
    budget respects _ _ runtime (plain_named setup.source.crypto codec setup.serverKeyId budget route .s2b)]
  exact Finset.sum_le_sum fun g _ => ce_plain_s2b_target setup functional codec checks route ensureInit phase1 phase2
    correct caps bounded qInit initBound frameReadBack bounds mode adversary budget respects runtime fallback
    (g.1, g.2.castSucc)


/-- With the ideal environment of the target of `g`, the probability that the record lift's view of `idealAuth` ends with `dec_g ∧ ISs_g` of the b2s origin failure with the plaintext field is at most `publicationTerm budget`: the unpublished-accept part is the frozen bound (`PqxdhDeploymentHeadlineOrigin.unpublished_final`) and the plaintext part has probability zero (AG). -/
theorem idealAuth_originPlain_b2s_le (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (caps : KemCaps) (bounded : KemBound setup caps)
    (ensureInit : StateT A ProbComp Bool) (qInit : ℕ)
    (initBound : ∀ state, (ensureInit.run state).IsTotalQueryBound qInit)
    (frameReadBack : PqxdhServerAuthNegativeControl.FrameReadBack codec) (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) (budget : Budget) (respects : budget.Respects adversary)
    (g : Fin budget.accept × Fin budget.capacity) (runtime : A) :
    𝒟[serverSlotted setup codec budget (originPlainEvent setup.source.crypto codec setup.serverKeyId budget route
        .b2s) (originPlainClaim setup.source.crypto codec setup.serverKeyId budget route .b2s) g <$>
      (ctxView <$> idealAuth setup codec route
        (PqxdhDeploymentIdealEnv.envGD setup codec checks (Target.ofCE budget g) ensureInit 0 runtime)
        setup.serverKeyId bounds mode adversary)] {true} ≤ publicationTerm budget := by
  have final := PqxdhDeploymentHeadlineOrigin.unpublished_final setup codec checks route caps bounded ensureInit qInit
    initBound frameReadBack bounds mode adversary budget respects g runtime
  have zero := PqxdhDeploymentHeadlineAgree.agreement_statement setup codec route setup.serverKeyId bounds 2
    (PqxdhDeploymentIdealEnv.envGD setup codec checks (Target.ofCE budget g) ensureInit 0 runtime) mode adversary
  rw [Functor.map_map] at final ⊢
  calc _ ≤ 𝒟[(fun result => PqxdhRecordLiftIdeal.unpublishedEvent codec route (ctxView result) ||
        agreeEvent codec route result) <$> idealAuth setup codec route
          (PqxdhDeploymentIdealEnv.envGD setup codec checks (Target.ofCE budget g) ensureInit 0 runtime)
          setup.serverKeyId bounds mode adversary] {true} :=
        chance_mono_support _ _ _ fun result member held => by
          rcases originPlain_contain_b2s setup codec budget route g result (idealAuth_plainFacts setup codec route
            frameReadBack _ setup.serverKeyId bounds mode adversary result member) held with unpublished | failure
          · simp only [unpublished, Bool.true_or]
          · simp only [agreeEvent, failure, decide_true, Bool.or_true]
    _ ≤ _ := chance_or_le _ _ _
    _ ≤ publicationTerm budget := by
        rw [zero, add_zero]
        exact final

/-- With the ideal environment of the target of `g`, the probability that the record lift's view of `idealAuth` ends with `dec_g ∧ IS_g` of the s2b origin failure with the plaintext field is at most `publicationTerm budget`. -/
theorem idealAuth_originPlain_s2b_le (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (caps : KemCaps) (bounded : KemBound setup caps)
    (ensureInit : StateT A ProbComp Bool) (qInit : ℕ)
    (initBound : ∀ state, (ensureInit.run state).IsTotalQueryBound qInit)
    (frameReadBack : PqxdhServerAuthNegativeControl.FrameReadBack codec) (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) (budget : Budget) (respects : budget.Respects adversary)
    (g : Fin budget.accept × Fin budget.capacity) (runtime : A) :
    𝒟[slotted setup codec budget (originPlainEvent setup.source.crypto codec setup.serverKeyId budget route .s2b)
        (originPlainClaim setup.source.crypto codec setup.serverKeyId budget route .s2b) g <$>
      (ctxView <$> idealAuth setup codec route
        (PqxdhDeploymentIdealEnv.envGD setup codec checks (Target.ofCE budget g) ensureInit 0 runtime)
        setup.serverKeyId bounds mode adversary)] {true} ≤ publicationTerm budget := by
  have final := PqxdhDeploymentHeadlineOrigin.unpublished_final setup codec checks route caps bounded ensureInit qInit
    initBound frameReadBack bounds mode adversary budget respects g runtime
  have zero := PqxdhDeploymentHeadlineAgree.agreement_statement setup codec route setup.serverKeyId bounds 2
    (PqxdhDeploymentIdealEnv.envGD setup codec checks (Target.ofCE budget g) ensureInit 0 runtime) mode adversary
  rw [Functor.map_map] at final ⊢
  calc _ ≤ 𝒟[(fun result => PqxdhRecordLiftIdeal.unpublishedEvent codec route (ctxView result) ||
        agreeEvent codec route result) <$> idealAuth setup codec route
          (PqxdhDeploymentIdealEnv.envGD setup codec checks (Target.ofCE budget g) ensureInit 0 runtime)
          setup.serverKeyId bounds mode adversary] {true} :=
        chance_mono_support _ _ _ fun result member held => by
          rcases originPlain_contain_s2b setup codec budget route g result (idealAuth_plainFacts setup codec route
            frameReadBack _ setup.serverKeyId bounds mode adversary result member) held with unpublished | failure
          · simp only [unpublished, Bool.true_or]
          · simp only [agreeEvent, failure, decide_true, Bool.or_true]
    _ ≤ _ := chance_or_le _ _ _
    _ ≤ publicationTerm budget := by
        rw [zero, add_zero]
        exact final

/-- **CE-OR b2s with the plaintext field, per target** (design-v2 sections 4.2 and 7.6): the probability that the deployment experiment ends with a b2s origin failure or a b2s plaintext failure whose claimed receiving Server peer designates `g` is at most `kemLoss + slotLoss + authLoss_g(dec_g ∧ ISs_g) + publicationTerm budget`, each with coefficient one; no anomaly term. -/
theorem ce_or_plain_b2s_target (setup : Setup baseSpec KemSK)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem)
    (codec : Codec Reader Response) (checks : Checks) (route : RawCtxServerRouting.SenderDecoder)
    (ensureInit : StateT A ProbComp Bool) (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec)
    (correct : PqxdhFullSecretInputKdf.SourceFullCorrect setup.source setup.hmac) (caps : KemCaps)
    (bounded : KemBound setup caps) (qInit : ℕ) (initBound : ∀ state, (ensureInit.run state).IsTotalQueryBound qInit)
    (frameReadBack : PqxdhServerAuthNegativeControl.FrameReadBack codec)
    (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) (budget : Budget) (respects : budget.Respects adversary) (runtime : A)
    (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery) (g : Fin budget.accept × Fin budget.capacity) :
    𝒟[(fun outcome => decide (happens (originPlainEvent setup.source.crypto codec setup.serverKeyId budget route .b2s)
        outcome = true ∧ designated setup.source.crypto codec setup.serverKeyId budget
          (originPlainClaim setup.source.crypto codec setup.serverKeyId budget route .b2s) outcome = some g)) <$>
      (PqxdhDeploymentSecrecy.game setup codec checks route ensureInit 0 bounds mode adversary).run runtime] {true} ≤
      ENNReal.ofReal (kemLoss setup codec checks route ensureInit bounds mode adversary budget
        (originPlainEvent setup.source.crypto codec setup.serverKeyId budget route .b2s)
        (originPlainClaim setup.source.crypto codec setup.serverKeyId budget route .b2s) g runtime) +
      ENNReal.ofReal (slotLoss setup codec checks route ensureInit bounds mode adversary budget
        (originPlainEvent setup.source.crypto codec setup.serverKeyId budget route .b2s)
        (originPlainClaim setup.source.crypto codec setup.serverKeyId budget route .b2s) g runtime) +
      authLoss setup codec checks route ensureInit bounds mode adversary budget g runtime fallback caps qInit
        (serverSlotted setup codec budget (originPlainEvent setup.source.crypto codec setup.serverKeyId budget route
            .b2s)
          (originPlainClaim setup.source.crypto codec setup.serverKeyId budget route .b2s) g) +
      publicationTerm budget := by
  have chain := PqxdhDeploymentHeadlineChain.chain_server setup functional codec checks route ensureInit phase1 phase2
    correct bounds mode adversary budget respects (originPlainEvent setup.source.crypto codec setup.serverKeyId budget
        route .b2s) (originPlainClaim setup.source.crypto codec setup.serverKeyId budget route .b2s) g runtime
  have lift := PqxdhDeploymentHeadlineChain.auth_le setup codec checks route correct caps bounded ensureInit qInit
    initBound bounds mode adversary budget respects g runtime fallback
    (serverSlotted setup codec budget (originPlainEvent setup.source.crypto codec setup.serverKeyId budget route .b2s)
        (originPlainClaim setup.source.crypto codec setup.serverKeyId budget route .b2s) g)
  have final := idealAuth_originPlain_b2s_le setup codec checks route caps bounded ensureInit qInit initBound
    frameReadBack bounds mode adversary budget respects g runtime
  calc _ ≤ _ := chain
    _ ≤ ((publicationTerm budget +
          authLoss setup codec checks route ensureInit bounds mode adversary budget g runtime fallback caps qInit
            (serverSlotted setup codec budget (originPlainEvent setup.source.crypto codec setup.serverKeyId budget
                route .b2s)
              (originPlainClaim setup.source.crypto codec setup.serverKeyId budget route .b2s) g)) +
        ENNReal.ofReal (kemLoss setup codec checks route ensureInit bounds mode adversary budget
          (originPlainEvent setup.source.crypto codec setup.serverKeyId budget route .b2s)
          (originPlainClaim setup.source.crypto codec setup.serverKeyId budget route .b2s) g runtime)) +
        ENNReal.ofReal (slotLoss setup codec checks route ensureInit bounds mode adversary budget
          (originPlainEvent setup.source.crypto codec setup.serverKeyId budget route .b2s)
          (originPlainClaim setup.source.crypto codec setup.serverKeyId budget route .b2s) g runtime) :=
        add_le_add (add_le_add (lift.trans (add_le_add final le_rfl)) le_rfl) le_rfl
    _ = _ := by ring

/-- **CE-OR b2s with the plaintext field** (`ce_or_plain_b2s`, design-v2 sections 4.2 and 7.6): the probability that the deployment experiment ends with a b2s origin failure or a b2s plaintext failure is at most the sum over `g` in `Fin qAccept × Fin qCreate` (with `k` read in `Fin (qCreate + 1)`) of `kemLoss + slotLoss + authLoss_g(dec_g ∧ ISs_g) + publicationTerm budget`, each with coefficient one; no anomaly term. -/
theorem ce_or_plain_b2s (setup : Setup baseSpec KemSK)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem)
    (codec : Codec Reader Response) (checks : Checks) (route : RawCtxServerRouting.SenderDecoder)
    (ensureInit : StateT A ProbComp Bool) (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec)
    (correct : PqxdhFullSecretInputKdf.SourceFullCorrect setup.source setup.hmac) (caps : KemCaps)
    (bounded : KemBound setup caps) (qInit : ℕ) (initBound : ∀ state, (ensureInit.run state).IsTotalQueryBound qInit)
    (frameReadBack : PqxdhServerAuthNegativeControl.FrameReadBack codec)
    (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) (budget : Budget) (respects : budget.Respects adversary) (runtime : A)
    (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery) :
    𝒟[(fun outcome => happens (originPlainEvent setup.source.crypto codec setup.serverKeyId budget route .b2s)
        outcome) <$>
      (PqxdhDeploymentSecrecy.game setup codec checks route ensureInit 0 bounds mode adversary).run runtime] {true} ≤
      ∑ g : Fin budget.accept × Fin budget.create,
        (ENNReal.ofReal (kemLoss setup codec checks route ensureInit bounds mode adversary budget
            (originPlainEvent setup.source.crypto codec setup.serverKeyId budget route .b2s)
            (originPlainClaim setup.source.crypto codec setup.serverKeyId budget route .b2s) (g.1, g.2.castSucc)
                runtime) +
          ENNReal.ofReal (slotLoss setup codec checks route ensureInit bounds mode adversary budget
            (originPlainEvent setup.source.crypto codec setup.serverKeyId budget route .b2s)
            (originPlainClaim setup.source.crypto codec setup.serverKeyId budget route .b2s) (g.1, g.2.castSucc)
                runtime) +
          authLoss setup codec checks route ensureInit bounds mode adversary budget (g.1, g.2.castSucc) runtime
              fallback caps qInit
            (serverSlotted setup codec budget (originPlainEvent setup.source.crypto codec setup.serverKeyId budget
                route .b2s)
              (originPlainClaim setup.source.crypto codec setup.serverKeyId budget route .b2s) (g.1, g.2.castSucc)) +
          publicationTerm budget) := by
  rw [PqxdhDeploymentHeadlineChain.split_named setup codec checks route ensureInit phase1 phase2 bounds mode adversary
    budget respects _ _ runtime (originPlain_named setup.source.crypto codec setup.serverKeyId budget route .b2s)]
  exact Finset.sum_le_sum fun g _ => ce_or_plain_b2s_target setup functional codec checks route ensureInit phase1
    phase2 correct caps bounded qInit initBound frameReadBack bounds mode adversary budget respects runtime fallback
    (g.1, g.2.castSucc)

/-- **CE-OR s2b with the plaintext field, per target** (design-v2 sections 4.2 and 7.6): the probability that the deployment experiment ends with an s2b origin failure or an s2b plaintext failure whose claimed receiving owner designates `g` is at most `kemLoss + slotLoss + β_g + authLoss_g(dec_g ∧ IS_g) + publicationTerm budget`, each with coefficient one. -/
theorem ce_or_plain_s2b_target (setup : Setup baseSpec KemSK)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem)
    (codec : Codec Reader Response) (checks : Checks) (route : RawCtxServerRouting.SenderDecoder)
    (ensureInit : StateT A ProbComp Bool) (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec)
    (correct : PqxdhFullSecretInputKdf.SourceFullCorrect setup.source setup.hmac) (caps : KemCaps)
    (bounded : KemBound setup caps) (qInit : ℕ) (initBound : ∀ state, (ensureInit.run state).IsTotalQueryBound qInit)
    (frameReadBack : PqxdhServerAuthNegativeControl.FrameReadBack codec)
    (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) (budget : Budget) (respects : budget.Respects adversary) (runtime : A)
    (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery) (g : Fin budget.accept × Fin budget.capacity) :
    𝒟[(fun outcome => decide (happens (originPlainEvent setup.source.crypto codec setup.serverKeyId budget route .s2b)
        outcome = true ∧ designated setup.source.crypto codec setup.serverKeyId budget
          (originPlainClaim setup.source.crypto codec setup.serverKeyId budget route .s2b) outcome = some g)) <$>
      (PqxdhDeploymentSecrecy.game setup codec checks route ensureInit 0 bounds mode adversary).run runtime] {true} ≤
      ENNReal.ofReal (kemLoss setup codec checks route ensureInit bounds mode adversary budget
        (originPlainEvent setup.source.crypto codec setup.serverKeyId budget route .s2b)
        (originPlainClaim setup.source.crypto codec setup.serverKeyId budget route .s2b) g runtime) +
      ENNReal.ofReal (slotLoss setup codec checks route ensureInit bounds mode adversary budget
        (originPlainEvent setup.source.crypto codec setup.serverKeyId budget route .s2b)
        (originPlainClaim setup.source.crypto codec setup.serverKeyId budget route .s2b) g runtime) +
      beta setup codec route checks ensureInit bounds mode adversary budget g runtime +
      authLoss setup codec checks route ensureInit bounds mode adversary budget g runtime fallback caps qInit
        (slotted setup codec budget (originPlainEvent setup.source.crypto codec setup.serverKeyId budget route .s2b)
          (originPlainClaim setup.source.crypto codec setup.serverKeyId budget route .s2b) g) +
      publicationTerm budget := by
  have chain := PqxdhDeploymentHeadlineAnomaly.chain_beta setup functional codec checks route ensureInit phase1 phase2
    correct bounds mode adversary budget respects (originPlainEvent setup.source.crypto codec setup.serverKeyId budget
        route .s2b) (originPlainClaim setup.source.crypto codec setup.serverKeyId budget route .s2b) g runtime
  have lift := PqxdhDeploymentHeadlineChain.auth_le setup codec checks route correct caps bounded ensureInit qInit
    initBound bounds mode adversary budget respects g runtime fallback
    (slotted setup codec budget (originPlainEvent setup.source.crypto codec setup.serverKeyId budget route .s2b)
        (originPlainClaim setup.source.crypto codec setup.serverKeyId budget route .s2b) g)
  have final := idealAuth_originPlain_s2b_le setup codec checks route caps bounded ensureInit qInit initBound
    frameReadBack bounds mode adversary budget respects g runtime
  calc _ ≤ _ := chain
    _ ≤ (((publicationTerm budget +
          authLoss setup codec checks route ensureInit bounds mode adversary budget g runtime fallback caps qInit
            (slotted setup codec budget (originPlainEvent setup.source.crypto codec setup.serverKeyId budget route .s2b)
              (originPlainClaim setup.source.crypto codec setup.serverKeyId budget route .s2b) g)) +
        beta setup codec route checks ensureInit bounds mode adversary budget g runtime) +
        ENNReal.ofReal (kemLoss setup codec checks route ensureInit bounds mode adversary budget
          (originPlainEvent setup.source.crypto codec setup.serverKeyId budget route .s2b)
          (originPlainClaim setup.source.crypto codec setup.serverKeyId budget route .s2b) g runtime)) +
        ENNReal.ofReal (slotLoss setup codec checks route ensureInit bounds mode adversary budget
          (originPlainEvent setup.source.crypto codec setup.serverKeyId budget route .s2b)
          (originPlainClaim setup.source.crypto codec setup.serverKeyId budget route .s2b) g runtime) :=
        add_le_add (add_le_add (add_le_add (lift.trans (add_le_add final le_rfl)) le_rfl) le_rfl) le_rfl
    _ = _ := by ring

/-- **CE-OR s2b with the plaintext field** (`ce_or_plain_s2b`, design-v2 sections 4.2 and 7.6): the probability that the deployment experiment ends with an s2b origin failure or an s2b plaintext failure is at most the sum over `g` in `Fin qAccept × Fin qCreate` (with `k` read in `Fin (qCreate + 1)`) of `kemLoss + slotLoss + β_g + authLoss_g(dec_g ∧ IS_g) + publicationTerm budget`, each with coefficient one. -/
theorem ce_or_plain_s2b (setup : Setup baseSpec KemSK)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem)
    (codec : Codec Reader Response) (checks : Checks) (route : RawCtxServerRouting.SenderDecoder)
    (ensureInit : StateT A ProbComp Bool) (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec)
    (correct : PqxdhFullSecretInputKdf.SourceFullCorrect setup.source setup.hmac) (caps : KemCaps)
    (bounded : KemBound setup caps) (qInit : ℕ) (initBound : ∀ state, (ensureInit.run state).IsTotalQueryBound qInit)
    (frameReadBack : PqxdhServerAuthNegativeControl.FrameReadBack codec)
    (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) (budget : Budget) (respects : budget.Respects adversary) (runtime : A)
    (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery) :
    𝒟[(fun outcome => happens (originPlainEvent setup.source.crypto codec setup.serverKeyId budget route .s2b)
        outcome) <$>
      (PqxdhDeploymentSecrecy.game setup codec checks route ensureInit 0 bounds mode adversary).run runtime] {true} ≤
      ∑ g : Fin budget.accept × Fin budget.create,
        (ENNReal.ofReal (kemLoss setup codec checks route ensureInit bounds mode adversary budget
            (originPlainEvent setup.source.crypto codec setup.serverKeyId budget route .s2b)
            (originPlainClaim setup.source.crypto codec setup.serverKeyId budget route .s2b) (g.1, g.2.castSucc)
                runtime) +
          ENNReal.ofReal (slotLoss setup codec checks route ensureInit bounds mode adversary budget
            (originPlainEvent setup.source.crypto codec setup.serverKeyId budget route .s2b)
            (originPlainClaim setup.source.crypto codec setup.serverKeyId budget route .s2b) (g.1, g.2.castSucc)
                runtime) +
          beta setup codec route checks ensureInit bounds mode adversary budget (g.1, g.2.castSucc) runtime +
          authLoss setup codec checks route ensureInit bounds mode adversary budget (g.1, g.2.castSucc) runtime
              fallback caps qInit
            (slotted setup codec budget (originPlainEvent setup.source.crypto codec setup.serverKeyId budget route .s2b)
              (originPlainClaim setup.source.crypto codec setup.serverKeyId budget route .s2b) (g.1, g.2.castSucc)) +
          publicationTerm budget) := by
  rw [PqxdhDeploymentHeadlineChain.split_named setup codec checks route ensureInit phase1 phase2 bounds mode adversary
    budget respects _ _ runtime (originPlain_named setup.source.crypto codec setup.serverKeyId budget route .s2b)]
  exact Finset.sum_le_sum fun g _ => ce_or_plain_s2b_target setup functional codec checks route ensureInit phase1
    phase2 correct caps bounded qInit initBound frameReadBack bounds mode adversary budget respects runtime fallback
    (g.1, g.2.castSucc)


/-- `happens` is monotone in the event. -/
theorem happens_mono {KemSK' : Type} (event event' : Observed X → Bool)
    (implies : ∀ observed, event observed = true → event' observed = true)
    (outcome : Option (PqxdhRegistrationJointServerBirth.ClientCreated Unit × X ×
      PqxdhDeploymentSecrecy.State KemSK') × A) (held : happens event outcome = true) : happens event' outcome =
          true := by
  unfold happens at held ⊢
  rcases observed : PqxdhDeploymentKemTransfer.observeGame outcome.1 with _ | value
  · rw [observed] at held
    cases held
  · rw [observed] at held
    exact implies value held

/-- **R2 b2s with every production** (the reading of design-v2 section 7.6 in which the returned plaintext differs from every counterpart production of the frame and one exists): its probability on the deployment experiment is at most the bound of `ce_plain_b2s`, because it is contained in the b2s plaintext failure (`plainEvery_plain`). -/
theorem ce_plain_every_b2s (setup : Setup baseSpec KemSK)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem)
    (codec : Codec Reader Response) (checks : Checks) (route : RawCtxServerRouting.SenderDecoder)
    (ensureInit : StateT A ProbComp Bool) (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec)
    (correct : PqxdhFullSecretInputKdf.SourceFullCorrect setup.source setup.hmac) (caps : KemCaps)
    (bounded : KemBound setup caps) (qInit : ℕ) (initBound : ∀ state, (ensureInit.run state).IsTotalQueryBound qInit)
    (frameReadBack : PqxdhServerAuthNegativeControl.FrameReadBack codec)
    (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) (budget : Budget) (respects : budget.Respects adversary) (runtime : A)
    (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery) :
    𝒟[(fun outcome => happens (plainEveryEvent setup.source.crypto codec setup.serverKeyId budget route .b2s) outcome)
        <$>
      (PqxdhDeploymentSecrecy.game setup codec checks route ensureInit 0 bounds mode adversary).run runtime] {true} ≤
      ∑ g : Fin budget.accept × Fin budget.create,
        (ENNReal.ofReal (kemLoss setup codec checks route ensureInit bounds mode adversary budget
            (plainEvent setup.source.crypto codec setup.serverKeyId budget route .b2s)
            (plainClaim setup.source.crypto codec setup.serverKeyId budget route .b2s) (g.1, g.2.castSucc) runtime) +
          ENNReal.ofReal (slotLoss setup codec checks route ensureInit bounds mode adversary budget
            (plainEvent setup.source.crypto codec setup.serverKeyId budget route .b2s)
            (plainClaim setup.source.crypto codec setup.serverKeyId budget route .b2s) (g.1, g.2.castSucc) runtime) +
          authLoss setup codec checks route ensureInit bounds mode adversary budget (g.1, g.2.castSucc) runtime
              fallback caps qInit
            (serverSlotted setup codec budget (plainEvent setup.source.crypto codec setup.serverKeyId budget route .b2s)
              (plainClaim setup.source.crypto codec setup.serverKeyId budget route .b2s) (g.1, g.2.castSucc))) :=
  (PqxdhDeploymentHeadlineContain.chance_mono _ _ _ fun outcome held => happens_mono _ _
    (plainEvery_plain setup.source.crypto codec setup.serverKeyId budget route .b2s) outcome held).trans
    (ce_plain_b2s setup functional codec checks route ensureInit phase1 phase2 correct caps bounded qInit initBound
      frameReadBack bounds mode adversary budget respects runtime fallback)

/-- **R2 s2b with every production**: its probability on the deployment experiment is at most the bound of `ce_plain_s2b` (`plainEvery_plain`). -/
theorem ce_plain_every_s2b (setup : Setup baseSpec KemSK)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem)
    (codec : Codec Reader Response) (checks : Checks) (route : RawCtxServerRouting.SenderDecoder)
    (ensureInit : StateT A ProbComp Bool) (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec)
    (correct : PqxdhFullSecretInputKdf.SourceFullCorrect setup.source setup.hmac) (caps : KemCaps)
    (bounded : KemBound setup caps) (qInit : ℕ) (initBound : ∀ state, (ensureInit.run state).IsTotalQueryBound qInit)
    (frameReadBack : PqxdhServerAuthNegativeControl.FrameReadBack codec)
    (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) (budget : Budget) (respects : budget.Respects adversary) (runtime : A)
    (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery) :
    𝒟[(fun outcome => happens (plainEveryEvent setup.source.crypto codec setup.serverKeyId budget route .s2b) outcome)
        <$>
      (PqxdhDeploymentSecrecy.game setup codec checks route ensureInit 0 bounds mode adversary).run runtime] {true} ≤
      ∑ g : Fin budget.accept × Fin budget.create,
        (ENNReal.ofReal (kemLoss setup codec checks route ensureInit bounds mode adversary budget
            (plainEvent setup.source.crypto codec setup.serverKeyId budget route .s2b)
            (plainClaim setup.source.crypto codec setup.serverKeyId budget route .s2b) (g.1, g.2.castSucc) runtime) +
          ENNReal.ofReal (slotLoss setup codec checks route ensureInit bounds mode adversary budget
            (plainEvent setup.source.crypto codec setup.serverKeyId budget route .s2b)
            (plainClaim setup.source.crypto codec setup.serverKeyId budget route .s2b) (g.1, g.2.castSucc) runtime) +
          beta setup codec route checks ensureInit bounds mode adversary budget (g.1, g.2.castSucc) runtime +
          authLoss setup codec checks route ensureInit bounds mode adversary budget (g.1, g.2.castSucc) runtime
              fallback caps qInit
            (slotted setup codec budget (plainEvent setup.source.crypto codec setup.serverKeyId budget route .s2b)
              (plainClaim setup.source.crypto codec setup.serverKeyId budget route .s2b) (g.1, g.2.castSucc))) :=
  (PqxdhDeploymentHeadlineContain.chance_mono _ _ _ fun outcome held => happens_mono _ _
    (plainEvery_plain setup.source.crypto codec setup.serverKeyId budget route .s2b) outcome held).trans
    (ce_plain_s2b setup functional codec checks route ensureInit phase1 phase2 correct caps bounded qInit initBound
      frameReadBack bounds mode adversary budget respects runtime fallback)

/-- With the ideal environment of the target of `g`, the probability that the record lift's view of `idealAuth` ends with `dec_g ∧ ISs_g` of the b2s origin failure with every computational field is at most `publicationTerm budget`: the unpublished-accept part is the frozen bound and the pin and plaintext parts have probability zero (AG, with the pin facts `PqxdhDeploymentHeadlinePinInvariant.idealAuth_pinFacts` and the plaintext facts `idealAuth_plainFacts`). -/
theorem idealAuth_originFields_le (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (caps : KemCaps) (bounded : KemBound setup caps)
    (ensureInit : StateT A ProbComp Bool) (qInit : ℕ)
    (initBound : ∀ state, (ensureInit.run state).IsTotalQueryBound qInit)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec)
    (frameReadBack : PqxdhServerAuthNegativeControl.FrameReadBack codec) (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) (budget : Budget) (respects : budget.Respects adversary)
    (g : Fin budget.accept × Fin budget.capacity) (runtime : A) :
    𝒟[serverSlotted setup codec budget (originFieldsEvent setup.source.crypto codec setup.serverKeyId budget route)
        (originFieldsClaim setup.source.crypto codec setup.serverKeyId budget route) g <$>
      (ctxView <$> idealAuth setup codec route
        (PqxdhDeploymentIdealEnv.envGD setup codec checks (Target.ofCE budget g) ensureInit 0 runtime)
        setup.serverKeyId bounds mode adversary)] {true} ≤ publicationTerm budget := by
  have final := PqxdhDeploymentHeadlineOrigin.unpublished_final setup codec checks route caps bounded ensureInit qInit
    initBound frameReadBack bounds mode adversary budget respects g runtime
  have zero := PqxdhDeploymentHeadlineAgree.agreement_statement setup codec route setup.serverKeyId bounds 2
    (PqxdhDeploymentIdealEnv.envGD setup codec checks (Target.ofCE budget g) ensureInit 0 runtime) mode adversary
  rw [Functor.map_map] at final ⊢
  calc _ ≤ 𝒟[(fun result => PqxdhRecordLiftIdeal.unpublishedEvent codec route (ctxView result) ||
        agreeEvent codec route result) <$> idealAuth setup codec route
          (PqxdhDeploymentIdealEnv.envGD setup codec checks (Target.ofCE budget g) ensureInit 0 runtime)
          setup.serverKeyId bounds mode adversary] {true} :=
        chance_mono_support _ _ _ fun result member held => by
          rcases originFields_contain setup codec budget route phase2 g result
            (PqxdhDeploymentHeadlinePinInvariant.idealAuth_pinFacts setup codec checks route (Target.ofCE budget g)
              ensureInit 0 runtime bounds mode adversary result member)
            (idealAuth_plainFacts setup codec route frameReadBack _ setup.serverKeyId bounds mode adversary result
              member) held with unpublished | failure
          · simp only [unpublished, Bool.true_or]
          · simp only [agreeEvent, failure, decide_true, Bool.or_true]
    _ ≤ _ := chance_or_le _ _ _
    _ ≤ publicationTerm budget := by
        rw [zero, add_zero]
        exact final

/-- **CE-OR b2s with every computational field, per target** (design-v2 sections 4.2 and 7.6): the probability that the deployment experiment ends with a b2s origin failure, a Server pin failure or a b2s plaintext failure whose claimed receiving Server peer designates `g` is at most `kemLoss + slotLoss + authLoss_g(dec_g ∧ ISs_g) + publicationTerm budget`, each with coefficient one; no anomaly term. -/
theorem ce_or_fields_b2s_target (setup : Setup baseSpec KemSK)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem)
    (codec : Codec Reader Response) (checks : Checks) (route : RawCtxServerRouting.SenderDecoder)
    (ensureInit : StateT A ProbComp Bool) (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec)
    (correct : PqxdhFullSecretInputKdf.SourceFullCorrect setup.source setup.hmac) (caps : KemCaps)
    (bounded : KemBound setup caps) (qInit : ℕ) (initBound : ∀ state, (ensureInit.run state).IsTotalQueryBound qInit)
    (frameReadBack : PqxdhServerAuthNegativeControl.FrameReadBack codec)
    (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) (budget : Budget) (respects : budget.Respects adversary) (runtime : A)
    (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery) (g : Fin budget.accept × Fin budget.capacity) :
    𝒟[(fun outcome => decide (happens (originFieldsEvent setup.source.crypto codec setup.serverKeyId budget route)
        outcome = true ∧ designated setup.source.crypto codec setup.serverKeyId budget
          (originFieldsClaim setup.source.crypto codec setup.serverKeyId budget route) outcome = some g)) <$>
      (PqxdhDeploymentSecrecy.game setup codec checks route ensureInit 0 bounds mode adversary).run runtime] {true} ≤
      ENNReal.ofReal (kemLoss setup codec checks route ensureInit bounds mode adversary budget
        (originFieldsEvent setup.source.crypto codec setup.serverKeyId budget route)
        (originFieldsClaim setup.source.crypto codec setup.serverKeyId budget route) g runtime) +
      ENNReal.ofReal (slotLoss setup codec checks route ensureInit bounds mode adversary budget
        (originFieldsEvent setup.source.crypto codec setup.serverKeyId budget route)
        (originFieldsClaim setup.source.crypto codec setup.serverKeyId budget route) g runtime) +
      authLoss setup codec checks route ensureInit bounds mode adversary budget g runtime fallback caps qInit
        (serverSlotted setup codec budget (originFieldsEvent setup.source.crypto codec setup.serverKeyId budget route)
          (originFieldsClaim setup.source.crypto codec setup.serverKeyId budget route) g) +
      publicationTerm budget := by
  have chain := PqxdhDeploymentHeadlineChain.chain_server setup functional codec checks route ensureInit phase1 phase2
    correct bounds mode adversary budget respects (originFieldsEvent setup.source.crypto codec setup.serverKeyId
        budget route) (originFieldsClaim setup.source.crypto codec setup.serverKeyId budget route) g runtime
  have lift := PqxdhDeploymentHeadlineChain.auth_le setup codec checks route correct caps bounded ensureInit qInit
    initBound bounds mode adversary budget respects g runtime fallback
    (serverSlotted setup codec budget (originFieldsEvent setup.source.crypto codec setup.serverKeyId budget route)
        (originFieldsClaim setup.source.crypto codec setup.serverKeyId budget route) g)
  have final := idealAuth_originFields_le setup codec checks route caps bounded ensureInit qInit initBound phase2
    frameReadBack bounds mode adversary budget respects g runtime
  calc _ ≤ _ := chain
    _ ≤ ((publicationTerm budget +
          authLoss setup codec checks route ensureInit bounds mode adversary budget g runtime fallback caps qInit
            (serverSlotted setup codec budget (originFieldsEvent setup.source.crypto codec setup.serverKeyId budget
                route)
              (originFieldsClaim setup.source.crypto codec setup.serverKeyId budget route) g)) +
        ENNReal.ofReal (kemLoss setup codec checks route ensureInit bounds mode adversary budget
          (originFieldsEvent setup.source.crypto codec setup.serverKeyId budget route)
          (originFieldsClaim setup.source.crypto codec setup.serverKeyId budget route) g runtime)) +
        ENNReal.ofReal (slotLoss setup codec checks route ensureInit bounds mode adversary budget
          (originFieldsEvent setup.source.crypto codec setup.serverKeyId budget route)
          (originFieldsClaim setup.source.crypto codec setup.serverKeyId budget route) g runtime) :=
        add_le_add (add_le_add (lift.trans (add_le_add final le_rfl)) le_rfl) le_rfl
    _ = _ := by ring

/-- **CE-OR b2s with every computational field** (`ce_or_fields_b2s`, design-v2 sections 4.2 and 7.6): the probability that the deployment experiment ends with a b2s origin failure, a Server pin failure or a b2s plaintext failure is at most the sum over `g` in `Fin qAccept × Fin qCreate` (with `k` read in `Fin (qCreate + 1)`) of `kemLoss + slotLoss + authLoss_g(dec_g ∧ ISs_g) + publicationTerm budget`, each with coefficient one; no anomaly term. -/
theorem ce_or_fields_b2s (setup : Setup baseSpec KemSK)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem)
    (codec : Codec Reader Response) (checks : Checks) (route : RawCtxServerRouting.SenderDecoder)
    (ensureInit : StateT A ProbComp Bool) (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec)
    (correct : PqxdhFullSecretInputKdf.SourceFullCorrect setup.source setup.hmac) (caps : KemCaps)
    (bounded : KemBound setup caps) (qInit : ℕ) (initBound : ∀ state, (ensureInit.run state).IsTotalQueryBound qInit)
    (frameReadBack : PqxdhServerAuthNegativeControl.FrameReadBack codec)
    (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) (budget : Budget) (respects : budget.Respects adversary) (runtime : A)
    (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery) :
    𝒟[(fun outcome => happens (originFieldsEvent setup.source.crypto codec setup.serverKeyId budget route) outcome) <$>
      (PqxdhDeploymentSecrecy.game setup codec checks route ensureInit 0 bounds mode adversary).run runtime] {true} ≤
      ∑ g : Fin budget.accept × Fin budget.create,
        (ENNReal.ofReal (kemLoss setup codec checks route ensureInit bounds mode adversary budget
            (originFieldsEvent setup.source.crypto codec setup.serverKeyId budget route)
            (originFieldsClaim setup.source.crypto codec setup.serverKeyId budget route) (g.1, g.2.castSucc) runtime) +
          ENNReal.ofReal (slotLoss setup codec checks route ensureInit bounds mode adversary budget
            (originFieldsEvent setup.source.crypto codec setup.serverKeyId budget route)
            (originFieldsClaim setup.source.crypto codec setup.serverKeyId budget route) (g.1, g.2.castSucc) runtime) +
          authLoss setup codec checks route ensureInit bounds mode adversary budget (g.1, g.2.castSucc) runtime
              fallback caps qInit
            (serverSlotted setup codec budget (originFieldsEvent setup.source.crypto codec setup.serverKeyId budget
                route)
              (originFieldsClaim setup.source.crypto codec setup.serverKeyId budget route) (g.1, g.2.castSucc)) +
          publicationTerm budget) := by
  rw [PqxdhDeploymentHeadlineChain.split_named setup codec checks route ensureInit phase1 phase2 bounds mode adversary
    budget respects _ _ runtime (originFields_named setup.source.crypto codec setup.serverKeyId budget route)]
  exact Finset.sum_le_sum fun g _ => ce_or_fields_b2s_target setup functional codec checks route ensureInit phase1
    phase2 correct caps bounded qInit initBound frameReadBack bounds mode adversary budget respects runtime fallback
    (g.1, g.2.castSucc)

end Headline

end BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePlain

-- Axiom guards (generated)

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePlain.plain_named' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePlain.plain_named

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePlain.originPlain_named' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePlain.originPlain_named

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePlain.plainEvery_plain' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePlain.plainEvery_plain

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePlain.originFields_named' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePlain.originFields_named

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePlain.ctxRun_plainFacts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePlain.ctxRun_plainFacts

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePlain.idealAuth_plainFacts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePlain.idealAuth_plainFacts

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePlain.counterpart_slot' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePlain.counterpart_slot

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePlain.plain_core' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePlain.plain_core

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePlain.view_value' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePlain.view_value

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePlain.plain_agree_b2s' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePlain.plain_agree_b2s

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePlain.plain_agree_s2b' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePlain.plain_agree_s2b

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePlain.originPlain_contain_b2s' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePlain.originPlain_contain_b2s

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePlain.originPlain_contain_s2b' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePlain.originPlain_contain_s2b

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePlain.originFields_contain' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePlain.originFields_contain

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePlain.idealAuth_plain_b2s_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePlain.idealAuth_plain_b2s_zero

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePlain.idealAuth_plain_s2b_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePlain.idealAuth_plain_s2b_zero

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePlain.ce_plain_b2s_target' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePlain.ce_plain_b2s_target

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePlain.ce_plain_b2s' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePlain.ce_plain_b2s

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePlain.ce_plain_s2b_target' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePlain.ce_plain_s2b_target

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePlain.ce_plain_s2b' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePlain.ce_plain_s2b

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePlain.idealAuth_originPlain_b2s_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePlain.idealAuth_originPlain_b2s_le

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePlain.idealAuth_originPlain_s2b_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePlain.idealAuth_originPlain_s2b_le

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePlain.ce_or_plain_b2s_target' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePlain.ce_or_plain_b2s_target

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePlain.ce_or_plain_b2s' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePlain.ce_or_plain_b2s

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePlain.ce_or_plain_s2b_target' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePlain.ce_or_plain_s2b_target

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePlain.ce_or_plain_s2b' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePlain.ce_or_plain_s2b

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePlain.happens_mono' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePlain.happens_mono

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePlain.ce_plain_every_b2s' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePlain.ce_plain_every_b2s

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePlain.ce_plain_every_s2b' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePlain.ce_plain_every_s2b

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePlain.idealAuth_originFields_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePlain.idealAuth_originFields_le

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePlain.ce_or_fields_b2s_target' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePlain.ce_or_fields_b2s_target

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePlain.ce_or_fields_b2s' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePlain.ce_or_fields_b2s
