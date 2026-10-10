-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhDeploymentHeadlineAgreeReceive

/-!
# AG: agreement of accepted hidden receives with a counterpart production (CE-12 P2b, design-v2 section 7.7)

`AgreementStatement` in `idealAuth` (design-v2 section 7.7): for every environment, observation mode and adversary, the probability that the run ends with an accepted raw receive on a handle that holds a hidden slot, whose decoded frame has no counterpart production agreeing with it in associated data and plaintext, is zero (`agreement_statement`). No premise, assumption or contract is needed; the same holds in every ideal CTX world (`ctxRun_agree_zero`, any assignment of the replay and random modes; `idealRecords_agree_zero`).

- A counterpart production (`Production control secret handle frame ad plaintext`) is a replay-dictionary seal at a label that `handle` owns, matching `frame` (sequence, sender and complete payload, `PqxdhRecordFactsOriginReplay.Matches`), whose frame `handle` produced (it is in the tagged produced-frame log, whether or not its writer succeeded), with record AD bytes `ad` and plaintext `plaintext`.
- `AgreeFailure codec route result`: some transcript entry is an accepted raw receive (`Entry.received` with a decryption) on a receiving handle (`PqxdhRecordLiftIdeal.receivingHandle`) that holds a hidden slot, with decoded frame `frame`, and there is no counterpart handle of that slot (`PqxdhRecordLiftIdeal.Counterpart`) with a production of `frame` whose AD bytes are both the receiving handle's and the producing handle's AD (`PqxdhDeploymentHeadlineAgreeSeal.handleAd`) and whose plaintext is the received plaintext. `agreeEvent` is its Boolean.
- `ctxRun_agreement` is the positive pointwise form on every supported outcome of every ideal CTX world. Its proof joins the receive side (`PqxdhDeploymentHeadlineAgreeReceive.ctxRun_entryAd`: the accepted receive matches a seal with the received plaintext and the receiving handle's AD), the dictionary origin of the frozen origin facts (`PqxdhRecordFactsOriginInvariant.ctxRun_dictionary_origin`: the seal's frame was produced by a handle that owns its label, the counterpart by `counterpart_of_opposite`) and the seal side (`PqxdhDeploymentHeadlineAgreeSeal.ctxRun_sealAd`: some owner of the label has the seal's AD), with `ownsLabel_unique` (one installed handle per slot and role, `PqxdhRecordLiftOrigins.Unique`) identifying the two owners. `ctxRun_agree` is its negated form.
- The identity form, the third ingredient: `associatedBytes_inj`, the injectivity of the extracted `build_associated_data` (Rust `beaconcrypt-core/src/pqxdh.rs:928-947`: fixed-width Ed25519-tagged Server identity, then Beacon identity, then the two domain strings) through `RawCtxServerRouting.associatedBytes_exact` and `Pqxdh.assocData_inj`; `ctxRun_peer_agreement` (a Server peer receive: its counterpart is an established Beacon owner holding the slot, which produced the frame from a seal with the received plaintext and the AD `associatedBytes(Server identity, peer identity)`, and whose installed shell AD is that AD), `ctxRun_owner_agreement` (the same for a Beacon owner receive with its Server peer counterpart), and `owner_pin` (an owner whose installed AD is a peer's AD carries exactly that peer's ordered identity pair: any pair from which the extracted builder produces the owner's AD bytes is the Server identity and the peer identity).

Not claimed here: a statement in the common deployment experiment. The record-lift view (`PqxdhRecordLiftIdeal.View`) and the CE observation (`PqxdhDeploymentKemTransfer.Observed`) carry neither handle ADs nor seal plaintexts, so the agreement is a fact about the full ideal-world outcome; turning the b2s Server-pin and mode-O plaintext rows of design-v2 section 7.6 computational additionally needs the CE environment's AD facts (an established owner's shell AD is the builder's output on its created pin and its own identity, and the Server identity is the one its build responses carry) and a containment of the corresponding CE events in `AgreeFailure` under the chain's designation and ideal-slot facts; this is recorded as the remainder of P2b step 3. No `PqxdhBoundary*` module is imported.
-/

open OracleComp OracleSpec ENNReal CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false

namespace BeaconcryptCore.Computational.PqxdhDeploymentHeadlineAgree
open CtxRomAuth AdaptiveCtxReceive
open PqxdhRecordLiftInterface PqxdhRecordLiftIdeal PqxdhRecordLiftFlat
open PqxdhRecordFactsOriginHandles PqxdhRecordFactsOriginReplay
open PqxdhDeploymentHeadlineAgreeSeal (handleAd)
open PqxdhDeploymentHeadlineAgreeReceive (AcceptedAd)
open PqxdhRecordLiftProtocolHistory (Safe Step)
open PqxdhRecordLiftWorldCompiler (Label StoredKernel LabeledKernel)
open PqxdhDeploymentInterface (Handle FrameTag Receiver Entry FreshBounds Mode ModeSpec)
variable {n : Nat} {ι KemSK Reader Response E X : Type} {baseSpec : OracleSpec ι}

/-- Injectivity of the extracted `build_associated_data` (design-v2 section 7.7): equal associated data of two ordered pairs of 32-byte identities forces equal Server identities and equal Beacon identities. -/
theorem associatedBytes_inj (server peer otherServer otherPeer : RawCtxServerRouting.Identity)
    (same : RawCtxServerRouting.associatedBytes server peer = RawCtxServerRouting.associatedBytes otherServer otherPeer) :
    server = otherServer ∧ peer = otherPeer := by
  have identities := Pqxdh.assocData_inj (by simp : (PqxdhRefinement.absBytes server).length = 32)
    (by simp : (PqxdhRefinement.absBytes peer).length = 32) (by simp : (PqxdhRefinement.absBytes otherServer).length = 32)
    (by simp : (PqxdhRefinement.absBytes otherPeer).length = 32)
    ((RawCtxServerRouting.associatedBytes_exact server peer).symm.trans
      (same.trans (RawCtxServerRouting.associatedBytes_exact otherServer otherPeer)))
  exact ⟨Subtype.ext ((PqxdhRefinement.absBytes_inj_iff _ _).mp identities.1),
    Subtype.ext ((PqxdhRefinement.absBytes_inj_iff _ _).mp identities.2)⟩

/-- On a source-reachable control, two handles that own the same label coincide: one installed handle per slot and role. -/
theorem ownsLabel_unique (control : PqxdhRecordLiftProtocol.Control n) (safe : Safe control) (label : Label n)
    (first second : Handle) (left : OwnsLabel control label first) (right : OwnsLabel control label second) :
    first = second := by
  have unique := safe.2.2
  cases first with
  | peer a =>
    cases second with
    | peer b => exact congrArg Handle.peer (unique.1 a b label.slot left.1 right.1)
    | owner b => exact absurd (left.2.symm.trans right.2) (by simp [handleDirection])
  | owner a =>
    cases second with
    | peer b => exact absurd (left.2.symm.trans right.2) (by simp [handleDirection])
    | owner b => exact congrArg Handle.owner (unique.2 a b label.slot left.1 right.1)

/-- A counterpart production of `frame`: a replay-dictionary seal at a label that `handle` owns, matching `frame`, whose frame `handle` produced, with record AD bytes `ad` and plaintext `plaintext`. -/
def Production (control : PqxdhRecordLiftProtocol.Control n) (secret : CtxPrivate n) (handle : Handle)
    (frame : PqxdhDeploymentNative.Frame) (ad plaintext : Pqxdh.Bytes) : Prop :=
  ∃ label entry, OwnsLabel control label handle ∧ entry ∈ (secret.keys label).1.successfulSeals ∧
    Matches frame entry ∧ (some handle, frame) ∈ secret.base.produced ∧
    entry.input.context.ad.bytes = ad ∧ entry.input.plaintext = plaintext

/-- AG's failure event (design-v2 section 7.7): some accepted raw receive on a handle holding a hidden slot has no counterpart production of its decoded frame whose AD bytes are both the receiving and the producing handle's AD and whose plaintext is the received plaintext. -/
def AgreeFailure (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (result : Client n E X × CtxPrivate n) : Prop :=
  ∃ value ∈ result.1.1, ∃ entry ∈ value.2.1.2.transcript, ∃ receiver raw decrypted handle slot frame,
    entry.received = some (receiver, raw, .Some decrypted) ∧ receivingHandle route receiver raw = some handle ∧
      handleSlot result.1.2 handle = some slot ∧ codec.frameRead raw = some frame ∧
      ¬∃ other ad, Counterpart (handleSlot result.1.2) slot handle other ∧
        Production result.1.2 result.2 other frame ad decrypted.plaintext ∧
        handleAd result.1.2 handle = some ad ∧ handleAd result.1.2 other = some ad

open Classical in
/-- AG's failure event as a Boolean of the ideal-world outcome. -/
noncomputable def agreeEvent (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (result : Client n E X × CtxPrivate n) : Bool :=
  decide (AgreeFailure codec route result)

/-- AG, pointwise: on every supported outcome of every ideal CTX world, every accepted raw receive on a handle holding a hidden slot has a counterpart production of its decoded frame with the received plaintext, whose AD bytes are both the receiving and the producing handle's AD. -/
theorem ctxRun_agreement (modes : Label n → KeyMode) (ideal : ∀ label, modes label ≠ .real)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (env : Environment n E) (serverKid : Std.U64) (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) (result : Client n E X × CtxPrivate n)
    (supported : result ∈ support (ctxRun modes replace setup codec route env serverKid bounds mode adversary))
    (value : PqxdhRegistrationJointServerBirth.ClientCreated Unit × (X × PqxdhDeploymentSecrecy.Ledger) × E)
    (valueMember : value ∈ result.1.1) (entry : Entry) (entryMember : entry ∈ value.2.1.2.transcript)
    (receiver : Receiver) (raw : Pqxdh.Bytes) (decrypted : RawCtxWholeOwner.Decrypted) (handle : Handle)
    (slot : Slot n) (frame : PqxdhDeploymentNative.Frame)
    (received : entry.received = some (receiver, raw, .Some decrypted))
    (routed : receivingHandle route receiver raw = some handle) (hidden : handleSlot result.1.2 handle = some slot)
    (decoded : codec.frameRead raw = some frame) :
    ∃ other ad, Counterpart (handleSlot result.1.2) slot handle other ∧
      Production result.1.2 result.2 other frame ad decrypted.plaintext ∧
      handleAd result.1.2 handle = some ad ∧ handleAd result.1.2 other = some ad := by
  obtain ⟨actualHandle, actualRouted, accepted⟩ := PqxdhDeploymentHeadlineAgreeReceive.ctxRun_entryAd modes ideal
    replace setup codec route env serverKid bounds mode adversary result supported value valueMember entry entryMember
    receiver raw decrypted received
  have handleEq : actualHandle = handle := Option.some.inj (actualRouted.symm.trans routed)
  subst actualHandle
  rcases accepted with known | ⟨label, installed, direction, actualFrame, actualDecoded, sealedEntry, member,
    matched, plaintext, receiverAd⟩
  · have absent := PqxdhRecordFactsOriginAccepted.known_no_slot result.1.2 handle known
    change handleSlot result.1.2 handle = some slot at hidden
    rw [absent] at hidden
    cases hidden
  · have slotEq : label.slot = slot := Option.some.inj (installed.symm.trans hidden)
    have frameEq : actualFrame = frame := Option.some.inj (actualDecoded.symm.trans decoded)
    subst actualFrame
    obtain ⟨sender, producedFrame, owns, produced, producedMatches⟩ :=
      PqxdhRecordFactsOriginInvariant.ctxRun_dictionary_origin modes ideal replace setup codec route
        env serverKid bounds mode adversary result supported label sealedEntry member
    have sameFrame := PqxdhRecordFactsOriginAccepted.matches_unique frame producedFrame sealedEntry matched producedMatches
    subst producedFrame
    obtain ⟨sealer, sealerOwns, sealerAd⟩ := PqxdhDeploymentHeadlineAgreeSeal.ctxRun_sealAd modes ideal replace setup
      codec route env serverKid bounds mode adversary result supported label sealedEntry member
    have safe := (PqxdhRecordFactsOriginInvariant.ctxRun_invariant modes ideal replace setup codec route env serverKid
      bounds mode adversary result supported).1
    have sealerEq : sealer = sender := ownsLabel_unique result.1.2 safe label sealer sender sealerOwns owns
    subst sealer
    have counterpart := counterpart_of_opposite result.1.2 label sender handle owns direction
    rw [slotEq] at counterpart
    exact ⟨sender, sealedEntry.input.context.ad.bytes, counterpart,
      ⟨label, sealedEntry, owns, member, matched, produced, rfl, plaintext⟩, receiverAd, sealerAd⟩

/-- No supported outcome of an ideal CTX world has an AG failure. -/
theorem ctxRun_agree (modes : Label n → KeyMode) (ideal : ∀ label, modes label ≠ .real)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (env : Environment n E) (serverKid : Std.U64) (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) (result : Client n E X × CtxPrivate n)
    (supported : result ∈ support (ctxRun modes replace setup codec route env serverKid bounds mode adversary)) :
    ¬AgreeFailure codec route result := by
  rintro ⟨value, valueMember, entry, entryMember, receiver, raw, decrypted, handle, slot, frame,
    received, routed, hidden, decoded, noAgreement⟩
  exact noAgreement (ctxRun_agreement modes ideal replace setup codec route env serverKid bounds mode adversary
    result supported value valueMember entry entryMember receiver raw decrypted handle slot frame received routed
    hidden decoded)

/-- The counterpart of a Server peer handle is a Beacon owner handle holding the slot. -/
theorem counterpart_peer (slots : Handle → Option (Slot n)) (slot : Slot n) (keyId : Std.U64) (other : Handle)
    (counterpart : Counterpart slots slot (.peer keyId) other) : ∃ owner, other = .owner owner ∧
      slots (.owner owner) = some slot := by
  cases other with
  | peer _ => exact False.elim counterpart
  | owner owner => exact ⟨owner, rfl, counterpart⟩

/-- An established owner whose installed AD is a Server peer's AD carries that peer's ordered identity pair: for every ordered pair of 32-byte identities from which the extracted `build_associated_data` produces the owner's installed AD bytes, the pair is the Server identity and the peer identity. -/
theorem owner_pin (server peer : RawCtxServerRouting.Identity) (shell : BeaconShell)
    (same : PqxdhRefinement.absBytes shell.associatedData = RawCtxServerRouting.associatedBytes server peer)
    (pin beacon : RawCtxServerRouting.Identity) (built : shell.associatedData = RawCtxServerRouting.associatedArray pin beacon) :
    pin = server ∧ beacon = peer := by
  apply associatedBytes_inj
  rw [← same, built]
  rfl

/-- AG for a Server peer receive: its counterpart is an established Beacon owner holding the slot that produced the decoded frame from a seal with the received plaintext and the AD `associatedBytes(Server identity, peer identity)`, and the owner's installed shell AD is that AD. -/
theorem ctxRun_peer_agreement (modes : Label n → KeyMode) (ideal : ∀ label, modes label ≠ .real)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (env : Environment n E) (serverKid : Std.U64) (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) (result : Client n E X × CtxPrivate n)
    (supported : result ∈ support (ctxRun modes replace setup codec route env serverKid bounds mode adversary))
    (value : PqxdhRegistrationJointServerBirth.ClientCreated Unit × (X × PqxdhDeploymentSecrecy.Ledger) × E)
    (valueMember : value ∈ result.1.1) (entry : Entry) (entryMember : entry ∈ value.2.1.2.transcript)
    (raw : Pqxdh.Bytes) (decrypted : RawCtxWholeOwner.Decrypted) (keyId : Std.U64) (slot : Slot n)
    (frame : PqxdhDeploymentNative.Frame)
    (received : entry.received = some (.server, raw, .Some decrypted)) (routed : route raw = some keyId)
    (hidden : handleSlot result.1.2 (.peer keyId) = some slot) (decoded : codec.frameRead raw = some frame) :
    ∃ server peer owner shell kernel, result.1.2.server = some server ∧ server.peers keyId = some peer ∧
      result.1.2.owners[owner]? = some (.established shell kernel) ∧
      handleSlot result.1.2 (.owner owner) = some slot ∧
      Production result.1.2 result.2 (.owner owner) frame
        (RawCtxServerRouting.associatedBytes server.identity peer.identity) decrypted.plaintext ∧
      PqxdhRefinement.absBytes shell.associatedData = RawCtxServerRouting.associatedBytes server.identity peer.identity := by
  obtain ⟨other, ad, counterpart, production, receiverAd, producerAd⟩ := ctxRun_agreement modes ideal replace setup
    codec route env serverKid bounds mode adversary result supported value valueMember entry entryMember .server raw
    decrypted (.peer keyId) slot frame received (by simp only [receivingHandle, routed, Option.map_some]) hidden decoded
  obtain ⟨owner, rfl, ownerSlot⟩ := counterpart_peer _ slot keyId other counterpart
  cases existing : result.1.2.server with
  | none => simp [handleAd, existing] at receiverAd
  | some server =>
    cases found : server.peers keyId with
    | none => simp [handleAd, existing, found] at receiverAd
    | some peer =>
      simp only [handleAd, existing, found, Option.bind_some, Option.map_some, Option.some.injEq] at receiverAd
      subst ad
      simp only [handleAd, Option.bind_eq_some_iff] at producerAd
      obtain ⟨phase, foundOwner, phaseAd⟩ := producerAd
      cases phase with
      | inactive _ => cases phaseAd
      | established shell kernel =>
        exact ⟨server, peer, owner, shell, kernel, rfl, found, foundOwner, ownerSlot, production,
          Option.some.inj phaseAd⟩

/-- The counterpart of a Beacon owner handle is a Server peer handle holding the slot. -/
theorem counterpart_owner (slots : Handle → Option (Slot n)) (slot : Slot n) (owner : Nat) (other : Handle)
    (counterpart : Counterpart slots slot (.owner owner) other) : ∃ keyId, other = .peer keyId ∧
      slots (.peer keyId) = some slot := by
  cases other with
  | peer keyId => exact ⟨keyId, rfl, counterpart⟩
  | owner _ => exact False.elim counterpart

/-- AG for a Beacon owner receive: its counterpart is a present Server peer holding the slot that produced the decoded frame from a seal with the received plaintext and the AD `associatedBytes(Server identity, peer identity)`, and the receiving owner's installed shell AD is that AD. -/
theorem ctxRun_owner_agreement (modes : Label n → KeyMode) (ideal : ∀ label, modes label ≠ .real)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (env : Environment n E) (serverKid : Std.U64) (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) (result : Client n E X × CtxPrivate n)
    (supported : result ∈ support (ctxRun modes replace setup codec route env serverKid bounds mode adversary))
    (value : PqxdhRegistrationJointServerBirth.ClientCreated Unit × (X × PqxdhDeploymentSecrecy.Ledger) × E)
    (valueMember : value ∈ result.1.1) (entry : Entry) (entryMember : entry ∈ value.2.1.2.transcript)
    (owner : Nat) (raw : Pqxdh.Bytes) (decrypted : RawCtxWholeOwner.Decrypted) (slot : Slot n)
    (frame : PqxdhDeploymentNative.Frame)
    (received : entry.received = some (.owner owner, raw, .Some decrypted))
    (hidden : handleSlot result.1.2 (.owner owner) = some slot) (decoded : codec.frameRead raw = some frame) :
    ∃ server keyId peer shell kernel, result.1.2.server = some server ∧ server.peers keyId = some peer ∧
      result.1.2.owners[owner]? = some (.established shell kernel) ∧
      handleSlot result.1.2 (.peer keyId) = some slot ∧
      Production result.1.2 result.2 (.peer keyId) frame
        (RawCtxServerRouting.associatedBytes server.identity peer.identity) decrypted.plaintext ∧
      PqxdhRefinement.absBytes shell.associatedData = RawCtxServerRouting.associatedBytes server.identity peer.identity := by
  obtain ⟨other, ad, counterpart, production, receiverAd, producerAd⟩ := ctxRun_agreement modes ideal replace setup
    codec route env serverKid bounds mode adversary result supported value valueMember entry entryMember (.owner owner)
    raw decrypted (.owner owner) slot frame received rfl hidden decoded
  obtain ⟨keyId, rfl, peerSlot⟩ := counterpart_owner _ slot owner other counterpart
  cases existing : result.1.2.server with
  | none => simp [handleAd, existing] at producerAd
  | some server =>
    cases found : server.peers keyId with
    | none => simp [handleAd, existing, found] at producerAd
    | some peer =>
      simp only [handleAd, existing, found, Option.bind_some, Option.map_some, Option.some.injEq] at producerAd
      subst ad
      simp only [handleAd, Option.bind_eq_some_iff] at receiverAd
      obtain ⟨phase, foundOwner, phaseAd⟩ := receiverAd
      cases phase with
      | inactive _ => cases phaseAd
      | established shell kernel =>
        exact ⟨server, keyId, peer, shell, kernel, rfl, found, foundOwner, peerSlot, production,
          Option.some.inj phaseAd⟩

/-- AG's failure event has probability zero in every ideal CTX world, for every environment, observation mode and adversary. -/
theorem ctxRun_agree_zero (modes : Label n → KeyMode) (ideal : ∀ label, modes label ≠ .real)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (env : Environment n E) (serverKid : Std.U64) (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) :
    𝒟[agreeEvent codec route <$> ctxRun modes replace setup codec route env serverKid bounds mode adversary] {true} = 0 := by
  rw [evalDist_apply_singleton]
  apply probOutput_eq_zero_of_not_mem_support
  rw [support_map]
  rintro ⟨result, supported, failing⟩
  simp only [agreeEvent, decide_eq_true_eq] at failing
  exact ctxRun_agree modes ideal replace setup codec route env serverKid bounds mode adversary result supported failing

section Targets
variable (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK) (codec : PqxdhServerAuthExperiment.Codec Reader Response)
  (route : RawCtxServerRouting.SenderDecoder) (serverKid : Std.U64) (bounds : FreshBounds)

/-- `AgreementStatement` (design-v2 section 7.7): in `idealAuth`, for every environment, observation mode and adversary, AG's failure event has probability zero. -/
def AgreementStatement (n : Nat) : Prop :=
  ∀ {E X : Type} (env : Environment n E) (mode : Mode) (adversary : OracleComp (ModeSpec mode) X),
    𝒟[agreeEvent codec route <$> idealAuth setup codec route env serverKid bounds mode adversary] {true} = 0

/-- **AG** (design-v2 section 7.7): `AgreementStatement` holds for every setup, codec, router, Server key ID, fresh bounds and slot count, with no premise. -/
theorem agreement_statement (n : Nat) : AgreementStatement setup codec route serverKid bounds n :=
  fun env mode adversary => ctxRun_agree_zero (fun _ => .replay) (by intro label; decide) id setup codec route env
    serverKid bounds mode adversary

/-- AG's failure event also has probability zero in `idealRecords`, in both observation modes. -/
theorem idealRecords_agree_zero (n : Nat) {E X : Type} (env : Environment n E) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) :
    𝒟[agreeEvent codec route <$> idealRecords setup codec route env serverKid bounds mode adversary] {true} = 0 :=
  ctxRun_agree_zero (fun _ => recordMode mode) (by intro label; cases mode <;> decide) id setup codec route env
    serverKid bounds mode adversary

end Targets

end BeaconcryptCore.Computational.PqxdhDeploymentHeadlineAgree

-- Axiom guards (generated)

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineAgree.associatedBytes_inj' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineAgree.associatedBytes_inj

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineAgree.ownsLabel_unique' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineAgree.ownsLabel_unique

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineAgree.ctxRun_agreement' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineAgree.ctxRun_agreement

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineAgree.ctxRun_agree' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineAgree.ctxRun_agree

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineAgree.counterpart_peer' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineAgree.counterpart_peer

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineAgree.owner_pin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineAgree.owner_pin

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineAgree.ctxRun_peer_agreement' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineAgree.ctxRun_peer_agreement

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineAgree.counterpart_owner' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineAgree.counterpart_owner

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineAgree.ctxRun_owner_agreement' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineAgree.ctxRun_owner_agreement

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineAgree.ctxRun_agree_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineAgree.ctxRun_agree_zero

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineAgree.agreement_statement' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineAgree.agreement_statement

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineAgree.idealRecords_agree_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineAgree.idealRecords_agree_zero
