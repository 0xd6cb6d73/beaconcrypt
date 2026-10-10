-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhDeploymentHeadlineEvents

/-!
# The containments of the CE-12 headlines (CE-12 P1, design-v2 sections 4.2-4.5, step C8)

On every record-lift view (`PqxdhRecordLiftIdeal.View 2 E X`, for every environment state type `E`), the per-target decision `dec_g` of a CE event with its claim, together with `IdealSlots` of the target of `g` (`PqxdhDeploymentHeadlineChain.slotted`) or with its three Server-side conjuncts (`PqxdhDeploymentHeadlineChain.serverSlotted`), implies the record lift's public event of the final ideal-world fact:

- `designation_peer`, `designation_owner`: a Server peer designating `g` holds slot 0 and is the target's peer (Server converse and restriction); an owner designating `g` is owner `k` and holds a slot (Beacon converse).
- CE-OR: `origin_b2s` (b2s with `ServerSlots`) and `origin_s2b` (s2b with `IdealSlots`) imply `UnpublishedAccept` (`PqxdhRecordLiftIdeal.unpublishedEvent`): every counterpart of the receiving handle's slot is its CE counterpart `cpart`, which did not publish the frame before.
- CE-UKS: `uks_receiver` (with `ServerSlots`) and `uks_sender` (with `IdealSlots`) imply `CrossAccept` (`PqxdhRecordLiftIdeal.crossEvent`): the designated handle holds a slot, and record-lift partners of opposite roles in one slot are the CE partners, which the event excludes.
- CE-APP: `app_hit` (with `IdealSlots`) and `app_peer_hit` (with `ServerSlots`) imply `FreshHit` (`PqxdhRecordLiftIdeal.freshEvent`): the claimed fresh message's handle designates `g`, so it holds a slot.
- CE-LOR: `lor_hidden` (with `IdealSlots`) and `lor_peer_hidden` (with `ServerSlots`) imply `TestsHidden`: every admitted test handle designates `g`, so it holds a slot.
- `chance_mono`: a pointwise containment bounds the probability.

These are pointwise implications; no probability and no security claim is made here.
-/

open OracleComp OracleSpec ENNReal

set_option autoImplicit false

namespace BeaconcryptCore.Computational.PqxdhDeploymentHeadlineContain
open PqxdhServerAuthExperiment (Setup Codec)
open PqxdhDeploymentInterface (Handle Entry Budget)
open PqxdhDeploymentKemTransfer (Observed)
open PqxdhDeploymentIdealParams (Target)
open PqxdhDeploymentIdealTrace (IdealSlots peerOf)
open PqxdhDeploymentTranscript (designateIn)
open PqxdhDeploymentIdealHandoff (decisionOn viewObserved)
open PqxdhRecordLiftIdeal (View)
open PqxdhRecordLiftInterface (Slot)
open PqxdhDeploymentHeadlineChain (ServerSlots slotted serverSlotted)
open PqxdhDeploymentHeadlineEvents

/-! ### Designation and slots -/

section Designation
variable {Reader Response : Type} (crypto : Pqxdh.Crypto) (codec : Codec Reader Response)
  (serverKid : Aeneas.Std.U64) (budget : Budget)

/-- A Server peer designating `g` holds slot 0 and is the target's peer (the Server converse and the Server restriction). -/
theorem designation_peer (g : Fin budget.accept × Fin budget.capacity) (slots : Handle → Option (Slot 2))
    (transcript : List Entry) (keyId : Aeneas.Std.U64)
    (server : ServerSlots crypto codec serverKid (Target.ofCE budget g) slots transcript)
    (designated : designateIn crypto codec serverKid budget transcript (.peer keyId) = some g) :
    slots (.peer keyId) = some 0 ∧ peerOf (Target.ofCE budget g) transcript = some keyId := by
  have zero := server.2.2 keyId (PqxdhDeploymentKemTransfer.designateIn_some crypto codec serverKid budget transcript
    (.peer keyId) g designated)
  exact ⟨zero, (server.1 keyId 0 zero).2⟩

/-- An owner designating `g` is owner `k` and holds a slot (the Beacon converse). -/
theorem designation_owner (g : Fin budget.accept × Fin budget.capacity) (slots : Handle → Option (Slot 2))
    (transcript : List Entry) (owner : ℕ)
    (slotted : IdealSlots crypto codec serverKid (Target.ofCE budget g) slots transcript)
    (designated : designateIn crypto codec serverKid budget transcript (.owner owner) = some g) :
    owner = g.2.val ∧ (slots (.owner owner)).isSome := by
  have pair := PqxdhDeploymentKemTransfer.designateIn_some crypto codec serverKid budget transcript (.owner owner) g
    designated
  have same := (PqxdhDeploymentTranscript.designate_owner crypto codec serverKid transcript owner g.1.val g.2.val
    pair).1
  subst same
  exact ⟨rfl, slotted.2.2.2 pair⟩

/-- A designated handle holds a slot under `IdealSlots`. -/
theorem designation_slot (g : Fin budget.accept × Fin budget.capacity) (slots : Handle → Option (Slot 2))
    (transcript : List Entry) (handle : Handle)
    (slotted : IdealSlots crypto codec serverKid (Target.ofCE budget g) slots transcript)
    (designated : designateIn crypto codec serverKid budget transcript handle = some g) : (slots handle).isSome := by
  cases handle with
  | peer keyId =>
      rw [(designation_peer crypto codec serverKid budget g slots transcript keyId
        (PqxdhDeploymentHeadlineChain.idealSlots_server crypto codec serverKid _ slots transcript slotted)
        designated).1]
      rfl
  | owner owner => exact (designation_owner crypto codec serverKid budget g slots transcript owner slotted designated).2

end Designation

/-! ### Unpacking the per-target decision on a view -/

section Unpack
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response E X : Type}
  (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (budget : Budget)

/-- The per-target decision on a view: the view has a result, the event holds on its observation, and the claim names a handle designating `g`. -/
theorem decision_unpack {n : ℕ} (event : Observed X → Bool) (claim : Observed X → Option Handle)
    (g : Fin budget.accept × Fin budget.capacity) (view : View n E X)
    (held : (viewObserved view).any (decisionOn setup codec budget event claim g) = true) :
    ∃ value, view.result = some value ∧ event (value.1, value.2.1, view.produced) = true ∧
      ∃ handle, claim (value.1, value.2.1, view.produced) = some handle ∧
        designateIn setup.source.crypto codec setup.serverKeyId budget value.2.1.transcript handle = some g := by
  rcases view with ⟨_ | value, produced, raw, slots⟩
  · simp [viewObserved] at held
  · simp only [viewObserved, Option.map_some, Option.any_some, decisionOn, Bool.and_eq_true, decide_eq_true_eq,
      PqxdhDeploymentKemTransfer.target, Option.bind_eq_some_iff] at held
    obtain ⟨happened, handle, claimed, designated⟩ := held
    exact ⟨value, rfl, happened, handle, claimed, designated⟩

end Unpack

/-! ### The containments -/

section Contain
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response E X : Type}
  (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (budget : Budget)
  (route : RawCtxServerRouting.SenderDecoder)

/-- CE-OR, b2s (design-v2 section 4.2, `or_unpublished`): `dec_g ∧ ISs_g` of the b2s origin failure with its claim implies `UnpublishedAccept` on every view. The receiving Server peer designates `g`, so it holds slot 0 (Server converse); a counterpart of slot 0 is an owner holding slot 0, hence owner `k` (Beacon restriction), its CE counterpart. -/
theorem origin_b2s (g : Fin budget.accept × Fin budget.capacity) (view : View 2 E X)
    (held : serverSlotted setup codec budget (originEvent setup.source.crypto codec setup.serverKeyId budget route .b2s)
      (orClaim setup.source.crypto codec setup.serverKeyId budget route .b2s) g view = true) :
    PqxdhRecordLiftIdeal.unpublishedEvent codec route view = true := by
  classical
  unfold serverSlotted at held
  obtain ⟨decided, server⟩ := of_decide_eq_true held
  obtain ⟨value, found, _, handle, claimed, designated⟩ := decision_unpack setup codec budget _ _ g view decided
  have slots := server value found
  obtain ⟨before, entry, after, split, ⟨g', forged⟩, handled⟩ := firstHandle_some _ _ _ handle claimed
  obtain ⟨receiver, raw, decrypted, received, frame, receivedEq, routed, receives, designated', framed, unpublished⟩ :=
    forged
  simp only [receivedHandle, receivedEq, Option.bind_some, routed, Option.some.injEq] at handled
  subst handled
  rw [designated] at designated'
  cases designated'
  cases received with
  | owner _ => exact absurd receives (by simp [Direction.Receives])
  | peer keyId =>
      obtain ⟨zero, _⟩ := designation_peer setup.source.crypto codec setup.serverKeyId budget g view.slots
        value.2.1.transcript keyId slots designated
      unfold PqxdhRecordLiftIdeal.unpublishedEvent
      refine decide_eq_true ⟨value, found, before, entry, after, split, receiver, raw, decrypted, .peer keyId, 0, frame,
        receivedEq, routed, zero, framed, fun other counter => ?_⟩
      cases other with
      | peer _ => exact absurd counter id
      | owner owner =>
          have same := slots.2.1 owner 0 counter
          subst same
          exact unpublished (.owner g.2.val) rfl

/-- CE-OR, s2b (design-v2 section 4.2, `or_unpublished`): `dec_g ∧ IS_g` of the s2b origin failure with its claim implies `UnpublishedAccept` on every view. The receiving owner designates `g`, so it is owner `k` and holds a slot (Beacon converse); a counterpart of that slot is a Server peer holding it, hence slot 0 and the target's peer (Server restriction), its CE counterpart. -/
theorem origin_s2b (g : Fin budget.accept × Fin budget.capacity) (view : View 2 E X)
    (held : slotted setup codec budget (originEvent setup.source.crypto codec setup.serverKeyId budget route .s2b)
      (orClaim setup.source.crypto codec setup.serverKeyId budget route .s2b) g view = true) :
    PqxdhRecordLiftIdeal.unpublishedEvent codec route view = true := by
  classical
  unfold slotted at held
  obtain ⟨decided, ideal⟩ := of_decide_eq_true held
  obtain ⟨value, found, _, handle, claimed, designated⟩ := decision_unpack setup codec budget _ _ g view decided
  have slots := ideal value found
  obtain ⟨before, entry, after, split, ⟨g', forged⟩, handled⟩ := firstHandle_some _ _ _ handle claimed
  obtain ⟨receiver, raw, decrypted, received, frame, receivedEq, routed, receives, designated', framed, unpublished⟩ :=
    forged
  simp only [receivedHandle, receivedEq, Option.bind_some, routed, Option.some.injEq] at handled
  subst handled
  rw [designated] at designated'
  cases designated'
  cases received with
  | peer _ => exact absurd receives (by simp [Direction.Receives])
  | owner owner =>
      obtain ⟨_, holds⟩ := designation_owner setup.source.crypto codec setup.serverKeyId budget g view.slots
        value.2.1.transcript owner slots designated
      obtain ⟨slot, slotFound⟩ := Option.isSome_iff_exists.mp holds
      unfold PqxdhRecordLiftIdeal.unpublishedEvent
      refine decide_eq_true ⟨value, found, before, entry, after, split, receiver, raw, decrypted, .owner owner, slot,
        frame, receivedEq, routed, slotFound, framed, fun other counter => ?_⟩
      cases other with
      | owner _ => exact absurd counter id
      | peer keyId =>
          obtain ⟨_, peer⟩ := slots.1 keyId slot counter
          exact unpublished (.peer keyId) (by simp [cpart, peer])

/-- CE-UKS, receiver side (design-v2 section 4.3, `uks_cross`): `dec_g ∧ ISs_g` of the receiver-side UKS failure with its claim implies `CrossAccept` on every view. The receiving Server peer designates `g`, so it holds slot 0 and is the target's peer; record-lift partners of it are owners holding slot 0, hence owner `k`, its CE partner, which the event excludes. -/
theorem uks_receiver (g : Fin budget.accept × Fin budget.capacity) (view : View 2 E X)
    (held : serverSlotted setup codec budget (uksReceiverEvent setup.source.crypto codec setup.serverKeyId budget route)
      (uksReceiverClaim setup.source.crypto codec setup.serverKeyId budget route) g view = true) :
    PqxdhRecordLiftIdeal.crossEvent codec route view = true := by
  classical
  unfold serverSlotted at held
  obtain ⟨decided, server⟩ := of_decide_eq_true held
  obtain ⟨value, found, _, handle, claimed, designated⟩ := decision_unpack setup codec budget _ _ g view decided
  have slots := server value found
  obtain ⟨before, entry, after, split, ⟨g', witness⟩, handled⟩ := firstHandle_some _ _ _ handle claimed
  obtain ⟨receiver, raw, decrypted, keyId, sender, frame, receivedEq, routed, framed, published, designated',
    notPartners⟩ := witness
  simp only [receivedHandle, receivedEq, Option.bind_some, routed, Option.some.injEq] at handled
  subst handled
  rw [designated] at designated'
  cases designated'
  obtain ⟨zero, peer⟩ := designation_peer setup.source.crypto codec setup.serverKeyId budget g view.slots
    value.2.1.transcript keyId slots designated
  unfold PqxdhRecordLiftIdeal.crossEvent
  refine decide_eq_true ⟨value, found, entry, by rw [split]; simp, receiver, raw, decrypted, .peer keyId, sender, frame,
    receivedEq, routed, framed, published, Or.inl (by rw [zero]; rfl), ?_⟩
  rintro ⟨slot, slotFound, counter⟩
  rw [zero, Option.some.injEq] at slotFound
  subst slotFound
  cases sender with
  | peer _ => exact counter
  | owner owner =>
      have same := slots.2.1 owner 0 counter
      subst same
      exact notPartners (Or.inr ⟨rfl, by simp [peer]⟩)

/-- CE-UKS, sender side (design-v2 section 4.3): `dec_g ∧ IS_g` of the sender-side UKS failure with its claim implies `CrossAccept` on every view. The sending owner designates `g`, so it is owner `k` and holds a slot (Beacon converse); a record-lift partner of the receiving handle is then a Server peer holding the owner's slot, hence slot 0 and the target's peer, the owner's CE partner, which the event excludes. -/
theorem uks_sender (g : Fin budget.accept × Fin budget.capacity) (view : View 2 E X)
    (held : slotted setup codec budget (uksSenderEvent setup.source.crypto codec setup.serverKeyId budget route)
      (uksSenderClaim setup.source.crypto codec setup.serverKeyId budget route) g view = true) :
    PqxdhRecordLiftIdeal.crossEvent codec route view = true := by
  classical
  unfold slotted at held
  obtain ⟨decided, ideal⟩ := of_decide_eq_true held
  obtain ⟨value, found, _, handle, claimed, designated⟩ := decision_unpack setup codec budget _ _ g view decided
  have slots := ideal value found
  obtain ⟨before, entry, after, split, ⟨g', witness⟩, handled⟩ := firstHandle_some _ _ _ handle claimed
  obtain ⟨owner, encrypted, frame, publishedEq, framed, designated', other, otherMember, receiver, raw, decrypted,
    receiving, receivedEq, routed, rawFramed, notPartners⟩ := witness
  simp only [publishedHandle, publishedEq, Option.map_some, Option.some.injEq] at handled
  subst handled
  rw [designated] at designated'
  cases designated'
  obtain ⟨rfl, holds⟩ := designation_owner setup.source.crypto codec setup.serverKeyId budget g view.slots
    value.2.1.transcript owner slots designated
  have member : entry ∈ value.2.1.transcript := by
    rw [split]
    simp
  have published : PqxdhRecordLiftIdeal.PublishedBefore codec value.2.1.transcript (.owner g.2.val) frame :=
    ⟨encrypted, List.mem_filterMap.mpr ⟨entry, member, publishedEq⟩, framed⟩
  unfold PqxdhRecordLiftIdeal.crossEvent
  refine decide_eq_true ⟨value, found, other, otherMember, receiver, raw, decrypted, receiving, .owner g.2.val, frame,
    receivedEq, routed, rawFramed, published, Or.inr holds, ?_⟩
  rintro ⟨slot, slotFound, counter⟩
  cases receiving with
  | owner _ => exact counter
  | peer keyId =>
      obtain ⟨_, peer⟩ := slots.1 keyId slot slotFound
      exact notPartners (Or.inr ⟨rfl, by simp [peer]⟩)

/-- CE-APP (design-v2 section 4.4, `app_hit`): `dec_g ∧ IS_g` of the CE-APP win with its claim implies `FreshHit` on every view: the claimed fresh message's handle designates `g`, so it holds a slot. -/
theorem app_hit (appClaim : X → Option (Nat × Pqxdh.Bytes)) (g : Fin budget.accept × Fin budget.capacity)
    (view : View 2 E X)
    (held : slotted setup codec budget (appEvent setup.source.crypto codec setup.serverKeyId budget appClaim)
      (appHandle appClaim) g view = true) :
    PqxdhRecordLiftIdeal.freshEvent appClaim view = true := by
  classical
  unfold slotted at held
  obtain ⟨decided, ideal⟩ := of_decide_eq_true held
  obtain ⟨value, found, won, handle, claimed, designated⟩ := decision_unpack setup codec budget _ _ g view decided
  have slots := ideal value found
  unfold appEvent at won
  obtain ⟨index, guess, entry, claimEq, fresh, _, message⟩ := of_decide_eq_true won
  simp only [appHandle, claimEq, Option.bind_some, fresh, Option.map_some, Option.some.injEq] at claimed
  subst claimed
  unfold PqxdhRecordLiftIdeal.freshEvent
  exact decide_eq_true ⟨value, found, index, guess, entry, claimEq, fresh,
    designation_slot setup.source.crypto codec setup.serverKeyId budget g view.slots value.2.1.transcript _ slots
      designated, message⟩

/-- CE-APP on a Server peer (design-v2 section 4.4, `ce_app_server`): `dec_g ∧ ISs_g` of the Server-side CE-APP win with its claim implies `FreshHit` on every view. -/
theorem app_peer_hit (appClaim : X → Option (Nat × Pqxdh.Bytes)) (g : Fin budget.accept × Fin budget.capacity)
    (view : View 2 E X)
    (held : serverSlotted setup codec budget (appPeerEvent setup.source.crypto codec setup.serverKeyId budget appClaim)
      (appHandle appClaim) g view = true) :
    PqxdhRecordLiftIdeal.freshEvent appClaim view = true := by
  classical
  unfold serverSlotted at held
  obtain ⟨decided, server⟩ := of_decide_eq_true held
  obtain ⟨value, found, won, handle, claimed, designated⟩ := decision_unpack setup codec budget _ _ g view decided
  have slots := server value found
  unfold appPeerEvent at won
  obtain ⟨index, guess, entry, keyId, claimEq, fresh, peer, _, message⟩ := of_decide_eq_true won
  simp only [appHandle, claimEq, Option.bind_some, fresh, Option.map_some, Option.some.injEq] at claimed
  subst claimed
  rw [peer] at designated
  have zero := (designation_peer setup.source.crypto codec setup.serverKeyId budget g view.slots value.2.1.transcript
    keyId slots designated).1
  unfold PqxdhRecordLiftIdeal.freshEvent
  exact decide_eq_true ⟨value, found, index, guess, entry, claimEq, fresh, by rw [peer, zero]; rfl, message⟩

/-- CE-LOR (design-v2 section 4.5, `lor_hidden`): `dec_g ∧ IS_g` of the CE-LOR eligibility with its claim implies `TestsHidden` on every view: every admitted test handle designates `g`, so it holds a slot. -/
theorem lor_hidden (filter : List (PqxdhDeploymentInterface.PublicEntry .P) → Bool)
    (g : Fin budget.accept × Fin budget.capacity) (view : View 2 E X)
    (held : slotted setup codec budget (lorEligEvent setup.source.crypto codec setup.serverKeyId budget filter)
      lorClaim g view = true) :
    PqxdhRecordLiftIdeal.TestsHidden setup.source.crypto codec setup.serverKeyId view := by
  classical
  unfold slotted at held
  obtain ⟨decided, ideal⟩ := of_decide_eq_true held
  obtain ⟨value, found, eligible, handle, claimed, designated⟩ := decision_unpack setup codec budget _ _ g view decided
  have slots := ideal value found
  unfold lorEligEvent at eligible
  obtain ⟨g', tested, _, ⟨first, firstFound, firstDesignated⟩, admitted⟩ := of_decide_eq_true eligible
  simp only [lorClaim] at claimed
  rw [claimed, Option.some.injEq] at firstFound
  subst firstFound
  rw [designated, Option.some.injEq] at firstDesignated
  subst firstDesignated
  exact ⟨value, found, tested, fun before entry after testHandle left right split query admittedTest =>
    designation_slot setup.source.crypto codec setup.serverKeyId budget g view.slots value.2.1.transcript testHandle
      slots (admitted before entry after testHandle left right split query admittedTest)⟩

/-- CE-LOR on Server peers (design-v2 section 4.5, `ce_lor_server`): `dec_g ∧ ISs_g` of the Server-side CE-LOR eligibility with its claim implies `TestsHidden` on every view: every admitted test handle is a Server peer designating `g`, so it holds slot 0. -/
theorem lor_peer_hidden (filter : List (PqxdhDeploymentInterface.PublicEntry .P) → Bool)
    (g : Fin budget.accept × Fin budget.capacity) (view : View 2 E X)
    (held : serverSlotted setup codec budget (lorEligPeerEvent setup.source.crypto codec setup.serverKeyId budget filter)
      lorClaim g view = true) :
    PqxdhRecordLiftIdeal.TestsHidden setup.source.crypto codec setup.serverKeyId view := by
  classical
  unfold serverSlotted at held
  obtain ⟨decided, server⟩ := of_decide_eq_true held
  obtain ⟨value, found, eligible, handle, claimed, designated⟩ := decision_unpack setup codec budget _ _ g view decided
  have slots := server value found
  unfold lorEligPeerEvent at eligible
  obtain ⟨⟨g', tested, _, ⟨first, firstFound, firstDesignated⟩, admitted⟩, peers⟩ := of_decide_eq_true eligible
  simp only [lorClaim] at claimed
  rw [claimed, Option.some.injEq] at firstFound
  subst firstFound
  rw [designated, Option.some.injEq] at firstDesignated
  subst firstDesignated
  refine ⟨value, found, tested, fun before entry after testHandle left right split query admittedTest => ?_⟩
  obtain ⟨keyId, rfl⟩ := peers before entry after testHandle left right split query admittedTest
  rw [(designation_peer setup.source.crypto codec setup.serverKeyId budget g view.slots value.2.1.transcript keyId
    slots (admitted before entry after _ left right split query admittedTest)).1]
  rfl

end Contain

/-! ### Monotonicity of a pointwise containment -/

set_option linter.deprecated false in
/-- A Boolean observation that implies another on every outcome has at most its probability. -/
theorem chance_mono {α : Type} (run : ProbComp α) (first second : α → Bool)
    (implies : ∀ a, first a = true → second a = true) : 𝒟[first <$> run] {true} ≤ 𝒟[second <$> run] {true} := by
  rw [evalDist_apply_singleton, evalDist_apply_singleton, ← probEvent_eq_eq_probOutput, ← probEvent_eq_eq_probOutput,
    probEvent_map, probEvent_map]
  exact probEvent_mono fun a _ held => implies a held

end BeaconcryptCore.Computational.PqxdhDeploymentHeadlineContain

-- Axiom guards (generated)

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineContain.designation_peer' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineContain.designation_peer

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineContain.designation_owner' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineContain.designation_owner

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineContain.designation_slot' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineContain.designation_slot

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineContain.decision_unpack' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineContain.decision_unpack

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineContain.origin_b2s' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineContain.origin_b2s

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineContain.origin_s2b' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineContain.origin_s2b

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineContain.uks_receiver' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineContain.uks_receiver

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineContain.uks_sender' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineContain.uks_sender

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineContain.app_hit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineContain.app_hit

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineContain.app_peer_hit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineContain.app_peer_hit

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineContain.lor_hidden' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineContain.lor_hidden

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineContain.lor_peer_hidden' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineContain.lor_peer_hidden

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineContain.chance_mono' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineContain.chance_mono
