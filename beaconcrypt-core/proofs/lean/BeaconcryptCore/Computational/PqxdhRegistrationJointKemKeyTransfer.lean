import BeaconcryptCore.Computational.PqxdhRegistrationJointBeaconFinishOnce

/-!
# Theorem T8: the authenticated registration with ideal keys (item 2, stage S5)

This module composes theorem T5 in its opaque form (`PqxdhRegistrationJointKemRawOpaque.authenticated_selected_opaque`, theorem T6 applied) with theorem T7 at two slots (`PqxdhRegistrationJointBeaconFinishOnce.opaqueBranch_idealKeys_two`, stage T). The result, `authenticated_ideal_keys`, bounds the probability of T5's event (the decision holds, the selected KEM key was not revealed, and the selected raw accept is protected) in the real source run by the probability that the decision holds in the ideal-key branch `PqxdhRegistrationJointKemIdealKeys.idealKeysBranch` (H4 of the item 2 plan), plus T5's loss terms (the IND-CCA advantage of the KEM adversary, the KEM correctness error and the joint EUF-CMA advantages), plus the item 2 loss `idealKeysLoss`:

- `(qAccept + qFinish + qHmac) / 2^256` (stage S1c), valid only because the zero-key 192-byte Extract slice is modelled as a random oracle (route R1, owner decision 2), which also gives the hidden entries at distinct coordinates their mutual independence;
- the sum of two one-query HMAC-SHA-512 PRF advantages of reductions built from the candidate-free root client (stages S2 and T);
- the four key-schedule advantages of G2 on entry 0's distinguisher `entryD` (`PqxdhRegistrationJointKemSecondEntry.keyScheduleBound`): the Extract game on an independent uniform 32-byte input twice and the HMAC-SHA-512 PRF game twice.

`authenticated_all_ideal` is the same composition with stage S7 at two entries (every hidden entry holds 108 uniform bytes, `allIdealBranch`), and `authenticated_slots` its slot form through the first-touch allocator on `PqxdhRecordLiftInterface.Slot 2` (`slotGame 2`), the shape of the CE-11 hand-off.

The premises are T5's (`functional`, `shortRejects`, `certified`, `capacity`) and the functional contract `SourceFullCorrect setup.source setup.hmac`. The statements are one-sided because T5 is. They are real-to-ideal-key transfers of the registration segment for an arbitrary decision: they have no test query and are not secrecy theorems, and they cover no evolving key, skipped key, record replay or later record (item 2 plan sections 0 and 14). The bills of the reductions (T8b, stage S8) are not part of this module.
-/

open OracleComp OracleSpec ENNReal

set_option autoImplicit false
set_option maxRecDepth 100000

namespace BeaconcryptCore.Computational.PqxdhRegistrationJointKemKeyTransfer

open PqxdhKemIndCca PqxdhInitializerSecrecy PqxdhServerAuthExperiment PqxdhJointIdentity
open PqxdhSecretInputKdf (hmacPrfRealGame hmacPrfRandomGame)
open PqxdhFullSecretInputKdf (SourceFullCorrect)
open PqxdhCorrelatedExpandHybrid (indexedReduction)
open PqxdhRegistrationJointKemCommands (SourceSpec)
open PqxdhRegistrationJointKemRawOpaque (opaqueBranch)
open PqxdhRegistrationJointKemRootExpand (rootClient)
open PqxdhRegistrationJointKemEntryFactor (entryD)
open PqxdhRegistrationJointKemIdealKeys (idealKeysBranch)
open PqxdhRegistrationJointKemSecondEntry (keyScheduleBound entryDk allIdealBranch slotGame)

variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response A X : Type}

/-! ### The item 2 losses -/

/-- The item 2 loss of theorem T7 at two slots: the random-oracle term of stage S1c, two HMAC-SHA-512 PRF advantages of stage S2, and the four key-schedule advantages of G2 on entry 0's distinguisher. -/
noncomputable def idealKeysLoss (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes)
    (decision : X → Bool) (work : OracleComp (SourceSpec KemSK) X) (runtime : A)
    (count : Nat) (selected : Fin (count + 1)) (index : Nat)
    (budget : PqxdhRegistrationJointRevealCosts.SourceKind → Nat) : ℝ :=
  ((budget (.inl 3) + budget (.inl 5) + budget (.inl 6) : ℕ) : ℝ) / 2 ^ 256 +
    ∑ slot ∈ Finset.range 2,
      (hmacPrfRealGame setup.hmac (indexedReduction setup.hmac (rootClient (Reader := Reader) setup codec checks
        ensureInit supplied decision work runtime count selected index) slot)).boolDistance
        (hmacPrfRandomGame (indexedReduction setup.hmac (rootClient (Reader := Reader) setup codec checks ensureInit
          supplied decision work runtime count selected index) slot)) +
    keyScheduleBound setup.source setup.hmac
      (entryD (Reader := Reader) setup codec checks ensureInit supplied decision work runtime count selected index)

/-- The item 2 loss of stage S7 at two entries: as `idealKeysLoss`, with the key-schedule advantages of the first two fresh hidden entries. -/
noncomputable def allIdealLoss (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes)
    (decision : X → Bool) (work : OracleComp (SourceSpec KemSK) X) (runtime : A)
    (count : Nat) (selected : Fin (count + 1)) (index : Nat)
    (budget : PqxdhRegistrationJointRevealCosts.SourceKind → Nat) : ℝ :=
  ((budget (.inl 3) + budget (.inl 5) + budget (.inl 6) : ℕ) : ℝ) / 2 ^ 256 +
    ∑ slot ∈ Finset.range 2,
      (hmacPrfRealGame setup.hmac (indexedReduction setup.hmac (rootClient (Reader := Reader) setup codec checks
        ensureInit supplied decision work runtime count selected index) slot)).boolDistance
        (hmacPrfRandomGame (indexedReduction setup.hmac (rootClient (Reader := Reader) setup codec checks ensureInit
          supplied decision work runtime count selected index) slot)) +
    ∑ k ∈ Finset.range 2, keyScheduleBound setup.source setup.hmac
      (entryDk (Reader := Reader) setup codec checks ensureInit supplied decision work runtime count selected index k)

/-- Theorem T7 at two slots with its loss written as `idealKeysLoss`. -/
theorem idealKeys_loss (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes)
    (decision : X → Bool) (work : OracleComp (SourceSpec KemSK) X) (runtime : A)
    (count : Nat) (selected : Fin (count + 1)) (index : Nat)
    (budget : PqxdhRegistrationJointRevealCosts.SourceKind → Nat)
    (certified : ∀ source, work.IsQueryBoundP
      (fun query => PqxdhRegistrationJointRevealCosts.sourceKind (KemSK := KemSK) query = source) (budget source))
    (correct : SourceFullCorrect setup.source setup.hmac) :
    (opaqueBranch (Reader := Reader) setup codec checks ensureInit supplied decision work runtime count selected index
        false).boolDistance
      (idealKeysBranch (Reader := Reader) setup codec checks ensureInit supplied decision work runtime count selected
        index) ≤
      idealKeysLoss (Reader := Reader) setup codec checks ensureInit supplied decision work runtime count selected index
        budget :=
  PqxdhRegistrationJointBeaconFinishOnce.opaqueBranch_idealKeys_two setup codec checks ensureInit supplied decision work
    runtime count selected index budget certified correct

/-- Stage S7 at two entries with its loss written as `allIdealLoss`. -/
theorem allIdeal_loss (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes)
    (decision : X → Bool) (work : OracleComp (SourceSpec KemSK) X) (runtime : A)
    (count : Nat) (selected : Fin (count + 1)) (index : Nat)
    (budget : PqxdhRegistrationJointRevealCosts.SourceKind → Nat)
    (certified : ∀ source, work.IsQueryBoundP
      (fun query => PqxdhRegistrationJointRevealCosts.sourceKind (KemSK := KemSK) query = source) (budget source))
    (correct : SourceFullCorrect setup.source setup.hmac) :
    (opaqueBranch (Reader := Reader) setup codec checks ensureInit supplied decision work runtime count selected index
        false).boolDistance
      (allIdealBranch (Reader := Reader) setup codec checks ensureInit supplied decision work runtime count selected
        index) ≤
      allIdealLoss (Reader := Reader) setup codec checks ensureInit supplied decision work runtime count selected index
        budget :=
  PqxdhRegistrationJointBeaconFinishOnce.opaqueBranch_allIdeal_two setup codec checks ensureInit supplied decision work
    runtime count selected index budget certified correct

/-- Composition of T5's opaque form with a two-sided bound on the right: the event probability is bounded by the decision probability of the new game plus T5's loss and the new loss. -/
theorem compose_right {left branch ideal : ProbComp Bool} {loss : ℝ} {kemTerm euf : ℝ≥0∞}
    (first : 𝒟[left] {true} ≤ 𝒟[branch] {true} + kemTerm + euf)
    (second : branch.boolDistance ideal ≤ loss) :
    𝒟[left] {true} ≤ 𝒟[ideal] {true} + kemTerm + euf + ENNReal.ofReal loss := by
  calc 𝒟[left] {true} ≤ 𝒟[branch] {true} + kemTerm + euf := first
    _ ≤ (𝒟[ideal] {true} + ENNReal.ofReal (branch.boolDistance ideal)) + kemTerm + euf := by
        gcongr
        exact ProbComp.evalDist_apply_true_le_add_ofReal_boolDistance branch ideal
    _ ≤ (𝒟[ideal] {true} + ENNReal.ofReal loss) + kemTerm + euf := by
        gcongr
    _ = 𝒟[ideal] {true} + kemTerm + euf + ENNReal.ofReal loss := by ring

/-! ### Theorem T8 -/

/-- Theorem T8 (item 2, registration segment). The probability of T5's event in the real source run (the decision holds, the selected KEM key was not revealed, and the selected raw accept is protected) is at most the probability that the decision holds in the ideal-key branch, plus T5's IND-CCA advantage and KEM correctness error, plus the joint EUF-CMA advantages, plus the item 2 loss `idealKeysLoss`: `(qAccept + qFinish + qHmac) / 2^256`, two one-query HMAC-SHA-512 PRF advantages, and four key-schedule advantages on entry 0's distinguisher. The first item 2 term is valid only because the zero-key 192-byte Extract slice is modelled as a random oracle (route R1); without that idealization the step that removes the hidden entries' dependence on the KEM candidate would be the forbidden decorrelation. The bound is one-sided because T5 is. This is a real-to-ideal-key transfer of the registration segment for an arbitrary decision, not a secrecy theorem: it has no test query and covers no later record. -/
theorem authenticated_ideal_keys (setup : Setup baseSpec KemSK)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem)
    (codec : Codec Reader Response) (checks : Checks)
    (shortRejects : ∀ (publicKey : PqxdhEd25519EufCma.Ed25519PublicKey) bytes, bytes.length < 64 →
      setup.source.crypto.verify publicKey.toList bytes = none)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes) (count : Nat)
    (work : OracleComp (SourceSpec KemSK) X) (runtime : A) (index : Nat)
    (budget : PqxdhRegistrationJointRevealCosts.SourceKind → Nat)
    (certified : ∀ source, work.IsQueryBoundP
      (fun query => PqxdhRegistrationJointRevealCosts.sourceKind (KemSK := KemSK) query = source) (budget source))
    (capacity : (if supplied.isNone then 1 else 0) + budget (.inl 1) ≤ count + 1)
    (decision : X → Bool) (kemIndex : Fin (count + 1)) (chosenOwner : Nat) (fallback : Pqxdh.Bytes)
    (dynamicFallback : PqxdhDynamicIdentityRouting.DynamicForgery) (ordinaryFallback : Forgery)
    (correct : SourceFullCorrect setup.source setup.hmac) :
    (letI := Classical.propDecidable; 𝒟[(fun pair =>
        decide (PqxdhRegistrationJointKemRawBridge.Decided decision
            (PqxdhRegistrationJointInitializedReports.sourceResult pair.2) ∧
          PqxdhRegistrationJointKemRawBridge.GoodKem kemIndex
            (PqxdhRegistrationJointInitializedReports.sourceResult pair.2) ∧
          PqxdhRegistrationJointAcceptOrigin.Protected setup codec checks kemIndex pair.1)) <$>
      PqxdhRegistrationJointAcceptCutReports.split setup codec checks ensureInit supplied (count + 1) work index
        runtime] {true}) ≤
    𝒟[idealKeysBranch (Reader := Reader) setup codec checks ensureInit supplied decision work runtime count kemIndex
        index] {true} +
      ENNReal.ofReal ((setup.kem.IND_CCA_Advantage (runtimeOfImpl (kemAmbientImpl setup.baseImpl))
        (PqxdhRegistrationJointKemRawCertified.adversary setup codec checks ensureInit supplied decision work runtime
          count kemIndex index).toINDCCA).toReal +
        PqxdhRegistrationJointKemRawGame.correctnessError setup) +
      ∑ target : Fin (count + 1), advantage setup.joint
        (PqxdhRegistrationJointNativeOriginBound.reduction setup codec checks ensureInit supplied count
          (PqxdhRegistrationJointAcceptCut.selected work index chosenOwner fallback) runtime
          dynamicFallback ordinaryFallback target) +
      ENNReal.ofReal (idealKeysLoss (Reader := Reader) setup codec checks ensureInit supplied decision work runtime count
        kemIndex index budget) :=
  compose_right
    (PqxdhRegistrationJointKemRawOpaque.authenticated_selected_opaque setup functional codec checks shortRejects
      ensureInit supplied count work runtime index budget certified capacity decision kemIndex chosenOwner fallback
      dynamicFallback ordinaryFallback)
    (idealKeys_loss setup codec checks ensureInit supplied decision work runtime count kemIndex index budget certified
      correct)

/-- Theorem T8 with every hidden entry ideal (stage S7 at two entries): as `authenticated_ideal_keys`, with the game `allIdealBranch` and the loss `allIdealLoss`. One-sided because T5 is; not a secrecy theorem. -/
theorem authenticated_all_ideal (setup : Setup baseSpec KemSK)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem)
    (codec : Codec Reader Response) (checks : Checks)
    (shortRejects : ∀ (publicKey : PqxdhEd25519EufCma.Ed25519PublicKey) bytes, bytes.length < 64 →
      setup.source.crypto.verify publicKey.toList bytes = none)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes) (count : Nat)
    (work : OracleComp (SourceSpec KemSK) X) (runtime : A) (index : Nat)
    (budget : PqxdhRegistrationJointRevealCosts.SourceKind → Nat)
    (certified : ∀ source, work.IsQueryBoundP
      (fun query => PqxdhRegistrationJointRevealCosts.sourceKind (KemSK := KemSK) query = source) (budget source))
    (capacity : (if supplied.isNone then 1 else 0) + budget (.inl 1) ≤ count + 1)
    (decision : X → Bool) (kemIndex : Fin (count + 1)) (chosenOwner : Nat) (fallback : Pqxdh.Bytes)
    (dynamicFallback : PqxdhDynamicIdentityRouting.DynamicForgery) (ordinaryFallback : Forgery)
    (correct : SourceFullCorrect setup.source setup.hmac) :
    (letI := Classical.propDecidable; 𝒟[(fun pair =>
        decide (PqxdhRegistrationJointKemRawBridge.Decided decision
            (PqxdhRegistrationJointInitializedReports.sourceResult pair.2) ∧
          PqxdhRegistrationJointKemRawBridge.GoodKem kemIndex
            (PqxdhRegistrationJointInitializedReports.sourceResult pair.2) ∧
          PqxdhRegistrationJointAcceptOrigin.Protected setup codec checks kemIndex pair.1)) <$>
      PqxdhRegistrationJointAcceptCutReports.split setup codec checks ensureInit supplied (count + 1) work index
        runtime] {true}) ≤
    𝒟[allIdealBranch (Reader := Reader) setup codec checks ensureInit supplied decision work runtime count kemIndex
        index] {true} +
      ENNReal.ofReal ((setup.kem.IND_CCA_Advantage (runtimeOfImpl (kemAmbientImpl setup.baseImpl))
        (PqxdhRegistrationJointKemRawCertified.adversary setup codec checks ensureInit supplied decision work runtime
          count kemIndex index).toINDCCA).toReal +
        PqxdhRegistrationJointKemRawGame.correctnessError setup) +
      ∑ target : Fin (count + 1), advantage setup.joint
        (PqxdhRegistrationJointNativeOriginBound.reduction setup codec checks ensureInit supplied count
          (PqxdhRegistrationJointAcceptCut.selected work index chosenOwner fallback) runtime
          dynamicFallback ordinaryFallback target) +
      ENNReal.ofReal (allIdealLoss (Reader := Reader) setup codec checks ensureInit supplied decision work runtime count
        kemIndex index budget) :=
  compose_right
    (PqxdhRegistrationJointKemRawOpaque.authenticated_selected_opaque setup functional codec checks shortRejects
      ensureInit supplied count work runtime index budget certified capacity decision kemIndex chosenOwner fallback
      dynamicFallback ordinaryFallback)
    (allIdeal_loss setup codec checks ensureInit supplied decision work runtime count kemIndex index budget certified
      correct)

/-- Theorem T8 in the slot form at two slots: as `authenticated_all_ideal`, with the game `slotGame 2` (the first-touch allocator in front of the persistent lazy table on `PqxdhRecordLiftInterface.Slot 2`). -/
theorem authenticated_slots (setup : Setup baseSpec KemSK)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem)
    (codec : Codec Reader Response) (checks : Checks)
    (shortRejects : ∀ (publicKey : PqxdhEd25519EufCma.Ed25519PublicKey) bytes, bytes.length < 64 →
      setup.source.crypto.verify publicKey.toList bytes = none)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes) (count : Nat)
    (work : OracleComp (SourceSpec KemSK) X) (runtime : A) (index : Nat)
    (budget : PqxdhRegistrationJointRevealCosts.SourceKind → Nat)
    (certified : ∀ source, work.IsQueryBoundP
      (fun query => PqxdhRegistrationJointRevealCosts.sourceKind (KemSK := KemSK) query = source) (budget source))
    (capacity : (if supplied.isNone then 1 else 0) + budget (.inl 1) ≤ count + 1)
    (decision : X → Bool) (kemIndex : Fin (count + 1)) (chosenOwner : Nat) (fallback : Pqxdh.Bytes)
    (dynamicFallback : PqxdhDynamicIdentityRouting.DynamicForgery) (ordinaryFallback : Forgery)
    (correct : SourceFullCorrect setup.source setup.hmac) :
    (letI := Classical.propDecidable; 𝒟[(fun pair =>
        decide (PqxdhRegistrationJointKemRawBridge.Decided decision
            (PqxdhRegistrationJointInitializedReports.sourceResult pair.2) ∧
          PqxdhRegistrationJointKemRawBridge.GoodKem kemIndex
            (PqxdhRegistrationJointInitializedReports.sourceResult pair.2) ∧
          PqxdhRegistrationJointAcceptOrigin.Protected setup codec checks kemIndex pair.1)) <$>
      PqxdhRegistrationJointAcceptCutReports.split setup codec checks ensureInit supplied (count + 1) work index
        runtime] {true}) ≤
    𝒟[slotGame (Reader := Reader) setup codec checks ensureInit supplied decision work runtime count kemIndex index
        2] {true} +
      ENNReal.ofReal ((setup.kem.IND_CCA_Advantage (runtimeOfImpl (kemAmbientImpl setup.baseImpl))
        (PqxdhRegistrationJointKemRawCertified.adversary setup codec checks ensureInit supplied decision work runtime
          count kemIndex index).toINDCCA).toReal +
        PqxdhRegistrationJointKemRawGame.correctnessError setup) +
      ∑ target : Fin (count + 1), advantage setup.joint
        (PqxdhRegistrationJointNativeOriginBound.reduction setup codec checks ensureInit supplied count
          (PqxdhRegistrationJointAcceptCut.selected work index chosenOwner fallback) runtime
          dynamicFallback ordinaryFallback target) +
      ENNReal.ofReal (allIdealLoss (Reader := Reader) setup codec checks ensureInit supplied decision work runtime count
        kemIndex index budget) := by
  rw [PqxdhRegistrationJointBeaconFinishOnce.slotGame_two]
  exact authenticated_all_ideal setup functional codec checks shortRejects ensureInit supplied count work runtime index
    budget certified capacity decision kemIndex chosenOwner fallback dynamicFallback ordinaryFallback correct

end BeaconcryptCore.Computational.PqxdhRegistrationJointKemKeyTransfer

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemKeyTransfer.idealKeys_loss' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemKeyTransfer.idealKeys_loss

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemKeyTransfer.allIdeal_loss' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemKeyTransfer.allIdeal_loss

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemKeyTransfer.compose_right' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemKeyTransfer.compose_right

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemKeyTransfer.authenticated_ideal_keys' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemKeyTransfer.authenticated_ideal_keys

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemKeyTransfer.authenticated_all_ideal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemKeyTransfer.authenticated_all_ideal

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemKeyTransfer.authenticated_slots' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemKeyTransfer.authenticated_slots
