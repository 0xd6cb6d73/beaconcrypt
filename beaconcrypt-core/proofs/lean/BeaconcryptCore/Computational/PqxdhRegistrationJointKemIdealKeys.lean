import BeaconcryptCore.Computational.PqxdhRegistrationJointKemEntryFactor
import BeaconcryptCore.Computational.PqxdhKeyScheduleFromRoot

/-!
# The ideal-key branch and theorem T7 (item 2, stage S4b)

This module states theorem T7 of the item 2 plan, the registration-segment transfer from the opaque KEM-ideal branch of theorem T6 (`PqxdhRegistrationJointKemRawOpaque.opaqueBranch … false`, H0 of the plan) to the ideal-key branch `idealKeysBranch` (H4).

`idealKeysBranch` is `PqxdhServerAuthKeySchedule.uniformGame entryD`: the same key generation, prefix, challenger encapsulation, stopped router, CCA evaluation, stop status and decision as the opaque branch, with no KEM candidate drawn, and with the following private root semantics:

- every hidden read (the Server's selected private root on the challenge marker and every grouped Beacon finish on the challenge marker; identified by public handles only) reads one consistent table keyed by the 128-byte DH coordinates;
- entry 0, the first hidden coordinate in execution order, holds 108 uniform bytes `(key32 ‖ next32 ‖ nonce12, right32)`, which the Server build of the marked session and every Beacon finish at entry 0's coordinates consume through the factored forms of plan section 18 (`PqxdhServerAuthEntryFactor.factorServices` fields); the marked session's pending token holds the fixed placeholder root;
- every other hidden coordinate holds the 108-byte key-schedule output of a fresh uniform 32-byte root;
- every other root (other sessions, other KEM keys, known decapsulation results, the adversary's public HMAC on the zero-key 192-byte slice) reads the public lazily sampled table with real Expand, and every other HMAC/HKDF evaluation is the real function.

T7 (`opaqueBranch_idealKeys`) bounds the advantage between H0 and H4 by the sum of three groups of terms, each with coefficient one:

- `ε_rom = (qAccept + qFinish + qHmac) / 2^256` (stage S1c, `PqxdhRegistrationJointKemRomSplit.opaqueBranch_split`), a statistical term under the random-oracle model of the zero-key 192-byte Extract slice (route R1, extended to this line by owner decision 2). That step, which removes the hidden entries' dependence on the KEM candidate and their reachability by direct reads, is valid only because the slice is modelled as a random oracle; R1 also gives the hidden entries at distinct coordinates their mutual independence. Without that idealization it would be the forbidden decorrelation of Extract outputs at inputs sharing one secret 32-byte suffix;
- `ε_exp`, the sum over `slot < 1 + qFinish` of HMAC-SHA-512 PRF advantages of `PqxdhCorrelatedExpandHybrid.indexedReduction setup.hmac rootClient slot` (stage S2), each a one-query reduction; stage T (`PqxdhRegistrationJointBeaconFinishOnce`) restates the bound with 2 instead of `1 + qFinish`;
- `ε_ks`, the four key-schedule advantages of G2 (`PqxdhKeyScheduleFromRoot.fromRoot_bound`) on the distinguisher `entryD` (stages S3b and S4a): the Extract game on an independent uniform 32-byte input twice and the HMAC-SHA-512 PRF game twice (one and two challenge queries).

The premises are T5's source budget `certified` and the functional contract `SourceFullCorrect setup.source setup.hmac` (owner decision of 2026-10-06). The HMAC-SHA-512 PRF game and the Extract game on a uniform 32-byte key are the ordinary primitive games accepted by the owner; their advantages are explicit terms. T7 is two-sided. It is a transfer of the registration segment only (plan sections 0 and 14): it has no test query, it is not a secrecy theorem, and it covers neither evolving keys, skipped keys, record replay nor later records.
-/

open OracleComp OracleSpec ENNReal

set_option autoImplicit false
set_option maxRecDepth 100000

namespace BeaconcryptCore.Computational.PqxdhRegistrationJointKemIdealKeys

open PqxdhKemIndCca PqxdhInitializerSecrecy PqxdhServerAuthExperiment PqxdhJointIdentity
open PqxdhSecretInputKdf (hmacPrfRealGame hmacPrfRandomGame extractRealGame extractUniformGame RootOutput)
open PqxdhFullSecretInputKdf (SourceFullCorrect)
open PqxdhServerAuthKeySchedule (uniform32 initExtractReduction initExpandReduction stepExtractReduction
  stepExpandReduction rootHybrid)
open PqxdhCorrelatedExpandHybrid (indexedReduction)
open PqxdhRegistrationJointKemCommands (SourceSpec)
open PqxdhRegistrationJointKemRawOpaque (opaqueBranch)
open PqxdhRegistrationJointKemRootExpand (rootClient)
open PqxdhRegistrationJointKemEntryFactor (entryD)

variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response A X : Type}

/-- H4 of the plan: the ideal-key branch. Entry 0's 108 bytes are uniform; every other hidden entry holds the key-schedule output of a fresh uniform root; no KEM candidate is drawn. -/
noncomputable def idealKeysBranch (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes)
    (decision : X → Bool) (work : OracleComp (SourceSpec KemSK) X) (runtime : A)
    (count : Nat) (selected : Fin (count + 1)) (index : Nat) : ProbComp Bool :=
  PqxdhServerAuthKeySchedule.uniformGame (entryD (Reader := Reader) setup codec checks ensureInit supplied decision work
    runtime count selected index)

/-- Two games with equal output distributions have equal advantages against any game, on either side. -/
theorem advantage_left {left left' right : ProbComp Bool} (same : 𝒟[left] = 𝒟[left']) :
    left.boolDistAdvantage right = left'.boolDistAdvantage right := by
  unfold ProbComp.boolDistAdvantage
  rw [same]

/-- Stages S3b and S4b. The uniform-root world of stage S2 and the ideal-key branch are distinguishable with advantage at most the four key-schedule advantages of G2 on entry 0's distinguisher. -/
theorem uniform_idealKeys (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes)
    (decision : X → Bool) (work : OracleComp (SourceSpec KemSK) X) (runtime : A)
    (count : Nat) (selected : Fin (count + 1)) (index : Nat)
    (correct : SourceFullCorrect setup.source setup.hmac) :
    (PqxdhCorrelatedExpandHybrid.uniformGame (rootClient (Reader := Reader) setup codec checks ensureInit supplied
        decision work runtime count selected index)).boolDistAdvantage
      (idealKeysBranch (Reader := Reader) setup codec checks ensureInit supplied decision work runtime count selected
        index) ≤
      (extractRealGame setup.hmac uniform32 (initExtractReduction setup.source setup.hmac
          (entryD (Reader := Reader) setup codec checks ensureInit supplied decision work runtime count selected
            index))).boolDistAdvantage
          (extractUniformGame uniform32 (initExtractReduction setup.source setup.hmac
            (entryD (Reader := Reader) setup codec checks ensureInit supplied decision work runtime count selected
              index))) +
        (hmacPrfRealGame setup.hmac (initExpandReduction setup.source
          (entryD (Reader := Reader) setup codec checks ensureInit supplied decision work runtime count selected
            index))).boolDistAdvantage
          (hmacPrfRandomGame (initExpandReduction setup.source
            (entryD (Reader := Reader) setup codec checks ensureInit supplied decision work runtime count selected
              index))) +
        (extractRealGame setup.hmac uniform32 (stepExtractReduction setup.hmac
          (entryD (Reader := Reader) setup codec checks ensureInit supplied decision work runtime count selected
            index))).boolDistAdvantage
          (extractUniformGame uniform32 (stepExtractReduction setup.hmac
            (entryD (Reader := Reader) setup codec checks ensureInit supplied decision work runtime count selected
              index))) +
        (hmacPrfRealGame setup.hmac (stepExpandReduction
          (entryD (Reader := Reader) setup codec checks ensureInit supplied decision work runtime count selected
            index))).boolDistAdvantage
          (hmacPrfRandomGame (stepExpandReduction
            (entryD (Reader := Reader) setup codec checks ensureInit supplied decision work runtime count selected
              index))) := by
  rw [advantage_left (PqxdhRegistrationJointKemEntryFactor.uniformGame_entry setup codec checks ensureInit supplied
    decision work runtime count selected index)]
  exact PqxdhKeyScheduleFromRoot.fromRoot_bound setup.source setup.hmac correct _

/-- Theorem T7 (item 2, registration segment). The opaque KEM-ideal branch of theorem T6 (H0) and the ideal-key branch (H4) are distinguishable with advantage at most `(qAccept + qFinish + qHmac) / 2^256`, plus the sum of `1 + qFinish` one-query HMAC-SHA-512 PRF advantages of reductions built from the candidate-free root client, plus four key-schedule advantages (Extract on an independent uniform 32-byte input twice, HMAC-SHA-512 PRF twice) of reductions built from entry 0's distinguisher `entryD`. The first term is valid only because the zero-key 192-byte Extract slice is modelled as a random oracle (route R1): it pays for removing the hidden entries' dependence on the KEM candidate and their reachability by direct reads, and R1 also gives the hidden entries at distinct coordinates their mutual independence; without that idealization this step would be the forbidden decorrelation. The premises are T5's source budget and the functional contract `SourceFullCorrect`. This is a two-sided transfer of the registration segment, not a secrecy theorem: it has no test query and covers no later record. -/
theorem opaqueBranch_idealKeys (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes)
    (decision : X → Bool) (work : OracleComp (SourceSpec KemSK) X) (runtime : A)
    (count : Nat) (selected : Fin (count + 1)) (index : Nat)
    (budget : PqxdhRegistrationJointRevealCosts.SourceKind → Nat)
    (certified : ∀ source, work.IsQueryBoundP
      (fun query => PqxdhRegistrationJointRevealCosts.sourceKind (KemSK := KemSK) query = source) (budget source))
    (correct : SourceFullCorrect setup.source setup.hmac) :
    (opaqueBranch (Reader := Reader) setup codec checks ensureInit supplied decision work runtime count selected index
        false).boolDistAdvantage
      (idealKeysBranch (Reader := Reader) setup codec checks ensureInit supplied decision work runtime count selected
        index) ≤
      ((budget (.inl 3) + budget (.inl 5) + budget (.inl 6) : ℕ) : ℝ) / 2 ^ 256 +
        ∑ slot ∈ Finset.range (1 + budget (.inl 5)),
          (hmacPrfRealGame setup.hmac (indexedReduction setup.hmac (rootClient (Reader := Reader) setup codec checks
            ensureInit supplied decision work runtime count selected index) slot)).boolDistAdvantage
            (hmacPrfRandomGame (indexedReduction setup.hmac (rootClient (Reader := Reader) setup codec checks
              ensureInit supplied decision work runtime count selected index) slot)) +
        ((extractRealGame setup.hmac uniform32 (initExtractReduction setup.source setup.hmac
            (entryD (Reader := Reader) setup codec checks ensureInit supplied decision work runtime count selected
              index))).boolDistAdvantage
            (extractUniformGame uniform32 (initExtractReduction setup.source setup.hmac
              (entryD (Reader := Reader) setup codec checks ensureInit supplied decision work runtime count selected
                index))) +
          (hmacPrfRealGame setup.hmac (initExpandReduction setup.source
            (entryD (Reader := Reader) setup codec checks ensureInit supplied decision work runtime count selected
              index))).boolDistAdvantage
            (hmacPrfRandomGame (initExpandReduction setup.source
              (entryD (Reader := Reader) setup codec checks ensureInit supplied decision work runtime count selected
                index))) +
          (extractRealGame setup.hmac uniform32 (stepExtractReduction setup.hmac
            (entryD (Reader := Reader) setup codec checks ensureInit supplied decision work runtime count selected
              index))).boolDistAdvantage
            (extractUniformGame uniform32 (stepExtractReduction setup.hmac
              (entryD (Reader := Reader) setup codec checks ensureInit supplied decision work runtime count selected
                index))) +
          (hmacPrfRealGame setup.hmac (stepExpandReduction
            (entryD (Reader := Reader) setup codec checks ensureInit supplied decision work runtime count selected
              index))).boolDistAdvantage
            (hmacPrfRandomGame (stepExpandReduction
              (entryD (Reader := Reader) setup codec checks ensureInit supplied decision work runtime count selected
                index)))) :=
  (ProbComp.boolDistAdvantage_triangle _ _ _).trans (add_le_add
    (PqxdhRegistrationJointKemRootExpand.opaqueBranch_uniform setup codec checks ensureInit supplied decision work
      runtime count selected index budget certified)
    (uniform_idealKeys setup codec checks ensureInit supplied decision work runtime count selected index correct))

end BeaconcryptCore.Computational.PqxdhRegistrationJointKemIdealKeys

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemIdealKeys.advantage_left' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemIdealKeys.advantage_left

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemIdealKeys.uniform_idealKeys' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemIdealKeys.uniform_idealKeys

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemIdealKeys.opaqueBranch_idealKeys' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemIdealKeys.opaqueBranch_idealKeys
