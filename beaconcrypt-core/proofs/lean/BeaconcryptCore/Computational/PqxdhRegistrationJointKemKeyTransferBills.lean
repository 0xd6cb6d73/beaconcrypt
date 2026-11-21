import BeaconcryptCore.Computational.PqxdhRegistrationJointKemRootCosts
import BeaconcryptCore.Computational.PqxdhRegistrationJointKemKeyTransfer

/-!
# Theorem T8b: the bills of the item 2 reductions (item 2, stage S5, second part)

Theorem T8 (`PqxdhRegistrationJointKemKeyTransfer.authenticated_ideal_keys`) charges T5's terms and the item 2 loss `idealKeysLoss`; `authenticated_all_ideal` charges `allIdealLoss`. Besides the statistical random-oracle term, these losses are advantages of constructed reductions: the two one-query HMAC-SHA-512 PRF reductions `indexedReduction setup.hmac rootClient slot` of stages S2 and T (slots 0 and 1), and the four G2 key-schedule reductions on the distinguisher `entryD` (or, for `allIdealLoss`, on `entryDk k` for `k < 2`). This module gives each of them its challenge-query count and its complete local bill, derived only from the source budget `certified` of theorem T5, `KemBound setup caps` and the runtime initialization bound `initBound` (stage S8, `PqxdhRegistrationJointKemRootCosts`):

- each PRF reduction makes one challenge query and at most `rootBill + 64 · 2` local uniform queries, and its real and random games draw at most `64 + rootBill + 64 · 2`, where `rootBill caps qInit supplied count budget` is the coin bill of the root client (`rootClient_coins`) and 2 its number of root requests (`PqxdhRegistrationJointBeaconFinishOnce.rootClient_two`);
- each key-schedule reduction has the counts and bills of `PqxdhServerAuthEntryFactor.EntryComponentBills` at the distinguisher bill `rootBill + 64` for `entryD` (`entryD_total`) and `rootBill + 216` for `entryDk k` (`entryDk_total`).

The bills are resource bounds: they make no security claim, and they add no premise to T8.
-/

open OracleComp OracleSpec ENNReal

set_option autoImplicit false
set_option maxRecDepth 100000

namespace BeaconcryptCore.Computational.PqxdhRegistrationJointKemKeyTransfer

open PqxdhKemIndCca PqxdhInitializerSecrecy PqxdhServerAuthExperiment PqxdhJointIdentity
open PqxdhSecretInputKdf (hmacPrfRealGame hmacPrfRandomGame IsHmacChallengeQuery)
open PqxdhSecretInputInitializer (IsHmacUniformQuery)
open PqxdhServerAuthSourceCosts (KemCaps KemBound)
open PqxdhCorrelatedExpandHybrid (indexedReduction)
open PqxdhRegistrationJointKemCommands (SourceSpec)
open PqxdhRegistrationJointKemRootExpand (rootClient)
open PqxdhRegistrationJointKemEntryFactor (entryD)
open PqxdhRegistrationJointKemSecondEntry (entryDk)
open PqxdhRegistrationJointKemRootCosts (rootBill)
open PqxdhRegistrationJointRevealCosts (SourceKind sourceKind)
open PqxdhServerAuthEntryFactor (EntryComponentBills)

variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response A X : Type}

/-- The bills of one PRF reduction of stage S2: one challenge query, `qCoins + 64 · 2` local uniform queries, and `64 + qCoins + 64 · 2` draws in each of its two games. -/
def PrfBills (hmac : PqxdhSecretInputKdf.HmacSha512) (client : OracleComp PqxdhCorrelatedExpand.RootSpec Bool)
    (slot qCoins : ℕ) : Prop :=
  (indexedReduction hmac client slot).IsQueryBoundP IsHmacChallengeQuery 1 ∧
    (indexedReduction hmac client slot).IsQueryBoundP IsHmacUniformQuery (qCoins + 64 * 2) ∧
    (hmacPrfRealGame hmac (indexedReduction hmac client slot)).IsTotalQueryBound (64 + qCoins + 64 * 2) ∧
    (hmacPrfRandomGame (indexedReduction hmac client slot)).IsTotalQueryBound (64 + qCoins + 64 * 2)

/-- The PRF reductions of stages S2 and T at every slot. -/
theorem prf_bills (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (caps : KemCaps) (bounded : KemBound setup caps) (ensureInit : StateT A ProbComp Bool)
    (qInit : Nat) (initBound : ∀ runtime, (ensureInit.run runtime).IsTotalQueryBound qInit)
    (supplied : Option Pqxdh.Bytes) (decision : X → Bool) (work : OracleComp (SourceSpec KemSK) X)
    (budget : SourceKind → ℕ)
    (certified : ∀ source, work.IsQueryBoundP (fun query => sourceKind (KemSK := KemSK) query = source) (budget source))
    (runtime : A) (count : Nat) (selected : Fin (count + 1)) (index : Nat) (slot : ℕ) :
    PrfBills setup.hmac (rootClient (Reader := Reader) setup codec checks ensureInit supplied decision work runtime count
      selected index) slot (rootBill caps qInit supplied count budget) := by
  have coins := PqxdhRegistrationJointKemRootCosts.rootClient_coins (Reader := Reader) setup codec checks caps bounded
    ensureInit qInit initBound supplied decision work budget certified runtime count selected index
  have roots := PqxdhRegistrationJointBeaconFinishOnce.rootClient_two (Reader := Reader) setup codec checks ensureInit
    supplied decision work runtime count selected index
  have queries := PqxdhCorrelatedExpandQueryBounds.indexed_bounds setup.hmac _ slot _ _ coins roots
  have games := PqxdhCorrelatedExpandQueryBounds.indexed_uniform_ledger setup.hmac _ slot _ _ coins roots
  exact ⟨queries.2, queries.1, games.1, games.2⟩

/-- Theorem T8b: every reduction of `idealKeysLoss` with its challenge-query counts and its complete bills, from `certified`, `KemBound setup caps` and `initBound`. -/
theorem idealKeys_bills (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (caps : KemCaps) (bounded : KemBound setup caps) (ensureInit : StateT A ProbComp Bool)
    (qInit : Nat) (initBound : ∀ runtime, (ensureInit.run runtime).IsTotalQueryBound qInit)
    (supplied : Option Pqxdh.Bytes) (decision : X → Bool) (work : OracleComp (SourceSpec KemSK) X)
    (budget : SourceKind → ℕ)
    (certified : ∀ source, work.IsQueryBoundP (fun query => sourceKind (KemSK := KemSK) query = source) (budget source))
    (runtime : A) (count : Nat) (selected : Fin (count + 1)) (index : Nat) :
    (∀ slot ∈ Finset.range 2, PrfBills setup.hmac (rootClient (Reader := Reader) setup codec checks ensureInit supplied
      decision work runtime count selected index) slot (rootBill caps qInit supplied count budget)) ∧
    EntryComponentBills setup.source setup.hmac (entryD (Reader := Reader) setup codec checks ensureInit supplied
      decision work runtime count selected index) (rootBill caps qInit supplied count budget + 64) :=
  ⟨fun slot _ => prf_bills setup codec checks caps bounded ensureInit qInit initBound supplied decision work budget
      certified runtime count selected index slot,
    PqxdhServerAuthEntryFactor.entry_component_bills setup.source setup.hmac _ _ fun value =>
      PqxdhRegistrationJointKemRootCosts.entryD_total setup codec checks caps bounded ensureInit qInit initBound
        supplied decision work budget certified runtime count selected index value⟩

/-- Theorem T8b for stage S7: every reduction of `allIdealLoss` with its challenge-query counts and its complete bills. -/
theorem allIdeal_bills (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (caps : KemCaps) (bounded : KemBound setup caps) (ensureInit : StateT A ProbComp Bool)
    (qInit : Nat) (initBound : ∀ runtime, (ensureInit.run runtime).IsTotalQueryBound qInit)
    (supplied : Option Pqxdh.Bytes) (decision : X → Bool) (work : OracleComp (SourceSpec KemSK) X)
    (budget : SourceKind → ℕ)
    (certified : ∀ source, work.IsQueryBoundP (fun query => sourceKind (KemSK := KemSK) query = source) (budget source))
    (runtime : A) (count : Nat) (selected : Fin (count + 1)) (index : Nat) :
    (∀ slot ∈ Finset.range 2, PrfBills setup.hmac (rootClient (Reader := Reader) setup codec checks ensureInit supplied
      decision work runtime count selected index) slot (rootBill caps qInit supplied count budget)) ∧
    ∀ k ∈ Finset.range 2, EntryComponentBills setup.source setup.hmac (entryDk (Reader := Reader) setup codec checks
      ensureInit supplied decision work runtime count selected index k) (rootBill caps qInit supplied count budget + 216) :=
  ⟨fun slot _ => prf_bills setup codec checks caps bounded ensureInit qInit initBound supplied decision work budget
      certified runtime count selected index slot,
    fun k _ => PqxdhServerAuthEntryFactor.entry_component_bills setup.source setup.hmac _ _ fun value =>
      PqxdhRegistrationJointKemRootCosts.entryDk_total setup codec checks caps bounded ensureInit qInit initBound
        supplied decision work budget certified runtime count selected index k value⟩

end BeaconcryptCore.Computational.PqxdhRegistrationJointKemKeyTransfer

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemKeyTransfer.prf_bills' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemKeyTransfer.prf_bills

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemKeyTransfer.idealKeys_bills' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemKeyTransfer.idealKeys_bills

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemKeyTransfer.allIdeal_bills' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemKeyTransfer.allIdeal_bills
