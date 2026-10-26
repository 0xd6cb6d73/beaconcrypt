import BeaconcryptCore.Computational.PqxdhFirstRecordKeyBound
import BeaconcryptCore.Computational.PqxdhFirstRecordFinishBound
/-!
# First-record confidentiality without explicit game terms

This module states first-record left-or-right confidentiality (step S7) with every explicit game term bounded. `PqxdhFirstRecordConfidentiality.first_record_confidentiality` bounds the difference of the accepted pending masses of the two challenge bits by constructed-reduction losses, stop bounds, alias terms and two explicit games per bit, `keyGame` and `collGame`. `PqxdhFirstRecordKeyBound.first_record_confidentiality_key` replaces the two `keyGame` terms, and `first_record_confidentiality_complete` replaces the two `collGame` terms through `PqxdhFirstRecordFinishBound.coll_real`. Its premises are exactly those of `first_record_confidentiality`, and its right side contains only advantages of constructed reductions, the KEM correctness error inside the completed-branch loss, and explicit numbers. `first_record_confidentiality_complete_budget` does the same for `first_record_confidentiality_budget`, with the adversary's own per-kind budget `budget` in place of the certificates' post budgets. This module adds no premise, primitive law or cryptographic assumption.

The terms of the bound, for each challenge bit, are as follows.

`twinLoss` is the ordinary CTX privacy loss of the constructed key-free confidentiality client (`PqxdhFirstRecordConfidentiality.source_random`, through `AdaptiveCtxDynamicKnownBounds.selected_privacy`): the IND$ advantage of the constructed validation reduction, the hash-guessing term `qHash / 2^128`, twice the INT-CTXT advantages of the constructed attempt-indexed reductions, the raw-guessing term `qRaw / 2^512` and the IND$ advantage of the constructed view reduction. It compares the selected-key CTX source game of the client with its random view, and the two random views are equal (`random_views_equal`).

`PqxdhAdaptiveCoordinateSecrecy.targetLoss` is the HB-112 first-record target loss of the challenge-fixed post (`PqxdhFirstRecordTarget.pending_bound`): the authenticated-root event loss and the initial and evolving-chain losses of the key-last endpoint, each the advantage of a constructed reduction.

`PqxdhFirstRecordTarget.completedLoss` is the loss of the constant-`false` continuation of the HB-112 actual game (`PqxdhFirstRecordTarget.target_split`): the joint identity advantage, the KEM correctness error, the one-key IND-CCA advantage, the Extract advantage and one indexed HMAC-PRF advantage, each for its constructed reduction.

`PqxdhFirstRecordKeyBound.recoveryLoss` bounds `keyGame` (`key_bound`): the CTX key-recovery loss of the constructed candidate client, twice the sum of the IND$ advantage of its validation reduction, `(qHash + qCand) / 2^128` and the INT-CTXT advantages of its attempt-indexed reductions, where the candidate count comes from the certificate.

`(2 + qSend + 51 (qRaw + qFinish)) / 2^256` bounds `collGame` (`PqxdhFirstRecordFinishBound.coll_bound`): `2^-256` for the initial half alias of the CTX client, plus the target-free tagged bound `(1 + qSend + 51 (qRaw + qFinish)) / 2^256` of `PqxdhFirstRecordStopTagged.tagged_game_bound`, because a Beacon finish that makes a selected raw opening derives its receive material on a chain equal to the selected chain, which the tagged world logs.

`2 * (1 + qSend + 51 (qRaw + qFinish)) / 2^256` are the two nonce-repeat stop bounds of `PqxdhFirstRecordStopTagged.stop_bound`: one from the main chain (`PqxdhFirstRecordConfidentiality.stop_real`) and one from the key-last to compiled step of `key_bound` (`PqxdhFirstRecordKeyBound.keyRun_le`).

Finally, `4 / 2^256` collects the initial half-alias terms: one per bit in the main chain (`insCompiled_le_separated`, `insClient_le_separated`) and one per bit in `key_bound`.

Here `qSend`, `qRaw` and `qFinish` are the send, raw-receive and attempted-finish budgets of the certificate of the wrapper post `confPost adversary b β` in `first_record_confidentiality_complete`, and of the adversary's own budget, each challenge counted as one Beacon `b` send, in `first_record_confidentiality_complete_budget`. `qHash`, `qRaw` and `qCand` inside the losses are derived from the same certificates and the preparation hash budget. Messages are abstract byte strings that each side knows how to decode; no serialization-library behaviour is used.
-/
open OracleComp OracleSpec ENNReal CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhFirstRecordConfidentialityComplete
open PqxdhFirstRecordConfidentiality PqxdhFirstRecordKeyBound PqxdhFirstRecordFinishBound

section Complete
open PqxdhNativeSharedPrefix PqxdhInitialBeaconAmbient PqxdhSecretInputKdf PqxdhFullSecretInputKdf PqxdhJointKdfGame PqxdhJointKdf
open PqxdhCorrelatedExpand PqxdhCorrelatedExtractFamily RawCtxSelectedParentTable PqxdhSelectedFirstRecord
open PqxdhKemIndCca PqxdhEd25519EufCma PqxdhJointIdentity PqxdhStatefulPhase1EufCma PqxdhPhase2GeneratedDriver
open PqxdhPrivateKemSource PqxdhGeneratedBeaconState PqxdhAdaptiveAcceptedResult PqxdhPhase1AcceptanceOracle
open PqxdhFirstBeaconRecordIntegrity PqxdhFirstBeaconRecordCtx CtxRomAuth AdaptiveCtxSharedHash
open RawCtxSelectedAuthenticationObserver AdaptiveCtxDynamicKnownBounds AdaptiveCtxQueryBounds AdaptiveCtxReceive
open CtxNonceAeadIntCtxt CtxNonceAeadIndDollarValidation
variable {ι M P I K X Response A KemSK : Type} {baseSpec : OracleSpec ι} {S B : Nat}
variable (setup : StatefulPhase1Setup baseSpec)
    (env : PqxdhAuthenticatedRootExperiment.Environment setup M P I K X Response A S B)
    (callbacks : PqxdhSourceAuxiliary.Callbacks A)
    (baseImpl : QueryImpl baseSpec ProbComp) (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes) (primitives : Primitives)
    (program : Program baseSpec setup.Context S (B + 1))

local notation "env0" => PqxdhSourceSharedPreparation.environment setup env callbacks ∅

/-- First-record left-or-right confidentiality (S7) with no explicit game term. For any adversary against the full post-registration protocol (secrets sampled inside, HB-112 actual game) that chooses two equal-length plaintexts for the first send of Beacon `b`, the difference between the accepted pending masses of the two challenge bits is at most, for each bit: the confidentiality client's ordinary CTX privacy loss `twinLoss`, the HB-112 first-record target loss and completed-branch loss of the challenge-fixed post, the key-recovery loss `recoveryLoss` of the constructed candidate client, the finish-collision bound `(2 + qSend + 51 (qRaw + qFinish)) / 2^256`, twice the nonce-repeat stop bound `(1 + qSend + 51 (qRaw + qFinish)) / 2^256`, and `2 * 2^-256` for the initial half aliases; the budgets are the certificate post budgets `c0.postBudget` and `c1.postBudget` of the two wrapper posts. The premises are exactly those of `PqxdhFirstRecordConfidentiality.first_record_confidentiality`. -/
theorem first_record_confidentiality_complete (b : Fin (B + 1))
    (adversary : program.Selection → RustM (Option PqxdhServerRegistrationPublication.Response) →
      OracleComp (AdvSpec (SelectorSpec baseSpec) S (B + 1)) Bool)
    (c0 : PqxdhAuthenticatedRootBudgets.Certificate env0 baseImpl kem program (confPost adversary b false))
    (c1 : PqxdhAuthenticatedRootBudgets.Certificate env0 baseImpl kem program (confPost adversary b true))
    (compatible : PqxdhOptionalKemSource.HonestKeyCompatibility baseImpl kem (env0).native)
    (adapter : HasAttachedVerificationAdapter attachedVerify primitives.verify)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation kem) (hmac : HmacSha512) (correct : SourceFullCorrect (env0).source hmac)
    (fallback : PqxdhDynamicIdentityRouting.DynamicForgery) (ordinaryFallback : Forgery)
    (ctxFallback : ModifiedNonceAeadForgery) (qPrelude0 qPrelude1 : Nat)
    (prepareHash0 : PrepareHashBudget setup env callbacks baseImpl kem attachedVerify primitives program (confPost adversary b false)
      qPrelude0)
    (prepareHash1 : PrepareHashBudget setup env callbacks baseImpl kem attachedVerify primitives program (confPost adversary b true)
      qPrelude1)
    (small0 : 1 + postTotal setup env callbacks baseImpl kem program c0 < 2 ^ 96)
    (small1 : 1 + postTotal setup env callbacks baseImpl kem program c1 < 2 ^ 96) :
    |(𝒟[confGame setup env callbacks baseImpl kem attachedVerify primitives program b adversary false] {true}).toReal -
      (𝒟[confGame setup env callbacks baseImpl kem attachedVerify primitives program b adversary true] {true}).toReal| ≤
    (twinLoss setup env callbacks baseImpl kem attachedVerify primitives program (confPost adversary b false) b c0 ctxFallback
      qPrelude0).toReal +
    (twinLoss setup env callbacks baseImpl kem attachedVerify primitives program (confPost adversary b true) b c1 ctxFallback
      qPrelude1).toReal +
    (PqxdhAdaptiveCoordinateSecrecy.targetLoss env0 baseImpl kem attachedVerify primitives program
      (PqxdhFirstRecordTarget.unitPost program (confPost adversary b false)) (PqxdhFirstRecordTarget.unitTargets (firstBeacon b))
      (PqxdhFirstRecordTarget.certificate env0 baseImpl kem program (confPost adversary b false) c0) hmac fallback ordinaryFallback () +
    PqxdhFirstRecordTarget.completedLoss env0 baseImpl kem attachedVerify primitives program (confPost adversary b false) hmac fallback
      ordinaryFallback) +
    (PqxdhAdaptiveCoordinateSecrecy.targetLoss env0 baseImpl kem attachedVerify primitives program
      (PqxdhFirstRecordTarget.unitPost program (confPost adversary b true)) (PqxdhFirstRecordTarget.unitTargets (firstBeacon b))
      (PqxdhFirstRecordTarget.certificate env0 baseImpl kem program (confPost adversary b true) c1) hmac fallback ordinaryFallback () +
    PqxdhFirstRecordTarget.completedLoss env0 baseImpl kem attachedVerify primitives program (confPost adversary b true) hmac fallback
      ordinaryFallback) +
    ((2 + c0.postBudget (.inl .send) + 51 * (c0.postBudget (.inl .raw) + c0.postBudget (.inr 5)) : ℕ) : ℝ) / 2 ^ 256 +
    ((2 + c1.postBudget (.inl .send) + 51 * (c1.postBudget (.inl .raw) + c1.postBudget (.inr 5)) : ℕ) : ℝ) / 2 ^ 256 +
    (recoveryLoss setup env callbacks baseImpl kem attachedVerify primitives program (confPost adversary b false) b c0 ctxFallback
      qPrelude0).toReal +
    (recoveryLoss setup env callbacks baseImpl kem attachedVerify primitives program (confPost adversary b true) b c1 ctxFallback
      qPrelude1).toReal +
    2 * (((1 + c0.postBudget (.inl .send) + 51 * (c0.postBudget (.inl .raw) + c0.postBudget (.inr 5)) : ℕ) : ℝ) / 2 ^ 256) +
    2 * (((1 + c1.postBudget (.inl .send) + 51 * (c1.postBudget (.inl .raw) + c1.postBudget (.inr 5)) : ℕ) : ℝ) / 2 ^ 256) +
    4 / 2 ^ 256 := by
  have main := first_record_confidentiality_key setup env callbacks baseImpl kem attachedVerify primitives program b adversary c0 c1
    compatible adapter functional hmac correct fallback ordinaryFallback ctxFallback qPrelude0 qPrelude1 prepareHash0 prepareHash1
    small0 small1
  have coll0 := coll_real setup env callbacks baseImpl kem attachedVerify primitives program (confPost adversary b false) b c0
  have coll1 := coll_real setup env callbacks baseImpl kem attachedVerify primitives program (confPost adversary b true) b c1
  linarith

/-- First-record left-or-right confidentiality with the adversary's own budget and no explicit game term: `first_record_confidentiality_complete` for the certificates `confCertificate` built from a certificate of any post and the adversary's per-kind budget `budget`, each challenge counted as one Beacon `b` send. The numeric terms become `2 * (2 + budget send + 51 * (budget raw + budget finish)) / 2^256` for the finish collisions, `4 * (1 + budget send + 51 * (budget raw + budget finish)) / 2^256` for the stop bounds and `4 / 2^256` for the aliases. The premises are exactly those of `PqxdhFirstRecordConfidentiality.first_record_confidentiality_budget`. -/
theorem first_record_confidentiality_complete_budget (b : Fin (B + 1))
    (adversary : program.Selection → RustM (Option PqxdhServerRegistrationPublication.Response) →
      OracleComp (AdvSpec (SelectorSpec baseSpec) S (B + 1)) Bool)
    {post0 : PqxdhAuthenticatedRootExperiment.Post (baseSpec := baseSpec) program.Selection S (B + 1)}
    (c : PqxdhAuthenticatedRootBudgets.Certificate env0 baseImpl kem program post0)
    (budget : PqxdhPhase2SourceSchedulerBounds.Budget) (bounded : AdvBounded program b adversary budget)
    (compatible : PqxdhOptionalKemSource.HonestKeyCompatibility baseImpl kem (env0).native)
    (adapter : HasAttachedVerificationAdapter attachedVerify primitives.verify)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation kem) (hmac : HmacSha512) (correct : SourceFullCorrect (env0).source hmac)
    (fallback : PqxdhDynamicIdentityRouting.DynamicForgery) (ordinaryFallback : Forgery)
    (ctxFallback : ModifiedNonceAeadForgery) (qPrelude0 qPrelude1 : Nat)
    (prepareHash0 : PrepareHashBudget setup env callbacks baseImpl kem attachedVerify primitives program (confPost adversary b false)
      qPrelude0)
    (prepareHash1 : PrepareHashBudget setup env callbacks baseImpl kem attachedVerify primitives program (confPost adversary b true)
      qPrelude1)
    (small : 1 + ∑ kind, budget kind < 2 ^ 96) :
    |(𝒟[confGame setup env callbacks baseImpl kem attachedVerify primitives program b adversary false] {true}).toReal -
      (𝒟[confGame setup env callbacks baseImpl kem attachedVerify primitives program b adversary true] {true}).toReal| ≤
    (twinLoss setup env callbacks baseImpl kem attachedVerify primitives program (confPost adversary b false) b
      (confCertificate env0 baseImpl kem program c b adversary budget bounded false) ctxFallback qPrelude0).toReal +
    (twinLoss setup env callbacks baseImpl kem attachedVerify primitives program (confPost adversary b true) b
      (confCertificate env0 baseImpl kem program c b adversary budget bounded true) ctxFallback qPrelude1).toReal +
    (PqxdhAdaptiveCoordinateSecrecy.targetLoss env0 baseImpl kem attachedVerify primitives program
      (PqxdhFirstRecordTarget.unitPost program (confPost adversary b false)) (PqxdhFirstRecordTarget.unitTargets (firstBeacon b))
      (PqxdhFirstRecordTarget.certificate env0 baseImpl kem program (confPost adversary b false)
        (confCertificate env0 baseImpl kem program c b adversary budget bounded false)) hmac fallback ordinaryFallback () +
    PqxdhFirstRecordTarget.completedLoss env0 baseImpl kem attachedVerify primitives program (confPost adversary b false) hmac fallback
      ordinaryFallback) +
    (PqxdhAdaptiveCoordinateSecrecy.targetLoss env0 baseImpl kem attachedVerify primitives program
      (PqxdhFirstRecordTarget.unitPost program (confPost adversary b true)) (PqxdhFirstRecordTarget.unitTargets (firstBeacon b))
      (PqxdhFirstRecordTarget.certificate env0 baseImpl kem program (confPost adversary b true)
        (confCertificate env0 baseImpl kem program c b adversary budget bounded true)) hmac fallback ordinaryFallback () +
    PqxdhFirstRecordTarget.completedLoss env0 baseImpl kem attachedVerify primitives program (confPost adversary b true) hmac fallback
      ordinaryFallback) +
    2 * (((2 + budget (.inl .send) + 51 * (budget (.inl .raw) + budget (.inr 5)) : ℕ) : ℝ) / 2 ^ 256) +
    (recoveryLoss setup env callbacks baseImpl kem attachedVerify primitives program (confPost adversary b false) b
      (confCertificate env0 baseImpl kem program c b adversary budget bounded false) ctxFallback qPrelude0).toReal +
    (recoveryLoss setup env callbacks baseImpl kem attachedVerify primitives program (confPost adversary b true) b
      (confCertificate env0 baseImpl kem program c b adversary budget bounded true) ctxFallback qPrelude1).toReal +
    4 * (((1 + budget (.inl .send) + 51 * (budget (.inl .raw) + budget (.inr 5)) : ℕ) : ℝ) / 2 ^ 256) +
    4 / 2 ^ 256 := by
  have main := first_record_confidentiality_key_budget setup env callbacks baseImpl kem attachedVerify primitives program b adversary c
    budget bounded compatible adapter functional hmac correct fallback ordinaryFallback ctxFallback qPrelude0 qPrelude1 prepareHash0
    prepareHash1 small
  have coll0 := coll_real setup env callbacks baseImpl kem attachedVerify primitives program (confPost adversary b false) b
    (confCertificate env0 baseImpl kem program c b adversary budget bounded false)
  have coll1 := coll_real setup env callbacks baseImpl kem attachedVerify primitives program (confPost adversary b true) b
    (confCertificate env0 baseImpl kem program c b adversary budget bounded true)
  have budget0 : (confCertificate env0 baseImpl kem program c b adversary budget bounded false).postBudget = budget := rfl
  have budget1 : (confCertificate env0 baseImpl kem program c b adversary budget bounded true).postBudget = budget := rfl
  rw [budget0] at coll0
  rw [budget1] at coll1
  linarith

end Complete

end BeaconcryptCore.Computational.PqxdhFirstRecordConfidentialityComplete

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordConfidentialityComplete.first_record_confidentiality_complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordConfidentialityComplete.first_record_confidentiality_complete

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordConfidentialityComplete.first_record_confidentiality_complete_budget' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordConfidentialityComplete.first_record_confidentiality_complete_budget
