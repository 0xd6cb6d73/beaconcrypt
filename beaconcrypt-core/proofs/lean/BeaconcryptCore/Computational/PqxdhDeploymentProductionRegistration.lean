-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhDeploymentProductionTransfer
import BeaconcryptCore.Computational.PqxdhDeploymentServerAuth
import BeaconcryptCore.Computational.PqxdhDeploymentServerAuthBills
import BeaconcryptCore.Computational.PqxdhDeploymentServerAuthInjectiveGame
import BeaconcryptCore.Computational.PqxdhDeploymentPublishedTuple
import BeaconcryptCore.Computational.PqxdhDeploymentReplay
import BeaconcryptCore.Computational.PqxdhDeploymentRecordReplay

/-!
# Production composition of items 3 and 7: the registration-authentication and replay claims on the production source game

Second follow-up to `PqxdhDeploymentProductionHeadlines` (which stays as published). The published production modules restate the CE-12 headlines; the registration claims of item 3 are not CE-12 theorems and had no production form. Every theorem of this module except `support_zero` is the production form of a published registration-authentication or replay claim of item 3 that is stated over the CE experiment `PqxdhDeploymentSecrecy.game`, and keeps the frozen theorem's name:

- CE-A1 (CE-8, the initial-response origin of every Beacon): `a1_bound` (per creation index), `a1_sum` (over all Beacons, `A1At` form), `ce_a1` (the headline, `A1NoPinnedMatch`), `ce_a1_billed` (at the transported deployment budget), `injective_bound` (the injectivity loss `ε_inj`) and `ce_a1_injective` (with injectivity);
- CE-A2pub (CE-7, published-tuple provenance): `a2pub_owner_bound`, `a2pub_bound`; CE-R1' (CE-6, published-tuple replay): `r1prime_owner_bound`, `r1prime_bound`;
- CE-R1 (CE-6, registration replay, deterministic): `replay_game`; CE-C3 (CE-6, record replay, deterministic): `record_replay_game`.

Each is the frozen statement instantiated at the production codec `codec′ = PqxdhBoundaryRecordPrelude.withReader codec reader` and route `route′ = RawCtxFrameDecoding.sender reader.model` of item 7 and at the Server identity index 0 (the frozen CE-A1 forms other than the injective ones, `replay_game` and `record_replay_game` hold at every index). In the ten probability forms every probability of the CE experiment is replaced by the probability of the same event, read back through `PqxdhBoundaryDeployment.unwrap`, on the classical production source game `PqxdhBoundaryDeployment.sourceGame setup codec reader erased checks ensureInit 0 …` of PB-D (`PqxdhDeploymentProductionTransfer.chance`); the bound and the bills are the frozen ones word for word at codec′ and route′: the Server-authentication bounds `serverAuthBound` of the reductions `R_c` built from the compiled program at codec′ and route′ with their bills; `ε_inj`, the fixed collider advantage of the setup at `qCreate` (the sum over the identity indices `t ≤ qCreate` of the joint-use weak-EUF advantage of the collision reduction `B^coll_t = PqxdhDeploymentServerAuthInjective.collider setup.joint budget.create t`, which depends on neither the codec, the route nor the adversary, makes no signing and no static-DH query and at most `32·qCreate` uniform queries, its whole joint-use game at most `32·(qCreate + 1)`); and the joint-use weak-EUF advantages of the A2 client's reductions `PqxdhDeploymentProvenance.reduction` at codec′ and route′; all CE-model quantities at the production instance. In the two deterministic forms every outcome of the CE experiment is replaced by an outcome of the classical source game read back through `unwrap` (`support_zero`, from the published `PqxdhDeploymentProductionTransfer.observe_zero`), and the conclusion is the frozen one at codec′. Premises: the frozen ones at codec′ and route′, except that `Phase1ReadBack` and `Phase2ReadBack` are stated at `codec` and transported by `PqxdhBoundaryDeploymentStep.phase1_withReader` and `phase2_withReader` (`Iff.rfl`); `FrameReadBack`, `ReadWritable`, the X25519 class and scalar laws, `SourceFullCorrect`, `HasAttachedVerificationAdapter`, the KEM base caps, the reductions' query caps and `shortRejects` are carried exactly where the frozen theorem takes them; `replay_game` and `record_replay_game` take none. No form takes `DecoderAgreement`. CE-A2 itself (`PqxdhDeploymentProvenance.a2_bound`, `a2_generated_bound`) is stated over the report-instrumented compiled run, not over the CE experiment, and has no production form; its CE-experiment reading is CE-A2pub. No assumption or contract is added.
-/

open OracleComp OracleSpec ENNReal

set_option autoImplicit false

namespace BeaconcryptCore.Computational.PqxdhDeploymentProductionRegistration

variable {ι KemSK Reader Response Message Root A X : Type} {baseSpec : OracleSpec ι}

section Support
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhDeploymentInterface (FreshBounds Mode ModeSpec)

/-- Support transfer for the classical game at index 0 (from `PqxdhDeploymentProductionTransfer.observe_zero` with the identity observation): every outcome of the classical production source game, read back through `unwrap`, is an outcome of the CE experiment `PqxdhDeploymentSecrecy.game` at the production codec `withReader codec reader` and route `RawCtxFrameDecoding.sender reader.model`. -/
theorem support_zero (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (reader : RawCtxNativeFramePrelude.Reader Message Root) (erased : Aeneas.Std.Array Aeneas.Std.U8 357#usize)
    (checks : Checks) (ensureInit : StateT A ProbComp Bool) (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) (runtime : A) (outcome : PqxdhBoundaryDeployment.Outcome KemSK X × A)
    (supported : outcome ∈ support
      ((PqxdhBoundaryDeployment.sourceGame setup codec reader erased checks ensureInit 0 bounds mode adversary).run
        runtime)) :
    PqxdhBoundaryDeployment.unwrap outcome ∈ support ((PqxdhDeploymentSecrecy.game setup
      (PqxdhBoundaryRecordPrelude.withReader codec reader) checks (RawCtxFrameDecoding.sender reader.model) ensureInit 0
      bounds mode adversary).run runtime) := by
  have same := PqxdhDeploymentProductionTransfer.observe_zero setup codec reader erased checks ensureInit bounds mode
    adversary runtime id
  rw [id_map] at same
  rw [← same, support_map]
  exact ⟨outcome, supported, rfl⟩

end Support

section
open PqxdhDeploymentServerAuth
open OracleComp OracleSpec CoreModels Aeneas ENNReal
open Aeneas.Std hiding namespace core alloc
open PqxdhServerAuthExperiment PqxdhServerAuthEntryFactor PqxdhServerAuthSourceCosts
open PqxdhServerAuthBodyCosts PqxdhServerAuthGapDh PqxdhServerAuthAssumptions
open PqxdhSecretInputKdf PqxdhFullSecretInputKdf PqxdhEd25519EufCma CtxNonceAeadIntCtxt
open PqxdhJointIdentity
open PqxdhDeploymentInterface (FreshBounds ModeSpec Mode Budget)
open PqxdhDeploymentSecrecy (Ledger)
open PqxdhDeploymentCompile (Local)
open PqxdhDeploymentCompileSecrecy (compileFull mergeFull)
open PqxdhDeploymentServerAuthEvent (SourceEntry Reg regsOf regsOfSource summarizeReg accepted Matched Unmatched A1At
  protectedBinding)
open PqxdhDeploymentServerAuthChain (seedBinding seedInput)

/-- Production form of `PqxdhDeploymentServerAuth.a1_bound` (frozen: Theorem CE-A1 at one creation index `c`). The frozen statement at the production codec `withReader codec reader` and route `RawCtxFrameDecoding.sender reader.model`, with every probability of the CE experiment (`PqxdhDeploymentSecrecy.game`, index 0) replaced by the probability of the same event read back through `unwrap` on the classical source game `PqxdhBoundaryDeployment.sourceGame` (`PqxdhDeploymentProductionTransfer.chance`). Everything else in the conclusion (every bound term and every bills conjunct) is the frozen text at the production codec and route. The Phase 1 and Phase 2 read-back laws are stated at `codec` (`PqxdhBoundaryDeploymentStep.phase1_withReader`, `phase2_withReader`, `Iff.rfl`); every other premise is the frozen one at the production codec and route. The frozen theorem holds at every Server identity index; the production form is at index 0, as every production form. -/
theorem a1_bound (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (reader : RawCtxNativeFramePrelude.Reader Message Root) (erased : Aeneas.Std.Array Aeneas.Std.U8 357#usize)
    (checks : Checks) (caps : KemCaps) (bounded : KemBound setup caps) (ensureInit : StateT A ProbComp Bool)
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec)
    (frameBack : PqxdhServerAuthNegativeControl.FrameReadBack (PqxdhBoundaryRecordPrelude.withReader codec reader))
    (writable : PqxdhFirstBeaconRecordCanonical.ReadWritable (PqxdhBoundaryRecordPrelude.withReader codec
      reader).frameWrite (PqxdhBoundaryRecordPrelude.withReader codec reader).frameRead)
    (law : X25519ClassLaw setup.source.crypto) (spread : X25519ScalarSpread setup.source.crypto)
    (correct : SourceFullCorrect setup.source setup.hmac)
    (adapter : HasAttachedVerificationAdapter
      (fun identity => setup.source.crypto.verify identity.toList)
      setup.joint.verify)
    (bounds : FreshBounds) (mode : Mode) (adversary : OracleComp (ModeSpec mode) X) (runtime : A) (c : Nat)
    (qCoin Q qH qHash qTotal qFinish : Nat)
    (reductionCaps : ReductionCaps (reduction (KemSK := KemSK) setup (PqxdhBoundaryRecordPrelude.withReader codec
      reader) (RawCtxFrameDecoding.sender reader.model) bounds mode adversary c)
      qCoin Q qH qHash qTotal qFinish)
    (fallback : ModifiedNonceAeadForgery) (signatureFallback : PqxdhJointIdentity.Forgery) :
    (𝒟[(a1Decision setup (PqxdhBoundaryRecordPrelude.withReader codec reader) c ∘ PqxdhBoundaryDeployment.unwrap) <$>
        (PqxdhBoundaryDeployment.sourceGame setup codec reader erased checks ensureInit 0 bounds mode adversary).run
          runtime]
        {true}).toReal ≤
      serverAuthBound setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks caps
        (serverAuthAdversary setup (PqxdhBoundaryRecordPrelude.withReader codec reader)
          (RawCtxFrameDecoding.sender reader.model) bounds mode adversary c)
        qCoin Q qH qHash fallback signatureFallback ∧
    PqxdhServerAuthCommonAuthentication.ReductionBills setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
      caps
      (serverAuthAdversary setup (PqxdhBoundaryRecordPrelude.withReader codec reader)
        (RawCtxFrameDecoding.sender reader.model) bounds mode adversary c) qCoin Q qH qHash qTotal qFinish fallback
      signatureFallback := by
  simp only [PqxdhDeploymentProductionTransfer.chance]
  exact PqxdhDeploymentServerAuth.a1_bound setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks caps
      bounded (RawCtxFrameDecoding.sender reader.model) ensureInit 0
      ((PqxdhBoundaryDeploymentStep.phase1_withReader codec reader).mpr phase1)
      ((PqxdhBoundaryDeploymentStep.phase2_withReader codec reader).mpr phase2) frameBack writable law spread correct
      adapter bounds mode adversary runtime c qCoin Q qH qHash qTotal qFinish reductionCaps fallback signatureFallback

end

section
open PqxdhDeploymentServerAuth
open OracleComp OracleSpec CoreModels Aeneas ENNReal
open Aeneas.Std hiding namespace core alloc
open PqxdhServerAuthExperiment PqxdhServerAuthEntryFactor PqxdhServerAuthSourceCosts
open PqxdhServerAuthBodyCosts PqxdhServerAuthGapDh PqxdhServerAuthAssumptions
open PqxdhSecretInputKdf PqxdhFullSecretInputKdf PqxdhEd25519EufCma CtxNonceAeadIntCtxt
open PqxdhJointIdentity
open PqxdhDeploymentInterface (FreshBounds ModeSpec Mode Budget)
open PqxdhDeploymentSecrecy (Ledger)
open PqxdhDeploymentCompile (Local)
open PqxdhDeploymentCompileSecrecy (compileFull mergeFull)
open PqxdhDeploymentServerAuthEvent (SourceEntry Reg regsOf regsOfSource summarizeReg accepted Matched Unmatched A1At
  protectedBinding)
open PqxdhDeploymentServerAuthChain (seedBinding seedInput)

/-- Production form of `PqxdhDeploymentServerAuth.a1_sum` (frozen: Theorem CE-A1 over all Beacons, in the A1At form). The frozen statement at the production codec `withReader codec reader` and route `RawCtxFrameDecoding.sender reader.model`, with every probability of the CE experiment (`PqxdhDeploymentSecrecy.game`, index 0) replaced by the probability of the same event read back through `unwrap` on the classical source game `PqxdhBoundaryDeployment.sourceGame` (`PqxdhDeploymentProductionTransfer.chance`). Everything else in the conclusion (every bound term and every bills conjunct) is the frozen text at the production codec and route. The Phase 1 and Phase 2 read-back laws are stated at `codec` (`PqxdhBoundaryDeploymentStep.phase1_withReader`, `phase2_withReader`, `Iff.rfl`); every other premise is the frozen one at the production codec and route. The frozen theorem holds at every Server identity index; the production form is at index 0, as every production form. -/
theorem a1_sum (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (reader : RawCtxNativeFramePrelude.Reader Message Root) (erased : Aeneas.Std.Array Aeneas.Std.U8 357#usize)
    (checks : Checks) (caps : KemCaps) (bounded : KemBound setup caps) (ensureInit : StateT A ProbComp Bool)
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec)
    (frameBack : PqxdhServerAuthNegativeControl.FrameReadBack (PqxdhBoundaryRecordPrelude.withReader codec reader))
    (writable : PqxdhFirstBeaconRecordCanonical.ReadWritable (PqxdhBoundaryRecordPrelude.withReader codec
      reader).frameWrite (PqxdhBoundaryRecordPrelude.withReader codec reader).frameRead)
    (law : X25519ClassLaw setup.source.crypto) (spread : X25519ScalarSpread setup.source.crypto)
    (correct : SourceFullCorrect setup.source setup.hmac)
    (adapter : HasAttachedVerificationAdapter
      (fun identity => setup.source.crypto.verify identity.toList)
      setup.joint.verify)
    (bounds : FreshBounds) (mode : Mode) (adversary : OracleComp (ModeSpec mode) X) (budget : Budget)
    (respects : budget.Respects adversary) (runtime : A) (qCoin Q qH qHash qTotal qFinish : Nat)
    (reductionCaps : ∀ c, ReductionCaps (reduction (KemSK := KemSK) setup
      (PqxdhBoundaryRecordPrelude.withReader codec reader) (RawCtxFrameDecoding.sender reader.model) bounds mode
        adversary c)
      qCoin Q qH qHash qTotal qFinish)
    (fallback : ModifiedNonceAeadForgery) (signatureFallback : PqxdhJointIdentity.Forgery) :
    (𝒟[((fun outcome => @decide (∃ c, A1At setup (PqxdhBoundaryRecordPrelude.withReader codec reader) c outcome)
      (Classical.propDecidable _)) ∘ PqxdhBoundaryDeployment.unwrap) <$>
        (PqxdhBoundaryDeployment.sourceGame setup codec reader erased checks ensureInit 0 bounds mode adversary).run
          runtime]
        {true}).toReal ≤
      ∑ c : Fin budget.create, serverAuthBound setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks caps
        (serverAuthAdversary setup (PqxdhBoundaryRecordPrelude.withReader codec reader)
          (RawCtxFrameDecoding.sender reader.model) bounds mode adversary c) qCoin Q qH qHash fallback
            signatureFallback ∧
    ∀ c, PqxdhServerAuthCommonAuthentication.ReductionBills setup (PqxdhBoundaryRecordPrelude.withReader codec reader)
      checks caps
      (serverAuthAdversary setup (PqxdhBoundaryRecordPrelude.withReader codec reader)
        (RawCtxFrameDecoding.sender reader.model) bounds mode adversary c) qCoin Q qH qHash qTotal qFinish fallback
      signatureFallback := by
  simp only [PqxdhDeploymentProductionTransfer.chance]
  exact PqxdhDeploymentServerAuth.a1_sum setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks caps bounded
      (RawCtxFrameDecoding.sender reader.model) ensureInit 0
      ((PqxdhBoundaryDeploymentStep.phase1_withReader codec reader).mpr phase1)
      ((PqxdhBoundaryDeploymentStep.phase2_withReader codec reader).mpr phase2) frameBack writable law spread correct
      adapter bounds mode adversary budget respects runtime qCoin Q qH qHash qTotal qFinish reductionCaps fallback
      signatureFallback

end

section
open PqxdhDeploymentServerAuth
open OracleComp OracleSpec CoreModels Aeneas ENNReal
open Aeneas.Std hiding namespace core alloc
open PqxdhServerAuthExperiment PqxdhServerAuthEntryFactor PqxdhServerAuthSourceCosts
open PqxdhServerAuthBodyCosts PqxdhServerAuthGapDh PqxdhServerAuthAssumptions
open PqxdhSecretInputKdf PqxdhFullSecretInputKdf PqxdhEd25519EufCma CtxNonceAeadIntCtxt
open PqxdhJointIdentity
open PqxdhDeploymentInterface (FreshBounds ModeSpec Mode Budget)
open PqxdhDeploymentSecrecy (Ledger)
open PqxdhDeploymentCompile (Local)
open PqxdhDeploymentCompileSecrecy (compileFull mergeFull)
open PqxdhDeploymentServerAuthEvent (SourceEntry Reg regsOf regsOfSource summarizeReg accepted Matched Unmatched A1At
  protectedBinding)
open PqxdhDeploymentServerAuthChain (seedBinding seedInput)

/-- Production form of `PqxdhDeploymentServerAuth.ce_a1` (frozen: Theorem CE-A1 (plan section 10, option (b) of section 19), with the public pinned matching in place of the plan's eleven-field common session). The frozen statement at the production codec `withReader codec reader` and route `RawCtxFrameDecoding.sender reader.model`, with every probability of the CE experiment (`PqxdhDeploymentSecrecy.game`, index 0) replaced by the probability of the same event read back through `unwrap` on the classical source game `PqxdhBoundaryDeployment.sourceGame` (`PqxdhDeploymentProductionTransfer.chance`). Everything else in the conclusion (every bound term and every bills conjunct) is the frozen text at the production codec and route. The Phase 1 and Phase 2 read-back laws are stated at `codec` (`PqxdhBoundaryDeploymentStep.phase1_withReader`, `phase2_withReader`, `Iff.rfl`); every other premise is the frozen one at the production codec and route. The frozen theorem holds at every Server identity index; the production form is at index 0, as every production form. -/
theorem ce_a1 (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (reader : RawCtxNativeFramePrelude.Reader Message Root) (erased : Aeneas.Std.Array Aeneas.Std.U8 357#usize)
    (checks : Checks) (caps : KemCaps) (bounded : KemBound setup caps) (ensureInit : StateT A ProbComp Bool)
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec)
    (frameBack : PqxdhServerAuthNegativeControl.FrameReadBack (PqxdhBoundaryRecordPrelude.withReader codec reader))
    (writable : PqxdhFirstBeaconRecordCanonical.ReadWritable (PqxdhBoundaryRecordPrelude.withReader codec
      reader).frameWrite (PqxdhBoundaryRecordPrelude.withReader codec reader).frameRead)
    (law : X25519ClassLaw setup.source.crypto) (spread : X25519ScalarSpread setup.source.crypto)
    (correct : SourceFullCorrect setup.source setup.hmac)
    (adapter : HasAttachedVerificationAdapter
      (fun identity => setup.source.crypto.verify identity.toList)
      setup.joint.verify)
    (bounds : FreshBounds) (mode : Mode) (adversary : OracleComp (ModeSpec mode) X) (budget : Budget)
    (respects : budget.Respects adversary) (runtime : A) (qCoin Q qH qHash qTotal qFinish : Nat)
    (reductionCaps : ∀ c, ReductionCaps (reduction (KemSK := KemSK) setup
      (PqxdhBoundaryRecordPrelude.withReader codec reader) (RawCtxFrameDecoding.sender reader.model) bounds mode
        adversary c)
      qCoin Q qH qHash qTotal qFinish)
    (fallback : ModifiedNonceAeadForgery) (signatureFallback : PqxdhJointIdentity.Forgery) :
    (𝒟[((fun outcome => @decide (∃ c, A1NoPinnedMatch setup (PqxdhBoundaryRecordPrelude.withReader codec reader) c
      outcome) (Classical.propDecidable _)) ∘ PqxdhBoundaryDeployment.unwrap) <$>
        (PqxdhBoundaryDeployment.sourceGame setup codec reader erased checks ensureInit 0 bounds mode adversary).run
          runtime]
        {true}).toReal ≤
      ∑ c : Fin budget.create, serverAuthBound setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks caps
        (serverAuthAdversary setup (PqxdhBoundaryRecordPrelude.withReader codec reader)
          (RawCtxFrameDecoding.sender reader.model) bounds mode adversary c) qCoin Q qH qHash fallback
            signatureFallback ∧
    ∀ c, PqxdhServerAuthCommonAuthentication.ReductionBills setup (PqxdhBoundaryRecordPrelude.withReader codec reader)
      checks caps
      (serverAuthAdversary setup (PqxdhBoundaryRecordPrelude.withReader codec reader)
        (RawCtxFrameDecoding.sender reader.model) bounds mode adversary c) qCoin Q qH qHash qTotal qFinish fallback
      signatureFallback := by
  simp only [PqxdhDeploymentProductionTransfer.chance]
  exact PqxdhDeploymentServerAuth.ce_a1 setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks caps bounded
      (RawCtxFrameDecoding.sender reader.model) ensureInit 0
      ((PqxdhBoundaryDeploymentStep.phase1_withReader codec reader).mpr phase1)
      ((PqxdhBoundaryDeploymentStep.phase2_withReader codec reader).mpr phase2) frameBack writable law spread correct
      adapter bounds mode adversary budget respects runtime qCoin Q qH qHash qTotal qFinish reductionCaps fallback
      signatureFallback

end

section
open PqxdhDeploymentServerAuthBills
open OracleComp OracleSpec CoreModels Aeneas ENNReal
open Aeneas.Std hiding namespace core alloc
open PqxdhServerAuthExperiment PqxdhServerAuthSourceCosts PqxdhJointIdentity
open PqxdhJointGapDh (ScalarBytes)
open PqxdhDeploymentInterface (FreshBounds ModeSpec Mode Budget)
open PqxdhDeploymentSecrecy (Ledger)
open PqxdhDeploymentCompile (Local)
open PqxdhDeploymentCompileSecrecy (compileFull)
open PqxdhRegistrationJointRevealCosts (SourceKind sourceKind)
open PqxdhDeploymentServerAuthEvent (SourceEntry)
open PqxdhDeploymentServerAuthEmbed (SourceSpec Owner Emb embed freezeImpl freeze dflt stopAt coins forward localCreate
  localBundle localCallbacks localRoot)

/-- Production form of `PqxdhDeploymentServerAuthBills.ce_a1_billed` (frozen: Theorem CE-A1 at the transported deployment budget). The frozen statement at the production codec `withReader codec reader` and route `RawCtxFrameDecoding.sender reader.model`, with every probability of the CE experiment (`PqxdhDeploymentSecrecy.game`, index 0) replaced by the probability of the same event read back through `unwrap` on the classical source game `PqxdhBoundaryDeployment.sourceGame` (`PqxdhDeploymentProductionTransfer.chance`). Everything else in the conclusion (every bound term and every bills conjunct) is the frozen text at the production codec and route. The Phase 1 and Phase 2 read-back laws are stated at `codec` (`PqxdhBoundaryDeploymentStep.phase1_withReader`, `phase2_withReader`, `Iff.rfl`); every other premise is the frozen one at the production codec and route. The frozen theorem holds at every Server identity index; the production form is at index 0, as every production form. -/
theorem ce_a1_billed (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (reader : RawCtxNativeFramePrelude.Reader Message Root) (erased : Aeneas.Std.Array Aeneas.Std.U8 357#usize)
    (checks : Checks) (caps : KemCaps) (bounded : KemBound setup caps) (ensureInit : StateT A ProbComp Bool)
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec)
    (frameBack : PqxdhServerAuthNegativeControl.FrameReadBack (PqxdhBoundaryRecordPrelude.withReader codec reader))
    (writable : PqxdhFirstBeaconRecordCanonical.ReadWritable (PqxdhBoundaryRecordPrelude.withReader codec
      reader).frameWrite (PqxdhBoundaryRecordPrelude.withReader codec reader).frameRead)
    (law : PqxdhServerAuthAssumptions.X25519ClassLaw setup.source.crypto)
    (spread : PqxdhServerAuthAssumptions.X25519ScalarSpread setup.source.crypto)
    (correct : PqxdhFullSecretInputKdf.SourceFullCorrect setup.source setup.hmac)
    (adapter : PqxdhEd25519EufCma.HasAttachedVerificationAdapter
      (fun identity => setup.source.crypto.verify identity.toList) setup.joint.verify)
    (bounds : FreshBounds) (mode : Mode) (adversary : OracleComp (ModeSpec mode) X) (budget : Budget)
    (respects : budget.Respects adversary) (runtime : A) (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery)
    (signatureFallback : PqxdhJointIdentity.Forgery) :
    (𝒟[((fun outcome => @decide (∃ c, PqxdhDeploymentServerAuth.A1NoPinnedMatch setup
      (PqxdhBoundaryRecordPrelude.withReader codec reader) c outcome)
        (Classical.propDecidable _)) ∘ PqxdhBoundaryDeployment.unwrap) <$>
        (PqxdhBoundaryDeployment.sourceGame setup codec reader erased checks ensureInit 0 bounds mode adversary).run
          runtime]
        {true}).toReal ≤
      ∑ c : Fin budget.create, PqxdhDeploymentServerAuth.serverAuthBound setup
        (PqxdhBoundaryRecordPrelude.withReader codec reader) checks caps
        (PqxdhDeploymentServerAuth.serverAuthAdversary setup (PqxdhBoundaryRecordPrelude.withReader codec reader)
          (RawCtxFrameDecoding.sender reader.model) bounds mode adversary c)
        (coinCap caps bounds budget) budget.accept (romCap budget) (hashCap budget) fallback signatureFallback ∧
    ∀ c, PqxdhServerAuthCommonAuthentication.ReductionBills setup (PqxdhBoundaryRecordPrelude.withReader codec reader)
      checks caps
      (PqxdhDeploymentServerAuth.serverAuthAdversary setup (PqxdhBoundaryRecordPrelude.withReader codec reader)
        (RawCtxFrameDecoding.sender reader.model) bounds mode adversary c)
      (coinCap caps bounds budget) budget.accept (romCap budget) (hashCap budget) (totalCap caps bounds budget)
      budget.finish fallback signatureFallback := by
  simp only [PqxdhDeploymentProductionTransfer.chance]
  exact PqxdhDeploymentServerAuthBills.ce_a1_billed setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
      caps bounded (RawCtxFrameDecoding.sender reader.model) ensureInit 0
      ((PqxdhBoundaryDeploymentStep.phase1_withReader codec reader).mpr phase1)
      ((PqxdhBoundaryDeploymentStep.phase2_withReader codec reader).mpr phase2) frameBack writable law spread correct
      adapter bounds mode adversary budget respects runtime fallback signatureFallback

end

section
open PqxdhDeploymentServerAuthInjectiveGame
open OracleComp OracleSpec CoreModels Aeneas ENNReal
open Aeneas.Std hiding namespace core alloc
open PqxdhServerAuthExperiment PqxdhJointIdentity
open PqxdhDeploymentInterface (Entry FreshBounds ModeSpec Mode Budget)
open PqxdhDeploymentSecrecy (Ledger)
open PqxdhDeploymentCompile (Local)
open PqxdhDeploymentCompileSecrecy (compileFull mergeFull)
open PqxdhDeploymentServerAuthEvent (Reg regOfEntry regsOf summarizeReg accepted bundleOfReg keysOfBundle publishedKeys
  MatchedAt)
open PqxdhDeploymentServerAuthInjective (identities Collision)
open PqxdhDeploymentRegistrationTrace (Logged acceptsOf traceFrom)
open PqxdhDeploymentKemTransfer (registrations regOf)

/-- Production form of `PqxdhDeploymentServerAuthInjectiveGame.injective_bound` (frozen: The injectivity loss `ε_inj` of CE-A1). The frozen statement at the production codec `withReader codec reader` and route `RawCtxFrameDecoding.sender reader.model`, with every probability of the CE experiment (`PqxdhDeploymentSecrecy.game`, index 0) replaced by the probability of the same event read back through `unwrap` on the classical source game `PqxdhBoundaryDeployment.sourceGame` (`PqxdhDeploymentProductionTransfer.chance`). Everything else in the conclusion (every bound term and every bills conjunct) is the frozen text at the production codec and route. The Phase 1 and Phase 2 read-back laws are stated at `codec` (`PqxdhBoundaryDeploymentStep.phase1_withReader`, `phase2_withReader`, `Iff.rfl`); every other premise is the frozen one at the production codec and route. -/
theorem injective_bound (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (reader : RawCtxNativeFramePrelude.Reader Message Root) (erased : Aeneas.Std.Array Aeneas.Std.U8 357#usize)
    (checks : Checks) (ensureInit : StateT A ProbComp Bool)
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec) (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) (budget : Budget) (respects : budget.Respects adversary) (runtime : A) :
    𝒟[((fun outcome => @decide (∃ c c', SharedMatch setup (PqxdhBoundaryRecordPrelude.withReader codec reader) c c'
      outcome) (Classical.propDecidable _)) ∘ PqxdhBoundaryDeployment.unwrap) <$>
        (PqxdhBoundaryDeployment.sourceGame setup codec reader erased checks ensureInit 0 bounds mode adversary).run
          runtime] {true} ≤
      ∑ target : Fin (budget.create + 1), advantage setup.joint
        (PqxdhDeploymentServerAuthInjective.collider setup.joint budget.create target) := by
  simp only [PqxdhDeploymentProductionTransfer.chance]
  exact PqxdhDeploymentServerAuthInjectiveGame.injective_bound setup
      (PqxdhBoundaryRecordPrelude.withReader codec reader) checks (RawCtxFrameDecoding.sender reader.model) ensureInit
      ((PqxdhBoundaryDeploymentStep.phase1_withReader codec reader).mpr phase1)
      ((PqxdhBoundaryDeploymentStep.phase2_withReader codec reader).mpr phase2) bounds mode adversary budget respects
      runtime

end

section
open PqxdhDeploymentServerAuthInjectiveGame
open OracleComp OracleSpec CoreModels Aeneas ENNReal
open Aeneas.Std hiding namespace core alloc
open PqxdhServerAuthExperiment PqxdhJointIdentity
open PqxdhDeploymentInterface (Entry FreshBounds ModeSpec Mode Budget)
open PqxdhDeploymentSecrecy (Ledger)
open PqxdhDeploymentCompile (Local)
open PqxdhDeploymentCompileSecrecy (compileFull mergeFull)
open PqxdhDeploymentServerAuthEvent (Reg regOfEntry regsOf summarizeReg accepted bundleOfReg keysOfBundle publishedKeys
  MatchedAt)
open PqxdhDeploymentServerAuthInjective (identities Collision)
open PqxdhDeploymentRegistrationTrace (Logged acceptsOf traceFrom)
open PqxdhDeploymentKemTransfer (registrations regOf)

/-- Production form of `PqxdhDeploymentServerAuthInjectiveGame.ce_a1_injective` (frozen: Theorem CE-A1 with injectivity (plan section 10)). The frozen statement at the production codec `withReader codec reader` and route `RawCtxFrameDecoding.sender reader.model`, with every probability of the CE experiment (`PqxdhDeploymentSecrecy.game`, index 0) replaced by the probability of the same event read back through `unwrap` on the classical source game `PqxdhBoundaryDeployment.sourceGame` (`PqxdhDeploymentProductionTransfer.chance`). Everything else in the conclusion (every bound term and every bills conjunct) is the frozen text at the production codec and route. The Phase 1 and Phase 2 read-back laws are stated at `codec` (`PqxdhBoundaryDeploymentStep.phase1_withReader`, `phase2_withReader`, `Iff.rfl`); every other premise is the frozen one at the production codec and route. -/
theorem ce_a1_injective (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (reader : RawCtxNativeFramePrelude.Reader Message Root) (erased : Aeneas.Std.Array Aeneas.Std.U8 357#usize)
    (checks : Checks) (caps : PqxdhServerAuthSourceCosts.KemCaps)
    (bounded : PqxdhServerAuthSourceCosts.KemBound setup caps) (ensureInit : StateT A ProbComp Bool)
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec)
    (frameBack : PqxdhServerAuthNegativeControl.FrameReadBack (PqxdhBoundaryRecordPrelude.withReader codec reader))
    (writable : PqxdhFirstBeaconRecordCanonical.ReadWritable (PqxdhBoundaryRecordPrelude.withReader codec
      reader).frameWrite (PqxdhBoundaryRecordPrelude.withReader codec reader).frameRead)
    (law : PqxdhServerAuthAssumptions.X25519ClassLaw setup.source.crypto)
    (spread : PqxdhServerAuthAssumptions.X25519ScalarSpread setup.source.crypto)
    (correct : PqxdhFullSecretInputKdf.SourceFullCorrect setup.source setup.hmac)
    (adapter : PqxdhEd25519EufCma.HasAttachedVerificationAdapter
      (fun identity => setup.source.crypto.verify identity.toList) setup.joint.verify)
    (bounds : FreshBounds) (mode : Mode) (adversary : OracleComp (ModeSpec mode) X) (budget : Budget)
    (respects : budget.Respects adversary) (runtime : A) (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery)
    (signatureFallback : PqxdhJointIdentity.Forgery) :
    (𝒟[((fun outcome => @decide ((∃ c, PqxdhDeploymentServerAuth.A1NoPinnedMatch setup
      (PqxdhBoundaryRecordPrelude.withReader codec reader) c outcome) ∨
        ∃ c c', SharedMatch setup (PqxdhBoundaryRecordPrelude.withReader codec reader) c c' outcome)
          (Classical.propDecidable _)) ∘ PqxdhBoundaryDeployment.unwrap) <$>
        (PqxdhBoundaryDeployment.sourceGame setup codec reader erased checks ensureInit 0 bounds mode adversary).run
          runtime]
        {true}).toReal ≤
      (∑ c : Fin budget.create, PqxdhDeploymentServerAuth.serverAuthBound setup
        (PqxdhBoundaryRecordPrelude.withReader codec reader) checks caps
        (PqxdhDeploymentServerAuth.serverAuthAdversary setup (PqxdhBoundaryRecordPrelude.withReader codec reader)
          (RawCtxFrameDecoding.sender reader.model) bounds mode adversary c)
        (PqxdhDeploymentServerAuthBills.coinCap caps bounds budget) budget.accept
        (PqxdhDeploymentServerAuthBills.romCap budget) (PqxdhDeploymentServerAuthBills.hashCap budget) fallback
        signatureFallback) +
      ∑ target : Fin (budget.create + 1), (advantage setup.joint
        (PqxdhDeploymentServerAuthInjective.collider setup.joint budget.create target)).toReal ∧
    (∀ c, PqxdhServerAuthCommonAuthentication.ReductionBills setup (PqxdhBoundaryRecordPrelude.withReader codec reader)
      checks caps
      (PqxdhDeploymentServerAuth.serverAuthAdversary setup (PqxdhBoundaryRecordPrelude.withReader codec reader)
        (RawCtxFrameDecoding.sender reader.model) bounds mode adversary c)
      (PqxdhDeploymentServerAuthBills.coinCap caps bounds budget) budget.accept
      (PqxdhDeploymentServerAuthBills.romCap budget) (PqxdhDeploymentServerAuthBills.hashCap budget)
      (PqxdhDeploymentServerAuthBills.totalCap caps bounds budget) budget.finish fallback signatureFallback) ∧
    ∀ target : Fin (budget.create + 1),
      (∀ jointPublic, (PqxdhDeploymentServerAuthInjective.collider setup.joint budget.create target
        jointPublic).IsQueryBoundP (PqxdhJointIdentityFamily.IsClass .uniform) (32 * budget.create)) ∧
      (∀ jointPublic, (PqxdhDeploymentServerAuthInjective.collider setup.joint budget.create target
        jointPublic).IsQueryBoundP (PqxdhJointIdentityFamily.IsClass .sign) 0) ∧
      (∀ jointPublic, (PqxdhDeploymentServerAuthInjective.collider setup.joint budget.create target
        jointPublic).IsQueryBoundP (PqxdhJointIdentityFamily.IsClass .staticDh) 0) ∧
      (game setup.joint (PqxdhDeploymentServerAuthInjective.collider setup.joint budget.create
        target)).IsTotalQueryBound (32 * (budget.create + 1)) := by
  simp only [PqxdhDeploymentProductionTransfer.chance]
  exact PqxdhDeploymentServerAuthInjectiveGame.ce_a1_injective setup
      (PqxdhBoundaryRecordPrelude.withReader codec reader) checks caps bounded (RawCtxFrameDecoding.sender reader.model)
      ensureInit ((PqxdhBoundaryDeploymentStep.phase1_withReader codec reader).mpr phase1)
      ((PqxdhBoundaryDeploymentStep.phase2_withReader codec reader).mpr phase2) frameBack writable law spread correct
      adapter bounds mode adversary budget respects runtime fallback signatureFallback

end

section
open PqxdhDeploymentPublishedTuple
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open PqxdhServerAuthExperiment PqxdhJointIdentity
open PqxdhRegistrationJointRevealSchedule (Spec)

/-- Production form of `PqxdhDeploymentPublishedTuple.a2pub_owner_bound` (frozen: Theorem CE-A2pub per owner (published-tuple provenance at owners without a failed bundle call, no selection factor)). The frozen statement at the production codec `withReader codec reader` and route `RawCtxFrameDecoding.sender reader.model`, with every probability of the CE experiment (`PqxdhDeploymentSecrecy.game`, index 0) replaced by the probability of the same event read back through `unwrap` on the classical source game `PqxdhBoundaryDeployment.sourceGame` (`PqxdhDeploymentProductionTransfer.chance`). Everything else in the conclusion (every bound term and every bills conjunct) is the frozen text at the production codec and route. The Phase 1 and Phase 2 read-back laws are stated at `codec` (`PqxdhBoundaryDeploymentStep.phase1_withReader`, `phase2_withReader`, `Iff.rfl`); every other premise is the frozen one at the production codec and route. -/
theorem a2pub_owner_bound (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (reader : RawCtxNativeFramePrelude.Reader Message Root) (erased : Aeneas.Std.Array Aeneas.Std.U8 357#usize)
    (checks : Checks)
    (shortRejects : ∀ (publicKey : PqxdhEd25519EufCma.Ed25519PublicKey) bytes, bytes.length < 64 →
      setup.source.crypto.verify publicKey.toList bytes = none)
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec) (ensureInit : StateT A ProbComp Bool)
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (adversary : OracleComp (PqxdhDeploymentInterface.ModeSpec mode) X) (budget : PqxdhDeploymentInterface.Budget)
    (respects : budget.Respects adversary) (runtime : A) (fallback : PqxdhDynamicIdentityRouting.DynamicForgery)
    (ordinaryFallback : PqxdhJointIdentity.Forgery) :
    letI := Classical.propDecidable
    𝒟[((fun outcome => decide (OwnerEvent setup (PqxdhBoundaryRecordPrelude.withReader codec reader) outcome)) ∘
      PqxdhBoundaryDeployment.unwrap) <$>
        (PqxdhBoundaryDeployment.sourceGame setup codec reader erased checks ensureInit 0 bounds mode adversary).run
          runtime] {true} ≤
      ∑ target : Fin (budget.create + 1), PqxdhJointIdentity.advantage setup.joint
        (PqxdhDeploymentProvenance.reduction setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
          (RawCtxFrameDecoding.sender reader.model) ensureInit bounds mode adversary budget.create
          runtime fallback ordinaryFallback target) := by
  simp only [PqxdhDeploymentProductionTransfer.chance]
  exact PqxdhDeploymentPublishedTuple.a2pub_owner_bound setup (PqxdhBoundaryRecordPrelude.withReader codec reader)
      checks shortRejects ((PqxdhBoundaryDeploymentStep.phase1_withReader codec reader).mpr phase1)
      ((PqxdhBoundaryDeploymentStep.phase2_withReader codec reader).mpr phase2)
      (RawCtxFrameDecoding.sender reader.model) ensureInit bounds mode adversary budget respects runtime fallback
      ordinaryFallback

end

section
open PqxdhDeploymentPublishedTuple
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open PqxdhServerAuthExperiment PqxdhJointIdentity
open PqxdhRegistrationJointRevealSchedule (Spec)

/-- Production form of `PqxdhDeploymentPublishedTuple.a2pub_bound` (frozen: Theorem CE-A2pub (published-tuple provenance, on `NoBundleFailure` runs, no selection factor)). The frozen statement at the production codec `withReader codec reader` and route `RawCtxFrameDecoding.sender reader.model`, with every probability of the CE experiment (`PqxdhDeploymentSecrecy.game`, index 0) replaced by the probability of the same event read back through `unwrap` on the classical source game `PqxdhBoundaryDeployment.sourceGame` (`PqxdhDeploymentProductionTransfer.chance`). Everything else in the conclusion (every bound term and every bills conjunct) is the frozen text at the production codec and route. The Phase 1 and Phase 2 read-back laws are stated at `codec` (`PqxdhBoundaryDeploymentStep.phase1_withReader`, `phase2_withReader`, `Iff.rfl`); every other premise is the frozen one at the production codec and route. -/
theorem a2pub_bound (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (reader : RawCtxNativeFramePrelude.Reader Message Root) (erased : Aeneas.Std.Array Aeneas.Std.U8 357#usize)
    (checks : Checks)
    (shortRejects : ∀ (publicKey : PqxdhEd25519EufCma.Ed25519PublicKey) bytes, bytes.length < 64 →
      setup.source.crypto.verify publicKey.toList bytes = none)
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec) (ensureInit : StateT A ProbComp Bool)
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (adversary : OracleComp (PqxdhDeploymentInterface.ModeSpec mode) X) (budget : PqxdhDeploymentInterface.Budget)
    (respects : budget.Respects adversary) (runtime : A) (fallback : PqxdhDynamicIdentityRouting.DynamicForgery)
    (ordinaryFallback : PqxdhJointIdentity.Forgery) :
    letI := Classical.propDecidable
    𝒟[((fun outcome => decide (GameEvent setup (PqxdhBoundaryRecordPrelude.withReader codec reader) outcome)) ∘
      PqxdhBoundaryDeployment.unwrap) <$>
        (PqxdhBoundaryDeployment.sourceGame setup codec reader erased checks ensureInit 0 bounds mode adversary).run
          runtime] {true} ≤
      ∑ target : Fin (budget.create + 1), PqxdhJointIdentity.advantage setup.joint
        (PqxdhDeploymentProvenance.reduction setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
          (RawCtxFrameDecoding.sender reader.model) ensureInit bounds mode adversary budget.create
          runtime fallback ordinaryFallback target) := by
  simp only [PqxdhDeploymentProductionTransfer.chance]
  exact PqxdhDeploymentPublishedTuple.a2pub_bound setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
      shortRejects ((PqxdhBoundaryDeploymentStep.phase1_withReader codec reader).mpr phase1)
      ((PqxdhBoundaryDeploymentStep.phase2_withReader codec reader).mpr phase2)
      (RawCtxFrameDecoding.sender reader.model) ensureInit bounds mode adversary budget respects runtime fallback
      ordinaryFallback

end

section
open PqxdhDeploymentPublishedTuple
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open PqxdhServerAuthExperiment PqxdhJointIdentity
open PqxdhRegistrationJointRevealSchedule (Spec)

/-- Production form of `PqxdhDeploymentPublishedTuple.r1prime_owner_bound` (frozen: Theorem CE-R1' per owner (published-tuple replay at owners without a failed bundle call)). The frozen statement at the production codec `withReader codec reader` and route `RawCtxFrameDecoding.sender reader.model`, with every probability of the CE experiment (`PqxdhDeploymentSecrecy.game`, index 0) replaced by the probability of the same event read back through `unwrap` on the classical source game `PqxdhBoundaryDeployment.sourceGame` (`PqxdhDeploymentProductionTransfer.chance`). Everything else in the conclusion (every bound term and every bills conjunct) is the frozen text at the production codec and route. The Phase 1 and Phase 2 read-back laws are stated at `codec` (`PqxdhBoundaryDeploymentStep.phase1_withReader`, `phase2_withReader`, `Iff.rfl`); every other premise is the frozen one at the production codec and route. -/
theorem r1prime_owner_bound (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (reader : RawCtxNativeFramePrelude.Reader Message Root) (erased : Aeneas.Std.Array Aeneas.Std.U8 357#usize)
    (checks : Checks)
    (shortRejects : ∀ (publicKey : PqxdhEd25519EufCma.Ed25519PublicKey) bytes, bytes.length < 64 →
      setup.source.crypto.verify publicKey.toList bytes = none)
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec) (ensureInit : StateT A ProbComp Bool)
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (adversary : OracleComp (PqxdhDeploymentInterface.ModeSpec mode) X) (budget : PqxdhDeploymentInterface.Budget)
    (respects : budget.Respects adversary) (runtime : A) (fallback : PqxdhDynamicIdentityRouting.DynamicForgery)
    (ordinaryFallback : PqxdhJointIdentity.Forgery) :
    letI := Classical.propDecidable
    𝒟[((fun outcome => decide (ReplayOwnerEvent setup (PqxdhBoundaryRecordPrelude.withReader codec reader) outcome)) ∘
      PqxdhBoundaryDeployment.unwrap) <$>
        (PqxdhBoundaryDeployment.sourceGame setup codec reader erased checks ensureInit 0 bounds mode adversary).run
          runtime] {true} ≤
      ∑ target : Fin (budget.create + 1), PqxdhJointIdentity.advantage setup.joint
        (PqxdhDeploymentProvenance.reduction setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
          (RawCtxFrameDecoding.sender reader.model) ensureInit bounds mode adversary budget.create
          runtime fallback ordinaryFallback target) := by
  simp only [PqxdhDeploymentProductionTransfer.chance]
  exact PqxdhDeploymentPublishedTuple.r1prime_owner_bound setup (PqxdhBoundaryRecordPrelude.withReader codec reader)
      checks shortRejects ((PqxdhBoundaryDeploymentStep.phase1_withReader codec reader).mpr phase1)
      ((PqxdhBoundaryDeploymentStep.phase2_withReader codec reader).mpr phase2)
      (RawCtxFrameDecoding.sender reader.model) ensureInit bounds mode adversary budget respects runtime fallback
      ordinaryFallback

end

section
open PqxdhDeploymentPublishedTuple
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open PqxdhServerAuthExperiment PqxdhJointIdentity
open PqxdhRegistrationJointRevealSchedule (Spec)

/-- Production form of `PqxdhDeploymentPublishedTuple.r1prime_bound` (frozen: Theorem CE-R1' (published-tuple replay, on `NoBundleFailure` runs)). The frozen statement at the production codec `withReader codec reader` and route `RawCtxFrameDecoding.sender reader.model`, with every probability of the CE experiment (`PqxdhDeploymentSecrecy.game`, index 0) replaced by the probability of the same event read back through `unwrap` on the classical source game `PqxdhBoundaryDeployment.sourceGame` (`PqxdhDeploymentProductionTransfer.chance`). Everything else in the conclusion (every bound term and every bills conjunct) is the frozen text at the production codec and route. The Phase 1 and Phase 2 read-back laws are stated at `codec` (`PqxdhBoundaryDeploymentStep.phase1_withReader`, `phase2_withReader`, `Iff.rfl`); every other premise is the frozen one at the production codec and route. -/
theorem r1prime_bound (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (reader : RawCtxNativeFramePrelude.Reader Message Root) (erased : Aeneas.Std.Array Aeneas.Std.U8 357#usize)
    (checks : Checks)
    (shortRejects : ∀ (publicKey : PqxdhEd25519EufCma.Ed25519PublicKey) bytes, bytes.length < 64 →
      setup.source.crypto.verify publicKey.toList bytes = none)
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec) (ensureInit : StateT A ProbComp Bool)
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (adversary : OracleComp (PqxdhDeploymentInterface.ModeSpec mode) X) (budget : PqxdhDeploymentInterface.Budget)
    (respects : budget.Respects adversary) (runtime : A) (fallback : PqxdhDynamicIdentityRouting.DynamicForgery)
    (ordinaryFallback : PqxdhJointIdentity.Forgery) :
    letI := Classical.propDecidable
    𝒟[((fun outcome => decide (ReplayEvent setup (PqxdhBoundaryRecordPrelude.withReader codec reader) outcome)) ∘
      PqxdhBoundaryDeployment.unwrap) <$>
        (PqxdhBoundaryDeployment.sourceGame setup codec reader erased checks ensureInit 0 bounds mode adversary).run
          runtime] {true} ≤
      ∑ target : Fin (budget.create + 1), PqxdhJointIdentity.advantage setup.joint
        (PqxdhDeploymentProvenance.reduction setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
          (RawCtxFrameDecoding.sender reader.model) ensureInit bounds mode adversary budget.create
          runtime fallback ordinaryFallback target) := by
  simp only [PqxdhDeploymentProductionTransfer.chance]
  exact PqxdhDeploymentPublishedTuple.r1prime_bound setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
      shortRejects ((PqxdhBoundaryDeploymentStep.phase1_withReader codec reader).mpr phase1)
      ((PqxdhBoundaryDeploymentStep.phase2_withReader codec reader).mpr phase2)
      (RawCtxFrameDecoding.sender reader.model) ensureInit bounds mode adversary budget respects runtime fallback
      ordinaryFallback

end

section
open PqxdhDeploymentReplay
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open PqxdhServerAuthExperiment PqxdhServerAuthNative PqxdhJointIdentity PqxdhJointGapDh
open PqxdhServerRootPreparation (Inputs registrationId collect)
open PqxdhDeploymentInterface (Spec Command FullSpec ModeSpec Mode Entry FreshBounds parsePin asModeO)
open PqxdhDeploymentTranscript (candidateOf acceptedKeys)
open PqxdhDeploymentSecrecy (Ledger ledgerImpl)

/-- Production form of `PqxdhDeploymentReplay.replay_game` (frozen: Theorem CE-R1 (per live Server object, deterministic, zero loss)). The frozen statement at the production codec `withReader codec reader` and route `RawCtxFrameDecoding.sender reader.model`, with every outcome of the CE experiment (`PqxdhDeploymentSecrecy.game`, index 0) replaced by an outcome of the classical source game `PqxdhBoundaryDeployment.sourceGame` read back through `unwrap` (`support_zero`). The conclusion is the frozen text at the production codec; the frozen theorem takes no codec law, contract or budget, and neither does the production form. Reading back through `unwrap` loses no run: the source game never returns a Rust `fail` or `div` result, every supported source outcome being the `okMap` image of a supported outcome of the CE game (`PqxdhBoundaryDeployment.classical_normal`), of which `unwrap` is a left inverse (`unwrap_okMap`), so every supported source run is covered. The frozen theorem holds at every Server identity index; the production form is at index 0, as every production form. -/
theorem replay_game (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (reader : RawCtxNativeFramePrelude.Reader Message Root) (erased : Aeneas.Std.Array Aeneas.Std.U8 357#usize)
    (checks : Checks) (ensureInit : StateT A ProbComp Bool) (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) (runtime : A) (outcome : PqxdhBoundaryDeployment.Outcome KemSK X × A)
    (supported : outcome ∈ support ((PqxdhBoundaryDeployment.sourceGame setup codec reader erased checks ensureInit 0
      bounds mode adversary).run runtime))
    (created : PqxdhRegistrationJointServerBirth.ClientCreated Unit) (output : X)
    (final : PqxdhDeploymentSecrecy.State KemSK)
    (reached : (PqxdhBoundaryDeployment.unwrap outcome).1 = some (created, output, final)) (rid : Pqxdh.Bytes) :
    final.1.transcript.countP (fun entry => entryRegistration setup.source.crypto
      (PqxdhBoundaryRecordPrelude.withReader codec reader) entry = some rid) ≤ 1 ∧
      final.2.native.shared.2.server.consumed = acceptIds setup.source.crypto
        (PqxdhBoundaryRecordPrelude.withReader codec reader) final.1.transcript := by
  exact PqxdhDeploymentReplay.replay_game setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
      (RawCtxFrameDecoding.sender reader.model) ensureInit 0 bounds mode adversary runtime
      (PqxdhBoundaryDeployment.unwrap outcome)
      (support_zero setup codec reader erased checks ensureInit bounds mode adversary runtime outcome supported) created
      output final reached rid

end

section
open PqxdhDeploymentRecordReplay
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
open PqxdhServerAuthExperiment PqxdhServerAuthNative PqxdhJointIdentity RawCtxMaterialPositions
open PqxdhDeploymentInterface (Spec Command FullSpec ModeSpec Mode Entry FreshBounds parsePin asModeO)
open PqxdhDeploymentSecrecy (Ledger ledgerImpl)
open PqxdhDeploymentRecordKernels (Live Finished peerKernel ownerKernel PeerStep OwnersSame)

/-- Production form of `PqxdhDeploymentRecordReplay.record_replay_game` (frozen: Theorem CE-C3 (record replay, for every owner and peer)). The frozen statement at the production codec `withReader codec reader` and route `RawCtxFrameDecoding.sender reader.model`, with every outcome of the CE experiment (`PqxdhDeploymentSecrecy.game`, index 0) replaced by an outcome of the classical source game `PqxdhBoundaryDeployment.sourceGame` read back through `unwrap` (`support_zero`). The conclusion is the frozen text at the production codec; the frozen theorem takes no codec law, contract or budget, and neither does the production form. Reading back through `unwrap` loses no run: the source game never returns a Rust `fail` or `div` result, every supported source outcome being the `okMap` image of a supported outcome of the CE game (`PqxdhBoundaryDeployment.classical_normal`), of which `unwrap` is a left inverse (`unwrap_okMap`), so every supported source run is covered. The frozen theorem holds at every Server identity index; the production form is at index 0, as every production form. -/
theorem record_replay_game (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (reader : RawCtxNativeFramePrelude.Reader Message Root) (erased : Aeneas.Std.Array Aeneas.Std.U8 357#usize)
    (checks : Checks) (ensureInit : StateT A ProbComp Bool) (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) (runtime : A) (outcome : PqxdhBoundaryDeployment.Outcome KemSK X × A)
    (supported : outcome ∈ support ((PqxdhBoundaryDeployment.sourceGame setup codec reader erased checks ensureInit 0
      bounds mode adversary).run runtime))
    (created : PqxdhRegistrationJointServerBirth.ClientCreated Unit) (output : X)
    (final : PqxdhDeploymentSecrecy.State KemSK)
    (reached : (PqxdhBoundaryDeployment.unwrap outcome).1 = some (created, output, final)) :
    (∀ kid, (peerSequences final.1.transcript kid).Nodup) ∧
      ∀ index, (ownerSequences final.1.transcript index).Nodup := by
  exact PqxdhDeploymentRecordReplay.record_replay_game setup (PqxdhBoundaryRecordPrelude.withReader codec reader) checks
      (RawCtxFrameDecoding.sender reader.model) ensureInit 0 bounds mode adversary runtime
      (PqxdhBoundaryDeployment.unwrap outcome)
      (support_zero setup codec reader erased checks ensureInit bounds mode adversary runtime outcome supported) created
      output final reached

end

end BeaconcryptCore.Computational.PqxdhDeploymentProductionRegistration

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentProductionRegistration.support_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentProductionRegistration.support_zero

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentProductionRegistration.a1_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentProductionRegistration.a1_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentProductionRegistration.a1_sum' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentProductionRegistration.a1_sum

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentProductionRegistration.ce_a1' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentProductionRegistration.ce_a1

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentProductionRegistration.ce_a1_billed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentProductionRegistration.ce_a1_billed

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentProductionRegistration.injective_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentProductionRegistration.injective_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentProductionRegistration.ce_a1_injective' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentProductionRegistration.ce_a1_injective

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentProductionRegistration.a2pub_owner_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentProductionRegistration.a2pub_owner_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentProductionRegistration.a2pub_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentProductionRegistration.a2pub_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentProductionRegistration.r1prime_owner_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentProductionRegistration.r1prime_owner_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentProductionRegistration.r1prime_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentProductionRegistration.r1prime_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentProductionRegistration.replay_game' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentProductionRegistration.replay_game

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentProductionRegistration.record_replay_game' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentProductionRegistration.record_replay_game
