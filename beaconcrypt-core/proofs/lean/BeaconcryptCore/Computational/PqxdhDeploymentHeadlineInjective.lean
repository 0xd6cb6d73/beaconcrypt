-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhDeploymentHeadlineSymbolic
import BeaconcryptCore.Computational.PqxdhDeploymentRecordReplay

/-!
# Injective forms of the symbolic CE-OR corollaries (CE-12 P2, design-v2 sections 7.3 and 7.6)

The injective origin conclusions of ProVerif (L2-origin and S2b-origin as injective correspondences) add, to the origin of each accepted record, that no two accepts are matched to one send. The theorems here bound the following named failure modes of injectivity in the common deployment experiment, with their existing bounds; that these modes cover every way an injective correspondence can fail is argued in prose (the guide's CE-12 P2 sections), not proved in Lean:

- b2s: a registration replayed under one Beacon identity, so that two Server peers belong to one Beacon (CE-R1', `PqxdhDeploymentPublishedTuple.ReplayOwnerEvent`: two successful accepts at distinct transcript positions under one owner's identity key, where that owner has no rejected bundle call in Fresh; two Server peers accepting frames of one Beacon send reach this case through their counterparts, by the prose argument), or one Server peer accepting a sequence number twice (CE-C3, `PeerReplay`);
- s2b: two Beacons matched to one session (`PqxdhDeploymentServerAuthInjectiveGame.SharedMatch`), two distinct owners with equal identity public keys (`PqxdhDeploymentHeadlineCollision.IdentityCollision`, which covers two Beacon owners accepting frames published by one Server peer whose session verifies to both identity keys; key IDs are unique, so one peer is one session), or one Beacon accepting a sequence number twice (CE-C3, `OwnerReplay`).

`ce_or_injective_b2s`: the probability of a symbolic b2s origin failure, a registration replay or a peer record replay is at most CE-OR b2s's bound plus `ε_A2pub`, because the Server-side gap and the registration replay are both published-tuple forgeries at an owner without a rejected bundle call in Fresh (`server_gap`, `PqxdhDeploymentPublishedTuple.replay_owner_published`), and record replay never happens (`PqxdhDeploymentRecordReplay.record_replay_game`). `ce_or_injective_s2b_full`: the probability of a symbolic s2b origin failure, a shared match, an identity collision or an owner record replay is at most CE-OR s2b's bound plus `ε_A1inj` (`ce_a1_injective`'s right side: `ε_A1 + ε_inj`) plus the explicit terms `ctGapTerm` (F-ct2) and `ctCollTerm`; a shared match is an identity collision (`shared_collision`) and `ε_inj` bounds the identity collision (`identity_collision_game`), so adding the identity collision costs nothing. `ce_or_injective_s2b` is the same bound without the identity collision in the event (implied by `ce_or_injective_s2b_full`). Event forms: `injective_b2s_le`, `injective_s2b_le`, `injective_s2b_full_le`.

No new assumption or contract; the premises are those of the corollaries and of CE-A1, CE-A2pub and CE-A1's injectivity.
-/

open OracleComp OracleSpec ENNReal

set_option autoImplicit false

namespace BeaconcryptCore.Computational.PqxdhDeploymentHeadlineInjective
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhDeploymentInterface (Handle Entry FreshBounds Mode ModeSpec Budget)
open PqxdhDeploymentKemTransfer (Observed happens observeGame)
open PqxdhDeploymentHeadlineSymbolic (OriginFailureSym originSym)

variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response A X : Type}

/-- CE-C3's failure at a Server peer: a Server was constructed and some peer accepted a sequence number twice. -/
def PeerReplay (outcome : Option (PqxdhRegistrationJointServerBirth.ClientCreated Unit × X ×
    PqxdhDeploymentSecrecy.State KemSK) × A) : Prop :=
  ∃ created output final, outcome.1 = some (created, output, final) ∧
    ∃ kid, ¬(PqxdhDeploymentRecordReplay.peerSequences final.1.transcript kid).Nodup

/-- CE-C3's failure at a Beacon owner: a Server was constructed and some owner accepted a sequence number twice. -/
def OwnerReplay (outcome : Option (PqxdhRegistrationJointServerBirth.ClientCreated Unit × X ×
    PqxdhDeploymentSecrecy.State KemSK) × A) : Prop :=
  ∃ created output final, outcome.1 = some (created, output, final) ∧
    ∃ index, ¬(PqxdhDeploymentRecordReplay.ownerSequences final.1.transcript index).Nodup

open Classical in
/-- The injective b2s failure: a symbolic b2s origin failure, a registration replay under one Beacon identity (CE-R1') or a peer record replay (CE-C3). -/
noncomputable def injectiveB2s (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder)
    (outcome : Option (PqxdhRegistrationJointServerBirth.ClientCreated Unit × X × PqxdhDeploymentSecrecy.State KemSK) × A) :
    Bool :=
  decide (OriginFailureSym setup codec route .b2s outcome ∨
    PqxdhDeploymentPublishedTuple.ReplayOwnerEvent setup codec outcome ∨ PeerReplay outcome)

open Classical in
/-- The injective s2b failure: a symbolic s2b origin failure, two Beacons matched to one session or an owner record replay (CE-C3). -/
noncomputable def injectiveS2b (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder)
    (outcome : Option (PqxdhRegistrationJointServerBirth.ClientCreated Unit × X × PqxdhDeploymentSecrecy.State KemSK) × A) :
    Bool :=
  decide (OriginFailureSym setup codec route .s2b outcome ∨
    (∃ c c', PqxdhDeploymentServerAuthInjectiveGame.SharedMatch setup codec c c' outcome) ∨ OwnerReplay outcome)

open Classical in
/-- The injective s2b failure with the identity collision: `injectiveS2b` or two distinct created owners with equal identity public keys (`PqxdhDeploymentHeadlineCollision.IdentityCollision`). The identity collision covers two Beacon owners that accept, at positions from 2, frames published by one Server peer whose session verifies to both owners' identity keys (two Beacon accepts of one B matched to one Server send); `SharedMatch` is one of its cases (`PqxdhDeploymentServerAuthInjectiveGame.shared_collision`). -/
noncomputable def injectiveS2bFull (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder)
    (outcome : Option (PqxdhRegistrationJointServerBirth.ClientCreated Unit × X × PqxdhDeploymentSecrecy.State KemSK) × A) :
    Bool :=
  decide (OriginFailureSym setup codec route .s2b outcome ∨
    (∃ c c', PqxdhDeploymentServerAuthInjectiveGame.SharedMatch setup codec c c' outcome) ∨
    PqxdhDeploymentHeadlineCollision.IdentityCollision setup outcome ∨ OwnerReplay outcome)

/-! ### Record replay never happens -/

/-- On every outcome of the experiment no Server peer and no Beacon owner accepted a sequence number twice (`PqxdhDeploymentRecordReplay.record_replay_game`). -/
theorem replay_never (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (ensureInit : StateT A ProbComp Bool) (bounds : FreshBounds)
    (mode : Mode) (adversary : OracleComp (ModeSpec mode) X) (runtime : A)
    (outcome : Option (PqxdhRegistrationJointServerBirth.ClientCreated Unit × X × PqxdhDeploymentSecrecy.State KemSK) × A)
    (member : outcome ∈ support ((PqxdhDeploymentSecrecy.game setup codec checks route ensureInit 0 bounds mode
      adversary).run runtime)) :
    ¬PeerReplay outcome ∧ ¬OwnerReplay outcome := by
  constructor
  · rintro ⟨created, output, final, found, kid, repeated⟩
    exact repeated ((PqxdhDeploymentRecordReplay.record_replay_game setup codec checks route ensureInit 0 bounds mode
      adversary runtime outcome member created output final found).1 kid)
  · rintro ⟨created, output, final, found, index, repeated⟩
    exact repeated ((PqxdhDeploymentRecordReplay.record_replay_game setup codec checks route ensureInit 0 bounds mode
      adversary runtime outcome member created output final found).2 index)

/-! ### The injective forms -/

section Injective
open PqxdhServerAuthSourceCosts (KemCaps KemBound)
open PqxdhDeploymentHeadlineChain (kemLoss slotLoss authLoss slotted serverSlotted)
open PqxdhDeploymentHeadlineAnomaly (beta)
open PqxdhDeploymentHeadlineEvents (originEvent orClaim)
open PqxdhDeploymentHeadlineGap (a2pubTerm ctGapTerm chance_le_support chance_le_add_support)
open PqxdhDeploymentHeadlineCollision (ctCollTerm)
open PqxdhRecordLiftIdeal (publicationTerm)

/-- `ce_or_injective_b2s` in event form: a symbolic b2s origin failure, a registration replay under one Beacon identity or a peer record replay is a CE b2s origin failure or CE-A2pub's per-owner event (`origin_b2s_sym`, `server_gap`, `replay_owner_published`, `replay_never`). Premises: the read-back contracts and the budget. -/
theorem injective_b2s_le (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (ensureInit : StateT A ProbComp Bool)
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec) (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) (budget : Budget) (respects : budget.Respects adversary) (runtime : A) :
    𝒟[injectiveB2s setup codec route <$>
      (PqxdhDeploymentSecrecy.game setup codec checks route ensureInit 0 bounds mode adversary).run runtime] {true} ≤
      𝒟[(fun outcome => happens (originEvent setup.source.crypto codec setup.serverKeyId budget route .b2s) outcome) <$>
        (PqxdhDeploymentSecrecy.game setup codec checks route ensureInit 0 bounds mode adversary).run runtime] {true} +
      𝒟[(fun outcome => @decide (PqxdhDeploymentPublishedTuple.OwnerEvent setup codec outcome)
          (Classical.propDecidable _)) <$>
        (PqxdhDeploymentSecrecy.game setup codec checks route ensureInit 0 bounds mode adversary).run runtime] {true} := by
  refine chance_le_add_support _ _ _ _ fun outcome member held => ?_
  simp only [injectiveB2s, decide_eq_true_eq] at held
  rcases held with origin | replayed | repeated
  · rcases PqxdhDeploymentHeadlineSymbolic.origin_b2s_sym setup codec route budget outcome origin with ce | gap
    · exact Or.inl ce
    · right
      simp only [decide_eq_true_eq]
      obtain ⟨created, output, final, found, keyId, sym, undesignated⟩ := gap
      obtain ⟨c, forged, clean⟩ := PqxdhDeploymentHeadlineGap.server_gap setup codec checks route ensureInit phase1
        phase2 bounds mode adversary budget respects runtime outcome member created output final found keyId sym
        undesignated
      exact ⟨created, output, final, found, c, forged, clean⟩
  · right
    simp only [decide_eq_true_eq]
    exact PqxdhDeploymentPublishedTuple.replay_owner_published setup codec checks route ensureInit 0 bounds mode
      adversary runtime outcome member replayed
  · exact absurd repeated (replay_never setup codec checks route ensureInit bounds mode adversary runtime outcome
      member).1

/-- `ce_or_injective_b2s` (design-v2 section 7.3; the injective L2-origin rows with CE-R1' and CE-C3): the probability of a symbolic b2s origin failure, a registration replay under one Beacon identity (two successful accepts at distinct positions under the identity key of an owner without a rejected bundle call in Fresh) or a Server peer accepting a sequence number twice is at most CE-OR b2s's bound plus `ε_A2pub`. Premises: those of `ce_or_b2s_sym`. -/
theorem ce_or_injective_b2s (setup : Setup baseSpec KemSK)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem)
    (codec : Codec Reader Response) (checks : Checks) (route : RawCtxServerRouting.SenderDecoder)
    (ensureInit : StateT A ProbComp Bool) (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec)
    (correct : PqxdhFullSecretInputKdf.SourceFullCorrect setup.source setup.hmac) (caps : KemCaps)
    (bounded : KemBound setup caps) (qInit : ℕ) (initBound : ∀ state, (ensureInit.run state).IsTotalQueryBound qInit)
    (frameReadBack : PqxdhServerAuthNegativeControl.FrameReadBack codec)
    (shortRejects : ∀ (publicKey : PqxdhEd25519EufCma.Ed25519PublicKey) bytes, bytes.length < 64 →
      setup.source.crypto.verify publicKey.toList bytes = none)
    (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) (budget : Budget) (respects : budget.Respects adversary) (runtime : A)
    (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery)
    (identityFallback : PqxdhDynamicIdentityRouting.DynamicForgery) (ordinaryFallback : PqxdhJointIdentity.Forgery) :
    𝒟[injectiveB2s setup codec route <$>
      (PqxdhDeploymentSecrecy.game setup codec checks route ensureInit 0 bounds mode adversary).run runtime] {true} ≤
      (∑ g : Fin budget.accept × Fin budget.create,
        (ENNReal.ofReal (kemLoss setup codec checks route ensureInit bounds mode adversary budget
            (originEvent setup.source.crypto codec setup.serverKeyId budget route .b2s)
            (orClaim setup.source.crypto codec setup.serverKeyId budget route .b2s) (g.1, g.2.castSucc) runtime) +
          ENNReal.ofReal (slotLoss setup codec checks route ensureInit bounds mode adversary budget
            (originEvent setup.source.crypto codec setup.serverKeyId budget route .b2s)
            (orClaim setup.source.crypto codec setup.serverKeyId budget route .b2s) (g.1, g.2.castSucc) runtime) +
          authLoss setup codec checks route ensureInit bounds mode adversary budget (g.1, g.2.castSucc) runtime
            fallback caps qInit (serverSlotted setup codec budget
              (originEvent setup.source.crypto codec setup.serverKeyId budget route .b2s)
              (orClaim setup.source.crypto codec setup.serverKeyId budget route .b2s) (g.1, g.2.castSucc)) +
          publicationTerm budget)) +
      a2pubTerm setup codec checks route ensureInit bounds mode adversary budget runtime identityFallback
        ordinaryFallback :=
  (injective_b2s_le setup codec checks route ensureInit phase1 phase2 bounds mode adversary budget respects
    runtime).trans
    (add_le_add (PqxdhDeploymentHeadlineOrigin.ce_or_b2s setup functional codec checks route ensureInit phase1 phase2
      correct caps bounded qInit initBound frameReadBack bounds mode adversary budget respects runtime fallback)
      (PqxdhDeploymentPublishedTuple.a2pub_owner_bound setup codec checks shortRejects phase1 phase2 route ensureInit
        bounds mode adversary budget respects runtime identityFallback ordinaryFallback))

/-- `ce_or_injective_s2b` in event form: a symbolic s2b origin failure, two Beacons matched to one session or an owner record replay is a CE s2b origin failure, CE-A1's event with injectivity (`A1NoPinnedMatch` or `SharedMatch`), a ciphertext gap or a ciphertext collision (`origin_s2b_sym`, `replay_never`). Premises: the read-back contracts and the budget. -/
theorem injective_s2b_le (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (ensureInit : StateT A ProbComp Bool)
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec) (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) (budget : Budget) (respects : budget.Respects adversary) (runtime : A) :
    𝒟[injectiveS2b setup codec route <$>
      (PqxdhDeploymentSecrecy.game setup codec checks route ensureInit 0 bounds mode adversary).run runtime] {true} ≤
      𝒟[(fun outcome => happens (originEvent setup.source.crypto codec setup.serverKeyId budget route .s2b) outcome) <$>
        (PqxdhDeploymentSecrecy.game setup codec checks route ensureInit 0 bounds mode adversary).run runtime] {true} +
      𝒟[(fun outcome => @decide ((∃ c, PqxdhDeploymentServerAuth.A1NoPinnedMatch setup codec c outcome) ∨
          ∃ c c', PqxdhDeploymentServerAuthInjectiveGame.SharedMatch setup codec c c' outcome)
          (Classical.propDecidable _)) <$>
        (PqxdhDeploymentSecrecy.game setup codec checks route ensureInit 0 bounds mode adversary).run runtime] {true} +
      ctGapTerm setup codec checks route ensureInit bounds mode adversary runtime +
      ctCollTerm setup codec checks route ensureInit bounds mode adversary runtime := by
  refine PqxdhDeploymentHeadlineSymbolic.chance_le_add4 _ _ _ _ _ _ fun outcome member held => ?_
  simp only [injectiveS2b, decide_eq_true_eq] at held
  rcases held with origin | shared | repeated
  · rcases PqxdhDeploymentHeadlineSymbolic.origin_s2b_sym setup codec checks route ensureInit phase1 phase2 bounds mode
      adversary budget respects runtime outcome member origin with ce | a1 | gap | coll
    · exact Or.inl ce
    · exact Or.inr (Or.inl (by simp only [decide_eq_true_eq]; exact Or.inl a1))
    · exact Or.inr (Or.inr (Or.inl gap))
    · exact Or.inr (Or.inr (Or.inr coll))
  · exact Or.inr (Or.inl (by simp only [decide_eq_true_eq]; exact Or.inr shared))
  · exact absurd repeated (replay_never setup codec checks route ensureInit bounds mode adversary runtime outcome
      member).2

/-- `ce_or_injective_s2b` (design-v2 section 7.3; the injective S2b-origin rows with CE-A1's injectivity and CE-C3, without the identity collision, which `ce_or_injective_s2b_full` adds at the same bound): the probability of a symbolic s2b origin failure, two distinct Beacons matched to one session or a Beacon owner accepting a sequence number twice is at most CE-OR s2b's bound plus `ε_A1inj` (`ce_a1_injective`: the CE-A1 bound plus `ε_inj`, real-valued) plus the explicit terms `ctGapTerm` (F-ct2) and `ctCollTerm`. Premises: those of `ce_or_s2b_sym`. -/
theorem ce_or_injective_s2b (setup : Setup baseSpec KemSK)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem)
    (codec : Codec Reader Response) (checks : Checks) (route : RawCtxServerRouting.SenderDecoder)
    (ensureInit : StateT A ProbComp Bool) (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec)
    (correct : PqxdhFullSecretInputKdf.SourceFullCorrect setup.source setup.hmac) (caps : KemCaps)
    (bounded : KemBound setup caps) (qInit : ℕ) (initBound : ∀ state, (ensureInit.run state).IsTotalQueryBound qInit)
    (frameReadBack : PqxdhServerAuthNegativeControl.FrameReadBack codec)
    (writable : PqxdhFirstBeaconRecordCanonical.ReadWritable codec.frameWrite codec.frameRead)
    (law : PqxdhServerAuthAssumptions.X25519ClassLaw setup.source.crypto)
    (spread : PqxdhServerAuthAssumptions.X25519ScalarSpread setup.source.crypto)
    (adapter : PqxdhEd25519EufCma.HasAttachedVerificationAdapter
      (fun identity => setup.source.crypto.verify identity.toList) setup.joint.verify)
    (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) (budget : Budget) (respects : budget.Respects adversary) (runtime : A)
    (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery)
    (a1Fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery) (signatureFallback : PqxdhJointIdentity.Forgery) :
    𝒟[injectiveS2b setup codec route <$>
      (PqxdhDeploymentSecrecy.game setup codec checks route ensureInit 0 bounds mode adversary).run runtime] {true} ≤
      (∑ g : Fin budget.accept × Fin budget.create,
        (ENNReal.ofReal (kemLoss setup codec checks route ensureInit bounds mode adversary budget
            (originEvent setup.source.crypto codec setup.serverKeyId budget route .s2b)
            (orClaim setup.source.crypto codec setup.serverKeyId budget route .s2b) (g.1, g.2.castSucc) runtime) +
          ENNReal.ofReal (slotLoss setup codec checks route ensureInit bounds mode adversary budget
            (originEvent setup.source.crypto codec setup.serverKeyId budget route .s2b)
            (orClaim setup.source.crypto codec setup.serverKeyId budget route .s2b) (g.1, g.2.castSucc) runtime) +
          beta setup codec route checks ensureInit bounds mode adversary budget (g.1, g.2.castSucc) runtime +
          authLoss setup codec checks route ensureInit bounds mode adversary budget (g.1, g.2.castSucc) runtime
            fallback caps qInit (slotted setup codec budget
              (originEvent setup.source.crypto codec setup.serverKeyId budget route .s2b)
              (orClaim setup.source.crypto codec setup.serverKeyId budget route .s2b) (g.1, g.2.castSucc)) +
          publicationTerm budget)) +
      ENNReal.ofReal ((∑ c : Fin budget.create, PqxdhDeploymentServerAuth.serverAuthBound setup codec checks caps
          (PqxdhDeploymentServerAuth.serverAuthAdversary setup codec route bounds mode adversary c)
          (PqxdhDeploymentServerAuthBills.coinCap caps bounds budget) budget.accept
          (PqxdhDeploymentServerAuthBills.romCap budget) (PqxdhDeploymentServerAuthBills.hashCap budget) a1Fallback
          signatureFallback) +
        ∑ target : Fin (budget.create + 1), (PqxdhJointIdentity.advantage setup.joint
          (PqxdhDeploymentServerAuthInjective.collider setup.joint budget.create target)).toReal) +
      ctGapTerm setup codec checks route ensureInit bounds mode adversary runtime +
      ctCollTerm setup codec checks route ensureInit bounds mode adversary runtime := by
  have injective := PqxdhDeploymentServerAuthInjectiveGame.ce_a1_injective setup codec checks caps bounded route
    ensureInit phase1 phase2 frameReadBack writable law spread correct adapter bounds mode adversary budget respects
    runtime a1Fallback signatureFallback
  refine (injective_s2b_le setup codec checks route ensureInit phase1 phase2 bounds mode adversary budget respects
    runtime).trans (add_le_add (add_le_add (add_le_add
      (PqxdhDeploymentHeadlineOrigin.ce_or_s2b setup functional codec checks route ensureInit phase1 phase2 correct caps
        bounded qInit initBound frameReadBack bounds mode adversary budget respects runtime fallback) ?_) le_rfl) le_rfl)
  rw [← ENNReal.ofReal_toReal (UniformTargetSelection.chance_ne_top _ _)]
  exact ENNReal.ofReal_le_ofReal injective.1

/-- `ce_or_injective_s2b_full` in event form: a symbolic s2b origin failure, two Beacons matched to one session, an identity collision or an owner record replay is a CE s2b origin failure, CE-A1's event or an identity collision (`A1NoPinnedMatch` or `IdentityCollision`; a shared match is an identity collision, `shared_collision`), a ciphertext gap or a ciphertext collision (`origin_s2b_sym`, `replay_never`). Premises: the read-back contracts and the budget. -/
theorem injective_s2b_full_le (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (ensureInit : StateT A ProbComp Bool)
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec) (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) (budget : Budget) (respects : budget.Respects adversary) (runtime : A) :
    𝒟[injectiveS2bFull setup codec route <$>
      (PqxdhDeploymentSecrecy.game setup codec checks route ensureInit 0 bounds mode adversary).run runtime] {true} ≤
      𝒟[(fun outcome => happens (originEvent setup.source.crypto codec setup.serverKeyId budget route .s2b) outcome) <$>
        (PqxdhDeploymentSecrecy.game setup codec checks route ensureInit 0 bounds mode adversary).run runtime] {true} +
      𝒟[(fun outcome => @decide ((∃ c, PqxdhDeploymentServerAuth.A1NoPinnedMatch setup codec c outcome) ∨
          PqxdhDeploymentHeadlineCollision.IdentityCollision setup outcome)
          (Classical.propDecidable _)) <$>
        (PqxdhDeploymentSecrecy.game setup codec checks route ensureInit 0 bounds mode adversary).run runtime] {true} +
      ctGapTerm setup codec checks route ensureInit bounds mode adversary runtime +
      ctCollTerm setup codec checks route ensureInit bounds mode adversary runtime := by
  refine PqxdhDeploymentHeadlineSymbolic.chance_le_add4 _ _ _ _ _ _ fun outcome member held => ?_
  simp only [injectiveS2bFull, decide_eq_true_eq] at held
  rcases held with origin | ⟨c, c', shared⟩ | collision | repeated
  · rcases PqxdhDeploymentHeadlineSymbolic.origin_s2b_sym setup codec checks route ensureInit phase1 phase2 bounds mode
      adversary budget respects runtime outcome member origin with ce | a1 | gap | coll
    · exact Or.inl ce
    · exact Or.inr (Or.inl (by simp only [decide_eq_true_eq]; exact Or.inl a1))
    · exact Or.inr (Or.inr (Or.inl gap))
    · exact Or.inr (Or.inr (Or.inr coll))
  · have identity : PqxdhDeploymentHeadlineCollision.IdentityCollision setup outcome :=
      PqxdhDeploymentServerAuthInjectiveGame.shared_collision setup codec checks route ensureInit phase1 phase2
        bounds mode adversary runtime outcome member c c' shared
    exact Or.inr (Or.inl (by simp only [decide_eq_true_eq]; exact Or.inr identity))
  · exact Or.inr (Or.inl (by simp only [decide_eq_true_eq]; exact Or.inr collision))
  · exact absurd repeated (replay_never setup codec checks route ensureInit bounds mode adversary runtime outcome
      member).2

/-- `ce_or_injective_s2b_full` (design-v2 section 7.3; the injective S2b-origin rows with CE-A1's injectivity, the identity collision and CE-C3): the probability of a symbolic s2b origin failure, two distinct Beacons matched to one session, two distinct owners with equal identity public keys (`IdentityCollision`, which covers two Beacon owners accepting frames published by one Server peer) or a Beacon owner accepting a sequence number twice is at most the right side of `ce_or_injective_s2b`: CE-OR s2b's bound plus `ε_A1inj` (the CE-A1 bound plus `ε_inj`, real-valued; `ε_inj` bounds the identity collision, `identity_collision_game`, and a shared match is an identity collision) plus the explicit terms `ctGapTerm` (F-ct2) and `ctCollTerm`. Its event contains `injectiveS2b`'s, so it implies `ce_or_injective_s2b`. Premises: those of `ce_or_injective_s2b`. -/
theorem ce_or_injective_s2b_full (setup : Setup baseSpec KemSK)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem)
    (codec : Codec Reader Response) (checks : Checks) (route : RawCtxServerRouting.SenderDecoder)
    (ensureInit : StateT A ProbComp Bool) (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec)
    (correct : PqxdhFullSecretInputKdf.SourceFullCorrect setup.source setup.hmac) (caps : KemCaps)
    (bounded : KemBound setup caps) (qInit : ℕ) (initBound : ∀ state, (ensureInit.run state).IsTotalQueryBound qInit)
    (frameReadBack : PqxdhServerAuthNegativeControl.FrameReadBack codec)
    (writable : PqxdhFirstBeaconRecordCanonical.ReadWritable codec.frameWrite codec.frameRead)
    (law : PqxdhServerAuthAssumptions.X25519ClassLaw setup.source.crypto)
    (spread : PqxdhServerAuthAssumptions.X25519ScalarSpread setup.source.crypto)
    (adapter : PqxdhEd25519EufCma.HasAttachedVerificationAdapter
      (fun identity => setup.source.crypto.verify identity.toList) setup.joint.verify)
    (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) (budget : Budget) (respects : budget.Respects adversary) (runtime : A)
    (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery)
    (a1Fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery) (signatureFallback : PqxdhJointIdentity.Forgery) :
    𝒟[injectiveS2bFull setup codec route <$>
      (PqxdhDeploymentSecrecy.game setup codec checks route ensureInit 0 bounds mode adversary).run runtime] {true} ≤
      (∑ g : Fin budget.accept × Fin budget.create,
        (ENNReal.ofReal (kemLoss setup codec checks route ensureInit bounds mode adversary budget
            (originEvent setup.source.crypto codec setup.serverKeyId budget route .s2b)
            (orClaim setup.source.crypto codec setup.serverKeyId budget route .s2b) (g.1, g.2.castSucc) runtime) +
          ENNReal.ofReal (slotLoss setup codec checks route ensureInit bounds mode adversary budget
            (originEvent setup.source.crypto codec setup.serverKeyId budget route .s2b)
            (orClaim setup.source.crypto codec setup.serverKeyId budget route .s2b) (g.1, g.2.castSucc) runtime) +
          beta setup codec route checks ensureInit bounds mode adversary budget (g.1, g.2.castSucc) runtime +
          authLoss setup codec checks route ensureInit bounds mode adversary budget (g.1, g.2.castSucc) runtime
            fallback caps qInit (slotted setup codec budget
              (originEvent setup.source.crypto codec setup.serverKeyId budget route .s2b)
              (orClaim setup.source.crypto codec setup.serverKeyId budget route .s2b) (g.1, g.2.castSucc)) +
          publicationTerm budget)) +
      ENNReal.ofReal ((∑ c : Fin budget.create, PqxdhDeploymentServerAuth.serverAuthBound setup codec checks caps
          (PqxdhDeploymentServerAuth.serverAuthAdversary setup codec route bounds mode adversary c)
          (PqxdhDeploymentServerAuthBills.coinCap caps bounds budget) budget.accept
          (PqxdhDeploymentServerAuthBills.romCap budget) (PqxdhDeploymentServerAuthBills.hashCap budget) a1Fallback
          signatureFallback) +
        ∑ target : Fin (budget.create + 1), (PqxdhJointIdentity.advantage setup.joint
          (PqxdhDeploymentServerAuthInjective.collider setup.joint budget.create target)).toReal) +
      ctGapTerm setup codec checks route ensureInit bounds mode adversary runtime +
      ctCollTerm setup codec checks route ensureInit bounds mode adversary runtime := by
  classical
  set run := (PqxdhDeploymentSecrecy.game setup codec checks route ensureInit 0 bounds mode adversary).run runtime
  have unmatched := PqxdhDeploymentServerAuthBills.ce_a1_billed setup codec checks caps bounded route ensureInit 0
    phase1 phase2 frameReadBack writable law spread correct adapter bounds mode adversary budget respects runtime
    a1Fallback signatureFallback
  have collision := PqxdhDeploymentHeadlineCollision.identity_collision_game setup codec checks route ensureInit phase1
    phase2 bounds mode adversary budget respects runtime
  have split := chance_le_add_support run
    (fun outcome => @decide ((∃ c, PqxdhDeploymentServerAuth.A1NoPinnedMatch setup codec c outcome) ∨
      PqxdhDeploymentHeadlineCollision.IdentityCollision setup outcome) (Classical.propDecidable _))
    (fun outcome => @decide (∃ c, PqxdhDeploymentServerAuth.A1NoPinnedMatch setup codec c outcome)
      (Classical.propDecidable _))
    (fun outcome => @decide (PqxdhDeploymentHeadlineCollision.IdentityCollision setup outcome)
      (Classical.propDecidable _))
    fun outcome _ held => by simpa using held
  have finiteSum : PqxdhDeploymentHeadlineCollision.injTerm setup budget ≠ ⊤ :=
    ENNReal.sum_ne_top.mpr fun _ _ => ne_top_of_le_ne_top ENNReal.one_ne_top probOutput_le_one
  have joint : 𝒟[(fun outcome => @decide ((∃ c, PqxdhDeploymentServerAuth.A1NoPinnedMatch setup codec c outcome) ∨
      PqxdhDeploymentHeadlineCollision.IdentityCollision setup outcome) (Classical.propDecidable _)) <$> run] {true} ≤
      ENNReal.ofReal ((∑ c : Fin budget.create, PqxdhDeploymentServerAuth.serverAuthBound setup codec checks caps
          (PqxdhDeploymentServerAuth.serverAuthAdversary setup codec route bounds mode adversary c)
          (PqxdhDeploymentServerAuthBills.coinCap caps bounds budget) budget.accept
          (PqxdhDeploymentServerAuthBills.romCap budget) (PqxdhDeploymentServerAuthBills.hashCap budget) a1Fallback
          signatureFallback) +
        ∑ target : Fin (budget.create + 1), (PqxdhJointIdentity.advantage setup.joint
          (PqxdhDeploymentServerAuthInjective.collider setup.joint budget.create target)).toReal) := by
    rw [← ENNReal.ofReal_toReal (UniformTargetSelection.chance_ne_top _ _)]
    refine ENNReal.ofReal_le_ofReal ((ENNReal.toReal_mono (ENNReal.add_ne_top.mpr
      ⟨UniformTargetSelection.chance_ne_top _ _, UniformTargetSelection.chance_ne_top _ _⟩) split).trans ?_)
    rw [ENNReal.toReal_add (UniformTargetSelection.chance_ne_top _ _) (UniformTargetSelection.chance_ne_top _ _)]
    refine add_le_add unmatched.1 ?_
    rw [← ENNReal.toReal_sum fun target _ => ne_top_of_le_ne_top finiteSum
      (Finset.single_le_sum (fun _ _ => zero_le) (Finset.mem_univ target))]
    exact ENNReal.toReal_mono finiteSum collision
  exact (injective_s2b_full_le setup codec checks route ensureInit phase1 phase2 bounds mode adversary budget respects
    runtime).trans (add_le_add (add_le_add (add_le_add
      (PqxdhDeploymentHeadlineOrigin.ce_or_s2b setup functional codec checks route ensureInit phase1 phase2 correct caps
        bounded qInit initBound frameReadBack bounds mode adversary budget respects runtime fallback) joint) le_rfl) le_rfl)

end Injective

end BeaconcryptCore.Computational.PqxdhDeploymentHeadlineInjective

-- Axiom guards (generated)

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineInjective.replay_never' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineInjective.replay_never

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineInjective.injective_b2s_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineInjective.injective_b2s_le

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineInjective.ce_or_injective_b2s' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineInjective.ce_or_injective_b2s

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineInjective.injective_s2b_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineInjective.injective_s2b_le

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineInjective.ce_or_injective_s2b' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineInjective.ce_or_injective_s2b

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineInjective.injective_s2b_full_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineInjective.injective_s2b_full_le

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineInjective.ce_or_injective_s2b_full' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineInjective.ce_or_injective_s2b_full
