import BeaconcryptCore.Computational.RawCtxSelectedProtocolOriginCases

/-!
The selected-key inner-production error is a concrete event over actual accepted positions of the finite role family. It ranges over all recorded attempts without selecting another raw-query index. Successful publication, installation/session agreement, selection of the protected source key, and its joint distribution remain separate obligations.
-/
open OracleComp OracleSpec ENNReal
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RawCtxSelectedProtocolOriginEvent
open PqxdhSecretInputKdf PqxdhFullSecretInputKdf PqxdhJointKdfGame
open RawCtxSelectedParentTable RawCtxSelectedParentEntry CtxRomAuth AdaptiveCtxReceive
open RawCtxSelectedAuthenticationObserver RawCtxSelectedPlaintextOrigins
open RawCtxSelectedProductionAudit (Audit Record)
open RawCtxSelectedAcceptanceOrigins (KnownRoute PriorProduction)
open RawCtxSelectedProtocolOriginCases (Fields)

structure Parameters (M : Type) where
  source : FixedHkdfSha512NoSaltSource
  writer : RawCtxMixedShared.Writer
  prior : Prior
  parent : Option Entry
  target : RootOutput
  nonce : NonceOutput
  next : RootOutput
  sender : M → Aeneas.Std.U64
  route : RawCtxServerRouting.SenderDecoder
  read : RawCtxReceive.FrameDecoder

def NoOrigin {M P I D K : Type} {S B : Nat} (p : Parameters M) (initial : State)
    (preceding : List (Record M P I D K S B)) (bytes ad : Pqxdh.Bytes)
    (decrypted : RawCtxWholeOwner.Decrypted) : Prop :=
  ∀ entry, ¬(PriorProduction p.source p.writer p.prior p.parent p.target p.nonce p.next p.sender p.route p.read
    initial preceding entry ∧ Fields p.read bytes ad decrypted entry)

def BeaconFailure {M P I D K : Type} {S B : Nat} (p : Parameters M)
    (initial final : Audit M P I D K S B) : Prop :=
  ∃ (preceding suffix : List (Record M P I D K S B)) (index : Fin B) (bytes : Pqxdh.Bytes)
    (roles finalRoles : RawCtxGenericRoleFamily.Roles RawCtxSelectedMessageReveals.Kernel M P I D K S B)
    (before after : State) (decrypted : RawCtxWholeOwner.Decrypted),
    final.records = initial.records ++ (preceding ++
      ⟨.inr (.inl ⟨index, .inr bytes⟩), roles, some (.Some decrypted, finalRoles), before, after⟩ :: suffix) ∧
    ∀ control ad kernel, (roles.2 index).beacon.phase = .established control ad kernel →
      ¬KnownRoute p.prior p.parent p.target p.nonce p.next p.read bytes
        (RawCtxGenericBeacon.selected (roles.2 index) control ad kernel) ∧
      NoOrigin p initial.observer preceding bytes
        (RawCtxGenericBeacon.selected (roles.2 index) control ad kernel).associatedData decrypted

def ServerFailure {M P I D K : Type} {S B : Nat} (p : Parameters M)
    (initial final : Audit M P I D K S B) : Prop :=
  ∃ (preceding suffix : List (Record M P I D K S B)) (index : Fin S) (bytes : Pqxdh.Bytes)
    (roles finalRoles : RawCtxGenericRoleFamily.Roles RawCtxSelectedMessageReveals.Kernel M P I D K S B)
    (before after : State) (decrypted : RawCtxWholeOwner.Decrypted),
    final.records = initial.records ++ (preceding ++
      ⟨.inl ⟨index, .inr bytes⟩, roles, some (.Some decrypted, finalRoles), before, after⟩ :: suffix) ∧
    ∀ kid ad peer, p.route bytes = some kid →
      RawCtxGenericServer.peerAssociatedData (roles.1 index).server kid = some ad →
      (roles.1 index).server.peers kid = some peer →
      ¬KnownRoute p.prior p.parent p.target p.nonce p.next p.read bytes
        (RawCtxGenericServer.selectedOwner kid ad peer (roles.1 index).rawAttempts) ∧
      NoOrigin p initial.observer preceding bytes
        (RawCtxGenericServer.selectedOwner kid ad peer (roles.1 index).rawAttempts).associatedData decrypted

def Failure {M P I D K : Type} {S B : Nat} (p : Parameters M)
    (initial final : Audit M P I D K S B) : Prop :=
  BeaconFailure p initial final ∨ ServerFailure p initial final

noncomputable def client {M P I D K Result : Type} {S B : Nat} (p : Parameters M)
    (original : OracleComp (RawCtxProtocolReveals.SourceSpec S B) Result) (state : Audit M P I D K S B) :=
  RawCtxSelectedProductionAudit.client p.source p.writer p.prior p.parent p.target p.nonce p.next p.sender p.route p.read original state

/-- Any selected-key Beacon origin error anywhere in the actual adaptive audit supplies the same final ordinary integrity winner; no raw-attempt ordinal is sampled here. -/
theorem beacon_wins {M P I D K Result : Type} {S B : Nat} (p : Parameters M)
    (c : Pqxdh.Crypto) (key : CtxKey)
    (original : OracleComp (RawCtxProtocolReveals.SourceSpec S B) Result)
    (state : Audit M P I D K S B) (component : AdaptiveCtxDynamicKnownKeys.SourceState)
    (good : Good (RawCtxUniversalDecoder.decoder p.read) c key (state.observer, component))
    (result : (Option Result × Audit M P I D K S B) × AdaptiveCtxDynamicKnownKeys.SourceState)
    (supported : result ∈ support ((simulateQ (AdaptiveCtxDynamicKnownKeys.sourceImpl true
      (RawCtxUniversalDecoder.decoder p.read) c key) (client p original state)).run component))
    (failure : BeaconFailure p state result.1.2) :
    won (RawCtxUniversalDecoder.decoder p.read) result.1.2.observer = true := by
  obtain ⟨preceding, suffix, index, bytes, roles, finalRoles, before, after, decrypted, position, missing⟩ := failure
  obtain ⟨control, ad, kernel, finalOwner, established, published, branch⟩ :=
    RawCtxSelectedProtocolOriginCases.beacon_cases p.source p.writer p.prior p.parent p.target p.nonce p.next
      p.sender p.route p.read c key original state component good result supported preceding suffix index bytes
      roles finalRoles before after decrypted position
  rcases branch with known | winning | ⟨entry, _, produced, fields⟩
  · exact False.elim ((missing control ad kernel established).1 known)
  · exact winning
  · exact False.elim ((missing control ad kernel established).2 entry ⟨produced, fields⟩)

/-- Every actual selected-key Server origin error at any stored position yields the same final observer win, retaining the source route and both lookups. -/
theorem server_wins {M P I D K Result : Type} {S B : Nat} (p : Parameters M)
    (c : Pqxdh.Crypto) (key : CtxKey)
    (original : OracleComp (RawCtxProtocolReveals.SourceSpec S B) Result)
    (state : Audit M P I D K S B) (component : AdaptiveCtxDynamicKnownKeys.SourceState)
    (good : Good (RawCtxUniversalDecoder.decoder p.read) c key (state.observer, component))
    (result : (Option Result × Audit M P I D K S B) × AdaptiveCtxDynamicKnownKeys.SourceState)
    (supported : result ∈ support ((simulateQ (AdaptiveCtxDynamicKnownKeys.sourceImpl true
      (RawCtxUniversalDecoder.decoder p.read) c key) (client p original state)).run component))
    (failure : ServerFailure p state result.1.2) :
    won (RawCtxUniversalDecoder.decoder p.read) result.1.2.observer = true := by
  obtain ⟨preceding, suffix, index, bytes, roles, finalRoles, before, after, decrypted, position, missing⟩ := failure
  obtain ⟨kid, ad, peer, finalOwner, routed, adFound, peerFound, published, branch⟩ :=
    RawCtxSelectedProtocolOriginCases.server_cases p.source p.writer p.prior p.parent p.target p.nonce p.next
      p.sender p.route p.read c key original state component good result supported preceding suffix index bytes
      roles finalRoles before after decrypted position
  rcases branch with known | winning | ⟨entry, _, produced, fields⟩
  · exact False.elim ((missing kid ad peer routed adFound peerFound).1 known)
  · exact winning
  · exact False.elim ((missing kid ad peer routed adFound peerFound).2 entry ⟨produced, fields⟩)

/-- The union over both finite role families and every actual accepted position uses one ordinary all-attempt winner, without a further session or record multiplier at this selected-key layer. -/
theorem failure_wins {M P I D K Result : Type} {S B : Nat} (p : Parameters M)
    (c : Pqxdh.Crypto) (key : CtxKey)
    (original : OracleComp (RawCtxProtocolReveals.SourceSpec S B) Result)
    (state : Audit M P I D K S B) (component : AdaptiveCtxDynamicKnownKeys.SourceState)
    (good : Good (RawCtxUniversalDecoder.decoder p.read) c key (state.observer, component))
    (result : (Option Result × Audit M P I D K S B) × AdaptiveCtxDynamicKnownKeys.SourceState)
    (supported : result ∈ support ((simulateQ (AdaptiveCtxDynamicKnownKeys.sourceImpl true
      (RawCtxUniversalDecoder.decoder p.read) c key) (client p original state)).run component))
    (failure : Failure p state result.1.2) :
    won (RawCtxUniversalDecoder.decoder p.read) result.1.2.observer = true := by
  exact failure.elim (beacon_wins p c key original state component good result supported)
    (server_wins p c key original state component good result supported)

def begin {M P I D K : Type} {S B : Nat} (front : RawCtxSelectedFamilyLiveCompiler.Front M P I D K S B) :
    Audit M P I D K S B := ⟨front, initialState, []⟩

noncomputable def base {M P I D K Result : Type} {S B : Nat} (p : Parameters M)
    (original : OracleComp (RawCtxProtocolReveals.SourceSpec S B) Result)
    (front : RawCtxSelectedFamilyLiveCompiler.Front M P I D K S B) :=
  RawCtxSelectedFamilyLiveCompiler.client p.source p.writer p.prior p.parent p.target p.nonce p.next
    p.sender p.route p.read original front

/-- The initialized source audit's computed winner is exactly the existing executable ordinary observer on the original compiled record/reveal client. -/
theorem decision_exact {M P I D K Result : Type} {S B : Nat} (p : Parameters M)
    (original : OracleComp (RawCtxProtocolReveals.SourceSpec S B) Result)
    (front : RawCtxSelectedFamilyLiveCompiler.Front M P I D K S B) :
    (fun result => won (RawCtxUniversalDecoder.decoder p.read) result.2.observer) <$> client p original (begin front) =
      decision (RawCtxUniversalDecoder.decoder p.read) (base p original front) := by
  have same := congrArg (fun work => (fun result => won (RawCtxUniversalDecoder.decoder p.read) result.2) <$> work)
    (RawCtxSelectedProductionAudit.client_erase p.source p.writer p.prior p.parent p.target p.nonce p.next
      p.sender p.route p.read original (begin front))
  simpa only [Functor.map_map, RawCtxSelectedProductionAudit.erase, begin, decision, base, client] using same

/-- The actual uniform-key ordinary source game carries the same initialized audit winner, retaining complete component state and all optional source outputs. -/
theorem game_decision {M P I D K Result : Type} {S B : Nat} (p : Parameters M)
    (real : Bool) (c : Pqxdh.Crypto)
    (original : OracleComp (RawCtxProtocolReveals.SourceSpec S B) Result)
    (front : RawCtxSelectedFamilyLiveCompiler.Front M P I D K S B) :
    (fun result => won (RawCtxUniversalDecoder.decoder p.read) result.1.2.observer) <$>
      AdaptiveCtxDynamicKnownKeys.sourceGame real (RawCtxUniversalDecoder.decoder p.read) c (client p original (begin front)) =
      Prod.fst <$> AdaptiveCtxDynamicKnownKeys.sourceGame real (RawCtxUniversalDecoder.decoder p.read) c
        (decision (RawCtxUniversalDecoder.decoder p.read) (base p original front)) := by
  have same := congrArg (fun work => Prod.fst <$> AdaptiveCtxDynamicKnownKeys.sourceGame
    real (RawCtxUniversalDecoder.decoder p.read) c work) (decision_exact p original front)
  simpa only [AdaptiveCtxDynamicKnownKeys.sourceGame, map_bind, simulateQ_map, StateT.run_map, Functor.map_map] using same

/-- Every supported ordinary source-game origin error yields the concrete executable winner, with the empty history invariant discharged rather than assumed. -/
theorem game_wins {M P I D K Result : Type} {S B : Nat} (p : Parameters M)
    (c : Pqxdh.Crypto) (original : OracleComp (RawCtxProtocolReveals.SourceSpec S B) Result)
    (front : RawCtxSelectedFamilyLiveCompiler.Front M P I D K S B)
    (result : (Option Result × Audit M P I D K S B) × AdaptiveCtxDynamicKnownKeys.SourceState)
    (supported : result ∈ support (AdaptiveCtxDynamicKnownKeys.sourceGame true
      (RawCtxUniversalDecoder.decoder p.read) c (client p original (begin front))))
    (failure : Failure p (begin front) result.1.2) :
    won (RawCtxUniversalDecoder.decoder p.read) result.1.2.observer = true := by
  simp only [AdaptiveCtxDynamicKnownKeys.sourceGame, mem_support_bind_iff] at supported
  obtain ⟨key, _, supported⟩ := supported
  exact failure_wins p c key original (begin front) AdaptiveCtxDynamicKnownKeys.initialSource
    (RawCtxSelectedPlaintextOrigins.initial_good (RawCtxUniversalDecoder.decoder p.read) c key) result supported failure

/-- The concrete missing-production event is bounded by the unchanged ordinary observer probability, with coefficient one across all roles and recorded attempts of this selected-key game. -/
theorem probability {M P I D K Result : Type} {S B : Nat} (p : Parameters M)
    (c : Pqxdh.Crypto) (original : OracleComp (RawCtxProtocolReveals.SourceSpec S B) Result)
    (front : RawCtxSelectedFamilyLiveCompiler.Front M P I D K S B) :
    RawCtxSelectedNativeFreshLift.mass (fun result => Failure p (begin front) result.1.2)
      (AdaptiveCtxDynamicKnownKeys.sourceGame true (RawCtxUniversalDecoder.decoder p.read) c (client p original (begin front))) ≤
      𝒟[Prod.fst <$> AdaptiveCtxDynamicKnownKeys.sourceGame true (RawCtxUniversalDecoder.decoder p.read) c
        (decision (RawCtxUniversalDecoder.decoder p.read) (base p original front))] {true} := by
  rw [← game_decision]
  unfold RawCtxSelectedNativeFreshLift.mass
  simp only [evalDist_apply_singleton, ← probEvent_eq_eq_probOutput, probEvent_map, Function.comp_def, decide_eq_true_eq]
  exact probEvent_mono fun result supported event => game_wins p c original front result supported event

open AdaptiveCtxDynamicKnownBounds AdaptiveCtxQueryBounds AdaptiveCtxSharedReplayBounds
open CtxNonceAeadIntCtxt CtxNonceAeadIndDollarValidation

/-- The actual selected-key protocol-production event consumes the ordinary validation and adaptive raw-integrity reductions, with every indexed attempt and explicit statistical term retained. -/
theorem authentication_bound {M P I D K Result : Type} {S B : Nat} (p : Parameters M)
    (c : Pqxdh.Crypto) (fallback : ModifiedNonceAeadForgery)
    (original : OracleComp (RawCtxProtocolReveals.SourceSpec S B) Result)
    (front : RawCtxSelectedFamilyLiveCompiler.Front M P I D K S B)
    (qHash qSeal qRaw : Nat)
    (hashBound : (base p original front).IsQueryBoundP HashRoute qHash)
    (sealBound : (base p original front).IsQueryBoundP (TargetClass SourceSeal) qSeal)
    (rawBound : (base p original front).IsQueryBoundP (TargetClass IsRawQuery) qRaw)
    (small : qSeal < 2 ^ 96) :
    let decode := RawCtxUniversalDecoder.decoder p.read
    let reduction := AdaptiveCtxDynamicKnownKeys.decisionClient c (decision decode (base p original front))
    RawCtxSelectedNativeFreshLift.mass (fun result => Failure p (begin front) result.1.2)
      (AdaptiveCtxDynamicKnownKeys.sourceGame true decode c (client p original (begin front))) ≤
      ENNReal.ofReal (modifiedNonceAeadINDDollarAdvantage c
        (AdaptiveCtxPrefixValidation.validationReduction decode c reduction qHash)) +
      (qHash : ℝ≥0∞) * (((2 ^ 128 : Nat) : ℝ≥0∞))⁻¹ +
      2 * ∑ index ∈ Finset.range qRaw, modifiedNonceAeadINTCTXTAdvantage c
        (AdaptiveRawNonceAead.indexedReduction (baseDecoder decode) fallback
          (AdaptiveCtxReceive.wrapped decode reduction) index) +
      (qRaw : ℝ≥0∞) / (2 ^ 512 : Nat) := by
  exact (probability p c original front).trans
    (RawCtxSelectedAuthenticationObserver.authentication_bound (RawCtxUniversalDecoder.decoder p.read) c fallback
      (base p original front) qHash qSeal qRaw hashBound sealBound rawBound small)

/-- The actual ordinary decision reduction retains separate random, shared-hash, selected-seal and selected-raw allowances from the same executable protocol client. -/
theorem reduction_budgets {M P I D K Result : Type} {S B : Nat} (p : Parameters M)
    (c : Pqxdh.Crypto) (original : OracleComp (RawCtxProtocolReveals.SourceSpec S B) Result)
    (front : RawCtxSelectedFamilyLiveCompiler.Front M P I D K S B)
    (qUniform qHash qSeal qRaw : Nat)
    (uniformBound : (base p original front).IsQueryBoundP UniformRoute qUniform)
    (hashBound : (base p original front).IsQueryBoundP HashRoute qHash)
    (sealBound : (base p original front).IsQueryBoundP (TargetClass SourceSeal) qSeal)
    (rawBound : (base p original front).IsQueryBoundP (TargetClass IsRawQuery) qRaw) :
    let reduction := AdaptiveCtxDynamicKnownKeys.decisionClient c
      (decision (RawCtxUniversalDecoder.decoder p.read) (base p original front))
    reduction.IsQueryBoundP SourceUniform qUniform ∧ reduction.IsQueryBoundP SourceHash qHash ∧
      reduction.IsQueryBoundP SourceSeal qSeal ∧ reduction.IsQueryBoundP IsRawQuery qRaw := by
  exact AdaptiveCtxDynamicKnownBounds.decision_budgets c _ qUniform qHash qSeal qRaw
    ((decision_queries _ _ _ _).mpr uniformBound) ((decision_queries _ _ _ _).mpr hashBound)
    ((decision_queries _ _ _ _).mpr sealBound) ((decision_queries _ _ _ _).mpr rawBound)

/-- The original six-coordinate schedule supplies concrete component and ordinary reduction allowances. This conservative total includes every send, raw attempt, explicit coin, public hash and public HKDF request; reveals still count in the original source budget. -/
theorem source_budgets {M P I D K Result : Type} {S B : Nat} (p : Parameters M)
    (c : Pqxdh.Crypto) (original : OracleComp (RawCtxProtocolReveals.SourceSpec S B) Result)
    (front : RawCtxSelectedFamilyLiveCompiler.Front M P I D K S B)
    (budget : RawCtxRevealBudgets.Budget) (bounded : RawCtxRevealBudgets.Bounded original budget) :
    let q := RawCtxRevealBudgets.bill (fun _ => 1) 0 budget
    let reduction := AdaptiveCtxDynamicKnownKeys.decisionClient c
      (decision (RawCtxUniversalDecoder.decoder p.read) (base p original front))
    (base p original front).IsTotalQueryBound q ∧
      reduction.IsQueryBoundP SourceUniform q ∧ reduction.IsQueryBoundP SourceHash q ∧
      reduction.IsQueryBoundP SourceSeal q ∧ reduction.IsQueryBoundP IsRawQuery q := by
  have counted := RawCtxSelectedFamilyLiveCompiler.client_queries p.source p.writer p.prior p.parent
    p.target p.nonce p.next p.sender p.route p.read original budget bounded front
  exact ⟨counted, reduction_budgets p c original front _ _ _ _
    counted.isQueryBoundP counted.isQueryBoundP counted.isQueryBoundP counted.isQueryBoundP⟩

/-- The original bounded protocol schedule discharges every component-query premise in the accepted-origin reduction. Every adaptive attempt is retained; this conservative fallback adds no second record-selection factor. -/
theorem source_bound {M P I D K Result : Type} {S B : Nat} (p : Parameters M)
    (c : Pqxdh.Crypto) (fallback : ModifiedNonceAeadForgery)
    (original : OracleComp (RawCtxProtocolReveals.SourceSpec S B) Result)
    (front : RawCtxSelectedFamilyLiveCompiler.Front M P I D K S B)
    (budget : RawCtxRevealBudgets.Budget) (bounded : RawCtxRevealBudgets.Bounded original budget)
    (small : RawCtxRevealBudgets.bill (fun _ => 1) 0 budget < 2 ^ 96) :
    let q := RawCtxRevealBudgets.bill (fun _ => 1) 0 budget
    let decode := RawCtxUniversalDecoder.decoder p.read
    let reduction := AdaptiveCtxDynamicKnownKeys.decisionClient c (decision decode (base p original front))
    RawCtxSelectedNativeFreshLift.mass (fun result => Failure p (begin front) result.1.2)
      (AdaptiveCtxDynamicKnownKeys.sourceGame true decode c (client p original (begin front))) ≤
      ENNReal.ofReal (modifiedNonceAeadINDDollarAdvantage c
        (AdaptiveCtxPrefixValidation.validationReduction decode c reduction q)) +
      (q : ℝ≥0∞) * (((2 ^ 128 : Nat) : ℝ≥0∞))⁻¹ +
      2 * ∑ index ∈ Finset.range q, modifiedNonceAeadINTCTXTAdvantage c
        (AdaptiveRawNonceAead.indexedReduction (baseDecoder decode) fallback
          (AdaptiveCtxReceive.wrapped decode reduction) index) +
      (q : ℝ≥0∞) / (2 ^ 512 : Nat) := by
  have counted := (source_budgets p c original front budget bounded).1
  exact authentication_bound p c fallback original front _ _ _
    counted.isQueryBoundP counted.isQueryBoundP counted.isQueryBoundP small

end BeaconcryptCore.Computational.RawCtxSelectedProtocolOriginEvent

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedProtocolOriginEvent.beacon_wins' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedProtocolOriginEvent.beacon_wins
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedProtocolOriginEvent.server_wins' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedProtocolOriginEvent.server_wins
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedProtocolOriginEvent.failure_wins' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedProtocolOriginEvent.failure_wins
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedProtocolOriginEvent.decision_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedProtocolOriginEvent.decision_exact
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedProtocolOriginEvent.game_decision' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedProtocolOriginEvent.game_decision
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedProtocolOriginEvent.game_wins' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedProtocolOriginEvent.game_wins
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedProtocolOriginEvent.probability' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedProtocolOriginEvent.probability
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedProtocolOriginEvent.authentication_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedProtocolOriginEvent.authentication_bound
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedProtocolOriginEvent.reduction_budgets' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedProtocolOriginEvent.reduction_budgets
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedProtocolOriginEvent.source_budgets' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedProtocolOriginEvent.source_budgets
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedProtocolOriginEvent.source_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedProtocolOriginEvent.source_bound
