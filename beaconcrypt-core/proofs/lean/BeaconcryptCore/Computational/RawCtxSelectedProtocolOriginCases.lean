import BeaconcryptCore.Computational.RawCtxSelectedPlaintextOrigins

/-!
The actual interpreted finite role family classifies every accepted raw record into reached known material, the ordinary all-attempt integrity winner, or an exact earlier source cryptographic production. The final alternative keeps failed writing, arbitrary initial receipts, and session/installation origin separate. These are concrete source event implications, not a new primitive security contract.
-/
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RawCtxSelectedProtocolOriginCases
open PqxdhSecretInputKdf PqxdhFullSecretInputKdf PqxdhJointKdfGame
open RawCtxSelectedParentTable RawCtxSelectedParentEntry CtxRomAuth
open RawCtxSelectedAuthenticationObserver RawCtxSelectedPlaintextOrigins
open RawCtxSelectedProductionAudit (Audit Record)
open RawCtxSelectedAcceptanceOrigins (KnownRoute PriorProduction)

def Fields (read : RawCtxReceive.FrameDecoder) (bytes ad : Pqxdh.Bytes)
    (decrypted : RawCtxWholeOwner.Decrypted) (entry : CtxSuccessfulSeal) : Prop :=
  decrypted.plaintext = entry.input.plaintext ∧ ad = entry.input.context.ad.bytes ∧
    decrypted.sequence.val = entry.input.context.ad.seq ∧ decrypted.keyId.val = entry.input.context.ad.sid ∧
    ∃ frame, read bytes = some frame ∧ frame.payload = entry.record.encode

private theorem actual_support {Result : Type} (decode : AdaptiveCtxReceive.RawDecoder)
    (c : Pqxdh.Crypto) (key : CtxKey) (client : OracleComp AdaptiveCtxDynamicKnownKeys.Spec Result)
    (state : AdaptiveCtxDynamicKnownKeys.SourceState) (result : Result × AdaptiveCtxDynamicKnownKeys.SourceState)
    (supported : result ∈ support ((simulateQ (AdaptiveCtxDynamicKnownKeys.sourceImpl true decode c key) client).run state)) :
    result.1 ∈ support client := by
  apply support_simulateQ_run'_subset (AdaptiveCtxDynamicKnownKeys.sourceImpl true decode c key) client state
  rw [StateT.run'_eq, support_map]
  exact ⟨result, supported, rfl⟩

/-- Every actual accepted Beacon position has an exhaustive cryptographic origin classification, with the original complete role publication and the same accepted plaintext. -/
theorem beacon_cases {M P I D K Result : Type} {S B : Nat}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (parent : Option Entry) (target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (sender : M → Aeneas.Std.U64) (route : RawCtxServerRouting.SenderDecoder) (read : RawCtxReceive.FrameDecoder)
    (c : Pqxdh.Crypto) (key : CtxKey)
    (original : OracleComp (RawCtxProtocolReveals.SourceSpec S B) Result)
    (state : Audit M P I D K S B) (component : AdaptiveCtxDynamicKnownKeys.SourceState)
    (good : Good (RawCtxUniversalDecoder.decoder read) c key (state.observer, component))
    (result : (Option Result × Audit M P I D K S B) × AdaptiveCtxDynamicKnownKeys.SourceState)
    (supported : result ∈ support ((simulateQ (AdaptiveCtxDynamicKnownKeys.sourceImpl true
      (RawCtxUniversalDecoder.decoder read) c key)
      (RawCtxSelectedProductionAudit.client source writer prior parent target nonce next sender route read original state)).run component))
    (preceding suffix : List (Record M P I D K S B)) (index : Fin B) (bytes : Pqxdh.Bytes)
    (roles finalRoles : RawCtxGenericRoleFamily.Roles RawCtxSelectedMessageReveals.Kernel M P I D K S B)
    (before after : State) (decrypted : RawCtxWholeOwner.Decrypted)
    (position : result.1.2.records = state.records ++ (preceding ++
      ⟨.inr (.inl ⟨index, .inr bytes⟩), roles, some (.Some decrypted, finalRoles), before, after⟩ :: suffix)) :
    ∃ control ad kernel finalOwner,
      (roles.2 index).beacon.phase = .established control ad kernel ∧
      finalRoles = (roles.1, Function.update roles.2 index
        (RawCtxGenericBeacon.reinstall (roles.2 index) control ad finalOwner)) ∧
      (KnownRoute prior parent target nonce next read bytes (RawCtxGenericBeacon.selected (roles.2 index) control ad kernel) ∨
        won (RawCtxUniversalDecoder.decoder read) result.1.2.observer = true ∨
        ∃ entry ∈ before.seals, PriorProduction source writer prior parent target nonce next sender route read
          state.observer preceding entry ∧ Fields read bytes
            (RawCtxGenericBeacon.selected (roles.2 index) control ad kernel).associatedData decrypted entry) := by
  have syntactic := actual_support (RawCtxUniversalDecoder.decoder read) c key _ component result supported
  obtain ⟨control, ad, kernel, finalOwner, established, published, branch⟩ :=
    RawCtxSelectedAcceptanceOrigins.audited_beacon_cases source writer prior parent target nonce next sender route read
      original state result.1 syntactic preceding suffix index bytes roles finalRoles before after decrypted position
  refine ⟨control, ad, kernel, finalOwner, established, published, ?_⟩
  rcases branch with known | winning | matching
  · exact Or.inl known
  · exact Or.inr (Or.inl winning)
  · have correct := current_correct source writer prior parent target nonce next sender route read c key original
      state component good result supported preceding suffix
      ⟨.inr (.inl ⟨index, .inr bytes⟩), roles, some (.Some decrypted, finalRoles), before, after⟩ position
    obtain ⟨entry, member, fields⟩ := matching_plaintext prior parent target nonce next read bytes
      (RawCtxGenericBeacon.selected (roles.2 index) control ad kernel) decrypted before after matching.1 correct.2.1
    exact Or.inr (Or.inr ⟨entry, member, matching.2 entry member, fields⟩)

/-- Actual Server acceptance retains routing, repeated AD/peer lookup and peer publication while deriving the same complete cryptographic-origin alternatives. -/
theorem server_cases {M P I D K Result : Type} {S B : Nat}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (parent : Option Entry) (target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (sender : M → Aeneas.Std.U64) (route : RawCtxServerRouting.SenderDecoder) (read : RawCtxReceive.FrameDecoder)
    (c : Pqxdh.Crypto) (key : CtxKey)
    (original : OracleComp (RawCtxProtocolReveals.SourceSpec S B) Result)
    (state : Audit M P I D K S B) (component : AdaptiveCtxDynamicKnownKeys.SourceState)
    (good : Good (RawCtxUniversalDecoder.decoder read) c key (state.observer, component))
    (result : (Option Result × Audit M P I D K S B) × AdaptiveCtxDynamicKnownKeys.SourceState)
    (supported : result ∈ support ((simulateQ (AdaptiveCtxDynamicKnownKeys.sourceImpl true
      (RawCtxUniversalDecoder.decoder read) c key)
      (RawCtxSelectedProductionAudit.client source writer prior parent target nonce next sender route read original state)).run component))
    (preceding suffix : List (Record M P I D K S B)) (index : Fin S) (bytes : Pqxdh.Bytes)
    (roles finalRoles : RawCtxGenericRoleFamily.Roles RawCtxSelectedMessageReveals.Kernel M P I D K S B)
    (before after : State) (decrypted : RawCtxWholeOwner.Decrypted)
    (position : result.1.2.records = state.records ++ (preceding ++
      ⟨.inl ⟨index, .inr bytes⟩, roles, some (.Some decrypted, finalRoles), before, after⟩ :: suffix)) :
    ∃ kid ad peer, ∃ finalOwner : RawCtxChainOwner.State RawCtxSelectedMessageReveals.Kernel P,
      route bytes = some kid ∧ RawCtxGenericServer.peerAssociatedData (roles.1 index).server kid = some ad ∧
      (roles.1 index).server.peers kid = some peer ∧
      finalRoles = (Function.update roles.1 index
        ⟨RawCtxGenericServer.putPeer (roles.1 index).server kid peer finalOwner.kernel, finalOwner.rawAttempts⟩, roles.2) ∧
      (KnownRoute prior parent target nonce next read bytes (RawCtxGenericServer.selectedOwner kid ad peer (roles.1 index).rawAttempts) ∨
        won (RawCtxUniversalDecoder.decoder read) result.1.2.observer = true ∨
        ∃ entry ∈ before.seals, PriorProduction source writer prior parent target nonce next sender route read
          state.observer preceding entry ∧ Fields read bytes
            (RawCtxGenericServer.selectedOwner kid ad peer (roles.1 index).rawAttempts).associatedData decrypted entry) := by
  have syntactic := actual_support (RawCtxUniversalDecoder.decoder read) c key _ component result supported
  obtain ⟨kid, ad, peer, finalOwner, routed, adFound, peerFound, published, branch⟩ :=
    RawCtxSelectedAcceptanceOrigins.audited_server_cases source writer prior parent target nonce next sender route read
      original state result.1 syntactic preceding suffix index bytes roles finalRoles before after decrypted position
  refine ⟨kid, ad, peer, finalOwner, routed, adFound, peerFound, published, ?_⟩
  rcases branch with known | winning | matching
  · exact Or.inl known
  · exact Or.inr (Or.inl winning)
  · have correct := current_correct source writer prior parent target nonce next sender route read c key original
      state component good result supported preceding suffix
      ⟨.inl ⟨index, .inr bytes⟩, roles, some (.Some decrypted, finalRoles), before, after⟩ position
    obtain ⟨entry, member, fields⟩ := matching_plaintext prior parent target nonce next read bytes
      (RawCtxGenericServer.selectedOwner kid ad peer (roles.1 index).rawAttempts) decrypted before after matching.1 correct.2.1
    exact Or.inr (Or.inr ⟨entry, member, matching.2 entry member, fields⟩)

end BeaconcryptCore.Computational.RawCtxSelectedProtocolOriginCases

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedProtocolOriginCases.beacon_cases' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedProtocolOriginCases.beacon_cases
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedProtocolOriginCases.server_cases' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedProtocolOriginCases.server_cases
