import BeaconcryptCore.Computational.RawCtxSelectedProductionAudit

/-!
Actual accepted raw records are split by their reached source material and ordinary full CTX tuple, without assuming SelectedFresh. Known material remains explicit, including possible byte aliases. The selected branch is an ordinary fresh accepted attempt or a match against the actual attempt-time successful-seal history; matching alone is not session-origin agreement.
-/
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.refined ratchet.concrete
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RawCtxSelectedAcceptanceOrigins
open PqxdhSecretInputKdf PqxdhFullSecretInputKdf PqxdhJointKdfGame
open RawCtxSelectedParentTable RawCtxSelectedParentEntry RawCtxSelectedMessageKey
open RawCtxSelectedAuthenticationObserver RawCtxSelectedAcceptedRecord RawCtxSelectedReceiveReceipt
open CtxRomAuth
variable {M P I D K : Type}

noncomputable def KnownRoute (prior : Prior) (parent : Option Entry) (target : RootOutput)
    (nonce : NonceOutput) (next : RootOutput) (read : RawCtxReceive.FrameDecoder) (bytes : Pqxdh.Bytes)
    (owner : RawCtxChainOwner.State Kernel P) : Prop :=
  ∃ (frame : RawCtxReceive.DecodedFrame) (pending : Pending) (material : RatchetMaterial),
    read bytes = some frame ∧
    terminal prior parent target nonce next
      (RawCtxInterpretedReceive.normalBegin owner.kernel frame.sequence ⟨bytes, frame, owner.associatedData⟩) = .opening pending ∧
    RawCtxInterpretedArguments.openArguments pending =
      some ⟨.known material, frame.sequence, ⟨bytes, frame, owner.associatedData⟩⟩

noncomputable def Matching (prior : Prior) (parent : Option Entry) (target : RootOutput)
    (nonce : NonceOutput) (next : RootOutput) (read : RawCtxReceive.FrameDecoder) (bytes : Pqxdh.Bytes)
    (owner : RawCtxChainOwner.State Kernel P) (decrypted : RawCtxWholeOwner.Decrypted) (before after : State) : Prop :=
  ∃ (frame : RawCtxReceive.DecodedFrame) (pending : Pending) (actualNonce : NonceOutput)
    (width : owner.associatedData.length = 281) (slices : RawCtxFrameDecoding.Slices)
    (parsed : RawCtxFrameDecoding.fromPayload frame.payload = some slices) (plaintext : Pqxdh.Bytes),
    bytes.isEmpty = false ∧ read bytes = some frame ∧ RawCtxReceive.ValidFrame owner.expectedSender owner.associatedData frame ∧
    terminal prior parent target nonce next
      (RawCtxInterpretedReceive.normalBegin owner.kernel frame.sequence ⟨bytes, frame, owner.associatedData⟩) = .opening pending ∧
    RawCtxInterpretedArguments.openArguments pending =
      some ⟨.hidden actualNonce, frame.sequence, ⟨bytes, frame, owner.associatedData⟩⟩ ∧
    decrypted = ⟨plaintext, frame.sender, frame.sequence⟩ ∧
    after = step (.inl (.inr (RawCtxUniversalDecoder.pack
      (RawCtxUniversalDecoder.envelope actualNonce ⟨bytes, frame, owner.associatedData⟩ width)))) (some plaintext) before ∧
    ∃ entry ∈ before.seals, (RawCtxKeyFreeDecoder.target actualNonce frame.sequence frame owner.associatedData
      slices parsed width).toLegacy.sameFullTupleAsSuccessfulSeal entry

/-- Every actual accepted raw owner execution either used a reached known material, wins the ordinary fresh-tuple observer, or has the exact selected receipt and a matching prior CTX production. No freshness or honest-target premise is assumed. -/
theorem raw_cases (prior : Prior) (parent : Option Entry) (target : RootOutput)
    (nonce : NonceOutput) (next : RootOutput) (read : RawCtxReceive.FrameDecoder) (bytes : Pqxdh.Bytes)
    (owner finalOwner : RawCtxChainOwner.State Kernel P) (before after : State)
    (decrypted : RawCtxWholeOwner.Decrypted)
    (supported : ((.Some decrypted, finalOwner), after) ∈ support (monitor
      (RawCtxSelectedReceiveCompiler.raw prior parent target nonce next read bytes owner) before)) :
    KnownRoute prior parent target nonce next read bytes owner ∨
      won (RawCtxUniversalDecoder.decoder read) after = true ∨
        Matching prior parent target nonce next read bytes owner decrypted before after := by
  classical
  obtain ⟨frame, kernel, nonempty, decoded, valid, received, published⟩ :=
    raw_accepts prior parent target nonce next read bytes owner finalOwner before after decrypted supported
  obtain ⟨pending, material, plaintext, reached, getter, value, finished, branch⟩ :=
    receive_branch prior parent target nonce next read frame.sender owner.kernel frame.sequence
      ⟨bytes, frame, owner.associatedData⟩ before after kernel decrypted received
  rcases branch with ⟨known, materialSame⟩ | ⟨actualNonce, width, materialSame, observed⟩
  · left
    exact ⟨frame, pending, known, decoded, reached, by simpa only [materialSame] using getter⟩
  · right
    obtain ⟨slices, parsed⟩ := (RawCtxFrameDecoding.fromPayload_some_iff frame.payload).mpr valid.2.1
    by_cases matched : ∃ entry ∈ before.seals, (RawCtxKeyFreeDecoder.target actualNonce frame.sequence frame
      owner.associatedData slices parsed width).toLegacy.sameFullTupleAsSuccessfulSeal entry
    · exact Or.inr ⟨frame, pending, actualNonce, width, slices, parsed, plaintext, nonempty, decoded, valid,
        reached, by simpa only [materialSame] using getter, value, observed, matched⟩
    · left
      rw [observed]
      apply (won_iff _ _).mpr
      refine ⟨⟨RawCtxUniversalDecoder.pack (RawCtxUniversalDecoder.envelope actualNonce
        ⟨bytes, frame, owner.associatedData⟩ width), some plaintext, before.seals⟩,
        List.mem_cons_self, RawCtxKeyFreeDecoder.target actualNonce frame.sequence frame owner.associatedData slices parsed width,
        ?_, Option.some_ne_none _, ?_⟩
      · exact RawCtxUniversalDecoder.decoder_pack read
          (RawCtxUniversalDecoder.envelope actualNonce ⟨bytes, frame, owner.associatedData⟩ width)
          frame slices nonempty decoded parsed
      · intro entry member same
        exact matched ⟨entry, member, same⟩

/-- Actual indexed Beacon acceptance supplies its original established owner and complete role publication before the known/fresh/matching split. No selected-slot or tuple-freshness event is assumed. -/
theorem family_beacon_cases {S B : Nat} (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (parent : Option Entry) (target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (read : RawCtxReceive.FrameDecoder)
    (index : Fin B) (bytes : Pqxdh.Bytes)
    (roles finalRoles : RawCtxGenericRoleFamily.Roles Kernel M P I D K S B) (before after : State)
    (decrypted : RawCtxWholeOwner.Decrypted)
    (supported : (some (.Some decrypted, finalRoles), after) ∈ support (monitor
      (RawCtxSelectedFamilyCompiler.family source writer prior parent target nonce next sender route read
        (.inr (.inl ⟨index, .inr bytes⟩)) roles) before)) :
    ∃ control ad kernel finalOwner,
      (roles.2 index).beacon.phase = .established control ad kernel ∧
      finalRoles = (roles.1, Function.update roles.2 index
        (RawCtxGenericBeacon.reinstall (roles.2 index) control ad finalOwner)) ∧
      (KnownRoute prior parent target nonce next read bytes (RawCtxGenericBeacon.selected (roles.2 index) control ad kernel) ∨
        won (RawCtxUniversalDecoder.decoder read) after = true ∨
        Matching prior parent target nonce next read bytes (RawCtxGenericBeacon.selected (roles.2 index) control ad kernel)
          decrypted before after) := by
  obtain ⟨finalBeacon, accepted, familyPublished⟩ := RawCtxSelectedRoleReceipt.family_beacon_accepts
    source writer prior parent target nonce next sender route read index bytes roles finalRoles before after decrypted supported
  obtain ⟨control, ad, kernel, finalOwner, established, raw, published⟩ := RawCtxSelectedRoleReceipt.beacon_accepts
    source writer prior parent target nonce next read bytes (roles.2 index) finalBeacon before after decrypted accepted
  exact ⟨control, ad, kernel, finalOwner, established, by simpa only [published] using familyPublished,
    raw_cases prior parent target nonce next read bytes (RawCtxGenericBeacon.selected (roles.2 index) control ad kernel)
      finalOwner before after decrypted raw⟩

/-- Actual indexed Server acceptance supplies its original raw route, both peer/AD lookups and exact peer publication before the exhaustive source-origin split. Claimed IDs are not equated with assigned IDs. -/
theorem family_server_cases {S B : Nat} (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (parent : Option Entry) (target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (read : RawCtxReceive.FrameDecoder)
    (index : Fin S) (bytes : Pqxdh.Bytes)
    (roles finalRoles : RawCtxGenericRoleFamily.Roles Kernel M P I D K S B) (before after : State)
    (decrypted : RawCtxWholeOwner.Decrypted)
    (supported : (some (.Some decrypted, finalRoles), after) ∈ support (monitor
      (RawCtxSelectedFamilyCompiler.family source writer prior parent target nonce next sender route read
        (.inl ⟨index, .inr bytes⟩) roles) before)) :
    ∃ kid ad peer, ∃ finalOwner : RawCtxChainOwner.State Kernel P,
      route bytes = some kid ∧ RawCtxGenericServer.peerAssociatedData (roles.1 index).server kid = some ad ∧
      (roles.1 index).server.peers kid = some peer ∧
      finalRoles = (Function.update roles.1 index
        ⟨RawCtxGenericServer.putPeer (roles.1 index).server kid peer finalOwner.kernel, finalOwner.rawAttempts⟩, roles.2) ∧
      (KnownRoute prior parent target nonce next read bytes
          (RawCtxGenericServer.selectedOwner kid ad peer (roles.1 index).rawAttempts) ∨
        won (RawCtxUniversalDecoder.decoder read) after = true ∨
        Matching prior parent target nonce next read bytes
          (RawCtxGenericServer.selectedOwner kid ad peer (roles.1 index).rawAttempts) decrypted before after) := by
  obtain ⟨finalServer, accepted, familyPublished⟩ := RawCtxSelectedRoleReceipt.family_server_accepts
    source writer prior parent target nonce next sender route read index bytes roles finalRoles before after decrypted supported
  obtain ⟨kid, ad, peer, finalOwner, routed, adFound, peerFound, raw, published⟩ := RawCtxSelectedRoleReceipt.server_accepts
    source writer prior parent target nonce next sender route read bytes (roles.1 index) finalServer before after decrypted accepted
  exact ⟨kid, ad, peer, finalOwner, routed, adFound, peerFound, by simpa only [published] using familyPublished,
    raw_cases prior parent target nonce next read bytes (RawCtxGenericServer.selectedOwner kid ad peer (roles.1 index).rawAttempts)
      finalOwner before after decrypted raw⟩

open RawCtxSelectedProductionAudit (Record Audit Edges Recorded)

/-- An ordinary accepted-attempt winner persists along the actual later source-query trace, keeping the freshness history at the original attempt rather than recomputing it after later seals. -/
theorem trace_won {S B : Nat} (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (parent : Option Entry) (target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (read : RawCtxReceive.FrameDecoder)
    {before after : State} {records : List (Record M P I D K S B)}
    (edges : Edges before records after)
    (actual : ∀ record ∈ records, Recorded source writer prior parent target nonce next sender route read record)
    (winning : won (RawCtxUniversalDecoder.decoder read) before = true) :
    won (RawCtxUniversalDecoder.decoder read) after = true := by
  induction edges with
  | nil state => exact winning
  | cons record rest ih =>
    have middle := monitor_won (RawCtxUniversalDecoder.decoder read)
      (RawCtxSelectedFamilyCompiler.family source writer prior parent target nonce next sender route read record.query record.roles)
      record.before winning (record.reply, record.after) (actual record List.mem_cons_self)
    exact ih (fun later member => actual later (List.mem_cons_of_mem record member)) middle

/-- The actual adaptive execution supplies the current source call, propagates its ordinary winner to the final observer, and gives strictly earlier source origins for every receipt available before it. -/
theorem current_record {Result : Type} {S B : Nat} (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (parent : Option Entry) (target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (read : RawCtxReceive.FrameDecoder)
    (original : OracleComp (RawCtxProtocolReveals.SourceSpec S B) Result) (state : Audit M P I D K S B)
    (result : Option Result × Audit M P I D K S B)
    (supported : result ∈ support (RawCtxSelectedProductionAudit.client source writer prior parent target nonce next sender route read original state))
    (preceding suffix : List (Record M P I D K S B)) (current : Record M P I D K S B)
    (position : result.2.records = state.records ++ (preceding ++ current :: suffix)) :
    Recorded source writer prior parent target nonce next sender route read current ∧
      (won (RawCtxUniversalDecoder.decoder read) current.after = true →
        won (RawCtxUniversalDecoder.decoder read) result.2.observer = true) ∧
      ∀ entry ∈ current.before.seals, entry ∈ state.observer.seals ∨ ∃ earlier ∈ preceding,
        Recorded source writer prior parent target nonce next sender route read earlier ∧
        RawCtxSelectedProductionOrigins.FamilyProduced writer prior parent target nonce next sender
          earlier.query earlier.roles earlier.reply entry := by
  obtain ⟨generated, appended, edges, actual⟩ :=
    RawCtxSelectedProductionAudit.client_trace source writer prior parent target nonce next sender route read original state result supported
  have same : generated = preceding ++ current :: suffix := List.append_cancel_left (appended.symm.trans position)
  rw [same] at edges actual
  refine ⟨actual current (List.mem_append_right _ List.mem_cons_self), ?_, ?_⟩
  · intro winning
    exact trace_won source writer prior parent target nonce next sender route read
      (RawCtxSelectedProductionAudit.edges_cut preceding suffix current edges).2
      (fun later member => actual later (List.mem_append_right _ (List.mem_cons_of_mem current member))) winning
  · intro entry found
    exact RawCtxSelectedProductionAudit.client_before_production source writer prior parent target nonce next sender route read
      original state result supported preceding suffix current position entry found

noncomputable def PriorProduction {S B : Nat} (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (parent : Option Entry) (target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (read : RawCtxReceive.FrameDecoder)
    (initial : State) (preceding : List (Record M P I D K S B)) (entry : CtxSuccessfulSeal) : Prop :=
  entry ∈ initial.seals ∨ ∃ earlier ∈ preceding,
    Recorded source writer prior parent target nonce next sender route read earlier ∧
    RawCtxSelectedProductionOrigins.FamilyProduced writer prior parent target nonce next sender
      earlier.query earlier.roles earlier.reply entry

/-- An accepted Beacon query at an actual adaptive audit position either uses known material, yields the final ordinary forgery winner, or matches an actual strictly earlier source production (or the retained entry prefix). The original phase and full role publication remain in the conclusion. -/
theorem audited_beacon_cases {Result : Type} {S B : Nat} (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (parent : Option Entry) (target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (read : RawCtxReceive.FrameDecoder)
    (original : OracleComp (RawCtxProtocolReveals.SourceSpec S B) Result) (state : Audit M P I D K S B)
    (result : Option Result × Audit M P I D K S B)
    (supported : result ∈ support (RawCtxSelectedProductionAudit.client source writer prior parent target nonce next sender route read original state))
    (preceding suffix : List (Record M P I D K S B)) (index : Fin B) (bytes : Pqxdh.Bytes)
    (roles finalRoles : RawCtxGenericRoleFamily.Roles Kernel M P I D K S B) (before after : State)
    (decrypted : RawCtxWholeOwner.Decrypted)
    (position : result.2.records = state.records ++ (preceding ++
      ⟨.inr (.inl ⟨index, .inr bytes⟩), roles, some (.Some decrypted, finalRoles), before, after⟩ :: suffix)) :
    ∃ control ad kernel finalOwner,
      (roles.2 index).beacon.phase = .established control ad kernel ∧
      finalRoles = (roles.1, Function.update roles.2 index
        (RawCtxGenericBeacon.reinstall (roles.2 index) control ad finalOwner)) ∧
      (KnownRoute prior parent target nonce next read bytes (RawCtxGenericBeacon.selected (roles.2 index) control ad kernel) ∨
        won (RawCtxUniversalDecoder.decoder read) result.2.observer = true ∨
        Matching prior parent target nonce next read bytes (RawCtxGenericBeacon.selected (roles.2 index) control ad kernel)
          decrypted before after ∧
          ∀ entry ∈ before.seals, PriorProduction source writer prior parent target nonce next sender route read state.observer preceding entry) := by
  have contextual := current_record source writer prior parent target nonce next sender route read original state result supported
    preceding suffix ⟨.inr (.inl ⟨index, .inr bytes⟩), roles, some (.Some decrypted, finalRoles), before, after⟩ position
  obtain ⟨control, ad, kernel, finalOwner, established, published, branch⟩ :=
    family_beacon_cases source writer prior parent target nonce next sender route read index bytes roles finalRoles before after decrypted contextual.1
  refine ⟨control, ad, kernel, finalOwner, established, published, ?_⟩
  rcases branch with known | winning | matching
  · exact Or.inl known
  · exact Or.inr (Or.inl (contextual.2.1 winning))
  · exact Or.inr (Or.inr ⟨matching, contextual.2.2⟩)

/-- The same exhaustive adaptive classification holds for an actual accepted Server query, retaining routing, original AD/peer lookup and indexed publication. Matching is attributed only to preceding source sends; assignment equality is not inferred. -/
theorem audited_server_cases {Result : Type} {S B : Nat} (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (parent : Option Entry) (target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (read : RawCtxReceive.FrameDecoder)
    (original : OracleComp (RawCtxProtocolReveals.SourceSpec S B) Result) (state : Audit M P I D K S B)
    (result : Option Result × Audit M P I D K S B)
    (supported : result ∈ support (RawCtxSelectedProductionAudit.client source writer prior parent target nonce next sender route read original state))
    (preceding suffix : List (Record M P I D K S B)) (index : Fin S) (bytes : Pqxdh.Bytes)
    (roles finalRoles : RawCtxGenericRoleFamily.Roles Kernel M P I D K S B) (before after : State)
    (decrypted : RawCtxWholeOwner.Decrypted)
    (position : result.2.records = state.records ++ (preceding ++
      ⟨.inl ⟨index, .inr bytes⟩, roles, some (.Some decrypted, finalRoles), before, after⟩ :: suffix)) :
    ∃ kid ad peer, ∃ finalOwner : RawCtxChainOwner.State Kernel P,
      route bytes = some kid ∧ RawCtxGenericServer.peerAssociatedData (roles.1 index).server kid = some ad ∧
      (roles.1 index).server.peers kid = some peer ∧
      finalRoles = (Function.update roles.1 index
        ⟨RawCtxGenericServer.putPeer (roles.1 index).server kid peer finalOwner.kernel, finalOwner.rawAttempts⟩, roles.2) ∧
      (KnownRoute prior parent target nonce next read bytes (RawCtxGenericServer.selectedOwner kid ad peer (roles.1 index).rawAttempts) ∨
        won (RawCtxUniversalDecoder.decoder read) result.2.observer = true ∨
        Matching prior parent target nonce next read bytes (RawCtxGenericServer.selectedOwner kid ad peer (roles.1 index).rawAttempts)
          decrypted before after ∧
          ∀ entry ∈ before.seals, PriorProduction source writer prior parent target nonce next sender route read state.observer preceding entry) := by
  have contextual := current_record source writer prior parent target nonce next sender route read original state result supported
    preceding suffix ⟨.inl ⟨index, .inr bytes⟩, roles, some (.Some decrypted, finalRoles), before, after⟩ position
  obtain ⟨kid, ad, peer, finalOwner, routed, adFound, peerFound, published, branch⟩ :=
    family_server_cases source writer prior parent target nonce next sender route read index bytes roles finalRoles before after decrypted contextual.1
  refine ⟨kid, ad, peer, finalOwner, routed, adFound, peerFound, published, ?_⟩
  rcases branch with known | winning | matching
  · exact Or.inl known
  · exact Or.inr (Or.inl (contextual.2.1 winning))
  · exact Or.inr (Or.inr ⟨matching, contextual.2.2⟩)

end BeaconcryptCore.Computational.RawCtxSelectedAcceptanceOrigins

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedAcceptanceOrigins.raw_cases' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedAcceptanceOrigins.raw_cases

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedAcceptanceOrigins.family_beacon_cases' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedAcceptanceOrigins.family_beacon_cases

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedAcceptanceOrigins.family_server_cases' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedAcceptanceOrigins.family_server_cases

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedAcceptanceOrigins.trace_won' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedAcceptanceOrigins.trace_won

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedAcceptanceOrigins.current_record' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedAcceptanceOrigins.current_record

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedAcceptanceOrigins.audited_beacon_cases' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedAcceptanceOrigins.audited_beacon_cases

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedAcceptanceOrigins.audited_server_cases' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedAcceptanceOrigins.audited_server_cases
