import BeaconcryptCore.Computational.RawCtxSelectedDriverAudit
import BeaconcryptCore.Computational.RawCtxGenericFamilyInterpretation
import BeaconcryptCore.Computational.RawCtxSelectedMessageFamily

/-!
The original indexed role frontend supplies private owner labels to the audited drivers. All receive/send derivations and seal occurrences share one audit interface, while public services remain ordinary source requests. The selected message key is absent from the executable compiler. Source erasure retains every role and optional reply; registration installation identity and the probability of a repeated selected send remain separate obligations.
-/
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RawCtxSelectedFamilyAudit
open PqxdhSecretInputKdf PqxdhFullSecretInputKdf RawCtxSelectedMessageDriver
open RawCtxSelectedParentEntry RawCtxSelectedDriverAudit
open RawCtxProtocolReveals (Owner)
variable {M P I D K Result : Type} {S B : Nat}

abbrev Services := ReceiveServices RawCtxWholeOwner.OpenContext RawCtxWholeOwner.Decrypted +
  (SendServices RawCtxSourceSend.SealContext RawCtxSourceSend.Encrypted + RawCtxServerServices.PublicSpec)
abbrev Spec (S B : Nat) := Services + Audit (Owner S B)

def receiveLift : QueryImpl (RawCtxSelectedDriverAudit.ReceiveSpec (Owner S B)) (OracleComp (Spec S B))
  | .inl query => (Spec S B).query (.inl (.inl query))
  | .inr event => (Spec S B).query (.inr event)

def sendLift : QueryImpl (RawCtxSelectedDriverAudit.SendSpec (Owner S B)) (OracleComp (Spec S B))
  | .inl query => (Spec S B).query (.inl (.inr (.inl query)))
  | .inr event => (Spec S B).query (.inr event)

def originalReceive : QueryImpl (ReceiveServices RawCtxWholeOwner.OpenContext RawCtxWholeOwner.Decrypted) (OracleComp Services) :=
  fun query => Services.query (.inl query)

def originalSend : QueryImpl (SendServices RawCtxSourceSend.SealContext RawCtxSourceSend.Encrypted) (OracleComp Services) :=
  fun query => Services.query (.inr (.inl query))

/-- Combining the receive and send service families does not change the exact erased receive callback. -/
theorem receive_lift (query : (RawCtxSelectedDriverAudit.ReceiveSpec (Owner S B)).Domain) :
    simulateQ RawCtxSelectedDriverAudit.erase (receiveLift query) =
      simulateQ originalReceive (RawCtxSelectedDriverAudit.erase query) := by
  cases query <;> simp [receiveLift, originalReceive, RawCtxSelectedDriverAudit.erase]

/-- Combining the service families preserves both layers of sealing interpretation; the audit itself is private. -/
theorem send_lift (query : (RawCtxSelectedDriverAudit.SendSpec (Owner S B)).Domain) :
    simulateQ RawCtxSelectedDriverAudit.erase (sendLift query) =
      simulateQ originalSend (RawCtxSelectedDriverAudit.erase query) := by
  cases query <;> simp [sendLift, originalSend, RawCtxSelectedDriverAudit.erase]

noncomputable def ownedCalls (parent : Option Entry) (target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (owner : Owner S B) : RawCtxChainOwner.Calls RawCtxSelectedMessageReveals.Kernel (OracleComp (Spec S B)) where
  receive entry sequence context := simulateQ receiveLift
    (RawCtxSelectedDriverAudit.receive owner entry parent target nonce next sequence context)
  send entry context := simulateQ sendLift (RawCtxSelectedDriverAudit.send owner entry parent target nonce next context)

noncomputable def calls (parent : Option Entry) (target : RootOutput) (nonce : NonceOutput) (next : RootOutput) :=
  RawCtxOwnerLabels.calls (ownedCalls (S := S) (B := B) parent target nonce next)

noncomputable def originalCalls (parent : Option Entry) (target : RootOutput) (nonce : NonceOutput) (next : RootOutput) :=
  RawCtxSelectedMessageFamily.calls originalReceive originalSend parent target nonce next

/-- The actual labelled receive call erases to the unchanged source driver, including its original optional plaintext and complete returned kernel. -/
theorem receive_map (parent : Option Entry) (target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (entry : RawCtxOwnerLabels.Labelled RawCtxSelectedMessageReveals.Kernel S B)
    (sequence : Std.U64) (context : RawCtxWholeOwner.OpenContext) :
    (originalCalls parent target nonce next).receive entry.2 sequence context =
      Prod.map Prod.snd id <$> simulateQ RawCtxSelectedDriverAudit.erase
        ((calls parent target nonce next).receive entry sequence context) := by
  simp only [calls, RawCtxOwnerLabels.calls, ownedCalls, simulateQ_map, ← QueryImpl.simulateQ_compose]
  have same : RawCtxSelectedDriverAudit.erase ∘ₛ (receiveLift (S := S) (B := B)) =
      originalReceive ∘ₛ RawCtxSelectedDriverAudit.erase := by
    funext query
    exact receive_lift query
  rw [same, QueryImpl.simulateQ_compose, RawCtxSelectedDriverAudit.receive_erased]
  simp [originalCalls, RawCtxSelectedMessageFamily.calls, Functor.map_map, Prod.map_def]

/-- The actual labelled send forwards its route and entry into the audit and erases to the complete original send driver. -/
theorem send_map (parent : Option Entry) (target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (entry : RawCtxOwnerLabels.Labelled RawCtxSelectedMessageReveals.Kernel S B)
    (context : RawCtxSourceSend.SealContext) :
    (originalCalls parent target nonce next).send entry.2 context =
      Prod.map Prod.snd id <$> simulateQ RawCtxSelectedDriverAudit.erase
        ((calls parent target nonce next).send entry context) := by
  simp only [calls, RawCtxOwnerLabels.calls, ownedCalls, simulateQ_map, ← QueryImpl.simulateQ_compose]
  have same : RawCtxSelectedDriverAudit.erase ∘ₛ (sendLift (S := S) (B := B)) =
      originalSend ∘ₛ RawCtxSelectedDriverAudit.erase := by
    funext query
    exact send_lift query
  rw [same, QueryImpl.simulateQ_compose, RawCtxSelectedDriverAudit.send_erased]
  simp [originalCalls, RawCtxSelectedMessageFamily.calls, Functor.map_map, Prod.map_def]

def publicService : QueryImpl RawCtxServerServices.PublicSpec (OracleComp (Spec S B)) :=
  fun query => (Spec S B).query (.inl (.inr (.inr query)))

def originalPublic : QueryImpl RawCtxServerServices.PublicSpec (OracleComp Services) :=
  fun query => Services.query (.inr (.inr query))

noncomputable def frontend (parent : Option Entry) (target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder) :=
  RawCtxGenericFamilyFrontend.impl (calls (S := S) (B := B) parent target nonce next) publicService
    sender route decode (PeerMetadata := P) (Identity := I) (DhPair := D) (KemPair := K) (serverCount := S) (beaconCount := B)

set_option backward.isDefEq.respectTransparency false in
/-- Every actual original indexed role operation supplies its stored owner label to the audited driver and erases to the unchanged complete source frontend. -/
theorem step_erased (parent : Option Entry) (target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (query : (RawCtxProtocolRoles.SourceSpec S B).Domain)
    (roles : RawCtxGenericRoleFamily.Roles
      (RawCtxOwnerLabels.Labelled RawCtxSelectedMessageReveals.Kernel S B) M P I D K S B) :
    (RawCtxSelectedMessageFamily.frontend originalReceive originalSend originalPublic
      parent target nonce next sender route decode query).run (RawCtxGenericRoleFamily.mapRoles Prod.snd roles) =
    Prod.map id (RawCtxGenericRoleFamily.mapRoles Prod.snd) <$>
      simulateQ RawCtxSelectedDriverAudit.erase
        ((frontend parent target nonce next sender route decode query).run roles) := by
  rw [frontend, RawCtxGenericFamilyInterpretation.step_interpretation]
  have same := RawCtxGenericFamilyFrontend.step_map Prod.snd
    (RawCtxGenericOwnerInterpretation.interpretedCalls RawCtxSelectedDriverAudit.erase (calls parent target nonce next))
    (originalCalls parent target nonce next) originalPublic
    (receive_map parent target nonce next) (send_map parent target nonce next) sender route decode query roles
  have pub : (fun request => simulateQ RawCtxSelectedDriverAudit.erase (publicService (S := S) (B := B) request)) = originalPublic := by
    funext request
    cases request <;> rfl
  rw [pub]
  exact same

set_option backward.isDefEq.respectTransparency false in
/-- An arbitrary adaptive source record/public schedule has exactly the original optional replies and whole role family after erasing the private owner/derivation audit. -/
theorem schedule_erased (parent : Option Entry) (target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp (RawCtxProtocolRoles.SourceSpec S B) Result)
    (roles : RawCtxGenericRoleFamily.Roles
      (RawCtxOwnerLabels.Labelled RawCtxSelectedMessageReveals.Kernel S B) M P I D K S B) :
    (simulateQ (RawCtxSelectedMessageFamily.frontend originalReceive originalSend originalPublic
      parent target nonce next sender route decode) client).run (RawCtxGenericRoleFamily.mapRoles Prod.snd roles) =
    Prod.map id (RawCtxGenericRoleFamily.mapRoles Prod.snd) <$>
      simulateQ RawCtxSelectedDriverAudit.erase
        ((simulateQ (frontend parent target nonce next sender route decode) client).run roles) := by
  rw [frontend, RawCtxGenericFamilyInterpretation.schedule_interpretation]
  have same := RawCtxGenericFamilyFrontend.schedule_map Prod.snd
    (RawCtxGenericOwnerInterpretation.interpretedCalls RawCtxSelectedDriverAudit.erase (calls parent target nonce next))
    (originalCalls parent target nonce next) originalPublic
    (receive_map parent target nonce next) (send_map parent target nonce next) sender route decode client roles
  have pub : (fun request => simulateQ RawCtxSelectedDriverAudit.erase (publicService (S := S) (B := B) request)) = originalPublic := by
    funext request
    cases request <;> rfl
  rw [pub]
  exact same

/-- The original family itself supplies all private labels before the audited schedule; no initial label-consistency premise is needed. -/
theorem attached_erased (parent : Option Entry) (target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp (RawCtxProtocolRoles.SourceSpec S B) Result)
    (roles : RawCtxGenericRoleFamily.Roles RawCtxSelectedMessageReveals.Kernel M P I D K S B) :
    (simulateQ (RawCtxSelectedMessageFamily.frontend originalReceive originalSend originalPublic
      parent target nonce next sender route decode) client).run roles =
    Prod.map id (RawCtxGenericRoleFamily.mapRoles Prod.snd) <$>
      simulateQ RawCtxSelectedDriverAudit.erase
        ((simulateQ (frontend parent target nonce next sender route decode) client).run (RawCtxOwnerLabels.attach roles)) := by
  simpa only [RawCtxOwnerLabels.forget_attach] using
    schedule_erased parent target nonce next sender route decode client (RawCtxOwnerLabels.attach roles)

noncomputable def sourceServices {A : Type} (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (writer : RawCtxMixedShared.Writer) (prior : RawCtxSelectedParentTable.Prior)
    (parent : Option Entry) (key target : RootOutput) (nonce : NonceOutput) (next : RootOutput) :
    QueryImpl Services (StateT (A × CtxRomAuth.CtxRO.QueryCache) ProbComp)
  | .inl query => receiveServices source writer prior parent key target nonce next query
  | .inr (.inl query) => sendServices source writer prior parent key target nonce next query
  | .inr (.inr query) =>
      (RawCtxFunctionalFamily.backend source writer
        (RawCtxSelectedMessageDriver.privateTable prior parent target (RawCtxSelectedMessageKdf.response key nonce next))
        ∘ₛ RawCtxServerServices.publicLift) query

set_option backward.isDefEq.respectTransparency false in
/-- The shared service family interprets the literal original receive/send/public callbacks, retaining complete local and commitment-cache state. -/
theorem service_frontend {A : Type} (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (writer : RawCtxMixedShared.Writer) (prior : RawCtxSelectedParentTable.Prior)
    (parent : Option Entry) (key target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (query : (RawCtxProtocolRoles.SourceSpec S B).Domain)
    (roles : RawCtxGenericRoleFamily.Roles RawCtxSelectedMessageReveals.Kernel M P I D K S B) :
    simulateQ (sourceServices (A := A) source writer prior parent key target nonce next)
      ((RawCtxSelectedMessageFamily.frontend originalReceive originalSend originalPublic
        parent target nonce next sender route decode query).run roles) =
    (RawCtxSelectedMessageFamily.frontend
      (receiveServices source writer prior parent key target nonce next)
      (sendServices source writer prior parent key target nonce next)
      (RawCtxFunctionalFamily.backend source writer
        (RawCtxSelectedMessageDriver.privateTable prior parent target (RawCtxSelectedMessageKdf.response key nonce next))
        ∘ₛ RawCtxServerServices.publicLift)
      parent target nonce next sender route decode query).run roles := by
  rw [RawCtxSelectedMessageFamily.frontend, RawCtxGenericFamilyInterpretation.step_interpretation]
  simp only [RawCtxSelectedMessageFamily.frontend, RawCtxGenericOwnerInterpretation.interpretedCalls,
    RawCtxSelectedMessageFamily.calls, ← QueryImpl.simulateQ_compose]
  have recv : sourceServices (A := A) source writer prior parent key target nonce next ∘ₛ originalReceive =
      receiveServices source writer prior parent key target nonce next := by
    funext request
    simp only [QueryImpl.compose, originalReceive, simulateQ_spec_query, sourceServices]
  have send : sourceServices (A := A) source writer prior parent key target nonce next ∘ₛ originalSend =
      sendServices source writer prior parent key target nonce next := by
    funext request
    simp only [QueryImpl.compose, originalSend, simulateQ_spec_query, sourceServices]
  rw [recv, send]
  congr 2
  funext request
  simp only [originalPublic, simulateQ_spec_query, sourceServices]

/-- The complete adaptive schedule consumes the actual receive/send/public source interpreter and retains every reached role state. -/
theorem service_schedule {A : Type} (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (writer : RawCtxMixedShared.Writer) (prior : RawCtxSelectedParentTable.Prior)
    (parent : Option Entry) (key target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp (RawCtxProtocolRoles.SourceSpec S B) Result)
    (roles : RawCtxGenericRoleFamily.Roles RawCtxSelectedMessageReveals.Kernel M P I D K S B) :
    simulateQ (sourceServices (A := A) source writer prior parent key target nonce next)
      ((simulateQ (RawCtxSelectedMessageFamily.frontend originalReceive originalSend originalPublic
        parent target nonce next sender route decode) client).run roles) =
    (simulateQ (RawCtxSelectedMessageFamily.frontend
      (receiveServices source writer prior parent key target nonce next)
      (sendServices source writer prior parent key target nonce next)
      (RawCtxFunctionalFamily.backend source writer
        (RawCtxSelectedMessageDriver.privateTable prior parent target (RawCtxSelectedMessageKdf.response key nonce next))
        ∘ₛ RawCtxServerServices.publicLift)
      parent target nonce next sender route decode) client).run roles := by
  induction client using OracleComp.inductionOn generalizing roles with
  | pure value => simp only [simulateQ_pure, StateT.run_pure]
  | query_bind query continuation ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
    rw [service_frontend]
    exact bind_congr fun result => ih result.1 result.2

/-- Erasing private owner annotations and audit requests preserves every actual service-class bound of the complete adaptive schedule. -/
theorem service_queries (parent : Option Entry) (target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp (RawCtxProtocolRoles.SourceSpec S B) Result)
    (roles : RawCtxGenericRoleFamily.Roles RawCtxSelectedMessageReveals.Kernel M P I D K S B)
    (select : Services.Domain → Prop) [DecidablePred select] (budget : Nat) :
    (simulateQ RawCtxSelectedDriverAudit.erase
      ((simulateQ (frontend parent target nonce next sender route decode) client).run (RawCtxOwnerLabels.attach roles))).IsQueryBoundP select budget ↔
    ((simulateQ (RawCtxSelectedMessageFamily.frontend originalReceive originalSend originalPublic
      parent target nonce next sender route decode) client).run roles).IsQueryBoundP select budget := by
  rw [attached_erased, isQueryBoundP_map_iff]

end BeaconcryptCore.Computational.RawCtxSelectedFamilyAudit

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedFamilyAudit.receive_lift' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedFamilyAudit.receive_lift
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedFamilyAudit.send_lift' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedFamilyAudit.send_lift
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedFamilyAudit.receive_map' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedFamilyAudit.receive_map
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedFamilyAudit.send_map' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedFamilyAudit.send_map
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedFamilyAudit.step_erased' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedFamilyAudit.step_erased
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedFamilyAudit.schedule_erased' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedFamilyAudit.schedule_erased
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedFamilyAudit.attached_erased' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedFamilyAudit.attached_erased
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedFamilyAudit.service_frontend' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedFamilyAudit.service_frontend
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedFamilyAudit.service_schedule' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedFamilyAudit.service_schedule
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedFamilyAudit.service_queries' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedFamilyAudit.service_queries
