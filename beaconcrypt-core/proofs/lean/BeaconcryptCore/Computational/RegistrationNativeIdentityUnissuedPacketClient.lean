-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorPacketClient
import BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxNoReveal
/-! The unissued-field reduction stops before a fixed public parsed-accept ordinal. Every earlier query runs through the literal source dictionary, including failed signatures, failed writers and real shared-hash calls. -/
open OracleComp OracleSpec
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityUnissuedPacketClient
open RegistrationNativeRawAdapter (TypedSpec)
variable {S Value : Type}
abbrev Source := RegistrationNativePlatformIdentityCtxCompiler.Spec
abbrev Packet := beaconcrypt_core.registration.InitPacket

def visit (accept : Nat) (frontend : QueryImpl TypedSpec (StateT S (OracleComp Source)))
    (work : OracleComp TypedSpec Value) : S → Nat → OracleComp Source (Option Packet) :=
  work.recOn (fun _ _before _cursor => pure none)
    (fun query _next continued before cursor => match query with
      | .inr (.accept packet) =>
          if cursor = accept then pure (some packet)
          else do
            let reached ← (frontend (.inr (.accept packet))).run before
            continued reached.1 reached.2 (cursor + 1)
      | query => do
          let reached ← (frontend query).run before
          continued reached.1 reached.2 cursor)

private theorem accept_step (accept cursor : Nat) (frontend : QueryImpl TypedSpec (StateT S (OracleComp Source)))
    (packet : Packet) (next : TypedSpec.Range (.inr (.accept packet)) → OracleComp TypedSpec Value) (before : S) :
    visit accept frontend (TypedSpec.query (.inr (.accept packet)) >>= next) before cursor =
      (if cursor = accept then pure (some packet) else do
        let reached ← (frontend (.inr (.accept packet))).run before
        visit accept frontend (next reached.1) reached.2 (cursor + 1)) := rfl

private theorem visit_step (accept cursor : Nat) (frontend : QueryImpl TypedSpec (StateT S (OracleComp Source)))
    (query : TypedSpec.Domain) (next : TypedSpec.Range query → OracleComp TypedSpec Value) (before : S) :
    visit accept frontend (TypedSpec.query query >>= next) before cursor =
      (match query with
      | .inr (.accept packet) =>
          if cursor = accept then pure (some packet) else do
            let reached ← (frontend (.inr (.accept packet))).run before
            visit accept frontend (next reached.1) reached.2 (cursor + 1)
      | query => do
          let reached ← (frontend query).run before
          visit accept frontend (next reached.1) reached.2 cursor) := by
  cases query with
  | inl coin => rfl
  | inr command => cases command <;> rfl

/-- Stopping preserves every syntactic source restriction satisfied by each actual callback. -/
theorem scope (accept cursor : Nat) (frontend : QueryImpl TypedSpec (StateT S (OracleComp Source)))
    (permitted : Source.Domain → Prop)
    (safe : ∀ query before, ((frontend query).run before).AllQueriesSatisfy permitted)
    (work : OracleComp TypedSpec Value) (before : S) :
    (visit accept frontend work before cursor).AllQueriesSatisfy permitted := by
  induction work using OracleComp.inductionOn generalizing before cursor with
  | pure value => exact allQueriesSatisfy_pure _ _
  | query_bind query next ih =>
      rw [visit_step]
      rcases query with coin | command
      · exact allQueriesSatisfy_bind (safe _ _) (fun reached => ih reached.1 cursor reached.2)
      · cases command
        case accept packet =>
          by_cases chosen : cursor = accept
          · simpa only [chosen,ite_true] using (allQueriesSatisfy_pure (some packet) permitted : (pure (some packet) : OracleComp Source _).AllQueriesSatisfy permitted)
          · simpa only [chosen,ite_false] using allQueriesSatisfy_bind (safe (.inr (.accept packet)) before) (fun reached => ih reached.1 (cursor+1) reached.2)
        all_goals exact allQueriesSatisfy_bind (safe _ _) (fun reached => ih reached.1 cursor reached.2)

/-- The chosen submitted packet is captured before the callback, with no primitive or hash work at that position. -/
theorem at_accept (accept : Nat) (frontend : QueryImpl TypedSpec (StateT S (OracleComp Source)))
    (packet : Packet) (next : TypedSpec.Range (.inr (.accept packet)) → OracleComp TypedSpec Value) (before : S) :
    visit accept frontend (TypedSpec.query (.inr (.accept packet)) >>= next) before accept = pure (some packet) := by
  rw [accept_step, ite_eq_left rfl]

/-- A completed client with fewer parsed accepts submits no forgery candidate. -/
theorem returned (accept cursor : Nat) (frontend : QueryImpl TypedSpec (StateT S (OracleComp Source)))
    (value : Value) (before : S) : visit accept frontend (pure value) before cursor = pure none := rfl

def field (tag : Fin 3) (packet : Option Packet) : Option PqxdhJointIdentity.Forgery :=
  packet.bind fun current => (PqxdhJointPhase1Reports.candidateFields (RegistrationRootInput.candidate current))[tag.val]?

/-- The three public positions cover every literal attached field, including when some malformed fields are absent. -/
theorem field_exists (packet : Packet) (forgery : PqxdhJointIdentity.Forgery)
    (member : forgery ∈ PqxdhJointPhase1Reports.candidateFields (RegistrationRootInput.candidate packet)) :
    ∃ tag : Fin 3, field tag (some packet) = some forgery := by
  obtain ⟨index,found⟩ := List.mem_iff_getElem?.mp member
  have within := (List.getElem?_eq_some_iff.mp found).1
  have length : (PqxdhJointPhase1Reports.candidateFields (RegistrationRootInput.candidate packet)).length ≤ 3 := by
    exact List.length_filterMap_le _ _
  exact ⟨⟨index,lt_of_lt_of_le within length⟩,found⟩

/-- The submitted field itself wins ordinary message weak-EUF whenever its same-prefix history shows it was unissued; no canonical signature is substituted. -/
theorem field_wins (joint : PqxdhJointIdentity.Primitives) (identity : PqxdhJointIdentity.PublicIdentity)
    (tag : Fin 3) (packet : Option Packet) (forgery fallback : PqxdhJointIdentity.Forgery)
    (history : PqxdhJointIdentity.History) (selected : field tag packet = some forgery)
    (valid : joint.verify identity.ed25519 forgery.message forgery.signature = true)
    (fresh : forgery.message ∉ PqxdhJointIdentity.signedMessages history) :
    PqxdhJointIdentity.wins joint identity ((field tag packet).getD fallback) history = true := by
  simp [PqxdhJointIdentity.wins,selected,valid,fresh]

section Native
variable [primitive : BeaconcryptCore.Refinement.AdapterSealPrimitive.Operations]
variable {n : Nat} {I KemSK Platform E : Type} {base : OracleSpec I} {source : RegistrationNativeMldsa.Source}
variable (setup : PqxdhServerAuthExperiment.Setup base KemSK) (checks : PqxdhServerAuthExperiment.Checks) (wire : RegistrationNativeWire.Wire)
variable (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
variable (created : PqxdhLiveServerConstruction.Created Unit) (credential : RegistrationNativeMldsa.Credential source)
variable (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
variable (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
variable (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
variable (reserveFrame : Nat → StateT Platform ProbComp (CoreModels.core.result.Result Unit E)) (erased : beaconcrypt_core.commitment.CommitmentTranscript)
variable (helper : QueryImpl (BeaconcryptCore.Refinement.AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
variable (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
local notation "actual" => RegistrationNativePlatformIdentityCtxTyped.handler (n := n) setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer

/-- The literal source dictionary discharges no-reveal safety for this public stopping client internally. -/
theorem native_scope (accept cursor : Nat) (work : OracleComp TypedSpec Value)
    (before : RegistrationNativeIdentityMain.State n KemSK source × Platform) :
    (visit accept actual work before cursor).AllQueriesSatisfy RegistrationNativePlatformIdentityCtxNoReveal.Allowed :=
  scope accept cursor actual _
    (RegistrationNativePlatformIdentityCtxNoReveal.handler_safe setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer) work before

end Native

end BeaconcryptCore.Computational.RegistrationNativeIdentityUnissuedPacketClient

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityUnissuedPacketClient.scope' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityUnissuedPacketClient.scope

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityUnissuedPacketClient.at_accept' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityUnissuedPacketClient.at_accept

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityUnissuedPacketClient.returned' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityUnissuedPacketClient.returned

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityUnissuedPacketClient.field_exists' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityUnissuedPacketClient.field_exists

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityUnissuedPacketClient.field_wins' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityUnissuedPacketClient.field_wins

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityUnissuedPacketClient.native_scope' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityUnissuedPacketClient.native_scope
