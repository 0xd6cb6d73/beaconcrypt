-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformServerHistoryOrigin
import BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryInitPendingJournal
import BeaconcryptCore.Computational.RegistrationNativePlatformRoleFrame
import BeaconcryptCore.Computational.RegistrationNativePlatformServerIssuance
import BeaconcryptCore.Computational.RegistrationNativePlatformInitPendingJournal
import BeaconcryptCore.Computational.RegistrationNativeServerHistoryOrigin

/-! Every Server-role issuance in the actual initialized dynamic-writer runtime has its own earlier literal build, moved token and first-record source hash stage. Non-build callback reasoning retains the same actual native state through the public terminal reservation gate; actual platform failures and replies remain in the new chronological path. No equality of complete old and new profiles is assumed. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 32768
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryServerHistoryOrigin
open BeaconcryptCore.Refinement
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeMldsaRoleFrame (NonBuild serverReceipts)
open RegistrationNativeServerIssuance (history)
open RegistrationSigningShared (Receipt)
open RegistrationSigningTrace (Command)
open RegistrationNativePlatformMldsaProgram (coins)
open RegistrationNativeStageTrace (Call Path Executed)
variable {n : Nat} {E Platform Value ι KemSK : Type} {base : OracleSpec ι} {source : RegistrationNativeMldsa.Source}
local notation "Native" => RegistrationNativeExperiment.State n KemSK source
local notation "Whole" => Native × Platform

open RegistrationNativePlatformServerHistoryOrigin (SourceAt)

variable [primitive : AdapterSealPrimitive.Operations]
variable (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
variable (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
variable (created : PqxdhLiveServerConstruction.Created Unit) (credential : RegistrationNativeMldsa.Credential source)
variable (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
variable (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
variable (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
variable (reserveFrame : Nat → StateT Platform ProbComp (core.result.Result Unit E)) (erased : commitment.CommitmentTranscript)
variable (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
variable (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
local notation "impl" => RegistrationNativePlatformOrdinaryKemClientJournal.actual setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
attribute [local irreducible] RegistrationNativeExperiment.handler RegistrationServerNativeSource.authenticate
  RegistrationServerNativeSource.agree RegistrationWorldAuthentication.begin RegistrationAuthenticationShared.begin

omit primitive in
private theorem after_cut (reserve : Nat → StateT Platform ProbComp (core.result.Result Unit E))
    (work : RegistrationNativePlatformOrdinaryExperiment.M n KemSK source Platform (Option RawCtxSourceSend.Encrypted))
    (before : Native) (previous : Platform) (result : (Option RawCtxSourceSend.Encrypted × Native) × Platform)
    (supported : result ∈ support (((RegistrationNativePlatformOrdinaryExperimentRouting.after reserve work).run before).run previous)) :
    ∃ middle ∈ support ((work.run before).run previous), result.1.2 = middle.1.2 := by
  simp only [RegistrationNativePlatformOrdinaryExperimentRouting.after, StateT.run_bind, mem_support_bind_iff] at supported
  obtain ⟨middle, called, continued⟩ := supported
  simp only [StateT.run_lift, bind_pure_comp, StateT.run_map, support_map] at continued
  obtain ⟨gated, _reserved, same⟩ := continued
  exact ⟨middle, called, (congrArg (fun result => result.1.2) same).symm⟩

private theorem actual (query : RegistrationNativeRawAdapter.TypedSpec.Domain) (before after : Whole)
    (reply : RegistrationNativeRawAdapter.TypedSpec.Range query)
    (supported : (reply, after) ∈ support ((impl query).run before)) :
    ((reply, after.1), after.2) ∈ support
      (((RegistrationNativePlatformOrdinaryExperiment.handler setup checks wire route representation created source credential view failure allocation
        reserveRegistration reservePeer reserveFrame erased helper writer query).run before.1).run before.2) := by
  simp only [RegistrationNativePlatformOrdinaryKemClientJournal.actual, RegistrationNativePlatformPackedState.pack, StateT.run, support_map] at supported
  obtain ⟨⟨⟨value, native⟩, platform⟩, called, same⟩ := supported
  cases same
  exact called

private theorem old_cut (query : RegistrationNativeRawAdapter.TypedSpec.Domain) (before after : Whole)
    (reply : RegistrationNativeRawAdapter.TypedSpec.Range query)
    (supported : (reply, after) ∈ support ((impl query).run before)) :
    ∃ oldReply oldP, ((oldReply, after.1), oldP) ∈ support
      (((RegistrationNativePlatformExperiment.handler coins setup checks (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) route representation created source credential view failure allocation
        reserveRegistration reservePeer erased helper writer query).run before.1).run before.2) := by
  have called := actual setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer query before after reply supported
  rw [RegistrationNativePlatformOrdinaryExperimentRouting.handler_terminal] at called
  cases query with
  | inl coin => exact ⟨reply, after.2, called⟩
  | inr command => cases command with
    | serverSend key plaintext =>
      obtain ⟨middle, reached, same⟩ := after_cut reserveFrame _ before.1 before.2 ((reply, after.1), after.2) called
      change after.1 = middle.1.2 at same
      exact ⟨middle.1.1, middle.2, by rw [same]; exact reached⟩
    | beaconSend owner plaintext =>
      obtain ⟨middle, reached, same⟩ := after_cut reserveFrame _ before.1 before.2 ((reply, after.1), after.2) called
      change after.1 = middle.1.2 at same
      exact ⟨middle.1.1, middle.2, by rw [same]; exact reached⟩
    | _ => exact ⟨reply, after.2, called⟩

private theorem call_origin (call : Call RegistrationNativeRawAdapter.TypedSpec Whole)
    (called : Executed impl call) (receipt : Receipt) (member : receipt ∈ serverReceipts (history call.after.1.server)) :
    receipt ∈ serverReceipts (history call.before.1.server) ∨ SourceAt call receipt := by
  have supported := actual setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
    call.query call.before call.after call.reply called
  obtain ⟨oldReply, oldP, oldSupported⟩ := old_cut setup checks wire route representation created credential view failure allocation
    reserveRegistration reservePeer reserveFrame erased helper writer call.query call.before call.after call.reply called
  rw [RegistrationNativePlatformOrdinaryExperimentRouting.handler_terminal] at supported
  rcases call with ⟨query, before, reply, after⟩
  by_cases allowed : NonBuild query
  · have frame := RegistrationNativePlatformRoleFrame.handler setup checks (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) route representation created credential view failure allocation
      reserveRegistration reservePeer erased helper writer query allowed before.1 before.2 ((oldReply, after.1), oldP) oldSupported
    exact Or.inl (frame ▸ member)
  · cases query with
    | inl coin => exact False.elim (allowed trivial)
    | inr query => cases query with
      | build index application =>
        obtain ⟨raw, role⟩ := List.mem_filter.mp member
        by_cases prior : receipt ∈ history before.1.server
        · exact Or.inl (List.mem_filter.mpr ⟨prior, role⟩)
        · have changed : history after.1.server ≠ history before.1.server := by
            intro same
            exact prior (same ▸ raw)
          obtain ⟨token, current, pin, plaintext, taken, input, availability, initial, hashed, digest, signature, admitted, path, appended⟩ :=
            RegistrationNativePlatformServerIssuance.typed coins setup checks (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) route representation created credential view failure allocation erased
              reserveRegistration reservePeer helper writer index application before.1 after.1 before.2 after.2 reply supported changed
          have added : receipt ∈ history before.1.server ++ [⟨⟨hashed.binding.server_pin.public_key, Command.payload (.server hashed), RegistrationSigningTrace.replyBytes signature⟩, digest⟩] :=
            appended ▸ raw
          rcases List.mem_append.mp added with old | single
          · exact False.elim (prior old)
          · have receiptEq := List.mem_singleton.mp single
            subst receipt
            exact Or.inr ⟨index, application, token, current, pin, plaintext, availability, initial, hashed, rfl,
              taken, input, admitted, path, rfl, rfl, raw, prior⟩
      | _ => exact False.elim (allowed trivial)

/-- Every actual corrected chronological path attributes its final Server receipts to initial receipts or their own earlier source build stage. -/
theorem path_origin {first last : Whole} {calls : List (Call RegistrationNativeRawAdapter.TypedSpec Whole)}
    (reached : Path impl first calls last) (receipt : Receipt) (member : receipt ∈ serverReceipts (history last.1.server)) :
    receipt ∈ serverReceipts (history first.1.server) ∨ ∃ call ∈ calls, SourceAt call receipt := by
  induction reached with
  | nil => exact Or.inl member
  | cons call called rest last following ih =>
    rcases ih member with previous | ⟨earlier, inRest, stage⟩
    · rcases call_origin setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
        call called receipt previous with old | stage
      · exact Or.inl old
      · exact Or.inr ⟨call, List.mem_cons_self, stage⟩
    · exact Or.inr ⟨earlier, List.mem_cons_of_mem _ inRest, stage⟩

/-- Actual initialized source history supplies an earlier literal build stage for each Server issuance receipt. -/
theorem initialized_journal (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64)
    (initial : RegistrationNativeExperiment.Initial n KemSK source)
    (startup : some initial ∈ support (RegistrationNativeExperiment.start setup source ensureInit identityIndex serverKeyId))
    (previous : Platform) (work : OracleComp RegistrationNativeRawAdapter.TypedSpec Value)
    (result : Value × (Whole × List (Call RegistrationNativeRawAdapter.TypedSpec Whole)))
    (supported : result ∈ support ((simulateQ (RegistrationNativeStageTrace.handler impl) work).run ((initial.state, previous), [])))
    (receipt : Receipt) (member : receipt ∈ serverReceipts (history result.2.1.1.server)) :
    ∃ call leading trailing, result.2.2 = leading ++ call :: trailing ∧ Path impl (initial.state, previous) leading call.before ∧
      Executed impl call ∧ SourceAt call receipt := by
  have reached := RegistrationNativeStageTrace.path impl work (initial.state, previous) result supported
  rcases path_origin setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer reached receipt member with original | ⟨call, present, stage⟩
  · have empty := RegistrationNativeServerHistoryOrigin.start_empty setup ensureInit identityIndex serverKeyId initial startup
    rw [empty] at original
    cases original
  · obtain ⟨leading, trailing, split, before, called, _after⟩ := reached.member call present
    exact ⟨call, leading, trailing, split, before, called, stage⟩

/-- An actual prior unsigned Server issuance has an earlier same-run source build and exact hash stage; signature-byte equality and completed installation are unnecessary. -/
theorem issued_journal (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64)
    (initial : RegistrationNativeExperiment.Initial n KemSK source)
    (startup : some initial ∈ support (RegistrationNativeExperiment.start setup source ensureInit identityIndex serverKeyId))
    (previous : Platform) (work : OracleComp RegistrationNativeRawAdapter.TypedSpec Value)
    (result : Value × (Whole × List (Call RegistrationNativeRawAdapter.TypedSpec Whole)))
    (supported : result ∈ support ((simulateQ (RegistrationNativeStageTrace.handler impl) work).run ((initial.state, previous), [])))
    (publicKey : Pqxdh.Bytes) (payload : MldsaTranscriptAuth.Payload) (signature : Pqxdh.Bytes) (serverRole : payload.role = .server)
    (issued : MldsaTranscriptAuth.Issued (⟨publicKey, true,
      RegistrationSigningShared.historyFor publicKey (RegistrationNativeMldsaShared.nativeProject result.2.1.1), payload, signature⟩ : MldsaTranscriptAuth.Trial)) :
    ∃ call leading trailing receipt, result.2.2 = leading ++ call :: trailing ∧ Path impl (initial.state, previous) leading call.before ∧
      Executed impl call ∧ SourceAt call receipt ∧ receipt.observation.payload = payload ∧ PqxdhRefinement.absBytes receipt.observation.publicKey = publicKey := by
  obtain ⟨signed, member, samePayload⟩ := issued
  have historyMember : signed ∈ BeaconcryptCore.Refinement.RegistrationSigningTrace.historyFor publicKey
      ((history result.2.1.1.server).map Receipt.observation) := member
  obtain ⟨observation, observed, sameKey, sameCall⟩ :=
    (BeaconcryptCore.Refinement.RegistrationSigningHistory.history_mem_iff _ _ _).mp historyMember
  obtain ⟨receipt, recorded, sameObservation⟩ := List.mem_map.mp observed
  subst observation
  have content : receipt.observation.payload = payload :=
    (congrArg MldsaTranscriptAuth.SigningCall.payload sameCall).trans samePayload
  have included : receipt ∈ serverReceipts (history result.2.1.1.server) := by
    apply List.mem_filter.mpr
    exact ⟨recorded, by simp only [content, serverRole, decide_true]⟩
  obtain ⟨call, leading, trailing, split, before, called, stage⟩ := initialized_journal setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
    ensureInit identityIndex serverKeyId initial startup previous work result supported receipt included
  exact ⟨call, leading, trailing, receipt, split, before, called, stage, content, sameKey⟩

end BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryServerHistoryOrigin

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryServerHistoryOrigin.path_origin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryServerHistoryOrigin.path_origin

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryServerHistoryOrigin.initialized_journal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryServerHistoryOrigin.initialized_journal

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryServerHistoryOrigin.issued_journal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryServerHistoryOrigin.issued_journal
