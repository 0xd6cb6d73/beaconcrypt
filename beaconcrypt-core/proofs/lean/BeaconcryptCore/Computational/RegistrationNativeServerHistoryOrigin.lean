-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeMldsaRoleFrame
import BeaconcryptCore.Computational.RegistrationNativeStageJournal
import BeaconcryptCore.Computational.RegistrationNativeMldsaInitializedChronology

/-! Every Server-role receipt in one actual native source history originates at a same-run earlier response build, with its actual moved token and root-bearing source record stage. The derivation includes failed signing, encoding and insertion and does not assume prior-stage provenance. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeServerHistoryOrigin
open RegistrationNativeStageTrace (Call Path Executed)
open RegistrationNativeMldsaRoleFrame (serverReceipts NonBuild)
open RegistrationNativeServerIssuance (history)
open RegistrationSigningShared (Receipt)
open BeaconcryptCore.Refinement.RegistrationSigningTrace (Command)
open PqxdhServerAuthExperiment (Setup Checks)
variable {n : Nat} {ι KemSK V : Type} {base : OracleSpec ι} {source : RegistrationNativeMldsa.Source}
variable (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (credential : RegistrationNativeMldsa.Credential source)
local notation "Native" => RegistrationNativeExperiment.State n KemSK source
local notation "implementation" => RegistrationNativeExperiment.handler setup checks wire route representation created source credential
attribute [local irreducible] RegistrationNativeExperiment.handler

def SourceAt (call : Call RegistrationNativeRawAdapter.TypedSpec Native) (receipt : Receipt) : Prop :=
  ∃ index application token current plaintext availability initial hashed,
    call.query = .inr (.build index application) ∧
    RegistrationServerSdkSource.take index call.before.server = (some token, current) ∧ application = some plaintext ∧
    registration.begin_server_completion current.control current.pin availability token.agreement plaintext = .ok (.Ok initial) ∧
    RegistrationServerRecordExecutor.Path initial hashed ∧
    receipt.observation.publicKey = hashed.binding.server_pin.public_key ∧ receipt.observation.payload = Command.payload (.server hashed)

private theorem call_origin (call : Call RegistrationNativeRawAdapter.TypedSpec Native) (called : Executed implementation call)
    (receipt : Receipt) (member : receipt ∈ serverReceipts (history call.after.server)) :
    receipt ∈ serverReceipts (history call.before.server) ∨ SourceAt call receipt := by
  rcases call with ⟨query, before, reply, after⟩
  by_cases allowed : NonBuild query
  · have frame : serverReceipts (history after.server) = serverReceipts (history before.server) :=
      RegistrationNativeMldsaRoleFrame.handler setup checks wire route representation created credential query allowed before (reply, after) called
    exact Or.inl (frame ▸ member)
  · cases query with
    | inl coin => exact False.elim (allowed trivial)
    | inr query => cases query with
      | build index application =>
          obtain ⟨raw, role⟩ := List.mem_filter.mp member
          by_cases prior : receipt ∈ history before.server
          · exact Or.inl (List.mem_filter.mpr ⟨prior, role⟩)
          · obtain ⟨token, current, plaintext, availability, initial, hashed, taken, input, admitted, path, key, payload⟩ :=
              RegistrationNativeServerIssuance.new_receipt setup checks wire route representation created credential index application before after
                reply called receipt raw prior
            exact Or.inr ⟨index, application, token, current, plaintext, availability, initial, hashed, rfl,
              taken, input, admitted, path, key, payload⟩
      | _ => exact False.elim (allowed trivial)

/-- A complete native source path attributes each final Server receipt to an identical initial receipt or its actual earlier root-bearing build stage. -/
theorem path_origin {first last : Native} {calls : List (Call RegistrationNativeRawAdapter.TypedSpec Native)}
    (actual : Path implementation first calls last) (receipt : Receipt)
    (member : receipt ∈ serverReceipts (history last.server)) :
    receipt ∈ serverReceipts (history first.server) ∨ ∃ call ∈ calls, SourceAt call receipt := by
  induction actual with
  | nil => exact Or.inl member
  | cons call called rest last following ih =>
      rcases ih member with previous | ⟨earlier, inRest, stage⟩
      · rcases call_origin setup checks wire route representation created credential call called receipt previous with old | stage
        · exact Or.inl old
        · exact Or.inr ⟨call, List.mem_cons_self, stage⟩
      · exact Or.inr ⟨earlier, List.mem_cons_of_mem _ inRest, stage⟩

/-- Actual effectful startup has no preexisting Server signing receipt. -/
theorem start_empty (setup : Setup base KemSK) (ensureInit : StateT Unit ProbComp Bool)
    (identityIndex : Nat) (serverKeyId : Std.U64) (initial : RegistrationNativeExperiment.Initial n KemSK source)
    (supported : some initial ∈ support (RegistrationNativeExperiment.start setup source ensureInit identityIndex serverKeyId)) :
    history initial.state.server = [] := by
  simp only [RegistrationNativeExperiment.start, mem_support_bind_iff] at supported
  obtain ⟨constructed, _constructor, continued⟩ := supported
  cases born : constructed.1.1 with
  | none =>
      simp only [born, support_pure, Set.mem_singleton_iff] at continued
      cases continued
  | some created =>
      simp only [born, mem_support_bind_iff] at continued
      obtain ⟨generated, _generation, continued⟩ := continued
      cases keyed : generated.1 with
      | none =>
          simp only [keyed, support_pure, Set.mem_singleton_iff] at continued
          cases continued
      | some credential =>
          simp only [keyed, mem_support_bind_iff] at continued
          obtain ⟨initialized, possible, returned⟩ := continued
          rcases initialized with ⟨reply, after⟩
          cases reply with
          | fail error | div =>
              simp only [support_pure, Set.mem_singleton_iff] at returned
              cases returned
          | ok option => cases option with
            | none =>
                simp only [support_pure, Set.mem_singleton_iff] at returned
                cases returned
            | some native =>
                simp only [support_pure, Set.mem_singleton_iff] at returned
                cases returned
                exact RegistrationNativeMldsaInitializedChronology.world_start created credential.publicKey
                  RegistrationServerRoleBackend.empty generated.2 after native possible


/-- Every Server receipt in the actual initialized journal has its same-run earlier source build and actual consumed token/root/first-record stage. -/
theorem initialized_journal (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKid : U64)
    (initial : RegistrationNativeExperiment.Initial n KemSK source)
    (startup : some initial ∈ support (RegistrationNativeExperiment.start setup source ensureInit identityIndex serverKid))
    (work : OracleComp RegistrationNativeRawAdapter.TypedSpec V)
    (result : V × (Native × List (Call RegistrationNativeRawAdapter.TypedSpec Native)))
    (supported : result ∈ support ((simulateQ (RegistrationNativeStageTrace.handler
      (RegistrationNativeExperiment.handler setup checks wire route representation initial.created source initial.credential)) work).run (initial.state, [])))
    (receipt : Receipt) (member : receipt ∈ serverReceipts (history result.2.1.server)) :
    ∃ call leading trailing,
      result.2.2 = leading ++ call :: trailing ∧
      Path (RegistrationNativeExperiment.handler setup checks wire route representation initial.created source initial.credential)
        initial.state leading call.before ∧
      Executed (RegistrationNativeExperiment.handler setup checks wire route representation initial.created source initial.credential) call ∧
      SourceAt call receipt := by
  have actual := RegistrationNativeStageTrace.path
    (RegistrationNativeExperiment.handler setup checks wire route representation initial.created source initial.credential) work initial.state result supported
  rcases path_origin setup checks wire route representation initial.created initial.credential actual receipt member with original | ⟨call, present, stage⟩
  · have empty := start_empty setup ensureInit identityIndex serverKid initial startup
    rw [empty] at original
    cases original
  · obtain ⟨leading, trailing, split, before, called, _after⟩ := actual.member call present
    exact ⟨call, leading, trailing, split, before, called, stage⟩

/-- Same-key unsigned response issuance in the actual initialized history supplies an earlier same-run root-bearing Server stage; no signature-byte equality or completed peer premise is introduced. -/
theorem issued_journal (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKid : U64)
    (initial : RegistrationNativeExperiment.Initial n KemSK source)
    (startup : some initial ∈ support (RegistrationNativeExperiment.start setup source ensureInit identityIndex serverKid))
    (work : OracleComp RegistrationNativeRawAdapter.TypedSpec V)
    (result : V × (Native × List (Call RegistrationNativeRawAdapter.TypedSpec Native)))
    (supported : result ∈ support ((simulateQ (RegistrationNativeStageTrace.handler
      (RegistrationNativeExperiment.handler setup checks wire route representation initial.created source initial.credential)) work).run (initial.state, [])))
    (publicKey : Pqxdh.Bytes) (payload : MldsaTranscriptAuth.Payload) (signature : Pqxdh.Bytes)
    (serverRole : payload.role = .server)
    (issued : MldsaTranscriptAuth.Issued (⟨publicKey, true,
      RegistrationSigningShared.historyFor publicKey (RegistrationNativeMldsaShared.nativeProject result.2.1), payload, signature⟩ : MldsaTranscriptAuth.Trial)) :
    ∃ call leading trailing receipt,
      result.2.2 = leading ++ call :: trailing ∧
      Path (RegistrationNativeExperiment.handler setup checks wire route representation initial.created source initial.credential)
        initial.state leading call.before ∧
      Executed (RegistrationNativeExperiment.handler setup checks wire route representation initial.created source initial.credential) call ∧
      SourceAt call receipt ∧ receipt.observation.payload = payload ∧ PqxdhRefinement.absBytes receipt.observation.publicKey = publicKey := by
  obtain ⟨signed, member, samePayload⟩ := issued
  have historyMember : signed ∈ BeaconcryptCore.Refinement.RegistrationSigningTrace.historyFor publicKey
      ((history result.2.1.server).map Receipt.observation) := member
  obtain ⟨observation, observed, sameKey, sameCall⟩ :=
    (BeaconcryptCore.Refinement.RegistrationSigningHistory.history_mem_iff _ _ _).mp historyMember
  obtain ⟨receipt, recorded, sameObservation⟩ := List.mem_map.mp observed
  subst observation
  have content : receipt.observation.payload = payload :=
    (congrArg MldsaTranscriptAuth.SigningCall.payload sameCall).trans samePayload
  have included : receipt ∈ serverReceipts (history result.2.1.server) := by
    apply List.mem_filter.mpr
    exact ⟨recorded, by simp only [content, serverRole, decide_true]⟩
  obtain ⟨call, leading, trailing, split, before, called, stage⟩ := initialized_journal setup checks wire route representation
    ensureInit identityIndex serverKid initial startup work result supported receipt included
  exact ⟨call, leading, trailing, receipt, split, before, called, stage, content, sameKey⟩

end BeaconcryptCore.Computational.RegistrationNativeServerHistoryOrigin
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeServerHistoryOrigin.path_origin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeServerHistoryOrigin.path_origin

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeServerHistoryOrigin.start_empty' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeServerHistoryOrigin.start_empty

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeServerHistoryOrigin.initialized_journal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeServerHistoryOrigin.initialized_journal

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeServerHistoryOrigin.issued_journal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeServerHistoryOrigin.issued_journal
