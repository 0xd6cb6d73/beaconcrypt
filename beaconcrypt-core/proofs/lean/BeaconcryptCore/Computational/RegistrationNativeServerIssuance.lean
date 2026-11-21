-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeServerSigningOrigin

/-! Every new response issuance in an actual SDK build is attached to its moved registration token, initial root capability and source first-record path, including later signature, encoding and insertion failures. Issuance does not assert completed peer installation. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeServerIssuance
open PqxdhServerAuthExperiment (Setup Codec Checks)
open RegistrationSigningShared (SignReply Receipt)
open BeaconcryptCore.Refinement.RegistrationSigningTrace (Command replyBytes)
open RegistrationServerFrontendCompiler (State)
variable {n : Nat} {ι KemSK Reader Response : Type} {base : OracleSpec ι}

abbrev history (before : State n) := before.world.world.2

/-- One actual source AD callback, retaining its owned continuation and complete reached source states. The capacity is private state representation and is irrelevant to the public core admission. -/
def AdCut (token : peer.ConsumedRegistration) (control : pqxdh.ServerState)
    (pin : session.ServerAuthenticationPin) (availability : pqxdh.KeyIdAvailability)
    (application : Slice U8) (initial : registration.ServerInitialKdf) : Prop :=
  ∃ capacity : Nat, ∃ pending : registration.ServerAdHash, ∃ before after : State capacity,
    registration.begin_server_completion control pin availability token.agreement application = .ok (.Ok pending) ∧
    (.ok (.Ok initial), after) ∈ support ((RegistrationServerSdkSource.adHash pending).run before)

def Stage (token : peer.ConsumedRegistration) (control : pqxdh.ServerState) (pin : session.ServerAuthenticationPin)
    (application : Slice U8) (old newest : List Receipt) : Prop :=
  ∃ availability initial hashed digest signature,
    BeaconcryptCore.Refinement.RegistrationAd.ServerAdmission control pin availability token.agreement application initial ∧
    RegistrationServerRecordExecutor.Path initial hashed ∧
    newest = old ++ [(⟨⟨hashed.binding.server_pin.public_key, Command.payload (.server hashed), replyBytes signature⟩, digest⟩ : Receipt)] ∧
    AdCut token control pin availability application initial

private theorem pure_history {Value : Type} (value : Value) (before : State n) (result : Value × State n)
    (supported : result ∈ support ((pure value : StateT (State n) ProbComp Value).run before)) : history result.2 = history before := by
  simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
  cases supported
  rfl

private theorem commit_history (published : RustM (RegistrationWorldServerCompletion.Result Pqxdh.Bytes))
    (before : State n) (result : RustM (Option (U64 × Pqxdh.Bytes)) × State n)
    (supported : result ∈ support ((RegistrationServerSdkSource.commit published).run before)) : history result.2 = history before := by
  cases published with
  | fail error | div =>
      simp only [RegistrationServerSdkSource.commit, StateT.run, support_pure, Set.mem_singleton_iff] at supported
      cases supported
      rfl
  | ok answer => cases answer <;>
      simp only [RegistrationServerSdkSource.commit, StateT.run, support_pure, Set.mem_singleton_iff] at supported <;>
      cases supported <;> rfl

private theorem fromInitial_history (setup : Setup base KemSK) (codec : Codec Reader Response)
    (sign : registration.MldsaSigningRequest → ProbComp SignReply)
    (encode : registration.SignedResponseView → core.option.Option Pqxdh.Bytes)
    (control : pqxdh.ServerState) (initial : registration.ServerInitialKdf)
    (before : State n) (result : RustM (Option (U64 × Pqxdh.Bytes)) × State n)
    (supported : result ∈ support ((RegistrationServerSdkSource.fromInitial setup codec sign encode control initial).run before)) :
    history result.2 = history before ∨ ∃ hashed digest signature,
      RegistrationServerRecordExecutor.Path initial hashed ∧
      history result.2 = history before ++
        [(⟨⟨hashed.binding.server_pin.public_key, Command.payload (.server hashed), replyBytes signature⟩, digest⟩ : Receipt)] := by
  rw [RegistrationServerSdkSource.fromInitial, StateT.run_bind, mem_support_bind_iff] at supported
  obtain ⟨middle, queried, continued⟩ := supported
  simp only [RegistrationServerSdkSource.world, StateT.run, support_map] at queried
  obtain ⟨inner, reached, same⟩ := queried
  subst middle
  have retained := commit_history inner.1 _ result continued
  rcases RegistrationNativeServerSigningOrigin.fromInitial_stage setup codec sign encode control initial before.world inner reached
      with unchanged | ⟨hashed, _recorded, digest, signature, _supported, path, appended⟩
  · exact Or.inl (retained.trans unchanged)
  · exact Or.inr ⟨hashed, digest, signature, path, retained.trans appended⟩

private theorem afterOccupancy_history (setup : Setup base KemSK) (codec : Codec Reader Response) (checks : Checks)
    (sign : registration.MldsaSigningRequest → ProbComp SignReply)
    (encode : registration.SignedResponseView → core.option.Option Pqxdh.Bytes)
    (control : pqxdh.ServerState) (lookup : peer.CompletionLookup) (occupied : Bool)
    (before : State n) (result : RustM (Option (U64 × Pqxdh.Bytes)) × State n)
    (supported : result ∈ support ((RegistrationServerSdkSource.afterOccupancy setup codec checks sign encode control lookup occupied).run before)) :
    history result.2 = history before ∨ Stage lookup.registration lookup.control lookup.pin lookup.application (history before) (history result.2) := by
  unfold RegistrationServerSdkSource.afterOccupancy at supported
  cases resumed : lookup.resume occupied with
  | fail error | div =>
      simp only [resumed] at supported
      exact Or.inl (pure_history _ before result supported)
  | ok answer => cases answer with
    | Err previous =>
        simp only [resumed] at supported
        exact Or.inl (pure_history _ before result supported)
    | Ok pendingAd =>
        simp only [resumed, StateT.run_bind, mem_support_bind_iff] at supported
        obtain ⟨middle, hashCalled, continued⟩ := supported
        have retained := RegistrationServerSdkSource.adHash_history pendingAd before middle.2 middle.1 hashCalled
        cases reply : middle.1 with
        | fail error | div =>
            rw [reply] at continued
            exact Or.inl ((pure_history _ middle.2 result continued).trans retained)
        | ok answer => cases answer with
          | Err previous =>
              rw [reply] at continued
              exact Or.inl ((pure_history _ middle.2 result continued).trans retained)
          | Ok initial =>
              have hashSupport : (.ok (.Ok initial), middle.2) ∈ support
                  ((RegistrationServerSdkSource.adHash pendingAd).run before) := by
                have same : middle = (.ok (.Ok initial), middle.2) := Prod.ext reply rfl
                exact same ▸ hashCalled
              obtain ⟨adDigest, adResumed⟩ := RegistrationServerSdkSource.adHash_receipt pendingAd before middle.2 initial
                hashSupport
              rw [reply] at continued
              split_ifs at continued with reserved
              · rcases fromInitial_history setup codec sign encode control initial middle.2 result continued with old | added
                · exact Or.inl (old.trans retained)
                · obtain ⟨hashed, digest, signature, path, appended⟩ := added
                  have admitted : registration.begin_server_completion lookup.control lookup.pin
                      (if occupied then .Occupied else .Available) lookup.registration.agreement lookup.application = .ok (.Ok pendingAd) := by
                    cases occupied <;> simpa only [peer.CompletionLookup.resume, Bool.false_eq_true, ite_false, ite_true, bind_tc_ok] using resumed
                  exact Or.inr ⟨_, initial, hashed, digest, signature, ⟨pendingAd, adDigest, admitted, adResumed⟩,
                    path, (by simpa only [retained] using appended),
                    ⟨n, pendingAd, before, middle.2, admitted, hashSupport⟩⟩
              · exact Or.inl ((pure_history _ middle.2 result continued).trans retained)

private theorem occupancy_history (keyId : U64) (before : State n) (result : Bool × State n)
    (supported : result ∈ support ((RegistrationServerSdkSource.world
      (RegistrationWorldServerCompletion.capability (.peerPresent keyId))).run before)) : history result.2 = history before := by
  simp only [RegistrationServerSdkSource.world, RegistrationWorldServerCompletion.capability, StateT.run, Functor.map_map, support_map] at supported
  obtain ⟨inner, _queried, same⟩ := supported
  cases same
  rfl

/-- Every newly attempted response from actual completion keeps the exact supplied consumed token and source gate, including all later failures. -/
theorem complete (setup : Setup base KemSK) (codec : Codec Reader Response) (checks : Checks)
    (sign : registration.MldsaSigningRequest → ProbComp SignReply)
    (encode : registration.SignedResponseView → core.option.Option Pqxdh.Bytes)
    (token : peer.ConsumedRegistration) (application : Slice U8) (before : State n)
    (result : RustM (Option (U64 × Pqxdh.Bytes)) × State n)
    (supported : result ∈ support ((RegistrationServerSdkSource.complete setup codec checks sign encode token application).run before)) :
    history result.2 = history before ∨ Stage token before.control before.pin application (history before) (history result.2) := by
  simp only [RegistrationServerSdkSource.complete, StateT.run] at supported
  cases looked : peer.begin_completion_lookup before.control before.pin token application with
  | fail error | div =>
      simp only [looked] at supported
      exact Or.inl (pure_history _ before result supported)
  | ok answer => cases answer with
    | Err previous =>
        simp only [looked] at supported
        exact Or.inl (pure_history _ before result supported)
    | Ok lookup =>
        simp only [looked] at supported
        cases requested : lookup.request with
        | fail error | div =>
            simp only [requested] at supported
            exact Or.inl (pure_history _ before result supported)
        | ok keyId =>
            simp only [requested] at supported
            split_ifs at supported with admitted
            · rw [mem_support_bind_iff] at supported
              obtain ⟨occupied, queried, continued⟩ := supported
              have old : history occupied.2 = history before := occupancy_history keyId before occupied queried
              obtain ⟨controlEq, pinEq, tokenEq, appEq⟩ :=
                RegistrationNativeServerBindingReceipt.lookup_fields before.control before.pin token application lookup looked
              rcases afterOccupancy_history setup codec checks sign encode before.control lookup occupied.1 occupied.2 result continued with unchanged | stage
              · exact Or.inl (unchanged.trans old)
              · exact Or.inr (by simpa only [old, controlEq, pinEq, tokenEq, appEq] using stage)
            · exact Or.inl (pure_history _ before result supported)

private theorem take_history (index : Nat) (before : State n) : history (RegistrationServerSdkSource.take index before).2 = history before := by
  cases found : before.sessions[index]? with
  | none => simp only [RegistrationServerSdkSource.take, found]
  | some token => cases token <;> simp only [RegistrationServerSdkSource.take, found]

/-- Any new response issuance from an actual moved-handle SDK build retains the actual consumed token and initial root stage, even when build returns failure. -/
theorem build (setup : Setup base KemSK) (codec : Codec Reader Response) (checks : Checks)
    (sign : registration.MldsaSigningRequest → ProbComp SignReply)
    (encode : registration.SignedResponseView → core.option.Option Pqxdh.Bytes)
    (index : Nat) (application : Option (Slice U8)) (before : State n)
    (result : RustM (Option (U64 × Pqxdh.Bytes)) × State n)
    (supported : result ∈ support ((RegistrationServerSdkSource.build setup codec checks sign encode index application).run before)) :
    history result.2 = history before ∨ ∃ token current plaintext,
      RegistrationServerSdkSource.take index before = (some token, current) ∧ application = some plaintext ∧
      Stage token current.control current.pin plaintext (history before) (history result.2) := by
  simp only [RegistrationServerSdkSource.build, StateT.run] at supported
  have retained := take_history index before
  cases taken : RegistrationServerSdkSource.take index before with
  | mk token current =>
      rw [taken] at retained
      change history current = history before at retained
      cases token with
      | none =>
          simp only [taken] at supported
          exact Or.inl ((pure_history _ current result supported).trans retained)
      | some token =>
          simp only [taken] at supported
          cases application with
          | none => exact Or.inl ((pure_history _ current result supported).trans retained)
          | some plaintext =>
              rcases complete setup codec checks sign encode token plaintext current result supported with old | stage
              · exact Or.inl (old.trans retained)
              · exact Or.inr ⟨token, current, plaintext, rfl, rfl, by simpa only [retained] using stage⟩

/-- Every issued response retains the actual hash-completed binding, root initializer and complete consumed sequence-one AD151 context. -/
theorem stage_contents (token : peer.ConsumedRegistration) (control : pqxdh.ServerState) (pin : session.ServerAuthenticationPin)
    (application : Slice U8) (old newest : List Receipt)
    (stage : Stage token control pin application old newest) :
    ∃ (digest : Std.Array U8 64#usize) (binding : session.CompletedRegistrationBinding)
        (initial : registration.ServerInitialKdf) (hashed : registration.ServerResponseHash),
      token.agreement.binding.complete digest = .ok binding ∧
      BeaconcryptCore.Refinement.SessionBinding.sameServerPin token.agreement.binding.server_pin pin ∧
      initial.binding = binding ∧ initial.application = application ∧
      pqxdh.concrete.start_server_candidate_ratchet_kdf initial.candidate token.agreement.root.bytes = .ok initial.pending ∧
      RegistrationServerRecordExecutor.Path initial hashed ∧ hashed.binding = binding ∧
      ∃ selected : ratchet.concrete.SendSeal record_effects.SealFrameContext,
        hashed.kernel = selected.advanced ∧ selected.sequence.val = 1 ∧
        selected.context.plaintext = application ∧ selected.context.associated_data = binding.associated_data := by
  obtain ⟨availability, initial, hashed, _digest, _signature, admitted, path, _appended, _adCut⟩ := stage
  obtain ⟨pinSame, adDigest, binding, completed, sameBinding, payload, rooted⟩ :=
    RegistrationNativeServerBindingReceipt.initial_root control pin availability token.agreement application initial admitted
  obtain ⟨retained, _candidate, _response, _kernel, bound, selected, _initialized, _boundRun, _boundBytes, consumed, sequence, context⟩ :=
    RegistrationNativeServerContents.path_contents initial hashed path
  exact ⟨adDigest, binding, initial, hashed, completed, pinSame, sameBinding, payload, rooted, path, retained.trans sameBinding,
    selected, consumed, sequence, by rw [context]; exact payload,
    by rw [context]; exact congrArg session.CompletedRegistrationBinding.associated_data sameBinding⟩

/-- Every complete original typed build has that same moved-token issuance alternative on all source outcomes. -/
theorem typed_build {source : RegistrationNativeMldsa.Source}
    (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (credential : RegistrationNativeMldsa.Credential source)
    (index : Nat) (application : Option (Slice U8)) (before : RegistrationNativeExperiment.State n KemSK source)
    (result : RustM (Option (U64 × Pqxdh.Bytes)) × RegistrationNativeExperiment.State n KemSK source)
    (supported : result ∈ support ((RegistrationNativeExperiment.handler setup checks wire route representation created source credential
      (.inr (.build index application))).run before)) :
    history result.2.server = history before.server ∨ ∃ token current plaintext,
      RegistrationServerSdkSource.take index before.server = (some token, current) ∧ application = some plaintext ∧
      Stage token current.control current.pin plaintext (history before.server) (history result.2.server) := by
  simp only [RegistrationNativeExperiment.handler, RegistrationNativeExperiment.server, StateT.run, support_map] at supported
  obtain ⟨inner, reached, same⟩ := supported
  cases same
  exact build setup (RegistrationNativeWire.ledgerCodec wire) checks (RegistrationNativeMldsa.owned source credential)
    wire.encodeResponse index application before.server inner reached

/-- A newly recorded actual native response receipt has a same-run moved token and root-bearing first-record source stage, irrespective of later build failure. -/
theorem new_receipt {source : RegistrationNativeMldsa.Source}
    (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (credential : RegistrationNativeMldsa.Credential source)
    (index : Nat) (application : Option (Slice U8)) (before after : RegistrationNativeExperiment.State n KemSK source)
    (answer : RustM (Option (U64 × Pqxdh.Bytes)))
    (supported : (answer, after) ∈ support ((RegistrationNativeExperiment.handler setup checks wire route representation created source credential
      (.inr (.build index application))).run before))
    (receipt : Receipt) (member : receipt ∈ history after.server) (fresh : receipt ∉ history before.server) :
    ∃ token current plaintext availability initial hashed,
      RegistrationServerSdkSource.take index before.server = (some token, current) ∧ application = some plaintext ∧
      BeaconcryptCore.Refinement.RegistrationAd.ServerAdmission current.control current.pin availability token.agreement plaintext initial ∧
      RegistrationServerRecordExecutor.Path initial hashed ∧
      receipt.observation.publicKey = hashed.binding.server_pin.public_key ∧ receipt.observation.payload = Command.payload (.server hashed) := by
  rcases typed_build setup checks wire route representation created credential index application before (answer, after) supported with old | issued
  · exact False.elim (fresh (old ▸ member))
  · obtain ⟨token, current, plaintext, taken, input, availability, initial, hashed, digest, signature, admitted, path, appended, _adCut⟩ := issued
    rw [appended, List.mem_append, List.mem_singleton] at member
    rcases member with earlier | same
    · exact False.elim (fresh earlier)
    · subst receipt
      exact ⟨token, current, plaintext, availability, initial, hashed, taken, input, admitted, path, rfl, rfl⟩

end BeaconcryptCore.Computational.RegistrationNativeServerIssuance
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeServerIssuance.complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeServerIssuance.complete

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeServerIssuance.build' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeServerIssuance.build

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeServerIssuance.stage_contents' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeServerIssuance.stage_contents

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeServerIssuance.typed_build' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeServerIssuance.typed_build

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeServerIssuance.new_receipt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeServerIssuance.new_receipt
