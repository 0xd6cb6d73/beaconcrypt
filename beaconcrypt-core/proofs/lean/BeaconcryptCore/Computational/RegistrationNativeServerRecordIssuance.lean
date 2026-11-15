-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeWorldStageCache
import BeaconcryptCore.Computational.RegistrationNativeInitialKdfReceipt
import BeaconcryptCore.Computational.RegistrationNativeServerSigningOrigin
import BeaconcryptCore.Computational.RegistrationNativeAdHashCache

/-! Every new response issuance in an actual SDK build retains its moved token and an actual supported concrete World first-record computation, including later signing, encoding and insertion failures. The source cut retains concrete initial/step replies rather than only an abstract path. Completed peer installation is not asserted. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeServerRecordIssuance
open PqxdhServerAuthExperiment (Setup Codec Checks)
open RegistrationSigningShared (SignReply Receipt)
open BeaconcryptCore.Refinement.RegistrationSigningTrace (Command replyBytes)
open RegistrationServerFrontendCompiler (State)
variable {n : Nat} {ι KemSK Reader Response : Type} {base : OracleSpec ι}

abbrev history (before : State n) := before.world.world.2

/-- An actually reached concrete World first-record computation, before any later response signing or publication outcome. -/
def RecordCut (setup : Setup base KemSK) (codec : Codec Reader Response)
    (initial : registration.ServerInitialKdf) (hashed : registration.ServerResponseHash) (cache : CtxRomAuth.CtxRO.QueryCache) : Prop :=
  ∃ before recorded : RegistrationWorldAgreement.State n RegistrationServerRoleBackend.State,
    (.ok (.Ok hashed), recorded) ∈ support ((simulateQ (RegistrationWorldRecords.handler setup codec)
      (RegistrationServerRecordExecutor.fromInitial initial)).run before) ∧ recorded.world.1.primitive.2 ≤ cache

/-- The actual earlier AD callback and its reached hash state remain connected to this same later record cache. -/
def AdCut (token : peer.ConsumedRegistration) (control : pqxdh.ServerState)
    (pin : session.ServerAuthenticationPin) (availability : pqxdh.KeyIdAvailability)
    (application : Slice U8) (initial : registration.ServerInitialKdf)
    (cache : CtxRomAuth.CtxRO.QueryCache) : Prop :=
  ∃ pending : registration.ServerAdHash, ∃ before after : State n,
    registration.begin_server_completion control pin availability token.agreement application = .ok (.Ok pending) ∧
    (.ok (.Ok initial), after) ∈ support ((RegistrationServerSdkSource.adHash pending).run before) ∧
    after.world.world.1.primitive.2 ≤ cache

def Stage (setup : Setup base KemSK) (codec : Codec Reader Response) (token : peer.ConsumedRegistration) (control : pqxdh.ServerState) (pin : session.ServerAuthenticationPin)
    (application : Slice U8) (cache : CtxRomAuth.CtxRO.QueryCache) (old newest : List Receipt) : Prop :=
  ∃ availability initial hashed digest signature,
    BeaconcryptCore.Refinement.RegistrationAd.ServerAdmission control pin availability token.agreement application initial ∧
    RegistrationServerRecordExecutor.Path initial hashed ∧ RecordCut (n := n) setup codec initial hashed cache ∧
    newest = old ++ [(⟨⟨hashed.binding.server_pin.public_key, Command.payload (.server hashed), replyBytes signature⟩, digest⟩ : Receipt)] ∧
    AdCut (n := n) token control pin availability application initial cache

/-- The actual retained AD cut supplies its selected preimage digest in this same later record cache. -/
theorem AdCut.cached (token : peer.ConsumedRegistration) (control : pqxdh.ServerState)
    (pin : session.ServerAuthenticationPin) (availability : pqxdh.KeyIdAvailability)
    (application : Slice U8) (initial : registration.ServerInitialKdf)
    (cache : CtxRomAuth.CtxRO.QueryCache)
    (cut : AdCut (n := n) token control pin availability application initial cache) :
    ∃ pending : registration.ServerAdHash, ∃ digest : CtxRomAuth.CtxDigest,
      registration.begin_server_completion control pin availability token.agreement application = .ok (.Ok pending) ∧
      pending.resume (.Some (RegistrationAuthenticationShared.digestArray digest)) = .ok (.Ok initial) ∧
      cache ((), PqxdhRefinement.absBytes pending.input) = some digest := by
  obtain ⟨pending, before, after, began, called, extension⟩ := cut
  obtain ⟨digest, resumed, _extended, cached⟩ :=
    RegistrationNativeAdHashCache.sdk_ad_hash_cached pending before after initial called
  exact ⟨pending, digest, began, resumed, extension cached⟩

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

private theorem commit_cache (published : RustM (RegistrationWorldServerCompletion.Result Pqxdh.Bytes))
    (before : State n) (result : RustM (Option (U64 × Pqxdh.Bytes)) × State n)
    (supported : result ∈ support ((RegistrationServerSdkSource.commit published).run before)) :
    result.2.world.world.1.primitive.2 = before.world.world.1.primitive.2 := by
  cases published with
  | fail error | div =>
      simp only [RegistrationServerSdkSource.commit, StateT.run, support_pure, Set.mem_singleton_iff] at supported
      cases supported
      rfl
  | ok answer => cases answer <;>
      simp only [RegistrationServerSdkSource.commit, StateT.run, support_pure, Set.mem_singleton_iff] at supported <;>
      cases supported <;> rfl

private theorem world_pure_history {Value : Type} (value : Value)
    (before : RegistrationWorldAgreement.State n RegistrationServerRoleBackend.State)
    (result : Value × RegistrationWorldAgreement.State n RegistrationServerRoleBackend.State)
    (supported : result ∈ support ((pure value : StateT _ ProbComp Value).run before)) : result.2.world.2 = before.world.2 := by
  simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
  cases supported
  rfl

private theorem world_stage (setup : Setup base KemSK) (codec : Codec Reader Response)
    (sign : registration.MldsaSigningRequest → ProbComp SignReply)
    (encode : registration.SignedResponseView → core.option.Option Pqxdh.Bytes)
    (control : pqxdh.ServerState) (initial : registration.ServerInitialKdf)
    (before : RegistrationWorldAgreement.State n RegistrationServerRoleBackend.State)
    (result : RustM (RegistrationWorldServerCompletion.Result Pqxdh.Bytes) × RegistrationWorldAgreement.State n RegistrationServerRoleBackend.State)
    (supported : result ∈ support ((RegistrationWorldServerCompletion.fromInitial setup codec sign encode control initial).run before)) :
    result.2.world.2 = before.world.2 ∨ ∃ hashed recorded digest signature,
      (.ok (.Ok hashed), recorded) ∈ support ((simulateQ (RegistrationWorldRecords.handler setup codec)
        (RegistrationServerRecordExecutor.fromInitial initial)).run before) ∧
      RegistrationServerRecordExecutor.Path initial hashed ∧ recorded.world.1.primitive.2 ≤ result.2.world.1.primitive.2 ∧
      result.2.world.2 = before.world.2 ++ [(⟨⟨hashed.binding.server_pin.public_key, Command.payload (.server hashed), replyBytes signature⟩, digest⟩ : Receipt)] := by
  rw [RegistrationWorldServerCompletion.fromInitial, StateT.run_bind, mem_support_bind_iff] at supported
  obtain ⟨⟨reply, middle⟩, called, continued⟩ := supported
  have facts := RegistrationNativeWorldStageCache.records setup codec (RegistrationServerRecordExecutor.fromInitial initial) before (reply, middle) called
  have unchanged : middle.world.2 = before.world.2 := facts.2
  cases reply with
  | fail error | div => exact Or.inl ((world_pure_history _ middle result continued).trans facts.2)
  | ok answer => cases answer with
    | Err previous => exact Or.inl ((world_pure_history _ middle result continued).trans facts.2)
    | Ok hashed =>
      obtain ⟨digest, signature, appended⟩ := RegistrationNativeServerSigningOrigin.publish_receipt sign encode control hashed middle result continued
      have cached := RegistrationNativeWorldStageCache.publication sign encode control hashed middle result continued
      have path : RegistrationServerRecordExecutor.Path initial hashed := by
        apply RegistrationServerRecordExecutor.fromInitial_path
        apply OracleComp.support_simulateQ_run'_subset (RegistrationWorldRecords.handler setup codec) _ before
        rw [StateT.run'_eq, support_map]
        exact Set.mem_image_of_mem Prod.fst called
      exact Or.inr ⟨hashed, middle, digest, signature, called, path, cached, by simpa only [unchanged] using appended⟩

private theorem fromInitial_history (setup : Setup base KemSK) (codec : Codec Reader Response)
    (sign : registration.MldsaSigningRequest → ProbComp SignReply)
    (encode : registration.SignedResponseView → core.option.Option Pqxdh.Bytes)
    (control : pqxdh.ServerState) (initial : registration.ServerInitialKdf)
    (before : State n) (result : RustM (Option (U64 × Pqxdh.Bytes)) × State n)
    (supported : result ∈ support ((RegistrationServerSdkSource.fromInitial setup codec sign encode control initial).run before)) :
    history result.2 = history before ∨ ∃ hashed digest signature,
      RegistrationServerRecordExecutor.Path initial hashed ∧ RecordCut (n := n) setup codec initial hashed result.2.world.world.1.primitive.2 ∧
      before.world.world.1.primitive.2 ≤ result.2.world.world.1.primitive.2 ∧
      history result.2 = history before ++
        [(⟨⟨hashed.binding.server_pin.public_key, Command.payload (.server hashed), replyBytes signature⟩, digest⟩ : Receipt)] := by
  rw [RegistrationServerSdkSource.fromInitial, StateT.run_bind, mem_support_bind_iff] at supported
  obtain ⟨middle, queried, continued⟩ := supported
  simp only [RegistrationServerSdkSource.world, StateT.run, support_map] at queried
  obtain ⟨inner, reached, same⟩ := queried
  subst middle
  have retained := commit_history inner.1 _ result continued
  have retainedCache := commit_cache inner.1 _ result continued
  rcases world_stage setup codec sign encode control initial before.world inner reached
      with unchanged | ⟨hashed, recorded, digest, signature, recordSupport, path, cacheBound, appended⟩
  · exact Or.inl (retained.trans unchanged)
  · have recordExtension := (RegistrationNativeWorldStageCache.records setup codec
      (RegistrationServerRecordExecutor.fromInitial initial) before.world (.ok (.Ok hashed), recorded) recordSupport).1
    exact Or.inr ⟨hashed, digest, signature, path,
      ⟨before.world, recorded, recordSupport, cacheBound.trans retainedCache.symm.le⟩,
      recordExtension.trans (cacheBound.trans retainedCache.symm.le), retained.trans appended⟩

private theorem afterOccupancy_history (setup : Setup base KemSK) (codec : Codec Reader Response) (checks : Checks)
    (sign : registration.MldsaSigningRequest → ProbComp SignReply)
    (encode : registration.SignedResponseView → core.option.Option Pqxdh.Bytes)
    (control : pqxdh.ServerState) (lookup : peer.CompletionLookup) (occupied : Bool)
    (before : State n) (result : RustM (Option (U64 × Pqxdh.Bytes)) × State n)
    (supported : result ∈ support ((RegistrationServerSdkSource.afterOccupancy setup codec checks sign encode control lookup occupied).run before)) :
    history result.2 = history before ∨ Stage (n := n) setup codec lookup.registration lookup.control lookup.pin lookup.application result.2.world.world.1.primitive.2 (history before) (history result.2) := by
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
              obtain ⟨adDigest, adResumed⟩ := RegistrationServerSdkSource.adHash_receipt pendingAd before middle.2 initial
                (by rw [← reply]; exact hashCalled)
              rw [reply] at continued
              split_ifs at continued with reserved
              · rcases fromInitial_history setup codec sign encode control initial middle.2 result continued with old | added
                · exact Or.inl (old.trans retained)
                · obtain ⟨hashed, digest, signature, path, recordCut, cacheExtension, appended⟩ := added
                  have admitted : registration.begin_server_completion lookup.control lookup.pin
                      (if occupied then .Occupied else .Available) lookup.registration.agreement lookup.application = .ok (.Ok pendingAd) := by
                    cases occupied <;> simpa only [peer.CompletionLookup.resume, Bool.false_eq_true, ite_false, ite_true, bind_tc_ok] using resumed
                  exact Or.inr ⟨_, initial, hashed, digest, signature, ⟨pendingAd, adDigest, admitted, adResumed⟩,
                    path, recordCut, (by simpa only [retained] using appended),
                    ⟨pendingAd, before, middle.2, admitted, (by rw [← reply]; exact hashCalled), cacheExtension⟩⟩
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
    history result.2 = history before ∨ Stage (n := n) setup codec token before.control before.pin application result.2.world.world.1.primitive.2 (history before) (history result.2) := by
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
      Stage (n := n) setup codec token current.control current.pin plaintext result.2.world.world.1.primitive.2 (history before) (history result.2) := by
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
theorem stage_contents (setup : Setup base KemSK) (codec : Codec Reader Response) (token : peer.ConsumedRegistration) (control : pqxdh.ServerState) (pin : session.ServerAuthenticationPin)
    (application : Slice U8) (cache : CtxRomAuth.CtxRO.QueryCache) (old newest : List Receipt)
    (stage : Stage (n := n) setup codec token control pin application cache old newest) :
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
  obtain ⟨availability, initial, hashed, _digest, _signature, admitted, path, _recordCut, _appended, _adCut⟩ := stage
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
      Stage (n := n) setup (RegistrationNativeWire.ledgerCodec wire) token current.control current.pin plaintext result.2.server.world.world.1.primitive.2 (history before.server) (history result.2.server) := by
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
      RecordCut (n := n) setup (RegistrationNativeWire.ledgerCodec wire) initial hashed after.server.world.world.1.primitive.2 ∧
      receipt.observation.publicKey = hashed.binding.server_pin.public_key ∧ receipt.observation.payload = Command.payload (.server hashed) := by
  rcases typed_build setup checks wire route representation created credential index application before (answer, after) supported with old | issued
  · exact False.elim (fresh (old ▸ member))
  · obtain ⟨token, current, plaintext, taken, input, availability, initial, hashed, digest, signature, admitted, path, recordCut, appended, _adCut⟩ := issued
    rw [appended, List.mem_append, List.mem_singleton] at member
    rcases member with earlier | same
    · exact False.elim (fresh earlier)
    · subst receipt
      exact ⟨token, current, plaintext, availability, initial, hashed, taken, input, admitted, path, recordCut, rfl, rfl⟩

/-- Every retained concrete record cut contains the actual fixed-source initial response and source resume. -/
theorem RecordCut.initial (setup : Setup base KemSK) (codec : Codec Reader Response)
    (initial : registration.ServerInitialKdf) (hashed : registration.ServerResponseHash)
    (cache : CtxRomAuth.CtxRO.QueryCache) (cut : RecordCut (n := n) setup codec initial hashed cache) :
    ∃ (before recorded : RegistrationWorldAgreement.State n RegistrationServerRoleBackend.State)
      (request : ratchet.InitialRatchetKdfRequest) (atStep : RegistrationWorldAgreement.State n RegistrationServerRoleBackend.State)
      (next : registration.ServerInitialSeal),
      (.ok (.Ok hashed), recorded) ∈ support ((simulateQ (RegistrationWorldRecords.handler setup codec)
        (RegistrationServerRecordExecutor.fromInitial initial)).run before) ∧
      initial.request = .ok request ∧
      (.Some (RawCtxSourceHkdf.initialResponse setup.source.crypto request), atStep) ∈ support
        ((RegistrationWorldRecords.handler setup codec (.initialKdf request)).run before) ∧
      initial.resume (.Some (RawCtxSourceHkdf.initialResponse setup.source.crypto request)) = .ok (.Ok next) ∧
      (.ok (.Ok hashed), recorded) ∈ support ((simulateQ (RegistrationWorldRecords.handler setup codec)
        (RegistrationServerRecordExecutor.fromRatchet next)).run atStep) := by
  obtain ⟨before, recorded, supported, _extension⟩ := cut
  obtain ⟨request, atStep, next, requested, called, resumed, continued⟩ :=
    RegistrationNativeInitialKdfReceipt.server setup codec initial hashed before recorded supported
  exact ⟨before, recorded, request, atStep, next, supported, requested, called, resumed, continued⟩

end BeaconcryptCore.Computational.RegistrationNativeServerRecordIssuance

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeServerRecordIssuance.complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeServerRecordIssuance.complete

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeServerRecordIssuance.build' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeServerRecordIssuance.build

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeServerRecordIssuance.stage_contents' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeServerRecordIssuance.stage_contents

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeServerRecordIssuance.typed_build' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeServerRecordIssuance.typed_build

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeServerRecordIssuance.new_receipt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeServerRecordIssuance.new_receipt

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeServerRecordIssuance.RecordCut.initial' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeServerRecordIssuance.RecordCut.initial

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeServerRecordIssuance.AdCut.cached' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeServerRecordIssuance.AdCut.cached
