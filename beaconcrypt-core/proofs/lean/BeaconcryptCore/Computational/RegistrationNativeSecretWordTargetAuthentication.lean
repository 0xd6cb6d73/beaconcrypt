-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationEd25519Receipts
import BeaconcryptCore.Computational.RegistrationAuthenticationCompiler
import BeaconcryptCore.Computational.RegistrationRootInput

/-! Actual open native authentication preserves all three attached Ed25519 verification receipts under every concrete interpretation of its hash effects. The proof follows the extracted callback trace and the compiler's literal pure Ed verifier. It requires no real-KDF, fixed SDK, cache simulation or caller-supplied verification fact. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
set_option autoImplicit false
set_option maxRecDepth 2048
namespace BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetAuthentication
open BeaconcryptCore.Refinement.RegistrationAuthentication
open BeaconcryptCore.Refinement.RegistrationInbound
open BeaconcryptCore.Refinement.RegistrationAuthenticationFlow
open RegistrationAuthenticationExecutor
variable {n : Nat}

private def implementation {S : Type} (crypto : Pqxdh.Crypto) (verify : MldsaTranscriptAuth.Verify)
    (environment : QueryImpl (PqxdhRecordLiftInterface.EnvEffects n) (StateT S ProbComp)) :
    QueryImpl Spec (StateT S ProbComp) := environment ∘ₛ RegistrationAuthenticationCompiler.callbacks crypto verify

private def program {S : Type} (crypto : Pqxdh.Crypto) (verify : MldsaTranscriptAuth.Verify)
    (environment : QueryImpl (PqxdhRecordLiftInterface.EnvEffects n) (StateT S ProbComp))
    (pin : session.ServerAuthenticationPin) (packet : registration.InitPacket) :=
  simulateQ (implementation crypto verify environment) (RegistrationAuthenticationExecutor.begin pin packet)

private theorem ed_exact {S : Type} (crypto : Pqxdh.Crypto) (verify : MldsaTranscriptAuth.Verify)
    (environment : QueryImpl (PqxdhRecordLiftInterface.EnvEffects n) (StateT S ProbComp))
    (request : registration.Ed25519VerificationRequest) :
    implementation crypto verify environment (.ed25519 request) =
      pure (RegistrationAuthenticationShared.verifyEd25519 crypto request) := by
  simp only [implementation, QueryImpl.apply_compose, RegistrationAuthenticationCompiler.callbacks, simulateQ_pure]

private theorem tail_bytes (identity : Array Std.U8 33#usize) (key : Array Std.U8 32#usize)
    (actual : key.val = (List.range 32).map (fun index => identity.val[index + 1]!)) :
    absBytes key = (absBytes identity).drop 1 := by
  apply List.ext_getElem
  · simp
  · intro index left right
    simp only [absBytes, actual, List.getElem_map, List.getElem_range, List.getElem_drop]
    have inside : index + 1 < identity.val.length := by
      have bound := identity.property
      simp only [List.length_drop, absBytes_length] at right
      simp only [Std.UScalar.ofNatCore_val_eq] at right bound
      omega
    simp only [getElem!_pos identity.val (index + 1) inside, Nat.add_comm 1 index]

private def KeyMetadata (packet : registration.InitPacket) : registration.InitAuthentication → Prop
  | .HashRequested before => before.fields = ownedFields packet
  | .Ed25519VerificationRequested before => before.state.fields = ownedFields packet ∧
      absBytes before.public_key = (absBytes packet.identity_key).drop 1
  | _ => True

private theorem key_step (packet : registration.InitPacket) {before after : registration.InitAuthentication}
    {event : Event} (edge : Step before event after) (prior : KeyMetadata packet before) : KeyMetadata packet after := by
  cases edge with
  | hash before reply after run =>
      cases reply with
      | none => exact (RustM.ok.inj run) ▸ True.intro
      | some digest =>
          obtain ⟨result, resumed, outcome⟩ := init_hash_resume_refines before digest
          have facts : initHashOutcome before digest after := (RustM.ok.inj (resumed.symm.trans run)) ▸ outcome
          cases after
          all_goals simp only [initHashOutcome] at facts
          case Rejected => trivial
          case Ed25519VerificationRequested next =>
            obtain ⟨_tag, fieldsSame, _pin, _digest, _stage, key⟩ := facts
            refine ⟨fieldsSame.trans prior, ?_⟩
            have exactTail := tail_bytes before.fields.identity_key next.public_key key
            simpa only [show before.fields = ownedFields packet from prior, ownedFields] using exactTail
  | ed25519 before opened after run =>
      obtain ⟨result, resumed, progress⟩ := init_ed_resume_refines before opened
      have facts : edProgress before opened after := (RustM.ok.inj (resumed.symm.trans run)) ▸ progress
      cases after
      all_goals simp only [edProgress] at facts
      case Rejected => trivial
      case Accepted => trivial
      case Ed25519VerificationRequested next =>
        obtain ⟨_bytes, _reply, _suffix, stateSame, keySame, _transition⟩ := facts
        exact ⟨by simpa only [stateSame] using prior.1, by simpa only [keySame] using prior.2⟩

def signedBytes (packet : registration.InitPacket) : registration.SignedKeyStage → Pqxdh.Bytes
  | .PqKey => absBytes packet.pq_key
  | .PreKey => absBytes packet.pre_key
  | .OneTimeKey => absBytes packet.one_time_key

def Receipt (crypto : Pqxdh.Crypto) (packet : registration.InitPacket) : Event → Prop
  | .ed25519 stage (.Some opened) =>
      crypto.verify ((absBytes packet.identity_key).drop 1) (signedBytes packet stage) =
        some (TranscriptAuthParts.absSlice opened)
  | _ => True

private theorem interpreted_step {S : Type}
    (implementation : QueryImpl Spec (StateT (S) ProbComp))
    (initial final : registration.InitAuthentication) (event : Event)
    (before after : S)
    (supported : (.ok (some (event, final)), after) ∈ support
      ((simulateQ implementation (step initial)).run before)) : Step initial event final := by
  apply step_sound initial event final
  apply OracleComp.support_simulateQ_run'_subset implementation _ before
  rw [StateT.run'_eq, support_map]
  exact Set.mem_image_of_mem Prod.fst supported

private theorem step_receipt {S : Type} (crypto : Pqxdh.Crypto) (verify : MldsaTranscriptAuth.Verify)
    (environment : QueryImpl (PqxdhRecordLiftInterface.EnvEffects n) (StateT S ProbComp))
    (packet : registration.InitPacket) (initial final : registration.InitAuthentication) (event : Event)
    (before after : S) (prior : KeyMetadata packet initial)
    (supported : (.ok (some (event, final)), after) ∈ support
      ((simulateQ (implementation crypto verify environment) (step initial)).run before)) :
    Receipt crypto packet event := by
  have native : Step initial event final := by
    apply step_sound initial event final
    apply OracleComp.support_simulateQ_run'_subset
      (implementation crypto verify environment) _ before
    rw [StateT.run'_eq, support_map]
    exact Set.mem_image_of_mem Prod.fst supported
  cases native with
  | hash => trivial
  | ed25519 pending reply final resumed =>
      cases reply with
      | none => trivial
      | some opened =>
          obtain ⟨request, requested, key, signed, _length⟩ := init_ed_request_exact pending
          obtain ⟨next, actualResume, _progress⟩ :=
            init_ed_resume_refines pending (RegistrationAuthenticationShared.verifyEd25519 crypto request)
          simp only [step, continueWith, requested, simulateQ_bind, simulateQ_spec_query,
            StateT.run_bind] at supported
          rw [ed_exact, StateT.run_pure, pure_bind] at supported
          simp only [actualResume, edge, simulateQ_pure, StateT.run_pure, support_pure,
            Set.mem_singleton_iff, Prod.mk.injEq, RustM.ok.injEq, Option.some.injEq,
            Event.ed25519.injEq] at supported
          have actualReply : RegistrationAuthenticationShared.verifyEd25519 crypto request = .Some opened := by
            tauto
          have actualVerify := RegistrationEd25519Receipts.opened_receipt crypto request opened actualReply
          change crypto.verify ((absBytes packet.identity_key).drop 1) (signedBytes packet pending.stage) =
            some (TranscriptAuthParts.absSlice opened)
          rw [key, prior.2] at actualVerify
          have bytes : TranscriptAuthParts.absSlice request.signed = signedBytes packet pending.stage := by
            simp only [TranscriptAuthParts.absSlice, signed, edSignedBytes, signedBytes, prior.1, ownedFields, absBytes]
            cases pending.stage <;> rfl
          simpa only [bytes] using actualVerify

private theorem trace_receipts {S : Type} (crypto : Pqxdh.Crypto) (verify : MldsaTranscriptAuth.Verify)
    (environment : QueryImpl (PqxdhRecordLiftInterface.EnvEffects n) (StateT S ProbComp))
    (packet : registration.InitPacket) {initial final : registration.InitAuthentication} {events : List Event}
    {before after : S}
    (trace : RegistrationAuthenticationInterpretation.Trace
      (implementation crypto verify environment) initial before events final after)
    (prior : KeyMetadata packet initial) : ∀ event ∈ events, Receipt crypto packet event := by
  revert prior
  induction trace with
  | refl => intro prior event member; simp at member
  | @cons initial before event next middle events final after first rest ih =>
      intro prior selected member
      simp only [List.mem_cons] at member
      rcases member with same | member
      · subst selected
        exact step_receipt crypto verify environment packet initial next event before middle prior first
      · exact ih (key_step packet
          (interpreted_step (implementation crypto verify environment)
            initial next event before middle first) prior) selected member

attribute [local irreducible] execute registration.begin_init_authentication

private theorem begin_parts {S : Type} (crypto : Pqxdh.Crypto) (verify : MldsaTranscriptAuth.Verify)
    (environment : QueryImpl (PqxdhRecordLiftInterface.EnvEffects n) (StateT S ProbComp))
    (pin : session.ServerAuthenticationPin) (packet : registration.InitPacket)
    (before after : S) (events : List Event) (final : registration.InitAuthentication)
    (supported : (.ok (events, final), after) ∈ support ((program crypto verify environment pin packet).run before)) :
    ∃ initial : registration.InitHash,
      registration.begin_init_authentication pin packet = .ok (.HashRequested initial) ∧
      initial.fields = ownedFields packet ∧ initial.server_pin = pin ∧ absBytes initial.input = initPreimage pin packet ∧
      (.ok (events, final), after) ∈ support
        ((simulateQ (implementation crypto verify environment) (execute 5 (.HashRequested initial))).run before) := by
  unfold program RegistrationAuthenticationExecutor.begin at supported
  obtain ⟨initial, started, executed⟩ := RegistrationAuthenticationInterpretation.continueWith_support
    (implementation crypto verify environment) (registration.begin_init_authentication pin packet) (execute 5)
    (events, final) before after supported
  obtain ⟨source, sourceStarted, samePacket, samePin, preimage⟩ := begin_init_exact pin packet
  have same : initial = .HashRequested source := RustM.ok.inj (started.symm.trans sourceStarted)
  exact ⟨source, sourceStarted, samePacket, samePin, preimage, same ▸ executed⟩

theorem accepted_suffixes {S : Type} (crypto : Pqxdh.Crypto) (verify : MldsaTranscriptAuth.Verify)
    (environment : QueryImpl (PqxdhRecordLiftInterface.EnvEffects n) (StateT S ProbComp))
    (pin : session.ServerAuthenticationPin) (packet : registration.InitPacket)
    (before after : S) (events : List Event)
    (accepted : registration.AuthenticatedInit)
    (supported : (.ok (events, .Accepted accepted), after) ∈ support
      ((program crypto verify environment pin packet).run before)) :
    crypto.verify ((absBytes packet.identity_key).drop 1) (absBytes packet.pq_key) =
        some ((absBytes packet.pq_key).drop 64) ∧
      crypto.verify ((absBytes packet.identity_key).drop 1) (absBytes packet.pre_key) =
        some ((absBytes packet.pre_key).drop 64) ∧
      crypto.verify ((absBytes packet.identity_key).drop 1) (absBytes packet.one_time_key) =
        some ((absBytes packet.one_time_key).drop 64) := by
  obtain ⟨initial, _started, packetSame, _pin, _input, executed⟩ :=
    begin_parts crypto verify environment pin packet before after events
      (.Accepted accepted) supported
  have trace := RegistrationAuthenticationInterpretation.execute_trace
    (implementation crypto verify environment) 5 (.HashRequested initial)
    events (.Accepted accepted) before after executed
  have receipts := trace_receipts crypto verify environment packet trace
    (show KeyMetadata packet (.HashRequested initial) from packetSame)
  have execution := simulated_begin_sound
    (implementation crypto verify environment) pin packet events
    (.Accepted accepted) before after supported
  obtain ⟨digest, pq, pre, oneTime, eventList, pqSuffix, preSuffix, oneTimeSuffix⟩ :=
    accepted_requires_classical_checks pin packet events accepted execution
  have pqReceipt := receipts (.ed25519 .PqKey (.Some pq)) (by rw [eventList]; simp)
  have preReceipt := receipts (.ed25519 .PreKey (.Some pre)) (by rw [eventList]; simp)
  have oneTimeReceipt := receipts (.ed25519 .OneTimeKey (.Some oneTime)) (by rw [eventList]; simp)
  simpa only [Receipt, signedBytes, TranscriptAuthParts.absSlice, absBytes, pqSuffix, preSuffix,
    oneTimeSuffix, List.map_drop] using And.intro pqReceipt (And.intro preReceipt oneTimeReceipt)

private theorem parsed_head (packet : registration.InitPacket) (verified : pqxdh.VerifiedInitKex)
    (parsed : RegistrationCredentialBridge.parsedPacket packet = some (PqxdhHeadlineBridges.typedVerified verified)) :
    PqxdhEd25519EufCma.parseIdentity (absBytes packet.identity_key) =
      some (PqxdhHeadlineBridges.typedVerified verified).1 := by
  open PqxdhHeadlineBridges PqxdhEd25519EufCma in
    simp only [RegistrationCredentialBridge.parsedPacket, parsedBytes,
      Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at parsed
  obtain ⟨identity, identityParsed, prekey, _pre, oneTime, _one, pq, _pq, tupleSame⟩ := parsed
  have same : identity = (PqxdhHeadlineBridges.typedVerified verified).1 := congrArg Prod.fst tupleSame
  simpa only [same] using identityParsed

private theorem parsed_identity (packet : registration.InitPacket) (verified : pqxdh.VerifiedInitKex)
    (parsed : RegistrationCredentialBridge.parsedPacket packet = some (PqxdhHeadlineBridges.typedVerified verified)) :
    (absBytes packet.identity_key).drop 1 = absBytes verified.beacon_identity_public_key := by
  have identityParsed := parsed_head packet verified parsed
  have encoded := (PqxdhEd25519EufCma.parseIdentity_eq_some_iff _ _).mp identityParsed
  rw [encoded]
  rfl

theorem accepted_verify {S : Type} (crypto : Pqxdh.Crypto) (verify : MldsaTranscriptAuth.Verify)
    (environment : QueryImpl (PqxdhRecordLiftInterface.EnvEffects n) (StateT S ProbComp))
    (pin : session.ServerAuthenticationPin) (packet : registration.InitPacket)
    (before after : S) (events : List Event)
    (accepted : registration.AuthenticatedInit)
    (supported : (.ok (events, .Accepted accepted), after) ∈ support
      ((program crypto verify environment pin packet).run before)) :
    crypto.verify (absBytes accepted.registration.beacon_identity_public_key) (absBytes packet.pq_key) =
        some ((absBytes packet.pq_key).drop 64) ∧
      crypto.verify (absBytes accepted.registration.beacon_identity_public_key) (absBytes packet.pre_key) =
        some ((absBytes packet.pre_key).drop 64) ∧
      crypto.verify (absBytes accepted.registration.beacon_identity_public_key) (absBytes packet.one_time_key) =
        some ((absBytes packet.one_time_key).drop 64) := by
  have parsed := RegistrationCredentialBridge.interpreted_accepted_parsed
    (implementation crypto verify environment) pin packet events accepted before after supported
  simpa only [parsed_identity packet accepted.registration parsed] using
    accepted_suffixes crypto verify environment pin packet before after events accepted supported

def packetCandidate (packet : registration.InitPacket) : PqxdhEd25519EufCma.Phase1Candidate :=
  ⟨absBytes packet.identity_key, absBytes packet.pre_key, absBytes packet.one_time_key, absBytes packet.pq_key⟩

theorem accepted_source {S : Type} (crypto : Pqxdh.Crypto) (verify : MldsaTranscriptAuth.Verify)
    (environment : QueryImpl (PqxdhRecordLiftInterface.EnvEffects n) (StateT S ProbComp))
    (pin : session.ServerAuthenticationPin) (packet : registration.InitPacket)
    (before after : S) (events : List Event)
    (accepted : registration.AuthenticatedInit)
    (supported : (.ok (events, .Accepted accepted), after) ∈ support
      ((program crypto verify environment pin packet).run before)) :
    PqxdhJointPhase1Reports.sourceAccept (fun publicKey bytes => crypto.verify publicKey.toList bytes)
      (packetCandidate packet) = some (PqxdhHeadlineBridges.typedVerified accepted.registration) := by
  have parsed := RegistrationCredentialBridge.interpreted_accepted_parsed
    (implementation crypto verify environment) pin packet events accepted before after supported
  have identityParsed := parsed_head packet accepted.registration parsed
  obtain ⟨pqVerify, preVerify, oneVerify⟩ :=
    accepted_verify crypto verify environment pin packet before after events accepted supported
  have pq : crypto.verify (PqxdhHeadlineBridges.typedVerified accepted.registration).1.toList (absBytes packet.pq_key) =
      some ((absBytes packet.pq_key).drop 64) := pqVerify
  have pre : crypto.verify (PqxdhHeadlineBridges.typedVerified accepted.registration).1.toList (absBytes packet.pre_key) =
      some ((absBytes packet.pre_key).drop 64) := preVerify
  have one : crypto.verify (PqxdhHeadlineBridges.typedVerified accepted.registration).1.toList (absBytes packet.one_time_key) =
      some ((absBytes packet.one_time_key).drop 64) := oneVerify
  have same : PqxdhJointPhase1Reports.sourceAccept (fun publicKey bytes => crypto.verify publicKey.toList bytes)
      (packetCandidate packet) = RegistrationCredentialBridge.parsedPacket packet := by
    simp only [PqxdhJointPhase1Reports.sourceAccept, packetCandidate,
      RegistrationCredentialBridge.parsedPacket, PqxdhHeadlineBridges.parsedBytes,
      identityParsed, Option.bind_eq_bind, Option.bind_some, Option.pure_def, pq, pre, one]
  exact same.trans parsed

/-- Successful actual Compiler.program authentication yields exactly the original publicly verified packet tuple under any concrete hash-effect state, including the G2/Word interpreter. -/
theorem compiler_accepted {S : Type} (crypto : Pqxdh.Crypto) (verify : MldsaTranscriptAuth.Verify)
    (environment : QueryImpl (PqxdhRecordLiftInterface.EnvEffects n) (StateT S ProbComp))
    (pin : session.ServerAuthenticationPin) (packet : registration.InitPacket)
    (before after : S) (events : List Event) (accepted : registration.AuthenticatedInit)
    (supported : (.ok (events, .Accepted accepted), after) ∈ support
      ((simulateQ environment (RegistrationAuthenticationCompiler.program crypto verify pin packet)).run before)) :
    PqxdhDeploymentTranscript.acceptedKeys crypto (RegistrationRootInput.candidate packet) =
      some (RegistrationRootInput.identity accepted.registration, RegistrationRootInput.keys accepted.registration) := by
  apply accepted_source crypto verify environment pin packet before after events accepted
  simpa only [program, RegistrationAuthenticationCompiler.program, ← QueryImpl.simulateQ_compose, implementation] using supported

end BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetAuthentication
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetAuthentication.accepted_suffixes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetAuthentication.accepted_suffixes
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetAuthentication.accepted_verify' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetAuthentication.accepted_verify
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetAuthentication.accepted_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetAuthentication.accepted_source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetAuthentication.compiler_accepted' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetAuthentication.compiler_accepted
