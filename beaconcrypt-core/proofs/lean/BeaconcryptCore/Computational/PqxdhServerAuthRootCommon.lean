import BeaconcryptCore.Computational.PqxdhServerAuthRootObserved

/-! The complete sampled source session event, from actual public publication and matching accepted-owner receipts. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhServerAuthRootCommon
open PqxdhServerAuthExperiment PqxdhServerAuthEntryFactor PqxdhServerAuthRootOccurrences
open PqxdhServerAuthRootExecution PqxdhServerAuthRootSession
open PqxdhJointIdentity PqxdhJointGapDh PqxdhSecretInputKdf PqxdhEd25519EufCma
variable {ι KemSK Reader Response : Type} {baseSpec : OracleSpec ι}

/-- A successful publication in the literal public journal supplies an actual completed build occurrence at that same index. No byte decoding or writer inversion is used. -/
theorem published_call (calls : List (Call KemSK)) (index : Nat)
    (published : PqxdhServerAuthPublicationOccurrence.Published index (calls.map publicCall)) :
    ∃ data response before after roots,
      (⟨.inr (.build index data), some response, before, after, roots⟩ : Call KemSK) ∈ calls := by
  obtain ⟨data, response, member⟩ := published
  have full := List.takeWhile_subset _ member
  obtain ⟨call, actual, same⟩ := List.mem_map.mp full
  cases call with
  | mk query reply before after roots =>
      change (⟨query, reply⟩ : (query : ServerAuthSpec.Domain) × ServerAuthSpec.Range query) = _ at same
      cases same
      exact ⟨data, response, before, after, roots, actual⟩

/-- Initial emptiness and actual final acceptance identify a successful finish occurrence in the same sampled audit. -/
theorem accepted_call (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (adversary : Adversary) (result : Outcome KemSK)
    (supported : result ∈ support (game setup codec checks false adversary))
    (snap : Snapshot) (accepted : result.state.1.ghost.acceptance = some snap) :
    ∃ raw payload before after roots,
      (⟨.inr (.finish raw), some payload, before, after, roots⟩ : Call KemSK) ∈ result.state.2 := by
  obtain ⟨sampled, position, path⟩ := game_path setup codec checks false adversary result supported
  obtain ⟨call, actual, raw, payload, same⟩ := PqxdhServerAuthRootJournal.path_finish_exists setup codec checks
    (result.context.publicValue setup) result.context.beaconSeed result.context.seed result.context.scalar
    (contextState setup result.context, PqxdhJointDhExtractFamily.empty) (result.state.1, result.primitive)
    result.state.2 path rfl snap accepted
  cases call with
  | mk query reply before after roots =>
      change (⟨query, reply⟩ : (query : ServerAuthSpec.Domain) × ServerAuthSpec.Range query) = _ at same
      cases same
      exact ⟨raw, payload, before, after, roots, actual⟩

/-- The actual accepted partner, exact pre-acceptance seal and literal earlier successful publication at that same coordinate. This event contains no session-origin or root-equality assumption. -/
def MatchingPublication (setup : Setup baseSpec KemSK) (result : Outcome KemSK) (index : Nat) : Prop :=
  ∃ snap sealContext, result.state.1.ghost.acceptance = some snap ∧
    Partner setup result.context.seed result.context.scalar snap index ∧
    (index, sealContext) ∈ snap.seals ∧ sealed sealContext = snap.accepted ∧
    PqxdhServerAuthPublicationOccurrence.Published index (result.state.2.map publicCall)

/-- Full same-run source agreement: original consumed token and verified fields, actual root/initializer receipts for both roles, exact publications and all eleven retained fields. The source callbacks and original first Beacon root input remain explicit. -/
def Agreement (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (result : Outcome KemSK) (index : Nat) : Prop :=
  ∃ data response serverBefore serverAfter serverRoots raw payload beaconBefore beaconAfter beaconRoots
      snap sealContext,
    (⟨.inr (.build index data), some response, serverBefore, serverAfter, serverRoots⟩ : Call KemSK) ∈ result.state.2 ∧
    (⟨.inr (.finish raw), some payload, beaconBefore, beaconAfter, beaconRoots⟩ : Call KemSK) ∈ result.state.2 ∧
    result.state.1.ghost.acceptance = some snap ∧
    Partner setup result.context.seed result.context.scalar snap index ∧
    (index, sealContext) ∈ snap.seals ∧ sealed sealContext = snap.accepted ∧
    ∃ token candidate kernel logged cache acceptCall acceptRaw input consumed pending root staged,
      serverBefore.pending index = some token ∧
      acceptCall ∈ result.state.2 ∧
      (⟨acceptCall.query, acceptCall.reply⟩ : (query : ServerAuthSpec.Domain) × ServerAuthSpec.Range query) =
        ⟨.inr (.accept acceptRaw), some index⟩ ∧
      (some input, consumed) ∈ support ((serverPrefix setup codec checks acceptRaw).run acceptCall.before.server.consumed) ∧
      token.pending = PqxdhServerClearedRoot.pending (binding setup (result.context.publicValue setup)) input ∧
      PqxdhServerAuthPhase1Receipt.Decoded codec acceptRaw input.verified ∧
      PqxdhServerAuthPhase1Projection.Projected setup (result.context.publicValue setup) token input.verified ∧
      serverSession token serverBefore.server sealContext input.verified .targetPhase1 =
        beaconSession setup result.context root .targetPhase1 ∧
      token.root = root ∧ Installed setup.source root kernel ∧
      serverAfter.server = PqxdhServerRegistrationPublication.publish serverBefore.server candidate kernel () ∧
      (ok (some response, PqxdhServerRegistrationPublication.publish serverBefore.server candidate kernel ()),
        (logged, cache)) ∈ support ((simulateQ (tailImpl setup codec checks)
          (PqxdhServerRegistrationPublication.build setup.source token.pending token.root data () serverBefore.server)).run
            ([], serverBefore.ctx)) ∧
      RootAt setup result.context.seed result.context.scalar result.primitive.cache
        (PqxdhJointDhExtractRoot.beaconMessage (result.context.publicValue setup) pending.collected) root ∧
      (some staged, ((), beaconAfter.ctx)) ∈ support ((simulateQ (beaconNative setup codec)
        (PqxdhPhase2DhRootConsumer.afterRoot codec.frameRead pending (PqxdhRootTableInitialization.rootArray root))).run
          ((), beaconBefore.ctx)) ∧
      beaconAfter.beacon.beacon.phase = .established
        ⟨staged.authenticated.candidate.server_binding, staged.authenticated.candidate.assigned_key_id⟩
        staged.associatedData staged.kernel ∧
      ∃ control prekey oneTime kem,
        beaconBefore.beacon.beacon.phase = .initSent control prekey oneTime kem ∧
        some pending ∈ support ((beaconPrefix setup codec result.context.beaconSeed control
          beaconBefore.beacon.beacon.identity oneTime kem raw).run' ()) ∧
        firstBeacon result.state.1.ghost.touches = some
          (PqxdhJointDhExtractRoot.beaconMessage (result.context.publicValue setup) pending.collected)

/-- The actual sampled matching/publication event and absence of the existing signed-field substitution event imply the complete eleven-field source agreement. No caller supplies any callback, token, root, initialization or generation-origin witness. -/
theorem game_agreement (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (adversary : Adversary) (result : Outcome KemSK)
    (supported : result ∈ support (game setup codec checks false adversary)) (index : Nat)
    (matching : MatchingPublication setup result index)
    (adapter : HasAttachedVerificationAdapter
      (fun identity => setup.source.crypto.verify identity.toList) setup.joint.verify)
    (unchanged : PqxdhServerAuthRootObserved.changed setup codec result = false) :
    Agreement setup codec checks result index := by
  obtain ⟨sampled, position, path⟩ := game_path setup codec checks false adversary result supported
  obtain ⟨snap, sealContext, accepted, partner, loggedBefore, matched, published⟩ := matching
  obtain ⟨data, response, serverBefore, serverAfter, serverRoots, built⟩ :=
    published_call result.state.2 index published
  obtain ⟨raw, payload, beaconBefore, beaconAfter, beaconRoots, finished⟩ :=
    accepted_call setup codec checks adversary result supported snap accepted
  refine ⟨data, response, serverBefore, serverAfter, serverRoots, raw, payload, beaconBefore,
    beaconAfter, beaconRoots, snap, sealContext, built, finished, accepted, partner, loggedBefore, matched, ?_⟩
  exact path_session setup codec checks result.context sampled PqxdhJointDhExtractFamily.empty
    (result.state.1, result.primitive) result.state.2 path index data response serverBefore serverAfter serverRoots
    built raw payload beaconBefore beaconAfter beaconRoots finished snap accepted partner sealContext loggedBefore
    matched adapter unchanged

/-- The retained origin is the original singleton generation invocation, with its actual successful Phase1 writer and full private published state. Failed writers are not treated as installations. -/
def Generation (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (result : Outcome KemSK) : Prop :=
  result.position = .targetPhase1 ∧ PqxdhServerAuthPhase1Generation.Generated setup codec result.context ∧
  ∃ bytes,
    codec.write1 (PqxdhServerAuthNegativeControl.beaconCandidate setup (result.context.publicValue setup)
      result.context.beaconSeed result.context.oneTime result.context.keys.1) = some bytes ∧
    result.context.published = (some bytes, PqxdhServerAuthNegativeControl.publishedBeacon setup
      (result.context.publicValue setup) result.context.beaconSeed result.context.oneTime result.context.keys.2)

/-- Actual acceptance supplies the original generation and successful Phase1 publication occurrence. This is derived through the active pre-finish source state, without comparing keys or roots. -/
theorem game_generation (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (adversary : Adversary) (result : Outcome KemSK)
    (supported : result ∈ support (game setup codec checks false adversary))
    (snap : Snapshot) (accepted : result.state.1.ghost.acceptance = some snap) :
    Generation setup codec result := by
  obtain ⟨sampled, position, path⟩ := game_path setup codec checks false adversary result supported
  obtain ⟨raw, payload, before, after, roots, finished⟩ :=
    accepted_call setup codec checks adversary result supported snap accepted
  obtain ⟨earlier, later, primitive, next, split, preceding, reached, following⟩ :=
    path_occurrence setup codec checks (result.context.publicValue setup) result.context.beaconSeed
      result.context.seed result.context.scalar (contextState setup result.context, PqxdhJointDhExtractFamily.empty)
      (result.state.1, result.primitive) result.state.2 path _ finished
  have source := callback_source setup codec checks (result.context.publicValue setup) result.context.beaconSeed
    result.context.seed result.context.scalar _ primitive next reached
  obtain ⟨control, prekey, oneTime, kem, staged, middle, active, _⟩ :=
    PqxdhServerAuthRootInitialization.finish_receipt setup codec (result.context.publicValue setup)
      result.context.beaconSeed result.context.seed result.context.scalar raw payload (before, primitive)
      (after, next) source
  obtain ⟨bytes, written, published, _⟩ := PqxdhServerAuthRootSessionFields.path_generation setup codec checks
    result.context sampled PqxdhJointDhExtractFamily.empty (before, primitive) earlier preceding
    ⟨control, prekey, oneTime, kem, active⟩
  exact ⟨position, PqxdhServerAuthPhase1Generation.context_generated setup codec result.context sampled,
    bytes, written, published⟩

/-- The complete retained source session and its original generation occurrence. Both role initializations and successful publications are part of Agreement, rather than inferred from matching installed keys. -/
def Common (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (result : Outcome KemSK) (index : Nat) : Prop :=
  Generation setup codec result ∧ MatchingPublication setup result index ∧ Agreement setup codec checks result index

/-- Complete sampled eleven-field common-event implication, retaining the actual generation and all original occurrence/root/publication witnesses. The only event alternatives are the supplied actual matching-publication event and the existing all-attempt signed-field substitution event. -/
theorem game_common (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (adversary : Adversary) (result : Outcome KemSK)
    (supported : result ∈ support (game setup codec checks false adversary)) (index : Nat)
    (matching : MatchingPublication setup result index)
    (adapter : HasAttachedVerificationAdapter
      (fun identity => setup.source.crypto.verify identity.toList) setup.joint.verify)
    (unchanged : PqxdhServerAuthRootObserved.changed setup codec result = false) :
    Common setup codec checks result index := by
  have agreement := game_agreement setup codec checks adversary result supported index matching adapter unchanged
  have retained := matching
  obtain ⟨snap, _, accepted, _⟩ := retained
  exact ⟨game_generation setup codec checks adversary result supported snap accepted, matching, agreement⟩

/-- A failed complete common event on an actually matched/published accepted source run is included in the existing all-attempt substitution event. This is a supported deterministic implication, not an assumed cryptographic bound. -/
theorem missing_common_changed (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (adversary : Adversary) (result : Outcome KemSK)
    (supported : result ∈ support (game setup codec checks false adversary)) (index : Nat)
    (matching : MatchingPublication setup result index)
    (adapter : HasAttachedVerificationAdapter
      (fun identity => setup.source.crypto.verify identity.toList) setup.joint.verify)
    (missing : ¬ Common setup codec checks result index) :
    PqxdhServerAuthRootObserved.changed setup codec result = true := by
  cases value : PqxdhServerAuthRootObserved.changed setup codec result with
  | false => exact (missing (game_common setup codec checks adversary result supported index matching adapter value)).elim
  | true => rfl

end BeaconcryptCore.Computational.PqxdhServerAuthRootCommon

/-! ## Checked theorem dependencies -/

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthRootCommon.published_call' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthRootCommon.published_call

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthRootCommon.accepted_call' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthRootCommon.accepted_call

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthRootCommon.game_agreement' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthRootCommon.game_agreement

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthRootCommon.game_generation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthRootCommon.game_generation

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthRootCommon.game_common' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthRootCommon.game_common

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthRootCommon.missing_common_changed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthRootCommon.missing_common_changed
